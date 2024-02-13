freeze;

import "linear/SLCentralizer.m": SLCentralizer; 
import "linear/GLCentralizer.m": GLCentralizer; 
import "MaxDeterminant.m": ElementOfMaxDeterminant;
import "semisimple/form.m": DetermineForm, IndicateType, SpinN, ConjugatePolynomial;
import "semisimple/Centralizer/Correctors.m": CorrectSpecial;
import "semisimple/Centralizer/SSCentralizer.m": SSCentralizer;
import "size.m": MyIsIn;
import "Gen-Label.m": TransformMatrix;

// modify the standard Magma description of the elementary divisors
// Now c is a sequence [<f_i, [m_i1, ... , m_ij] > : i], where the m_i1, ... , m_ij 
// are the dimensions of the Jordan blocks relative to the elementary divisor f_i
// Moreover, the polynomials t+1 and t-1 are put at the beginning of the sequence.

FixJordanForm := function (r, t)
   i := 0;
   c := [];
   for y in r do
      if y[1] ne t-1 and y[1] ne t+1 then
         if i gt 0 and y[1] eq c[i][1] then
            Append (~c[i][2], y[2]);
         else
            i +:= 1;
            Append (~c, <y[1], [y[2]]>);
         end if;
      end if;
   end for;

   for y in r do
      if y[1] eq t-1 or y[1] eq t+1 then
         if i gt 0 and y[1] eq c[1][1] then
            Insert (~c[1][2], 1, y[2]);
         else
            i +:= 1;
            Insert (~c, 1, <y[1], [y[2]]>);
         end if;
      end if;
   end for;
   // this is to put t+1 and t-1 at the beginning of the list

   // if the first elementary divisor is t-1 of multiplicity 1, then  
   // it is not possible to correct both Determinant and SpinorNorm 
   if #c gt 1 and c[1][1] eq t-1 and &+c[1][2] eq 1 and c[2][1] eq t+1 then
      d := c[1];
      c[1] := c[2];
      c[2] := d;
   end if;

   return c;
end function;

// G must be a classical group (GO, GU, Sp, SO, Su, Omega) and x in G
// returns Centralizer (G, x) with assigned Order and FactoredOrder
// Does not work for orthogonal groups in even characteristic and odd dimension

GenCentralizer := function (G, x)
   F<w> := BaseRing (G);
   n := Nrows (x);
   p := Characteristic (F);
   q := #F;
   t := PolynomialRing (F).1;
   M := MatrixAlgebra (F, n);
   Card := Factorization (1);
   FirstHasDim1 := false;

   B, type, sgn, special, IsOmega, Q, is_abelian := DetermineForm (G, x);

   // trivial case
   if is_abelian then return G; end if;

   e := type eq "unitary" select Degree (F) div 2 else 0;

   //conjugate transpose matrix
   Star := func<M: exp := e| Transpose (FrobeniusImage (M, exp))>;

   //conjugate polynomial
   ConjPol := ConjugatePolynomial (type eq "unitary");

   a, b, r := JordanForm (x);
   c := FixJordanForm (r, t);

   SetGen := [Generic (G) | ];  // generators for the centralizer
   X := ZeroMatrix (F, 0, 0);

   // X: form in which is easier to compute the centralizer
   i := 1;
   pos := 1;
   while i le #c do
      f := c[i][1];
      d := Degree (f);
      Y := ZeroMatrix (F, 0, 0);
      for m in c[i][2] do            // m = dimension of the Jordan block
         y := DiagonalJoin ([CompanionMatrix (f): j in [1..m]]);
         for j in [1..m*d-d] do
            y[j, j+d] := 1;
         end for;
         Y := DiagonalJoin (Y, y);
      end for;
      X := DiagonalJoin (X, Y);
      if f ne ConjPol (f) then
         X := DiagonalJoin (X, Star (Y)^-1);
         Exclude (~c, <ConjPol (f), c[i][2]>);
      end if;
      i +:= 1;
   end while;

   _, bX := JordanForm (X);
   b1 := bX^-1*b;
   // rewrite A in the upper triangular form
   if p eq 2 and type ne "unitary" and type ne "symplectic" then
      A := b1*Q*Star (b1);              // A = quadratic form preserved by X
      for i in [1..n] do
      for j in [i+1..n] do
         A[i, j] +:= A[j, i];
         A[j, i] := 0;
      end for;
      end for;
   else
      A := b1*B*Star (b1);    // A = sesquilinear form preserved by X
   end if;

   if special and type ne "unitary" then
      ThereIsOdd := false;
      if c[1][1] in {t+1, t-1} then
         if true in [IsOdd (d): d in c[1][2]] then
            ThereIsOdd := true;
         elif #c gt 1 and c[2][1] in {t-1, t+1} then
            if true in [IsOdd (d): d in c[2][2]] then
               ThereIsOdd := true;
               FirstHasDim1 := true;
            end if;
         end if;
      end if;
      if ThereIsOdd eq false then
         special := false;   // in this case the centralizers in GO and SO coincide
      end if;
   end if;

   // CorrectSp is an element in the centralizer of the first el.div. 
   // (or the second el.div. in the case x^2-1 has rank n-1)
   // with determinant 1 and SpinorNorm 1
   if (special or IsOmega) and type ne "unitary" then
      CorrectSp, FirstHasDim1 := CorrectSpecial (c, F, n, q, p, e, type, A, b1);
      DetC := Determinant (CorrectSp);
   end if;

   // the i-th element of AddDeterminant is Y_i, where Y_i is an element 
   // in the centralizer in GU of X_i of maximal order of the determinant
   if special and type eq "unitary" then
      AddDeterminant := <>;
   end if;

   // create generators

   // case Special Orthogonal: 
   // if <x_1, ..., x_k> are generators for centralizer of x in the general group, 
   // generators of the centralizer of the first el.div. are replaced by generators 
   // for centralizer in the special group;
   // the other generators are multiplied by some power of CorrectSp, 
   // depending on determinant

   // case Special Unitary: the first part produces generators of the 
   // centralizer of every single block in its corresponding special group;
   // elements with overall determinant 1, but not for every single block, 
   // are added in second part

   // case Omega: the set of generators is the same as the special case;
   // it will be modified in the third part

   Y := IdentityMatrix (F, n);
   pos := 1;
   ind := 1;
   if FirstHasDim1 then ind := 2; end if;
   for i in [1..#c] do
      f := c[i][1];
      d := &+c[i][2];
      deg := Degree (f);
      if f eq ConjPol (f) and deg eq 1 then
         B1 := Submatrix (A, pos, pos, d, d);
         X1 := Submatrix (X, pos, pos, d, d);
         // U1 = unipotent part. They have the same centralizer
         U1 := X1*ScalarMatrix (d, (-ConstantCoefficient (f))^-1);
         case type:

            when "unitary":
               m := TransformForm (B1, "unitary": Restore := false);
               mInv := m^-1;
               if special then
                  MyH := SU(d, F); MyH`ClassicalType := "SU";
                  Cent := InternalUnipotentCentralizer (MyH, GL(d, F)!(mInv*U1*m));
                  Append (~AddDeterminant, ElementOfMaxDeterminant (U1, B1, m, "unitary"));
                  for j in [1..Ngens (Cent)] do
                     Y1 := InsertBlock (Y, m*Cent.j*mInv, pos, pos);
                     Y1 := b1^-1*Y1*b1;
                     Append (~SetGen, Y1);
                  end for;
               else
                  MyH := GU(d, F); MyH`ClassicalType := "GU";
                  Cent := InternalUnipotentCentralizer (MyH, GL(d, F)!(mInv*U1*m));
                  for j in [1..Ngens (Cent)] do
                     Y1 := InsertBlock (Y, m*Cent.j*mInv, pos, pos);
                     Y1 := b1^-1*Y1*b1;
                     Append (~SetGen, Y1);
                  end for;
               end if;
               Card *:= FactoredOrder (Cent);

            when "symplectic":
               m := TransformForm (B1, "symplectic": Restore := false);
               MyH := Sp(d, F); MyH`ClassicalType := "Sp";
               Cent := InternalUnipotentCentralizer (MyH, GL(d, F)!(m^-1*U1*m));
               for j in [1..Ngens (Cent)] do
                  Y1 := InsertBlock (Y, m*Cent.j*m^-1, pos, pos);
                  Append (~SetGen, b1^-1*Y1*b1);
               end for;
               Card *:= FactoredOrder (Cent);

            when "orthogonalcircle", "orthogonalplus", "orthogonalminus", "orthogonal":
               if d eq 1 then
                  type1 := "orthogonal";
                  if not special or i ne ind then
                     Y1 := InsertBlock (Y, -IdentityMatrix (F, 1), pos, pos);
                     Y1 := b1^-1*Y1*b1;
                     if special then
                        Y1 *:= CorrectSp;
                     end if;
                     Card *:= SequenceToFactorization ([<2, 1>]);
                     Append (~SetGen, Y1);
                  end if;
               else
                  type1 := IndicateType (B1);
                  m := TransformForm (B1, type1: Restore := false);
                  if type1 eq "orthogonalplus" then
                     if special or (IsOmega and IsOdd (p)) then
                        if i eq ind then
                           MyH := SOPlus(d, F); MyH`ClassicalType := "SO+";
                           Cent := InternalUnipotentCentralizer (MyH, GL(d, F)!(m^-1*U1*m));
                           for j in [1..Ngens (Cent)] do
                              Y1 := InsertBlock (Y, m*Cent.j*m^-1, pos, pos);
                              Y1 := b1^-1*Y1*b1;
                              Append (~SetGen, Y1);
                           end for;
                        else
                           MyH := GOPlus(d, F); MyH`ClassicalType := "GO+";
                           Cent := InternalUnipotentCentralizer (MyH, GL(d, F)!(m^-1*U1*m));
                           for j in [1..Ngens (Cent)] do
                              Y1 := InsertBlock (Y, m*Cent.j*m^-1, pos, pos);
                              Y1 := b1^-1*Y1*b1;
                              if Determinant (Y1) eq -1 then
                                 Y1 *:= CorrectSp;
                              end if;
                              Append (~SetGen, Y1);
                           end for;
                        end if;
                     else
                        MyH := GOPlus(d, F); MyH`ClassicalType := "GO+";
                        Cent := InternalUnipotentCentralizer (MyH, GL(d, F)!(m^-1*U1*m));
                        for j in [1..Ngens (Cent)] do
                           Y1 := InsertBlock (Y, m*Cent.j*m^-1, pos, pos);
                           Y1 := b1^-1*Y1*b1;
                           Append (~SetGen, Y1);
                        end for;
                     end if;
                  elif type1 eq "orthogonalminus" then
                     if special or (IsOmega and IsOdd (p)) then
                        if i eq ind then
                           MyH := SOMinus(d, F); MyH`ClassicalType := "SO-";
                           Cent := InternalUnipotentCentralizer (MyH, GL(d, F)!(m^-1*U1*m));
                           for j in [1..Ngens (Cent)] do
                              Y1 := InsertBlock (Y, m*Cent.j*m^-1, pos, pos);
                              Y1 := b1^-1*Y1*b1;
                              Append (~SetGen, Y1);
                           end for;
                        else
                           MyH := GOMinus(d, F); MyH`ClassicalType := "GO-";
                           Cent := InternalUnipotentCentralizer (MyH, GL(d, F)!(m^-1*U1*m));
                           for j in [1..Ngens (Cent)] do
                              Y1 := InsertBlock (Y, m*Cent.j*m^-1, pos, pos);
                              Y1 := b1^-1*Y1*b1;
                              if Determinant (Y1) eq -1 then
                                 Y1 *:= CorrectSp;
                              end if;
                              Append (~SetGen, Y1);
                           end for;
                        end if;
                     else
                        MyH := GOMinus(d, F); MyH`ClassicalType := "GO-";
                        Cent := InternalUnipotentCentralizer (MyH, GL(d, F)!(m^-1*U1*m));
                        for j in [1..Ngens (Cent)] do
                           Y1 := InsertBlock (Y, m*Cent.j*m^-1, pos, pos);
                           Y1 := b1^-1*Y1*b1;
                           Append (~SetGen, Y1);
                        end for;
                     end if;
                  else
                     if special or (IsOmega and IsOdd (p)) then
                        if i eq ind then
                           MyH := SO(d, F); MyH`ClassicalType := "SO";
                           Cent := InternalUnipotentCentralizer (MyH, GL(d, F)!(m^-1*U1*m));
                           for j in [1..Ngens (Cent)] do
                              Y1 := InsertBlock (Y, m*Cent.j*m^-1, pos, pos);
                              Y1 := b1^-1*Y1*b1;
                              Append (~SetGen, Y1);
                           end for;
                        else
                           MyH := GO(d, F); MyH`ClassicalType := "GO";
                           Cent := InternalUnipotentCentralizer (MyH, GL(d, F)!(m^-1*U1*m));
                           for j in [1..Ngens (Cent)] do
                              Y1 := InsertBlock (Y, m*Cent.j*m^-1, pos, pos);
                              Y1 := b1^-1*Y1*b1;
                              if Determinant (Y1) eq -1 then
                                 Y1 *:= CorrectSp;
                              end if;
                              Append (~SetGen, Y1);
                           end for;
                        end if;
                     else
                        MyH := GO(d, F); MyH`ClassicalType := "GO";
                        Cent := InternalUnipotentCentralizer (MyH, GL(d, F)!(m^-1*U1*m));
                        for j in [1..Ngens (Cent)] do
                           Y1 := InsertBlock (Y, m*Cent.j*m^-1, pos, pos);
                           Y1 := b1^-1*Y1*b1;
                           Append (~SetGen, Y1);
                        end for;
                     end if;
                  end if;
                  Card *:= FactoredOrder (Cent);
               end if;
         end case;
         pos +:= d;
      elif f ne ConjPol (f) then
         E<l> := ext<F | f: Optimize := false>;
         A1 := Submatrix (A, pos, pos+d*deg, d*deg, d*deg);
         y := IdentityMatrix (E, d);
         pos1 := 1;
         for j1 in c[i][2] do
            for j2 in [1..j1-1] do
               y[pos1, pos1+1] := 1;
               pos1 +:= 1;
            end for;
            pos1 +:= 1;
         end for;
         if special and type eq "unitary" then
            MyH := SL(d, E); MyH`ClassicalType := "SL";
            Cent := InternalUnipotentCentralizer (MyH, GL(d, E)!y);
            y, GCD := ElementOfMaxDeterminant (y, c[i][2], IdentityMatrix (E, d), "linear");
            suss := BlockMatrix (d, d, [&+[CompanionMatrix (f)^(k-1)*Eltseq (y[j1, j2], F)[k]:
                       k in [1..deg]]: j1, j2 in [1..d]]);
            suss := DiagonalJoin (suss, Star (A1^-1*suss^-1*A1));
            Append (~AddDeterminant, suss);
            // add an element having determinant 1 in SU(d*deg, F), but not in SU(d, E)
            // Gcd (deg*GCD, p^e+1) = Gcd (GCD * (p^(2*e*deg)-1) / (p^2e-1), p^e+1)
            alpha := (p^e+1) div Gcd (GCD, p^e+1);
            y := InsertBlock (Y, suss^alpha, pos, pos);
            Append (~SetGen, b1^-1*y*b1);
            Card *:= Factorization (p^(2*e*deg)-1);
            Card /:= Factorization (GCD*alpha);
         else
            MyH := GL(d, E); MyH`ClassicalType := "GL";
            Cent := InternalUnipotentCentralizer (MyH, GL(d, E)!y);
         end if;
         for j in [1..Ngens (Cent)] do
            a := Cent.j;
            suss := BlockMatrix (d, d, [&+[CompanionMatrix (f)^(k-1)*Eltseq (a[j1, j2], F)[k]:
                       k in [1..deg]]: j1, j2 in [1..d]]);
            suss := DiagonalJoin (suss, Star (A1^-1*suss^-1*A1));
            y := InsertBlock (Y, suss, pos, pos);
            y := b1^-1*y*b1;
            if special then
               if type ne "unitary" then
 		  if Determinant (y) eq -1 then
                     y *:= CorrectSp;
                  end if;
               end if;
            end if;
            Append (~SetGen, y);
         end for;
         pos +:= 2*d*deg;
         Card *:= FactoredOrder (Cent);
      else
         E<l> := ext<F | f: Optimize := false>;
         H := GL(deg, F);
         _, T := IsConjugate (H, H!CompanionMatrix (f)^-1, H!Star (CompanionMatrix (f)));
         if Determinant (T+sgn*Star (T)) eq 0 then
            T := CompanionMatrix (f)*T+sgn*Star (CompanionMatrix (f)*T);
         else
            T := T+sgn*Star (T);
         end if;
         T := T^-1;
         A1 := Submatrix (A, pos, pos, d*deg, d*deg);
         if p eq 2 and type ne "unitary" and type ne "symplectic" then
            A1 +:= Transpose (A1);
         end if;
         B1 := A1*DiagonalJoin ([T: j in [1..d]]);
         H1 := ZeroMatrix (E, d, d);
         // H1 = matrix B1 over the smaller field
         for j1, j2 in [1..d] do
            H1[j1, j2] := &+[l^(k-1)*B1[deg*(j1-1)+1, deg*(j2-1)+k]: k in [1..deg]];
         end for;
         m := TransformForm (H1, "unitary": Restore := false);
         y := IdentityMatrix (E, d);
         pos1 := 1;
         lm := l^-1;
         for j1 in c[i][2] do
            for j2 in [1..j1-1] do
               y[pos1, pos1+1] := lm;
               pos1 +:= 1;
            end for;
            pos1 +:= 1;
         end for;
         y := m^-1*y*m;
         if special and type eq "unitary" then
            MyH := SU(d, E); MyH`ClassicalType := "SU";
            Cent := InternalUnipotentCentralizer (MyH, GL(d, E)!y);
            S, GCD := ElementOfMaxDeterminant (y, StandardHermitianForm (d, E), IdentityMatrix (E, d), "unitary");
            S := m*S*m^-1;
            suss := BlockMatrix (d, d, [&+[CompanionMatrix (f)^(k-1)*Eltseq (S[j1, j2], F)[k]:
                      k in [1..deg]]: j1, j2 in [1..d]]);
            Append (~AddDeterminant, suss);
            // add an element having determinant 1 in SU(d*deg, F), but not in SU(d, E)
            alpha := (p^e+1) div Gcd (GCD, p^e+1);
            S := InsertBlock (Y, suss^alpha, pos, pos);
            Append (~SetGen, b1^-1*S*b1);
            Card *:= Factorization (p^(e*deg)+1);
            Card /:= Factorization (alpha*GCD);
         else
            MyH := GU(d, E); MyH`ClassicalType := "GU";
            Cent := InternalUnipotentCentralizer (MyH, GL(d, E)!y);
         end if;
         for j in [1..Ngens (Cent)] do
            S := m*Cent.j*m^-1;
            suss := BlockMatrix (d, d, [&+[CompanionMatrix (f)^(k-1)*Eltseq (S[j1, j2], F)[k]:
                      k in [1..deg]]: j1, j2 in [1..d]]);
            Y1 := InsertBlock (Y, suss, pos, pos);
            Y1 := b1^-1*Y1*b1;
            if special then
               if type ne "unitary" then
                  if Determinant (Y1) eq -1 then
                     Y1 *:= CorrectSp;
                  end if;
               end if;
            end if;
            Append (~SetGen, Y1);
         end for;
         pos +:= d*deg;
         Card *:= FactoredOrder (Cent);
      end if;
   end for;

   // add elements with determinant of the single blocks 
   // different from 1, but overall determinant 1
   if special and type eq "unitary" then
      R := Integers (q-1);
      ArrayDet := [Determinant (y): y in AddDeterminant];
      ArrayInv := [Log (w, y): y in ArrayDet];
      As := Matrix (R, #c, 1, [R!y: y in ArrayInv]);
      W := Matrix (R, 1, 1, [R!0]);
      _, _, K := IsConsistent (As, W);
      for k in Generators (K) do
         k1 := [Integers ()!ki: ki in Eltseq (k)];
         Y := DiagonalJoin (<AddDeterminant[i]^(k1[i]): i in [1..#c]>);
         Append (~SetGen, b1^-1*Y*b1);
      end for;
   end if;

   // correct generating set in Omega case:
   // if x is a generator for SO, then the set of generators for Omega contains:
   // x and z^-1xz (if x in Omega) or xz and z^-1x (if x not in Omega), 
   // with z = element in the centralizer of SO with spinor norm 1
   if IsOmega then
      Split := exists(z){y: y in SetGen | SpinN (GL(n, F)!y, Q, p) eq 1}; 
      if Split then
         SetGen1 := SetGen;
         SetGen := [Generic (G) | ];
         zm := z^-1;
         for y in SetGen1 do
	    if SpinN (GL (n, F)!y, Q, p) eq 0 then
               Append (~SetGen, y);
               Append (~SetGen, zm*y*z);
            else
               Append (~SetGen, zm*y);
               Append (~SetGen, y*z);
            end if;
         end for;
      end if;
   end if;

   // correcting cardinality in Special and Omega case
   if special then
      if type eq "unitary" then
         GCD := [Gcd (y[2] cat [p^e+1]): y in c];
         Card *:= Factorization (p^e+1)^(#c-1);
         Card /:= &*[Factorization (y): y in GCD];
         Card *:= Factorization (Gcd (GCD));
      end if;
   end if;
   if IsOmega then
      if Split then
         Card /:= SequenceToFactorization ([<2, 1>]);
      end if;
   end if;

   H := sub<GL(n, F) | SetGen>;
   H`FactoredOrder := Card;
   H`Order := Integers ()!Card;

   return H;
end function;

ValidTypes := {"SL", "GL", "Sp", "SU", "GU", "Omega+", "Omega-", "Omega",
	      "SO+", "SO-", "SO", "GO+", "GO-", "GO"};

intrinsic IsClassicalCentralizerApplicable(G::GrpMat, g::GrpMatElt) -> BoolElt
{Does the ClassicalCentralizer intrinsic function apply to this group}

    d := Degree (G); F := BaseRing (G);

    if Type(F) ne FldFin or (d eq 2 and #F le 4) then return false; end if;

    flag, type := ClassicalGroupType (G);

    if not flag or type notin ValidTypes or not MyIsIn(G,g: Add := {"SL", "GL"}) then return false; end if;

    even :=  Characteristic(F) eq 2;
    if type eq "GL" or (type eq "GO" and IsOdd(d) and even) then
       return false;
    end if;

    if even and type in
	{"Omega+", "Omega-", "Omega", "SO+", "SO-", "SO", "GO+", "GO-", "GO"}
    then
        if not IsIrreducible(G) then return false; end if;
	flag, form, form_type := QuadraticForm (G);
	V := QuadraticSpace (form);
	apply := DicksonInvariant (V, g) eq 0;
	if not apply then return false; end if;
    end if;

    return true;

end intrinsic;

intrinsic ClassicalCentralizer (G:: GrpMat, g::GrpMatElt) -> GrpMat 
{Centralizer of g in classical group G}
   require (Generic (Parent (g)) cmpeq Generic (G)): "Input element is not in group"; 
   // require g in G: "Element not in group";
   require MyIsIn (G, g: Add := {"GL", "SL"}): "Input element is not in group";

   if IsCentral (G, g) then return G; end if;

   d := Degree (G); F := BaseRing (G); 
   if d eq 2 and #F le 4 then return Centraliser (G, g); end if;
   flag, type := ClassicalGroupType (G);
   require flag and type in ValidTypes: "Type of group must be one of ", ValidTypes;
   
   if IsOdd (d) and IsEven (#F) and type eq "GO" then
      error "Function does not apply to this case";
   end if;

   if type in {"SL", "GL"} then 
      // EOB -- changed to Centralizer because it's faster
      // Yes .. but if G is NOT set up as GL(d, q) then Magma does not use Murray algorithm
      // so back to our implementation of GLCentraliser 
      return type eq "SL" select SLCentralizer (G, g) else GLCentralizer (G, g);
      // return type eq "SL" select SLCentralizer (G, g) else Centralizer (G, g);
   end if;

   CB := TransformMatrix (G);
   Gr := G^CB; Gr`ClassicalType := G`ClassicalType;
   if IsSemisimple (g) then 
      Z := SSCentralizer (Gr, g^CB); 
   elif IsUnipotent (g) then 
      Z := InternalUnipotentCentralizer (Gr, g^CB);
   else
      Z := GenCentralizer (Gr, g^CB);
   end if;
   return Z^(CB^-1);
end intrinsic;

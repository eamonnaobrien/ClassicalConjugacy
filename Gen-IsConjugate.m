freeze;

import "MaxDeterminant.m": ElementOfMaxDeterminant, ElementOfSpinorNorm1;
import "Gen-Centralizer.m": FixJordanForm;
import "linear/SL-IsConjugate.m": GLIsConjugate, SLIsConjugate;
import "semisimple/form.m": DetermineForm, IsElementOf, IndicateType, SpinN, ConjugatePolynomial;
import "semisimple/SS-IsConjugate.m": SSIsConjugate, SwitchMatrix;
import "size.m": MyIsIn;
import "Gen-Label.m": TransformMatrix;

// are g and h both semisimple or unipotent?
HaveSameType := function (g, h)
   if IsUnipotent (g) then 
      return IsUnipotent (h);
   elif IsSemisimple (g) then 
      return IsSemisimple (h); 
   end if;
   return true;
end function;

// do g and h have same label in the isometry group?  
// called only for mixed elements 

HaveSameLabel := function (G, g, h)
   flag, type := ClassicalGroupType (G);
   if type in {"GO",  "SO", "Omega"} then type := "GO"; end if;
   if type in {"GO+", "SO+", "Omega+"} then type := "GO+"; end if;
   if type in {"GO-", "SO-", "Omega-"} then type := "GO-"; end if;
   if type in {"GU",  "SU"} then type := "GU"; end if;
   return IsometryGroupClassLabel (type, g) eq IsometryGroupClassLabel (type, h);
end function;

// returns an element in the centralizer of a block with max determinant order
// case f not equal to f*
MatrixInCentralizerNE := function (F, f, pos, A1, d, deg, c3, type)
   e := type eq "unitary" select Degree (F) div 2 else 0;
   Star := func<M: exp := e | Transpose (FrobeniusImage (M, exp))>;

   E<l> := ext<F | f>;
   B1 := Submatrix (A1, pos, pos+d*deg, d*deg, d*deg);
   z := IdentityMatrix (E, d);
   lm := l^-1;
   pos1 := 1;
   for j1 in c3[2] do
      for j2 in [1..j1-1] do
         z[pos1, pos1+1] := lm;
         pos1 +:= 1;
      end for;
      pos1 +:= 1;
   end for;
   // z is the unipotent part (the centralizer is the same)
   y := ElementOfMaxDeterminant (z, c3[2], IdentityMatrix (E, d), "linear");
   suss := BlockMatrix (d, d, [&+[CompanionMatrix (f)^(k-1)*Eltseq (y[j1, j2], F)[k]:
               k in [1..deg]]: j1, j2 in [1..d]]);
   suss := DiagonalJoin (suss, Star (B1^-1*suss^-1*B1));

   return suss, Determinant (y);
end function;

// returns an element in the centralizer of a block with max determinant order
// case f=f*
MatrixInCentralizerEQ := function (F, f, pos, sgn, A1, d, deg, c3, type)

   e := type eq "unitary" select Degree (F) div 2 else 0;
   Star := func<M: exp := e | Transpose (FrobeniusImage (M, exp))>;

   E<l> := ext<F | f>;
   H := GL (deg, F);
   _, T := IsConjugate (H, H!CompanionMatrix (f)^-1, H!Star (CompanionMatrix (f)));
   if Determinant (T+sgn*Star (T)) eq 0 then
      T := CompanionMatrix (f)*T+sgn*Star (CompanionMatrix (f)*T);
   else
      T := T+sgn*Star (T);
   end if;
   T := T^-1;
   B2 := Submatrix (A1, pos, pos, d*deg, d*deg);
   B1 := B2*DiagonalJoin ([T: j in [1..d]]);
   H1 := ZeroMatrix (E, d, d);
   // H1 = matrix B1 over the smaller field
   for j1, j2 in [1..d] do
      H1[j1, j2] := &+[l^(k-1)*B1[deg*(j1-1)+1, deg*(j2-1)+k]: k in [1..deg]];
   end for;
   m := TransformForm (H1, "unitary": Restore := false);
   y := IdentityMatrix (E, d);
   lm := l^-1;
   pos1 := 1;
   for j1 in c3[2] do
      for j2 in [1..j1-1] do
         y[pos1, pos1+1] := lm;
         pos1 +:= 1;
      end for;
      pos1 +:= 1;
   end for;
   // y is the unipotent part (the centralizer is the same)
   y := m^-1*y*m;
   S := ElementOfMaxDeterminant (y, StandardHermitianForm (d, E), IdentityMatrix (E, d), "unitary");
   S := m*S*m^-1;
   suss := BlockMatrix (d, d, [&+[CompanionMatrix (f)^(k-1)*Eltseq (S[j1, j2], F)[k]:
              k in [1..deg]]: j1, j2 in [1..d]]);

   return suss, Determinant (S);
end function;

// return flag, _ or flag, z 
// flag = true if x2, x1 are conjugate in G, and z in G such that z^-1*x2*z = x1;
// works for G = Sp, GU, SU, GO, SO, Omega (in every basis)
// we exclude orthogonal groups in odd dimension and even characteristic

GenIsConjugate := function (G, x2, x1: Checks := true)
   if Checks then 
      if not HaveSameType (x2, x1) then return false, _; end if;
      if not HaveSameLabel (G, x2, x1) then return false, _; end if;
   end if;

   F<w> := BaseRing (G);
   n := Nrows (x1);
   e := Degree (F);
   p := Characteristic (F);
   sgn := 1;
   M := MatrixAlgebra (F, n);
   t := PolynomialRing (F).1;

   B, type, sgn, special, IsOmega, Q, is_abelian := DetermineForm (G, x1);
   if is_abelian then
//    if x2 notin G then
      if not MyIsIn (G, x2) then
         error "Element is not in input group";
      else    // trivial case
         if x1 eq x2 then
            return true, Identity (G);
         else
            return false, _;
         end if;
      end if;
   elif assigned Q then 
      special2, IsOmega2 := IsElementOf (G, x2, type, B, Q);
   else 
      special2, IsOmega2 := IsElementOf (G, x2, type, B, []);
   end if;
   if (special2 ne special) or (IsOmega2 ne IsOmega) then 
      error "Both elements do not lie in same input group";
   end if;

   e := type eq "unitary" select Degree (F) div 2 else 0;

   //conjugate transpose matrix
   Star := func<M: exp := e | Transpose (FrobeniusImage (M, exp))>;
   //conjugate polynomial
   ConjPol := ConjugatePolynomial (type eq "unitary");

   a1, b1, r1 := JordanForm (x1);
   a2, b2, r2 := JordanForm (x2);
   if a1 ne a2 then return false, _; end if;

   c := FixJordanForm (r1, t);

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
   c1 := c;
   c2 := c;

   _, bX, _ := JordanForm (X);
   d1 := bX^-1*b1;
   d2 := bX^-1*b2;
   if type ne "unitary" and type ne "symplectic" and p eq 2 then
      A1 := d1*Q*Star (d1);
      A2 := d2*Q*Star (d2);
   else
      A1 := d1*B*Star (d1);
      A2 := d2*B*Star (d2);
   end if;

   // method: compute an easy form X, d1 x1 d1^-1 = X = d2 x2 d2^-1. 
   // Thus X is isometry for A1, A2 defined above. Compute Y such that Y A2 Y* = A1. 
   // Then the conjugating element is d2^-1 Y^-1 d1.

   if type in {"orthogonalplus", "orthogonalminus", "orthogonal", "orthogonalcircle"} and p ne 2 then
      if Determinant (M!x1-1) eq 0 and Determinant (M!x1+1) eq 0 then
         k := &+c1[1][2];      // the first element in c1 is t-1 or t+1
         B1 := Submatrix (A1, 1, 1, k, k);
         B2 := Submatrix (A2, 1, 1, k, k);
         if not IsSquare (Determinant (B1)*Determinant (B2)) then
	    return false, _;
         end if;
      end if;
   end if;

   // turn the matrices A1, A2 into upper triangular matrices in quadratic case
   if type in {"orthogonalplus", "orthogonalminus", "orthogonal", "orthogonalcircle"} and p eq 2 then
      for i in [1..n] do
         for j in [i+1..n] do
            A1[i, j] +:= A1[j, i];
            A2[i, j] +:= A2[j, i];
            A1[j, i] := 0;
            A2[j, i] := 0;
         end for;
      end for;
   end if;

   PreserveElements := <>;

   // create conjugating element in GO / Sp / GU
   Y := ZeroMatrix (F, n, n);
   pos := 1;
   i := 1;
   while i le #c1 do
      f := c1[i][1];
      d := &+c1[i][2];
      deg := Degree (f);
      if f eq ConjPol (f) and Degree (f) eq 1 then
         B1 := Submatrix (A1, pos, pos, d, d);
         B2 := Submatrix (A2, pos, pos, d, d);
         type1 := type;
         if type ne "unitary" and type ne "symplectic" then
            type1 := IndicateType (B1);
         end if;
         m1 := TransformForm (B1, type1: Restore := false);
         m2 := TransformForm (B2, type1: Restore := false);
         if IsSemisimple (Submatrix (X, pos, pos, d, d)) then
            InsertBlock (~Y, m1*m2^-1, pos, pos);
         else
            Y1 := m1^-1*Submatrix (X, pos, pos, d, d)*m1;
            Y2 := m2^-1*Submatrix (X, pos, pos, d, d)*m2;
            case type1:
               when "orthogonalplus":
                  H := GOPlus(d, F); H`ClassicalType := "GO+";
               when "orthogonalminus":
                  H := GOMinus(d, F); H`ClassicalType := "GO-";
               when "orthogonal":
                  H := GO(d, F); H`ClassicalType := "GO";
               when "symplectic":
                  H := Sp(d, F); H`ClassicalType := "Sp";
               when "unitary":
                  H := GU(d, F); H`ClassicalType := "GU";
            end case;
            //  Y1 is not unipotent, but -ConstantCoefficient (f)^-1*Y1 is. Result z is the same
            vero, z := InternalUnipotentIsConjugate (H, Generic (H)!(-ConstantCoefficient (f)^-1*Y1), 
                                                        Generic (H)!(-ConstantCoefficient (f)^-1*Y2));
            if vero then
               z := m1*z*m2^-1;
               InsertBlock (~Y, z, pos, pos);
            else
               return false, _;
            end if;
         end if;
         pos +:= d;
      elif f ne ConjPol (f) then
         ni := Degree (f)*d;
         Y1 := Submatrix (A1, pos, pos+ni, ni, ni);
         Y2 := Submatrix (A2, pos, pos+ni, ni, ni);
         Y1 := Y1*Y2^-1;
         Y1 := DiagonalJoin (Y1, IdentityMatrix (F, ni));
         InsertBlock (~Y, Y1, pos, pos);
         pos +:= 2*ni;
      else
         ni := deg*d;
         R := CompanionMatrix (f);
         H := GL(Degree (f), F);
         _, T := IsConjugate (H, H!R^-1, H!Star (R));
         if Determinant (T+sgn*Star (T)) eq 0 then
            T := R*T+sgn*Star (R*T);
         else
            T := T+sgn*Star (T);
         end if;
         T := DiagonalJoin ([T: j in [1..d]]);
         B1 := Submatrix (A1, pos, pos, ni, ni)*T^-1;
         B2 := Submatrix (A2, pos, pos, ni, ni)*T^-1;
         if type ne "unitary" and type ne "symplectic" and p eq 2 then
            B1 +:= Transpose (Submatrix (A1, pos, pos, ni, ni))*T^-1;
            B2 +:= Transpose (Submatrix (A2, pos, pos, ni, ni))*T^-1;
         end if;
         if IsSemisimple (Submatrix (X, pos, pos, ni, ni)) then
            Y1 := SwitchMatrix (B1, B2, f);
            InsertBlock (~Y, Y1, pos, pos);
         else
            K<a> := ext<F | f>;
            s1 := ZeroMatrix (K, d, d);
            s2 := ZeroMatrix (K, d, d);
            for j1, j2 in [1..d] do
               s1[j1, j2] := &+[a^(k-1)*B1[deg* (j1-1)+1, deg*(j2-1)+k]: k in [1..deg]];
               s2[j1, j2] := &+[a^(k-1)*B2[deg* (j1-1)+1, deg*(j2-1)+k]: k in [1..deg]];
            end for;
            m1 := TransformForm (s1, "unitary": Restore := false);
            m2 := TransformForm (s2, "unitary": Restore := false);
            suss := ScalarMatrix (d, a);
            pos1 := 1;
            for c3 in c1[i][2] do
               for j in [1..c3-1] do
                  suss[pos1, pos1+1] := 1;
                  pos1 +:= 1;
               end for;
               pos1 +:= 1;
            end for;
            suss := a^-1*suss;      // so it becomes unipotent and z is the same
            MyH := GU(d, K); MyH`ClassicalType := "GU";
            _, z := InternalUnipotentIsConjugate (MyH, Generic (MyH)!(m1^-1*suss*m1), Generic (MyH)!(m2^-1*suss*m2));
            z := m1*z*m2^-1;
            Z := BlockMatrix (d, d, [&+[R^(k-1)*Eltseq (z[j1, j2], F)[k]: k in [1..deg]]: j1, j2 in [1..d]]);
            InsertBlock (~Y, Z, pos, pos);
         end if;
         pos +:= ni;
      end if;
      i +:= 1;
   end while;

   // in the special case, if det (Z) ne 1, then Z need to be multiplied by Y
   // such that x1 Y = Y x1 and det (Y) = det (Z)^-1
   Z := d2^-1*Y^-1*d1;
   if special or IsOmega then
      detZ := Determinant (Z);
      if detZ ne 1 then
         GCD := [Gcd (c3[2]): c3 in c1];
         if type eq "unitary" then
            det := detZ^-1;
            if Log (w^((p^e-1)*Gcd (Gcd (GCD), p^e+1)), detZ) eq -1 then      
               // the determinant of Y cannot be corrected to 1
               return false, _;
            end if;
            // ArrayElements contains elements in the centralizer of the 
            // el.div. with determinant not equal to 1
            ArrayElements := <>;
            pos := 1;
            for i in [1..#c1] do
               c3 := c1[i];
               f := c3[1];
               deg := Degree (f);
               d := &+c3[2];
               if f eq ConjPol (f) and deg eq 1 then
	          B1 := Submatrix (A1, pos, pos, d, d);
                  y := Submatrix (X, pos, pos, d, d)*(-ConstantCoefficient (f))^-1;
                  // y is the unipotent part (the centralizer is the same)
                  if d eq 1 then
                     Append (~ArrayElements, <w^(p^e-1)*IdentityMatrix (F, 1), w^(p^e-1)>);
                  else
                     m := TransformForm (B1, "unitary": Restore := false);
                     y := ElementOfMaxDeterminant (y, B1, m, "unitary");
                     Append (~ArrayElements, <y, Determinant (y)>);
                  end if;
                  pos +:= d;
               elif f ne ConjPol (f) then
                  suss, Dety := MatrixInCentralizerNE (F, f, pos, A1, d, deg, c3, type);
                  Append (~ArrayElements, <suss, Norm (Dety, F)^(1-p^e)> );
                  pos +:= 2*d*deg;
               else
		  suss, DetS := MatrixInCentralizerEQ (F, f, pos, sgn, A1, d, deg, c3, type);
                  Append (~ArrayElements, <suss, Norm (DetS, F)> );
                  pos +:= d*deg;
               end if;
            end for;
            R := Integers (p^e+1);
            SetLog := [R!(Log (w, y[2]) div (p^e-1)): y in ArrayElements];
            num := #ArrayElements;
            A := Matrix (R, num, 1, SetLog);
            W := Matrix (R, 1, 1, [Log (w, det) div (p^e-1)]);
            _, v := IsConsistent (A, W);
            Y := DiagonalJoin (<ArrayElements[i][1]^(Integers ()!v[1, i]): i in [1..num]>);
            Y := d1^-1*Y*d1;
            Z := Z*Y;
         else
            if c1[1][1] ne t-1 and c1[1][1] ne t+1 then
	       return false, _;
            else
               i := 1;
               pos := 1;
               split := false;
               if IsOdd (GCD[1]) then
                  split := true;
                  d := &+c1[1][2];
               else
                  if #GCD gt 1 and c1[2][1] in {t-1, t+1} and IsOdd (GCD[2]) then
                     split := true;
                     i := 2;
                     pos +:= &+c1[1][2];
                     d := &+c[2][2];
                  end if;
               end if;
               if split then
                  Y := IdentityMatrix (F, n);
                  B1 := Submatrix (A1, pos, pos, d, d);
                  y := Submatrix (X, pos, pos, d, d)*(-ConstantCoefficient (c[i][1]));
                  if IsOdd (d) then
                     y := -IdentityMatrix (F, d);
                  elif IsSquare ((F!-1)^(d div 2)*Determinant (B1)) then
                     m := TransformForm (B1, "orthogonalplus": Restore := false);
                     y, _, C := ElementOfMaxDeterminant (y, B1, m, "orthogonalplus");
                     C := <i, C, m>;
                  else
                     m := TransformForm (B1, "orthogonalminus": Restore := false);
                     y, _, C := ElementOfMaxDeterminant (y, B1, m, "orthogonalminus");
                     C := <i, C, m>;
                    // useful to preserve the value C and avoid to recompute it if IsOmega=true
                  end if;
                  InsertBlock (~Y, y, pos, pos);       // YX=XY, detY = -1
                  Y := d1^-1*Y*d1;
                  Z := Z*Y;
               else
                  return false, _;
               end if;
            end if;
         end if;
      end if;
   end if;

   // in the omega case, if SpinorNorm (Z) ne 0, then need to be multiplied by Y
   // such that x1 Y = Y x1 and SpinorNorm (Y) ne 0
   if IsOmega then
      if SpinN (GL(n, F)!Z, Q, p) ne 0 then
         if IsEven (p) then
            if c1[1][1] ne t+1 then
	       return false, _;
            else
               Y := IdentityMatrix (F, n);
               d := &+c1[1][2];
               B1 := Submatrix (A1, 1, 1, d, d);
               type1 := IndicateType (B1);
               if type1 eq "orthogonalplus" then
                  m := TransformForm (B1, "orthogonalplus": Restore := false);
                  minv := m^-1;
                  MyH := GOPlus(d, F); MyH`ClassicalType := "GO+";
                  Cent := InternalUnipotentCentralizer (MyH, GL(d, F)! (minv*Submatrix (X, 1, 1, d, d)*m));
               else
                  m := TransformForm (B1, "orthogonalminus": Restore := false);
                  minv := m^-1;
                  MyH := GOMinus(d, F); MyH`ClassicalType := "GO-";
                  Cent := InternalUnipotentCentralizer (MyH, GL(d, F)! (minv*Submatrix (X, 1, 1, d, d)*m));
               end if;
               split := false;
               for i in [1..Ngens (Cent)] do
                  if SpinN (m*Cent.i*minv, B1, p) eq 1 then
                     split := true;
                     InsertBlock (~Y, m*Cent.i*minv, 1, 1);
                     break i;
                  end if;
               end for;
               if split then
                  Y := d1^-1*Y*d1;
                  Z := Z*Y;
               else
                  return false, _;
               end if;
            end if;
         else
            split := false;
            Y := IdentityMatrix (F, n);
            // an element in DoesNotSplit is <y, SpinorNorm (y)>
            DoesNotSplit := <>;
            i := 1;
            pos := 1;
            while split eq false and i le #c1 do
               f := c1[i][1];
               d := &+c1[i][2];
               deg := Degree (f);
               if f eq t-1 or f eq t+1 then
                  B1 := Submatrix (A1, pos, pos, d, d);
                  s := -ConstantCoefficient (f);
                  X1 := s*Submatrix (X, pos, pos, d, d);
                  if true in {IsOdd (y): y in c1[i][2]} then
                     if {Multiplicity (c1[i][2], y): y in c1[i][2] | IsOdd (y)} ne {1} then
                        split := true;
                        if assigned (C) and C[1] eq i then
                           y := ElementOfSpinorNorm1 (X1, B1: special := true, C := C[2], m := C[3]);
                        else
                           y := ElementOfSpinorNorm1 (X1, B1: special := true);
                        end if;
                        InsertBlock (~Y, y, pos, pos);
                     else
                        if assigned (C) and C[1] eq i then
                           y, ThereIs := ElementOfSpinorNorm1 (X1, B1: C := C[2], m := C[3]);
                        else
                           y, ThereIs := ElementOfSpinorNorm1 (X1, B1);
                        end if;
                        if ThereIs then
                           if Determinant (y) eq 1 then
                              split := true;
                              InsertBlock (~Y, y, pos, pos);
                           else
                              Append (~DoesNotSplit, <y, 1>);
                           end if;
                        else
                           // in this case y has determinant -1 and Spinor Norm 0
                           Append (~DoesNotSplit, <y, 0>);
                        end if;
                     end if;
                  end if;
                  pos +:= d;
               else
                  if true in {IsOdd (y): y in c1[i][2]} then
                     split := true;
                     if f ne ConjPol (f) then
                        suss := MatrixInCentralizerNE (F, f, pos, A1, d, deg, c1[i], type);
                        InsertBlock (~Y, suss, pos, pos);
                     else
		        suss := MatrixInCentralizerEQ (F, f, pos, sgn, A1, d, deg, c1[i], type);
                        InsertBlock (~Y, suss, pos, pos);
                     end if;
                  else
                     if f ne ConjPol (f) then
                        pos +:= 2*d*deg;
                     else
                        pos +:= d*deg;
                     end if;
                  end if;
               end if;
               i +:= 1;
            end while;
            if split eq false and {y[2]: y in DoesNotSplit} eq {0, 1} then
               split := true;
               InsertBlock (~Y, DiagonalJoin (<y[1]: y in DoesNotSplit>), 1, 1);
            end if;
            if split then
               Y := d1^-1*Y*d1;
               Z := Z*Y;
            else
               return false, _;
            end if;
         end if;
      end if;
   end if;

   return true, GL (n, F)!Z;
end function;

ValidTypes := {"SL", "GL", "Sp", "SU", "GU", "Omega+", "Omega-", "Omega",
                  "SO+", "SO-", "SO", "GO+", "GO-", "GO"};

intrinsic IsClassicalIsConjugateApplicable
               (G::GrpMat, g::GrpMatElt, h::GrpMatElt) -> BoolElt
{Does the ClassicalIsConjugate intrinsic function apply to this group}

    d := Degree (G); F := BaseRing (G);

    if Type(F) ne FldFin or (d eq 2 and #F le 97) then return false; end if;

    flag, type := ClassicalGroupType (G);

    if not flag or type notin ValidTypes or
       not MyIsIn(G,g: Add := {"SL", "GL"}) or
       not MyIsIn(G,h: Add := {"SL", "GL"})
       then return false;
    end if;

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
	apply := DicksonInvariant (V, g) eq 0 and DicksonInvariant(V, h) eq 0;
	if not apply then return false; end if;
    end if;

    return true;

end intrinsic;

intrinsic ClassicalIsConjugate (G:: GrpMat, g:: GrpMatElt, h:: GrpMatElt) -> BoolElt, GrpMatElt
{If g and h are conjugate in classical group G, return true and 
 a conjugating element, else false}

   require Generic (Parent (g)) cmpeq Generic (G) and
           Generic (Parent (h)) cmpeq Generic (G): "Elements not in input group"; 
   require MyIsIn (G, g: Add := {"GL", "SL"}) 
       and MyIsIn (G, h: Add := {"GL", "SL"}): "Elements not in input group";

   if g eq h then return true, G.0; end if;
   if IsAbelian (G) then return false, _; end if;
   if Order (g) ne Order (h) then return false, _; end if;

   d := Degree (G); F := BaseRing (G);
   if d eq 2 and #F le 4 then return IsConjugate (G, g, h); end if;

   flag, type := ClassicalGroupType (G);
   require flag and type in ValidTypes: "Type of group must be one of ", ValidTypes;

   if IsOdd (d) and IsEven (#F) and type eq "GO" then
      error "Function does not apply to this case";
   end if;

   if type in {"SL", "GL"} then 
      if type eq "SL" then 
         flag, x := SLIsConjugate (G, g, h);
      else  
         flag, x := GLIsConjugate (G, g, h); 
      end if;
      if flag then return true, x; else return false, _; end if;
   end if;
   
   CB := TransformMatrix (G);
   Gr := G^CB; Gr`ClassicalType := G`ClassicalType;
   if (IsSemisimple (g) and IsSemisimple (h)) then
      flag, x := SSIsConjugate (Gr, g^CB, h^CB);
   elif (IsUnipotent (g) and IsUnipotent (h)) then 
      flag, x := InternalUnipotentIsConjugate (Gr, g^CB, h^CB);
   else
      flag, x := GenIsConjugate (Gr, g^CB, h^CB);
   end if;

   if flag then return true, x^(CB^-1); else return false, _; end if;
end intrinsic;

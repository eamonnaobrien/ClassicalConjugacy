freeze;

import "../size.m": GroupType, FormsReducibleCase;

MyIsSymplecticGroup := function (G) 
   if assigned G`ClassicalType then
      type := G`ClassicalType; 
      return type in {"Sp"};
   else 
      return IsSymplecticGroup (G);
   end if;
end function;

MyIsUnitaryGroup := function (G) 
   if assigned G`ClassicalType then
      type := G`ClassicalType; 
      return type in {"SU", "GU"};
   else 
      return IsUnitaryGroup (G);
   end if;
end function;

MyIsOrthogonalGroup := function (G) 
   if assigned G`ClassicalType then
      type := G`ClassicalType; 
      return type in {"GO", "GO+", "GO-", "SO", "SO-", "SO+", 
                       "Omega+", "Omega-", "Omega"};
   else
      nmr := 0; Limit := 5; flag := false;
      repeat 
         flag := IsOrthogonalGroup (G);
         nmr +:= 1;
      until flag or nmr gt Limit;
      return flag; 
   end if;
end function;

MyClassicalType := function (G) 
   flag, type := GroupType (G);
   if type in {"GO+", "SO+", "Omega+"} then return "orthogonalplus"; end if;
   if type in {"GO-", "SO-", "Omega-"} then return "orthogonalminus"; end if;
   if type in {"GO", "SO", "Omega"} then return "orthogonalcircle"; end if;
end function;

// SFC := system for coefficients
// given a polynomial f, returns a matrix A and a vector v 
// such that the vector w=vA^-1 is the vector of the coefficients
// of the matrix of the quadratic form preserved by 
// CompanionMatrix (f) as in FormForCompanionMatrix below

SFC := function (f)
   F := BaseRing (f);
   n := Degree (f);
   if f ne ReciprocalPolynomial (f) then
      error "f is not self-dual";
   end if;

   m := Degree (f) div 2;
   a := Coefficients (f);
   A := IdentityMatrix (F, m);
   A[1, 1] := 2;
   for i in [1..m-1] do
      for j in [1..m-i] do
         A[j, j+i] := a[i+1];
      end for;
   end for;
   V := VectorSpace (F, m);
   v := Zero (V);
   for i in [1..m] do
      v[i] := -a[i+1];
   end for;
   v[1] *:= 2;
   v[2] -:= 1;
   if IsEven (#F) then
      for j in [0..m-1] do
         A[j+1, 1] := &+[a[i]*a[m+i+j]: i in [1..m-j]];
      end for;
      v[1] := &+[a[i]*a[m+i-1]: i in [1..m+1]];
   end if;

   return A, v;
end function;

// given a form X (diagonal join of standard forms), return 
// the set of discriminants of the forms of odd dimension
// it is useful in the case "Omega", q odd
Discriminants := function (X)
   n := Nrows (X);
   F := BaseRing (X);
   Vect := [];
   for i in [1..n] do
      if X[i, i] ne 0 then
         t := 0;
         k := 1;
         while i+k le n and i-k ge 1 and X[i-k, i+k] ne 0 do
            t +:= 1;
            k +:= 1;
         end while;
         Append (~Vect, (-1)^t*X[i, i]/2);
      end if;
   end for;
   return Vect;
end function;

// given the element c of the Cartesian product (see end of code "fixed-ss.m"), 
// returns true if its class in SO splits into two classes in Omega
CheckSplitOmega := function (c, F, L)
   SplitPm := true;
   SplitDg := true;
   ExistsDg := false;
   ExistsPm := false;
   Discr := [];
   Answer := false;

   for i in [1..#c] do
      if L[i][3] eq 0 then
         ExistsPm := true;
         T := {Multiplicity (c[i][5], j): j in [1..L[i][2] by 2]};
         if T notin {{0}, {1}, {0, 1}} then
            SplitPm := false;
         elif T eq {0, 1} or T eq {1} then
            v := Discriminants (c[i][4]);
            setv := {IsSquare (F!x): x in v};
            if #setv eq 2 then
               SplitPm := false;
            else
               Append (~Discr, SetToSequence (setv)[1]);
            end if;
         end if;
      else
         ExistsDg := true;
         if IsOdd (c[i][5]) then
            SplitDg := false;
         end if;
      end if;
   end for;
   if #Discr eq 2 and Discr[1] ne Discr[2] then
      SplitPm := false;
   end if;

   if SplitPm and SplitDg then
      Answer := true;
   end if;

   return Answer;
end function;

// return TildeDualPolynomial if unitary eq true, DualPolynomial otherwise
ConjugatePolynomial := function (unitary)
   if unitary then
      return TildeDualPolynomial;
   else
      return DualPolynomial;
   end if;
end function;

// SpinorNorm is defined in different ways in odd and even char
SpinN := function (x, Q, p)
   if IsOdd (p) then
      V := QuadraticSpace (Q);
      return SpinorNorm (V, x);
   else
      return SpinorNorm (x, Q);
   end if;
end function;

// returns the orthogonal type of the form B
IndicateType := function (B)
   n := Nrows (B);
   F := BaseRing (B);
   if IsOdd (n) then
      return "orthogonal";
   end if;
   if IsOdd (#F) then
      if IsSquare ((F!-1)^(n div 2)*Determinant (B)) then
         return "orthogonalplus";
      else
         return "orthogonalminus";
      end if;
   else
      V := QuadraticSpace (B);
      if WittIndex (V) eq n div 2 then
         return "orthogonalplus";
      else
         return "orthogonalminus";
      end if;
   end if;
end function;

// given polynomial f and its companion matrix C, return B such that CBC*=B, 
// where B is hermitian, alternating, symmetric or quadratic
FormForCompanionMatrix := function (f, type)

   C := CompanionMatrix (f);
   F := BaseRing (C);
   n := Nrows (C);

   if n eq 1 then
      return IdentityMatrix (F, 1);
   end if;

   if type in {"GU", "SU"} then
      Gr := sub<GL(n, F)|C>;
      flag, q := IsSquare (#F);
      F0 := GF (q);
      MA := MatrixAlgebra (F, n);
      w := PrimitiveElement (F);

      M := GModule (Gr);
      mu := hom<F -> F | x :-> x^q>;
      D := SemilinearDual (M, mu);
      E := AHom (M, D);
      d := 0;
      while d eq 0 do
         x := Random (E);
         y := x+ConjugateTranspose (x, mu);
         d := Determinant (y);
         if d eq 0 then
            y := (w-mu (w))*(x-ConjugateTranspose (x, mu));
            d := Determinant (y);
         end if;
      end while;
   elif type eq "Sp" then
      c := [];
      deg := Nrows (C);
      h := deg div 2;
      for l in [1..h-1] do
         c[l] := C[deg, l+1];
         if l gt 1 then
            c[l] +:= &+[C[deg, j+1]*c[l-j]: j in [1..l-1]];
         end if;
      end for;
      Insert (~c, 1, 1);
      d := [];
      for i in [1..h] do
         d := d cat c;
         Prune (~c);
      end for;
      A := UpperTriangularMatrix (F, d);
      y := BlockMatrix (2, 2, [0, A, -Transpose (A), 0]);
   elif IsOdd (#F) then
      c := [];
      i := Nrows (C);
      h := i div 2;
      c := [1, C[i, 2]];
      if h eq 1 then
         c := [1, C[i, 2]/2];
      end if;
      if h gt 1 then
         c[3] := C[i, 2]*c[2]+C[i, 3]-1;
      end if;
      if h gt 2 then
         for l in [3..h] do
            c[l+1] := &+[C[i, j+1]*c[l-j+1]: j in [1..l]];
         end for;
      end if;
      Reverse (~c);
      c cat:= [0: v in [1..h-1]];
      d := [];
      for v in [1..i] do
         d := c cat d;
         Remove (~c, 1);
      end for;
      y := SymmetricMatrix (F, d);
   else
      if n eq 2 then
         y := Matrix (F, 2, 2, [1, C[2, 2], 0, 1]);
      else
         A, v := SFC (f);
         _, w := IsConsistent (A, v);
         m := n div 2;
         y := ZeroMatrix (F, n, n);
         for i in [1..m] do
            for j in [1..m+1-i] do
               y[j, j+m+i-1] := w[i];
            end for;
         end for;
         for i in [1..m+1] do
            y[i, i+m-1] := 1;
         end for;
      end if;
   end if;

   return y;
end function;

// check if x in G, a group of supplied type preserving
// sesquilinear form B and quadratic form Q; 
// also decide if the element is in SO or Omega 

IsElementOf := function (G, x, type, B, Q)
   F := BaseRing (G);
   p := Characteristic (F);
   n := Nrows (x);
   special := false;
   IsOmega := false;

   if type eq "unitary" then
      e := Degree (F) div 2;
      if x*B*Transpose (FrobeniusImage (x, e)) ne B then
         error "x must be in G";
      end if;
   elif type ne "symplectic" and p eq 2 then
      if x*B*Transpose (x) ne B or Diagonal (x*Q*Transpose (x)+Q) ne [0: i in [1..n]] then
         error "x must be in G";
      end if;
   elif x*B*Transpose (x) ne B then
      error "x must be in G";
   end if;

   // in orthogonal case, check if G is of special type or Omega type
   if #F ne 2 and (type eq "unitary" or (type ne "symplectic" and type ne "unitary" and p ne 2)) then
      special := forall{g : g in Generators (G) | Determinant (g) eq 1};
   end if;

   if type ne "unitary" and type ne "symplectic" and (special or p eq 2) then
      IsOmega := forall{g : g in Generators (G) | SpinN (g, Q, p) eq 0};
   end if;

   // check if x is in the special group G
   if special and Determinant (x) ne 1 then 
      error "x must be in G";
   end if;

   //check if x is in the Omega group G
   if IsOmega and SpinN (GL (n, F)!x, Q, p) ne 0 then
      error "x must be in G";
   end if;
   return special, IsOmega;
end function; 

// determine form and check that x is in G 
DetermineForm := function (G, x)
   IsAbelian := false;
   F := BaseRing (G);
   q := #F;
   p := Characteristic (F);
   n := Nrows (x);
   sgn := 1;
   e := 0;

   // compute form of G
   if MyIsSymplecticGroup (G) then
      sgn := F! (-1);
      _, B := SymplecticForm (G);
      type := "symplectic";
   elif Degree (G) eq 1 then             
      // unitary group of dimension 1
      type := "unitary";
      IsAbelian := true;
      B := StandardHermitianForm (1, F);
   elif q eq 4 and Degree (G) eq 2 and #G eq 3 then   
      // OmegaPlus (2, 4) treated apart (erroneously recognized by UnitaryForm)
      type := "orthogonalplus";
      Q := InvariantQuadraticForms (G)[1];
      IsAbelian := true;
      B := Q+Transpose (Q);
   elif q eq 9 and Degree (G) eq 2 and #G eq 4 then  
      // OmegaPlus (2, 9) treated apart (erroneously recognized by UnitaryForm)
      type := "orthogonalplus";
      Q := InvariantQuadraticForms (G)[1];
      IsAbelian := true;
      B := Q+Transpose (Q);
   elif MyIsUnitaryGroup (G) eq true then
      type := "unitary";
      _, B := UnitaryForm (G);
   elif MyIsOrthogonalGroup (G) then
      type := MyClassicalType (G);
      if not IsTrivial (G) and Degree (G) eq 2 and IsIrreducible (G) eq false then 
          flag, Q := FormsReducibleCase (G, type);
      else
         flag, Q := QuadraticForm (G);
      end if;
      assert flag;
      B := Q + Transpose (Q);
   elif Degree (G) eq 2 and #G eq 1 then  
      // OmegaPlus (2, 2), OmegaPlus (2, 3)
      type := "orthogonalplus";
      Q := StandardQuadraticForm (2, F);
      B := Q + Transpose (Q);
      IsAbelian := true;
   else
      error "G must be a classical group";
   end if;

   if assigned Q then 
      special, IsOmega := IsElementOf (G, x, type, B, Q);
      if (special or IsOmega) and Degree (G) eq 2 then
         IsAbelian := true;
      end if;
      return B, type, sgn, special, IsOmega, Q, IsAbelian;
   else 
      special, IsOmega := IsElementOf (G, x, type, B, []);
      return B, type, sgn, special, IsOmega, _, IsAbelian;
   end if;
end function;

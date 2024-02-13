freeze;

import "semisimple/form.m": IndicateType, SpinN;

// This code is needed for GenCentralizer.m. 
// We assume that input x is unipotent with a unique el.div.

// if type = "unitary", "orthogonalplus", "orthogonalminus"
// given an element x in the unitary group G with form B where 
// m := TransformForm (B, type);
// return an element of the centralizer of x in G with determinant of maximal order;
// returns also the centralizer of x in G, which saves later computations 

// if type := "linear"
// given a Jordan block x in G=GL(n, F), B = vector of sizes of the blocks
// where m = IdentityMatrix (F, n)
// return an element of the centralizer of x in G with determinant of maximal order;
// returns also GCD, which saves later computations 

ElementOfMaxDeterminant := function (x, B, m, type)
   assert IsUnipotent (x);

   F := BaseRing (x);
   n := Nrows (x);

   case type:
      when "linear":
         q := #F;
         R := Integers (q-1);
         w := PrimitiveElement (F);
         d := #B;
         A := Matrix (R, d, 1, B);
         GCD := Gcd (B cat [q-1]);
         W := Matrix (R, 1, 1, [GCD]);
         _, v := IsConsistent (A, W);
         y := IdentityMatrix (F, n);
         pos := 1;
         for i in [1..d] do
            for j in [1..B[i]] do
               y[pos, pos] := w^(Integers ()!v[1, i]);
               pos +:= 1;
            end for;
         end for;
         C := GL(n, F);         // this is useless
      when "unitary":
         _, q := IsSquare (#F);
         R := Integers (q+1);
         MyH := GU (n, F); MyH`ClassicalType := "GU";
         C := InternalUnipotentCentralizer (MyH, Generic (MyH)!(m^-1*x*m));
         w := PrimitiveElement (F);
         SetGen := SetToSequence (Generators (C));
         d := #SetGen;
         SetDet := [Determinant (y): y in SetGen];
         SetLog := [Log (w, y) div (q-1): y in SetDet];
         A := Matrix (R, d, 1, [R!y: y in SetLog]);
         GCD := Gcd (SetLog cat [q+1]);
         W := Matrix (R, 1, 1, [GCD]);
         _, v := IsConsistent (A, W);
         y := &*[SetGen[i]^ (Integers ()!v[1, i]): i in [1..d]];
      when "orthogonalplus", "orthogonalminus":
         q := #F;
         GCD := 2;
         if type eq "orthogonalplus" then
            MyH := GOPlus(n, q); MyH`ClassicalType := "GO+";
            C := InternalUnipotentCentralizer (MyH, GL(n, q)!(m^-1*x*m));
         else
            MyH := GOMinus(n, q); MyH`ClassicalType := "GO-";
            C := InternalUnipotentCentralizer (MyH, GL(n, q)!(m^-1*x*m));
         end if;
         if exists(i){i: i in [1..Ngens (C)] | Determinant (C.i) eq -1} then
            y := C.i;
            GCD := 1;
         else 
            y := C.1;
         end if;
   end case;

   return m*y*m^-1, GCD, C;
end function;

// If there exists an element y in the centralizer of x in GO 
// with spinor norm 1, then the code returns y, true. 
// If there are no elements of spinor norm 1, then the code returns y, false  
// where y is an element in the centralizer of x in GO with determinant -1 
// (if such exists) or 1.
// If special=true, then we search for the element only in SO.
// B is the form preserved by GO / SO.
// If C is not [], then it is the centralizer of x in GO.
// If m is not [], then it is result of TransformForm (x, type) 
// so we avoid recomputing it

ElementOfSpinorNorm1 := function (x, B: special := false, C := [], m := [])
   assert IsUnipotent (x);

   F := BaseRing (x);
   p := Characteristic (F);
   n := Nrows (x);
   type := IndicateType (B);
   if Type (m) eq SeqEnum then
      m := TransformForm (B, type: Restore := false);
   end if;
   X := m^-1*x*m;

   case type:
      when "orthogonalplus":
         G := GOPlus(n, F); G`ClassicalType := "GO+";
         Form := p eq 2 select StandardQuadraticForm (n, F) else StandardSymmetricForm (n, F);

      when "orthogonalminus":
         G := GOMinus(n, F); G`ClassicalType := "GO-";
         Form := p eq 2 select StandardQuadraticForm (n, F: Minus, Variant := "Default") 
                          else StandardSymmetricForm (n, F: Minus, Variant := "Default");

      when "orthogonal", "orthogonalcircle":
         if n ne 1 then
            G := GO(n, F); G`ClassicalType := "GO";
         end if;
         Form := p eq 2 select StandardQuadraticForm (n, F) else 
                               StandardSymmetricForm (n, F: Variant := "Default");
         // need this otherwise the spinor norm may be affected
         if B ne m*Form*Transpose (m) then
            Form *:= PrimitiveElement (F);
         end if;
   end case;

   if Type (C) eq SeqEnum then
      if n eq 1 then
         Cent := sub<GL(1, F)| -IdentityMatrix (F, 1)>;
      else
         Cent := InternalUnipotentCentralizer (G, Generic (G)!X);
      end if;
   else
      Cent := C;
   end if;
   done := exists(index) {i : i in [1..Ngens (Cent)] | SpinN (Cent.i, Form, p) eq 1};
   if done then y := Cent.index; end if;

   if not done then
      y := Identity (GL (n, F));
      if special or p eq 2 then
         return y, false;
      end if;
      done := exists(i) {i : i in [1..Ngens (Cent)] | Determinant (Cent.i) eq -1};
      if done then y := Cent.i; end if;
      return m*y*m^-1, false;
   end if;

   if Determinant (y) eq -1 then
      done := false;
      for i in [1..index-1] do
         if Determinant (Cent.i) eq -1 then
            y *:= Cent.i;
            done := true;
            break i;
         end if;
      end for;

      if not done then
         for i in [index+1..Ngens (Cent)] do
            z := Cent.i;
            det := Determinant (z);
            s := SpinN (z, Form, p);
            if det eq -1 and s eq 0 then
               y *:= z;
               done := true;
               break i;
            elif det eq 1 and s eq 1 then
               y := z;
               done := true;
               break i;
            end if;
         end for;
      end if;
   end if;

   if special and done eq false then
      return Identity (GL(n, F)), false;
   else
      return m*y*m^-1, true;
   end if;
end function;

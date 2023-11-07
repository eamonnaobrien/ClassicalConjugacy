freeze;

// construct V block of size 2k + ell where k is largest for g 
// ell = 1 for Orthogonal, ell = 0 for Sp
ConstructVBlock := function (g, form, k: Orthogonal := false) 
   K := BaseRing (Parent (g));
   q := #K;
   d := Nrows (g);
   if Orthogonal then
      V := QuadraticSpace (form);
   else 
      V := SymplecticSpace (form);
   end if;
   MA := MatrixAlgebra (GF(q), d);
   u := MA!g;

   ell := Orthogonal select 0 else 1;
   repeat
      v := Random (V);
   until DotProduct (v, v * (u - 1)^(2 * k - ell)) ne 0;

   basis := [v * u^i: i in [0..2*k - ell]];
   U := sub<V | basis>;
   assert IsNondegenerate (U);

   dim := Orthogonal select 2 * k + 1 else 2 * k;
   assert Dimension (U) eq dim;

   return U, V;
end function;

// construct W block of size 2(l + 1) where l is largest for g 
ConstructWBlock := function (g, form, l : Orthogonal := false)
   K := BaseRing (Parent (g));
   q := #K;
   d := Nrows (g);

   if Orthogonal then
      V := QuadraticSpace (form);
   else
      V := SymplecticSpace (form);
   end if;

   MA := MatrixAlgebra (GF(q), d);
   u := MA!g;

   repeat
      v := Random (V);
      w := Random (V);
   until DotProduct (v, w * (u - 1)^(l)) ne 0 and
         DotProduct (w, v * (u - 1)^(l)) ne 0;

   basis := &cat[[v * u^i, w * u^i]: i in [0..l]];
   U := sub<V | basis>;
   assert IsNondegenerate (U);
   assert Dimension (U) eq 2 * (l + 1);

   return U, V;
end function;

freeze;

import "../../util.m": ChooseAlpha;

// true: V(4) false V_alpha (4)
J4BlockTest := function (g, form)
   K := BaseRing (Parent (g));
   q := #K;
   d := Nrows (g);
   
   V := VectorSpace (K, d, form);
   MA := MatrixAlgebra (GF(q), d);
   u := MA!g;

   repeat
       v := Random (V);
   until DotProduct (v * (u - u^0), v * (u - u^0)^2) ne 0;

   B := [v * (u - u^0)^i: i in [0..3]];
   beta := DotProduct (B[2], B[3]);
   assert beta ne 0;
 
   gamma := DotProduct (B[1], B[2]);
   P<x> := PolynomialRing (GF(q));
   f := x^2 + x + beta^-1 * gamma;
   result := IsIrreducible (f) select ChooseAlpha (q) else K!0;
   return result;
end function;

ReduceToJ4 := function (g, form, k) 
   G := Parent (g);
   d := Nrows (g);
   K := BaseRing (G);
   q := #K;
   assert IsEven (q);
   
   V := VectorSpace (K, d, form);
   CS := V; 
   
   for i in [1..k - 2] do 
      CS := sub< V | [v - v * g: v in Basis (CS)]>;
   end for;
   
   N := CS;
   radN := Radical (N);
   B := Basis (radN);
   b := #B;
   SS := ExtendBasis (radN, N);
   
   BN := VectorSpaceWithBasis (SS);
   
   F := Zero (MatrixAlgebra (GF(q), #SS - b));
   for i in [b + 1..#SS] do
      for j in [b + 1..#SS] do
         F[i - b, j - b] := DotProduct (SS[i], SS[j]);
      end for;
   end for;
   
   M := [];
   for i in [#B + 1..#SS] do
      if #B eq 0 then 
         C := Eltseq (BN!(SS[i] * g));
      else
         C := Coordinates (BN, SS[i] * g);
      end if;
      c := [C[j]: j in [b + 1..Dimension (BN)]];
      Append (~M, c);
   end for;

   small_g := GL(#M, q) ! M;
   small_form := GL(#M, q) !F;
   return J4BlockTest (small_g, small_form);
end function;

// assume g is W3 block 
// 0: W(3) alpha W_alpha (3)

W3BlockTest := function (u, form)
   d := Nrows (u); F := BaseRing (u); q := #F;
   V := VectorSpace (F, d, form);
   MA := MatrixAlgebra (F, d);
   u := MA!u;
   I := Image ((u - u^0)^2);
   B := Basis (I);
   flag, A := IsConsistent ((u - u^0)^2, B);
   assert flag;

   v1 := V! A[1]; 
   v2 := V! (v1 * (u - 1)); 
   v3 := V! B[1];
   w1 := V! A[2];
   w2 := V! (w1 * (u - 1)); 
   w3 := V! B[2];

   gamma1 := InnerProduct (v2, w2);
   gamma2 := InnerProduct (v1, v2);
   gamma3 := InnerProduct (w1, w2);
   
   P<x>:= PolynomialRing (F);
   f := x^2 + gamma1 * x + gamma2 * gamma3;
   if IsIrreducible (f) then return ChooseAlpha (q); else return F!0; end if;
end function;

ReduceToW3 := function (g, form, l)
   G := Parent (g);
   d := Nrows (g);
   K := BaseRing (G);
   q := #K;
   assert IsEven (q);
   
   V := VectorSpace (K, d, form);
   CS := V; 
   
   for i in [1..l - 1] do 
      CS := sub< V | [v - v * g: v in Basis (CS)]>;
   end for;
   
   N := CS;
   radN := Radical (N);
   B := Basis (radN);
   b := #B;
   SS := ExtendBasis (radN, N);
   
   BN := VectorSpaceWithBasis (SS);
   
   F := Zero (MatrixAlgebra (GF(q), #SS - b));
   for i in [b + 1..#SS] do
      for j in [b + 1..#SS] do
         F[i - b,j - b] := DotProduct (SS[i], SS[j]);
      end for;
   end for;
   
   M := [];
   for i in [#B + 1..#SS] do
      if #B eq 0 then 
         C := Eltseq (BN! (SS[i] * g));
      else
         C := Coordinates (BN, SS[i] * g);
      end if;
      c := [C[j]: j in [b + 1..Dimension (BN)]];
      Append (~M, c);
   end for;

   small_g := GL(#M, q) ! M;
   small_form := GL(#M, q) !F;
   return W3BlockTest (small_g, small_form);
end function;

J2Test := function (u, form)
   d := Nrows (u); F := BaseRing (u);
   V := VectorSpace (F, d, form);
   MA := MatrixAlgebra (F, d);
   u := MA!u;
   I := Image (u - u^0);
   B := Basis (I);
   flag, A := IsConsistent (u - u^0, B);
   assert flag;

   B := [V!b: b in B];
   A := [V!a: a in A];
   if forall{i: i in [1..#A] | DotProduct (A[i], B[i]) eq 0} then
      return 0;
   else
      return 1; 
   end if;
end function;

// q even 
// general J2 test 

GeneralJ2Test := function (g, form, k: Perp := true)
   G := Parent (g);
   d := Nrows (g);
   K := BaseRing (G);
   q := #K;
   assert IsEven (q);
   
   V := VectorSpace (K, d, form);
   CS := V; 
   
   for i in [1..k - 1] do 
      CS := sub< V | [v - v * g: v in Basis (CS)]>;
   end for;
   
   N := Perp select OrthogonalComplement (V, CS) else CS;
   radN := Radical (N);
   B := Basis (radN);
   b := #B;
   SS := ExtendBasis (radN, N);
   
   BN := VectorSpaceWithBasis (SS);
   
   F := Zero (MatrixAlgebra (GF(q), #SS - b));
   for i in [b + 1..#SS] do
      for j in [b + 1..#SS] do
         F[i - b, j - b] := DotProduct (SS[i], SS[j]);
      end for;
   end for;
   
   M := [];
   for i in [b + 1..#SS] do
      if b eq 0 then 
         C := Eltseq (BN!(SS[i] * g));
      else
         C := Coordinates (BN, SS[i] * g);
      end if;
      c := [C[j]: j in [b + 1..Dimension (BN)]];
      Append (~M, c);
   end for;
   if #M eq 0 then return [], []; end if;
   small_g := GL(#M, q) ! M;
   small_form := GL(#M, q) !F;
   return small_g, small_form;
end function;

// does g has a V_{2k} block?

MatrixHasVBlock := function (g, form, k)
   u1, form1 := GeneralJ2Test (g, form, k: Perp := false);
   if Type (u1) eq SeqEnum then return 0; end if;

   // DOES THIS EVER DO ANYTHING?
   u2, form2 := GeneralJ2Test (u1, form1, 3: Perp := true);

   if Type (u2) eq SeqEnum then return 0; end if;
   return J2Test (u2, form2);
end function;

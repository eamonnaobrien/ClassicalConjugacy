freeze;

import "../../util.m": MyCommutatorSpace, FixesForm;

// Sp even char: W_n(0) blocks where n can be odd or even 

Eval_Poly1 := function (f, t, u, S)
   mat := 0 * t;
   C, M := CoefficientsAndMonomials (f);
   C := Evaluate (C, S);
   for i in [1..#M] do 
      c := C[i]; g := M[i];
      exp := Exponents (g);
      mat +:= c * t^exp[1] * u^exp[2];
   end for;
   return mat;
end function;

Eval_Poly := function (f, S)
   C, M := CoefficientsAndMonomials (f);
   E := Evaluate (C, S);
   if #E gt 0 then 
      f := &+[E[i] * M[i]: i in [1..#E]];
   else 
      f := 0;
   end if;
   return f;
end function;

Sp_W0_ConjugateElement := function (g, rep, form: Verify := false)
   SetupDelta := function (g)
      MA := MatrixAlgebra (BaseRing (g), Nrows (g));
      return MA!g - MA!g^0;
   end function;

   d := Degree (g);
   n := d div 2;
   q := #BaseRing (g);
   
   T := SetupDelta (g);
   mat_T := T;
   V := SymplecticSpace (form);
   CS := MyCommutatorSpace (V, V, [g]);
   U := &+[T^i:i in [1..(n - 1)]];
   mat_U := U;
   
   repeat
      x := Random (V); 
      w := Random (V); 
   until sub<V | CS, w, x> eq V and DotProduct (w, x * U^(n - 1)) ne 0;
   
   Alpha := [DotProduct (w, w * T^i): i in [1..(n - 1) div 2]];
   Beta := [DotProduct (x, x * U^i): i in [1..(n - 1) div 2]];
   Gamma := [DotProduct (w, x * U^i): i in [1..(n - 1)]];
   Gamma0 := DotProduct (w, x);
   IP := Alpha cat Beta cat [Gamma0] cat Gamma;
   
   if IsEven (n) then m := 2 * n - 2; else m := 2 * n - 1; end if;
   
   P := PolynomialRing (GF(q), m);
   
   if IsEven (n) then
      B := [P.i: i in [1..(n - 1) div 2]];
      C := [P.i: i in [(n - 1) div 2 + 1 .. (n - 2)]];
      D := [P.i: i in [n - 1 ..m]];
   else 
      B := [P.i: i in [1..(n - 1) div 2]];
      C := [P.i: i in [(n - 1) div 2 + 1 .. (n - 1)]];
      D := [P.i: i in [n ..m]];
   end if;
   
   Q<T, U> := PolynomialRing (P, 2);
   
   V := &+[T^i:i in [1..(n - 1)]];
   if IsEven (n) then 
      q_u := n gt 2 select &+[B[i] * U^(i - 1): i in [1..(n - 1) div 2]] else Zero (Q);
      q_t := n gt 2 select &+[C[i] * T^(2 * i - 1): i in [1..(n - 1) div 2]] else Zero (Q);
      d_u := &+[D[i] * U^(i - 1): i in [1..n]];
   else 
      q_u := &+[B[i] * U^(2 * (i - 1)): i in [1..(n - 1) div 2]];
      q_t := &+[C[i] * T^(2 * (i - 1)): i in [1..(n - 1) div 2]];
      d_u := &+[D[i] * U^(i - 1): i in [1..n]];
   end if;
   
   L := [];

   // Gamma
   RS := [];
   W := [ q_u * q_t * V^i + d_u * U^i: i in [0..(n - 1)]];
   for i in [1..#W] do
      aa, bb := CoefficientsAndMonomials (W[i]);
      two := [aa[i]: i in [1..#bb]| Degree (bb[i]) eq (n - 1)];
      Append (~RS, &+two);
   end for;
   Append (~L, RS);
   
   // Beta 
   W := [ d_u * q_t * V^i + q_t * d_u * U^i: i in [1..(n - 1) div 2]];
   RS := [];
   for i in [1..#W] do
      aa, bb := CoefficientsAndMonomials (W[i]);
      two := [aa[i]: i in [1..#bb]| Degree (bb[i]) eq (n - 1)];
      Append (~RS, &+two);
   end for;
   Append (~L, RS);
   
   // Alpha 
   W := [ q_u * V^i + q_u * U^i: i in [1..(n - 1) div 2]];
   RS := [];
   for i in [1..#W] do
      aa, bb:=CoefficientsAndMonomials (W[i]);
      two := [aa[i]: i in [1..#bb]| Degree (bb[i]) eq (n - 1)];
      Append (~RS, &+two);
   end for;
   Append (~L, RS);
   
   Reverse (~L);
   L := &cat (L);
   
   M := [L[i] + IP[i]: i in [1..#L]];
   
   I := Ideal (M);
   I := ChangeOrder (I, "grevlex");
   B := GroebnerBasis (I);
   
   assert IsZeroDimensional (I);
   if exists{x : x in B | Degree (x) ne 1} then 
      degs := [Degree (x): x in B];
      assert #[d: d in degs | d gt 1] eq 1;
      pos := [i: i in [1..#degs] | degs[i] gt 1];
      pos := pos[1];
      f := B[pos];
      assert Degree (f) eq 2;
      mon := Monomials (f);
      assert IsIrreducible (f) eq false;
      R<y> := PolynomialRing (GF(q));
      f := R!Reverse (Coefficients (f));
      roots := Roots (f);
      root := roots[1][1];
      Append (~M, mon[2] + root);
      I := Ideal (M);
      I := ChangeOrder(I, "grevlex");
      B := GroebnerBasis (I);
   end if;
   
   C := [Coefficients (b) : b in B];
   S := [GF(q) | ];
   for i in [1..#C] do 
      if #C[i] eq 2 then S[i] := C[i][2]; else S[i] := 0; end if; 
   end for;
   
   a := Eval_Poly (d_u, S);
   b := Eval_Poly (q_u, S);
   c := Eval_Poly (q_t, S);
   poly_M := a + b * c;
   
   mat_M := Eval_Poly1 (poly_M, mat_T, mat_U, S);
   mat_q_t := Eval_Poly1 (q_t, mat_T, mat_U, S);
   mat_q_u := Eval_Poly1 (q_u, mat_T, mat_U, S);
   
   xmq := (w * mat_q_t + x) * mat_M^-1;
   wmq := w + xmq * mat_q_u;
   
   B := [wmq * mat_T^i: i in [0..n - 1]] cat [xmq * mat_U^i: i in [0..n - 1]]; 
   
   CB := GL(d, q) ! [Eltseq (x): x in B];
   if Verify then 
      assert CB * g * CB^-1 eq rep;
      assert FixesForm (CB, form);
   end if;
   return true, CB;
end function;

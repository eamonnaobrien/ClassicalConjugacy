freeze;

import "../../central/odd-sp.m": SpParameters, Sp_ClassRep;
import "../../util.m": CayleyTransform, MyCommutatorSpace, FixesForm, MySort, MyDiagonalJoin;
import "basics.m": RestrictToSpace, SpOConstructCB, MyPullback;
import "blocks.m": ConstructVBlock, ConstructWBlock;

forward SpSetupSpecialRep;

// Sp odd characteristic: conjugation  

// equations to solve for one block case 
Sp_OneBlock_SolveEquations := function (n, q, Alpha, beta)

   epsilon := (-1)^n;
   A := [GF(q) ! 0 : i in [1..2 * n - 1]];
   
   for i in [1..(n - 1) div 2] do
      I := [<j, 2 * i - j>: j in [2 .. i by 2]];
      lhs := epsilon * Alpha[2 * n - 2 * i - 1];
      sum := 0;
      for j in [1..#I] do
         X := I[j]; x := X[1]; y := X[2];
         if j eq #I and x eq y then fac := 1; else fac := 2; end if;
         sum +:= fac * A[x] * A[y];
      end for;
      A[2 * i] := (lhs - sum) / 2;
   end for;
   
   for j in [n div 2..1 by -1] do
      I := [<i, 2 * n - 2 * j - i>: i in [2..n - j by 2]];
      lhs := epsilon * Alpha[2 * j - 1];
      sum := 0;
      for i in [1..#I] do
         X := I[i]; x := X[1]; y := X[2];
         if x ge n - 2 * j + 1 then fac := beta; else fac := 1; end if;
         if i ne #I or (i eq #I and x ne y) then fac := 2 * fac; end if;
         sum +:= fac * A[x] * A[y];
      end for;
      A[2 * n - 2 * j] := (lhs - sum) / 2;
   end for;
   
   return A;
end function;

// r is special rep for one block in Sp fixing form f and has parameter beta;
// u is conjugate in Sp to r; return conjugating element 

Sp_OneBlock_ConjugationMatrix := function (r, f, beta, u: Verify := false)

   d := Degree (u);
   n := d div 2;

   F := BaseRing (u);
   epsilon := F!(-1)^n;
   q := #F;

   V := SymplecticSpace (f);
   CS := MyCommutatorSpace (V, V, [u]);
   T := CayleyTransform (u);
   repeat v1 := Random (V); until not v1 in CS;
   alpha := DotProduct (v1, v1 * T^(2*n-1) / beta); 
   v1 := SquareRoot (alpha^-1 * epsilon) * v1;
   assert DotProduct (v1, v1 * T^(2*n-1) / beta) eq epsilon;

   Alpha := [];
   for i in [1..(n - 1) div 2] do
      Alpha[2*n -2*i - 1] := DotProduct (v1, v1 * T^(2*n - 2 * i - 1) / beta);
   end for;
   for j in [1..n div 2] do
      Alpha[2*j - 1] := DotProduct (v1, v1 * T^(2*j - 1)); 
   end for;

   A := Sp_OneBlock_SolveEquations (n, q, Alpha, beta);

   if n gt 2 then 
      M := &+[A[i] * T^i: i in [1..n - 1] | IsEven (i)]
         + &+[A[i] * T^i / beta: i in [n..#A] | IsEven (i)];
   elif n eq 2 then 
      M := &+[A[i] * T^i / beta: i in [n..#A] | IsEven (i)];
   else
      M := Zero (MatrixAlgebra (F, d));
   end if;

   M := M^0 + M;
   assert Determinant (M) ne 0;

   vm := v1 * M^-1;

   VM := [vm * T^i: i in [0..n - 1]] cat 
         [vm * T^(n + i) / beta : i in [0..n-1]];

   CB := GL(d, q) ! [Eltseq (x): x in VM];
   if Verify then 
      assert CB * u * CB^-1 eq r;
      assert FixesForm (CB, f);
      B := DotProductMatrix (VM);
      assert B eq f;
   end if;

   return CB;
end function;

// equations to solve for two block case 
Sp_TwoBlocks_SolveEquations := function (Alpha, Beta, Gamma, k, q)

   epsilon := (-1)^k;
   A := [GF (q) ! 0 : i in [1..2*k]];
   B := [GF (q) ! 0 : i in [1..2*k]];
   C := [GF (q) ! 0 : i in [1..2*k]];

   A0 := epsilon * Gamma[2 * k + 1];

   for i in [1..2*k - 1 by 2] do 
      A[2*k - i] := -epsilon * Gamma[i + 1];
      C[2*k - i] := -1/2 * epsilon * Beta[i];
   end for;

   for i in [1..k] do
      if i gt 1 then 
         B[2 * i - 1] := (epsilon * Alpha[2*k - (2 * i - 1)] - 
          2 * &+[A[2 * j] * B[2 * i - 2 * j - 1]: j in [1..i - 1]]) / (2 * A0);
      else 
         B[2 * i - 1] := (epsilon * Alpha[2*k - (2 * i - 1)]) / (2 * A0);
      end if;
      A[2 * i] := epsilon * Gamma[2 * k - 2 * i + 1] -  
                &+[B[2 * j - 1] * C[2*i - 2 * j + 1]: j in [1..i]];
   end for;
   return A0, A, B, C;
end function;

// r is special rep for one block in Sp fixing form f 
// u is conjugate in Sp to r; return conjugating element 

Sp_TwoBlocks_ConjugationMatrix := function (r, f, u: Verify := false)

   if r eq u then return r^0; end if;

   d := Degree (u);
   n := d div 2;
   assert IsOdd (n); // otherwise we can reduce to 1 block
   k := (n - 1) div 2;

   F := BaseRing (u);
   q := #F;
   
   V := SymplecticSpace (f);
   CS := MyCommutatorSpace (V, V, [u]);
   T := CayleyTransform (u);
   repeat 
      repeat v1 := Random (V); until not v1 in CS;
      repeat w1 := Random (V); until not w1 in CS;
   until sub<V | CS, v1, w1> eq V;
   
   Alpha := [];
   for i in [1..2 * k - 1] do
      Alpha[i] := DotProduct (v1, v1 * T^i);
   end for;
   
   Beta := [];
   for j in [1..2 * k - 1] do
      Beta[j] := DotProduct (w1, w1 * T^j); 
   end for;
   
   Gamma := [];
   for j in [0..2 * k] do
      Gamma[j + 1] := DotProduct (v1, w1 * T^j); 
   end for;

   A0, A, B, C := Sp_TwoBlocks_SolveEquations (Alpha, Beta, Gamma, k, q);
   
   MA :=  &+[A[i] * T^i: i in [1..2 * k]];
   MA := A0 * MA^0 + MA;
   assert Determinant (MA) ne 0;
   
   MB :=  &+[B[i] * T^i: i in [1..2 * k by 2]];
   MC :=  &+[C[i] * T^i: i in [1..2 * k by 2]];
   
   v := (v1 - w1 * MB) * (MA - MC*MB)^-1;
   w := (w1 - v * MC);
   
   VM := [v * T^i: i in [0.. 2 * k]];
   WM := [w * T^i: i in [0.. 2 * k]];
   
   MA := MatrixAlgebra (GF(q), 2 * k + 1);
   CB := SpOConstructCB (VM, WM, d, q);

   if Verify then 
      assert CB * u * CB^-1 eq r;
      assert FixesForm (CB, f);
   end if;
   
   return CB;
end function;

SpOddDecomposition := function (g, form, L)
   Beta := SpParameters (g, form);
   V := SymplecticSpace (form);
   Dim := [Beta[i][1]: i in [1..#Beta]];
   Beta := [Beta[i][2]: i in [1..#Beta]];
   max, pos := Maximum (Dim);
   beta := Beta[pos];

   if IsEven (max) then 
      k := max div 2;
      repeat 
         VB := ConstructVBlock (g, form, k);
         gV, formV := RestrictToSpace (g, form, VB);
         par := SpParameters (gV, formV);
      until par[1][2] eq beta;
      P := OrthogonalComplement (V, VB);
      Append (~L, <gV, formV, VB, P, V>);
   else
      l := max - 1;
      WB := ConstructWBlock (g, form, l);
      gW, formW := RestrictToSpace (g, form, WB);
      P := OrthogonalComplement (V, WB);
      Append (~L, <gW, formW, WB, P, V>);
   end if;
   
   if Dimension (P) gt 0 then 
      gP, formP := RestrictToSpace (g, form, P);
      return $$ (gP, formP, L);
   end if;
   
   return L;
end function;

SpOrganiseBasis := function (U: VBlock := true)
   n := Dimension (U);
   k := n div 2;
   B := HyperbolicSplitting (U);
   B := B[1];
   first := [B[i][1]: i in [1..k]]; 
   if VBlock eq true then 
      second := [(-1)^(k - i + 1) * B[i][2]: i in [1..k]]; 
   else 
      second := [(-1)^((k - i) div 2) * B[i][2]: i in [1..k]]; 
   end if;
   Reverse (~second);
   return first cat second;
end function;

SpChooseBasis := function (g, form, types) 
   spaces := SpOddDecomposition (g, form, [* *]);
   spaces := MyPullback (g, form, spaces);
   d := Nrows (form);
   F := BaseRing (form);
   CB := [* *];
   for i in [1..#spaces] do 
      C := SpOrganiseBasis (spaces[i]: VBlock := types[i]);
      Append (~CB, C);
   end for;
   CB := [x : x in CB];
   CB := &cat (CB);
   M := GL(d, F) ! Matrix (CB);
   assert FixesForm (M, form); 
   return M, [Dimension (x): x in spaces];
end function;

SpConjugateBlock := function (g, h, form: OneBlock := true)
   Beta := SpParameters (g, form);
   Beta_h := SpParameters (h, form);
   if Beta ne Beta_h then return false, _; end if;

   beta := [Beta[i][2]: i in [1..#Beta]];
   r := SpSetupSpecialRep (g, form); 

   if OneBlock then 
      beta := beta[1];
      C1 := Sp_OneBlock_ConjugationMatrix (r, form, beta, g);
      C2 := Sp_OneBlock_ConjugationMatrix (r, form, beta, h);
   else
      C1 := Sp_TwoBlocks_ConjugationMatrix (r, form, g);
      C2 := Sp_TwoBlocks_ConjugationMatrix (r, form, h);
   end if;

   return true, C1^-1 * C2; 
end function;

SpConjugateBlocks := function (g, h, form, blocks, types)
   F := BaseRing (g);
   Conj := <>;
   for i in [1..#blocks] do
      offset := i eq 1 select 0 else &+[blocks[j]: j in [1..i - 1]]; 
      r := blocks[i];
      J := ExtractBlock (form, offset + 1, offset + 1, r, r);
      V := SymplecticSpace (J);
      block_g := GL(r, F) ! ExtractBlock (g, offset + 1, offset + 1, r, r);
      block_h := GL(r, F) ! ExtractBlock (h, offset + 1, offset + 1, r, r);
      flag, one := SpConjugateBlock (block_g, block_h, J: OneBlock := types[i]);
      if not flag then return false, _; end if;
      Append (~Conj, one);
   end for;

   d := &+blocks;
   return true, GL(d, F) ! DiagonalJoin (Conj);
end function;

SpSetupSpecialRep := function (g, form) 
   F := BaseRing (g);
   q := #F;
   L := SpOddDecomposition (g, form, [* *]);
   R := [* *];
   Dim := [];
   for i in [1..#L] do 
      a := L[i][1]; fa := L[i][2];
      Beta := SpParameters (a, fa);
      dim := [Beta[i][1]: i in [1..#Beta]];
      beta := [Beta[i][2]: i in [1..#Beta]];
      J, CB, b := JordanForm (a);
      s := [b[i][2]: i in [1..#b]];
      m := [<x, #[y: y in s | y eq x]>: x in Set (s)];
      m := MySort (m);
      r, fr, cc, dd, ee := Sp_ClassRep (m, q, beta);
      assert FixesForm (r, fr);
      Append (~R, <r, fr>);
      Append (~Dim, dim);
   end for;
   new_rep := MyDiagonalJoin ([* R[i][1]: i in [1..#R] *]);
   new_form := MyDiagonalJoin ([* R[i][2]: i in [1..#R] *]);
   assert FixesForm (new_rep, new_form);
   return new_rep, new_form, &cat (Dim);
end function;

SpDecideConjugacy := function (G, g, h) 
   flag, form := SymplecticForm (G);
   if not flag then error "G is not symplectic"; end if;

   new_rep, new_form, Dims := SpSetupSpecialRep (g, form);
   A := TransformForm (form, "symplectic");
   B := TransformForm (new_form, "symplectic");
   C := (A * B^-1)^-1;
   C := Generic (G) ! C;

   g := g^(C^-1);
   h := h^(C^-1);

   types := [IsEven (Dims[i]): i in [1..#Dims]];

   CA, Sg := SpChooseBasis (g, new_form, types);
   new_g := CA * g * CA^-1;

   CB := SpChooseBasis (h, new_form, types);
   new_h := CB * h * CB^-1;

   flag, X := SpConjugateBlocks (new_g, new_h, new_form, Sg, types);
   if not flag then return false, _; end if;

   conj := Generic (G) ! (C^-1 * CB^-1 * X^-1 * CA * C);
   return true, conj^-1;
end function;

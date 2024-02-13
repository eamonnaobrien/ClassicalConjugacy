freeze;

import "../../util.m": MyCommutatorSpace, FixesForm, MySort, MyDiagonalJoin, CayleyTransform;
import "../../central/odd-orthogonal.m": OrthogonalParameters, GO_ClassRep;
import "basics.m": RestrictToSpace, SpOConstructCB, MyPullback;
import "blocks.m": ConstructVBlock, ConstructWBlock;

forward GOSetupSpecialRep; 

// Orthogonal odd characteristic: conjugation  

// equations to solve for one block case 
GO_OneBlock_SolveEquations := function (n, q, Alpha, alpha0, beta)

   epsilon := (-1)^n;
   A := [GF (q) | ];

   if IsEven (n) then 
      A[1] := Alpha[n - 1] / (2 * epsilon * beta);
 
      for i in [n - 2..n div 2 + 1 by -1] do
         A[n-i] := (Alpha[i] / (epsilon * beta) - &+[A[j] * A[n - i - j]: 
                                              j in [1..n - i -1]]) / 2;
      end for;

      if n gt 2 then 
         A[n div 2] := (epsilon * Alpha[n div 2] / beta - &+[A[j] * A[n div 2 - j]: 
                                              j in [1..n div 2 - 1]]) / 2;
         A[n div 2 + 1] := (epsilon * Alpha[n div 2 - 1] - 
              beta * &+[A[j] * A[n div 2 + 1 - j]: j in [1..n div 2]]) / 2;
      else 
         A[n div 2] := (epsilon * Alpha[n div 2]) / (2 * beta);
         A[n div 2 + 1] := (epsilon * alpha0 - 
              beta * &+[A[j] * A[n div 2 + 1 - j]: j in [1..n div 2]]) / 2;
      end if;

      for i in [(n div 2 - 2)..1 by -1] do
         A[n-i] := (epsilon * Alpha[i] - 
                 2 * &+[A[j] * A[n - i - j]: j in [1..n div 2 - i - 1]] - 
            beta * &+[A[j] * A[n - i - j]: j in [n div 2 - i .. n div 2]]) / 2;
      end for;

      if n gt 2 then 
         A[n] := (epsilon * alpha0 - 
                 2 * &+[A[j] * A[n - j]: j in [1..n div 2 - 1]] - 
              beta * &+[A[j] * A[n - j]: j in [n div 2 ]]) / 2;
      else 
         A[n] := (epsilon * alpha0 - 
              beta * &+[A[j] * A[n - j]: j in [n div 2 ]]) / 2;
      end if;

   elif n gt 1 then 
      A[1] := Alpha[n - 1] / (2 * epsilon * beta);
 
      for i in [n - 2 .. (n + 1) div 2 by -1] do
         A[n-i] := (Alpha[i] / (epsilon * beta) - &+[A[j] * A[n - i - j]: 
                                                   j in [1..n - i -1]]) / 2;
      end for;

      i := (n - 1) div 2;
      A[(n + 1) div 2] := (Alpha[(n - 1) div 2]/epsilon - 
           beta * (&+[A[j] * A[n - i - j]: j in [1..(n - 1) div 2]])) / 2;
   
      for i in [(n - 1) div 2 - 1 .. 1 by -1] do 
         A[n - i] := (Alpha[i] / epsilon -
                2 * &+[A[j] * A[n - i - j]: j in [1..(n - 1) div 2 - i]] - 
             beta * &+[A[j] * A[n - i - j]: j in [(n + 1) div 2 - i .. (n - 1) div 2]]) / 2;
      end for;
 
      A[n] := (alpha0 / epsilon - 2 * &+[A[j] * A[n - j]: j in [1..(n - 1) div 2]]) / 2;
   else
      assert n eq 1;
      A[1] := alpha0 / (2 * epsilon);
      return A;
   end if;

   return A;
end function;

// r is special rep for one block in GO fixing form f and has parameter beta;
// u is conjugate in GO to r; return conjugating element 

GO_OneBlock_ConjugationMatrix := function (r, f, beta, u: Verify := false)

   d := Degree (u);
   n := d div 2;

   epsilon := (-1)^n;
   F := BaseRing (u);
   q := #F;

   V := QuadraticSpace (SymmetricToQuadraticForm (f));
   CS := MyCommutatorSpace (V, V, [u]);
   T := CayleyTransform (u);
   repeat 
      repeat v1 := Random (V); until not v1 in CS;
   until DotProduct (v1, v1 * T^(2*n) / beta) eq epsilon;

   Alpha := [];
   for i in [1..n - 1] do
      Alpha[i] := DotProduct (v1, v1 * T^(2 * i));
   end for;
   alpha0 := DotProduct (v1, v1);
   A := GO_OneBlock_SolveEquations (n, q, Alpha, alpha0, beta);

   if n gt 1 then 
      M := &+[A[i] * T^(2*i): i in [1..n div 2]] +
           &+[A[i] * T^(2*i) / beta: i in [n div 2 + 1..n]]; 
   else
      M := &+[A[i] * T^(2*i) / beta: i in [n div 2 + 1..n]]; 
   end if;

   M := M^0 + M;
   assert Determinant (M) ne 0;

   vm := v1 * M^-1;

   VM := [vm * T^i: i in [0..n]] cat 
         [vm * T^(n + i) / beta : i in [1..n]];

   CB := GL(d, q) ! [Eltseq (x): x in VM];

   if Verify then 
      assert CB * u * CB^-1 eq r;
      B := MatrixAlgebra (F, d) ! [DotProduct (VM[i], VM[j]):  j in [1..d], i in [1..d]];
      assert B eq f;
   end if;

   return CB, VM;
end function;

// solutions of equations for two block case 

GO_TwoBlocks_SolveEquations := function (Alpha, Beta, Gamma, k, q)

   Epsilon := [(-1)^(k - i): i in [0..2 * k]];

   C := [GF(q) | ];
   for j in [1..k] do
      C[j] := Beta[k - j + 1] / (2 * Epsilon[2*j - 1 + 1]);
   end for;

   A := [GF(q) | ];
   for j in [1..2*k - 1 by 2] do
      A[j] := Gamma[2*k - 1 - j + 1] / Epsilon[j + 1];
   end for;

   A0 := Gamma[2*k - 1 + 1] / Epsilon[0 + 1];
   B := [GF (q) | ];
   B[1] := Alpha[k - 1 + 1] / (2 * A0 * Epsilon[0 + 1]);
   
   for index in [1..k - 1] do 
      i := 2*index;
      if i lt 2 * k then 
         A[i] := Gamma[2*k - 1 - i + 1] * Epsilon[i + 1] -
                 (&+[B[j] * C[i div 2 + 1 - j] * Epsilon[2*k - 2 * j + 1] * Epsilon[i + 1]: j in [1..i div 2]]);
      end if;
      i := index + 1;
      B[i] := (Alpha[k - i + 1] * Epsilon[0 + 1]) / (2 * A0) -
              (&+[A[2 * j] * B[i - j] * Epsilon[2*j + 1] * Epsilon[0 + 1]: j in [1..i - 1]]) / A0;
   end for;

   return A0, A, B, C;
end function;

// r is special rep for two blocks in GO fixing form f 
// u is conjugate in GO to r; return conjugating element 

GO_TwoBlocks_ConjugationMatrix := function (r, f, u: Verify := false)

   d := Degree (u);
   n := d div 2;
   assert IsEven (n); // otherwise we can reduce to 1 block
   k := n div 2;
   
   F := BaseRing (u);
   q := #F;
   
   V := QuadraticSpace (SymmetricToQuadraticForm (f));
   CS := MyCommutatorSpace (V, V, [u]);
   T := CayleyTransform (u);
   repeat 
      repeat v1 := Random (V); until not v1 in CS;
      repeat w1 := Random (V); until not w1 in CS;
   until sub<V | CS, v1, w1> eq V;
   
   Alpha := [];
   for i in [0..k - 1] do
      Alpha[i + 1] := DotProduct (v1, v1 * T^(2 * i));
   end for;
   
   Beta := [];
   for j in [0..k - 1] do
      Beta[j + 1] := DotProduct (w1, w1 * T^(2 * j)); 
   end for;
   
   Gamma := [];
   for j in [0..2 * k - 1] do
      Gamma[j + 1] := DotProduct (v1, w1 * T^j); 
   end for;
   
   A0, A, B, C := GO_TwoBlocks_SolveEquations (Alpha, Beta, Gamma, k, q);

   MA :=  A0 * T^0 + &+[A[i] * T^i: i in [1..2 * k - 1]];
   assert Determinant (MA) ne 0;
   MB :=  &+[B[i] * T^(2*i - 1): i in [1..k]];
   MC :=  &+[C[i] * T^(2*i - 1): i in [1..k]];
   
   v := (v1 - w1 * MB) * (MA - MC*MB)^-1;
   w := (w1 - v * MC);
   
   VM := [v * T^i: i in [0.. 2 * k - 1]];
   WM := [w * T^i: i in [0.. 2 * k - 1]];
   
   CB := SpOConstructCB (VM, WM, d, q);
   assert CB * u * CB^-1 eq r;

   if Verify then 
      assert CB * u * CB^-1 eq r;
      assert FixesForm (CB, f);
   end if;
   
   return CB;
end function;

SQF := SymmetricToQuadraticForm;

GO_Odd_Decomposition := function (g, form, L)

   Beta := OrthogonalParameters (g, form);
   V := QuadraticSpace (SymmetricToQuadraticForm (form));
   Dim := [Beta[i][1]: i in [1..#Beta]];
   Beta := [Beta[i][2]: i in [1..#Beta]];
   max, pos := Maximum (Dim);
   beta := Beta[pos];

   if IsOdd (max) then 
      k := max div 2;
      repeat 
         VB := ConstructVBlock (g, SQF (form), k: Orthogonal := true);
         gV, formV := RestrictToSpace (g, form, VB);
         par := OrthogonalParameters (gV, formV);
      until par[1][2] eq beta;
      assert FixesForm (gV, formV);
      P := OrthogonalComplement (V, VB);
      Append (~L, <gV, formV, VB, P, V>);
   else
      l := max - 1;
      WB := ConstructWBlock (g, SQF (form), l: Orthogonal := true);
      gW, formW := RestrictToSpace (g, form, WB);
      assert FixesForm (gW, formW); 
      P := OrthogonalComplement (V, WB);
      Append (~L, <gW, formW, WB, P, V>);
   end if;
   
   if Dimension (P) gt 0 then 
      gP, formP := RestrictToSpace (g, form, P);
      return $$ (gP, formP, L);
   end if;
   
   return L;
end function;

GOOrganiseBasis := function (U: VBlock := true, beta := 0)
   n := Dimension (U);
   k := n div 2;
   B := HyperbolicSplitting (U);

   if VBlock then 
      add := B[2][1];
      alpha := DotProduct (add, add);
      if alpha ne beta then 
         add := SquareRoot (alpha^-1 * beta) * add;
         assert DotProduct (add, add) eq beta;
      end if;
      BC := [add];
   end if;

   B := B[1];
   if VBlock eq true then 
      first := [B[i][1]: i in [1..k]] cat BC;
      second := [(-1)^(k + 1 - i) * B[i][2]: i in [1..k]]; 
   else 
      first := [B[i][1]: i in [1..k]]; 
      second := [(-1)^((k + 1 - i) div 2) * B[i][2]: i in [1..k]]; 
   end if;
   Reverse (~second);
   return first cat second;
end function;

GOChooseBasis := function (g, form, types, Beta) 
   spaces := GO_Odd_Decomposition (g, form, [* *]);
   spaces := MyPullback (g, form, spaces);
   d := Nrows (form);
   F := BaseRing (form);
   CB := [* *];
   for i in [1..#spaces] do 
      C := GOOrganiseBasis (spaces[i]: VBlock := types[i], beta := Beta[i]);
      Append (~CB, C);
   end for;
   CB := [x : x in CB];
   CB := &cat (CB);
   M := GL(d, F) ! Matrix (CB);
   assert FixesForm (M, form); 
   return M, [Dimension (x): x in spaces];
end function;

GOConjugateBlock := function (g, h, form: OneBlock := true)
   Beta := OrthogonalParameters (g, form);
   Beta_h := OrthogonalParameters (h, form);
   if Beta ne Beta_h then return false, _; end if;

   beta := [Beta[i][2]: i in [1..#Beta]];
   r := GOSetupSpecialRep (g, form);

   if OneBlock then 
      beta := beta[1];
      C1 := GO_OneBlock_ConjugationMatrix (r, form, beta, g);
      C2 := GO_OneBlock_ConjugationMatrix (r, form, beta, h);
   else
      C1 := GO_TwoBlocks_ConjugationMatrix (r, form, g);
      C2 := GO_TwoBlocks_ConjugationMatrix (r, form, h);
   end if;

   return true, C1^-1 * C2; 
end function;

GOConjugateBlocks := function (g, h, form, blocks, types)
   F := BaseRing (g);
   Conj := <>;
   for i in [1..#blocks] do
      offset := i eq 1 select 0 else &+[blocks[j]: j in [1..i - 1]]; 
      r := blocks[i];
      J := ExtractBlock (form, offset + 1, offset + 1, r, r);
      V := QuadraticSpace (SymmetricToQuadraticForm (J));
      block_g := GL(r, F) ! ExtractBlock (g, offset + 1, offset + 1, r, r);
      block_h := GL(r, F) ! ExtractBlock (h, offset + 1, offset + 1, r, r);
      if Nrows (J) gt 1 then 
         flag, one := GOConjugateBlock (block_g, block_h, J: OneBlock := types[i]);
      else 
         V := QuadraticSpace (StandardQuadraticForm (1, F));
         I := IsometryGroup (V);
         RandomSchreier (I);
         flag, one := IsConjugate (I, block_g, block_h);
      end if;
      if not flag then return false, _; end if;
      Append (~Conj, one);
   end for;

   d := &+blocks;
   return true, GL(d, F) ! DiagonalJoin (Conj);
end function;

GOSetupSpecialRep := function (g, form) 
   F := BaseRing (g);
   q := #F;
   L := GO_Odd_Decomposition (g, form, [* *]);
   R := [* *];
   Dim := []; BV := [* *];
   for i in [1..#L] do 
      a := L[i][1]; fa := L[i][2];
      Beta := OrthogonalParameters (a, fa);
      dim := [Beta[i][1]: i in [1..#Beta]];
      beta := [Beta[i][2]: i in [1..#Beta]];
      J, CB, b := JordanForm (a);
      s := [b[i][2]: i in [1..#b]];
      m := [<x, #[y: y in s | y eq x]>: x in Set (s)];
      m := MySort (m);
      r, fr, cc, dd, ee := GO_ClassRep (m, q, beta);
      assert FixesForm (r, fr);
      Append (~R, <r, fr>);
      Append (~Dim, dim);
      Append (~BV, beta[1]);
   end for;
   new_rep := MyDiagonalJoin ([* R[i][1]: i in [1..#R] *]);
   new_form := MyDiagonalJoin ([* R[i][2]: i in [1..#R] *]);
   
   assert FixesForm (new_rep, new_form);
   return new_rep, new_form, &cat (Dim), BV;
end function;

// OrthogonalDecideConjugacy := function (G, g, h: InOmega := false) 

// decide whether g and h are conjugate in G = GO^\epsilon 
OrthogonalDecideConjugacy := function (G, g, h) 
   flag, type, form := OrthogonalForm (G);
   if not flag then error "G is not orthgonal"; end if;

   new_rep, new_form, Dims, BetaV := GOSetupSpecialRep (g, form);

   A := TransformForm (form, type);
   B := TransformForm (new_form, type);
   C := Generic (G) ! (A * B^-1)^-1;

   // orig_g := g;
   // orig_h := h;
   g := g^(C^-1);
   h := h^(C^-1);

   types := [IsOdd (Dims[i]): i in [1..#Dims]];

   CA, Sg := GOChooseBasis (g, new_form, types, BetaV);
   new_g := CA * g * CA^-1;

   CB := GOChooseBasis (h, new_form, types, BetaV);
   new_h := CB * h * CB^-1;

   flag, X := GOConjugateBlocks (new_g, new_h, new_form, Sg, types);
   if not flag then return false, _; end if;
   conj := Generic (G) ! (C^-1 * CB^-1 * X^-1 * CA * C);

   conj := conj^-1;
   // assert orig_g^conj eq orig_h;
   return true, conj;
end function;

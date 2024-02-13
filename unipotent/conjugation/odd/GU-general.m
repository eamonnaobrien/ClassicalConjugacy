freeze;

// conjugation code for GU / SU 

import "../../good-char.m": D_rep, GUUnipotentReps;
import "../../util.m": MyCommutatorSpace, FixesUnitaryForm, MySort, MyDiagonalJoin;
import "../../central/su.m": SU_ClassRep, SUForm;
import "basics.m": RestrictToSpace, MyPullback;

// map conjugate of V_beta() to *standard rep* for V_beta ()
   
GU_BetaConvertPoly := function (f, n)
   C, M := CoefficientsAndMonomials (f);
   P := Parent (f);
   U := P.1; T := P.2; 
   V := &+[(-1)^(i + 1) * T^i: i in [1..2*n - 1]];
   L := [];
   k := n - 1;
   for i in [1..#M] do
      d := Degree (M[i], 1);
      f := Degree (M[i], 2);
      if d le k then 
         Append (~L, U^d * T^f);
      else 
         Append (~L, U^(n - 1) * V^(d - (n - 1)) * T^f); 
      end if;
   end for;
   
   g :=  &+[C[i] * L[i]: i in [1..#C]];
   c, M := CoefficientsAndMonomials (g);
   g := &+[c[i] * M[i] : i in [1..#M] | Degree (M[i]) le 2 *n - 1];
   
   return g;
end function;
   
GU_BetaExtractRelation := function (f, g, n, beta, q)
   
   A, B := CoefficientsAndMonomials (f);
   C, D := CoefficientsAndMonomials (g);

   NC := [ Universe (C) | ];
   for i in [1..#A] do
      pos := Position (D, B[i]);
      if pos eq 0 then Append (~NC, 0); else Append (~NC, C[i]); end if;
   end for;
   C := NC;
   Reverse (~C);
   Reverse (~A);

   S := [A[i] * (beta * C[2*n + 1 - i])^q * (-1)^(n - i): i in [1..n]] cat 
        [A[n + i] * beta * C[n + 1 - i]^q * (-1)^(i + 1): i in [1..n]]; 
   return &+S;
end function;
   
GU_BetaEvaluatePoly := function (f, S, u, t)
   mat := 0 * t;
   C, M := CoefficientsAndMonomials (f);
   C := Evaluate (C, S);
   for i in [1..#M] do
      c := C[i]; g := M[i];
      exp := Exponents (g);
      mat +:= c * u^exp[1] * t^exp[2];
   end for;
   return mat;
end function;
   
GU_SetupT := function (u)
   MA := MatrixAlgebra (BaseRing (u), Nrows (u));
   u := MA!u;
   return u - u^0;
end function;

GU_SumOfPowers := function (u)
   MA := MatrixAlgebra (BaseRing (u), Nrows (u));
   u := MA!u;
   return u^0 - u^-1;
end function;

GU_SolveEquations := function (M, d)
   P := Parent (M[1]);
   F := BaseRing (P);
   q := Isqrt (#F);

   Solns := [];
   for m in [#M..1 by -1] do
      f := M[m];
      for j in [1..#Solns] do
         f := Evaluate (f, j, Solns[j]);
      end for;
      coeffs, monomials := CoefficientsAndMonomials (f);
      index := Position (monomials, F!1);
      c := index gt 0 select coeffs[#coeffs] else F!0;
      Hilbert := (coeffs[1] eq -coeffs[2]) or Characteristic (F) eq 2;
      if Hilbert then
         s := IsOdd (d) select AdditiveHilbert90 (-c * coeffs[1], q)
                          else AdditiveHilbert90 (c, q);
      else
         s := IsOdd (d) select F!(-1/2 * c * coeffs[1]) else F!(-1/2 * c);
      end if;
      Append (~Solns, s);
   end for;
   
   assert forall{f: f in M | Evaluate (f, Solns) eq 0};
   
   return Solns;
end function;
    
// element in GU to conjugate g to V_beta rep in even dimension 
GU_Even_VBetaConjugateElement := function (g) 

   d := Degree (g);
   F<w> := BaseRing (g);
   q := Isqrt (#F);
   
   n := d div 2;
   k := d div 2;
   
   // assert exists(beta) {x : x in F | x ne 0 and x + x^q eq 0};
   beta := Root (F!-1, q - 1);

   J, sigma := StandardHermitianForm(d, GF(q^2));
   V := UnitarySpace (J, sigma);
   CS := MyCommutatorSpace (V, V, [g]);
   CS := sub<V | Basis (CS)>;
   
   mat_T := GU_SetupT (g);
   T := mat_T;
   mat_U := GU_SumOfPowers (g);
   U := mat_U;

   repeat 
      repeat v1 := Random (V); until not v1 in CS;
   until DotProduct (v1, (-1)^(k + 1) * v1 * beta^-1 * U^(k - 1) * T^k) eq 1;

   L := [v1 * U^i: i in [0..(k - 1)]] cat 
        [v1 * (-1)^(i) * beta^-1 * U^(k - 1) * T^(i + 1): i in [0..k - 2]];
   IP := [DotProduct (v1, x) : x in L];

   P := PolynomialRing (F, 2 * k - 1);
   Q := PolynomialRing (P, 2);
   U := Q.1;
   T := Q.2;
   AssignNames (~Q, ["U", "T"]);
   
   J := [U^i: i in [1..(k - 1)]] cat [(-1)^i * beta^-1 * U^(k - 1) * T^(i + 1): 
                                            i in [0..k - 1]];

   if k gt 1 then 
      r := 1 + &+[P.i * J[i] : i in [1..k - 1]] + &+[P.i * J[i] : i in [k .. 2 * k - 1]];
   else 
      r := 1 + &+[P.i * J[i] : i in [k .. 2 * k - 1]];
   end if;
   
   J := [U^0] cat J;

   RS := [];

   W := [J[i] : i in [1..2 * k - 1]];
   W := [r * w: w in W];
   
   for i in [1..#W] do
      b := GU_BetaConvertPoly (W[i], d div 2);
      rel := GU_BetaExtractRelation (r, b, d div 2, beta, q);
      Append (~RS, rel);
   end for;
   
   L := RS;

   M := [L[i] - IP[i]: i in [1..#L]];
   
   S := GU_SolveEquations (M, d);

   M := GU_BetaEvaluatePoly (r, S, mat_U, mat_T);
   
   v := v1 * M^-1;

   U := mat_U; T := mat_T;
   B := [v * U^i: i in [0..k - 1]] cat 
        [v * beta^-1 * (-1)^(i) * U^(k - 1) * T^(i + 1): i in [0..k - 1]];

   CB := GL(d, q^2) ! [Eltseq (b): b in B];
   return CB;
end function;

// code for GU V_beta() odd dimension 
  
GU_GammaConvertPoly := function (f, gamma, n)

   C, M := CoefficientsAndMonomials (f);
   P := Parent (f);
   U := P.1; U0 := P.2; T := P.3; 

   V := &+[(-1)^(i + 1) * T^i: i in [1..2*n]];
   V0 := &+[gamma^(i - 1) * T^i: i in [1..2*n]];
   poly := (1 - gamma * T) * &+[(-1)^(i) * T^i: i in [0..2*n]];

   L := [];
   k := n - 1;
   for i in [1..#M] do
      d := Degree (M[i], 1);
      e := Degree (M[i], 2);
      f := Degree (M[i], 3);
      if d le k and e le 1 then 
         Append (~L, U^d * U0^e * T^f);
      elif d gt k and e eq 1 then 
         Append (~L, U^(n - 1) * V^(d - (n - 1)) * U0^e * T^f);
      elif d gt k and e eq 0 then 
         Append (~L, U^(n - 1) * U0 * poly * V^(d - (n)) * T^f);
      elif d le k and e gt 1 then
         Append (~L, U^d * U0 * V0^(e - 1)* T^f);
      else 
         assert d gt k and e gt 1;
         Append (~L, U^(n - 1) * V^(d - (n - 1)) * U0 * V0^(e - 1)* T^f);
      end if;
   end for;
   
   g :=  &+[C[i] * L[i]: i in [1..#C]];
   c, M := CoefficientsAndMonomials (g);
   g := &+[c[i] * M[i] : i in [1..#M] | Degree (M[i]) le 2 * n];
   
   return g;
end function;
   
GU_GammaExtractRelation := function (f, g, n, q)
   A, B := CoefficientsAndMonomials (f);
   C, D := CoefficientsAndMonomials (g);

   NC := [Universe (C) | ];
   for i in [1..#A] do
      pos := Position (D, B[i]);
      if pos eq 0 then Append (~NC, 0); else Append (~NC, C[i]); end if;
   end for;
   C := NC;
   Reverse (~C);
   Reverse (~A);

   S := [A[i + 1] * (C[2*n + 1 - i])^q * (-1)^(n - i): i in [0..n - 1]] cat 
        [A[n + 1] * C[n + 1]^q] cat 
        [A[n + 2 + i] * C[n - i]^q * (-1)^(i + 1): i in [0..n - 1]]; 
   return &+S;
end function;
   
GU_GammaEvaluatePoly := function (f, S, u, u0, t)
   mat := 0 * t;
   C, M := CoefficientsAndMonomials (f);
   C := Evaluate (C, S);
   for i in [1..#M] do
      c := C[i]; g := M[i];
      exp := Exponents (g);
      mat +:= c * u^exp[1] * u0^exp[2] * t^exp[3];
   end for;
   return mat;
end function;
   
GU_DefineU0 := function (T, gamma)
   d := Nrows (T);
   F := BaseRing (T);
   MA := MatrixAlgebra (F, d);
   T := MA!T;
   U0 := T * (T^0 - gamma * T)^-1;
   return U0;
end function;
    
// element in GU to conjugate g to V_beta rep in odd dimension 
GU_Odd_VBetaConjugateElement := function (g) 

   d := Degree (g);
   F<w> := BaseRing (g);
   q := Isqrt (#F);
   
   n := d div 2;
   k := d div 2;
   assert exists(gamma) {x : x in F | x + x^q eq F!-1};

   J, sigma := StandardHermitianForm (d, GF(q^2));
   V := UnitarySpace (J, sigma);
   CS := MyCommutatorSpace (V, V, [g]);
   CS := sub<V | Basis (CS)>;
   
   mat_T := GU_SetupT (g);
   T := mat_T;
   mat_U := GU_SumOfPowers (g);
   U := mat_U;

   U0 := GU_DefineU0 (T, gamma);
   mat_U0 := U0;

   repeat 
      repeat v1 := Random (V); until not v1 in CS;
   until DotProduct (v1, v1 * U^(k - 1) * U0 * T^k) eq (-1)^k;

   L := [v1 * U^i: i in [0..(k - 1)]] cat 
        [v1 * U^(k - 1) * U0 * T^(i): i in [0..k - 1]];
   IP := [DotProduct (v1, x) : x in L];

   P := PolynomialRing (F, 2 * k);
   
   Q := PolynomialRing (P, 3);
   
   U := Q.1;
   U0 := Q.2;
   T := Q.3;
   AssignNames (~Q, ["U", "U0", "T"]);
   
   J := [U^i: i in [1..(k - 1)]] cat [U^(k - 1) * U0 * T^(i): i in [0..k]];

   r := 1 + &+[P.i * J[i] : i in [1..2 * k]]; 
   
   J := [U^0] cat J;

   RS := [];

   W := [J[i] : i in [1..2 * k]];
   W := [r * w: w in W];
   
   for i in [1..#W] do
      b := GU_GammaConvertPoly (W[i], gamma, d div 2);
      rel := GU_GammaExtractRelation (r, b, d div 2, q);
      Append (~RS, rel);
   end for;
   
   L := RS;
   M := [L[i] - IP[i]: i in [1..#L]];
   
   S := GU_SolveEquations (M, d);

   M := GU_GammaEvaluatePoly (r, S, mat_U, mat_U0, mat_T);
   
   v := v1 * M^-1;

   U := mat_U; T := mat_T; U0 := mat_U0;
   B := [v * U^i: i in [0..k - 1]] cat 
        [v * (-1)^(i) * U^(k - 1) * U0 * T^(i): i in [0..k]];

   CB := GL(d, q^2) ! [Eltseq (b): b in B];
   return CB;
end function;

GU_VBetaConjugateElement := function (g)
   d := Degree (g);
   if IsOdd (d) then 
      CB := GU_Odd_VBetaConjugateElement (g);
   else 
      CB := GU_Even_VBetaConjugateElement (g);
   end if;
   return CB^+1;
end function;

// matrix in GU to conjugate leading rep in SU list 
// to another rep determined by SU parameter list 
H_matrix := function (alpha, n, q)
   F := GF (q^2);
   MA := MatrixAlgebra (F, n);
   D := Identity (MA);
   D[1,1] := alpha;
   D[n,n] := (alpha^-1)^q;
   return GL(n, F) ! D;
end function;

GUParameters := function (g)
   J, CB, b := JordanForm (g);
   s := [b[i][2]: i in [1..#b]];
   Sort (~s);
   Reverse (~s);
   return s;
end function;

// construct V block of dimension n 
GUConstructVBlock := function (g, V, n)
   d := Nrows (g);
   K := BaseRing (g);
   MA := MatrixAlgebra (K, d);
   u := MA!g;

   repeat
      v := Random (V);
   until DotProduct (v, v * (u - 1)^(n - 1)) ne 0;

   basis := [v * u^i: i in [0..n - 1]];
   U := sub<V | basis>;
   assert IsNondegenerate (U);
   return U;
end function;

GUDecomposition := function (g, form, V, L)
   Dim := GUParameters (g);
   K := BaseRing (form);
   q := #K;
   d := Nrows (g);
   max, pos := Maximum (Dim);

   VB := GUConstructVBlock (g, V, max);
   gV, formV := RestrictToSpace (g, form, VB);
   assert FixesUnitaryForm (gV, formV);
   P := OrthogonalComplement (V, VB);
   Append (~L, <gV, formV, VB, P, V>);
   
   if Dimension (P) gt 0 then 
      _, sigma := StandardHermitianForm (Nrows (g), K);
      gP, formP := RestrictToSpace (g, form, P);
      RV := UnitarySpace (formP, sigma);
      return $$ (gP, formP, RV, L);
   end if;
   
   return L;
end function;

GUSetupSpecialRep := function (g, form, V) 
   F := BaseRing (g);
   q := #F;
   L := GUDecomposition (g, form, V, [* *]);
   R := [* *];
   Dim := [];
   for i in [1..#L] do 
      a := L[i][1]; fa := L[i][2];
      dim := GUParameters (a);
      J, CB, b := JordanForm (a);
      s := [b[i][2]: i in [1..#b]];
      m := [<x, #[y: y in s | y eq x]>: x in Set (s)];
      m := MySort (m);
      r, aa := SU_ClassRep (m, Isqrt (q));
      fr := SUForm (m, aa, Isqrt (q));
      assert FixesUnitaryForm (r, fr);
      Append (~R, <r, fr>);
      Append (~Dim, dim);
   end for;
   new_rep := MyDiagonalJoin ([* R[i][1]: i in [1..#R] *]);
   new_form := MyDiagonalJoin ([* R[i][2]: i in [1..#R] *]);
   assert FixesUnitaryForm (new_rep, new_form);
   return new_rep, new_form, &cat (Dim);
end function;

GUOrganiseBasis := function (V, U: VBlock := true)
   F := BaseRing (U);
   q := Isqrt (#F);
   n := Dimension (U);
   k := n div 2;
   B := HyperbolicSplitting (U);
   if IsOdd (n) then
      add := B[2][1];
      alpha := DotProduct (add, add);
      if alpha ne 1 then
         root := Root (alpha, q + 1);
         add := (root^-1) * add;
         assert DotProduct (add, add) eq 1;
      end if;
      BC := [add];
   else 
      BC := [];
   end if;
   B := B[1];
   first := [B[i][1]: i in [1..k]] cat BC; 
   second := [B[i][2]: i in [1..k]]; 
   Reverse (~second);
   return first cat second;
end function;

GUChooseBasis := function (g, form, V) 
   spaces := GUDecomposition (g, form, V, [* *]);
   spaces := MyPullback (g, form, spaces);
   spaces := [sub<V | x>: x in spaces];
   
   // make sure U is viewed as unitary space -- otherwise chaos!
   sigma := V`Involution;
   d := Nrows (form);
   F := BaseRing (form);
   CB := [* *];
   for i in [1..#spaces] do 
      U := spaces[i]; U`Involution := sigma;
      C := GUOrganiseBasis (V, spaces[i]);
      C := [V!c: c in C];
      Append (~CB, C);
   end for;
   CB := [x : x in CB];
   CB := &cat (CB);
   M := GL(V) ! Matrix (CB);
   assert FixesUnitaryForm (M, form); 
   return M, [Dimension (x): x in spaces];
end function;

GUConjugateBlock := function (g, h, f)
   if IsOdd (Degree (g)) then
      C1 := GU_Odd_VBetaConjugateElement (g);
      C2 := GU_Odd_VBetaConjugateElement (h);
   else 
      C1 := GU_Even_VBetaConjugateElement (g);
      C2 := GU_Even_VBetaConjugateElement (h);
   end if;
   return true, C1^-1 * C2; 
end function;

GUConjugateBlocks := function (g, h, form, blocks) 
   F := BaseRing (g);
   Conj := <>;
   for i in [1..#blocks] do
      offset := i eq 1 select 0 else &+[blocks[j]: j in [1..i - 1]]; 
      r := blocks[i];
      J := ExtractBlock (form, offset + 1, offset + 1, r, r);
      _, sigma := StandardHermitianForm (Nrows (J), F);
      block_g := GL(r, F) ! ExtractBlock (g, offset + 1, offset + 1, r, r);
      block_h := GL(r, F) ! ExtractBlock (h, offset + 1, offset + 1, r, r);
      if Nrows (J) gt 1 then 
         flag, one := GUConjugateBlock (block_g, block_h, J);
      else 
         V := UnitarySpace (J, sigma);
         I := IsometryGroup (V);
         RandomSchreier (I);
         flag, one := IsConjugate (I, block_g, block_h);
      end if;
      if not flag then return false, _; end if;
      Append (~Conj, one);
   end for;

   d := &+blocks;
   return true, GL(d, F) ! DiagonalJoin (Conj), Conj;
end function;

// are g and h conjugate in G=GU?
GUDecideConjugacy := function (G, g, h) 
   flag, form := UnitaryForm (G);
   if not flag then error "G is not a unitary group"; end if;

   if GUParameters (g) ne GUParameters (h) then 
      return false, _;
   end if;

   _, sigma := StandardHermitianForm (Degree (G), BaseRing (G));
   V := UnitarySpace (form, sigma);

   new_rep, new_form, Dims := GUSetupSpecialRep (g, form, V);

   A := TransformForm (form, "unitary");
   B := TransformForm (new_form, "unitary");
   C := Generic (G) ! (A * B^-1)^-1;

   g := g^(C^-1);
   h := h^(C^-1);

   V := UnitarySpace (new_form, sigma);

   CA, Sg := GUChooseBasis (g, new_form, V);
   new_g := CA * g * CA^-1;

   CB := GUChooseBasis (h, new_form, V);
   new_h := CB * h * CB^-1;

   flag, X, blocks := GUConjugateBlocks (new_g, new_h, new_form, Sg); 
   if not flag then return false, _; end if;
   conj := Generic (G) ! (C^-1 * CB^-1 * X^-1 * CA * C);

   return true, conj^-1, C, CA, CB, X;
end function;

// parameters for g in SU 
SUParameters := function (G, g: rep := false, FullLabel := true)

   F := BaseRing (G);
   d := Degree (G);
   q := Isqrt (#F);
   M, phi := MultiplicativeGroup (F);

   z := (Order (M.1) div (q + 1)) * M.1;
   assert Order (z) eq q + 1;
   Z := sub< M | z >;

   partition := GUParameters (g);
   S := Set (partition) join {q + 1};
   t := Gcd (S);
   Q, tau := quo<Z | t * Z.1>;
   reps := [(x @@ tau) @ phi: x in Q];
   conj := [D_rep (d, q, alpha): alpha in reps];
   Params := [conj[i][1][1]: i in [1..#conj]];

   if FullLabel then 
      if Type (rep) eq BoolElt then 
         rep := GUUnipotentReps (d, q: Partition := [partition]);
         rep := rep[1][3];
      end if;
      flag, form := UnitaryForm (G);
      assert flag;
      tr := TransformForm (form, "unitary"); 
      tr := Generic (G) ! tr;
      rep := rep^(tr^-1);
      flag, CB := GUDecideConjugacy (G, g, rep);
      assert g^CB eq rep;
      l := Determinant (CB);
      val := (l^-1) @@ phi @ tau; // element of Z/tZ
      assert exists(alpha){alpha: alpha in Params |
                          (alpha^-q * alpha^+1) @@ phi @ tau eq val};
      return <partition, alpha>, CB;
   else 
      return <partition, Params>, CB;
   end if;
end function;

// decide if g and h are conjugate in G

SUDecideConjugacy := function (G, g, h)
   flag, conj, tr, CA, CB, X := GUDecideConjugacy (G, g, h);
   if not flag then return false, _; end if;
   if Determinant (conj) eq 1 then return true, conj; end if;

   det := Determinant (CB^-1 * X^-1 * CA^1);

   // construct a diagonal commuting element of determinant det^-1 
   partition := GUParameters (g);
   F := BaseRing (G);
   q := Isqrt (#F);
   M, phi := MultiplicativeGroup (F);

   z := (Order (M.1) div (q + 1)) * M.1;
   assert Order (z) eq q + 1;
   Z := sub<M | z>;

   t, coeffs := ExtendedGreatestCommonDivisor (partition cat [q + 1]);
   Q, tau := quo<Z | t * Z.1>;
   assert #Q eq Gcd (t, q + 1);

   delta := det @@ phi;
   k := #partition;
   C := CartesianPower (Q, k);
   flag := exists(soln){x: x in C | 
           &+[partition[i] * x[i]: i in [1..k]] eq tau (delta)};
   if not flag then return false, _; end if;

   soln := [x @@ tau @ phi: x in soln];

   // lhs = det * s^t
   lhs := &*[soln[i]^partition[i] : i in [1..k]];
   flag, s := IsPower (lhs * det^-1, t);

   // now kill off the s^t using the fact that t = Gcd (partition)  
   soln := [(soln[i] * s^-coeffs[i]): i in [1..k]];
   S := <ScalarMatrix (partition[i], soln[i]): i in [1..k]>;
   S := Generic (G) ! DiagonalJoin (S);

   c := Generic (G) ! (tr^-1 * CB^-1 * S^-1 * X^-1 * CA * tr);
   // assert Determinant (c) eq 1;
   return true, c^-1;
end function;

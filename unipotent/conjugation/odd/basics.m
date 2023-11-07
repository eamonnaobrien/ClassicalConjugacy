freeze;

import "../../util.m": Q_value;

SetupT := function (u)
   MA := MatrixAlgebra (BaseRing (u), Nrows (u));
   u := MA!u;
   return u + u^0;
end function;

SumOfPowers := function (u)
   T := SetupT (u);
   return &+[T^i: i in [1..Nrows (u) - 1]];
end function;

MyReduceBasis := function (B)
   L := [];
   if #B eq 1 then return L; end if;
   T := [t : t in B | IsIrreducible (t) eq false];
   for t in T do
      facs := Factorisation (t);
      j := Random ([1..#facs]);
      Append (~L, facs[j][1]);
   end for;
   return L;
end function;

// restriction of g and form to subspace U 
RestrictToSpace := function (g, form, U: Orthogonal := false)

   K := BaseRing (Parent (g)); 
   // if type eq "Unitary" then q := Isqrt (#K); else q := #K; end if;

   M := [];
   S := Basis (U);
   b := #S;
   for i in [1..b] do
      C := Coordinates (U, U!(S[i] * g));
      c := [C[j]: j in [1..Dimension (U)]];
      Append (~M, c);
   end for;

   F := Zero (MatrixAlgebra (K, b));
   if Orthogonal then 
      for i in [1..b] do
         for j in [i + 1..b] do
            F[i,j] := DotProduct (S[i], S[j]);
         end for;
         // F[i][i] := QuadraticNorm (S[i]);
         F[i][i] := Q_value (form, S[i]);
      end for;
   else 
      for i in [1..b] do
         for j in [1..b] do
            F[i,j] := DotProduct (S[i], S[j]);
         end for;
      end for;
   end if;

   small_form := MatrixAlgebra(K, #M) !F;
   small_g := GL(#M, K) ! M;
   small_form := MatrixAlgebra(K, #M) !F;

   return small_g, small_form;
end function;

// S 2-dimensional O- type space of quadratic space with norm f; 
// find standard basis for S so dot product = 1, and 
// quadratic norms of basis elements are alpha and beta 

SpecialQuadBasis := function (S, f, alpha, beta: Verify := false)
   B := Basis (S);
   u := B[1]; v := B[2];
   if DotProduct (u, v) eq 1 then
      a := QuadraticNorm (u);
      b := QuadraticNorm (v);
      if [a, b] eq [alpha, beta] then return [u, v]; end if; 
      if [b, a] eq [alpha, beta] then return [v, u]; end if; 
   end if;

   g, form := RestrictToSpace (f^0, f, S: Orthogonal:=true);
   F := BaseRing (form);
   n := Nrows (form);
   P := PolynomialRing (F, 3);
   MA := MatrixAlgebra (P, 2);
   f := MA!form;
   M := RMatrixSpace (P, 1, 2);

   // can assume that one of the two is scalar multiple of  
   // one vector from basis for S
   v := M![P.1, 0];
   u := M![P.2, P.3];
  
   // three relations 
   b := f + Transpose (f);
   one := v * f * Transpose (v);    o := one[1,1] + P!alpha;
   two := u * f * Transpose (u);    t := two[1,1] + P!beta;
   three := u * b * Transpose (v); t3 := three[1,1] + P!1;
   I := ideal <P | o, t, t3>;
   I := ChangeOrder (I, "grevlex");
   BI := GroebnerBasis (I);
   Solns := Variety (I);
   soln := Solns[1];
   soln := [F!x: x in soln];

   A1 := soln[1] * B[1];
   A2 := &+[soln[1+i] * B[i]: i in [1..2]];
   if Verify then 
      assert DotProduct (A1, A2) eq 1;
      assert QuadraticNorm (A1) eq alpha;
      assert QuadraticNorm (A2) eq beta;
   end if;
   return [A1, A2];
end function;

PullbackToParent := function (V, B, B1)
   new := [];
   d := Degree (V); q := #BaseRing (V);
   m := Dimension (B);
   for i in [1..Dimension (B1)] do
      e := Eltseq (B1.i);
      v := &+[e[i] * B.i: i in [1..#e]];
      Append (~new, v);
   end for;
   return sub<V | new>;
end function;

MyPullback := function (g, form, L)
   if #L eq 0 then return []; end if;
   Spaces := [* *];
   for j in [#L..2 by -1] do 
      U := L[j][3];
      for i in [j..2 by -1] do
         V := L[i - 1][5];
         P := L[i - 1][4];
         U := PullbackToParent (V, P, U);
      end for;
      Append (~Spaces, U);
   end for;
   Append (~Spaces, L[1][3]);
   Spaces := [x : x in Spaces];
   Reverse (~Spaces);
   return Spaces;
end function;

// basis [V[i], W[i]: i in [1..#V]];

SpOConstructCB := function (V, W, d, q)
   MA := MatrixAlgebra (GF (q), d);
   CB := [];
   for i in [1..#V] do
      B := [V[i], W[i]];
      Append (~CB, B);
   end for;
   CB := &cat (CB);
   CB := MA ! CB;
   return GL(d, q) ! CB;
end function;

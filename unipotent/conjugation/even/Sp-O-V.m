freeze;

import "../../util.m": MyCommutatorSpace, FixesForm;
import "../odd/basics.m": SumOfPowers, SetupT;

// code for Sp even char and for GO even char 
// V(beta) where beta can be 0 or non-zero 

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
   
BetaConvertPoly := function (f, n, c, m)
   C, M := CoefficientsAndMonomials (f);
   P := Parent (f);
   U := P.1; T := P.3; V0 := P.2;
   V := &+[T^i: i in [1..2 * n - 1]];
   D := [];
   L := [];
   k := n - 2;
   for i in [1..#M] do
      d := Degree (M[i], 1);
      e := Degree (M[i], 3);
      f := Degree (M[i], 2);
      if d le k and e eq 0 and f eq 0 then 
         Append (~L, U^d);
      elif d gt k and e eq 0 and f eq 0 then 
         Append (~L, V0^(n - 1) * V^(d - (n - 1)) + 
         &+[c[i - 1] * V0^(n - 1) * T^i * V^(d - (n - 1)): i in [2..n]]);
      else
         if f gt n - 1 then 
            assert f eq 2 * (n - 1);
            rest := V^(n - 1) + &+[m[i] * V^(n - 2 + i) : i in [2..#m]];
            Append (~L, V0^(n - 1) * T^e * rest);
         else
            assert f eq n - 1;
            Append (~L, V^d * T^e * V0^(n - 1));
          end if;
      end if;
   end for;
   
   g :=  &+[C[i] * L[i]: i in [1..#C]];
   return g;
end function;
   
BetaExtractRelation := function (f, g, n)
   
   A, B := CoefficientsAndMonomials (f);
   C, D := CoefficientsAndMonomials (g);
   
   S := [];
   for i in [1..#A] do
      d := Degree (B[i]);
      l := [j: j in [1..#C] | d + Degree (D[j]) eq n - 1];
      Append (~S, [A[i] * C[k]: k in l]);
   end for;
   S := &+(&cat S);
   return S;
end function;
   
BetaEvaluatePoly := function (f, S, u, v0, t)
   mat := 0 * t;
   C, M := CoefficientsAndMonomials (f);
   C := Evaluate (C, S);
   for i in [1..#M] do
      c := C[i]; g := M[i];
      exp := Exponents (g);
      if exp[2] eq 0 then 
         mat +:= c * u^exp[1] * t^exp[3];
      else
         mat +:= c * u^exp[1] * v0 * t^exp[3];
      end if;
   end for;
   return mat;
end function;
   
GetCoordinates := function (g, form: Orthogonal := false)
   d := Degree (g);
   n := d div 2;
   q := #BaseRing (g);
   
   mat_T := SetupT (g);
   T := mat_T;
   mat_U := SumOfPowers (g);
   U := mat_U;
   
   if Orthogonal then
      V := QuadraticSpace (form);
   else
      V := SymplecticSpace (form);
   end if;

   vm3 := V.(n - 1);
   
   E := [vm3 * U^i: i in [1..d div 2 + 1]];
   W := VectorSpaceWithBasis (E);
   WW := VectorSpace (GF(q), d);
   coords := Coordinates (W, WW!V.n);
   F<w>:= GF (q);
   w := PrimitiveElement (F);
   U0 := &+[coords[i] * U^(n - 2 + i) : i in [2..#coords]];
   mat_U0 := &+[coords[i] * mat_U^(n - 2 + i) : i in [2..#coords]];
   
   basis := [(U^(n - 1) + U0) * T^i: i in [2..n]];
   
   A := VectorSpace (F, d);
   Y := Hom (A, A);
   B := [Y!b: b in basis];
   S := KMatrixSpaceWithBasis (B);
   c := Coordinates (S, S!U0);
   
   return coords, c, mat_U0, basis;
end function;
   
// code for Sp and GO even char 
// V(beta) beta can be 0 or non-zero 
// map conjugate of V_beta to rep either in Sp or GO in char 2 
SpO_VBeta_ConjugateElement := function (g, rep, form: 
   Limit := 100, Orthogonal := false, Verify := true)

   d := Degree (g);
   F := BaseRing (g);
   q := #F;
   
   n := d div 2;
   k := d div 2;
   
   beta := rep[1][k + 2];
   
   coords, c, U0, basis := GetCoordinates (rep, form: Orthogonal := Orthogonal);
   assert U0 eq &+[c[i] * basis[i]: i in [1..n - 1]];
   // U := SumOfPowers (rep);
   // assert U0 eq &+[coords[i] * U^(n - 2 + i) : i in [2..#coords]];
   
   if Orthogonal then 
      V := QuadraticSpace (form);
   else
      V := SymplecticSpace (form);
   end if;

   CS := MyCommutatorSpace (V, V, [g]);
   CS := sub<V | Basis (CS)>;
   
   Ntries := 0;
   repeat
      Ntries +:= 1;
      mat_T := SetupT (g);
      T := mat_T;
      mat_U := SumOfPowers (g);
      U := mat_U;
      
      repeat v := Random (V); until not (v in CS);
      
      U0 := &+[coords[i] * U^(n - 2 + i) : i in [2..#coords]];
      mat_U0 := &+[coords[i] * mat_U^(n - 2 + i) : i in [2..#coords]];
      v0 := U^(k - 1) + U0;
      
      if IsOdd (k) then 
         L := [v * U^i: i in [1..(k - 2) by 2]] cat 
              [v * v0 * T^i: i in [1..k by 2]];
      else 
         L := [v * U^i: i in [1..(k - 2) by 2]] cat 
              [v * v0 * T^i: i in [0..k by 2]];
      end if;
      IP := [DotProduct (v, x) : x in L];
      
      P := Orthogonal select PolynomialRing (F, k + 1) else PolynomialRing (F, k);
      Q<U, V0, T> := PolynomialRing (P, 3);
      
      J := [U^0] cat [U^i: i in [1..(k - 2)]] cat [V0^(k - 1) * T^i: i in [0..k]];
      if Orthogonal then 
         r := P.1 + &+[P.i * J[2 * i - 2]: i in [2..k + 1]];
      else
         r := P.1 + &+[P.i * J[2 * i - 2]: i in [2..k]];
      end if;
      
      RS := [];
      W := [J[2 * i] : i in [1..k]];
      W := [r * w: w in W];
      for i in [1..#W] do
         b := BetaConvertPoly (W[i], d div 2, c, coords);
         rel := BetaExtractRelation (r, b, d);
         Append (~RS, rel);
      end for;
      
      if Orthogonal then 
         gamma := QuadraticNorm (v);
         IP cat:= [gamma];
         if IsEven (k) then 
            Append (~RS, beta * (P.((k + 2) div 2))^2 + P.1 * P.(k + 1)); 
         else 
            Append (~RS, (P.((k + 3) div 2))^2 + P.1 * P.(k + 1));
         end if;
      end if;
      
      L := RS;
      M := [L[i] + IP[i]: i in [1..#L]];
      I := Ideal (M);
      I := ChangeOrder(I, "grevlex");
      B := GroebnerBasis (I);
      // Solns := Variety (I);

      L := MyReduceBasis (B);
      while #L gt 0 do
         I := ideal<Generic (I) | I, L>;
         B := GroebnerBasis (I);
         L := MyReduceBasis (B);
      end while;

      C := [Coefficients (b): b in B];
      S := [GF(q) | ];
      for i in [1..#C] do
         if #C[i] eq 2 then S[i] := C[i][2]; else S[i] := 0; end if; 
      end for;
      
      if #C gt 1 then 
         mat_V02 := mat_U^(k - 1) + mat_U0;
         assert mat_V02 eq v0;
      
         M := BetaEvaluatePoly (r, S, mat_U, v0, mat_T);
      
         v := v * M^-1;
         B := [v * mat_U^i: i in [0..(k - 2)]] cat [v * mat_V02 * mat_T^i: i in [0..k]];
         CB := GL(d, q) ! [Eltseq (b): b in B];
         if Verify then 
            assert CB * g * CB^-1 eq rep;
            if Orthogonal then 
               assert FixesForm (CB, form + Transpose (form));
            else 
               assert FixesForm (CB, form);
            end if;
         end if;
         return true, CB;
      end if;
   until Ntries gt Limit;
   error "SpO_VBeta_ConjugateElement: Failed to decide conjugacy"; 
end function;

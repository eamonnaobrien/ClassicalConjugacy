freeze;

import "../odd/basics.m": SumOfPowers, SetupT;
import "../../util.m": MyCommutatorSpace, FixesForm, ChooseAlpha;
import "Omega-W-beta.m": GenerateRelation;

// handle W_n(beta) n odd beta different from 0 for Sp even char 

MyEvaluatePoly := function (f, t)
   mat := 0 * t;
   C, M := CoefficientsAndMonomials (f);
   for i in [1..#M] do
      c := C[i]; g := M[i];
      exp := Exponents (g);
      if #exp eq 3 then 
         mat +:= c * t^exp[3];
      end if;
   end for;
   return mat;
end function;

SpBasicSetup := function (rep, form, beta)
   // "Basic setup for Sp";

   d := Degree (rep);
   n := d div 2;
   k := n div 2;

   F := BaseRing (rep);

   q := #F;
   V := SymplecticSpace (form);

   mat_T := SetupT (rep);
   T := mat_T;

   w := V.1; x := V.(n + 1);

   B := [w * T^i: i in [0..n - 1]] cat [x * T^i: i in [0..n - 1]];

   W := VectorSpaceWithBasis (B);
   C := [Coordinates (W, W!V.i): i in [1..d]];
   C_coords := C;

   m := 4*k + 1;
   F<b0, c0, d0, d1, d2> := RationalFunctionField (GF(q), m);

   P<w, x, T> := PolynomialRing (F, 3);
   AssignNames (~P, ["w", "x", "T"]);

   V := VectorSpace (F, d);

   f_pols := [&+[C[j][i]* T^(i - 1): i in [1..n]]: j in [1..n]];
   g_pols := [&+[C[j][i] * T^(i - (n + 1)): i in [n + 1..d]]: j in [1..n]];

   h_pols := [&+[C[n + j][i]* T^(i - 1): i in [1..d div 2]]: j in [1..n]];
   k_pols := [&+[C[n + j][i] * T^(i - (n + 1)): i in [n + 1..d]]: j in [1..n]];

   PB := [w * T^i: i in [0..n - 1]] cat [x * T^i: i in [0..n - 1]];

   C_coords := [V!x: x in C_coords];
   S := VectorSpaceWithBasis (C_coords);

   w1 := w + &+[F.i * (w * h_pols[2*i - 1] + x * k_pols[2*i - 1]): i in [1..k]];
   x1 := &+[F.(k + i) * (w * f_pols[2*i - 1] + x * g_pols[2*i - 1]): i in [1..k]] + 
         &+[F.(2*k + i) * (w * h_pols[i] + x * k_pols[i]): i in [1..2*k + 1]];

   CC, CM := CoefficientsAndMonomials (w1);

   alpha := 0;
   Rels := [];
   for i in [1..2*k] do 
      w1_RHS := w1 * f_pols[i + 1] + x1 * g_pols[i + 1];
      rel := GenerateRelation (V, F, PB, S, w1, w1_RHS);
      Append (~Rels, rel);
   end for;
   for i in [1..2 * k] do 
      alpha_RHS := w1 * h_pols[i + 1] + x1 * k_pols[i + 1];
      rel := GenerateRelation (V, F, PB, S, x1, alpha_RHS);
      Append (~Rels, rel);
   end for;
   for i in [1..2*k + 1] do 
      alpha_RHS := w1 * h_pols[i] + x1 * k_pols[i];
      rel := GenerateRelation (V, F, PB, S, w1, alpha_RHS);
      Append (~Rels, rel);
   end for;

   return Rels, f_pols, g_pols, h_pols, k_pols;
end function;

Sp_WBeta_ConjugateElement := function (h, rep, form: Limit := 100) 

   d := Nrows (rep);
   n := d div 2;
   k := n div 2;
   
   F := BaseRing (rep);
   q := #F;
   
   beta := ChooseAlpha (q);
   Rels, F, G, H, K := SpBasicSetup (rep, form, beta);
   
   V := SymplecticSpace (form);
   
   mat_T := SetupT (h);
   T := mat_T;
   CS := MyCommutatorSpace (V, V, [h]);

   Ntries := 0; found := false;
   repeat 
      Ntries +:= 1;
      repeat
         w := Random (V);
         x := Random (V);
      until sub<V | CS, w, x> eq V; 
   
      IP := [];
      Alpha := []; Beta := []; Gamma := [];
      
      for i in [1..2 * k] do 
         Alpha[i] := DotProduct (w, w * MyEvaluatePoly (F[i + 1], mat_T) + x * MyEvaluatePoly (G[i + 1], mat_T));
         Beta[i] := DotProduct (x, w * MyEvaluatePoly (H[i + 1], mat_T) + x * MyEvaluatePoly (K[i + 1], mat_T));
      end for;
      
      for i in [1..n] do 
        Gamma[i] := DotProduct (w, w * MyEvaluatePoly (H[i], mat_T) + x * MyEvaluatePoly (K[i], mat_T));
      end for;
      
      IP := Alpha cat Beta cat Gamma;
      
      M := [Rels[i] + IP[i]: i in [1..#Rels]];
      PT := Universe (M);
      RI:= RingOfIntegers (PT);
      M := [RI!M[i] : i in [1..#M]];
      
      I := Ideal (M);
      I := ChangeOrder (I, "grevlex");
      B := GroebnerBasis (I);
      assert IsZeroDimensional (I);
      Solns := Variety (I);
   
      nmr := 0;
      for S in Solns do 
         nmr +:= 1;
         B := [S[i]: i in [1..k]];
         C := [S[k + i]: i in [1..k]];
         D := [S[2*k + i]: i in [1..2 * k + 1]];
   
         // check that matrix M is invertible 
         assert B[1] * C[1] ne D[1];
      
         f := 1 + &+[B[i + 1] * H[2 * i + 1] : i in [0..k - 1]];
         g := &+[B[i + 1] * K[2 * i + 1] : i in [0..k - 1]];
         r := &+[C[i + 1] * F[2 * i + 1] : i in [0..k - 1]] + 
              &+[D[i + 1] * H[i + 1] : i in [0..2 * k]];
         s := &+[C[i + 1] * G[2 * i + 1] : i in [0..k - 1]] + 
              &+[D[i + 1] * K[i + 1] : i in [0..2 * k]];
         mat_f := MyEvaluatePoly (f, T);
         mat_g := MyEvaluatePoly (g, T);
         mat_r := MyEvaluatePoly (r, T);
         mat_s := MyEvaluatePoly (s, T);
        
         M :=  mat_g * mat_r + mat_f * mat_s;
         x := (w * mat_r + x * mat_f) * M^-1;
         w := (w + x * mat_g) * mat_f^-1;
         
         mat_F := [MyEvaluatePoly (F[i], T): i in [1..#F]];
         mat_G := [MyEvaluatePoly (G[i], T): i in [1..#F]];
         mat_H := [MyEvaluatePoly (H[i], T): i in [1..#F]];
         mat_K := [MyEvaluatePoly (K[i], T): i in [1..#F]];
      
         B := [w * mat_F[i] + x * mat_G[i] : i in [1..#F]] cat 
              [w * mat_H[i] + x * mat_K[i] : i in [1..#F]]; 
      
         CB := GL(d, q) ! [Eltseq (x): x in B];
         assert CB * h * CB^-1 eq rep;
         found := FixesForm (CB, form); 
         if found then assert nmr eq 1; return found, CB; end if;
      end for;
      if Ntries gt 1 then assert beta ne 0; end if;
   until found or Ntries gt Limit;
   error "Sp_WBeta_ConjugationMatrix: Failed to decide conjugacy";
   // return false, -1;
end function;

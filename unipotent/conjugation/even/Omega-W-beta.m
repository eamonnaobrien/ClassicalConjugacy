freeze;

import "../../util.m": MyCommutatorSpace, FixesQuadraticForm; 
import "../odd/basics.m": SetupT;
import "Sp-W-beta.m": MyEvaluatePoly;

// handle W_n and W_n(beta) for GO even char 

GenerateRelation := function (V, F, PB, S, w1, w1_RHS) 
   d := Dimension (V);
   C, M := CoefficientsAndMonomials (w1_RHS);
   coords := [F| ];
   for i in [1..#PB] do
      pos := Position (M, PB[i]);
      if pos ne 0 then coords[i] := C[pos]; else coords[i] := 0; end if;
   end for;

   c_rhs := Coordinates (S, V!coords);

   C, M := CoefficientsAndMonomials (w1);
   coords := [F| ];
   for i in [1..#PB] do
      pos := Position (M, PB[i]);
      if pos ne 0 then coords[i] := C[pos]; else coords[i] := 0; end if;
   end for;
   c := Coordinates (S, V!coords);
   rel := &+[c[i] * c_rhs[d - i + 1]: i in [1..d]];
   return rel;
end function;

GOBasicSetup := function (rep, form, beta)
   d := Degree (rep);
   n := d div 2;
   k := n div 2;

   F := BaseRing (rep);

   q := #F;
   V := QuadraticSpace (form);

   mat_T := SetupT (rep);
   T := mat_T;

   w := V.1; x := V.(n + 1);

   B := [w * T^i: i in [0..n - 1]] cat [x * T^i: i in [0..n - 1]];

   W := VectorSpaceWithBasis (B);
   C := [Coordinates (W, W!V.i): i in [1..d]];
   C_coords := C;

   if IsEven (n) then m := 4*k; else m := 4*k + 3; end if;

   F := RationalFunctionField (GF(q), m);

   P<w, x, T> := PolynomialRing (F, 3);

   V := VectorSpace (F, d);

   f_pols := [&+[C[j][i]* T^(i - 1): i in [1..n]]: j in [1..n]];
   g_pols := [&+[C[j][i] * T^(i - (n + 1)): i in [n + 1..d]]: j in [1..n]];

   h_pols := [&+[C[n + j][i]* T^(i - 1): i in [1..d div 2]]: j in [1..n]];
   k_pols := [&+[C[n + j][i] * T^(i - (n + 1)): i in [n + 1..d]]: j in [1..n]];

   PB := [w * T^i: i in [0..n - 1]] cat [x * T^i: i in [0..n - 1]];

   C_coords := [V!x: x in C_coords];
   S := VectorSpaceWithBasis (C_coords);

   if IsOdd (n) then 
      w1 := w + &+[F.i * (w * h_pols[2*i - 1] + x * k_pols[2*i - 1]): i in [1..k + 1]];
      x1 := &+[F.(k + 1 + i)   * (w * f_pols[2*i - 1] + x * g_pols[2*i - 1]): i in [1..k + 1]] + 
            &+[F.(2*k + 2 + i) * (w * h_pols[i] + x * k_pols[i]): i in [1..2*k + 1]];
   else 
      if k gt 1 then 
         w1 := w + &+[x * F.i * k_pols[i]: i in [1..k - 1]] + x * F.k * k_pols[2 * k];
      else 
         w1 := w + x * F.k * k_pols[2 * k];
      end if;
      x1 := &+[F.(k + i) * w * f_pols[2*i]: i in [1..k]] + 
            &+[F.(2*k + i) * x * k_pols[i]: i in [1..2*k]];
   end if;

   alpha := 0;
   Rels := [];

   if IsEven (n) then bound := k - 1; else bound := 2 * k; end if;

   for i in [1..bound] do 
      alpha_RHS := w1 * f_pols[i + 1] + x1 * g_pols[i + 1];
      rel := GenerateRelation (V, F, PB, S, w1, alpha_RHS);
      Append (~Rels, rel);
   end for;
   for i in [1..bound] do 
      alpha_RHS := w1 * h_pols[i + 1] + x1 * k_pols[i + 1];
      rel := GenerateRelation (V, F, PB, S, x1, alpha_RHS);
      Append (~Rels, rel);
   end for;
   for i in [1..n] do 
      alpha_RHS := w1 * h_pols[i] + x1 * k_pols[i];
      rel := GenerateRelation (V, F, PB, S, w1, alpha_RHS);
      Append (~Rels, rel);
   end for;

   if IsOdd (n) then 
      if IsEven (k) then 
         Append (~Rels, F.(k + 1) + beta * F.(k div 2 + 1)^2);
      else 
         if k eq 1 then 
            Append (~Rels, beta + F.(k + 1)); 
         else 
            Append (~Rels, F.(k + 1)); 
         end if;
      end if;
      rel := &+[F.(k + 1 + i) * F.(4*k + 3 - 2 * (i - 1)): i in [1..k + 1]]
                + beta * F.(2*k + 2 + k + 1)^2 + beta * (F.((k + 1) + (k div 2) + 1))^2;
      Append (~Rels, rel);
   else 
      rel := F.k;
      Append (~Rels, rel);
      rel := &+[F.(k + i) * F.(4*k - 1 - 2 * (i - 1)): i in [1..k]];
      Append (~Rels, rel);
   end if;

   return Rels, f_pols, g_pols, h_pols, k_pols;
end function;

GO_WBeta_ConjugationMatrix := function (IG, rep, form, h, beta: Limit := 100) 
   d := Nrows (rep);
   n := d div 2;
   k := n div 2;
   
   F := BaseRing (rep);
   q := #F;
   
   Rels, F, G, H, K := GOBasicSetup (rep, form, beta);
   
   V := QuadraticSpace (form);
   
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
   
      if IsEven (n) then 
         for i in [1..k - 1] do 
            Alpha[i] := DotProduct (w, w * MyEvaluatePoly (F[i + 1], mat_T) + x * MyEvaluatePoly (G[i + 1], mat_T));
             Beta[i] := DotProduct (x, w * MyEvaluatePoly (H[i + 1], mat_T) + x * MyEvaluatePoly (K[i + 1], mat_T));
         end for;
         for i in [1..n] do 
            Gamma[i] := DotProduct (w, w * MyEvaluatePoly (H[i], mat_T) + x * MyEvaluatePoly (K[i], mat_T));
         end for;
      else 
         for i in [1..2 * k] do 
            Alpha[i] := DotProduct (w, w * MyEvaluatePoly (F[i + 1], mat_T) + x * MyEvaluatePoly (G[i + 1], mat_T));
             Beta[i] := DotProduct (x, w * MyEvaluatePoly (H[i + 1], mat_T) + x * MyEvaluatePoly (K[i + 1], mat_T));
         end for;
         for i in [1..n] do 
            Gamma[i] := DotProduct (w, w * MyEvaluatePoly (H[i], mat_T) + x * MyEvaluatePoly (K[i], mat_T));
         end for;
      end if;

      IP := Alpha cat Beta cat Gamma;
   
      // two additional relations 
      Append (~IP, QuadraticNorm (w));
      Append (~IP, QuadraticNorm (x));

      M := [Rels[i] + IP[i]: i in [1..#Rels]];

      PT := Universe (M);
      RI:= RingOfIntegers (PT);
      M := [RI!M[i] : i in [1..#M]];
   
      I := Ideal (M);
      I := ChangeOrder (I, "grevlex");
      // "Groebner basis call";
      B := GroebnerBasis (I);
      assert IsZeroDimensional (I); 
      Solns := Variety (I);

      nmr := 0;
      for S in Solns do 
         nmr +:= 1;
         if IsEven (n) then
            B := [S[i]: i in [1..k]];
            C := [S[k + i]: i in [1..k]];
            D := [S[2*k + i]: i in [1..2 * k]];

            if k gt 1 then 
               b := &+[B[i] * K[i] : i in [1..k - 1]] + B[k] * K[2*k];
            else 
               b := B[k] * K[2*k];
            end if;

            c := &+[C[i] * F[2 * i] : i in [1..k]]; 
            d1 := &+[D[i] * K[i] : i in [1..2 * k]]; 
            mat_b := MyEvaluatePoly (b, T);
            mat_c := MyEvaluatePoly (c, T);
            mat_d := MyEvaluatePoly (d1, T);
            M := mat_b * mat_c + mat_d;
            x := (w * mat_c + x) * M^-1;
            w := (w + x * mat_b);
         else 
            B := [S[i]: i in [1..k + 1]];
            C := [S[k + 1 + i]: i in [1..k + 1]];
            D := [S[2*k + 2 + i]: i in [1..2 * k + 1]];
   
            f := 1 + &+[B[i + 1] * H[2 * i + 1] : i in [0..k]];
            g := &+[B[i + 1] * K[2 * i + 1] : i in [0..k]];
            r := &+[C[i + 1] * F[2 * i + 1] : i in [0..k]] + &+[D[i + 1] * H[i + 1] : i in [0..2 * k]];
            s := &+[C[i + 1] * G[2 * i + 1] : i in [0..k]] + &+[D[i + 1] * K[i + 1] : i in [0..2 * k]];

            mat_f := MyEvaluatePoly (f, T);
            mat_g := MyEvaluatePoly (g, T);
            mat_r := MyEvaluatePoly (r, T);
            mat_s := MyEvaluatePoly (s, T);
     
            M :=  mat_g * mat_r + mat_f * mat_s;
            x := (w * mat_r + x * mat_f) * M^-1;
            w := (w + x * mat_g) * mat_f^-1;
         end if;
   
         mat_F := [MyEvaluatePoly (F[i], T): i in [1..#F]];
         mat_G := [MyEvaluatePoly (G[i], T): i in [1..#F]];
         mat_H := [MyEvaluatePoly (H[i], T): i in [1..#F]];
         mat_K := [MyEvaluatePoly (K[i], T): i in [1..#F]];
   
         B := [w * mat_F[i] + x * mat_G[i] : i in [1..#F]] cat [w * mat_H[i] + x * mat_K[i] : i in [1..#F]]; 

         CB := GL(d, q) ! [Eltseq (x): x in B];
   
         // "first assert - conjugates";
         assert CB * h * CB^-1 eq rep;
         // "second assert -- member";
         found := FixesQuadraticForm (CB, form);
         if found then 
            assert nmr eq 1;
            return true, CB; 
         end if; 
         // break S;
      end for;
      if Ntries gt 1 then assert beta ne 0; end if;
   until found or Ntries gt Limit;
   error "GO_WBeta_ConjugationMatrix: Failed to decide conjugacy"; 
end function;

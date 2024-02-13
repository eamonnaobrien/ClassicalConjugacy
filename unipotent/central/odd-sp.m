freeze;

import "../util.m": MyInsert, CentralisedSpace, MyInnerProduct, 
   NonSquare, MySort, FixesForm;
import "../Sp-Orthogonal-order.m": SpCentraliserDimension_Odd; 
import "even-sp.m": Sp_QSubgroup;

// Sp odd characteristic

// semisimple generators 

// odd block size -- set up Sp 
Sp_Case1 := function (g, q, N, a, d: OrderOnly := false) 
   order := ChevalleyGroupOrder ("C", d, q);
   if OrderOnly then return [], order; end if;

   MA := MatrixAlgebra (GF(q), 2);
   J := MA![0,-1,1,0];
   K := DiagonalJoin ([J: i in [1..d]]);
   G := IsometryGroup (K);

   index := [i : i in [1..#N] | N[i][1] in {"w", "x"} and N[i][3] eq a];

   X := [DiagonalJoin ([G.i: j in [1.. #index div (2 * d)]]): i in [1..Ngens (G)]];
      
   m := Nrows (g);
   M := MatrixAlgebra (GF(q), m);
   A := Identity (M);
   
   Y := [GL(m, q) ! MyInsert (A, x, index, index): x in X];
   return Y, order;
end function;

// even block size - set up GO 
Sp_Case2 := function (r, f, q, N, a, beta: OrderOnly := false, Verify := false)

   index := [i : i in [1..#N] | N[i][1] in {"v"} and N[i][3] eq a];
   form := ExtractBlock (f, index, index);
   b := #index div (2 * a);

   MA := MatrixAlgebra (GF(q), #index);
   B := Identity (MA);
   for i in [#index div 2 + 1..#index by b] do
      B[i, i] := beta;
   end for;
   form := B * form * Transpose (B);

   K := ExtractBlock (form, 1, #index - b + 1, b, b);

   if IsOdd (Nrows (K)) then 
      type := "circle"; 
   else 
      epsilon := (-1)^(Nrows (K) div 2) * Determinant (K);
      type := IsSquare (epsilon) select "plus" else "minus";
   end if;

   if Nrows (K) eq 1 then 
      G := sub<GL(1, q) | [-1]>;
      order := 2;
   else 
      G := IsometryGroup (K);
      if type eq "plus" then
         if Verify and Nrows (K) gt 2 then 
            // assert ClassicalType (G) cmpeq "orthogonalplus"; 
            _, type := ClassicalGroupType (G); assert type eq "GO+"; 
         end if;
         order := #GOPlus (Nrows (K), BaseRing (K));
      elif type eq "minus" then
         if Verify and Nrows (K) gt 2 then 
            // assert ClassicalType (G) cmpeq "orthogonalminus"; 
            _, type := ClassicalGroupType (G); assert type eq "GO-"; 
         end if;
         order := #GOMinus (Nrows (K), BaseRing (K));
      elif type eq "circle" then 
         order := #GO (Nrows (K), BaseRing (K));
      end if;
   end if;
   if OrderOnly then return [], order; end if;

   X := [DiagonalJoin ([G.i: j in [1.. #index div b]]): i in [1..Ngens (G)]];
   X := [B^-1 * x * B: x in X];

   m := Nrows (r);
   M := MatrixAlgebra (GF(q), m);
   A := Identity (M);
   
   Y := [GL(m, q) ! MyInsert (A, x, index, index): x in X];

   if Verify then 
      "Here check central property"; 
      assert {Order ((y, r)): y in Y} eq {1};
   end if;

   return Y, order;
end function;

// generators for semisimple piece 
// if OrderOnly then return order of semisimple piece 

Sp_SSGenerators_Odd := function (r, f, VBeta, N, T, q: OrderOnly := false)
   Gens := [];
   order := 1;

   W := T[1]; 
   for a in Set (W) do
      d := #[x: x in W | x eq a];
      X, ord := Sp_Case1 (r, q, N, a, d: OrderOnly := OrderOnly);
      order *:= ord;
      Gens cat:= X;
   end for;

   V := T[2];
   values_V := [v : v in Set (V)];
   Sort (~values_V);
   for a in values_V do 
      beta := [b[2] : b in VBeta | b[1] eq a];
      X, ord := Sp_Case2 (r, f, q, N, a, beta[#beta]: OrderOnly := OrderOnly);
      order *:= ord;
      Gens cat:= X;
   end for;
    
   return Gens, order;
end function;

Sp_V_beta := function (k, q, beta)
   assert IsOdd (q);

   d := 2 * k;
   M := MatrixAlgebra (GF(q), d);
   A := Identity (M);
   for i in [1..k] do
      for j in [i + 1..k] do 
         A[i][j] := (-1)^(i+j) * 2;
      end for;
   end for;

   for i in [1..k] do
      for j in [k + 1..2 * k] do 
         A[i][j] := (-1)^(i+j) * 2 * beta;
      end for;
   end for;
   
   for i in [k + 1..2 * k] do
      for j in [i + 1..2 * k] do 
         A[i][j] := (-1)^(i+j) * 2;
      end for;
   end for;
   return A;
end function;

Sp_W_rep := function (m, q : beta := 0)
   
   k := 2 * m + 1;
   d := 2 * k;
   M := MatrixAlgebra (GF(q), d);
   A := Identity (M);
   S := MatrixAlgebra (GF (q), 2);
   I := Identity (S);
   
   for i in [1..k] do
      for j in [i + 1..k] do
         InsertBlock (~A, (-1)^(i + j) * 2 * I, 2 * i - 1, 2 * j - 1);
      end for;
   end for;
   return A;
end function;

Sp_V_beta_form := function (k, q)
   d := 2 * k;
   M := MatrixAlgebra (GF(q), d);
   F := Zero (M);
   F[1, 2 * k] := (-1)^k;
   v := F[1, 2 * k];
   for i in [2..d] do
      v := -v;
      F[i, d - i + 1] := v;
   end for;
   return F;
end function;

Sp_W_form := function (m, q)
   k := 2 * m + 1;
   d := 2 * k;
   M := MatrixAlgebra (GF(q), d);
   F := Zero (M);
   m := (k - 1) div 2;
   S := MatrixAlgebra (GF (q), 2);
   B := Zero (S);
   B[1, 2] := (-1)^m; 
   B[2, 1] := -B[1,2];
   InsertBlock (~F, B, 1, d - 1);
   v := B;
   for i in [1..k - 1] do
      v := -v;
      InsertBlock (~F, v, 2 * i + 1, d - 2 * i - 1);
   end for;
   return F;
end function;

SpJordanBlock := function (k, q: beta := 1) 
   if IsEven (k) then
      return Sp_V_beta (k div 2, q, beta);
   else
      return Sp_W_rep ((k - 1) div 2, q: beta := beta);
   end if;
end function;

SpForm := function (k, q)
   if IsEven (k) then
      return Sp_V_beta_form (k div 2, q);
   else
      return Sp_W_form ((k - 1) div 2, q);
   end if;
end function;

Sp_ClassRep := function (m, q, beta)
   for i in [1..#m] do
      if IsOdd (m[i][1]) and IsOdd (m[i][2]) then 
         "Bad Jordan form description"; 
         return false, _, _; 
      end if;
   end for;
   d := &+[m[i][1] * m[i][2] : i in [1..#m]];

   R := [];
   for i in [1..#m] do 
      r := m[i][1]; 
      L := [-(r - 1) .. (r - 1) by 2];
      L := [x : x in L];
      if IsOdd (m[i][1]) then 
         for j in [1..m[i][2] div 2] do 
            Append (~R, L);
         end for;
      else 
         for j in [1..m[i][2]] do 
            Append (~R, L);
         end for;
      end if;
   end for;

   W := Set (&cat (R));
   W := [x : x in W];
   Sort (~W);

   L := [#x: x in R]; 

   rep := DiagonalJoin (<SpJordanBlock (L[i], q: beta := beta[i]): i  in [1..#L]>);
   form := DiagonalJoin (<SpForm (a, q): a in L>);

   L := [];
   for i in [1..#R] do
      if IsEven (#R[i]) then L[i] := R[i];
      else X := R[i]; L[i] := &cat([[x, x]: x in X]);
      end if;
   end for;
   
   L := &cat (L);
   pos := &cat[[i : i in [1..#L] | L[i] eq c]: c in W];
   S := Sym (d);
   P := PermutationMatrix (GF(q), S!pos);

   S := [<w, #[x : x in L | x eq w]>: w in W];
   
   return P * rep * Transpose (P), P * form * Transpose (P), S, R, P, rep;
end function;

// multiple J2 and J1 blocks 
   
J2andJ1Blocks := function (g, form: GLO := false)
   
   G := Parent (g);
   d := Degree (G);
   F := BaseRing (G);
   q := #F;
   
   MA := MatrixAlgebra (F, d);
   UB := [];
   
   u := g;
   
   V := VectorSpace (G);
   N := V;
   
   repeat 
      CS := sub< V | [v - v * g: v in Basis (N)]>;
      if Dimension (CS) gt 0 then 
         CV := CentralisedSpace (g);
         repeat 
            repeat e := Random (N); until not (e in CV);
            f := e * g - e;
            gamma := MyInnerProduct (form, e, f, q);
         until gamma ne 0;
         U := sub< V | [e, -gamma^-1 * f]>;
         Append (~UB, [e, -gamma^-1 * f]);
         L := [Eltseq (w) : w in Basis (U)];
         r := 2;
         W := KMatrixSpace (F, d, r) !  &cat [[L[i][j] : i in [1..r]]: j in [1..d]];
         N := NullSpace (form * W) meet N;
      end if;
   until Dimension (N) eq 0 or Dimension (CS) eq 0;
   
   B := &cat (UB) cat Basis (N);
   B := MA ! B;
   // assert B * form * Transpose (B) eq form;
   
   h := B * g * B^-1;
   
   L := VectorSpaceWithBasis (B);
   // assert MA ! [Eltseq (L!form[i]): i in [1..Nrows (form)]] eq form;
   
   _, _, w := JordanForm (g);
   nmr_j2 := d - #[x: x in w | x[2] eq 1];
   n := nmr_j2 div 2;
   // This to to get GLO labelling 
   if GLO then 
      beta := &*[h[2 * i - 1, 2 * i]: i in [1..n]] * (-1)^n;
   else 
      beta := &*[h[2 * i - 1, 2 * i]: i in [1..n]] * (-2)^n;
   end if;
   // element is conjugate to V_beta (2) + V(2)^(a - 1) 
   
   return beta;
end function;
   
// restrict g and form to subspace 
// used for both Sp and Orthogonal, hence defn of V 
RestrictToOnePart := function (g, form, k: Perp := false)
   G := Parent (g);
   d := Nrows (g);
   F := BaseRing (G);
   q := #F;
   
   V := VectorSpace (F, d, form);
   // EOB -- temporary to address bug in 2.25-8 and earlier 
   // with vector space inheriting Involution 
   // Ensure that V is not unitary
   if assigned V`Involution then delete V`Involution; end if;
   CS := V; 
   for i in [1..k] do 
      CS := sub< V | [v - v * g: v in Basis (CS)]>;
   end for;
   N := Perp eq true select OrthogonalComplement (V, CS) else CS;
   radN := Radical (N);
   B := Basis (radN);
   b := #B;
   SS := ExtendBasis (radN, N);
   BN := VectorSpaceWithBasis (SS);
   
   F := Zero (MatrixAlgebra (GF(q), #SS - b));
   for i in [b + 1..#SS] do
      for j in [b + 1..#SS] do
         F[i - b, j - b] := InnerProduct (SS[i], SS[j]);
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
   small_form := GL(#M, q) ! F;
   return small_g, small_form;
end function;
   
ProcessOneBlock := function (g, form, a: GLO := false)
   if a eq 1 then 
      small_g := g; small_form := form;
   else 
      small_g, small_form := RestrictToOnePart (g, form, a - 1: Perp := false);
   end if;
   
   two_g, two_form := RestrictToOnePart (small_g, small_form, 2: Perp := true);
   
   if Nrows (two_g) ne Nrows (small_g) then 
      small_g, small_form := RestrictToOnePart (small_g, small_form, 1: Perp := false);
   end if;
   return J2andJ1Blocks (two_g, two_form: GLO := GLO), small_g, small_form;
end function;
   
// identify square or non-square parameter for g 
SpIdentifyParameter := function (g, form: GLO := false) 
   a, b, c := JordanForm (g);
   blocks_info := [x[2]: x in c];
   even := [x : x in blocks_info | IsEven (x)];
   Sort (~even);
   
   a := even[1] div 2;
   val, small_g, small_form := ProcessOneBlock (g, form, a: GLO := GLO);

   F := BaseRing (g);
   if IsSquare (val) then val := F!1; else val := NonSquare (F); end if;
   
   return val, small_g, small_form;
end function;

SpCompleteLabels := function (m) 
   V := []; W := [];
   for i in [1..#m] do
      a := m[i][1]; b := m[i][2];
      if IsEven (a) then
         V cat:= [a div 2: i in [1..b]];
      else
         W cat:= [a: i in [1..b div 2]];
      end if;
   end for;
  
   T := [W, V];
   
   R := []; N := [];
   for i in [1..2] do
      if #T[i] gt 0 then 
         A := T[i]; 
         if i eq 1 then 
            for k in [1..#A] do 
               r := A[k];
               offset := #[x : x in [A[j]: j in [1..k - 1]] | x eq r];
               L := [-(r - 1) .. (r - 1) by 2];
               Append (~R, L cat L); 
               Append (~N, [<"w", L[i], r, offset + 1>: i in [1..#L]] cat 
                           [<"x", L[i], r, offset + 1>: i in [1..#L]]);
            end for;
         else
            for k in [1..#A] do 
               r := 2 * A[k];
               offset := #[x : x in [A[j]: j in [1..k - 1]] | x eq r div 2];
               L := [-(r - 1) .. (r - 1) by 2];
               Append (~R, L); 
               Append (~N, [<"v", L[i], r div 2, offset + 1>: i in [1..#L]]);
            end for;
         end if;
      end if;
   end for;
       
   W := Set (&cat (R));
   W := [x : x in W];
   Sort (~W);

   L := &cat (R);
   N := &cat (N);
   pos := &cat[[i : i in [1..#L] | L[i] eq c]: c in W];

   N := [N[i]: i in pos];

   M := [];
   for i in [1..#N] do
      r := N[i][1] in {"v"} select 2 * N[i][3] else N[i][3];
      M[i] := N[i][1] cat IntegerToString (r);
   end for;

   Wt := [<w, #[x : x in L | x eq w]>: w in W];
   return Wt, N, T;
end function;

// g has parameters beta 
// write down special rep for g and label fully the weight space 

Sp_ConvertToSpecialRep := function (g, beta)
   G := Parent (g);
   F := BaseRing (G);
   q := #F;
   J, CB, b := JordanForm (g);
   s := [b[i][2]: i in [1..#b]];
   m := [<x, #[y: y in s | y eq x]>: x in Set (s)];
   m := MySort (m);
   r, f, a := Sp_ClassRep (m, q, beta);
   J1, CB1 := JordanForm (r);
   cb := Generic (G) ! (CB1^-1 * CB);
   assert cb * g * cb^-1 eq r;
   Wt, N, T := SpCompleteLabels (m);
   return Generic (G) ! r, f, Generic (G) ! cb, m, a, N, T;
end function;
   
// identify parameters for element g preserving form 
SpParameters := function (g, form: GLO := false)
   a, b, c := JordanForm (g);
   F := BaseRing (Parent (g));
   blocks := [x[2]: x in c];
   even := {x : x in blocks | IsEven (x)};
   even := [x: x in even];
   Sort (~even);
   val := [];
   small_g := g; small_form := form;
   for i in [1..#even] do
      val[i], small_g, small_form := SpIdentifyParameter (small_g, small_form: GLO := GLO);
   end for;

   L := [];
   S := Set (blocks);
   S := [x: x in S];
   Sort (~S); 
   params := [];
   for s in S do
      nmr := #[x: x in blocks | x eq s];
      if IsEven (s) then
         L cat:= [s: j in [1..nmr]];
         if nmr gt 1 then 
            params cat:= [1: l in [1..nmr - 1]] cat [val[Position (even, s)]];
         else 
            params cat:= [val[Position (even, s)]];
         end if;
      else 
         L cat:= [s: j in [1..nmr div 2]];
         params cat:= [F!0: l in [1..nmr div 2]];
      end if;
   end for;
   params := [<L[i], params[i]>: i in [1..#L]];

   return params;
end function;

// return centraliser of special rep for g in copy of Sp
// OrderOnly: report only the order
// Verify: check the order of the centraliser is as claimed

SpUnipotentCentraliser_Odd := function (G, g, form: OrderOnly := false, Verify := false) 
   F := BaseRing (G);
   e := Degree (F);
   q := #F; 
   assert IsOdd (q);
   d := Degree (G);

   Beta := SpParameters (g, form);
   beta := [Beta[i][2]: i in [1..#Beta]];
   r, f, CB, m, W, N, T := Sp_ConvertToSpecialRep (g, Reverse (beta));
   assert FixesForm (r, f);

   // generators and order for semisimple part of centraliser
   VBeta := [<x[1] div 2, x[2]>: x in Beta | IsEven (x[1])];
   Add, order := Sp_SSGenerators_Odd (r, f, VBeta, N, T, q: OrderOnly := OrderOnly);
   
   // determine order of p-subgroup of centraliser 
   dim := SpCentraliserDimension_Odd (m);
   order *:= q^dim; 
   if OrderOnly then return order, T, VBeta, m; end if;

   // determine p-subgroup of centraliser 
   Q := Sp_QSubgroup (W, q, [N[j][1]: j in [1..#N]]);

   Q := UnipotentMatrixGroup (Q);
   P, phi, tau := PCPresentation (Q);
   CP := Centraliser (P, phi (r));
   C := CP @ tau;
   assert IsCentral (C, r);

   // assert dim * e eq NPCgens (CP);

   C := sub<Generic (G) | C, Add>;
   assert IsCentral (C, r);

   if Verify then 
      "Centraliser order is ", order;
      assert LMGOrder (C) eq order;
   else
      O := Factorisation (order);
      C`FactoredOrder := O;
      C`Order := order;
   end if;
   return C, r, f, CB;
end function;

// label which should accord with GLO label 
GLOLabel_SpOdd := function (g, form)
   return Sort (SpParameters (g, form: GLO := true));
end function;

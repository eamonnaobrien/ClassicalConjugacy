freeze;

import "../util.m": MyInsert, CentralisedSpace, MyInnerProduct, NonSquare, 
    MySort, KernelOfHom, FixesForm, MySpinorNorm;
import "../Sp-Orthogonal-order.m": GOCentraliserDimension_Odd;
import "odd-sp.m": RestrictToOnePart;

// centraliser in GO / SO / Omega odd characteristic

// additional semisimple generators
// even block size -- construct generators for Sp 
GO_Case1 := function (g, q, N, a, d: OrderOnly := false)
   C := ChevalleyGroup ("C", d, q);
   order := #C;
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
   
   Y := [MyInsert (A, x, index, index): x in X];
   Y := [GL(m, q) ! y: y in Y];
   return Y, order;
end function;

// odd block size -- construct generators for GO 
GO_Case2 := function (r, f, q, N, a, beta: OrderOnly := false, Verify := false)

   index := [i : i in [1..#N] | N[i][1] in {"v"} and N[i][3] eq a];
   ff := ExtractBlock (f, index, index);
   m := Nrows (r);
   b := #index div (2 * a + 1);

   MA := MatrixAlgebra (GF(q), #index);
   B := Identity (MA);
   start := (a + 1) * b;
   for i in [start + 1..#index by b] do
      B[i, i] := beta;
   end for;
   // rep := B * r * B^-1;
   form := B * ff * Transpose (B);

   K := ExtractBlock (form, 1, #index - b + 1, b, b);
   if IsOdd (Nrows (K)) then 
      type := "circle";
   else 
      epsilon := (-1)^(Nrows (K) div 2) * Determinant (K);
      type := IsSquare (epsilon) select "plus" else "minus";
   end if;

   if Nrows (K) eq 1 then 
      G := sub <GL(1, q) | [-1]>;
      order := 2;
   else 
      G := IsometryGroup (K);
      if type eq "plus" then
         if Verify then assert ClassicalType (G) cmpeq "orthogonalplus"; end if;
         order := #GOPlus (Nrows (K), BaseRing (K));
      elif type eq "minus" then
         if Verify then assert ClassicalType (G) cmpeq "orthogonalminus"; end if;
         order := #GOMinus (Nrows (K), BaseRing (K));
      elif type eq "circle" then
         order := #GO (Nrows (K), BaseRing (K));
      end if;
   end if;
   if OrderOnly then return [], order; end if;
   if Verify then assert order eq LMGOrder (G); end if;

   X := [DiagonalJoin ([G.i: j in [1.. #index div b]]): i in [1..Ngens (G)]];
   X := [B^-1 * x * B: x in X];

   M := MatrixAlgebra (GF(q), m);
   A := Identity (M);
   
   Y := [MyInsert (A, x, index, index): x in X];
   Y := [GL(m, q) ! y: y in Y];
   if Verify then assert {Order ((y, r)): y in Y} subset {1}; end if;

   return Y, order;
end function;

// generators for semisimple piece
// if OrderOnly then return order of semisimple piece

GO_SSGenerators_Odd := function (r, f, VBeta, N, T, q: OrderOnly := false)
   Gens := [];
   order := 1;
   W := T[1]; 
   for a in Set (W) do
      d := #[x: x in W | x eq a];
      X, ord := GO_Case1 (r, q, N, a, d: OrderOnly := OrderOnly);
      order *:= ord;
      Gens cat:= X;
   end for;

   V := T[2];
   V := [2 * x + 1: x in V];
   values_V := [v : v in Set (V)];
   Sort (~values_V);
   for a in values_V do 
      beta := [b[2] : b in VBeta | b[1] eq a];
      X, ord := GO_Case2 (r, f, q, N, (a - 1) div 2, beta[#beta]: 
                          OrderOnly := OrderOnly);
      order *:= ord;
      Gens cat:= X;
   end for;
    
   return Gens, order;
end function;

// sort out parameters; upper-triangular rep; 

GOProcessOneBlock := function (g, form, a: GLO := false)
   if a eq 0 then 
      small_g := g; small_form := form;
   else 
      small_g, small_form := RestrictToOnePart (g, form, a: Perp := false);
   end if;

   two_g, two_form := RestrictToOnePart (small_g, small_form, 1: Perp := true);

   a, b, c := JordanForm (small_g);
   blocks_info := [x[2]: x in c];
   odd := {x : x in blocks_info | IsOdd (x)};

   if (odd) ne {1} then 
      small_g, small_form := RestrictToOnePart (small_g, small_form, 1: Perp := false);
   end if;

   if GLO then 
      k := Nrows (two_form); 
      det := Determinant (two_form);
      // "det is ", det;
      return det / 2^k, small_g, small_form;
   end if;

   return Determinant (two_form), small_g, small_form;
end function;

// identify parameters for g

GOIdentifyParameter := function (g, form: GLO := false)
   F := BaseRing (g);
   if Nrows (g) eq 1 then 
      val := Determinant (form);
      if GLO then val := val / 2; end if;
      if IsSquare (val) then val := F!1; else val := NonSquare (F); end if;
      return val, g, form;
   end if;

   a, b, c := JordanForm (g);
   blocks_info := [x[2]: x in c];
   odd := [x : x in blocks_info | IsOdd (x)];
   Sort (~odd);

   a := odd[1] div 2;
   val, small_g, small_form := GOProcessOneBlock (g, form, a: GLO := GLO);
   val := IsSquare (val) select F!1 else NonSquare (F);

   return val, small_g, small_form;
end function;

// identify GO / SO parameters for g 
// this does NOT distinguish classes in Omega

OrthogonalParameters := function (g, form: GLO := false)
   a, b, c := JordanForm (g);
   F := BaseRing (g);

   blocks := [x[2]: x in c];
   odd := {x : x in blocks | IsOdd (x)};
   odd := [x: x in odd];
   Sort (~odd);
   val := [];
   small_g := g; small_form := form;
   for i in [1..#odd] do
      val[i], small_g, small_form := GOIdentifyParameter (small_g, small_form: GLO := GLO);
   end for;

   L := [];
   S := Set (blocks);
   S := [x: x in S];
   Sort (~S);

   params := [];
   for s in S do
      nmr := #[x: x in blocks | x eq s];
      if IsOdd (s) then
         L cat:= [s: j in [1..nmr]];
         if nmr gt 1 then
            params cat:= [1: l in [1..nmr - 1]] cat [val[Position (odd, s)]];
         else
            params cat:= [val[Position (odd, s)]];
         end if;
      else
         L cat:= [s: j in [1..nmr div 2]];
         params cat:= [F!0: l in [1..nmr div 2]];
      end if;
   end for;
   params := [<L[i], params[i]>: i in [1..#L]];

   return params;
end function;

// matrix generators for Q 
GOTriple := function (d, q, i, j, k, p1, beta: second := false)
   F := GF (q);
   lambda := PrimitiveElement (F);
   e := Degree (F);
   MA := MatrixAlgebra (GF (q), d);
   L := [GL(d, F) | ];

   for f in [0..e - 1] do 
      A := Identity (MA);
      v := lambda^f;
      if second then 
         one := v^2 * beta; two := 2 * (-1)^((-p1) div 2);
         alpha := -one / two;
         mu := -beta * v / ((-1)^((-p1) div 2));
      else 
         one := v^2 * beta; two := 2 * (-1)^(p1 div 2);
         alpha := -one / two;
         mu := -beta * v / ((-1)^(p1 div 2));
      end if;
      assert one + alpha * two eq 0;
      A[i,k] := v;
      A[i,j] := alpha;
      A[k,j] := mu;
      Append (~L, A);
   end for;
   return L;
end function;

// matrix generators for Q 
GOQuad := function (d, q, i, j, k, l, p1, p2: second := false)
   F := GF (q);
   lambda := PrimitiveElement (F);
   e := Degree (F);
   MA := MatrixAlgebra (GF (q), d);
   L := [GL(d, F) | ];
   for f in [0..e - 1] do 
      A := Identity (MA);
      A[i,k] := lambda^f;
      x := ((-1)^(p1 div 2));
      if second then 
         y := ((-1)^((-p2) div 2));
      else
         y := ((-1)^(p2 div 2));
      end if;
      sgn := x eq y select -1 else 1;
      assert sgn * x + y eq 0;
      A[j,l] := sgn * lambda^f;
      Append (~L, A);
   end for;
   return L;
end function;

GO_V_beta := function (k, q, beta)
   d := 2 * k + 1;
   M := MatrixAlgebra (GF(q), d);
   A := Identity (M);
   for i in [1..k + 1] do
      for j in [i + 1..k + 1] do 
         A[i][j] := (-1)^(i+j) * 2;
      end for;
   end for;

   for i in [1..k + 1] do
      for j in [k + 2..2 * k + 1] do 
         A[i][j] := (-1)^(i+j) * 2 * beta;
      end for;
   end for;
   
   for i in [k + 2..2 * k + 1] do
      for j in [i + 1..2 * k + 1] do 
         A[i][j] := (-1)^(i+j) * 2;
      end for;
   end for;
   return A;
end function;

GO_W_rep := function (m, q)
   k := 2 * m;
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

GO_V_beta_form := function (k, q, beta)
   d := 2 * k + 1;
   M := MatrixAlgebra (GF(q), d);
   F := Zero (M);
   F[1, d] := (-1)^k;
   v := F[1, d];
   for i in [2..d] do
      v := -v;
      F[i, d - i + 1] := v;
   end for;
   F[k + 1, k + 1] := beta;
   return F;
end function;

GO_W_form := function (m, q)
   k := 2 * m;
   d := 2 * k;
   M := MatrixAlgebra (GF(q), d);
   F := Zero (M);
   m := k div 2;
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

GOJordanBlock := function (k, q: beta := 1) 
   if IsOdd (k) then
      return GO_V_beta ((k - 1) div 2, q, beta);
   else
      return GO_W_rep ((k) div 2, q);
   end if;
end function;

GOForm := function (k, q, wt: beta := 1)
   if IsOdd (k) then
      return GO_V_beta_form ((k - 1) div 2, q, beta);
   else
      return GO_W_form (k div 2, q);
   end if;
end function;

GO_ClassRep := function (m, q, beta)
   for i in [1..#m] do
      if IsEven (m[i][1]) and IsOdd (m[i][2]) then 
         error "Bad Jordan form description"; 
      end if;
   end for;

   d := &+[m[i][1] * m[i][2] : i in [1..#m]];

   R := [];
   for i in [1..#m] do 
      r := m[i][1]; 
      L := [-(r - 1)..(r - 1) by 2];
      L := [x : x in L];
      if IsEven (m[i][1]) then 
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

   wt := [x : x in W | IsOdd (x)];

   assert #beta eq #L;
   rep := DiagonalJoin (<GOJordanBlock (L[i], q: beta := beta[i]): i  in [1..#L]>);
   form := DiagonalJoin (<GOForm (L[i], q, wt: beta := beta[i]): i in [1..#L]>);

   L := [];
   for i in [1..#R] do
      if IsOdd (#R[i]) then 
         L[i] := R[i];
      else 
         X := R[i]; L[i] := &cat([[x, x]: x in X]);
      end if;
   end for;
   
   L := &cat (L);
   pos := &cat[[i : i in [1..#L] | L[i] eq c]: c in W];
   S := Sym (d);
   P := PermutationMatrix (GF(q), S!pos);

   S := [<w, #[x : x in L | x eq w]>: w in W];
   
   return P * rep * Transpose (P), P * form * Transpose (P), S, R, P;
end function;

// Q-subgroup 

GO_QSubgroup := function (a, q, form)
   aa := &cat[[x[1]: i in [1..x[2]]]: x in a];
   zeros := [i: i in [1..#aa] | aa[i] eq 0];
   beta := [form[i][i]: i in zeros];

   weight := [a[i][1]: i in [1..#a]];
   odd := 0 in weight; 

   mult := [a[i][2]: i in [1..#a]];
   d := &+mult;

   full := [[weight[i]: j in [1..mult[i]]]: i  in [1..#weight]]; 
   full := &cat (full);

   // first and second of each pair 
   index := [i : i in [1..#full] | IsOdd (full[i])];
   first := [index[i]: i in [1..#index] | IsOdd (i)];
   second := [index[i]: i in [1..#index] | IsEven (i)];

   I := [];
   for j in [1..d] do 
      wj := full[j];
      if wj lt 0 then 
         for k in [j + 1..d] do 
            wk := full[k];
            if wk ne 0 and wk lt Abs (wj) then Append (~I, <j, k>); end if;
          end for;
      end if;
   end for;

   // record opposites 
   J := []; K := [];
   for w in weight do
      A := [i: i in [1..#full] | full[i] eq w]; 
      B := [i: i in [1..#full] | full[i] eq -w]; 
      if IsOdd (w) then 
         B := &cat[[B[2 * i], B[2 * i - 1]]: i in [1..#A div 2]];
      end if;
      for i in [1..#A] do 
         a := A[i]; b := B[i];
         if w lt 0 then K[a] := <a, b>; end if;
         J[a] := b;
         J[b] := a;
      end for;
   end for;

   T := [];
   zero := Position (full, 0);
   for z in [1..#full] do 
      if full[z] eq 0 then 
         T cat:= [<i, J[i], z>: i in [1..zero - 1]];
      end if;
   end for;

   L1 := [];
   R := I;
   for triple in T do 
       i := triple[1]; j := triple[2]; z := triple[3]; k := J[j]; ell := J[i];
       p1 := full[i]; p2 := full[j];
       Append (~L1, 
          GOTriple (d, q, i, j, z, p1, beta[Position (zeros, z)]: second := i in second));
   end for;
   L1 := &cat (L1);

   L := [];
   R := I;
   for pair in I do 
      i := pair[1]; j := pair[2]; k := J[j]; ell := J[i];
      p1 := full[i]; p2 := full[j];
      if IsEven (p1) and IsEven (p2) then 
         if p2 ne 0 and p2 le Abs (p1) then 
            Append (~L, GOQuad (d, q, i, j, k, ell, p1, p2));
            Exclude (~R, pair);
         end if;
      elif IsEven (p2) and IsOdd (p1) and i in second then 
         Append (~L, GOQuad (d, q, i, j, k, ell, -p1, -p2));
         Exclude (~R, pair);
      elif IsEven (p2) and IsOdd (p1) and i in first then 
         Append (~L, GOQuad (d, q, i, j, k, ell, p1, p2: second := true));
         Exclude (~R, pair);
      elif IsEven (p1) and IsOdd (p2) and j in first then
         Append (~L, GOQuad (d, q, i, j, k, ell, p1, p2));
         Exclude (~R, pair);
      elif IsEven (p1) and IsOdd (p2) and j in second then
         Append (~L, GOQuad (d, q, i, j, k, ell, p1, p2: second := true));
         Exclude (~R, pair);
      elif IsOdd (p1) and IsOdd (p2) and i in first and j in second then
         Append (~L, GOQuad (d, q, i, j, k, ell, p1, p2: second := true));
         Exclude (~R, pair);
      elif IsOdd (p1) and IsOdd (p2) and i in second and j in first then
         Append (~L, GOQuad (d, q, i, j, k, ell, p1, p2: second := true));
         Exclude (~R, pair);
      elif IsOdd (p1) and IsOdd (p2) and i in first and j in first then
         Append (~L, GOQuad (d, q, i, j, k, ell, p1, p2: second := false));
         Exclude (~R, pair);
      elif IsOdd (p1) and IsOdd (p2) and i in second and j in second then
         Append (~L, GOQuad (d, q, i, j, k, ell, -p1, -p2: second := false));
         Exclude (~R, pair);
      end if;
   end for;

   assert #R eq 0;

   L := &cat (L);
   L cat:= L1;
   Q := sub<GL(d, q) | L>;
   
   return Q, I, K, L, L1;
end function;

GOCompleteLabels := function (m) 

   V := []; W := [];
   for i in [1..#m] do
      a := m[i][1]; b := m[i][2];
      if IsOdd (a) then
         V cat:= [(a - 1) div 2: i in [1..b]];
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
               L := [-(r - 1)..(r - 1) by 2];
               Append (~R, L cat L); 
               Append (~N, [<"w", L[i], r, offset + 1>: i in [1..#L]] cat 
                           [<"x", L[i], r, offset + 1>: i in [1..#L]]);
            end for;
         else
            for k in [1..#A] do 
               r := A[k];
               offset := #[x : x in [A[j]: j in [1..k - 1]] | x eq r];
               L := [-(2 * r)..(2*r) by 2];
               Append (~R, L); 
               Append (~N, [<"v", L[i], r, offset + 1>: i in [1..#L]]);
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

GO_ConvertToSpecialRep := function (g, beta)
   G := Parent (g);
   F := BaseRing (G);
   q := #F;
   J, CB, b := JordanForm (g);
   s := [b[i][2]: i in [1..#b]];
   m := [<x, #[y: y in s | y eq x]>: x in Set (s)];
   m := MySort (m);
   r, f, a := GO_ClassRep (m, q, beta);
   J1, CB1 := JordanForm (r);
   cb := Generic (G) ! (CB1^-1 * CB);
   assert cb * g * cb^-1 eq r;
   Wt, N, T := GOCompleteLabels (m);
   return Generic (G) ! r, f, Generic (G) ! cb, m, a, N, T;
end function;

// return centraliser in GO of special rep for g 
// OrderOnly: report only the order
// Verify: check the order of the centraliser is as claimed

OrthogonalUnipotentCentraliser_Odd := function (G, g, form: 
   OrderOnly := false, Verify := false) 

   Beta := OrthogonalParameters (g, form);
   beta := [Beta[i][2]: i in [1..#Beta]];
   r, f, CB, m, W, N, T := GO_ConvertToSpecialRep (g, Reverse (beta));
   assert g^(CB^-1) eq r;
   assert FixesForm (r, f);

   F := BaseRing (Parent (g));
   q := #F; 

   // generators and order for semisimple part of centraliser
   VBeta := [<x[1], x[2]>: x in Beta | IsOdd (x[1])];
   Add, order := GO_SSGenerators_Odd (r, f, VBeta, N, T, q);

   // determine order of p-subgroup of centraliser
   dim := GOCentraliserDimension_Odd (m);
   order *:= q^dim;
   if OrderOnly then return order, T, Beta, m; end if;

   Q := GO_QSubgroup (W, q, f);
   Q := UnipotentMatrixGroup (Q);
   P, phi, tau := PCPresentation (Q);
   CP := Centraliser (P, phi (r));
   C := CP @ tau;
   assert IsCentral (C, r);

   e := Degree (F);
   assert dim * e eq NPCgens (CP);
   assert Ngens (Q) eq NPCgens (P);

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

// centraliser of g in GO, SO or Omega  
MyOrthogonalCentraliser_Odd := function (S, g, form)
   P := IsometryGroup (form);
   G, r, f, CB := OrthogonalUnipotentCentraliser_Odd (P, g, form); 

   // intersection with SO
   if forall{x: x in Generators (S) | Determinant (x) eq 1} then
      E := BaseRing (S);
      C, eta := MultiplicativeGroup (E);
      phi := hom <Generic (G) -> C | x :-> Determinant (x) @@ eta>;
      images := [phi (G.i): i in [1..Ngens (G)]];
      I := sub<C | images>;
      images := [Eltseq (I!x): x in images];
      images := &cat (images);
      order := G`FactoredOrder;
      G := KernelOfHom (G, I, images);
      G`FactoredOrder := order / FactoredOrder (I);
      G`Order := Integers ()!(order / FactoredOrder (I));
   end if;

   // intersection with Omega
   if forall{x: x in Generators (S) | MySpinorNorm (x, form) eq 0} then
      C := AbelianGroup ([2]);
      phi := hom <Generic (G) -> C | x :-> MySpinorNorm (x, f)>;
      images := [phi (G.i): i in [1..Ngens (G)]];
      I := sub<C | images>;
      images := [Eltseq (I!x): x in images];
      images := &cat (images);
      order := G`FactoredOrder;
      G := KernelOfHom (G, I, images);
      G`FactoredOrder := order / FactoredOrder (I);
      G`Order := Integers ()!(order / FactoredOrder (I));
   end if;

   return G, r, f, CB;
end function;

// label in accordance with GLO paper 
GLOLabel_OrthogonalOdd := function (g, form)
   // odd dimension? ensure form has square determinant 
   if IsOdd (Nrows (form)) then 
      det := Determinant (form);
      if IsSquare (det) eq false then
         F := BaseRing (g);
         lambda := NonSquare (F);
         form := lambda * form;
         det := Determinant (form);
         assert IsSquare (det);
      end if;
   end if;
   return OrthogonalParameters (g, form: GLO := true);
end function;

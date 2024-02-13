freeze;

import "../util.m": ChooseAlpha, MyInsert, FixesForm;
import "../Sp-Orthogonal-order.m": SpUnipotentCentraliserOrder_Even; 
import "../even-char.m": SetupRep;
import "../conjugation/even/even-label.m": SpO_EvenLabel; 
import "even-orthogonal.m": FindIndices, GO_ClassRep_Even;

// Sp even characteristic centraliser 

// semisimple generators and components
GL2Subgroup := function (q)
   F := GF(q);
   gens := [ GL(2, F) ! [a + 1, a, a, a + 1]: a in Basis (F)];
   G := sub<GL(2, F) | gens>;
   return G;
end function;

SetupGL2Subgroup := function (d, q)
   H := GL2Subgroup (q);
   gens := [H.i: i in [1..Ngens (H)]];
   L := [];
   nr := d div 2;
   for m in [1..#gens] do 
      g := gens[m];
      A := DiagonalJoin ([g: k in [1..nr]]); 
      Append (~L, A);
   end for;
   return sub<GL(d, q) | L>;
end function;

SetupBlock := function (d, q, form: type := "Sp") 
   a := Nrows (form) div 2;
   if type eq "Sp" then 
      tr := TransformForm (form, "symplectic");
      H := Sp (2 * a, q);
      H := H^(tr^-1);
   else 
      H := GL2Subgroup (q);
   end if;

   MA := MatrixAlgebra (GF(q), 2 * a);
   gens := [H.i: i in [1..Ngens (H)]];
   gens := [MA!g: g in gens];

   L := [];
   n := Nrows (form); nr := d div n;
   for m in [1..#gens] do 
      g := gens[m];
      A := DiagonalJoin ([g: k in [1..nr]]); 
      Append (~L, A);
   end for;
   return sub<GL(d, q) | L>;
end function;

SetupBlocks := function (I, q, a, form: type := "Sp");
   m := #I;
   J := [I[i]: i in [1..2 * a]];
   K := [I[i]: i in [m - 2* a + 1..m]];
   small := ExtractBlock (form, J, K);
   f := ExtractBlock (form, I, I);
   if type eq "orthogonal" then small +:= Transpose (small); end if;
   return SetupBlock (m, q, small), f;
end function;

OrthogonalBlock := function (d, q, form, type) 
   a := Nrows (form) div 2;
   tr := TransformForm (form, type);
   if type eq "orthogonalminus" then 
      H := GOMinus (2 * a, q);
   else
      H := GOPlus (2 * a, q);
   end if;

   H := H^(tr^-1);
   MA := MatrixAlgebra (GF(q), 2 * a);
   gens := [H.i: i in [1..Ngens (H)]];
   gens := [MA!g: g in gens];

   L := [];
   n := Nrows (form); nr := d div n;
   for m in [1..#gens] do 
      g := gens[m];
      A := DiagonalJoin ([g: k in [1..nr]]); 
      Append (~L, A);
   end for;
   return sub<GL(d, q) | L>;
end function;

OrthogonalBlocks := function (r, I, q, a, form, type)
   small_r := ExtractBlock (r, I, I);

   if type eq "orthogonalminus" then 
      beta := ChooseAlpha (q); 
   else 
      beta := 0; 
   end if;

   M := MatrixAlgebra (GF(q), 2);
   small_f := M![beta, 1, 0, beta];
   other := M![0,1,0,0];
   if a gt 1 then 
      small := DiagonalJoin (DiagonalJoin (<other: i in [1..a - 1]>), small_f);
   else 
      small := small_f;
   end if;
   return OrthogonalBlock (#I, q, small, type);
end function;

LargerMatGroup := function (d, q, B, I)
   MA := MatrixAlgebra (GF(q), d);
   L := [];
   gens := [B.i: i in [1..Ngens (B)]];
   for i in [1..#gens] do 
      x := Identity (MA);
      for j in I do 
         for k in I do 
            w := gens[i][Position (I, j), Position (I, k)];
            x[j, k] := w;
         end for;
      end for;
      Append (~L, x);
   end for;
   return sub<GL(d, q) | L>;
end function;

CaseOneAndTwo := function (T)
   W := T[1]; W_beta := T[3]; V := T[2]; V_alpha := T[4]; 
   R := [];
   for m in Set (W cat W_beta) do 
      if IsOdd (m) then 
         l := m div 2;
         good := l eq 0 or (l + 1 in V cat V_alpha or l in V cat V_alpha); 
         if good then Append (~R, m); end if;
      end if;
   end for;
   return R; 
end function;

CaseThree := function (T)
   W := T[1]; W_beta := T[3]; V := T[2]; V_alpha := T[4]; 
   R := [];
   for m in Set (W cat W_beta) do 
      if IsOdd (m) then 
         l := m div 2;
         if l gt 0 then 
            common := {x : x in V cat V_alpha} meet {l + 1, l};
            if #common eq 0 then Append (~R, m); end if;
         end if;
      end if;
   end for;
   return R; 
end function;

AdditionalMatrices := function (m, d, q)
   l := MatrixAlgebra (GF(q), 2) ! [1,1,1,1];
 
   MA := MatrixAlgebra (GF(q), m);
   a := (m - 2) div 2;
   gens := [];
   for i in [1..a] do 
      A := Identity (MA);
      I := [(i - 1) * 2 + 1, 2 * i]; J := [m - 1, m];
      A := MyInsert (A, l, I, J);
      A := MyInsert (A, l, J, I);
      nr := d div m;
      L := DiagonalJoin (<A: i in [1..nr]>);
      Append (~gens, L);
   end for;
   return sub<GL(d, q) | gens>;
end function;

// generators for semisimple piece 

Sp_SSGenerators_Even := function (r, form, m, T, N, P, phi, tau, N_full)
   d := Nrows (r);
   q := #BaseRing (r);

   W := T[1]; W_beta := T[3]; V := T[2]; V_alpha := T[4]; 

   Gens := [];

   // Sp 
   u := phi (r);
   for m in Set (W) do 
      if IsEven (m) then
         // "Case a: m is ", m;
         a := #[x : x in W | x eq m];
         strings := {s cat IntegerToString (m): s in {"w", "x"}}; 
         I := [i : i in [1..#N] | N[i] in strings];
         B, sf := SetupBlocks (I, q, a, form);
         B := LargerMatGroup (d, q, B, I);
         gens := [];
         for i in [1..Ngens (B)] do 
            flag, vi := IsConjugate (P, u, phi (r^B.i));
            assert flag;
            h := vi @ tau;
            Append (~gens, h);
         end for;
         gens := [B.i * gens[i]^-1: i in [1..#gens]];
         assert forall{x : x in gens | Order ((x, r)) eq 1};
         Append (~Gens, gens);
      end if;
   end for;

   // I_2a(q) for Sp 
   u := phi (r);
   // first two cases of this section
   R := CaseOneAndTwo (T);
   // "Case b: list of m = ", R;
   for m in R do 
      a := #[x : x in W cat W_beta | x eq m];
      strings := {s cat IntegerToString (m): s in {"w", "x"}}; 
      I := [i : i in [1..#N] | N[i] in strings];
      B, sf := SetupBlocks (I, q, a, form);
      B := LargerMatGroup (d, q, B, I);
      gens := [];
      for i in [1..Ngens (B)] do 
         flag, vi := IsConjugate (P, u, phi (r^B.i));
         assert flag;
         h := vi @ tau;
         Append (~gens, h);
      end for;
      gens := [B.i * gens[i]^-1: i in [1..#gens]];
      Append (~Gens, gens);
   end for;

   // I_2a (q) for Sp  
   u := phi (r);
   // third case 
   R := CaseThree (T);
   // "Case c: list of m = ", R;
   for m in R do 
      a := #[x : x in W cat W_beta | x eq m];
      type :=  m in W_beta select "orthogonalminus" else "orthogonalplus";
      strings := {s cat IntegerToString (m): s in {"w", "x"}}; 
      I := [i : i in [1..#N] | N[i] in strings];
      B := OrthogonalBlocks (r, I, q, a, form, type);
      B := LargerMatGroup (d, q, B, I);
      gens := [];
      for i in [1..Ngens (B)] do 
         flag, vi := IsConjugate (P, u, phi (r^B.i));
         assert flag;
         h := vi @ tau;
         Append (~gens, h);
      end for;
      gens := [B.i * gens[i]^-1: i in [1..#gens]];
      Append (~Gens, gens);
   end for;

   // construct unipotent radical 
   // step 2 
   u := phi (r);
   for m in Set (V cat V_alpha) do 
      a := #[x : x in V cat V_alpha | x eq m];
      if a eq 2 then 
         // "Case d: m = ",m;
         strings := {s cat IntegerToString (2 * m): s in {"v"}}; 
         I := [i : i in [1..#N] | N[i] in strings];
         B := SetupGL2Subgroup (#I, q);
         B := LargerMatGroup (d, q, B, I);
         // "Now test conjugacy ...";
         gens := [];
         for i in [1..Ngens (B)] do 
            flag, vi := IsConjugate (P, u, phi (r^B.i));
            assert flag;
            h := vi @ tau;
            Append (~gens, h);
         end for;
         gens := [B.i * gens[i]^-1: i in [1..#gens]];
         Append (~Gens, gens);
      end if;
   end for;

   // unipotent radical 
   // step 3 
   L := Set (W); 
   u := phi (r);
   for m in L do 
      if IsOdd (m) then continue; end if;
      // "Case f: m = ", m; 
      a := #[x : x in W | x eq m];
      if a gt 0 then 
         b := #[x : x in V cat V_alpha | x eq m div 2];
         if b eq 2 then 
            strings := {s cat IntegerToString (m): s in {"v"}}
                  join {s cat IntegerToString (m): s in {"w", "x"}}; 
            I := [i : i in [1..#N] | N[i] in strings];
            B := AdditionalMatrices (2*a + 2, #I, q);
            B := LargerMatGroup (d, q, B, I);
            // "Next test conjugacy ...";
            gens := [];
            for i in [1..Ngens (B)] do 
               flag, vi := IsConjugate (P, u, phi (r^B.i));
               assert flag;
               h := vi @ tau;
               Append (~gens, h);
            end for;
            gens := [B.i * gens[i]^-1: i in [1..#gens]];
            Append (~Gens, gens);
         end if;
      end if;
   end for;

   // Z_2^t
   V_list := V cat V_alpha;
   V_list := Set (V_list);
   V_list := [x : x in V_list];
   Sort (~V_list);
   gens := [];
   for i in [1..#V_list] do 
      rank := V_list[i]; 
      I := FindIndices (N_full, "V", rank);
      for j in [1..#I] do 
         u1 := ExtractBlock (r, I[j], I[j]);
         MA := MatrixAlgebra (GF(q), d);
         g := Identity (MA);
         u := MyInsert (g, u1, I[j], I[j]);
         Append (~gens, u);
       end for;
   end for;
   gens := [GL(d, q) ! g : g in gens];
   Append (~Gens, gens);

   Gens := &cat Gens;
   assert forall{x : x in Gens | Order ((x, r)) eq 1};
   return Gens; 
end function;

// generating matrices for Q 
SpPair := function (d, q, i, j)
   F := GF (q);
   lambda := PrimitiveElement (F);
   e := Degree (F);
   MA := MatrixAlgebra (GF (q), d);
   L := [GL(d, F) | ];
   for f in [0..e - 1] do 
      A := Identity (MA);
      A[i,j] := lambda^f;
      Append (~L, A);
   end for;
   return L;
end function;

// generating matrices for Q 
SpQuad := function (d, q, i, j, k, l, p1, p2: second := false)
   F := GF (q);
   lambda := PrimitiveElement (F);
   e := Degree (F);
   MA := MatrixAlgebra (GF (q), d);
   L := [GL(d, F) | ];
   for f in [0..e - 1] do 
      A := Identity (MA);
      A[i,k] := lambda^f;
      x := (-1)^(p1 div 2);
      y := (-1)^(p2 div 2);
      if second then 
         sgn := x eq y select -1 else 1;
         assert sgn * x + y eq 0;
      else
         sgn := x eq y select 1 else -1;
         assert sgn * x - y eq 0;
      end if;
      A[j,l] := sgn * lambda^f;
      Append (~L, A);
   end for;
   return L;
end function;

// code to set up Q-group for even and odd characteristic Sp

Sp_QSubgroup := function (a, q, N) 

   weight := [a[i][1]: i in [1..#a]];
   odd := 0 in weight; 

   mult := [a[i][2] : i in [1..#a]];
   d := &+mult;

   full := [[weight[i]: j in [1..mult[i]]]: i  in [1..#weight]]; 
   full := &cat (full);

   w_list := [i : i in [1..#full] | Substring (N[i], 1, 1) eq "w"];
   x_list := [i : i in [1..#full] | Substring (N[i], 1, 1) eq "x"];
   v_list := [i : i in [1..#full] | Substring (N[i], 1, 1) eq "v"];

   // w_j, w_k
   Iww := [];
   for j in [1..d] do 
      wj := full[j];
      if j in w_list and wj lt 0 then 
         for k in [j + 1..d] do 
            wk := full[k];
            if k in w_list and wk lt Abs (wj) then Append (~Iww, <j, k>); end if;
          end for;
      end if;
   end for;

   // w_j, x_k
   Iwx := [];
   for j in [1..d] do 
      wj := full[j];
      if j in w_list and wj lt 0 then 
         for k in [j + 1..d] do 
            xk := full[k];
            if k in x_list and xk lt Abs (wj) then Append (~Iwx, <j, k>); end if;
          end for;
      end if;
   end for;

   // x_i, x_j 
   Ixx := [];
   for j in [1..d] do 
      xj := full[j];
      if j in x_list and xj lt 0 then 
         for k in [j + 1..d] do 
            xk := full[k];
            if k in x_list and xk lt Abs (xj) then Append (~Ixx, <j, k>); end if;
          end for;
      end if;
   end for;

   // x_i, w_j 
   Ixw := [];
   for j in [1..d] do 
      xj := full[j];
      if j in x_list and xj lt 0 then 
         for k in [1..d] do 
            wk := full[k];
            if k in w_list and wk lt Abs (xj) then Append (~Ixw, <j, k>); end if;
          end for;
      end if;
   end for;

   // v_i, v_j 
   Ivv := [];
   for j in [1..d] do 
      vj := full[j];
      if j in v_list and vj lt 0 then 
         for k in [j + 1..d] do 
            vk := full[k];
            if k in v_list and vk lt Abs (vj) then Append (~Ivv, <j, k>); end if;
          end for;
      end if;
   end for;

   // v_i, w_j 
   Ivw := [];
   for j in [1..d] do 
      vj := full[j];
      if j in v_list and vj lt 0 then 
         for k in [1..d] do 
            wk := full[k];
            if k in w_list and wk lt Abs (vj) then Append (~Ivw, <j, k>); end if;
          end for;
      end if;
   end for;

   // w_i, v_j 
   Iwv := [];
   for j in [1..d] do 
      wj := full[j];
      if j in w_list and wj lt 0 then 
         for k in [1..d] do 
            wk := full[k];
            if k in v_list and wk lt Abs (wj) then Append (~Iwv, <j, k>); end if;
          end for;
      end if;
   end for;

   // v_i, x_j 
   Ivx := [];
   for j in [1..d] do 
      vj := full[j];
      if j in v_list and vj lt 0 then 
         for k in [1..d] do 
            xk := full[k];
            if k in x_list and xk lt Abs (vj) then Append (~Ivx, <j, k>); end if;
          end for;
      end if;
   end for;

   // x_i, v_j 
   Ixv := [];
   for j in [1..d] do 
      xj := full[j];
      if j in x_list and xj lt 0 then 
         for k in [1..d] do 
            xk := full[k];
            if k in v_list and xk lt Abs (xj) then Append (~Ixv, <j, k>); end if;
          end for;
      end if;
   end for;

   // record opposites 
   J := []; K := [];
   for w in weight do
      A := [i: i in [1..#full] | full[i] eq w and N[i][1] eq "v"]; 
      B := [i: i in [1..#full] | full[i] eq -w and N[i][1] eq "v"]; 
      for i in [1..#A] do 
         a := A[i]; b := B[i];
         J[a] := b;
         J[b] := a;
      end for;

      A := [i: i in [1..#full] | full[i] eq w and N[i][1] eq "w"]; 
      B := [i: i in [1..#full] | full[i] eq -w and N[i][1] eq "w"]; 
      for i in [1..#A] do 
         a := A[i]; b := B[i];
         J[a] := b;
         J[b] := a;
      end for;

      A := [i: i in [1..#full] | full[i] eq w and N[i][1] eq "x"]; 
      B := [i: i in [1..#full] | full[i] eq -w and N[i][1] eq "x"]; 
      for i in [1..#A] do 
         a := A[i]; b := B[i];
         J[a] := b;
         J[b] := a;
      end for;
   end for;

   I := Ivv cat Iww cat Ixx cat Iwx cat Ixw cat Ivw cat Ivx cat Ixv cat Iwv; 
   II := [];
   for s in I do
      if not <s[2], s[1]> in II then Append (~II, s); end if;
   end for;
   I := II;
      
   L := [];
   for pair in I do 
      i := pair[1]; j := pair[2]; k := J[j]; ell := J[i];
      p1 := full[i]; p2 := full[j];
      if pair in Ivv then 
         Append (~L, SpQuad (d, q, i, j, k, ell, p1, p2: second := false));
      end if;
      if pair in Ivw then 
         Append (~L, SpQuad (d, q, i, j, k + 1, ell, p1, p2: second := false));
      end if;

      if pair in Iwv then 
         Append (~L, SpQuad (d, q, j, i, ell + 1, k, p1, p2: second := false));
      end if;

      if pair in Ivx then 
         Append (~L, SpQuad (d, q, i, j, k - 1, ell, p1, p2: second := true));
      end if;

      if pair in Ixv then 
         Append (~L, SpQuad (d, q, j, i, ell - 1, k, p1, p2: second := true));
      end if;

      if pair in Iww then 
         Append (~L, SpQuad (d, q, i, j, k + 1, ell + 1, p1, p2: second := false));
      end if;
      if pair in Ixx then 
         Append (~L, SpQuad (d, q, i, j, k - 1, ell - 1, p1, p2: second := false));
      end if;
      if pair in Iwx then 
         Append (~L, SpQuad (d, q, i, j, k - 1, ell + 1, p1, p2: second := true));
      end if;
      if pair in Ixw then 
         Append (~L, SpQuad (d, q, i, j, k + 1, ell - 1, p1, p2: second := true)); 
      end if; 
   end for;

   R := [];
   for i in [1..d] do 
      wt_vi := full[i];
      if i in v_list and wt_vi gt 0 then 
         j := J[i];
         Append (~R, SpPair (d, q, j, i));
      end if;
   end for;

   for i in [1..d] do 
      wt_wi := full[i];
      if i in w_list and wt_wi lt 0 then 
         j := J[i + 1];
         Append (~R, SpPair (d, q, i, j));
      end if;
   end for;

   for i in [1..d] do 
      wt_xi := full[i];
      if i in x_list and wt_xi lt 0 then 
         j := J[i - 1];
         Append (~R, SpPair (d, q, i, j));
      end if;
   end for;

   gens := &cat (L) cat &cat (R);
   Q := sub< GL(d, q) | gens>;
   return Q, L, R;
end function;

Sp_ClassRep_Even := function (rep, form, m, T, q) 
   for i in [1..#m] do
      if IsOdd (m[i][1]) and IsOdd (m[i][2]) then 
         error "Bad Jordan form description"; 
      end if;
   end for;

   // we need this full labelling for last case of semisimple generators
   _,_,_,_,_, N_full := GO_ClassRep_Even (rep, form, m, T, q);

   d := &+[m[i][1] * m[i][2] : i in [1..#m]];

   R := []; N := [];
   for i in [1..4] do
      if #T[i] gt 0 then 
         A := T[i]; 
         if i in {1, 3} then 
            for k in [1..#A] do 
               r := A[k];
               L := [-(r - 1) .. (r - 1) by 2];
               Append (~R, L cat L); 
               Append (~N, ["w" cat IntegerToString (r): i in [1..#L]] 
                       cat ["x" cat IntegerToString (r): i in [1..#L]]);
            end for;
         else
            for k in [1..#A] do 
               r := 2 * A[k];
               L := [-(r - 1) .. (r - 1) by 2];
               Append (~R, L); 
               Append (~N, ["v" cat IntegerToString (r): i in [1..#L]]);
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
   
   S := Sym (d);
   P := PermutationMatrix (GF(q), S!pos);
   N := [N[i]: i in pos];

   S := [<w, #[x : x in L | x eq w]>: w in W];
   return GL(d, q) ! (P * rep * Transpose (P)), P * form * Transpose (P), S, N, P, N_full;
end function;

// g is the precise matrix written down in paper as class rep 
// NOT simply a conjugate of that rep!

Sp_ConvertToSpecialRep_Even := function (g, form, T)
   d := Nrows (g);
   q := #BaseRing (g);

   J, CB, b := JordanForm (g);
   s := [b[i][2]: i in [1..#b]];
   m := [<x, #[y: y in s | y eq x]>: x in Set (s)];
   r, form, Wt, N, CB, N_full := Sp_ClassRep_Even (g, form, m, T, q);
   r := GL(d, q) ! r;
   CB := GL(d, q) ! CB;
   return r, form, CB, m, Wt, N, N_full;
end function;

// centraliser of unipotent element of Sp (d,q) for q even 
// assumption: G and g are written wrt form listed in unipotent paper 
// assumption: g is specific class rep -- not simply conjugate!
// T is parameter list for g  
// write down special rep r for g 
// return centraliser in Sp preserving associated form for r 
 
SpUnipotentCentraliserRep := function (G, g, T: 
   OrderOnly := false, Verify := false)

   flag, form := SymplecticForm (G);
   assert flag;
 
   q := #BaseRing (g);
   order := SpUnipotentCentraliserOrder_Even (T, q);
   if OrderOnly then return order, _, _; end if;

   d := Nrows (g);

   r, f, CB, m, W, N, N_labelled := Sp_ConvertToSpecialRep_Even (g, form, T);
   assert FixesForm (r, f);

   Q := Sp_QSubgroup (W, q, N);
   Q := UnipotentMatrixGroup (Q);
   P, phi, tau := PCPresentation (Q);

   CP := Centraliser (P, phi (r));
   C := CP @ tau;
   assert IsCentral (C, r);

   Add := Sp_SSGenerators_Even (r, f, m, T, N, P, phi, tau, N_labelled);

   C := sub<GL(d, q) | C, Add>;
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

WeightsToLabel := function (L)
   Z := Integers ();
   T := <[Z | ]: i in [1..4]>;
   index := [i : i in [1..#L] | L[i][1] eq "W" and L[i][3] eq 0];
   T[1] := Sort ([L[i][2]: i in index]); 
   index := [i : i in [1..#L] | L[i][1] eq "V" and L[i][3] eq 0];
   T[2] := Sort ([L[i][2]: i in index]); 
   index := [i : i in [1..#L] | L[i][1] eq "W" and L[i][3] ne 0];
   T[3] := Sort ([L[i][2]: i in index]); 
   index := [i : i in [1..#L] | L[i][1] eq "V" and L[i][3] ne 0];
   T[4] := Sort ([L[i][2]: i in index]); 
   Append (~T, 1);
   return T;
end function;

SpUnipotentCentraliser_Even := function (G, g, form)
   F := BaseRing (G); q := #F;
   assert IsEven (q);
   label := SpO_EvenLabel (g, form);
   T := WeightsToLabel (label);
   rep, form_rep := SetupRep ("Sp", q, T[1], T[2], T[3], T[4], T[5]);
   I := IsometryGroup (form_rep);
   C, r, f, CB := SpUnipotentCentraliserRep (I, rep, T);
   return C, r, f, CB;
end function;

freeze;

import "../../util.m": ChooseAlpha, FixesQuadraticForm, MyDiagonalJoin;
import "../../even-char.m": W_odd, V_beta_even, W_even, OForm;
import "../odd/blocks.m": ConstructVBlock, ConstructWBlock;
import "../odd/basics.m": RestrictToSpace;
import "test-blocks.m": ReduceToJ4, ReduceToW3, MatrixHasVBlock;
import "Omega-even-general.m": ClassSplitsInOmega_Even, OrthogonalEvenDecideConjugacy; 
 
// compute labels for elements of Sp and Orthogonal in characteristic 2

OneHomocyclicComponent := function (g, form)
   V := SymplecticSpace (form);
   A, CB, f := PrimaryRationalForm (g);
   mult := [f[i][2]: i in [1..#f]];
   max := Maximum (mult);
   I := [i: i in [1..#mult] | mult[i] eq max];
   J := [i : i in [1..#mult] | mult[i] lt max];
   offset := #J gt 0 select &+[mult[i]: i in J] else 0;
   U := sub<V | [CB[i] : i in [offset + 1..Dimension (V)]]>;
   return U, max;
end function;

SpOneStep := function (g, form, L)
   C, r := OneHomocyclicComponent (g, form);
   a, f := RestrictToSpace (g, form, C);

   if IsEven (r) then 
      // V block test? 
      k := r div 2;
      deduct := 0;
      if MatrixHasVBlock (a, f, k) ne 0 then 
         // V block 
         U, PU := ConstructVBlock (a, f, k);
         aa, fa := RestrictToSpace (a, f, U);
         if Nrows (aa) eq 2 then 
            val := 0; 
         else
            val := ReduceToJ4 (aa, fa, k);
         end if;
         Append (~L, <"V", k, val>);
         deduct := k * 2;
         if Dimension (U) gt 0 and Dimension (U) lt Dimension (C) then 
            D := OrthogonalComplement (PU, U);
            aa, ff := RestrictToSpace (a, f, D); 
            X, Y := $$ (aa, ff, L);
            return C, Y;
         end if;
      end if;
      nmrW := (Dimension (C) - deduct) div 2;
      if nmrW gt 0 then 
         tot := (Dimension (C) - deduct); 
         for m in [1..tot div (2*r)] do 
            Append (~L, <"W", r, 0>);
         end for;
      end if;
   else
      // W block 
      m := Nrows (a);
      U, PU := ConstructWBlock (a, f, r - 1);
      if r eq 1 then 
         val := 0;
      else 
         aa, ff := RestrictToSpace (a, f, U);
         val := ReduceToW3 (aa, ff, r div 2);
      end if;
      Append (~L, <"W", r, val>);
      if Dimension (U) gt 0 and Dimension (U) lt Dimension (C) then 
         D := OrthogonalComplement (PU, U);
         aa, ff := RestrictToSpace (a, f, D); 
         X, Y := $$ (aa, ff, L);
         return C, Y;
      end if;
   end if;
   return C, L;
end function;

// fairly "standard" description of element 
SpEvenApproximateLabel := function (g, form)
   L := [* *];
   a := g; f := form;
   repeat 
      V := SymplecticSpace (f);
      C, L := SpOneStep (a, f, L);
      assert C subset V;
      D := OrthogonalComplement (V, C);
      if Dimension (D) gt 0 then a, f := RestrictToSpace (a, f, D); end if;
   until Dimension (D) eq 0;

   label := [x : x in L];
   L := [];
   for k in [1..#label] do
      x := label[k];
      if x[1] eq "V" and x[2] eq 1 then x[3] := 0; end if;
      if x[1] eq "W" and x[2] eq 1 then x[3] := 0; end if;
      L[k] := x;
   end for;
   return L;
end function;

SignOfQuadraticForm := function (form, q)
   type := QuadraticFormType (form);
   if type eq "orthogonalplus" then return 0; else return ChooseAlpha (q); end if;
end function;
   
OrthogonalOneStep := function (g, form, QForm, L)
   C, r := OneHomocyclicComponent (g, form);
   a, fq := RestrictToSpace (g, QForm, C: Orthogonal := true);
   f := fq + Transpose (fq);

   F := BaseRing (g);
   q := #F;

   if IsEven (r) then 
      // V block test? 
      k := r div 2;
      deduct := 0;
      if MatrixHasVBlock (a, f, k) ne 0 then 
         // V block 
         U, PU := ConstructVBlock (a, f, k);
         aa, fqa := RestrictToSpace (a, fq, U: Orthogonal :=true);
         fa := fqa + Transpose (fqa); 
         assert FixesQuadraticForm (aa, fqa);
         if Nrows (aa) eq 2 then 
            val := SignOfQuadraticForm (fqa, q);
         else
            val := ReduceToJ4 (aa, fa, k);
         end if;
         Append (~L, <"V", k, F!val>);
         deduct := k * 2;
         if Dimension (U) gt 0 and Dimension (U) lt Dimension (C) then 
            D := OrthogonalComplement (PU, U);
            aa, fqa := RestrictToSpace (a, fq, D: Orthogonal :=true);
            ff := fqa + Transpose (fqa); 
            X, Y := $$ (aa, ff, fqa, L);
            return C, Y;
         end if;
      end if;
      nmrW := (Dimension (C) - deduct) div 2;
      if nmrW gt 0 then 
         tot := (Dimension (C) - deduct); 
         for m in [1..tot div (2*r)] do 
            Append (~L, <"W", r, F!0>);
         end for;
      end if;
   else
      // W block 
      m := Nrows (a);
      U, PU := ConstructWBlock (a, f, r - 1);
      // orthogonal case 
      aa, fqa := RestrictToSpace (a, fq, U: Orthogonal :=true);
      ff := fqa + Transpose (fqa);
      if r eq 1 then 
         val := SignOfQuadraticForm (fqa, q);
      else 
         val := ReduceToW3 (aa, ff, r div 2);
      end if;
      Append (~L, <"W", r, F!val>);
      if Dimension (U) gt 0 and Dimension (U) lt Dimension (C) then 
         D := OrthogonalComplement (PU, U);
         aa, fqa := RestrictToSpace (a, fq, D: Orthogonal :=true);
         ff := fqa + Transpose (fqa);
         X, Y := $$ (aa, ff, fqa, L);
         return C, Y;
      end if;
   end if;
   return C, L;
end function;

// fairly "standard" description of element 
OrthogonalEvenApproximateLabel := function (g, QF)
   form := QF + Transpose (QF);
   L := [* *];
   a := g; f := form; qf := QF;
   repeat 
      V := QuadraticSpace (qf);
      C, L := OrthogonalOneStep (a, f, qf, L);
      assert C subset V;
      D := OrthogonalComplement (V, C);
      if Dimension (D) gt 0 then 
         a, qf := RestrictToSpace (a, qf, D: Orthogonal := true); 
         f := qf + Transpose (qf);
       end if;
   until Dimension (D) eq 0;

   label := [x : x in L];
   return L;
end function;

R_beta_J := function (beta, x, n_x, q) 
   F := GF(q);
   if IsOdd (x) then 
      R := W_odd (x, q, beta); 
      label := [<"W", x, F!beta>];
      m := n_x div 2 - 1; 
      if m gt 0 then 
         B := W_odd (x, q, 0);
         R := DiagonalJoin (R, DiagonalJoin ([B: i in [1..m]]));
         label cat:= [<"W", x, 0>: i in [1..m]];
      end if;
   else
      R := V_beta_even (x div 2, q, beta); 
      label := [<"V", x div 2, F!beta>];
      m := n_x - 1;
      if m gt 0 then 
         c := m div 2;
         if c gt 0 then 
            C := DiagonalJoin ([W_even (x, q): i in [1..c]]);
            label cat:= [<"W", x, F!0>: i in [1..c]];
            if m mod 2 eq 1 then 
               C := DiagonalJoin (C, V_beta_even (x div 2, q, 0));
               label cat:= [<"V", x div 2, F!0>];
            end if;
         elif m mod 2 eq 1 then 
            C := V_beta_even (x div 2, q, 0);
            label cat:= [<"V", x div 2, F!0>];
         end if;
         R := DiagonalJoin (R, C);
      end if;
   end if;
   return R, label;
end function;

MyEquivalenceClasses := function (S, T)
   C := {};
   nmr := 0;
   for s in S do
      U := &join (C);
      if s in U then continue s; end if;
      class := {s};
      for r in S do
         if exists{r : x in S | Abs (r - s) eq 1 or (IsEven (r) and IsEven (s) and Abs (r - s) eq 2)} then
            Include (~class, r);
         end if;
      end for;
      for c in C do
         if c meet class ne {} then class join:= c; Exclude (~C, c); end if;
      end for;
      Include (~C, class);
   end for;

   U := &join (C);
   for t in T do 
      if t in U then continue t; end if;
      Include (~C, {t});
   end for;
   return C;
end function;

Rep_S0 := function (L, S0, alpha_S0, S, T, q)
   F := GF (q);
   t := Rep (S0);
   if #S0 eq 1 and t in T diff S then
      assert IsEven (t);
      n_t := #[x : x in L | x[2] eq t];
      assert IsEven (n_t);
      r := W_even (t, q);
      label := <"W", t, F!0>;
      R := DiagonalJoin ([r: i in [1..n_t div 2]]);
      label := [label : i in [1..n_t div 2]];
   elif #S0 eq 1 and IsOdd (t) then 
      n_t := #[x : x in L | x[2] eq t];
      R, label := R_beta_J (alpha_S0, t, n_t, q);
   else
      assert exists{t: t in S0 | IsEven (t)} and S0 subset S; 
      r0 := Minimum ({s: s in S0 | IsEven (s)});
      n_r0 := #[x : x in L | x[2] eq r0];
      A, labelA := R_beta_J (alpha_S0, r0, n_r0, q);
      B := [* *]; label := [];
      for s in S0 diff {r0} do 
         n_s := #[x : x in L | x[2] eq s];
         r, l := R_beta_J (0, s, n_s, q);
         Append (~B, r);
         label cat:= l;
      end for;
      B := MyDiagonalJoin (B);
      R := (Type (B) eq List and #B eq 0) select A else DiagonalJoin (A, B); 
      label := (Type (B) eq List and #B eq 0) select labelA else labelA cat label; 
   end if;
   return R, label;
end function; 

// standard label for element having approproximate label L 

SpO_EvenStandardLabel := function (L, q, alpha: Orthogonal := false)
   LL := [];
   for i in [1..#L] do
      x := L[i]; 
      if x[1] eq "V" then x[2] := 2 * x[2]; end if;
      Append (~LL, x); 
   end for;
   orig_L := LL;

   LL := [];
   for i in [1..#L] do
      x := L[i]; 
      if x[1] eq "V" then x[2] := 2 * x[2]; Append (~LL, x); end if;
      if x[1] eq "W" then Append (~LL, x);  Append (~LL, x); end if;
   end for;
   L := LL;

   T := {L[i][2] : i in [1..#L]};
   S := {x : x in T | IsOdd (x)}; 
   index := [i : i in [1..#L] | IsEven (L[i][2]) and L[i][1] eq "V"]; 
   S join:= {L[i][2] : i in index};
   C := MyEquivalenceClasses (S, T);

   blocks := <>; lblocks := [];
   for S0 in C do
      L0 := [x : x in orig_L | x[2] in S0];
      n_S0 := #[i : i in [1..#L0] | L0[i][2] in S0
                   and ((L0[i][1] eq "W" and L0[i][3] eq alpha)
                        or (L0[i][1] eq "V" and L0[i][3] eq alpha))];
      if Orthogonal then 
         alpha_S0 := IsEven (n_S0) select 0 else alpha;
      else 
         alpha_S0 := (IsEven (n_S0) or 2 in S0) select 0 else alpha;
      end if;
      block, lblock := Rep_S0 (L, S0, alpha_S0, S, T, q);
      Append (~blocks, block);
      Append (~lblocks, lblock);
   end for;

   return DiagonalJoin (blocks), &cat (lblocks), blocks, lblocks;
end function;

// label of blocks to construct to decide conjugacy 

SpO_EvenLabelToConstruct := function (L, alpha) 
   F := Parent (alpha);
   LL := [];
   for i in [1..#L] do
      x := L[i];
      if x[1] eq "V" then x[2] := 2 * x[2]; end if;
      Append (~LL, x);
   end for;
   L := LL;

   Dims := {L[i][2]: i in [1..#L] | IsEven (L[i][2])};
   New := [L[i]: i in [1..#L] | IsOdd (L[i][2])];
   
   for m in Dims do
      k := m div 2;
      A := [i : i in [1..#L] | L[i][1] eq "W" and L[i][2] eq 2 * k];
      B := [i : i in [1..#L] | L[i][1] eq "V" and L[i][2] eq 2 * k and L[i][3] eq alpha];
      C := [i : i in [1..#L] | L[i][1] eq "V" and L[i][2] eq 2 * k and L[i][3] eq 0];
      a := #A; b := #B; c := #C;
      assert b + c le 2;
      if b + c eq 0 then 
         New cat:= [<"W", 2*k, F!0>: i in [1..a]];
      else
         New cat:= [<"V", k, F!0>: i in [1..2*a + c]];
         New cat:= [<"V", k, alpha>: i in [1..b]];
      end if;
   end for;

   return New;
end function;

// write down rep for \sum W_(2k) in G 
W_vs_Wdash_SpecialRep := function (G, label)
   F := BaseRing (G); q := #F;
   rep := Generic (G) ! DiagonalJoin (<W_even (w, q): w in label>);
   rep_form := DiagonalJoin (<OForm ("O", w, q, 0: nmr := 1): w in label>);
   trA := TransformForm (G);
   trB := TransformForm (rep_form, "orth+");
   return rep^(trB * trA^-1);
end function;

// label for element of Sp, GO or Omega
// Construct final version used to decide conjugacy
SpO_EvenLabel := function (g, form: Orthogonal := false, Omega := false, 
   Construct := false)

   Orthogonal := Orthogonal or Omega;
   F := BaseRing (g);
   q := #F;
   assert IsEven (q);
   alpha := ChooseAlpha (q);
   if Orthogonal then 
      label := OrthogonalEvenApproximateLabel (g, form);
   else
      label := SpEvenApproximateLabel (g, form);
   end if;
   mat, L := SpO_EvenStandardLabel (label, q, alpha: Orthogonal := Orthogonal);
   if Construct then L := SpO_EvenLabelToConstruct (L, alpha); end if;
      
   Dims := [];
   for k in [1..#L] do
      x := L[k];
      size := x[1] eq "V" select 2 * x[2] else x[2];
      Dims[k] := size;
   end for;
   ParallelSort (~Dims, ~L);

   add := 1;
   if Omega and ClassSplitsInOmega_Even (label) then
      V := QuadraticSpace (form);
      G := IsometryGroup (V);
      rep := W_vs_Wdash_SpecialRep (G, [label[i][2] : i in [1..#label]]);
      flag, x := OrthogonalEvenDecideConjugacy (G, g, rep: InOmega := true);
      add := flag select 1 else -1;
   end if;
   return L, add;
end function;

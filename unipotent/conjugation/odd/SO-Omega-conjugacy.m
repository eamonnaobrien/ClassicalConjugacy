freeze;

// labels for elements of Omega and SO in odd characteristic 
// also decide conjugacy in these groups

import "../../good-char.m": A_beta_odd, A_beta_even, A_beta_odd_form, A_beta_even_form;
import "../../util.m": MyCommutatorSpace, FixesForm, FixesQuadraticForm, MySort, 
   MyDiagonalJoin, MySpinorNorm;
import "../../central/odd-orthogonal.m": GLOLabel_OrthogonalOdd;
import "Orthogonal-odd-general.m": OrthogonalDecideConjugacy;
import "../../odd-char.m": Original_Reflection, Original_s;
import "../centraliser.m": MyUnipotentCentraliser;

// class splits in Omega?
ClassSplitsInOmega_Odd := function (label, F)
   // case 1 
   sizes := {label[i][1]: i in [1..#label]};
   if forall{m : m in sizes | IsEven (m)} then return true, false; end if;

   TestSplit := function (label, F) 
      index := [i : i in [1..#label] | IsOdd (label[i][1])];
      m := Multiset ([label[i]: i in index]);
      if exists{x : x in m | Multiplicity (m, x) gt 1} then return false; end if;

      w := PrimitiveElement (F);
      Fstar, phi := MultiplicativeGroup (F);
      Squares := sub<Fstar | (w^2) @@ phi>;

      k := [label[i][1] div 2: i in index];
      beta := [label[i][2]: i in index];
      for j in [1..#beta] do
        split := (beta[j] * ((-1)^(k[1] + k[j]) * beta[1])^-1) @@ phi in Squares;
        if not split then return false; end if;
      end for;
      return true;
   end function;

   // case 2 
   if TestSplit (label, F) then return true, true; end if; 

   return false, false;
end function;

MyOmegaRep := function (G, form, str, T, q)
   type := "Omega";
   X := <A_beta_odd (T[i][1] div 2, q, -T[i][2], -2 * T[i][2], type) : i in [1..#T] | IsOdd (T[i][1])>; 
   X := DiagonalJoin (X);
   Y := (<A_beta_even (T[i][1], q, 0, type) : i in [1..#T] | IsEven (T[i][1])>); 
   if #Y gt 0 then Y := DiagonalJoin (Y); rep := DiagonalJoin (X, Y); else rep := X; end if;
   rep := Generic (G) ! rep;

   form_X := <A_beta_odd_form (T[i][1] div 2, q, 2 * T[i][2], type) : i in [1..#T] | IsOdd (T[i][1])>;
   form_X := DiagonalJoin (form_X);
   form_Y := (<A_beta_even_form (T[i][1], q, type): i in [1..#T] | IsEven (T[i][1]) >);
   if #form_Y gt 0 then form_Y := DiagonalJoin (form_Y); rep_form := DiagonalJoin (form_X, form_Y);
   else rep_form := form_X; end if;

   A := TransformForm (form, str: Restore := false); 
   B := TransformForm (rep_form, str: Restore := false); 
   tr := A * B^-1;

   odd := [i : i in [1..#T] | IsOdd(T[i][1])];
   even := [i : i in [1..#T] | IsEven(T[i][1])];
   T := [T[i]: i in odd] cat [T[i]: i in even];

   return rep, rep_form, tr, T;
end function;

MyMatrix := function (new_g, rep_form, blocks, m)
   offset := m gt 1 select &+[blocks[i]: i in [1..m - 1]] else 0;
   I := IsometryGroup (rep_form);
   F := BaseRing (new_g);
   MA := MatrixAlgebra (F, Nrows (new_g));
   c0 := Identity (MA);
   size := blocks[m];
   for i in [offset + 1..offset + size] do
      c0[i,i] := -1;
   end for;
   c0 := Generic (I) ! c0;
   assert Determinant (c0) eq F!-1;
   return c0;
end function;

Case1_FindConjugator := function (I, new_g, rep, rep_form, L)
   assert FixesForm (new_g, rep_form);
   reps := [rep^l : l in L];
   string := ["id", "s", "t", "ts"];

   flag, c := OrthogonalDecideConjugacy (I, new_g, rep);
   assert flag;

   for i in [1..#L] do 
      y := L[i];
      assert FixesQuadraticForm (c*y, SymmetricToQuadraticForm (rep_form)); 
      if MySpinorNorm (c * y, rep_form) eq 0 then
         assert new_g^(c*y) eq rep^y;
         pos := Position (reps, rep^y);
         return true, c * y, rep^y, string[pos];
      end if;
   end for;
   return false, _, _, _; 
end function;

// g is conjugate to one of these 4 reps
// Omega (d, q) q odd: g consists of even W blocks only 

OmegaLabelCase1 := function (G, g, h, form, label: LabelOnly := false) 
   F := BaseRing (G);
   flag, str, ff := OrthogonalForm (G);
   q := #F;
   d := Degree (G);
   type := "Omega";

   blocks := [x[1]: x in label];
   assert forall{x : x in blocks | IsEven (x)};
   rep := Generic (G) ! DiagonalJoin (<A_beta_even (k, q, 0, type): k in blocks>);
   rep_form := DiagonalJoin (<A_beta_even_form (k, q, type): k in blocks>);

   A := TransformForm (form, str: Restore := false); 
   B := TransformForm (rep_form, str: Restore := false); 
   tr := A * B^-1;

   I := IsometryGroup (rep_form);
   assert FixesForm (rep, rep_form);

   t := Original_Reflection (rep_form);
   s := Original_s (rep_form);
   L := [Identity (I), s, t, t * s]; 

   new_g := g^tr;
   found, cg, rep_g, str := Case1_FindConjugator (I, new_g, rep, rep_form, L);
   if LabelOnly then return <label, str>; end if;
   if not found then return false, _; end if;

   new_h := h^tr;
   found, ch, rep_h, str := Case1_FindConjugator (I, new_h, rep, rep_form, L);
   if not found then return false, _; end if;

   if rep_g ne rep_h then return false, _; end if;

   orig_cg := cg^(tr^-1);
   orig_ch := ch^(tr^-1);
   assert g^(orig_cg * orig_ch^-1) eq h;

   return true, orig_cg * orig_ch^-1;
end function;

IdentifyIndex := function (label, F)
   index := [i : i in [1..#label] | IsOdd (label[i][1])];
   w := PrimitiveElement (F);
   Fstar, phi := MultiplicativeGroup (F);
   Squares := sub<Fstar | (w^2) @@ phi>;

   first := [i: i in index | IsOdd (label[i][1])];
   assert #first gt 0;
   first := first[1];

   k := [label[i][1] div 2: i in index];
   beta := [label[i][2]: i in index];
   first := 1;
   for j in [2..#beta] do
      split := (beta[j] * ((-1)^(k[1] + k[j]) * beta[1])^-1) @@ phi in Squares;
      if not split then return first, index[j]; end if;
   end for;

   return false, _;
end function;

Case2_FindConjugator := function (I, new_g, rep, rep_form, c0, L) 
   assert FixesForm (new_g, rep_form);
   flag, c := OrthogonalDecideConjugacy (I, new_g, rep);
   string := ["id", "s"];
   reps := [rep^l: l in L];
   for i in [1..#L] do 
      y := L[i];
      for j in [0..1] do 
         assert FixesQuadraticForm (c*c0^j * y, SymmetricToQuadraticForm (rep_form)); 
         if MySpinorNorm (c * c0^j * y, rep_form) eq 0 then
            assert new_g^(c*c0^j * y) eq rep^y;
            pos := Position (reps, rep^y);
            return true, c * c0^j * y, rep^y, string[pos];
         end if;
      end for;
   end for;
   return false, _, _, _;
end function;

OmegaLabelCase2 := function (G, g, h, form, T : LabelOnly := false)
   F := BaseRing (G);
   flag, str, ff := OrthogonalForm (G);

   q := #F;
   d := Degree (G);

   rep, rep_form, tr, T := MyOmegaRep (G, form, str, T, q);
   I := IsometryGroup (rep_form);
   assert FixesForm (rep, rep_form);
   index := [i: i in [1..#T] | IsOdd (T[i][1])]; 
   assert #index gt 0;
   m := index[1];

   sizes := [T[i][1]: i in [1..#T]];
   c0 := MyMatrix (rep, rep_form, sizes, m);
   s := Original_s (rep_form);
   L := [Identity (I), s]; 

   new_g := g^tr;
   found, cg, rep_g, str := Case2_FindConjugator (I, new_g, rep, rep_form, c0, L);
   if LabelOnly then return <T, str>; end if;
   if not found then return false, _; end if;

   new_h := h^tr;
   found, ch, rep_h, str := Case2_FindConjugator (I, new_h, rep, rep_form, c0, L);
   if not found then return false, _; end if;

   if rep_g ne rep_h then return false, _; end if;

   orig_cg := cg^(tr^-1);
   orig_ch := ch^(tr^-1);
   assert g^(orig_cg * orig_ch^-1) eq h;

   return true, orig_cg * orig_ch^-1;
end function;

NonSplit_FindConjugator := function (I, new_g, rep, rep_form, L)
   assert FixesForm (new_g, rep_form);
   flag, c := OrthogonalDecideConjugacy (I, new_g, rep);
   assert flag;
   for i in [1..#L] do
      y := L[i];
      assert FixesForm (c*y, rep_form); 
      if MySpinorNorm (c * y, rep_form) eq 0 then
         assert new_g^(c*y) eq rep;
         return true, c * y;
      end if;
   end for;
   return false, _;
end function;

// modify c by element of Z so that product lies in Omega 
ModifyByCentre := function (Z, form, c, gens)
   flag := exists(z) {z : z in gens | MySpinorNorm (c * z, form) eq 0};
   assert flag;
   return c * z; 
end function;

OmegaNonSplitCase := function (G, g, h, form, T) 
   F := BaseRing (G);
   flag, str := OrthogonalForm (G);

   q := #F;
   d := Degree (G);
   rep, rep_form, tr, T := MyOmegaRep (G, form, str, T, q);

   I := IsometryGroup (rep_form);
   assert FixesForm (rep, rep_form);

   i, j := IdentifyIndex (T, F);

   if i cmpeq false then 
      new_g := g^tr;
      flag, cg := OrthogonalDecideConjugacy (I, new_g, rep);
      new_h := h^tr;
      flag, ch := OrthogonalDecideConjugacy (I, new_h, rep);
      if MySpinorNorm (cg * ch^-1, rep_form) ne 0 then 
         flag, Z := MyUnipotentCentraliser (I, rep);
         gens := {Z.i * Z.j^-1: i in [1..Ngens (Z)], j in [1..Ngens (Z)]};
         cg := ModifyByCentre (Z, rep_form, cg, gens);
         ch := ModifyByCentre (Z, rep_form, ch, gens);
         assert MySpinorNorm (cg * ch^-1, rep_form) eq 0;
      end if;
   else
      sizes := [T[i][1]: i in [1..#T]];
      a := MyMatrix (rep, rep_form, sizes, i);
      b := MyMatrix (rep, rep_form, sizes, j);

      L := [a^i * b^j : i in [0..1], j in [0..1]];

      new_g := g^tr;
      found, cg := NonSplit_FindConjugator (I, new_g, rep, rep_form, L);
      if not found then return false, _; end if;

      new_h := h^tr;
      found, ch := NonSplit_FindConjugator (I, new_h, rep, rep_form, L);
      if not found then return false, _; end if;
   end if;

   orig_cg := cg^(tr^-1);
   orig_ch := ch^(tr^-1);
   assert g^(orig_cg * orig_ch^-1) eq h;

   return true, orig_cg * orig_ch^-1;
end function;

OmegaDecideConjugacy := function (G, g, h) 
   flag, type, form := OrthogonalForm (G);
   if not flag then error "G is not orthgonal"; end if;
   label := GLOLabel_OrthogonalOdd (g, form);
   label_h := GLOLabel_OrthogonalOdd (h, form);
   if label ne label_h then return false, _; end if;

   F := BaseRing (G);
   split, case2 := ClassSplitsInOmega_Odd (label, F); 

   if not split then 
      // "Nonsplit case";
      f, c := OmegaNonSplitCase (G, g, h, form, label); 
      if f then return true, c; else return false, _;  end if;
   elif case2 then 
      f, c := OmegaLabelCase2 (G, g, h, form, label);
      if f then return true, c; else return false, _;  end if;
   else 
      f, c := OmegaLabelCase1 (G, g, h, form, label);
   end if;
   if f then return true, c; else return false, _;  end if;
end function;

GLOLabel_OmegaOdd := function (G, g, form) 
   label := GLOLabel_OrthogonalOdd (g, form);
   F := BaseRing (g);
   splits, case2 := ClassSplitsInOmega_Odd (label, F); 
   if splits eq false then 
      // class non-split?
      return <label, "ns">;
   elif case2 then 
      return OmegaLabelCase2 (G, g, g, form, label: LabelOnly := true);
   else 
      return OmegaLabelCase1 (G, g, g, form, label: LabelOnly := true);
   end if;
end function;

SO_FindConjugator := function (I, new_g, rep, rep_form, L)
   assert FixesForm (new_g, rep_form);
   reps := [rep^l : l in L];
   string := ["id", "t"];

   flag, c := OrthogonalDecideConjugacy (I, new_g, rep);
   assert flag;

   for i in [1..#L] do 
      y := L[i];
      assert FixesQuadraticForm (c*y, SymmetricToQuadraticForm (rep_form)); 
      if Determinant (c * y) eq 1 then
         assert new_g^(c*y) eq rep^y;
         pos := Position (reps, rep^y);
         return true, c * y, rep^y, string[pos];
      end if;
   end for;
   return false, _, _, _; 
end function;

// g is conjugate to one of 2 reps 
// SO (d, q) q odd: g consists of even W blocks only 

SOLabel := function (G, g, h, form, label : LabelOnly := false) 
   F := BaseRing (G);
   flag, str := OrthogonalForm (G);
   q := #F;
   d := Degree (G);
   type := "Omega";

   blocks := [x[1]: x in label];
   assert forall{x : x in blocks | IsEven (x)};
   rep := Generic (G) ! DiagonalJoin (<A_beta_even (k, q, 0, type): k in blocks>);
   rep_form := DiagonalJoin (<A_beta_even_form (k, q, type): k in blocks>);

   A := TransformForm (form, str: Restore := false); 
   B := TransformForm (rep_form, str: Restore := false); 
   tr := A * B^-1;

   I := IsometryGroup (rep_form);
   assert FixesForm (rep, rep_form);

   t := Original_Reflection (rep_form);
   L := [Identity (I), t]; 

   new_g := g^tr;
   found, cg, rep_g, str := SO_FindConjugator (I, new_g, rep, rep_form, L);
   if LabelOnly then return <label, str>; end if;
   if not found then return false, _; end if;

   new_h := h^tr;
   found, ch, rep_h, str := SO_FindConjugator (I, new_h, rep, rep_form, L);
   if not found then return false, _; end if;

   if rep_g ne rep_h then return false, _; end if;

   orig_cg := cg^(tr^-1);
   orig_ch := ch^(tr^-1);
   assert g^(orig_cg * orig_ch^-1) eq h;

   return true, orig_cg * orig_ch^-1;
end function;

SONonSplit_FindConjugator := function (I, new_g, rep, rep_form, L)
   assert FixesForm (new_g, rep_form);
   flag, c := OrthogonalDecideConjugacy (I, new_g, rep);
   assert flag;
   for i in [1..#L] do
      y := L[i];
      assert FixesForm (c*y, rep_form);
      if Determinant (c * y) eq 1 then 
         assert new_g^(c*y) eq rep;
         return true, c * y;
      end if;
   end for;
   return false, _;
end function;

SONonSplitCase := function (G, g, h, form, T) 
   F := BaseRing (G);
   flag, str := OrthogonalForm (G);

   q := #F;
   d := Degree (G);
   rep, rep_form, tr, T := MyOmegaRep (G, form, str, T, q);

   I := IsometryGroup (rep_form);
   assert FixesForm (rep, rep_form);

   assert exists(i){i: i in [1..#T] | IsOdd(T[i][1])};
   sizes := [T[i][1]: i in [1..#T]];
   a := MyMatrix (rep, rep_form, sizes, i);
   L := [a^i : i in [0..1]];
      
   new_g := g^tr;
   found, cg := SONonSplit_FindConjugator (I, new_g, rep, rep_form, L);
   if not found then return false, _; end if;

   new_h := h^tr;
   found, ch := SONonSplit_FindConjugator (I, new_h, rep, rep_form, L);
   if not found then return false, _; end if;

   orig_cg := cg^(tr^-1);
   orig_ch := ch^(tr^-1);
   assert g^(orig_cg * orig_ch^-1) eq h;

   return true, orig_cg * orig_ch^-1;
end function;

SODecideConjugacy := function (G, g, h) 
   flag, type, form := OrthogonalForm (G);
   if not flag then error "G is not orthgonal"; end if;
   label := GLOLabel_OrthogonalOdd (g, form);
   label_h := GLOLabel_OrthogonalOdd (h, form);
   if label ne label_h then return false, _; end if;

   F := BaseRing (G);
   sizes := {label[i][1]: i in [1..#label]};
   split := forall{m : m in sizes | IsEven (m)}; 

   if not split then 
      // "Nonsplit case";
      f, c := SONonSplitCase (G, g, h, form, label); 
   else 
      f, c := SOLabel (G, g, h, form, label);
   end if;
   if f then return true, c; else return false, _;  end if;
end function;

GLOLabel_SOOdd := function (G, g, form) 
   label := GLOLabel_OrthogonalOdd (g, form);
   F := BaseRing (g);
   sizes := {label[i][1]: i in [1..#label]};
   splits := forall{m : m in sizes | IsEven (m)}; 
   if splits eq false then 
      // class non-split?
      return <label, "ns">;
   else 
      return SOLabel (G, g, g, form, label: LabelOnly := true);
   end if;
end function;

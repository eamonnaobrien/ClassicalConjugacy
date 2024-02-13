freeze;

import "../../util.m": ChooseAlpha, FixesForm, MyDiagonalJoin, MySort;
import "../../central/odd-sp.m": SpParameters, Sp_ClassRep;
import "../../even-char.m": V_beta_even, W_even, W_odd;
import "../odd/blocks.m": ConstructVBlock, ConstructWBlock;
import "../odd/basics.m": RestrictToSpace;
import "../odd/Sp-odd-general.m": SpOddDecomposition;
import "Sp-O-V.m": SpO_VBeta_ConjugateElement;
import "Sp-W.m": Sp_W0_ConjugateElement;
import "Sp-W-beta.m": Sp_WBeta_ConjugateElement;
import "even-label.m": SpO_EvenLabel;
import "Omega-even-general.m": EvenSpaces, EvenConjugateBlocks;
import "test-blocks.m": MatrixHasVBlock, ReduceToJ4, ReduceToW3;

// decide conjugacy of two unipotent elements in Sp even characteristic

SpThisStep := function (g, form, index, Label, P, Space, spaces)
   V := SymplecticSpace (form);

   desc := Label[index];
   type := desc[1]; 
   size := desc[2];
   value := desc[3];

   dim := Nrows (g);

   a := g; f := form;
   // V block test? 
   if type eq "V" then 
      k := size;
      if MatrixHasVBlock (a, f, k) eq 0 then 
         // "Failure here";
         return false, _, _, _;
      end if;
      NmrTries := 0; Limit := 10^2;
      repeat 
         U := ConstructVBlock (a, f, k);
         aa, fa := RestrictToSpace (a, f, U);
         if Nrows (aa) eq 2 then 
            val := 0; 
         else
            val := ReduceToJ4 (aa, fa, k);
         end if;
         // "val is ", val, "need ", value;
          NmrTries +:= 1;
         flag := val eq value;
      until flag or NmrTries gt Limit;
      if not flag then error "Failure in SpThisStep"; end if; 
      Append (~spaces, U);
      Append (~Space, V);
      if Dimension (U) gt 0 and Dimension (U) lt dim then 
         D := OrthogonalComplement (V, U);
         Append (~P, D);
         aa, ff := RestrictToSpace (a, f, D); 
         flag, P, Space, spaces := $$ (aa, ff, index - 1, Label, P, Space, spaces);
         if not flag then return false, _, _, _; end if;
      end if;
      return true, P, Space, spaces;
   elif type eq "W" then 
      // W block 
      r := size;  
      repeat 
         U := ConstructWBlock (a, f, r - 1);
         if IsEven (r) or r eq 1 then 
            val := 0;
         else 
            aa, ff := RestrictToSpace (a, f, U);
            val := ReduceToW3 (aa, ff, r div 2);
         end if;
      until val eq value;
      Append (~spaces, U);
      Append (~Space, V);
      if Dimension (U) gt 0 and Dimension (U) lt dim then 
          D := OrthogonalComplement (V, U);
          Append (~P, D);
          aa, ff := RestrictToSpace (a, f, D); 
          flag, P, Space, spaces := $$ (aa, ff, index - 1, Label, P, Space, spaces);
          if not flag then return false, _, _, _; end if;
          return true, P, Space, spaces;
      end if;
   end if;
   return true, P, Space, spaces;
end function;

SpEvenChooseBasis := function (g, form, Label) 
   SG := EvenSpaces (g, form, Label);
   HG := [HyperbolicSplitting (x): x in SG];
   HG := [ a[1] : a in HG ];
   HG := [ &cat (a): a in HG ];
   HG := &cat HG;
   CA := Matrix (HG);
   assert FixesForm (CA, form);
   return CA;
end function;

SpEvenSetupSpecialRep := function (g, form) 
   F := BaseRing (g);
   q := #F;
   L := SpOddDecomposition (g, form, [* *]);
   R := [* *];
   Dim := [];
   for i in [1..#L] do 
      a := L[i][1]; fa := L[i][2];
      Beta := SpParameters (a, fa);
      dim := [Beta[i][1]: i in [1..#Beta]];
      beta := [Beta[i][2]: i in [1..#Beta]];
      J, CB, b := JordanForm (a);
      s := [b[i][2]: i in [1..#b]];
      m := [<x, #[y: y in s | y eq x]>: x in Set (s)];
      m := MySort (m);
      r, fr, cc, dd, ee := Sp_ClassRep (m, q, beta);
      assert FixesForm (r, fr);
      Append (~R, <r, fr>);
      Append (~Dim, dim);
   end for;
   new_rep := MyDiagonalJoin ([* R[i][1]: i in [1..#R] *]);
   new_form := MyDiagonalJoin ([* R[i][2]: i in [1..#R] *]);
   assert FixesForm (new_rep, new_form);
   return new_rep, new_form, &cat (Dim);
end function;

Sp_Even_Conjugacy_BaseCases := function (h, form, type)
   assert FixesForm (h, form);
   H := IsometryGroup (form);
   F := BaseRing (H);
   q := #F;
   d := Degree (H);
   new_form := StandardSymmetricForm (d, #F);
   tr := form ne new_form select TransformForm (H) else Identity (H);
   new_g := h^tr;

   n := d div 2;
   if type[1] eq "V" then
      beta := type[3];
      r := V_beta_even (n, q, beta); 
      flag, C := SpO_VBeta_ConjugateElement (new_g, r, new_form);
   elif type[1] eq "W" and type[3] eq 0 then
      r := W_even (n, q); 
      flag, C := Sp_W0_ConjugateElement (new_g, r, new_form);
   elif type[1] eq "W" and type[3] ne 0 then
      beta := type[3];
      r := W_odd (n, q, beta); 
      flag, C := Sp_WBeta_ConjugateElement (new_g, r, new_form);
      // flag, C := Sp_WBeta_ConjugationMatrix (r, new_form, new_g);
   end if;
   if not flag then return false, _; end if;
   C := C^(tr^-1);
   assert FixesForm (C, form);
   return true, C;
end function;

JMatrix := function (d, q)
   MA := MatrixAlgebra (GF(q), 2);
   J := MA![0,1,1,0];
   return DiagonalJoin ([J: i in [1..d div 2]]);
end function;

// decide conjugacy of two unipotent elements g and h in Sp even characteristic

SpEvenDecideConjugacy := function (G, g, h: Verify := false)
   flag, form := SymplecticForm (G);
   if not flag then error "G is not symplectic";  end if;

   F := BaseRing (G);
   q := #F;

   orig_form := form;
   orig_g := g;
   orig_h := h;

   label := SpO_EvenLabel (g, form: Construct := true);
   Dims := [label[i][2]: i in [#label..1 by -1]];
   new_form := DiagonalJoin (<JMatrix (2 * x, q): x in Dims>);
   
   A := TransformForm (form, "symplectic");
   B := TransformForm (new_form, "symplectic");
   C := Generic (G) ! (A * B^-1)^-1;

   g := g^(C^-1);
   h := h^(C^-1);
   assert FixesForm (g, new_form);
   assert FixesForm (h, new_form);

   CA := SpEvenChooseBasis (g, new_form, label);
   new_g := CA * g * CA^-1;

   CB := SpEvenChooseBasis (h, new_form, label);
   new_h := CB * h * CB^-1;

   flag, X := EvenConjugateBlocks (new_g, new_h, new_form, 
                                 [2 * x: x in Dims], Reverse (label));
   if not flag then return false, _; end if;
   assert X^-1 * new_g * X eq new_h;
   assert CB^-1 * X^-1 * CA * g * CA^-1 * X * CB eq h;
   x := Generic (G) ! (CB^-1 * X^-1 * CA);
   assert x * g * x^-1 eq h;
   assert FixesForm (x, new_form);

   conj := x^C;

   if Verify then 
      assert orig_g^(conj^-1) eq orig_h;
      assert FixesForm (orig_g, orig_form);
      assert FixesForm (conj, orig_form);
      assert FixesForm (orig_h, orig_form);
   end if;
   return true, conj^-1;
end function;

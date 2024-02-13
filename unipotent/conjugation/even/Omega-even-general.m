freeze;

import "../odd/blocks.m": ConstructVBlock, ConstructWBlock;
import "../odd/basics.m": RestrictToSpace, PullbackToParent, SpecialQuadBasis;
import "../../util.m": ChooseAlpha, FixesQuadraticForm; 
import "../../even-char.m": V_beta_even, W_even, W_odd, OForm;
import "../centraliser.m": MyUnipotentCentraliser;

import "even-label.m": SignOfQuadraticForm, SpO_EvenLabel;
import "test-blocks.m": MatrixHasVBlock, ReduceToJ4, ReduceToW3;
import "Sp-O-V.m": SpO_VBeta_ConjugateElement;
import "Omega-W-beta.m": GO_WBeta_ConjugationMatrix;
import "Sp-even-general.m": Sp_Even_Conjugacy_BaseCases, SpThisStep;

// decide conjugacy of two unipotent elements in GO / Omega even characteristic 

OrthogonalThisStep := function (g, form, index, Label, P, Space, spaces: Orthogonal := true)
   V := QuadraticSpace (form);
   bilinear_form := form + Transpose (form);

   desc := Label[index];
   type := desc[1]; 
   size := desc[2];
   value := desc[3];

   dim := Nrows (g);
   F := BaseRing (g);
   q := #F;

   a := g; f := form;
   // V block test? 
   if type eq "V" then 
      k := size;
      repeat 
         if MatrixHasVBlock (a, bilinear_form, k) eq 0 then
            // "Failure here";
            return false, _, _, _;
         end if;
         U := ConstructVBlock (a, bilinear_form, k);
         aa, fa := RestrictToSpace (a, f, U: Orthogonal := true);
         if Nrows (aa) eq 2 then 
             val := SignOfQuadraticForm (fa, q);
         else
            val := ReduceToJ4 (aa, fa + Transpose (fa), k);
         end if;
      until val eq value;
      Append (~spaces, U);
      Append (~Space, V);
      if Dimension (U) gt 0 and Dimension (U) lt dim then 
         D := OrthogonalComplement (V, U);
         Append (~P, D);
         aa, ff := RestrictToSpace (a, f, D: Orthogonal := true); 
         flag, P, Space, spaces := $$ (aa, ff, index - 1, Label, P, Space, spaces);
         if not flag then return false, _, _, _; end if;
      end if;
      return true, P, Space, spaces;
   elif type eq "W" then 
      // W block 
      r := size;  
      repeat 
         U := ConstructWBlock (a, bilinear_form, r - 1);
         aa, ff := RestrictToSpace (a, f, U: Orthogonal := true);
         if IsEven (r) then  
            val := 0;
         elif r eq 1 then 
             val := SignOfQuadraticForm (ff, q);
         else 
            val := ReduceToW3 (aa, ff + Transpose (ff), r div 2);
         end if;
      until val eq value;
      Append (~spaces, U);
      Append (~Space, V);
      if Dimension (U) gt 0 and Dimension (U) lt dim then 
          D := OrthogonalComplement (V, U);
          Append (~P, D);
          aa, ff := RestrictToSpace (a, f, D: Orthogonal := true); 
          flag, P, Space, spaces := $$ (aa, ff, index - 1, Label, P, Space, spaces);
          if not flag then return false, _, _, _; end if;
          return true, P, Space, spaces;
      end if;
   end if;
   return true, P, Space, spaces;
end function;

// write space determined by form as direct sum of subspaces, 
// each determined by element of Label 
EvenSpaces := function (g, form, Labels: Orthogonal := false)
   L := [];
   a := g; f := form;
   if Orthogonal then 
      V := QuadraticSpace (form);
   else 
      V := SymplecticSpace (form);
   end if;

   index := #Labels;
   fct := Orthogonal select OrthogonalThisStep else SpThisStep;
   NmrTries := 0; Limit := 10^2;
   repeat 
      spaces := [* *];
      P := [V];
      Space := [];
      flag, P, Space, spaces := fct (a, f, index, Labels, P, Space, spaces);
      NmrTries +:= 1;
   until flag or NmrTries gt Limit;
   if NmrTries gt Limit then error "Failure in EvenSpaces"; end if;

   S := [* spaces[1] *];
   for i in [2..#P] do 
      X := spaces[i];
      for j in [i..2 by -1] do  
         X := PullbackToParent (Space[j-1], P[j], X);
      end for;
      Append (~S, X);
   end for;
   
   S := [x : x in S];
   S := [sub< V | Basis (x)>: x in S];
   return S;
end function;

Omega_V2k := function (V, U, form, alpha)
   H := HyperbolicSplitting (U);
   B := H[1];
   if alpha eq 0 then
      assert #H[2] eq 0;
      pair := B[#B];
      vm1 := pair[1];
      v1 := pair[2];
      v1 := v1 + vm1;
      last := [vm1, v1];
      B := Prune (B) cat [last];
      first := [B[i][1]: i in [1..#B]]; 
      third := Reverse ([B[i][2]: i in [1..#B]]); 
      CB := first cat third;
   else 
      assert #H[2] gt 0;
      C := H[2];
      C := sub<V | C>;
      C := SpecialQuadBasis (C, form, alpha, 1);
      first := [B[i][1]: i in [1..#B]]; 
      second := C;
      third := Reverse ([B[i][2]: i in [1..#B]]); 
      CB := first cat second cat third;
   end if;
   CB := Matrix (CB);
   return CB;
end function;

Omega_W2kp1 := function (V, U, form, alpha)
   H := HyperbolicSplitting (U);
   B := H[1];
   if alpha eq 0 then
      assert #H[2] eq 0;
      first := [B[i][1]: i in [1..#B]]; 
      third := Reverse ([B[i][2]: i in [1..#B]]); 
   else 
      assert #H[2] gt 0;
      assert IsEven (#B);

      C := H[2];
      C := sub<V | C>;
      C := SpecialQuadBasis (C, form, alpha, alpha);

      k := #B div 2;
      if k gt 0 then 
         pair := B[k];
         wm2 := pair[1];
         x2 := pair[2];
         wm2 := wm2 + alpha * x2;
         last := [wm2, x2];
         B := [B[i]: i in [1..k - 1]] cat [last] cat [C] cat 
              [B[i]: i in [k + 1..#B]]; 
      else 
         B := [C];
      end if;

      first := [B[i][1]: i in [1..#B]]; 
      third := Reverse ([B[i][2]: i in [1..#B]]); 
    end if;
    CB := first cat third;
    CB := Matrix (CB);
    return CB;
end function;

GOEvenChooseBasis := function (g, form, L)
   V := QuadraticSpace (form);
   Sg := EvenSpaces (g, form, L: Orthogonal := true);
   L := Reverse (L);
   M := <>;
   for i in [1..#Sg] do
      label := L[i];
      type := label[1]; 
      alpha := label[3];
      if type eq "V" then 
         CB := Omega_V2k (V, Sg[i], form, alpha);
      else 
         CB := Omega_W2kp1 (V, Sg[i], form, alpha);
      end if;
      Append (~M, CB);
    end for;
    M := Generic (Parent (g)) ! VerticalJoin (M);
    assert IsIsometry (V, M);
    return M;
end function;

GO_Even_Conjugacy_BaseCases := function (h, form, type) 
   assert FixesQuadraticForm (h, form);
   V := QuadraticSpace (form);
   H := IsometryGroup (V);
   F := BaseRing (H);
   q := #F;
   d := Degree (H);

   g := h;
   n := d div 2;
   if type[1] eq "V" then 
      alpha := type[3];
      r := V_beta_even (n, q, alpha); 
      k := d div 2;
      form := OForm ("O", k, q, alpha);
      flag, C := SpO_VBeta_ConjugateElement (g, r, form: Orthogonal := true);
   elif type[1] eq "W" and type[3] eq 0 then 
      rep := W_even (n, q); 
      form := OForm ("O", n, q, 0: nmr := 1);
      flag, C := GO_WBeta_ConjugationMatrix (H, rep, form, g, 0);
   elif type[1] eq "W" and type[3] ne 0 then 
      alpha := type[3];
      n := type[2];
      rep := W_odd (n, q, alpha);
      form := OForm ("Omega", n, q, alpha: nmr := 1);
      flag, C := GO_WBeta_ConjugationMatrix (H, rep, form, g, alpha);
   end if;
   if not flag then return false, _; end if;

   return true, C;
end function;

EvenConjugateBlock := function (block_g, block_h, form, type : Orthogonal := false)

   fct := Orthogonal select GO_Even_Conjugacy_BaseCases else
                            Sp_Even_Conjugacy_BaseCases; 
   flag, C1 := fct (block_g, form, type);
   if not flag then return false, _; end if;
   flag, C2 := fct (block_h, form, type);
   if not flag then return false, _; end if;
   return true, C1^-1 * C2;
end function;

EvenConjugateBlocks := function (g, h, form, blocks, types: Dim := 2,
                                 Orthogonal := false) 
   F := BaseRing (g);
   Conj := <>;
   for i in [1..#blocks] do
      offset := i eq 1 select 0 else &+[blocks[j]: j in [1..i - 1]]; 
      r := blocks[i];
      J := ExtractBlock (form, offset + 1, offset + 1, r, r);
      block_g := GL(r, F) ! ExtractBlock (g, offset + 1, offset + 1, r, r);
      block_h := GL(r, F) ! ExtractBlock (h, offset + 1, offset + 1, r, r);
      if Nrows (J) gt Dim then 
         flag, one := EvenConjugateBlock (block_g, block_h, J, types[i]:
                           Orthogonal := Orthogonal); 
      else 
         V := Orthogonal select QuadraticSpace (J) else SymplecticSpace (J);
         I := IsometryGroup (V);
         RandomSchreier (I);
         flag, one := IsConjugate (I, block_g, block_h);
      end if;
      if not flag then return false, _; end if;
      assert flag;
      Append (~Conj, one);
   end for;

   d := &+blocks;
   return true, GL(d, F) ! DiagonalJoin (Conj);
end function;

QuadFormMatrix := function (label)
   type := label[1];
   k := label[2];
   alpha := label[3];
   F := Parent (alpha);
   assert IsFinite (F);
   q := #F;
   if type eq "V" then
      form := OForm ("O", k, q, alpha);
   elif type eq "W" then 
      if IsEven (k) then 
         form := OForm ("O", k, q, 0: nmr := 1);
      else 
         form := OForm ("Omega", k, q, alpha: nmr := 1);
      end if;
   end if;
   return form;
end function;

// class splits in Omega?
ClassSplitsInOmega_Even := function (label)
   types := {label[i][1]: i in [1..#label]};
   if types ne {"W"} then return false; end if;
   sizes := {label[i][2]: i in [1..#label]};
   return forall{m : m in sizes | IsEven (m)};
end function;

// rep has V_2k block: identity matrix with this block in appropriate location 
ConstructMat := function (rep, label)
   label := Reverse (label);
   offset := 0;
   for j in [1..#label] do
     l := label[j];
     if l[1] eq "V" then
        m := l[2] * 2;
        break j;
     else
        offset +:= l[2] * 2;
     end if;
   end for;
   d := Nrows (rep);
   F := BaseRing (rep);
   MA := MatrixAlgebra (F, d);
   rep := MA!rep;
   block := ExtractBlock (rep, offset + 1, offset + 1, m, m);
   mat := rep^0;
   mat := GL(d, F) ! InsertBlock (mat, block, offset + 1, offset + 1);
   return mat;
end function;

// decide conjugacy of two unipotent elements g and h in GO / Omega even characteristic 

OrthogonalEvenDecideConjugacy := function (G, g, h: InOmega := false, Verify := false)
   flag, form, type := QuadraticForm (G);
   if not flag then error "G is not orthogonal group"; end if;

   label := SpO_EvenLabel (g, form: Construct := true, Orthogonal := true);

   new_form := DiagonalJoin (<QuadFormMatrix (l): l in Reverse (label)>);
   
   string := type eq "orthogonalplus" select "orth+" else "orth-";
   A := TransformForm (form, string);
   B := TransformForm (new_form, string);
   C := Generic (G) ! (A * B^-1)^-1;

   orig_g := g;
   orig_h := h;
   g := g^(C^-1);
   h := h^(C^-1);
   
   CA := GOEvenChooseBasis (g, new_form, label);
   new_g := CA * g * CA^-1;

   CB := GOEvenChooseBasis (h, new_form, label);
   new_h := CB * h * CB^-1;

   Dims := [2 * label[i][2]: i in [1..#label]];

   flag, X := EvenConjugateBlocks (new_g, new_h, new_form, Reverse (Dims), 
              Reverse (label): Orthogonal := true);

   if not flag then return false, _; end if;
   conj := Generic (G) ! (C^-1 * CB^-1 * X^-1 * CA * C);

   conj := conj^-1;
   if Verify then assert orig_g^conj eq orig_h; end if;

   if InOmega then
      V := QuadraticSpace (form);
      if ClassSplitsInOmega_Even (label) then 
         flag := DicksonInvariant (V, conj) eq 0;
      elif DicksonInvariant (V, conj) eq 1 then
         if exists{x: x in label | x[1] eq "V"} then 
            s := ConstructMat (new_h, label);
            s := C^-1 * CB^-1 * s * CB * C;   
         else
            I := IsometryGroup (V);
            f, Cr := MyUnipotentCentraliser (I, orig_h);
            assert exists(s) {s : s in Generators (Cr) | DicksonInvariant (V, s) eq 1};
         end if;
         conj := conj * s;
         assert DicksonInvariant (V, conj) eq 0;
         flag := orig_g^(conj) eq orig_h;
      end if;
   end if;
   if not flag then return false, _; else return true, conj; end if;
end function;

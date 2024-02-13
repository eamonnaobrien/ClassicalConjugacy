freeze;

import "util.m": NonSquare, MySpinorNorm;
import "good-char.m": A_beta_even, A_beta_even_form, A_beta_odd, 
    A_beta_odd_form, BackTrack;
import "Sp-Orthogonal-order.m": OrthogonalUnipotentCentraliserOrder;

OrthogonalUnipotentClassSize_Odd := function (G, type, T, VBeta, split, q)
   return #G div OrthogonalUnipotentCentraliserOrder (type, T, VBeta, split, q);
end function;

TestSplit := function (Data, K, q, S, phi)
   Split := [];
   K := [(x - 1) div 2: x in K];
   for i in [1..#Data] do 
      Beta := Data[i];
      split := false;
      for j in [1..#Beta] do 
          split := (Beta[j] * ((-1)^(K[1] + K[j]) * Beta[1])^-1) @@ phi in S; 
          if not split then break j; end if;
      end for;
      Split[i] := split;
   end for;
   return Split;
end function;

// reflection for Magma form 
MyReflection := function (n, q)
   MA := MatrixAlgebra (GF (q), n);
   r := Zero (MA);
   r[1][n] := -1;
   r[n][1] := -1;
   for i in [2 .. n - 1] do r[i][i] := 1; end for;
   return GL(n, q)!r;
end function;

// reflection in group preserving supplied orthogonal form 
Original_Reflection := function (form)
   Q := SymmetricToQuadraticForm (form);
   V := QuadraticSpace (Q);
   H := IsometryGroup (V);
   assert exists(j){j : j in [1..Ngens (H)] | IsReflection (H.j)};
   return H.j;
end function;

// element in SO but not in Omega 
Original_s := function (form) 
   Q := SymmetricToQuadraticForm (form);
   V := QuadraticSpace (Q);
   H := IsometryGroup (V);
   assert exists(i){i : i in [1..Ngens (H)] | MySpinorNorm (H.i, form) eq 1};
   return H.i;
end function;

// given type, rank and odd field size, write down unipotent class reps
// as elements of corresponding orthogonal group;
// default for: n odd G = SO(n, q) and n even G = GO(n, q)
// Special: reps in SOPlus(n, q), SOMinus(n, q)
// Perfect: reps in Omega(n, q)

OrthogonalUnipotentReps := function (n, q, epsilon: Special := false, 
   Perfect := false, Rewrite := true) 

   F := GF(q);

   // case n=1 dealt manually
   if n eq 1 then
      G := GL(1, q);
      return [<1, 1, Identity(G)>], [<1, 1, Identity (G)>], [MatrixAlgebra (F, 1)![1]], [{* 1^^1 *}],
             [<[<1, 1>], "id">];
   end if;

   // "Applies to odd characteristic only";
   assert IsOdd (q);
   k := n div 2;
   F := GF (q);
   w := PrimitiveElement (F);
   Fstar, phi := MultiplicativeGroup (F);
   Squares := sub<Fstar | (w^2) @@ phi>;
   // assert {x  @ phi : x in Squares} eq {x^2: x in F | x ne 0};

   if Perfect eq true then Special := true; end if;
   P := Partitions (n);
   S := [Multiset (p): p in P];
   T := [];
   for s in S do
      t := {x: x in s};
      if exists{x : x in t | IsEven (x) and IsOdd (Multiplicity (s, x))} then
         continue;
      end if;
      Append (~T, s);
   end for;
   S := T;

   type := "Omega";

   total := 0;
   omega := {};
   alpha := NonSquare (F);
   Reps := []; Forms := [MatrixAlgebra (F, n) | ];
   Shapes := [];
   special := [];
   Params := [];

   for i in [1..#S] do
      s := S[i];
      T := Set (s);
      T := [x : x in T];
      Sort (~T);
      M := MatrixAlgebra (F, 0);
      A := Zero (M);
      form_A := Zero (M);
      B := Zero (M);
      form_B := Zero (M);

      B_val := [];
      for t in T do 
         m := Multiplicity (s, t);
         if IsEven (t) then 
            k := t div 2;
            one := Zero (M);
            one := A_beta_even (2 * k, q, 0, type);
            one := DiagonalJoin ([one: i in [1..m div 2]]);
            A := DiagonalJoin (A, one);
            B_val cat:= [<2 * k, 0>: i in [1..(m div 2)]];
            one := A_beta_even_form (2 * k, q, type);
            one := DiagonalJoin ([one: i in [1..m div 2]]);
            form_A := DiagonalJoin (form_A, one);
         else
            k := (t - 1) div 2; 
            two := Zero (M);
            if m gt 1 then 
                temp := A_beta_odd (k, q, F!-1, F!-2, type);
                temp := DiagonalJoin ([temp: i in [1..m - 1]]);
                two := DiagonalJoin (two, temp);
            end if;
            B := DiagonalJoin (B, two); 
            B_val cat:= [<t, 1>: i in [1..(m - 1)]];
            if m gt 1 then 
               two := A_beta_odd_form (k, q, 2, type);
               two := DiagonalJoin ([two: i in [1..m - 1]]);
            end if;
            form_B := DiagonalJoin (form_B, two); 
         end if;
      end for;

      odd := [x : x in T | IsOdd (x)];
      r := #odd;
      params := [];
      if r eq 0 then total +:= 1; else total +:= 2^(r - 1); end if;
      if #odd gt 0 then 
         L := exists{t: t in T | IsOdd (t)} select [1, alpha] else [1];
         list := BackTrack ([#L: i in [1..#odd]]);
         X := [* [A_beta_odd (t div 2, q, -beta, -2 * beta, type) : beta in L]: t in T | IsOdd (t) *]; 
         params := [[<t, beta>: beta in L]: t in T | IsOdd (t)];
         Y := [* [A_beta_odd_form (t div 2, q, 2 * beta, type) : beta in L]: t in T | IsOdd (t) *]; 
         C := [DiagonalJoin (<X[i][l[i]]: i in [1..#X]>): l in list];
         params := [[params[i][l[i]]: i in [1..#X]]: l in list];
         Split := TestSplit ([L[i]: i in list], odd, q, Squares, phi);
         C_form := [DiagonalJoin (<Y[i][l[i]]: i in [1..#X]>): l in list];
         C := [DiagonalJoin (<c, A>): c in C];
         C_form := [DiagonalJoin (<c, form_A>): c in C_form];
         C := [DiagonalJoin (<c, B>): c in C];
         params := [params[i] cat B_val: i in [1..#params]];
         C_form := [DiagonalJoin (<c, form_B>): c in C_form];
      else 
         C := [DiagonalJoin (<A, B>)];
         params cat:= [B_val];
         C_form := [DiagonalJoin (<form_A, form_B>)];
         if epsilon eq 1 and Special eq true then
            Include (~special, #Reps + 1);
         end if;
      end if;

      if epsilon in {1, -1} then
         k := n div 2;
         value := epsilon eq 1 select true else false;
         index := [i: i in [1..#C] | IsSquare ((-1)^k * Determinant (C_form[i])) eq value];
      else
         index := [i: i in [1..#C] | IsSquare (Determinant (C_form[i]))];
         assert #C div 2 eq #index;
      end if;
      params := [params[i]: i in index];
      Append (~Params, params);

      // classes split in Omega? 
      m := {Multiplicity (s, t): t in odd};
      if Perfect then 
         split := [];
         if m eq {} then
            split := {i: i in [#Reps + 1..#Reps + #index]}; 
            omega join:= split;
         elif m eq {1} then 
            split := [i: i in [1..#index] | Split[index[i]] eq true];
            omega join:= {#Reps + i: i in split};
         end if;
      end if;
      reps := [GL(n, F) ! C[i]: i in index];
      forms := [GL(n, F) ! C_form[i] : i in index];
      shape := [s : k in [1..#index]];
      Reps cat:= reps;
      Forms cat:= forms;
      Shapes cat:= shape;
   end for;

   Params := &cat Params;

   if epsilon eq 0 then 
      form_type := "orthogonal";
   else 
      form_type := epsilon eq 1 select "orthogonalplus" else "orthogonalminus";
   end if;

   reps := []; 
   original := []; forms := []; shapes := [];
   Split := [];
   VBeta := [];
   L := [];
   for i in [1..#Reps] do
      Append (~original, Reps[i]);
      SP := [<Params[i], "id">];
      Append (~forms, Forms[i]);
      Append (~shapes, Shapes[i]);
      Append (~VBeta, Params[i]);
      assert #original eq #VBeta;
      if Rewrite then 
         tr := TransformForm (Forms[i], form_type: Restore := false);
      end if;
      if epsilon eq 1 and #special gt 0 then 
         orig_t := Original_Reflection (Forms[i]); 
         if Rewrite then t := orig_t^tr; end if;
      end if;
      if Perfect then 
         orig_s := Original_s (Forms[i]);
         if Rewrite then s := orig_s^tr; end if;
      end if;
      if Rewrite then
         rep := Reps[i]^tr;
         Append (~reps, rep);
      end if;
      if Perfect and i in omega then 
         Append (~forms, Forms[i]);
         Append (~shapes, Shapes[i]);
         if Rewrite then Append (~reps, rep^s); end if;
         Append (~original, Reps[i]^orig_s);
         Append (~SP, <Params[i], "s">);
         Append (~VBeta, Params[i]);
         assert #original eq #VBeta;
         Append (~Split, #shapes - 1);
         Append (~Split, #shapes);
      end if;
      if epsilon eq 1 and (Special and i in special) then 
         Append (~forms, Forms[i]);
         Append (~shapes, Shapes[i]);
         if Rewrite then Append (~reps, rep^t); end if;
         Append (~original, Reps[i]^orig_t);
         Append (~SP, <Params[i], "t">);
         Append (~VBeta, Params[i]);
         assert #original eq #VBeta;
         if Perfect and i in omega then 
            Append (~forms, Forms[i]);
            Append (~shapes, Shapes[i]);
            if Rewrite then Append (~reps, (rep^t)^s); end if;
            Append (~original, (Reps[i]^orig_t)^orig_s);
            Append (~SP, <Params[i], "ts">);
            Append (~VBeta, Params[i]);
            assert #original eq #VBeta;
            Append (~Split, #shapes - 1);
            Append (~Split, #shapes);
         end if;
      end if;
      Append (~L, SP);
   end for;

   // set up class list 
   // first set up parent group 
   if Special eq false then
      if epsilon eq 0 then
         G := GO(n, q);
         type := "GO";
      else
         G := epsilon eq 1 select GOPlus (n, q) else GOMinus (n, q);
         type := epsilon eq 1 select "GO+" else "GO-";
      end if;
   elif Special eq true and Perfect eq false then 
      if epsilon eq 0 then
         G := SO(n, q);
         type := "SO";
      else
         G := epsilon eq 1 select SOPlus (n, q) else SOMinus (n, q);
         type := epsilon eq 1 select "SO+" else "SO-";
      end if;
   else 
      if epsilon eq 0 then
         G := Omega(n, q);
         type := "Omega";
      else
         G := epsilon eq 1 select OmegaPlus (n, q) else OmegaMinus (n, q);
         type := epsilon eq 1 select "Omega+" else "Omega-";
      end if;
   end if;

   // EOB change April 8, 2020 -- identify non-split classes 
   LL := [];
   for i in [1..#L] do
      l := L[i];
      if #l eq 1 then l[1][2] := "ns"; end if; 
      Append (~LL, l);
   end for;
   L := LL;
   L := &cat (L);
   L := {@ <Multiset (x[1]), x[2]>: x in L @};

   // set up class list 
   C := []; D := [];
   for i in [1..#original] do
      size := OrthogonalUnipotentClassSize_Odd (G, type, shapes[i], VBeta[i], i in Split, q);
      if Rewrite then 
         Append (~C, <Order (reps[i]), size, reps[i]>);
      end if;
      Append (~D, <Order (original[i]), size, original[i]>);
   end for;
   
   return C, D, forms, shapes, L;
end function;

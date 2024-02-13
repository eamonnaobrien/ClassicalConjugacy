freeze;

import "Sp-Orthogonal-order.m":
   OrthogonalUnipotentCentraliserOrder_Even, SpUnipotentCentraliserOrder_Even;

import "util.m": ChooseAlpha, JordanBlock;

SpUnipotentClassSize_Even := function (G, T, q)
   return #G div SpUnipotentCentraliserOrder_Even (T, q);
end function;
 
OrthogonalUnipotentClassSize_Even := function (type, G, T, q)
   return #G div OrthogonalUnipotentCentraliserOrder_Even (type, T, q);
end function;

// building blocks 

V_beta_even := function (k, q, beta)
   MA := MatrixAlgebra (GF(q), 2 * k);
   if k eq 1 then 
      R := Identity (MA);
      R[1][2] := 1;
   else 
      M := MatrixAlgebra (GF (q), k);
      R := Zero (MA);
      I := Identity (M);
      for i in [1..Nrows (I)] do
         for j in [i + 1..Nrows (I)] do
            I[i][j] := 1;
         end for;
      end for;
      InsertBlock (~R, I, 1, 1);
      J := JordanBlock (k, q);
      InsertBlock (~R, J, k + 1, k + 1);
      for i in [1..k - 1] do
         R[i,k + 1] := 1;
         R[i,k + 2] := beta;
      end for;
      R[k,k + 1] := 1;
   end if;
   
   return GL(2 * k, q) ! R;
end function;
   
W_even := function (k, q)
   MA := MatrixAlgebra (GF(q), 2 * k);
   w := Zero (MA);
   for i in [1..k - 1] do 
      w[i, i] := 1; w[i, i + 1] := 1;
   end for;
   w[k, k] := 1;
   for i in [k + 1..2*k] do
      for j in [i..2 * k] do
         w[i][j] := 1;
      end for;
   end for;
   return GL(2 * k, q) ! w;
end function;

W_even_dash := function (k, q)
   MA := MatrixAlgebra (GF(q), 2 * k);
   w := Zero (MA);
   for i in [1..k - 2] do 
      w[i, i] := 1; w[i, i + 1] := 1;
   end for;
   w[k - 1, k - 1] := 1;
   w[k - 1, k + 1] := 1;
   w[k, k] := 1;
   for i in [k + 2..2 * k] do 
      w[k, i] := 1;
   end for;
   w[k + 1, k + 1] := 1;
   for i in [k + 2..2*k] do
      for j in [i..2 * k] do
          w[i][j] := 1;
      end for;
   end for;
   return GL(2 * k, q) ! w;
end function;
   
W_odd := function (k, q, beta)
   assert IsOdd (k);
   MA := MatrixAlgebra (GF(q), 2 * k);

   if k eq 1 then 
      I := Identity (MA);
      return GL(2 * k, q) ! I;
   end if;

   ell := k div 2;
   
   w := Zero (MA);
   // Revision EOB May 2016 
   for i in [1..k - 1] do 
      w[i, i] := 1; w[i, i + 1] := 1; 
      if i in {ell - 1, ell} then w[i, 2 * k - ell + 1] := beta; end if;
   end for;
   
   w[k, k] := 1;
   
   for i in [1..k] do
      if i ge ell + 2 then w[2 *k - i + 1, ell + 2] := beta; end if;
      for j in [k + i ..2 * k] do
         w[k + i][j] := 1;
      end for;
   end for;
   return GL(2 * k, q) ! w;
end function;

SpForm := function (k, q)
   MA := MatrixAlgebra (GF (q), 2 * k);
   form := Zero (MA);
   for i in [1..2 * k] do
      form[i, 2 * k + 1 - i] := 1;
   end for;
   return form;
end function;

// "O" form is satisfied by V_beta_even
// "Omega" form is satisfied by W_alpha 
OForm := function (type, k, q, b: nmr := 0)
   MA := MatrixAlgebra (GF (q), 2 * k);
   Q := Zero (MA);
   if type eq "O" then
      Q[k][k] := b; if nmr eq 0 then Q[k + 1, k + 1] := 1; end if;
      for i in [1..k] do
         Q[i][2*k - i + 1] := 1;
      end for;
   elif type eq "Omega" then  
      // EOB -- change of form June 2017 
      // if k eq 1 then return MA![b, b, 0, 1]; end if;
      if k eq 1 then return MA![b, 1, 0, b]; end if;
      assert IsOdd (k);
      l := k div 2;
      for i in [l..l + 1] do Q[i, i] := b; end for;
      Q[2 * k - l, 2 * k - l] := b;
      for i in [1..k] do
         Q[i][2*k - i + 1] := 1;
      end for;
   end if;
   return Q;
end function;

SetupRep := function (type, q, w, v, w_alpha, v_alpha, nmr)
   alpha := ChooseAlpha (q);
   MA := MatrixAlgebra (GF(q), 0);
   z := Zero (MA);
   V := z; W := z; W_alpha := z; V_alpha := z;
   formW := z; formV := z; formW_alpha := z; formV_alpha := z;

   if #w gt 0 then
      if nmr eq -1 then 
         A := W_even_dash (w[1], q);
         if #w gt 1 then 
            B := DiagonalJoin (<W_even (w[i], q): i in [2..#w]>);
            W := DiagonalJoin (A, B);
         else 
            W := A; 
         end if;
      else 
         W := DiagonalJoin (<W_even (k, q): k in w>); 
      end if;
      if type eq "Sp" then 
         formW := DiagonalJoin (<SpForm (k, q): k in w>);
      else 
         formW := DiagonalJoin (<OForm ("O", k, q, 0: nmr := 1): k in w>);
      end if;
   end if;
   if #v gt 0 then
      V := DiagonalJoin (<V_beta_even (k, q, 0): k in v>); 
      if type eq "Sp" then 
         formV := DiagonalJoin (<SpForm (k, q): k in v>);
      else 
         formV := DiagonalJoin (<OForm ("O", k, q, 0): k in v>);
      end if;
   end if;
   if #w_alpha gt 0 then
      W_alpha := DiagonalJoin (<W_odd (k, q, alpha): k in w_alpha>); 
      if type eq "Sp" then 
         formW_alpha := DiagonalJoin (<SpForm (k, q): k in w_alpha>);
      else 
         formW_alpha := DiagonalJoin (<OForm ("Omega", k, q, alpha: nmr := 1): k in w_alpha>);
      end if;
   end if;
   if #v_alpha gt 0 then
      V_alpha := DiagonalJoin (<V_beta_even (k, q, alpha): k in v_alpha>); 
      if type eq "Sp" then 
         formV_alpha := DiagonalJoin (<SpForm (k, q): k in v_alpha>);
      else 
         formV_alpha := DiagonalJoin (<OForm ("O", k, q, alpha): k in v_alpha>);
      end if;
   end if;
   t := <W, V, W_alpha, V_alpha>;
   r := DiagonalJoin (t); d := Nrows (r);
   r := GL(d, q) ! r;

   form := DiagonalJoin (<formW, formV, formW_alpha, formV_alpha>);

   return r, form;
end function;

ClassReps := function (type, q, T)
   R := []; F := [];
   for t in T do
      w := t[1]; v := t[2]; w_alpha := t[3]; v_alpha := t[4]; nmr := t[5];
      r, f := SetupRep (type, q, w, v, w_alpha, v_alpha, nmr);
      Append (~R, r);
      Append (~F, f);
   end for;
   return R, F;
end function;

IsGoodType := function (type, m, w, v, w_alpha, v_alpha)
   // sum of entries = m 
   t := v cat w cat w_alpha cat v_alpha;
   if &+t ne m then return false, 0, &+t; end if;

   if type in {"Omega+", "Omega-"} and IsOdd (#v + #v_alpha) then return false, 0, &+t; end if;

   // each case defines identity matrix 
   if Set (w) eq {1} and &+w eq m then return false, 0, &+t; end if;
   s := w cat w_alpha;
   if Set (s) eq {1} and &+s eq m then return false, 0, &+t; end if;

   if #v_alpha gt 0 then 
      for b in v_alpha do 
         if b in v then 
            if #[x : x in v | x eq b] gt 1 then return false, 0, &+t; end if;
         end if;
         if exists{a : a in v | (b - a) eq 1} then 
            // now enforced in setting up V_alpha 
            // or exists{a : a in v_alpha | (b - a) eq 1} then
            return false, 0, &+t; 
         end if;
      end for;
   end if;

   if #w_alpha gt 0 then 
      for b in w_alpha do 
         if exists{a : a in v | Abs (b - 2 * a) eq 1} or 
            exists{a : a in v_alpha | Abs (b - 2 * a) eq 1} then
            return false, 0, &+t; 
         end if;
      end for;
   end if;

   nmr := 1;
   if type in {"Omega+"} then
      if &+w eq m and forall{x: x in w | IsEven (x)} then
         // "*** Split class", w;
         nmr := 2;
      end if;
   end if;

   if type in {"O-", "Omega-"} and (IsOdd (#w_alpha + #v_alpha)) then
      return true, nmr, &+t;
   elif type in {"O+", "Omega+"} and (IsEven (#w_alpha + #v_alpha)) then
      return true, nmr, &+t;
   elif type eq "Sp" then 
      return true, nmr, &+t;
   else
      return false, 0, &+t;
   end if;
end function;

// set up form preserved by identity element 
FormForIdentity := function (type, d, q)
   assert IsEven (q);
   if type in {"O+", "Omega+"} then
      form := StandardQuadraticForm (d, q: Variant := "Default");
   elif type in {"O-", "Omega-"} then
      form := StandardQuadraticForm (d, q: Minus, Variant := "Default");
   elif type eq "Sp" then
      form := StandardAlternatingForm (d, q);
   end if;
   return form;
end function;

// given type, rank and even field size, write down unipotent class reps
// as elements of magma copy of corresponding SX (dim, q) 
// applies to Sp, Omega 

EvenUnipotentReps := function (type, dim, q: Rewrite := true) 

   // "Applies to even characteristic only";

   assert IsEven (q);
   assert IsEven (dim);

   m := dim div 2;
   F := GF (q);
   G := GL (2 * m, q);
   if type eq "Sp" then tf := "symplectic"; end if;
   if type in {"Omega+", "O+"} then tf := "orth+"; end if;
   if type in {"Omega-", "O-"} then tf := "orth-"; end if;

   S := [];
   for j in [1..m] do
      P := Partitions (j);
      S cat:= [Multiset (p): p in P];
   end for;

   W := S;
   W := [[Integers()|]] cat [[x : x in s] : s in W];

   // V rules
   V := [s : s in S | forall{x : x in s | Multiplicity (s, x) le 2}];
   V := [[Integers()|]] cat [[x : x in s] : s in V];

   // W_alpha rules
   W_alpha := [x : x in S | #Set (x) eq #x and forall{y : y in x | IsOdd (y)}];  
   if type eq "Sp" then 
      W_alpha := [x : x in W_alpha | forall{y : y in x | y ge 3}];
   end if;
   W_alpha := [[Integers()|]] cat [[x : x in s] : s in W_alpha];

   // V_alpha rules 
   V_alpha := [];
   for x in S do 
      if #Set (x) ne #x or exists{<a, b> : a in x, b in x | Abs (b - a) eq 1} then
         continue; 
      end if;
      Append (~V_alpha, x);
   end for;
   if type eq "Sp" then 
      V_alpha := [x : x in V_alpha | forall{y : y in x | y ge 2}];
   end if;
   V_alpha := [[Integers()|]] cat [[x : x in s] : s in V_alpha];

   T := [];
   // "length #W is ", #W, #V, #W_alpha, #V_alpha;
   for i in [1..#W] do
      // "i = ", i;
      for j in [1..#V] do
         x := W[i] cat V[j]; 
         if &+x gt m then break j; end if;
         for k in [1..#W_alpha] do 
            x := W[i] cat V[j] cat W_alpha[k]; 
            if &+x gt m then break k; end if;
            for l in [1..#V_alpha] do 
               flag, nmr, sum := IsGoodType (type, m, W[i], V[j], W_alpha[k], V_alpha[l]);
               if sum gt m then break l; end if;
               // if nmr gt 0 then "nmr is ", nmr; end if;
               if flag then 
                  Append (~T, <W[i], V[j], W_alpha[k], V_alpha[l], 1>);
                  // "last is ", #T, T[#T];
                  if nmr gt 1 then
                     Append (~T, <W[i], V[j], W_alpha[k], V_alpha[l], -1>);
                     // "now last is ", #T, T[#T];
                  end if;
               end if;
            end for;
         end for;
      end for;
   end for;

   reps, forms := ClassReps (type, q, T);

   R := [];
   if Rewrite then 
      for i in [1..#reps] do
         tr := GL(dim,q)!TransformForm (forms[i], tf: Restore := false);
         Append (~R, reps[i]^tr);
      end for; 
      Append (~R, Identity (G));
   end if;

   // add the identity element 
   id_rep := Identity (GL(dim, q));
   id_form := FormForIdentity (type, dim, q);
   reps cat:= [id_rep];
   forms cat:= [id_form];
   if type eq "Sp" then 
      Append (~T, <[1: i in [1..m]], [Integers()|], [Integers()|], [Integers()|], 1>);
   elif type in {"GO-", "O-", "SO-", "Omega-"} then 
      Append (~T, <[Integers()| 1: i in [1..m - 1]], [Integers()|], [1], [Integers()|], 1>);
   elif type in {"GO+", "O+", "SO+", "Omega+"} then 
      Append (~T, <[1: i in [1..m]], [Integers()|], [Integers()|], [Integers()|], 1>);
   end if;
   assert #T eq #reps;

   // set up class list 
   // first set up standard parent group 
   n := dim;
   if type eq "Sp" then
      G := Sp(n, q);
   elif type in {"O-", "GO-"} then
      G := GOMinus(n, q);
   elif type in {"O+", "GO+"} then
      G := GOPlus(n, q);
   elif type in {"SO-", "SO-"} then
      G := SOMinus(n, q);
   elif type in {"SO+", "SO+"} then
      G := SOPlus(n, q);
   elif type in {"Omega-"} then
      G := OmegaMinus(n, q);
   elif type in {"Omega+"} then
      G := OmegaPlus(n, q);
   end if;
   
   // set up class list 
   C := []; D := [];
   for i in [1..#reps] do
      size := type eq "Sp" select SpUnipotentClassSize_Even (G, T[i], q) 
              else OrthogonalUnipotentClassSize_Even (type, G, T[i], q);
      if Rewrite then 
         Append (~C, <Order (R[i]), size, R[i]>);
      end if;
      Append (~D, <Order (reps[i]), size, reps[i]>);
   end for;
   T := {@ t : t in T @};
   return C, D, forms, T;
end function;

// s, t, delta parameters for element of T 

OParameters := function (type, T)
   W := T[1] cat T[1] cat T[3] cat T[3];
    
   Sort (~W); Reverse (~W);
   V := T[2] cat T[4];
   Sort (~V);
    
   S := {w: w in W | IsOdd (w) and forall{v: v in V | Abs (w - 2 * v) ne 1}};
   if type eq "Sp" then Exclude (~S, 1); end if;
   s := #S;
     
   t := #[j: j in [1..#V - 1] | V[j + 1] - V[j] ge 2];
   delta := (#V eq 0) or (type eq "Sp" and 1 in V) select 0 else 1;
   return s, t, delta;
end function;

// given type and description of class over algebraically closed field,
// how many classes does it split into over finite field?

ClassesSplit := function (type, T)
   W := T[1] cat T[3];
   if #(T[2] cat T[4]) eq 0 and forall{w: w in W | IsEven (w)} then 
      if type in {"Omega-", "O-"} then return 0; end if;
      if type eq "O+" then return 1; end if;
      if type eq "Omega+" then return 2; end if;
   end if;
   s, t, delta := OParameters (type, T);
   if type eq "Sp" then 
      return 2^(s + t + delta); 
   else 
      return 2^(s + t + delta - 1); 
   end if;
end function;

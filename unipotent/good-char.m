freeze;

import "../semisimple/card.m": CardinalityOfClassicalGroup;
import "Centraliser-Order.m": UnipotentCentraliserOrder; 
import "Sp-Orthogonal-order.m": SpUnipotentCentraliserOrder;
import "util.m": NonSquare;

SLUnipotentClassSize := function (G, g)
   return #G div Integers () ! UnipotentCentraliserOrder ("SL", G, g, []);
end function;

SpUnipotentClassSize_Odd := function (G, T, VBeta, q)
   return #G div SpUnipotentCentraliserOrder (T, VBeta, q);
end function;

SUUnipotentClassSize := function (type, G, g)
   return #G div Integers () ! UnipotentCentraliserOrder (type, G, g, []);
end function;

// unipotent reps for GL, SL, GU, SU in all characteristics; 
// and for Sp in odd characteristic 
 
// all integer sequences whose i-th entry is in the 
// range [1..M[i] by 1] for i in [1..#M] 

BackTrack := function (M)
 
   if Set (M) eq {1} then return [M]; end if;
 
   offset := 1;
   n := #M;
   m := [1: i in [1..#M]] cat [1];
   original := m;
   min := Minimum (m);
 
   IndexList := [i: i in [1..#M] | M[i] ge min];
   len := #IndexList;
   Append (~IndexList, n + 1);
 
   Solns := [];
   repeat
      index := 1;
      m[IndexList[index]] +:= offset;
      while (index le len and m[IndexList[index]] gt M[IndexList[index]]) do
         m[IndexList[index]] := original[IndexList[index]];
         index +:= 1;
         m[IndexList[index]] +:= offset;                                       
      end while;
      Append (~Solns, Prune (m));
   until (index gt len);
 
   return Solns;
 
end function;

// building blocks 

MyJordanBlock := function (d, q, beta: sgn := 1)
   M := MatrixAlgebra (GF(q), d);
   A := Identity (M);
   for i in [1..d - 1] do
      A[i][i + 1] := sgn * 1;
   end for;
   if d gt 1 then A[1, 2] := beta; end if;
   return A;
end function;

// given rank and field size, write down unipotent class reps
// as elements of corresponding SL (n, q) 

SLUnipotentReps := function (n, q)

   F := GF (q);
   G := SL (n, q);

   P := Partitions (n);
   S := [Multiset (p): p in P];
   N := [[x : x in Set (s)]: s in S];
   T := [Gcd (n cat [q - 1]): n in N];
   M, phi := MultiplicativeGroup (GF (q));
   L := [];
   for t in T do 
      Q, tau := quo<M | t>;
      reps := [(x @@ tau) @ phi: x in Q];
      Append (~L, reps);
   end for;
   parameters := &cat (L);

   e := Degree (F);
   w := PrimitiveElement (GF(q));

   Reps := [];
   for i in [1..#S] do
      s := S[i];
      T := Set (s);
      T := [x : x in T];
      Sort (~T);
      n1 := Minimum (T);
      MA := MatrixAlgebra (F, 0);
      A := Zero (MA);
      B := Zero (MA);
      for t in T do 
         if t eq n1 then 
            m := Multiplicity (s, n1); 
            if m gt 1 then 
               two := MyJordanBlock (n1, q, 1);
               A := DiagonalJoin ([two: i in [1..m - 1]]);
            end if;
         else
            m := Multiplicity (s, t); 
            three := MyJordanBlock (t, q, 1);
            three := DiagonalJoin ([three: i in [1..m]]);
            B := DiagonalJoin (B, three); 
         end if;
      end for;
      reps := L[i];
      for beta in reps do 
         C := MyJordanBlock (n1, q, beta);
         C := DiagonalJoin (C, A);
         C := DiagonalJoin (C, B);
         Append (~Reps, <C, s>);
      end for;
   end for;

   T := [r[2]: r in Reps];
   Reps := [GL(n, q) ! r[1]: r in Reps];
   C := [];
   for i in [1..#Reps] do 
      size := SLUnipotentClassSize (G, Reps[i]);
      C[i] := <Order (Reps[i]), size, Reps[i]>;
   end for;

   T := {@ <T[i], parameters[i]>: i in [1..#T] @};
   return C, T;
end function;

GLUnipotentReps := function (n, q: Partition := [])

   F := GF (q);
   p := Characteristic (F);
   G := GL(n, q);
   Card := FactoredOrder (G);

   C := [];
   T := [];
   if #Partition eq 0 then 
      P := Partitions (n);
   else
      P := Partition;
   end if;
   for P1 in P do
      Y := IdentityMatrix (F, n);
      pos := 1;
      ord := p^Ceiling(Log (p, Maximum (P1)));
      for i in P1 do
         for j in [1..i-1] do
            Y[pos,pos+1] := 1;
            pos +:= 1;
         end for;
         pos +:= 1;
      end for;
      card := UnipotentCentraliserOrder ("GL", G, Y, Y: JF := P1);
      card := Integers () ! (Card / card);
      Append (~C, <ord, card, G!Y>);
      Append (~T, Multiset (P1));
   end for;
   return C, {@ t: t in T @};
end function;

A_beta_even := function (k, q, beta, type)
   F := type eq "SU" select GF (q^2) else GF (q);
   if type eq "SU" then assert beta + beta^q eq F!0; end if;
   MA := MatrixAlgebra (F, 2 * k);
   if k eq 1 then
      R := Identity (MA);
      R[1][2] := beta;
   else
      M := MatrixAlgebra (F, k);
      R := Zero (MA);
      I := Identity (M);
      for i in [1..Nrows (I)] do
       for j in [i + 1..Nrows (I)] do
          I[i][j] := 1;
       end for;
      end for;
      InsertBlock (~R, I, 1, 1);
      J := MyJordanBlock (k, #F, -1: sgn := -1);
      InsertBlock (~R, J, k + 1, k + 1);
      for i in [1..k] do
         R[i,k + 1] := beta;
      end for;
   end if;

   return GL(2 * k, F) ! R;
end function;

A_beta_odd := function (k, q, gamma, delta, type)
   F := type eq "SU" select GF (q^2) else GF (q);
   if type eq "SU" then 
      assert delta eq F!-1; assert gamma + gamma^q eq F!-1; 
   end if;
   MA := MatrixAlgebra (F, 2 * k + 1);
   if k eq 0 then 
       R := Identity (MA);
   else 
      M := MatrixAlgebra (F, k);
      R := Zero (MA);
      I := Identity (M);
      for i in [1..Nrows (I)] do
       for j in [i + 1..Nrows (I)] do
          I[i][j] := 1;
       end for;
      end for;
      InsertBlock (~R, I, 1, 1);
      J := MyJordanBlock (k, #F, -1: sgn := -1);
      InsertBlock (~R, J, k + 2, k + 2);
      for i in [1..k] do
         R[i,k + 1] := 1;
         R[i,k + 2] := gamma;
      end for;
      R[k + 1,k + 1] := 1;
      R[k + 1,k + 2] := delta;
   end if;
   
   return GL(2 * k + 1, F) ! R;
end function;

A_beta := function (k, q, beta, gamma, delta, type)
   if IsEven (k) then 
      return A_beta_even (k, q, beta, type);
   else  
      return A_beta_odd (k, q, gamma, delta, type);
   end if;
end function;

A_beta_even_form := function (k, q, type)
   F := type eq "SU" select GF (q^2) else GF (q);
   e := Degree (F);
   MA := MatrixAlgebra (F, 2 * k);
   form := Zero (MA);
   for i in [1..k] do
      form[i, 2 * k + 1 - i] := 1;
   end for;
   sign := type in {"SU", "Omega"} select 1 else -1;
   for i in [k + 1..2 * k] do
      form[i, 2 * k + 1 - i] := sign;
   end for;
   return form;
end function;

A_beta_odd_form := function (k, q, beta, type)
   F := type eq "SU" select GF (q^2) else GF (q);
   e := Degree (F);
   MA := MatrixAlgebra (F, 2 * k + 1);
   form := Zero (MA);
   for i in [1..k] do
      form[i, 2 * k + 2 - i] := 1;
   end for;
   form[k + 1, k + 1] := beta;
   sign := type in {"SU", "Omega"} select 1 else -1;
   for i in [k + 2..2 * k + 1] do
      form[i, 2 * k + 2 - i] := sign;
   end for;
   return form;
end function;

D_rep := function (n, q, alpha)
   F := GF (q^2); 
   f, lambda := Hilbert90 (alpha^-1, q);
   MA := MatrixAlgebra (F, n);
   D := Identity (MA);
   D[1,1] := lambda;
   D[n,n] := (lambda^-1)^q;
   assert Determinant (D) eq alpha;
   return GL(n, F) ! D;
end function;

// return element in standard copy of GU(n,F) with single Jordan block J_n

GUUnipotentBlock := function (n, F)            
   q := Isqrt (#F);
   w := F.1;
   if IsOdd (q) then
      b := w-(w+w^q)/2;                      // element of trace =0
      d := F!(q-1)/2;                        // element of trace =-1
   else
      b := w^(q+1);                          // element of trace =0
      d := w/(w+w^q);                        // element of trace =1
   end if;
   if n eq 1 then
      return IdentityMatrix (F, 1);
   end if;
   if n eq 2 then
      return Matrix (F, 2, 2, [1,b,0,1]);
   end if;
   if IsOdd (n) then
      m := n div 2;
      Y := IdentityMatrix (F, n);
      for i in [1..m+1] do
         for j in [i+1..m+1] do
            Y[i,j] := 1;
         end for;
         Y[i,m+2] := d;
      end for;
      for i in [m+2..n-1] do
         Y[i,i+1] := -1;
      end for;
      Y[m+1,m+2] := -1;
   else
      Y := IdentityMatrix (F, n);
      m := n div 2;
      for i in [1..m] do
         Y[i,m+1] := b;
         for j in [i+1..m] do
            Y[i,j] := 1;
         end for;
      end for;
      for i in [m+1..n-1] do
         Y[i,i+1] := -1;
      end for;
   end if;
   return Y;
end function;

// unipotent classes in GU(n, q)

GUUnipotentReps := function (n, q: Rewrite := true, Partition := [])

   F := GF(q^2);
   G := GL(n, q^2);
   VectorForms := <StandardHermitianForm(i, q): i in [1..n]>;
   Reps := [];
   Orig := [];
   Forms := [];
   T := [];
   
   if #Partition eq 0 then 
      P := Partitions (n);
   else
      P := Partition;
   end if;
   for p in P do
      Y := DiagonalJoin (<GUUnipotentBlock (i, F): i in p>);
      B := DiagonalJoin (<VectorForms[i]: i in p>);
      Append (~Orig, G!Y);
      Append (~Forms, B);
      Append (~T, Multiset(p));
      if Rewrite then
         m := TransformForm (B, "unitary": Restore := false);
         Append (~Reps, G!(m^-1*Y*m));
      end if;
   end for;

   C := []; D := [];
   for i in [1..#Orig] do 
      size := SUUnipotentClassSize ("GU", GU(n, q), Orig[i]);
      D[i] := <Order (Orig[i]), size, Orig[i]>;
      if Rewrite then 
         C[i] := <Order (Reps[i]), size, Reps[i]>;
      end if;
   end for;
   return C, D, Forms, {@ t : t in T @};
end function;

// given type, rank and field size, write down unipotent class reps
// as elements of corresponding SU (n, q) 

SUUnipotentReps := function (n, q: Rewrite := true, Verify := false)

   e := Degree (GF(q));
   F := GF (q^2);
   G := SU (n, q);
   _, form := UnitaryForm (G);

   P := Partitions (n);
   S := [Multiset (p): p in P];
   N := [[x : x in Set (s)]: s in S];
   T := [Gcd (n cat [q + 1]): n in N];
   // Same Jordan Form for each related collection of parameters  
   JF := &cat[[S[i]: j in [1..T[i]]]: i in [1..#T]];
   nmr := &+T;
   // "Nmr of classes is ", nmr;
   L := [];
   M, phi := MultiplicativeGroup (F);
   z := (Order (M.1) div (q + 1)) * M.1;
   assert Order (z) eq q + 1;
   Z := sub<M | z>;
   T := [Gcd (n): n in N];
   for t in T do 
      Q, tau := quo<Z | t * Z.1>;
      reps := [(x @@ tau) @ phi: x in Q];
      Append (~L, reps);
   end for;

   e := Degree (F) div 2;
   w := PrimitiveElement (GF(q));

   FixedRoot := function (f)
      roots := Roots (f);
      roots := [r[1]: r in roots];
      Sort (~roots);
      return roots[1], roots; 
   end function;

   // R<x>:= PolynomialRing (F);
   // time gamma := FixedRoot (x + x^q + 1);
   assert exists(gamma) {x : x in F | x ne 0 and x + x^q eq -1};
   beta := Root (F!-1, q - 1);
   // assert exists(beta) {x : x in F | x ne 0 and x + x^q eq 0};

   delta := F!-1;

   type := "SU";

   Reps := []; Forms := [];
   Orig := []; Params := [];
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
      for t in T do 
         m := Multiplicity (s, t);
         k := t div 2;
         if IsEven (t) then 
            one := A_beta_even (k, q, beta, type);
            one := DiagonalJoin ([one: i in [1..m]]);
            A := DiagonalJoin (A, one);
            one := A_beta_even_form (k, q, type);
            one := DiagonalJoin ([one: i in [1..m]]);
            form_A := DiagonalJoin (form_A, one);
         else
            two := A_beta_odd (k, q, gamma, delta, type);
            two := DiagonalJoin ([two: i in [1..m]]);
            B := DiagonalJoin (B, two); 
            two := A_beta_odd_form (k, q, 1, type);
            two := DiagonalJoin ([two: i in [1..m]]);
            form_B := DiagonalJoin (form_B, two); 
         end if;
      end for;
      rep := GL(n, F) ! DiagonalJoin (A, B);
      form := GL(n, F) ! DiagonalJoin (form_A, form_B);
      if Verify then
         assert rep * form * Transpose (FrobeniusImage (rep, e)) eq form;
      end if;

      conj := [D_rep (n, q, alpha): alpha in L[i]]; 
      reps := [rep^c: c in conj];
      Append (~Orig, reps);
      forms := [c^-1 * form * Transpose (FrobeniusImage (c^-1, e)): c in conj];
      Append (~Forms, forms);
      params := [conj[i][1][1]: i in [1..#conj]];
      Append (~Params, params);

      if Rewrite then 
         tr := TransformForm (form, "unitary": Restore := false);
         rep := rep^tr;
         reps := [rep^c: c in conj];
         Append (~Reps, reps);
      end if;
   end for;
   Reps := &cat (Reps);
   Orig := &cat (Orig);
   Forms := &cat(Forms);

   Reps := [GL(n, q^2) ! r : r in Reps];
   C := []; D := [];
   for i in [1..#Orig] do 
      size := SUUnipotentClassSize ("SU", SU(n, q), Orig[i]);
      D[i] := <Order (Orig[i]), size, Orig[i]>;
      if Rewrite then 
         C[i] := <Order (Reps[i]), size, Reps[i]>;
      end if;
   end for;

   Params := &cat (Params);
   JF := {@ <JF[i], Params[i]>: i in [1..#JF] @};

   return C, D, Forms, JF, Params;
end function;

// given type, rank and odd field size, write down unipotent class reps
// as elements of corresponding Sp (n, q) 

SpUnipotentReps := function (n, q: Rewrite := true)

   // "*** Applies to odd characteristic only";
   assert IsEven (n);
   assert IsOdd (q);
   k := n div 2;
   F := GF (q);
   G := Sp (n, q);

   P := Partitions (n);
   S := [Multiset (p): p in P];
   // W rules
   T := [];
   for s in S do
      t := {x: x in s};
      if exists{x : x in t | IsOdd (x) and IsOdd (Multiplicity (s, x))} then
         continue;
      end if;
      Append (~T, s);
   end for;
   S := T;
   List_T := [];

   type := "Sp";

   alpha := NonSquare (F);
   Reps := [ GL(n, q) | ]; Forms := []; original_reps := [ GL(n, q) | ];
   Params := [];
   Nmr := 0;
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

      A_val := [];
      for t in T do 
         m := Multiplicity (s, t);
         k := t div 2;
         if IsEven (t) then 
            one := Zero (M);
            if m gt 1 then 
               temp := A_beta_even (k, q, 1, type);
               temp := DiagonalJoin ([temp: i in [1..m - 1]]);
               one := DiagonalJoin (one, temp);
            end if;
            A := DiagonalJoin (A, one);
            A_val cat:= [<t, 1>: i in [1..(m - 1)]];
            if m gt 1 then 
               one := A_beta_even_form (k, q, type);
               one := DiagonalJoin ([one: i in [1..m - 1]]);
            end if;
            form_A := DiagonalJoin (form_A, one);
         else
            two := A_beta_even (2 * k + 1, q, 0, type);
            two := DiagonalJoin ([two: i in [1..m div 2]]);
            B := DiagonalJoin (B, two); 
            A_val cat:= [<2*k + 1, 0>: i in [1..m div 2]];
            two := A_beta_even_form (2 * k + 1, q, type);
            two := DiagonalJoin ([two: i in [1..m div 2]]);
            form_B := DiagonalJoin (form_B, two); 
         end if;
      end for;

      even := [x : x in T | IsEven (x)];
      Nmr +:= 2^#even;
      params := [];
      if #even gt 0 then 
         L := exists{t: t in T | IsEven (t)} select [1, alpha] else [1];
         list := BackTrack ([#L: i in [1..#even]]);
         X := [* [A_beta_even (t div 2, q, beta, type) : beta in L]: t in T | IsEven (t) *]; 
         params := [[<t, beta>: beta in L]: t in T | IsEven (t)];
         Y := [* [A_beta_even_form (t div 2, q, type) : beta in L]: t in T | IsEven (t) *]; 
         C := [DiagonalJoin (<X[i][l[i]]: i in [1..#X]>): l in list];
         params := [[params[i][l[i]]: i in [1..#X]]: l in list];
         C_form := [DiagonalJoin (<Y[i][l[i]]: i in [1..#X]>): l in list];
         C := [DiagonalJoin (<c, A>): c in C];
         params := [params[i] cat A_val: i in [1..#params]];
         C_form := [DiagonalJoin (<c, form_A>): c in C_form];
         C := [DiagonalJoin (<c, B>): c in C];
         C_form := [DiagonalJoin (<c, form_B>): c in C_form];
      else 
         C := [DiagonalJoin (<A, B>)];
         params cat:= [A_val];
         C_form := [DiagonalJoin (<form_A, form_B>)];
      end if;

      List_T cat:= [S[i]: j in [1..#C]];
      reps := [];
      if Rewrite eq true then 
         for r in [1..#C] do
            rep := GL(n, F) ! C[r];
            tr := GL(n, F) ! TransformForm (C_form[r], "symplectic": Restore := false);
            rep := rep^tr;
            Append (~reps, rep);
         end for;
      end if;
      Reps cat:= reps;
      original_reps cat:= C;
      Forms cat:= C_form;
      Append (~Params, params);
   end for;
   assert #original_reps eq Nmr; 
   assert #List_T eq Nmr;
   T := List_T;

   Params := &cat (Params);
   Params := {@ Multiset (x): x in Params @};
   C := []; D := [];
   for i in [1..#original_reps] do
      r := original_reps[i];
      size := SpUnipotentClassSize_Odd (G, T[i], Params[i], q);
      D[i] := <Order (r), size, r>;
      if Rewrite then 
         C[i] := <Order (r), size, Reps[i]>; 
      end if;
   end for; 

   return C, D, Forms, T, Params;
end function;

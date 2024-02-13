freeze;

import "../util.m": MySort, KernelOfHom;
import "../Centraliser-Order.m": UnipotentCentraliserOrder;
import "semisimple.m": SemisimpleMatrices;

// GU / SU all characteristics: 
// sort out parameters; upper-triangular rep; centraliser in Q-subgroup

SUJordanBlock := function (d, q: beta := 0)
   if beta eq 0 then 
      if IsEven (d) then 
         beta := Root (GF(q^2)!-1, q - 1);
      else
         flag := exists(beta){beta : beta in GF(q^2) | beta + beta^(q) eq -1};
      end if;
   end if;

   M := MatrixAlgebra (GF(q^2), d);
   A := Identity (M);

   if IsOdd (d) then 
      for i in [1..d div 2] do
         for j in [i + 1..d div 2 + 1] do
             A[i][j] := 1; 
         end for;
      end for;
      A[d div 2 + 1, d div 2 + 1] := 1;
      for i in [1..d div 2] do
         A[i, d div 2 + 2] := beta;
      end for;
      if d gt 1 then 
         A[d div 2 + 1, d div 2 + 2] := -1;
      end if;
      for i in [d div 2 + 2..d - 1] do
         A[i][i + 1] := -1;
      end for;
      return A;
   end if;

   for i in [1..d div 2] do
      for j in [i + 1..d div 2] do
         A[i][j] := 1; 
      end for;
   end for;
   for i in [d div 2 + 1..d - 1] do
      A[i][i + 1] := -1;
   end for;
   A[d div 2 + 1, d div 2 + 1] := 1;
   for i in [1..d div 2] do
      A[i, d div 2 + 1] := beta;
   end for;
   return A;
end function;

SU_ClassRep := function (m, q: beta := 0)
   d := &+[m[i][1] * m[i][2] : i in [1..#m]];

   R := [];
   for i in [1..#m] do 
      r := m[i][1]; 
      L := [-(r - 1)..(r - 1) by 2];
      L := [x : x in L];
      for j in [1..m[i][2]] do 
         Append (~R, L);
      end for;
   end for;

   W := Set (&cat (R));
   W := [x : x in W];
   Sort (~W);

   L := [#x: x in R];
   rep := DiagonalJoin (<SUJordanBlock (a, q: beta := beta): a in L>);
   
   L := &cat (R);
   pos := &cat[[i : i in [1..#L] | L[i] eq c]: c in W];
   S := Sym (d);
   P := PermutationMatrix (GF(q), S!pos);

   S := [<w, #[x : x in L | x eq w]>: w in W];
   
   return P * rep * Transpose (P), S, P;
end function;

SUForm := function (m, a, q)
   d := &+[m[i][1] * m[i][2] : i in [1..#m]];
   weight := [a[i][2] : i in [1..#a]];
   wt := [0] cat [a[i][2] : i in [1..#a]];
   index := [1 + &+[wt[i]: i in [1..j]]: j in [1..#a]];

   M := MatrixAlgebra (GF (q^2), d);
   form := Zero (M);
   for j in [1..#index] do 
      i := index[j];
      w := weight[j];
      offset := &+[weight[k]: k in [1..j]];
      MA := MatrixAlgebra (GF (q^2), w);
      A := Identity (MA);
      InsertBlock (~form, A, i, d - offset + 1);
   end for;
    
   return form;
end function;

MyTransvection := function (d, q, i, j, J)
   F<delta> := GF (q^2);
   MA := MatrixAlgebra (F, d);
   L := [ GL(d, F) | ]; 

   if <i, j> in J then
      l := AllRoots (F!-1, q - 1);
      p := Characteristic (F);
      V, phi := VectorSpace (F, GF(p));
      s := sub < V | [phi (x): x in l]>;
      B := Basis (s);
      B := [b @@ phi: b in B];
      for beta in B do 
         T := Identity (MA);
         T[i][j] := beta;
         Append (~L, T);
      end for;
      return L;
   end if;
      
   A := [J[i][1]: i in [1..#J]];
   B := [J[i][2]: i in [1..#J]];
   e := Degree (F);
   for f in [0..e - 1] do 
      lambda := delta^f;
      T := Identity (MA);
      a := Position (A, j);
      T[i][B[a]] := lambda;
      b := Position (A, i);
      T[j][B[b]] := -(lambda^q);
      Append (~L, T);
   end for;

   return L;
end function;

// B is F_p basis in both cases  
MyTriple := function (d, q, i, j, k, J)
   F<delta> := GF (q^2);
   MA := MatrixAlgebra (F, d);

   l := AllRoots (F!-1, q - 1);
   p := Characteristic (F);
   V, phi := VectorSpace (F, GF(p));
   s := sub< V | [phi (x): x in l]>;
   B := Basis (s);
   B := [x @@ phi: x in B];
   L := [ GL(d, F) | ]; 
   for alpha in B do 
      T := Identity (MA);
      T[i][k] := alpha;
      Append (~L, T);
   end for;

   B := Basis (V);
   B := [x @@ phi: x in B];
   for lambda in B do 
      flag := exists (alpha){alpha : alpha in F | lambda * lambda^q + alpha + alpha^q eq 0};
      assert flag;
      T := Identity (MA);
      T[i][k] := alpha;
      T[i][j] := lambda;
      T[j][k] := -lambda^q;
      Append (~L, T);
   end for;
   return L;
end function;
   
// Q-subgroup
SU_QSubgroup := function (a, q)
   weight := [a[i][1]: i in [1..#a]];
   mult := [a[i][2]: i in [1..#a]];
   d := &+mult;

   // odd dimensional Jordan block? 
   odd := 0 in weight;

   full := [[weight[i]: j in [1..mult[i]]]: i in [1..#weight]]; 
   full := &cat (full);

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

   J := [];
   for w in weight do 
      if w lt 0 then 
         posA := Position (full, w);
         posB := Position (full, -w);
         nmr := 0;
         for k in [posA..d div 2] do
            nmr +:= 1;
            if full[k] eq w then 
               Append (~J, <k, posB + nmr - 1>);
            end if;
         end for;
      end if;
   end for;

   T := [];
   if odd then 
      for i in [1..#full] do 
         if full[i] eq 0 then 
            T cat:= [<j[1], i, j[2]>: j in J];
         end if;
      end for;
   end if;
   
   L := [];
   if not odd then 
      I cat:= J;
      J := J cat [<j[2], j[1]>: j in J];
      L := [MyTransvection (d, q, i[1], i[2], J): i in I];
      L := &cat (L);
   else 
      J := J cat [<j[2], j[1]>: j in J];
      L := [MyTransvection (d, q, i[1], i[2], J): i in I];
      L := &cat (L);
      V := [MyTriple (d, q, t[1], t[2], t[3], J): t in T];
      V := &cat (V);
      L := L cat V;
   end if;

   Q := sub<GL(d, q^2) | L>;
      
   return Q, I, J, T;
end function;

SUCentraliserDimension := function (m)
   dim := [m[i][1]: i in [1..#m]];
   mult := [m[i][2]: i in [1..#m]];
   ParallelSort (~dim, ~mult);
   a := &+[(dim[i] - 1) * mult[i]^2: i in [1..#m]]; 

   b := 0;
   for i in [1..#m] do 
      x := [dim[i] * mult[i] * mult[j]: j in [i + 1..#m]];
      b +:= #x eq 0 select 0 else &+x;
   end for;
   return a + 2 * b;
end function;

SU_ConvertToSpecialRep := function (g)
   G := Parent (g);
   F := BaseRing (G);
   e := Degree (F) div 2;
   q := Isqrt (#F);
   J, CB, b := JordanForm (g);
   s := [b[i][2]: i in [1..#b]];
   m := [<x, #[y: y in s | y eq x]>: x in Set (s)];
   m, p := MySort (m);
   perm := PermutationMatrix (GF(q^2), p);
   r, a, P := SU_ClassRep (m, q);
   J1, CB1 := JordanForm (r);
   cb := Generic (G) ! (CB1^-1 * CB);
   assert cb * g * cb^-1 eq r;    
   form := SUForm (m, a, q);
   assert form eq r * form * Transpose (FrobeniusImage (r, e));
   return Generic (G) ! r, form, m, a, cb;
end function;

// construct centraliser in GU of special rep for unipotent element g in SU(d, q):
// i) construct maximal parabolic subgroup Q which contains unipotent
//    part of centraliser of special rep r for g;
// ii) construct semisimple matrices which centralise r

GUUnipotentCentraliser := function (G, g)
   F := BaseRing (Parent (g));
   q := Isqrt (#F);
   e := Degree (GF(q));
   d := Nrows (g);

   // special rep 
   r, form, m, W, CB := SU_ConvertToSpecialRep (g);

   //construct maximal parabolic Q and compute centraliser of r in Q
   Q := SU_QSubgroup (W, q);
   Q := UnipotentMatrixGroup (Q);
   P, phi, tau := PCPresentation (Q);
   CP := Centraliser (P, phi (r));
   C := CP @ tau;
   assert IsCentral (C, r);

   // check result 
   dim := SUCentraliserDimension (m);
   assert dim * e eq NPCgens (CP);
   assert Ngens (Q) eq NPCgens (P);

   // semisimple centraliser
   D := SemisimpleMatrices (W, q: Type := "Unitary");

   U := sub<GL(d, F) | C, D>;
   assert IsCentral (U, r);
   return U, r, form, CB;
end function;

// if S is SU, then construct centraliser in S as kernel of 
// hom from centraliser G in GU to group of determinants 
MyUnitary_UnipotentCentraliser := function (S, g)

   d := Degree (S); E := BaseRing (S);
   flag, form := UnitaryForm (S);
   assert flag;
    _, sigma := StandardHermitianForm (d, Isqrt (#E));
   V := UnitarySpace (form, sigma);
   U := IsometryGroup (V);
   G, r, form, CB := GUUnipotentCentraliser (U, g);

   if forall{x: x in Generators (S) | Determinant (x) eq 1} then 
      C, eta := MultiplicativeGroup (E);
      phi := hom <Generic (G) -> C | x :-> Determinant (x) @@ eta>;
      images := [phi (G.i): i in [1..Ngens (G)]];
      I := sub< C | images>;
      images := [Eltseq (I!i): i in images];
      images := &cat (images);
      G := KernelOfHom (G, I, images);
      order := UnipotentCentraliserOrder ("SU", S, g, g^0);
   else
      order := UnipotentCentraliserOrder ("GU", S, g, g^0);
   end if;
   G`FactoredOrder := order;
   G`Order := Integers ()!order;

   return G, r, form, CB;
end function;

freeze;

import "../util.m": MySort, JordanBlock, KernelOfHom;
import "../Centraliser-Order.m": UnipotentCentraliserOrder;
import "../good-char.m": D_rep, GLUnipotentReps;
import "semisimple.m": SemisimpleMatrices;
import "../../linear/SL-IsConjugate.m": GLIsConjugate; 

// GL and SL all characteristics: 
// sort out parameters; upper-triangular rep; Q-subgroup; and centraliser in Q 

// Q-subgroup
SL_QSubgroup := function (m, a, q) 
   weight := [a[i][2] : i in [1..#a]];
   d := &+weight;

   K := GF (q);
   g := DiagonalJoin (<GL(w, K).0: w in weight>);
   I := []; O := [];
   for i in [1..d] do
      I[i] := Minimum ({j : j in [1..#weight] | &+[weight[k]: k in [1..j]] ge i});
      O[i] := &+[weight[k]: k in [1..I[i]]];
   end for;
   L := [];
   e := Degree (K);
   delta := PrimitiveElement (K);
   for i in [1..d] do
      for j in [O[i] + 1 ..d] do
        for f in [1..e] do
            gen := g;
            gen[i][j] := delta^f;
            Append (~L, gen);
        end for;
      end for;
   end for;
   return sub<GL(d, K) | L>;
end function;

SL_ClassRep := function (m, q)
   d := &+[m[i][1] * m[i][2] : i in [1..#m]];
   R := [];
   for i in [1..#m] do 
      r := m[i][1]; 
      L := [-(r - 1) .. (r - 1) by 2];
      L := [x : x in L];
      for j in [1..m[i][2]] do 
         Append (~R, L);
      end for;
   end for;

   W := Set (&cat (R));
   W := [x : x in W];
   Sort (~W);

   L := [#x: x in R];
   rep := DiagonalJoin (<JordanBlock (a, q): a in L>);

   L := &cat (R);
   pos := &cat[[i : i in [1..#L] | L[i] eq c]: c in W];
   S := Sym (d);
   P := PermutationMatrix (GF(q), S!pos);

   S := [<w, #[x : x in L | x eq w]>: w in W];
   
   return P * rep * Transpose (P), S, P;
end function;

GLParameters := function (g)
   J, CB, b := JordanForm (g);
   s := [b[i][2]: i in [1..#b]];
   m := [<x, #[y: y in s | y eq x]>: x in Set (s)];
   m, p := MySort (m);
   return m;
end function;

SL_ConvertToSpecialRep := function (g)
   G := Parent (g);
   F := BaseRing (Parent (g));
   q := #F;
   J, CB, b := JordanForm (g);
   s := [b[i][2]: i in [1..#b]];
   m := [<x, #[y: y in s | y eq x]>: x in Set (s)];
   m, p := MySort (m);
   perm := PermutationMatrix (GF(q), p); 
   r, a, P := SL_ClassRep (m, q);
   J1, CB1 := JordanForm (r);
   cb := Generic (G) ! (CB1^-1 * CB);
   assert cb * g * cb^-1 eq r;
   return Generic (G) ! r, m, a, cb;
end function;

// centraliser of unipotent element g of SL(d, q): 
// i) construct maximal parabolic subgroup Q which contains unipotent
// part of centraliser of g; 
// ii) construct semisimple matrices which centralise g 

GLUnipotentCentraliser := function (G, g)
   F := BaseRing (Parent (g));
   d := Nrows (g);
   q := #F;

   // special rep 
   r, m, W, CB := SL_ConvertToSpecialRep (g);
   
   // construct maximal parabolic Q and compute centraliser in Q 
   Q := SL_QSubgroup (m, W, q);
   Q := UnipotentMatrixGroup (Q);
   P, phi, tau := PCPresentation (Q);

   CP := Centraliser (P, phi (r));
   C := CP @ tau;
   assert IsCentral (C, r);

   // semisimple centraliser 
   D := SemisimpleMatrices (W, q);

   U := sub<GL(d, q) | C, D>;
   U := U^CB;
   assert IsCentral (U, g);
   return U;
end function;

// if S is SL, then construct centraliser in S as kernel of
// hom from centraliser G in GL to group of determinants
SLUnipotentCentraliser := function (S, g)

   d := Degree (S); E := BaseRing (S);
   G := GLUnipotentCentraliser (S, g);

   if forall{x: x in Generators (S) | Determinant (x) eq 1} then
      C, eta := MultiplicativeGroup (E);
      phi := hom <Generic (G) -> C | x :-> Determinant (x) @@ eta>;
      images := [phi (G.i): i in [1..Ngens (G)]];
      I := sub<C | images>;
      images := [Eltseq (I!i): i in images];
      images := &cat (images);
      G := KernelOfHom (G, I, images);
      order := UnipotentCentraliserOrder ("SL", S, g, g^0);
   else 
      order := UnipotentCentraliserOrder ("GL", S, g, g^0);
   end if;
   G`FactoredOrder := order;
   G`Order := Integers ()!order;

   return G;
end function;

// parameters for g in SL 
SLParameters := function (G, g) 
   F := BaseRing (G);
   d := Degree (G);
   q := #F;
   Z, phi := MultiplicativeGroup (F);
   partition := GLParameters (g);
   partition := &cat[[x[1]: i in [1..x[2]]]: x in partition];
   S := Set (partition) join {q - 1};
   t := Gcd (S);
   Q, tau := quo<Z | t * Z.1>;
   Params := [(x @@ tau) @ phi: x in Q];
   rep := GLUnipotentReps (d, q: Partition := [partition]);
   rep := rep[1][3];
   flag, CB := GLIsConjugate (G, g, rep);
   assert g^CB eq rep;
   l := Determinant (CB);
   val := (l^-1) @@ phi @ tau; // element of Z/tZ
   assert exists(alpha){alpha: alpha in Params |
                        -alpha @@ phi @ tau eq val};
   return <partition, alpha>, CB;
end function;

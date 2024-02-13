/*
    $Id: ProjClasses.m 65133 2021-11-21 02:56:51Z don $
*/

// functions prepared with Derek Holt and Don Taylor

ClassicalCentreOrder := AssociativeArray();
ClassicalCentreOrder["GL"] := func<d, q | q - 1>;
ClassicalCentreOrder["SL"] := func<d, q | GCD(d, q - 1)>;

ClassicalCentreOrder["GU"] := func<d, q | q + 1>;
ClassicalCentreOrder["SU"] := func<d, q | GCD(d, q + 1)>;

ClassicalCentreOrder["Sp"] := func<d, q | GCD(2, q - 1)>;

ClassicalCentreOrder["GO"] := func<d, q | IsEven(q) select 1 else 2>;
ClassicalCentreOrder["SO"] := func<d, q | 1>;
ClassicalCentreOrder["Omega"] := func<d, q | 1>;

ClassicalCentreOrder["GO+"] := func<d, q | IsEven(q) select 1 else 2>;
ClassicalCentreOrder["SO+"] := func<d, q | IsEven(q) select 1 else 2>;
ClassicalCentreOrder["Omega+"] := func<d, q |
   IsEven(q) select 1 else (IsEven(d * (q - 1) div 4) select 2 else 1)>;

ClassicalCentreOrder["GO-"] := func<d, q | IsEven(q) select 1 else 2>;
ClassicalCentreOrder["SO-"] := func<d, q | IsEven(q) select 1 else 2>;
ClassicalCentreOrder["Omega-"] := func<d, q |
   IsEven(q) select 1 else (IsOdd(d * (q - 1) div 4) select 2 else 1)>;

import "Gen-Label.m": StandardGroup;

// tau is hom from standard classical group G to its projective copy G / <z>

ClassesForSpO := function (G, tau, z : MatricesOnly := false) 
   C := ClassicalConjugacyClasses (G);
   if Order (z) eq 1 then 
      mm := [<C[i][1], C[i][2], C[i][3]>: i in [1..#C]];
      if MatricesOnly then
         return mm, _;
      else
         return [<C[i][1], C[i][2], tau (C[i][3])>: i in [1..#C]],mm;
      end if;
   end if;
   
   phi := ClassicalClassMap (G);
   projclassrep := [i : i in [1..#C]];
   projclasslen := [];
   known := {};
   for i in [1..#C] do
      if i in known then continue; end if;
      g := C[i][3];
      if not ClassicalIsConjugate(G, g, g*z) then
         /* length of the class of the image of g in the projective 
            group is C[i][2] if this condition holds and C[i][2]/2 
            otherwise.  */
         cno := phi(g*z);
         Include (~known, cno);
         projclassrep[cno] := i;
         projclasslen[i] := C[i][2];
      else 
         projclasslen[i] := C[i][2] div 2;
      end if;
   end for; 
   index := [i: i in [1..#projclassrep] | projclassrep[i] eq i];
   mm := [<Order (C[i][3]), projclasslen[i], C[i][3]>: i in index];
   if MatricesOnly then
      return mm, _;
   else
      CL := [<Order (C[i][3]), projclasslen[i], tau (C[i][3])>: i in index];
      return CL, mm;
   end if;
end function;

//==============================================================================
intrinsic ProjectiveClassicalClasses (type::MonStgElt, 
  n::RngIntElt, q::RngIntElt : UseLMGHom := false, MatricesOnly := false)
  -> SeqEnum, GrpPerm, HomGrp, SeqEnum
{The conjugacy classes of the projective classical group P of 
 supplied type; return the classes, P, the homomorphism f from the classical
 group G to P, and preimages of the class representatives in G}

   ValidTypes := ["SL", "GL", "Sp", "SU", "GU", "Omega+", "Omega-", "Omega",
                  "SO+", "SO-", "SO", "GO+", "GO-", "GO"];
 
   require type in ValidTypes: "Type must be one of ", ValidTypes;
   require IsPrimePower (q): "Invalid field size";
 
   require n gt 1: "Degree must be at least 2";
   if type in {"GO", "SO", "Omega"} then
      require IsOdd (n) and n gt 2: "Degree must be odd and at least 3"; 
      require IsOdd (q): "Field size must be odd"; 
   elif type in {"Sp", "Omega+", "SO+", "GO+", "Omega-", "SO-", "GO-"} then 
      require IsEven (n): "Degree must be even"; 
   end if;
 
   G, P := StandardGroup (type, n, q : Projective);
   
   if IsTrivial (P) then // e.g. POmegaPlus (2, 2) 
      mm := [<1,1,G.0>];
      if MatricesOnly then
         return mm, _, _, _;
      else
         f := hom < G -> P | [P.0: i in [1..Ngens (G)]]>;
         return Classes (P), P, f, mm;
      end if;
   elif n eq 2 and q eq 3 and type eq "GO+" then
      mm := [<1,1,G.0>, <2,1,G.2>];
      if MatricesOnly then
         return mm, _, _, _;
      else
         f := hom< G -> P | [P.0,P.1] >;
         return Classes (P), P, f, mm;
      end if;
   end if;
 
   d := ClassicalCentreOrder[type](n, q);
   F := type in {"GU", "SU"} select GF(q^2) else GF(q);
   xi := PrimitiveElement (F);
   z := ScalarMatrix (F, n, xi);
   z := Generic (G) ! (z^((#F - 1) div d));
 
   if not MatricesOnly then
      // basic checks before setting up homomorphism 
      assert Ngens (P) eq Ngens (G);
      assert forall{i: i in [1..Ngens (G)] | Order (G.i) mod Order (P.i) eq 0};
      RandomSchreier (P);
      if not UseLMGHom or HasBSGS(G) then 
         f := hom<G -> P | [P.i : i in [1..Ngens(G)]] >;
      else 
         f := LMGHomomorphism (G, [P.i : i in [1..Ngens(G)]]);
      end if;
   end if;
 
   if type notin {"GL", "SL", "GU", "SU"} then 
      if MatricesOnly then
         f := IdentityHomomorphism (G);
         mm := ClassesForSpO (G, f, z : MatricesOnly);
         return mm, _, _, _;
      else
         cc, mm := ClassesForSpO (G, f, z); 
         P`Classes := cc;
         C := Classes (P);
         index := [Position (C, cc[i]): i in [1..#cc]];
         ParallelSort (~index, ~mm);
         return C, P, f, mm;
      end if;
   end if;
 
   cc := ClassicalClasses (G);
   phi := ClassicalClassMap (G);
 
   if d eq 1 then 
      mm := [<c[1], c[2], c[3] > : c in cc ];
      if not MatricesOnly then 
         cc := [<c[1], c[2], f(c[3]) > : c in cc ];
      end if;
   else 
      pClassSz := [0 : i in [1..#cc]];
      available := [ true : i in [1..#cc]];
      for i -> c in cc do
         if available[i] then
           g := c[3];
           count := 1;
           for k := 1 to d - 1 do
             h := g*z^k;
             if not ClassicalIsConjugate (G,g,h) then
               available[phi(h)] := false;
             else
               count +:= 1;
             end if;
           end for;
           flg, m := IsDivisibleBy (c[2],count);
           assert flg;
           pClassSz[i] := m;
         end if;
      end for;
      mm := [ < cc[i][1], pClassSz[i], cc[i][3] > : i in [1..#cc] | available[i] ]; 
      if not MatricesOnly then
        cc := [ < Order(x), pClassSz[i], x > : i in [1..#cc] | available[i]
           where x is f(cc[i][3]) ];
      end if;
   end if;
   if MatricesOnly then
      return mm, _, _, _;
   else
      P`Classes := cc;
      C := Classes (P);
      index := [Position (C, cc[i]): i in [1..#cc]];
      ParallelSort (~index, ~mm);
      return C, P, f, mm;
   end if;
end intrinsic;

intrinsic ProjectiveClassicalCentraliser (G:: GrpMat, g:: GrpMatElt)  -> Grp
{return preimage in the classical group G of centraliser of image of g in the central quotient of G}
   ValidTypes := ["SL", "GL", "Sp", "SU", "GU", "Omega+", "Omega-", "Omega",
                 "SO+", "SO-", "SO", "GO+", "GO-", "GO"];
   f, type := ClassicalGroupType (G);
   require type in ValidTypes: "Function does not apply to classical group of type", type; 

   n := Degree (G); F := BaseRing (G);
   q := type in {"GU", "SU"} select Isqrt (#F) else #F;
   d := ClassicalCentreOrder[type](n, q);
   xi := PrimitiveElement (F);
   z := ScalarMatrix (F, n, xi);
   z := Generic (G) ! (z^((#F - 1) div d));
   Z := sub<Generic (G) | z>;

   C := ClassicalCentraliser (G, g);
   if IsTrivial (Z) then return C; end if;
   o := #Z;
   D := Divisors (o);
   for i in [1..#D - 1] do
      f, c := ClassicalIsConjugate (G, g, g * z^D[i]);
      if f then return sub<Generic (G) | C, c>; end if;
   end for;
   return C;
end intrinsic;

intrinsic ProjectiveClassicalIsConjugate (G :: GrpMat, g:: GrpMatElt, h :: GrpMatElt) -> BoolElt, GrpMatElt
{if the images of g and h are conjugate in the central quotient of the classical group G, 
 then return true and preimage in G of a conjugating element, else return false}

   ValidTypes := ["SL", "GL", "Sp", "SU", "GU", "Omega+", "Omega-", "Omega",
                  "SO+", "SO-", "SO", "GO+", "GO-", "GO"];
   f, type := ClassicalGroupType (G);
   require type in ValidTypes: "Function does not apply to classical group of type", type; 

   n := Degree (G); F := BaseRing (G);
   q := type in {"GU", "SU"} select Isqrt (#F) else #F;
   d := ClassicalCentreOrder[type](n, q);
   xi := PrimitiveElement (F);
   z := ScalarMatrix (F, n, xi);
   z := Generic (G) ! (z^((#F - 1) div d));
   Z := sub<Generic (G) | z>;

   if IsTrivial (Z) then 
      f, c := ClassicalIsConjugate (G, g, h);
      if f then return f, c; else return f, _; end if;
   end if;

   o := #Z;
   for i in [0..o-1] do
      f, c := ClassicalIsConjugate (G, g, h * z^i);
      if f then return f, c; end if;
   end for;
   return false, _;
end intrinsic;

//------------------------------------------------------------------------------

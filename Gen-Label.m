freeze;

import "unipotent/ClassMap.m": UnipotentLabel;
import "semisimple/form.m": IndicateType, ConjugatePolynomial;
import "fixed-ss.m": ChangeClassLabel;
import "size.m": GroupType, MyIsIn;
import "Gen-IsConjugate.m": GenIsConjugate; 
import "translate/translateSp.m": tagToNameSp;
import "translate/translateU.m": tagToNameGU, tagToNameSU;
import "translate/translateO.m": tagToNameO, tagToNameSO;

// G is natural copy of classical group
// determine matrix to conjugate G to standard copy 
DetermineTransformMatrix := function (G)
    f, type := ClassicalGroupType (G);
    if type in {"SL", "GL"} then
       CB := G.0;
    elif type in {"SU", "GU"} then
       flag, form := UnitaryForm (G);
       CB := TransformForm (form, "unitary");
    elif type in {"GO+", "GO-", "SO+", "SO-", "Omega+", "Omega-", 
                   "GO", "SO", "Omega"} then
       F := BaseRing (G);
       if IsEven (#F) then 
          flag, form, ind := QuadraticForm (G);
       else 
          flag, ind, form := OrthogonalForm (G);
       end if;
       CB := TransformForm (form, ind);
    elif type in {"Sp"} then
       flag, form := SymplecticForm (G);
       CB := TransformForm (form, "symplectic");
    end if;
    G`TransformCB := CB;
    return CB;
end function;

TransformMatrix := function (G)
   if assigned G`TransformCB then
      return G`TransformCB;
   else
      return DetermineTransformMatrix (G);
   end if;
end function;

StandardGroup := function (type, n, q: Projective := false)
   case type:
      when "GO+":
         G := GOPlus(n, q); G`ClassicalType := "GO+";
         if Projective then P := PGOPlus (n, q); end if;
      when "GO":
         G := GO (n, q); G`ClassicalType := "GO";
         if Projective then P := PGO (n, q); end if;
      when "GO-":
         G := GOMinus(n, q); G`ClassicalType := "GO-";
         if Projective then P := PGOMinus (n, q); end if;
      when "SO+":
         G := SOPlus(n, q); G`ClassicalType := "SO+";
         if Projective then P := PSOPlus (n, q); end if;
      when "SO":
         G := SO(n, q); G`ClassicalType := "SO";
         if Projective then P := PSO (n, q); end if;
      when "SO-":
         G := SOMinus(n, q); G`ClassicalType := "SO-";
         if Projective then P := PSOMinus (n, q); end if;
      when "Omega+":
         G := OmegaPlus(n, q); G`ClassicalType := "Omega+";
         if Projective then P := POmegaPlus (n, q); end if;
      when "Omega":
         G := Omega(n, q); G`ClassicalType := "Omega";
         if Projective then P := POmega (n, q); end if;
      when "Omega-":
         G := OmegaMinus(n, q); G`ClassicalType := "Omega-";
         if Projective then P := POmegaMinus (n, q); end if;
      when "Sp":
         G := Sp(n, q); G`ClassicalType := "Sp";
         if Projective then P := PSp (n, q); end if;
      when "GU":
         G := GU(n, q); G`ClassicalType := "GU";
         if Projective then P := PGU (n, q); end if;
      when "SU":
         G := SU(n, q); G`ClassicalType := "SU";
         if Projective then P := PSU (n, q); end if;
      when "SL":
         G := SL(n, q); G`ClassicalType := "SL";
         if Projective then P := PSL (n, q); end if;
      when "GL":
         G := GL(n, q); G`ClassicalType := "GL";
         if Projective then P := PGL (n, q); end if;
   end case;
   if Projective then return G, P; else return G, _; end if;
end function;

// turn the matrix of an orthogonal form into an upper triangular matrix
// This is necessary because TransformForm (B, "orthogonalminus") fails if 
// B = Matrix (GF (2), 2, 2, [1, 0, 1, 1])
AdaptForm := function (A)
   n := Nrows (A);
   for i in [1..n] do
      for j in [i+1..n] do
         A[i, j] +:= A[j, i];
         A[j, i] := 0;
      end for;
   end for;
   return A;
end function;

// for even char, does GO-class split into two classes in Omega+? 
CaseSplits := function (L)
   return #L gt 0 and #L[1] gt 0 and forall{x: x in L[1] | IsEven (x)} 
      and forall{i: i in [2..4] | #L[i] eq 0}; 
end function;

/* 
Consider first labels for Sp in odd characteristic. 
The label corresponding to a single elementary divisor f is
<type, f, {* <d1, t1>, <d2, t2>, <d3, t3>, ... *}>
where type = 0, 1, 2 according to the type of "f".
-- type = 0 for f=f* & deg(f) = 1;  
-- type = 1 for f=gg* (g ne g*, g el. div.);  
-- type = 2 for f=f* & deg(f) > 1.

If type = 0 (f = f* & deg(f) = 1 so f = t+1 or t-1), then for every 
Jordan block of even dimension J_{2n} there is only one conjugacy class 
in Sp with Jordan form J_{2n}, but there are two classes for Jordan blocks 
of odd dimension. So d1, d2, d3,... are the dimensions of the Jordan blocks, 
and we record <d_i, t_i>, where t_i = 0 if d_i is even, and t_i = 1 or a 
primitive element for GF(q) if d_i is odd (according to the type of Jordan block).

If type = 1 or 2, then for uniformity the third element of the label remains 
{* <d1, 1>, <d2, 1>, <d3, 1>, ... *} since in GL and GU there is only one 
class for each Jordan block. 

A label for a class is a multiset {* <type, f, L>: f elementary divisor of x *}.

For orthogonal groups in odd characteristic, the same conventions apply -- 
but we must swap the roles of odd and even dimensional Jordan blocks.

For symplectic and orthogonal in even char L = {v1, v2, v3, v4 }, where 
v1, v2, v3, v4 record the dimensions of the blocks W, V, W_alpha, V_alpha 
-- see Gonshaw-Liebeck-O'Brien paper for their definitions.

For type 1 and 2, we simply designate all blocks to have type W.

For unitary in every char, L = Multiset of dimensions of Jordan blocks.

If type is a Special or Omega group, the label is <L1, symbol>, where L1 is the 
label in the isometry group, and symbol identifies the class in SO/Omega/SU.
For SO and Omega, the symbols are "ns" (= not split), "id", "t", "s", "st" [see GLO'B]. 
For SU, it assumes integer values from 0 to d-1, where d is the number of 
SU-classes which are mutually conjugate in GU.
*/

GenericLabel := function (type, x: X := [], ClassLabels := []) 
   F := BaseRing (x);
   pr := PrimitiveElement (F);
   p := Characteristic (F);
   n := Nrows (x);
   e := type in {"SU", "GU"} select Degree (F) div 2 else 0;
   q := type in {"SU", "GU"} select p^e else #F;
   LabelNumber := 0;

   //conjugate transpose matrix
   Star := func<M: exp := e | Transpose (FrobeniusImage (M, exp))>;

   //conjugate polynomial
   ConjPol := ConjugatePolynomial (e ne 0);

   a, b, c := JordanForm (x);
   special := false;
   omega := false;

   if type eq "SO+" and IsEven (p) then type := "GO+"; end if;
   if type eq "SO-" and IsEven (p) then type := "GO-"; end if;

   if type in {"GO+", "SO+", "Omega+"} then
      B := IsOdd (q) select StandardSymmetricForm (n, F: Variant := "Default") else 
                            StandardQuadraticForm (n, F: Variant := "Default");
   elif type in {"GO", "SO", "Omega"} then
      B := StandardSymmetricForm (n, F: Variant := "Default"); 
   elif type in {"GO-", "SO-", "Omega-"} then
      B := IsOdd (q) select StandardSymmetricForm (n, F: Minus, Variant := "Default") else 
                            StandardQuadraticForm (n, F: Minus, Variant := "Default");
   elif type eq "Sp" then
      B := StandardAlternatingForm (n, F);
      TypeForTF := "symplectic";
   elif type in {"GU", "SU"} then
      B := StandardHermitianForm (n, F);
      TypeForTF := "unitary";
   end if;

   if type notin {"SU", "GU", "Sp"} then
      if (q mod 4) eq 1 then
         tf2p := F!1; tf2m := pr;
      else
         tf2p := pr; tf2m := F!1;
      end if;
   end if;

   A := b*B*Star (b);   // A = form preserved by JordanForm (x)

   if type in {"SO+", "SO", "SO-", "SU", "Omega", "Omega+", "Omega-"} then
      special := true;
      if type in {"Omega+", "Omega", "Omega-"} then
         omega := true;
         // does the orthogonal class split into 2 classes in Omega (only even char)?
         SplitsOmega2 := false;               
         if IsEven (p) then special := false; end if;
      end if;
   end if;

   L := [];
   Done := {};        // if f ne f*, we put ff* as elementary divisor

   pos := 1;
   indexinc := 1;
   while indexinc le #c do
      f := c[indexinc][1];
      deg := Degree (f);
      if deg eq 1 and f eq ConjPol (f) then
         dim := 0;
         while indexinc le #c and c[indexinc][1] eq f do
            dim +:= deg*c[indexinc][2];
            indexinc +:= 1;
         end while;
         FormF := Submatrix (A, pos, pos, dim, dim);
         ElemF := GL(dim, F)!(-ConstantCoefficient (f)^-1 * Submatrix (a, pos, pos, dim, dim));
         if type notin {"SU", "GU", "Sp"} then
            TypeForTF := IndicateType (FormF);
            if IsEven (q) then
               FormF := AdaptForm (FormF);
            end if;
         end if;
         m := TransformForm (FormF, TypeForTF);
         case TypeForTF:
            when "unitary":
               l := UnipotentLabel (GU(dim, q), m^-1*ElemF*m: type := type);
               if special then l := l[1]; end if;
     
            when "orthogonalplus":
               if dim eq 2 then
                  if IsOdd (q) then
                     l := {* <1, F!1>, <1, tf2p> *};
                  elif ElemF[1, 2] eq 0 then  // if there are 2 Jordan blocks of dimension 1
                     l := <[1], [Integers ()|], [Integers ()|], [Integers ()|], 1>;
                  else
                     l := <[Integers ()|], [1], [Integers ()|], [Integers ()|], 1>;
                  end if;
               else
                  if IsOdd (q) then 
                     l := UnipotentLabel (GOPlus(dim, q), m^-1*ElemF*m: type := "GO+");
                     l := l[1];
                  else
                     if omega then 
                        l := UnipotentLabel (OmegaPlus(dim, q), m^-1*ElemF*m: type := "Omega+");
                     else
                        l := UnipotentLabel (GOPlus(dim, q), m^-1*ElemF*m: type := "GO+");
                     end if;
                     SplitsOmega2 := CaseSplits (l);
                  end if;
               end if;

            when "orthogonal":
               if dim eq 1 then
                  tsq := q mod 8 in {1, 7} select F!1 else pr;
                  l := {* <1, tsq> *};
               else
                  l := UnipotentLabel (GO(dim, q), m^-1*ElemF*m: type := "GO");
                  if IsOdd (q) then l := l[1]; end if;
               end if;
               if IsEven (n) and not IsSquare (Determinant (FormF)) then 
                  l := ChangeClassLabel (l, F, pr); 
               end if;

            when "orthogonalminus":
               if dim eq 2 then
                  if IsOdd (q) then
                     l := {* <1, F!1>, <1, tf2m> *};
                  elif ElemF[1, 2] eq 0 then      // i.e. if there are 2 Jordan blocks of dimension 1
                     l := <[Integers ()|], [Integers ()|], [1], [Integers ()|], 1>;
                  else
                     l := <[Integers ()|], [Integers ()|], [Integers ()|], [1], 1>;
                  end if;
               else
                  if IsOdd (q) then 
                     l := UnipotentLabel (GOMinus(dim, q), m^-1*ElemF*m: type := "GO-");
                     l := l[1];
                  else
                     if omega then 
                        l := UnipotentLabel (OmegaMinus(dim, q), m^-1*ElemF*m: type := "Omega-");
                     else
                        l := UnipotentLabel (GOMinus(dim, q), m^-1*ElemF*m: type := "GO-");
                     end if;
                     SplitsOmega2 := CaseSplits (l);
                  end if;
               end if;

            when "symplectic":
               l := UnipotentLabel (Sp(dim, q), m^-1*ElemF*m: type := type);

         end case;
         pos +:= dim;
         Append (~L, <0, f, l>);
      else
         // here I just use the Jordan block structure
         l := [];
         dim := 0;  // need this only in orthogonal case, odd dimension
         while indexinc le #c and c[indexinc][1] eq f do
            if type notin {"GU", "SU"} and IsOdd (q) then
               newone := <c[indexinc][2], F!1>;
               dim +:= deg*c[indexinc][2];
            else
               newone := c[indexinc][2];
            end if;
            Append (~l, newone);
            pos +:= deg*c[indexinc][2];
            indexinc +:= 1;
         end while;
         if type notin {"GU", "SU"} and IsEven (q) then
            l := <Sort (l), [Integers ()|], [Integers ()|], [Integers ()|], 1>;
         else
            l := Multiset (l);
         end if;
         cp_f := ConjPol (f); 
         if f ne cp_f then 
            if cp_f in Done then
               Append (~L, <1, f*cp_f, l>);
               // the form preserved by f has non-square determinant
            else
               Include (~Done, f);
            end if;
         else
            Append (~L, <2, f, l>);
            if type in {"GO", "SO", "Omega"} then
               mult := &+[r[1]: r in l];
               if IsOdd (mult) xor (q mod 4 eq 3 and IsOdd (dim div 2)) then 
               end if;  // the form preserved by f has non-square determinant
            end if;
         end if;
      end if;
   end while;

   if omega and SplitsOmega2 then
      i := [j: j in [1..#L] | L[j][1] eq 0][1];
      L_omega := L;
      L_omega[i][3][5] *:= -1;
      L_omega := Multiset (L_omega);
   end if;
   L := Multiset (L);

   if special or omega then
      Gr := StandardGroup (type, n, q); 
      Arr := [i: i in [1..#ClassLabels] | ClassLabels[i][1] eq L];
      if omega and SplitsOmega2 then
         Arr cat:= [i: i in [1..#ClassLabels] | ClassLabels[i][1] eq L_omega];
      end if;
      if #Arr eq 1 then
         if type eq "SU" then
            L := <L, 0>;
         else
            L := <L, "ns">;
         end if;
         LabelNumber := Arr[1];
      else
         for i in Arr do
            if GenIsConjugate (Gr, x, X[i][3]: Checks := false) then
               L := ClassLabels[i];
               LabelNumber := i;
               break i;
            end if;
         end for;
      end if;
   end if;
   return L, LabelNumber;   
end function;

intrinsic IsometryGroupClassLabel (type :: MonStgElt, g:: GrpMatElt) -> {* *}
{return class label for element g of corresponding standard isometry group G 
 determined by type; the labels of distinct elements of G agree 
 if and only if they are conjugate in G}

   types := ["GU", "Sp", "O+", "O-", "GO+", "GO-", "O", "GO"];
   require type in types: "type must be one ",types; 

   if type eq "O"  then type := "GO"; end if;
   if type eq "O+" then type := "GO+"; end if;
   if type eq "O-" then type := "GO-"; end if;

   d := Nrows (g); F := BaseRing (g);  
   if type eq "GU" then
      flag, q := IsSquare(#F);
      require flag: "Field must be of even degree";
   else
      q := #F;
   end if;
   G := StandardGroup (type, d, q);
   require g in G: "Element not in standard isometry group";

   if IsOdd(q) or type eq "GU" then
     if type in {"GO","GO+","GO-"} then tp := "O"; else tp := type; end if;
     mu := case< tp |
        "Sp" : InternalConjugacyInvariantSp(g),
        "GU" : InternalConjugacyInvariantGU(g),
        "O"  : type eq "GO-" select InternalConjugacyInvariantO(g: Minus :=true) 
                               else InternalConjugacyInvariantO(g),
        default : false >;
     trans := case< tp |
        "Sp" : tagToNameSp,
        "O"  : tagToNameO,
        "GU" : tagToNameGU,
     default : false >;
     label := trans(mu);
   else
      label := GenericLabel (type, g);
   end if;
   return label;
end intrinsic;

// C is sequence of classes and L is sequence of labels; 
//  return index of conjugacy class containing element g
MyClassIndex := function (G, g, C, L: type := false)
   if Generic (G) cmpne Generic (Parent (g)) then
      error "Element not in group";
   end if;
   l, n := GenericLabel (type, g: X := C, ClassLabels := L);
   if n eq 0 then n := Position (L, l); end if;
   return n;
end function;

intrinsic ClassicalClassMap (G:: GrpMat, C:: SeqEnum, L:: SetIndx: type := false) -> Map 
{C and L are output of ClassicalClasses, where C is sequence of classes and 
L is list of corresponding labels; return class map for G}

   if assigned G`Classes then
     require G`Classes eq C : "Supplied classes are inconsistent with stored classes";
   else
     require Generic (G) cmpeq Generic (Parent (C[1][3])): "Classes do not belong to G";
     // require forall{c : c in C | c[3] in G}: "Not all supplied classes belong to G";
     require forall{c : c in C | MyIsIn (G, c[3])}: "Not all supplied classes belong to G";
     require &+[c[2] : c in C] eq #G: "Wrong number of supplied classes";
     require #C eq #L: "Number of classes differs from number of labels";
     G`Classes := C;
     G`Labels_A := L;
   end if;

   if IsTrivial (G) then return ClassMap (G); end if;

   if type cmpne false then 
      if type in {"GO",  "O"} then type := "GO"; end if;
      if type in {"GO+", "O+"} then type := "GO+"; end if;
      if type in {"GO-", "O-"} then type := "GO-"; end if;
   end if;

   ValidTypes := {"Sp", "SU", "GU", "Omega+", "Omega-", "Omega", 
                  "SO+", "SO-", "SO", "GO+", "GO-", "GO"};

   if assigned G`ClassicalType then
      if type cmpne false then
         require type cmpeq G`ClassicalType: "supplied type is incorrect";
      else
         type := G`ClassicalType;
      end if;
   elif type cmpeq false then 
      flag, type := GroupType (G);
      require flag: "For this case, you must supply type";
   end if;

   require type in ValidTypes: "Type must be one of ", ValidTypes;
   G`ClassicalType := type;

   if Degree (G) eq 2 and IsIrreducible (G) eq false then 
      return ClassMap (G);
   end if;

   CB := TransformMatrix (G);
   if CB ne CB^0 then
      D := [<C[i][1], C[i][2], C[i][3]^CB>: i in [1..#C]];
      return map<G -> [1..#C] | g :-> MyClassIndex (G, g^CB, D, L : type := G`ClassicalType)>; 
   else 
      return map<G -> [1..#C] | g :-> MyClassIndex (G, g, C, L : type := G`ClassicalType)>; 
   end if;
end intrinsic;

intrinsic ClassicalClassMap (G :: GrpMat) -> Map
{The class map for the classical group G}
   
   if IsTrivial (G) then return ClassMap (G); end if;

   d := Degree (G); F := BaseRing (G);

   if not (d eq 2 and #F le 4) then 
      flag, tp := ClassicalGroupType (G);
      ValidTypes := {"SL", "GL", "Sp", "SU", "GU", "Omega+", "Omega-", "Omega",
                  "SO+", "SO-", "SO", "GO+", "GO-", "GO"};
      require flag and tp in ValidTypes: "Type of group must be one of ", ValidTypes;
      if tp cmpeq "GO" and IsEven (#F) then 
         error "Function does not apply to this case";
      end if;
   end if;

   if not assigned G`Classes then
     _ := Classes(G);
   end if;

   C := G`Classes;
   if not assigned G`Labels_A then
     if assigned G`Labels_S then
       if tp eq "Sp" then
         fn := tagToNameSp;
       elif tp in {"GO","GO+","GO-"} then
         fn := tagToNameO;
       elif tp in {"SO", "SO+", "SO-"} then
         fn := tagToNameSO;
       elif tp eq "GU" then
         fn := tagToNameGU;
       elif tp eq "SU" then
         fn := tagToNameSU;
       else
         error "Labels not available for this group of type", tp;
       end if;
       G`Labels_A := {@ fn(mu) : mu in G`Labels_S @};
     else
       vprint Classes: "No labels, so using the standard ClassMap";
       return ClassMap (G);
     end if;
   end if;
   L := G`Labels_A;

   if Degree (G) eq 2 and IsIrreducible (G) eq false then 
      return ClassMap (G);
   end if;
 
   CB := TransformMatrix (G);
   if CB ne CB^0 then
      D := [<C[i][1], C[i][2], C[i][3]^CB>: i in [1..#C]];
      return map<G -> [1..#C] | g :-> MyClassIndex (G, g^CB, D, L : type := G`ClassicalType)>; 
   else 
      return map<G -> [1..#C] | g :-> MyClassIndex (G, g, C, L : type := G`ClassicalType)>; 
   end if;
end intrinsic;

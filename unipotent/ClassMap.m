freeze;

import "central/even-sp.m": WeightsToLabel;
import "../size.m": GroupType;
import "conjugation/is-conjugate.m": MyUnipotentClassLabel;

// label in format returned by UnipotentClasses 

UnipotentLabel := function (G, g: type := false) 
   if type cmpeq false then 
      flag, type := GroupType (G);
   end if;

   F := BaseRing (G);
   label := MyUnipotentClassLabel (G, g: type := type);

   if type eq "GL" then 
      label := &cat[[x[1]: i in [1..x[2]]]: x in label];
      label := Multiset (label);

   elif type eq "SL" then 
      two := label[2];
      label := label[1];
      label := <Multiset (label), two>;

   elif type eq "GU" then 
      label := Multiset (label);

   elif type eq "SU" then 
      two := label[2];
      label := Multiset (label[1]);
      label := <label, two>;

   elif type eq "Sp" then
      if IsEven (#F) then 
         label := WeightsToLabel (label);
      else
         label := Multiset (label);
      end if;

   elif IsEven (#F) then
      // all orthogonal cases in even char 
      l := label;
      label := WeightsToLabel (l[1]); label[#label] := l[2];

   elif IsOdd (#F) and type in {"GO+", "GO-", "GO"} then 
      label := Multiset (label);
      label := <label, "ns">;

   else  
      // all remaining orthogonal cases in odd char 
      two := label[2];
      label := Multiset (label[1]);
      label := <label, two>;
   end if;

   return label;
end function;

intrinsic UnipotentClassLabel (G :: GrpMat, g:: GrpMatElt ) -> Any 
{return unipotent conjugacy class label for unipotent element g of classical G;
 if two elements of G have different labels, then they are not conjugate; two elements 
 of an isometry group G are conjugate in G if and only if they have same label}

   require IsUnipotent (g): "Element must be unipotent";
   require Generic (G) cmpeq Generic (Parent (g)): "Element is not in group";

   // what groups do we accept?
   flag, type := GroupType (G);
   require flag: "Input group must be classical";
   Valid := {"SL", "GL", "Sp", "SU", "GU", "Omega+", "Omega-", "Omega",
             "SO+", "SO-", "SO", "GO+", "GO-", "GO", "O+", "O-", "O"};
   require type in Valid: "Classical group type is not valid, must be one of ", Valid;

   label := UnipotentLabel (G, g);
   return label;
end intrinsic;

// C is sequence of classes and L is sequence of labels; 
// return index of conjugacy class containing element g

UnipotentClassIndex := function (G, g, U, L, type, F) 
   // two cases coincide 
   if type in {"GL", "SL"} and #F eq 2 then 
      type := Type (Rep (L)) cmpeq Tup select "SL" else "GL"; 
      G`ClassicalType := type;
   end if;

   // do we need label relative to isom group? or actual G?
   label := UnipotentLabel (G, g);

   if type eq "SU" then 
         two := label[2];
         label := label[1];
         index := [i: i in [1..#L] | L[i][1] eq label];
         if #index gt 1 then
            found := false;
            // "SU must decide conjugacy";
            // "index is ", #index;
            for j in index do
               if InternalUnipotentIsConjugate (G, g, U[j][3]) then
                  two := L[j][2];
                  found := true;
                  break j;
               end if;
            end for;
            assert found;
          end if;
          label := <label, two>;

   elif type in {"SO+", "SO-", "SO", "Omega+", "Omega-", "Omega"} and IsOdd (#F) then 
      // all remaining orthogonal cases in odd char 
      two := label[2];
      label := label[1];

      if two ne "ns" then 
         index := [i: i in [1..#L] | L[i][1] eq label];
         assert #index gt 1;
         found := false;
         // "Omega / SO here must decide conjugacy", type;
         // "index is ", #index;
         for j in index do
            if InternalUnipotentIsConjugate (G, g, U[j][3]) then
               two := L[j][2];
               found := true;
               break j;
            end if;
         end for;
         assert found;
      end if;
      label := <label, two>;
   end if;

   return Position (L, label);
end function;

intrinsic UnipotentClassMap (G:: GrpMat, U:: SeqEnum, L:: SetIndx: type := false) -> Map 
{U and L are output of UnipotentClasses, where U is sequence of unipotent
class representative and L is the corresponding list of labels; return 
unipotent class map for G}

   require IsIrreducible (G): "Input group must be irreducible";
   ValidTypes := {"GL", "SL", "Sp", "SU", "GU", "Omega+", "Omega-", "Omega", "O", "O+", "O-",
                   "SO+", "SO-", "SO", "GO+", "GO-", "GO"};

   require forall{x : x in U | IsUnipotent (x[3])}: "Must supply unipotent classes";

   require Generic (G) cmpeq Generic (Parent (U[1][3])): "classes do not belong to G";
   require forall{u : u in U | u[3] in G}: "not all supplied classes belong to G";

   if Degree (G) eq 2 and #U eq 1 then 
      return map<Generic (G) -> [1] | g :-> 1>;
   end if;

   F := BaseRing (G);

   if Degree (G) eq 2 then 
      require type cmpne false: "For this (small) case, you must supply type"; 
      require type in ValidTypes: "Type must be one of ", ValidTypes;
      if type eq "O" then type := "GO"; 
      elif type eq "O+" then type := "GO+"; 
      elif type eq "O-" then type := "GO+"; end if;
      G`ClassicalType := type;
   else 
      flag, type := GroupType (G);
      require flag and type in ValidTypes: 
         "Input group must be one of these types", ValidTypes;
   end if;

   return map<Generic (G) -> [1..#U] | g :-> UnipotentClassIndex (G, g, U, L, type, F)>;
end intrinsic;

freeze;

import "fixed-ss.m": AllUnipotentElementsOfS;
import "semisimple/Unitary/GUClasses.m": SSClassesGU;
import "semisimple/Symplectic/SpClasses.m": SSClassesSp;
import "semisimple/Orthogonal/GOClasses.m": GOClasses;
import "semisimple/Orthogonal/GOpmClasses.m": GOpmClasses;
import "semisimple/card.m": CardinalityOfClassicalGroup;
import "Gen-Label.m": StandardGroup;
import "translate/translateSp.m": tagToNameSp;
import "translate/translateU.m": tagToNameGU, tagToNameSU;
import "translate/translateO.m": tagToNameO, tagToNameSO;

// data about unipotent classes are computed just once and 
// passed as argument to AllUnipotentElementsOfS
UCComputation := function (type, dim, q0: Rewrite := true)
   UC := <>;
   UCRepr := <>;
   UCForm := <>;
   UCT := <>;
   UCL := <>;
   if type in {"Omega", "Omega+", "Omega-"} and IsOdd (q0) then
      Rewrite := false;
   end if;
   case type:
      when "GU", "SU":
         for j in [1..dim] do
            Y, T, _, Repr, Form := UnipotentClasses ("GU", j, q0: Rewrite := Rewrite);
            Append (~UC, Y);
            Append (~UCRepr, Repr);
            Append (~UCForm, Form);
            Append (~UCT, T);
            Append (~UCL, T);
         end for;
      when "Sp":
         for j in [2..dim by 2] do
            Y, T, L, Repr, Form := UnipotentClasses ("Sp", j, q0: Rewrite := Rewrite);
            if IsOdd (q0) then temp := L; L := T; T := temp; end if;
            Append (~UC, Y);
            Append (~UCRepr, Repr);
            Append (~UCForm, Form);
            Append (~UCT, T);
            if IsEven (q0) then Append (~UCL, T); else Append (~UCL, L); end if;
         end for;
      when "O", "Omega":
         for j in [1..dim by 2] do
            Y, T, L, Repr, Form := UnipotentClasses (type, j, q0: Rewrite := Rewrite);
            if IsOdd (q0) then temp := L; L := T; T := temp; end if;
            Append (~UC, Y);
            Append (~UCRepr, Repr);
            Append (~UCForm, Form);
            Append (~UCT, T);
            if IsEven (q0) then Append (~UCL, T); else Append (~UCL, L); end if;
         end for;
      when "O+", "Omega+", "O-", "Omega-":
         for j in [2..dim by 2] do
            Y, T, L, Repr, Form := UnipotentClasses (type, j, q0: Rewrite := Rewrite);
            if IsOdd (q0) then temp := L; L := T; T := temp; end if;
            Append (~UC, Y);
            Append (~UCRepr, Repr);
            Append (~UCForm, Form);
            Append (~UCT, T);
            if IsEven (q0) then Append (~UCL, T); else Append (~UCL, L); end if;
         end for;
   end case;

   return UC, UCRepr, UCForm, UCT, UCL;
end function;

// cardinality of group of isometries
IsometryGroupCardinality := function (type, d, q) 
   case type:
      when "Sp":
         CardOfG := CardinalityOfClassicalGroup ("Sp", d, q);
      when "GU", "SU":
         CardOfG := CardinalityOfClassicalGroup ("GU", d, q);
      when "O+", "GO+", "SO+", "Omega+":
         CardOfG := CardinalityOfClassicalGroup ("GO+", d, q);
      when "O", "GO", "SO", "Omega":
         CardOfG := CardinalityOfClassicalGroup ("GO", d, q);
      when "O-", "GO-", "SO-", "Omega-":
         CardOfG := CardinalityOfClassicalGroup ("GO-", d, q);
   end case;
   if IsEven (q) and type in {"Omega+", "Omega-"} then 
      CardOfG /:= SequenceToFactorization ([<2, 1>]); 
   end if;
   return CardOfG;
end function;

// returns list of representatives for conjugacy classes in symplectic, 
// orthogonal and unitary groups (in the standard MAGMA copy)

AllClasses := function (type, d, q: SameSSPart := false)

   X := [];
   Xlabel := [];
   CardOfG := IsometryGroupCardinality (type, d, q);

   if type in {"GU", "SU"} then
      L := SSClassesGU (d, q: OnlyPolynomials);
      UC, UCRepr, UCForm, UCT, UCL := UCComputation ("GU", d, q: Rewrite := SameSSPart);
      DataArray := <UC, UCRepr, UCForm, UCT, UCL>;
      for i in [1..#L] do
         y, ylabel := AllUnipotentElementsOfS (type, L[i]: SameSSPart := SameSSPart, 
                         DataArray := DataArray, CardOfG := CardOfG);
         for j in [1..#y] do
            Append (~X, y[j]);
            Append (~Xlabel, ylabel[j]);
         end for;
      end for;
   elif type in {"GO", "O", "SO", "Omega"} then
      L := GOClasses (d, q: OnlyPolynomials);
      VarRewrite := SameSSPart;
      if type eq "Omega" then VarRewrite := false; end if;
      UCp, UCpRepr, UCpForm, UCpT, UCpL := UCComputation ("O+", d, q: Rewrite := VarRewrite);
      UCm, UCmRepr, UCmForm, UCmT, UCmL := UCComputation ("O-", d, q: Rewrite := VarRewrite);
      UC, UCRepr, UCForm, UCT, UCL := UCComputation ("O", d, q: Rewrite := VarRewrite);
      DataArray := <UCp, UCpRepr, UCpForm, UCpT, UCpL, UCm, UCmRepr, UCmForm, UCmT, UCmL, 
                    UC, UCRepr, UCForm, UCT, UCL>;
      for i in [1..#L] do
         y, ylabel := AllUnipotentElementsOfS (type, L[i]: SameSSPart := SameSSPart, 
                         DataArray := DataArray, CardOfG := CardOfG);
         for j in [1..#y]  do
            Append (~X, y[j]);
            Append (~Xlabel, ylabel[j]);
         end for;
      end for;
   elif type in {"O+", "GO+", "SO+", "Omega+"} and IsOdd (q) then
      L := GOpmClasses (d, q, "plus": OnlyPolynomials);
      VarRewrite := SameSSPart;
      if type eq "Omega+" then VarRewrite := false; end if;
      UCp, UCpRepr, UCpForm, UCpT, UCpL := UCComputation ("O+", d, q: Rewrite := VarRewrite);
      UCm, UCmRepr, UCmForm, UCmT, UCmL := UCComputation ("O-", d, q: Rewrite := VarRewrite);
      if type in {"GO+", "O+"} then
         UC, UCRepr, UCForm, UCT, UCL := UCComputation ("O", d, q: Rewrite := VarRewrite);
         DataArray := <UCp, UCpRepr, UCpForm, UCpT, UCpL, UCm, UCmRepr, UCmForm, UCmT, UCmL, 
                       UC, UCRepr, UCForm, UCT, UCL>;
      else
         DataArray := <UCp, UCpRepr, UCpForm, UCpT, UCpL, UCm, UCmRepr, UCmForm, UCmT, UCmL>;
      end if;

      for i in [1..#L] do
         y, ylabel := AllUnipotentElementsOfS (type, L[i]: SameSSPart := SameSSPart, 
                         DataArray := DataArray, CardOfG := CardOfG);
         for j in [1..#y]  do
            Append (~X, y[j]);
            Append (~Xlabel, ylabel[j]);
         end for;
      end for;
   elif type in {"O-", "GO-", "SO-", "Omega-"} and IsOdd (q) then
      L := GOpmClasses (d, q, "minus": OnlyPolynomials);
      VarRewrite := SameSSPart;
      if type eq "Omega-" then VarRewrite := false; end if;
      UCp, UCpRepr, UCpForm, UCpT, UCpL := UCComputation ("O+", d, q: Rewrite := VarRewrite);
      UCm, UCmRepr, UCmForm, UCmT, UCmL := UCComputation ("O-", d, q: Rewrite := VarRewrite);
      if type in {"GO-", "O-"} then
         UC, UCRepr, UCForm, UCT, UCL := UCComputation ("O", d, q: Rewrite := VarRewrite);
         DataArray := <UCp, UCpRepr, UCpForm, UCpT, UCpL, UCm, UCmRepr, UCmForm, UCmT, UCmL, 
                       UC, UCRepr, UCForm, UCT, UCL >;
      else
         DataArray := <UCp, UCpRepr, UCpForm, UCpT, UCpL, UCm, UCmRepr, UCmForm, UCmT, UCmL>;
      end if;

      for i in [1..#L] do
         y, ylabel := AllUnipotentElementsOfS (type, L[i]: SameSSPart := SameSSPart, 
                         DataArray := DataArray, CardOfG := CardOfG);

         for j in [1..#y] do
            Append (~X, y[j]);
            Append (~Xlabel, ylabel[j]);
         end for;
      end for;
   elif type eq "Sp" then
      L := SSClassesSp (d, q: OnlyPolynomials);
      UC, UCRepr, UCForm, UCT, UCL := UCComputation ("Sp", d, q);
      DataArray := <UC, UCRepr, UCForm, UCT, UCL>;
      // UC := <UnipotentClasses ("Sp", s, q: Rewrite := SameSSPart): s in [2..d by 2]>;
      for i in [1..#L] do
         y, ylabel := AllUnipotentElementsOfS (type, L[i]: SameSSPart := SameSSPart, 
                         DataArray := DataArray, CardOfG := CardOfG);
         for j in [1..#y] do
            Append (~X, y[j]);
            Append (~Xlabel, ylabel[j]);
         end for;
      end for;
   elif type in {"O+", "GO+", "SO+", "Omega+"} and IsEven (q) then
      // the function GOpm2Classes does not support the parameter "OnlyPolynomials", 
      // so L needs to be defined starting by SpClasses, with a little change
      L1 := SSClassesSp (d, q: OnlyPolynomials);
      if type eq "Omega+" then
         UCp, UCpRepr, UCpForm, UCpT, UCpL := UCComputation ("Omega+", d, q: Rewrite := SameSSPart);
         UCm, UCmRepr, UCmForm, UCmT, UCmL := UCComputation ("Omega-", d, q: Rewrite := SameSSPart);
      else
         UCp, UCpRepr, UCpForm, UCpT, UCpL := UCComputation ("O+", d, q: Rewrite := SameSSPart);
         UCm, UCmRepr, UCmForm, UCmT, UCmL := UCComputation ("O-", d, q: Rewrite := SameSSPart);
      end if;
      DataArray := <UCp, UCpRepr, UCpForm, UCpT, UCpL, UCm, UCmRepr, UCmForm, UCmT, UCmL>;

      L := [**];
      for x in L1 do
         sign := GF (2)!0;
         // TIP = There Is PlusMinus (i.e. there is the elementary divisor t+1)
         TIP := false;                   
         for y in x do
            if y[3] eq 0 then
               TIP := true;
            elif y[3] eq 2 then
               sign +:= y[2];
            end if;
         end for;
         if TIP or sign eq 0 then
            Append (~L, [<y[1], y[2]>: y in x]);
         end if;
      end for;
      for i in [1..#L] do
         y, ylabel := AllUnipotentElementsOfS (type, L[i]: SameSSPart := SameSSPart, 
                         DataArray := DataArray, CardOfG := CardOfG);
         for j in [1..#y]  do
            Append (~X, y[j]);
            Append (~Xlabel, ylabel[j]);
         end for;
      end for;
   elif type in {"O-", "GO-", "SO-", "Omega-"} and IsEven (q) then
      L1 := SSClassesSp (d, q: OnlyPolynomials);
      if type eq "Omega-" then
         UCp, UCpRepr, UCpForm, UCpT, UCpL := UCComputation ("Omega+", d, q: Rewrite := SameSSPart);
         UCm, UCmRepr, UCmForm, UCmT, UCmL := UCComputation ("Omega-", d, q: Rewrite := SameSSPart);
      else
         UCp, UCpRepr, UCpForm, UCpT, UCpL := UCComputation ("O+", d, q: Rewrite := SameSSPart);
         UCm, UCmRepr, UCmForm, UCmT, UCmL := UCComputation ("O-", d, q: Rewrite := SameSSPart);
      end if;
      DataArray := <UCp, UCpRepr, UCpForm, UCpT, UCpL, UCm, UCmRepr, UCmForm, UCmT, UCmL>;

      L := [**];
      for x in L1 do
         sign := GF (2)!0;
         // TIP = There Is PlusMinus (i.e. there is the elementary divisor t+1)
         TIP := false;                   
         for y in x do
            if y[3] eq 0 then
               TIP := true;
            elif y[3] eq 2 then
               sign +:= y[2];
            end if;
         end for;
         if TIP or sign eq 1 then
            Append (~L, [<y[1], y[2]>: y in x]);
         end if;
      end for;
      for i in [1..#L] do
         y, ylabel := AllUnipotentElementsOfS (type, L[i]: SameSSPart := SameSSPart, 
                         DataArray := DataArray, CardOfG := CardOfG);
         for j in [1..#y]  do
            Append (~X, y[j]);
            Append (~Xlabel, ylabel[j]);
         end for;
      end for;
   else
      error "Input type is wrong";
   end if;

   // sort classes and labels: increasing order and sizes  
   ParallelSort (~X, ~Xlabel);

   // return labels as indexed set, not sequence 
   return X, {@ x : x in Xlabel @};
end function;

intrinsic ClassicalConjugacyClasses (type:: MonStgElt, d:: RngIntElt,
q:: RngIntElt) -> [], {@ @}
{Conjugacy classes and their class invariants (labels) for the standard 
classical group of supplied type and rank defined over field of given size;
labels are not returned for the general or special linear group} 

   Orthogonal := {"Omega+", "Omega-", "Omega", "O+", "O-", "O", 
                   "SO+", "SO-", "SO", "GO+", "GO-", "GO"};
   ValidTypes := {"SL", "GL", "Sp", "SU", "GU"} join Orthogonal; 

   require type in ValidTypes: "Type must be one of", ValidTypes;
   require d ge 1: "Degree must be positive";
   require IsPrimePower (q): "Invalid field size";

   if type in {"O", "GO", "SO", "Omega"} then 
      if IsEven (q) then
         error "Case of odd dimension and even characteristic not considered";
      end if;
      require IsOdd (d) and d ge 3: "Degree must be odd and at least 3"; 
   elif type in {"Sp"} join Orthogonal diff {"GO", "SO", "Omega", "O"} then 
      require IsEven (d): "Degree must be even"; 
   end if;

   if type eq "GL" then
      G := GL(d, q);
      C := Classes (G);
      return C, _;
   elif type eq "SL" then 
      G := SL(d, q);
      C := Classes (G);
      return C, _;
   else
      return AllClasses (type, d, q);
   end if;
end intrinsic;

intrinsic ClassicalConjugacyClasses (G :: GrpMat) -> [], {@ @}
{Conjugacy classes and their class invariants (labels) for the 
classical group G in its natural representation; if G has order 
at most 100, or it is the general or special linear group, 
then labels are not returned}

   F := BaseRing(G);
   require ISA (Type (F), FldFin): "Base ring is not a finite field";
   d := Degree (G);
   if (IsTrivial (G) or (d eq 2 and #F le 4)) then 
      cc := ConjugacyClasses(G);
      return cc, _; 
   end if;

   flag, tp := ClassicalGroupType (G);
   // allow GL and SL for consistency  
   ValidTypes := {"GL", "SL", "Sp", "SU", "GU", "Omega+", "Omega-", "Omega", "O+", "O-", "O", 
                  "SO+", "SO-", "SO", "GO+", "GO-", "GO"};
   require flag and tp in ValidTypes : "Type of group must be one of ", ValidTypes;

   cc := ConjugacyClasses (G);
   if not assigned G`Labels_A and not assigned G`Labels_S then 
      return cc, _;
   end if;

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
           error "labels not available for this group of type", tp;
        end if;
        G`Labels_A := {@ fn(mu) : mu in G`Labels_S @};
      else
        // error "labels not available for this group of type", tp;
      end if;
   end if;
   L := G`Labels_A;
   return cc, L;
end intrinsic;

// ClassicalClasses has been made a synonym of ClassicalConjugacyClasses in the bind file c.b

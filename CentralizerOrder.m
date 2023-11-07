freeze;

import "unipotent/Centraliser-Order.m": Jordan_Parameters, UnipotentCentraliserOrder;
import "unipotent/Sp-Orthogonal-order.m": SpUnipotentCentraliserOrder, 
   OrthogonalUnipotentCentraliserOrder;
import "Gen-Label.m": GenericLabel;
import "linear/GLCentralizerOrder.m": SLCentralizerOrder, GLCentralizerOrder;
import "size.m": MyIsIn;
import "Gen-Label.m": TransformMatrix;

TurnLabelToJordan := function (L, type)
   Risp := {**};
   if type eq "Sp" then
      for a in L do
         Include (~Risp, a[1]);
         if IsOdd (a[1]) then Include (~Risp, a[1]); end if;
      end for;
   else
      for a in L do
         Include (~Risp, a[1]);
         if IsEven (a[1]) then Include (~Risp, a[1]); end if;
      end for;
   end if;

   return Risp;
end function;

// returns 3 values: |C_GO:C_SO|>1, |C_SO:C_Omega|>1 , values of b_i(-1)^k_i
CheckSplitOmega := function (L, icl)      // icl = IsChangedLabel

   set := [x[1]: x in L | IsOdd (x[1])];
   if #set eq 0 then return false, false, _; end if;
   if #set ne #Set(set) then return true, true, _; end if;
   set := [IsSquare (x[2]*(-1)^((x[1]-1) div 2)): x in L | IsOdd (x[1])];
   if icl and IsEven(&+[x[1]: x in L]) then
      set := [not f: f in set];
   end if;
   if #Set(set) gt 1 then
      return true, true, _;
   else
      return true, false, set[1];
   end if;

end function;


// check whether the label of t \pm 1 with even multiplicity in Omega(odd, q) corresponds or it has changed
// by multiplying the form by a non-square when assembling in file fixed-ss.m
CheckWhetherChanged := function(L, n, q)

   is_square := ((q mod 8 in {1,3} and n mod 4 eq 3) or (q mod 8 in {1,7} and n mod 4 eq 1));  // det (StdForm) is a square or not
   DetForm := 1;    // 1 if square, -1 otherwise

   for l in L do
      if l[1] eq 0 and IsEven(&+[y[1]: y in l[3]]) then
         if not IsSquare( &*([GF(q)!1] cat [ 2*x[2]*(-1)^((x[1]-1) div 2): x in l[3] | IsOdd(x[1]) ]) ) then
            DetForm *:= -1;
         end if;
      elif l[1] eq 1 then
         if q mod 4 eq 3 and IsOdd(Degree(l[2])) and IsOdd(&+[y[1]: y in l[3]]) then
            DetForm *:= -1;
         end if;
      else
         if q mod 4 eq 1 then 
            if IsOdd(&+[y[1]: y in l[3]]) and Degree(l[2]) mod 4 eq 2 then DetForm *:= -1; end if;
         else
            if IsOdd(&+[y[1]: y in l[3]]) and Degree(l[2]) mod 4 eq 0 then DetForm *:= -1; end if;
         end if;
      end if;
   end for;

   if is_square xor DetForm eq 1 then
      return true;
   else
      return false;
   end if;
end function;


// compute the cardinality of the centralizer using only the label L 
// of the element g; the label L is that returned by ClassicalClasses but 
// can be the complete label returned by IsometryGroupClassLabel
MyCentraliserOrder := function (type, g : L := []) 
   special := false;
   is_omega := false;
   F := BaseRing (g);
   q := #F;
   p := Characteristic (F);
   e := Degree (F);
   if type in {"SU", "GU"} then
      q := p^(e div 2);
   end if;
   SpecialCase2 := false;
   SplitSO := false;     // true if |C_GO : C_SO| > 1
   SplitOmega := false;  // true if |C_SO : C_Omega| > 1

   if type in {"Omega", "Omega+", "Omega-"} then
      is_omega := true;
      if IsOdd (p) then special := true; end if;
      ValuesOmegapm := {};
   elif type in {"SO", "SO+", "SO-"} and IsOdd (p) then
      special := true;
   elif type eq "SU" then
      special := true;
   end if;

   if IsEven (q) and type in {"Sp", "GO+", "GO-", "SO+", "SO-", "Omega+", "Omega-"} then
      SpecialCase2 := true;
   end if;

   Card := Factorization (1);
   if L eq [] then
      L1 := GenericLabel (type, g);
   else
      L1 := L;
      if special or is_omega then L1 := L[1]; end if;
   end if;

   if is_omega then
      if type eq "Omega" then
         IsChangedLabel := CheckWhetherChanged(L1, Nrows(g), q);
      else
         IsChangedLabel := false;
      end if;
   end if;

   for l in L1 do
      case l[1]:
         when 0:
            if type eq "Sp" then
               if IsEven (q) then 
                  T := l[3];
                  card := Factorization (SpUnipotentCentraliserOrder (T, [], q));
               else
                  T := TurnLabelToJordan (l[3], "Sp");
                  W := MultisetToSequence (l[3]);
                  card := Factorization (SpUnipotentCentraliserOrder (T, W, q));
               end if;
            elif type in {"SU", "GU"} then
               JF := [a: a in l[3]];
               card := UnipotentCentraliserOrder ("GU", [], IdentityMatrix (F, 2), []: JF := JF);
            else
               if IsEven (q) then 
                  T := l[3];
                  card := Factorization (OrthogonalUnipotentCentraliserOrder ("GO+", T, [], false, q));
               else
                  T := TurnLabelToJordan (l[3], "GO");
                  W := MultisetToSequence (l[3]);
                  if is_omega then
                     v1, v2, v3 := CheckSplitOmega (W, IsChangedLabel);
                     if v1 then
                        SplitSO := true;
                        if v2 then
                           SplitOmega := true;
                        else
                           Include (~ValuesOmegapm, v3);
                        end if;
                     end if;
                  elif special and true in {IsOdd (x[1]): x in l[3]} then
                     SplitSO := true;
                  end if;
                  card := Factorization (OrthogonalUnipotentCentraliserOrder ("GO+", T, W, false, q));
               end if;
            end if;
         when 1:
            if SpecialCase2 then
               JF := l[3][1];
            elif type in {"GU", "SU"} then
               JF := [h: h in l[3]];
            else
               JF := [h[1]: h in l[3]];
            end if;
            card := UnipotentCentraliserOrder ("GL", [], IdentityMatrix (GF(p^(e*Degree (l[2]) div 2)), 2), []: JF := JF);
            if is_omega and true in {IsOdd(h): h in JF} then SplitOmega := true; end if;
         when 2:
            if SpecialCase2 then
               JF := l[3][1];
            elif type in {"GU", "SU"} then
               JF := [h: h in l[3]];
            else
               JF := [h[1]: h in l[3]];
            end if;
            card := UnipotentCentraliserOrder ("GU", [], IdentityMatrix (GF(p^(e*Degree (l[2]))), 2), []: JF := JF);
            if is_omega and true in {IsOdd(h): h in JF} then SplitOmega := true; end if;
      end case;
      Card *:= card;
   end for;

   D := Factorization (1);  // divide the centralizer cardinality by D
   if is_omega then
      if IsEven (q) then
         for l in L1 do
            if l[1] eq 0 then
               if l[3][2] ne [] or l[3][3] ne [] or l[3][4] ne [] or {IsEven(x): x in l[3][1]} ne {true} then
                  D := Factorization (2);
                  break l;
               end if;
            end if;
         end for;
      else
         if SplitSO then
            D *:= Factorization (2);
            SplitOmega := SplitOmega or #ValuesOmegapm gt 1;
         end if;
         if SplitOmega then D *:= Factorization (2); end if;
      end if;
   elif special then
      if type eq "SU" then
         r := Gcd (q+1, Gcd ([Gcd (x[3]): x in L1]));
         r := (q+1) div r;
         D := Factorization (r);
      else
         if SplitSO then D := Factorization (2); end if;
      end if;
   end if;

   return Card / D;
end function;

intrinsic ClassicalCentraliserOrder (G::GrpMat, g::GrpMatElt) -> RngIntEltFact
{Return the factored order of the centraliser of g in the standard 
classical group G of the given type}

   require (Generic (Parent (g)) cmpeq Generic (G)): "Input element is not in group";
   // require g in G: "Element not in group";
   require MyIsIn (G, g: Add := {"GL", "SL"}): "Input element is not in group";

   if IsCentral (G, g) then return FactoredOrder (G); end if;

   d := Degree (G); F := BaseRing (G);
   if (d eq 2 and #F le 4) then
      return FactoredOrder (Centraliser (G, g));
   end if;

   flag, tp := ClassicalGroupType (G);
   ValidTypes := {"SL", "GL", "Sp", "SU", "GU", "Omega+", "Omega-", "Omega",
                  "SO+", "SO-", "SO", "GO+", "GO-", "GO"};
   require flag and tp in ValidTypes: "Type of group must be one of ", ValidTypes;

   if tp eq "GO" and IsOdd (d) and IsEven (#F) then
      error "Function does not apply to this case";
   end if;

   if tp eq "GL" then
      return GLCentralizerOrder (G, g);
   elif tp eq "SL" then
      return SLCentralizerOrder (G, g);
   else 
      CB := TransformMatrix (G);
      return MyCentraliserOrder (tp, g^CB);
   end if;
end intrinsic;

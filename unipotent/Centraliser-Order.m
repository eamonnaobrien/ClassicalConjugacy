freeze;

import "../semisimple/card.m": CardinalityOfClassicalGroup;
import "Sp-Orthogonal-order.m": SpUnipotentCentraliserOrder, 
                        OrthogonalUnipotentCentraliserOrder;
import "central/even-sp.m": WeightsToLabel;
import "conjugation/is-conjugate.m": MyUnipotentClassLabel;

// compute cardinality of the centralizer of unipotent element g 
// in the group of type "type" preserving the supplied form;
// JF = multiset of the sizes of the Jordan blocks;
// 
// in the linear and unitary case, JF is the only information 
// needed to compute the cardinality;
// form is not required for Sp / Orthogonal in even characteristic 

Jordan_Parameters := function (g)
   _, _, c := JordanForm (g);
   blocks := [x[2]: x in c];
   return Multiset (blocks);
end function;

UnipotentCentraliserOrder := function (type, G, g, form: 
   JF := [], T := [], L := [], split := false)

   assert IsUnipotent (g);

   F := BaseRing (g);
   q := #F;
   p := Characteristic (F);
   e := Degree (F);
   if type in {"SU", "GU"} then
      q := p^(e div 2);
   end if;

   if type in {"GL", "SL", "GU", "SU"} then
      if JF eq [] then
         _, _, c := JordanForm (g);
         JF := [d[2]: d in c];
      end if;
      Array := {b: b in JF};
      Array := Sort (SetToSequence (Array));
      P := [<a, Multiplicity (JF, a)>: a in Array];
   end if;

   card := Factorization (1);
   case type:

      when "GL", "SL":
         for i in [1..#P] do
            card *:= CardinalityOfClassicalGroup ("linear", P[i][2], q);
         end for;
         exp := 0;
         for i in [1..#P] do
            exp +:= (P[i][1]-1)*P[i][2]^2;
            for j in [i+1..#P] do
               exp +:= 2*P[i][1]*P[i][2]*P[j][2];
            end for;
         end for;
         exp *:= e;
         if exp ne 0 then
            card *:= SequenceToFactorization ([<p, exp>]);
         end if;
         if type eq "SL" then
            card /:= Factorization (q-1);
            card *:= Factorization (Gcd (q-1, Gcd ([a[1]: a in P])));
         end if;

      when "GU", "SU":
         for i in [1..#P] do
            card *:= CardinalityOfClassicalGroup ("unitary", P[i][2], q);
         end for;
         exp :=0;
         for i in [1..#P] do
            exp +:= (P[i][1]-1)*P[i][2]^2;
            for j in [i+1..#P] do
               exp +:= 2*P[i][1]*P[i][2]*P[j][2];
            end for;
         end for;
         exp *:= (e div 2);
         if exp ne 0 then
            card *:= SequenceToFactorization ([<p, exp>]);
         end if;
         if type eq "SU" then
            card /:= Factorization (q+1);
            card *:= Factorization (Gcd (q+1, Gcd ([a[1]: a in P])));
         end if;

      when "Sp":
         if IsEven (q) then 
            if #L eq 0 then
               W := MyUnipotentClassLabel (G, g);
               T := WeightsToLabel (W);
            else
               T := L;
            end if;
            card := Factorization (SpUnipotentCentraliserOrder (T, [], q));
         elif IsOdd (q) then
            if #T eq 0 then T := Jordan_Parameters (g); end if;
            if #L eq 0 then L := MyUnipotentClassLabel (G, g); end if;
            card := Factorization (SpUnipotentCentraliserOrder (T, L, q));
         end if;

      when "GO+", "GO-", "GO", "SO+", "SO-", "SO", "Omega+", "Omega-", "Omega":
         if IsEven (q) then 
            if #L eq 0 then
               W := MyUnipotentClassLabel (G, g);
               T := WeightsToLabel (W[1]); T[#T] := W[2];
            else
               W := T;
            end if;
            card := Factorization (OrthogonalUnipotentCentraliserOrder (type, T, [], false, q));
         elif IsOdd (q) then 
            if #T eq 0 then T := Jordan_Parameters (g); end if;
            if #L eq 0 then L := MyUnipotentClassLabel (G, g); end if;
            if type in {"GO+", "GO-", "GO"} then 
               card := Factorization (OrthogonalUnipotentCentraliserOrder (type, T, L, false, q));
            else 
               split := L[2] eq "ns" select false else true;
               card := Factorization (OrthogonalUnipotentCentraliserOrder (type, T, L[1], split, q));
            end if;
         end if;

      else
         error "Type is incorrect";
   end case;
   return card;
end function;

UnipotentCentralizerOrder := UnipotentCentraliserOrder;

freeze;

import "SSCentralizer.m":SSCentralizer;
import "../card.m": CardinalityOfClassicalGroup;
import "../form.m": IndicateType, ConjugatePolynomial;

// compute the factored order of the centralizer of 
// semisimple element x in a classical group G

SSCentralizerOrder:=function(G,x)

   F:=BaseRing(G);
   // n:=Nrows(x);
   p:=Characteristic(F);
   q:=#F;
   t:=PolynomialRing(F).1;
   Card:=Factorization(1);

   A, c, type, special, IsOmega := SSCentralizer (G, x: OrderOnly := true);

   e := type eq "unitary" select Degree(F) div 2 else 0;

   //conjugate transpose matrix
   Star:=func<M: exp:=e| Transpose(FrobeniusImage(M,exp))>;
   //conjugate polynomial
   ConjPol:=ConjugatePolynomial(type eq "unitary");

   pos:=1;
   for i in [1..#c] do
      f:=c[i][1];
      d:=c[i][2];
      if f eq ConjPol(f) and Degree(f) eq 1 then
         case type:
            when "symplectic":
               Card*:=CardinalityOfClassicalGroup(type,d,q);
            when "unitary":
               Card*:=CardinalityOfClassicalGroup(type,d,p^e);
            when "orthogonal","orthogonalplus","orthogonalminus","orthogonalcircle":
               B1:=Submatrix(A,pos,pos,d,d);
               type1:=IndicateType(B1);
               Card*:=CardinalityOfClassicalGroup(type1,d,q);
         end case;
         pos+:=d;
      elif f ne ConjPol(f) then
         Card*:=CardinalityOfClassicalGroup("linear",d,q^Degree(f));
         pos+:=Degree(f)*d*2;
      else
         if type eq "unitary" then
            Card*:=CardinalityOfClassicalGroup("unitary",d,p^(e*Degree(f)));
         else
            Card*:=CardinalityOfClassicalGroup("unitary",d,q^(Degree(f) div 2));
         end if;
         pos+:=Degree(f)*d;
      end if;
   end for;

   if special then
      if type eq "unitary" then
         Card/:=Factorization(p^e+1);
      elif c[1][1] in {t-1,t+1} then
         Card/:=SequenceToFactorization([<2,1>]);
      end if;
   end if;
   if IsOmega then
      if IsOdd(p) or (IsEven(p) and c[1][1] eq t+1) then
         Card/:=SequenceToFactorization([<2,1>]);
      end if;
   end if;

   return Card;
end function;

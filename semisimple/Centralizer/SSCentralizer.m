freeze;

import "Correctors.m": CorrectSpecial, CorrectOmega;
import "../card.m": CardinalityOfClassicalGroup;
import "../form.m": DetermineForm, SpinN, IndicateType, ConjugatePolynomial;

// support function to reduce duplication 
RightGroup := function(type,d,q: special:=false, omega:=false)
   case type:
      when "orthogonalplus":
         if omega then G := OmegaPlus(d,q);
         elif special then G := SOPlus(d,q);
         else G := GOPlus(d,q);
         end if;
      when "orthogonalminus":
         if omega then G := OmegaMinus(d,q);
         elif special then G := SOMinus(d,q);
         else G := GOMinus(d,q);
         end if;
      when "orthogonal", "orthogonalcircle":
         if omega then G := Omega(d,q);
         elif special then G := SO(d,q);
         else G := GO(d,q);
         end if;
   end case;

   return G;
end function;

// G must be a classical group (GO, GU, Sp, SO, Su, Omega) and x semisimple 
// returns H = Centralizer(G,x)
// Does not work for orthogonal groups in even characteristic and odd dimension

SSCentralizer:=function(G,x: OrderOnly := false)
   F:=BaseRing(G);
   n:=Nrows(x);
   p:=Characteristic(F);
   q:=#F;
   t:=PolynomialRing(F).1;
   M:=MatrixAlgebra(F,n);
   Card:=Factorization(1);
   FirstHasDim1:=false;

   B,type,sgn,special,IsOmega,Q:=DetermineForm(G,x);

   e := type eq "unitary" select Degree(F) div 2 else 0;

   //conjugate transpose matrix
   Star:=func<M: exp:=e| Transpose(FrobeniusImage(M,exp))>;
   //conjugate polynomial
   ConjPol:=ConjugatePolynomial(type eq "unitary");

   a,b,r:=JordanForm(x);

   // little change in Jordan Form:
   // now c1 = [<f_i,m_i>], with m_i = multiplicity of el. div. f_i
   Set1:={x: x in r};
   c:=[<x[1],Multiplicity(r,x)>: x in Set1 | x[1] ne t-1 and x[1] ne t+1];
   for x in Set1 do
      if x[1] eq t-1 or x[1] eq t+1 then
         Insert(~c,1,<x[1],Multiplicity(r,x)>);
      end if;
   end for;
   // this is to put t+1 and t-1 at the beginning of the list

   // this is because if the first elementary divisor is t-1 of 
   // multiplicity 1 it is not possible
   // to correct Determinant and SpinorNorm at the same time
   if c[1][1] eq t-1 and c[1][2] eq 1 and c[2][1] eq t+1 then
      d:=c[1];
      c[1]:=c[2];
      c[2]:=d;
   end if;

   X:=ZeroMatrix(F,0,0);

   // X: form in which is easier to compute the centralizer
   i:=1;
   pos:=1;
   while i le #c do
      f:=c[i][1];
      d:=c[i][2];        // d = dimension
      if f eq ConjPol(f) then
         X:=DiagonalJoin(X,DiagonalJoin([CompanionMatrix(f): j in [1..d]]));
      else
          X:=DiagonalJoin(X,DiagonalJoin([CompanionMatrix(f): j in [1..d]]));
          X:=DiagonalJoin(X,DiagonalJoin([Star(CompanionMatrix(f))^-1: j in [1..d]]));
          Exclude(~c,<ConjPol(f),d>);
      end if;
      i+:=1;
   end while;

   _,bX:=JordanForm(X);
   b1:=bX^-1*b;
   // rewrite A in the upper triangular form
   if p eq 2 and type ne "unitary" and type ne "symplectic" then
      A:=b1*Q*Star(b1);              // A = quadratic form preserved by X
      for i in [1..n] do
      for j in [i+1..n] do
         A[i,j]+:=A[j,i];
         A[j,i]:=0;
      end for;
      end for;
   else
      A:=b1*B*Star(b1);   // A = sesquilinear form preserved by X
   end if;

   if OrderOnly then return A, c, type, special, IsOmega; end if;

   // CorrectO is an element in the centralizer of the first el.div. with determinant not 1 
   // CorrectSp is an element in the centralizer of the first el.div. 
   // (or the second el.div. in the case x^2-1 has rank n-1)
   // with determinant 1 and SpinorNorm 1
   if special or IsOmega then
      CorrectSp:=CorrectSpecial(c,F,n,q,p,e,type,A,b1: Semisimple);
      DetC:=Determinant(CorrectSp);
   end if;
   if IsOmega then
      CorrectO, FirstHasDim1:=CorrectOmega(c,F,n,q,p,e,type,A,b1: Semisimple);
   end if;

   // create generators for the centralizer
   Gens:=[]; 

   // case Special: if <x_1, ..., x_k> are generators for centralizer of x 
   // in the general group, generators of the centralizer of the first el.div. 
   // are replaced by generators for centralizer in the special group;
   // the other generators are multiplied by some power of CorrectSp, 
   // depending on their determinant

   // case Omega: if <x_1, ..., x_k> are generators for centralizer of x 
   // in the general group, generators of the centralizer of the first el.div. 
   // are replaced by generators for centralizer in the Omega group;
   // the other generators are multiplied by some power of CorrectSp 
   // and some power of CorrectO, depending on their determinant and SpinorNorm
   // above, the first el.div. has to be replaced by the second el.div. if FirstHasDim1=true.
   // (because in such a case there are no elements in the centralizer of the first 
   // el.div. with det=1 and SpinorNorm=1

   Y:=IdentityMatrix(F,n);
   pos:=1;
   ind:=1;
   if FirstHasDim1 then          
      // in this case the correction of SpinorNorm acts on the second summand, 
      // not on the first one
      ind:=2;
   end if; 
   for i in [1..#c] do
      f:=c[i][1];
      d:=c[i][2];
      deg:=Degree(f);
      if f eq ConjPol(f) and deg eq 1 then
         B1:=Submatrix(A,pos,pos,d,d);
         case type:
            when "unitary":
               m:=TransformForm(B1,"unitary": Restore:=false);
               if special then
                  if i eq 1 then
                     for j in [1..Ngens(SU(d,F))] do
                        Y1:=InsertBlock(Y,m*SU(d,F).j*m^-1,pos,pos);
                        Y1:=b1^-1*Y1*b1;
                        Append(~Gens,Y1);
                     end for;
                  else
                     for j in [1..Ngens(GU(d,F))] do
                        Y1:=InsertBlock(Y,m*GU(d,F).j*m^-1,pos,pos);
                        Y1:=b1^-1*Y1*b1;
                        Y1*:=CorrectSp^Log(DetC,Determinant(GU(d,F).j)^-1);
                        Append(~Gens,Y1);
                     end for;
                  end if;
               else
                  for j in [1..Ngens(GU(d,F))] do
                     Y1:=InsertBlock(Y,m*GU(d,F).j*m^-1,pos,pos);
                     Y1:=b1^-1*Y1*b1;
                     Append(~Gens,Y1);
                  end for;
               end if;
            when "symplectic":
               m:=TransformForm(B1,"symplectic": Restore:=false);
               for j in [1..Ngens(Sp(d,F))] do
                  Y1:=InsertBlock(Y,m*Sp(d,F).j*m^-1,pos,pos);
                  Append(~Gens,b1^-1*Y1*b1);
               end for;
            when "orthogonalcircle","orthogonalplus","orthogonalminus", "orthogonal":
               if d eq 1 then
                  type1:="orthogonal";
                  if i ne ind then
                     Y1:=InsertBlock(Y,-IdentityMatrix(F,1),pos,pos);
                     Y1:=b1^-1*Y1*b1;
                     if special then
                         Y1*:=CorrectSp;
                         if IsOmega and SpinN(GL(n,F)!Y1,Q,p) eq 1 then
                            Y1*:=CorrectO;
                         end if;
                     end if;
                     Append(~Gens,Y1);
                  else
                     Y1:=InsertBlock(Y,-IdentityMatrix(F,1),pos,pos);
                     Y1:=b1^-1*Y1*b1;
                     if special then
		        Y1*:=CorrectSp;
                     end if;
                     Append(~Gens,Y1);
                  end if;
               else
                  type1:=IndicateType(B1);
                  m:=TransformForm(B1,type1: Restore:=false);
                  if IsOmega then
                     if i eq ind then
                        G1 := RightGroup (type1, d, F: special, omega);
                        for j in [1..Ngens(G1)] do
                           Y1:=InsertBlock(Y,m*G1.j*m^-1,pos,pos);
                           Y1:=b1^-1*Y1*b1;
                           Append(~Gens,Y1);
                        end for;
                     else
                        G1 := RightGroup (type1, d, F);
                        for j in [1..Ngens(G1)] do
                           Y1:=InsertBlock(Y,m*G1.j*m^-1,pos,pos);
                           Y1:=b1^-1*Y1*b1;
                           if Determinant(Y1) eq -1 then
                              Y1*:=CorrectSp;
                           end if;
                           Y1*:=CorrectO^SpinN(GL(n,F)!Y1,Q,p);
                           Append(~Gens,Y1);
                        end for;
                     end if;
                  elif special then
                     if i eq ind then
                        G1 := RightGroup (type1, d, F: special);
                        for j in [1..Ngens(G1)] do
                           Y1:=InsertBlock(Y,m*G1.j*m^-1,pos,pos);
                           Y1:=b1^-1*Y1*b1;
                           Append(~Gens,Y1);
                        end for;
                     else
                        G1 := RightGroup (type1, d, F);
                        for j in [1..Ngens(G1)] do
                           Y1:=InsertBlock(Y,m*G1.j*m^-1,pos,pos);
                           Y1:=b1^-1*Y1*b1;
                           if Determinant(Y1) eq -1 then
                              Y1*:=CorrectSp;
                           end if;
                           Append(~Gens,Y1);
                        end for;
                     end if;
                  else
                     G1 := RightGroup (type1, d, F);
                     for j in [1..Ngens(G1)] do
                        Y1:=InsertBlock(Y,m*G1.j*m^-1,pos,pos);
                        Y1:=b1^-1*Y1*b1;
                        Append(~Gens,Y1);
                     end for;
                  end if;
               end if;
         end case;
         pos+:=d;
         if type eq "unitary" then
            Card*:=CardinalityOfClassicalGroup(type,d,p^e);
         elif type eq "symplectic" then
            Card*:=CardinalityOfClassicalGroup(type,d,q);
         else
            Card*:=CardinalityOfClassicalGroup(type1,d,q);
         end if;
      elif f ne ConjPol(f) then
         E<l>:=ext<F|f: Optimize := false>;
         A1:=Submatrix(A,pos,pos+d*deg,d*deg,d*deg);
         if i eq ind and (IsOmega or (special and type eq "unitary")) then
            // generate the subgroup of GL(d,E) of index 2 or q+1, 
            // using the generators for SL and an element of appropriate determinant
            for j in [1..Ngens(SL(d,E))] do
               a:=SL(d,E).j;
               suss:=BlockMatrix(d,d,[&+[CompanionMatrix(f)^(k-1)*Eltseq(a[j1,j2],F)[k]:
                       k in [1..deg]]: j1,j2 in [1..d]]);
               suss:=DiagonalJoin(suss,Star(A1^-1*suss^-1*A1));
               y:=InsertBlock(Y,suss,pos,pos);
               y:=b1^-1*y*b1;
               Append(~Gens,y);
            end for;
            array:=[E!1: j in [1..d]];
            if IsOmega then
               array[1]:=PrimitiveElement(E)^2;
            else 
               array[1]:=PrimitiveElement(E)^(p^e+1);
            end if;
            a:=DiagonalMatrix(E,array);
            suss:=BlockMatrix(d,d,[&+[CompanionMatrix(f)^(k-1)*Eltseq(a[j1,j2],F)[k]:
                    k in [1..deg]]: j1,j2 in [1..d]]);
            suss:=DiagonalJoin(suss,Star(A1^-1*suss^-1*A1));
            y:=InsertBlock(Y,suss,pos,pos);
            y:=b1^-1*y*b1;
            Append(~Gens, y);
         else
            for j in [1..Ngens(GL(d,E))] do
               a:=GL(d,E).j;
               suss:=BlockMatrix(d,d,[&+[CompanionMatrix(f)^(k-1)*Eltseq(a[j1,j2],F)[k]:
                       k in [1..deg]]: j1,j2 in [1..d]]);
               suss:=DiagonalJoin(suss,Star(A1^-1*suss^-1*A1));
               y:=InsertBlock(Y,suss,pos,pos);
               y:=b1^-1*y*b1;
               if special then
                  if type eq "unitary" then
                     l:=Log(DetC,Determinant(y)^-1);
                     y*:=CorrectSp^l;
	          else
 		     if Determinant(y) eq -1 then
                        y*:=CorrectSp;
                     end if;
                  end if;
               end if;
               if IsOmega then
                  y*:=CorrectO^SpinN(GL(n,F)!y,Q,p);
               end if;
               Append(~Gens, y);
            end for;
         end if;
         pos+:=2*d*deg;
         Card*:=CardinalityOfClassicalGroup("linear",d,q^deg);
      else
         E<l>:=ext<F|f: Optimize := false>;
         H:=GL(deg,F);
         _,T:=IsConjugate(H,H!CompanionMatrix(f)^-1,H!Star(CompanionMatrix(f)));
         if Determinant(T+sgn*Star(T)) eq 0 then
            T:=CompanionMatrix(f)*T+sgn*Star(CompanionMatrix(f)*T);
         else
            T:=T+sgn*Star(T);
         end if;
         T:=T^-1;
         A1:=Submatrix(A,pos,pos,d*deg,d*deg);
         if p eq 2 and type ne "unitary" and type ne "symplectic" then
            A1+:=Transpose(A1);
         end if;
         B1:=A1*DiagonalJoin([T: j in [1..d]]);
         H1:=ZeroMatrix(E,d,d);
         // H1 = matrix B1 over the smaller field
         for j1,j2 in [1..d] do
            H1[j1,j2]:=&+[l^(k-1)*B1[deg*(j1-1)+1,deg*(j2-1)+k]: k in [1..deg]];
         end for;
         m:=TransformForm(H1,"unitary": Restore:=false);
         if i eq ind and (IsOmega or (special and type eq "unitary")) then
            // generate the subgroup of GL(d,E) of index 2 or q+1, 
            // using the generators for SU and an element of appropriate determinant
            for j in [1..Ngens(SU(d,E))] do
               S:=m*SU(d,E).j*m^-1;
               suss:=BlockMatrix(d,d,[&+[CompanionMatrix(f)^(k-1)*Eltseq(S[j1,j2],F)[k]:
                         k in [1..deg]]: j1,j2 in [1..d]]);
               Y1:=InsertBlock(Y,suss,pos,pos);
               Y1:=b1^-1*Y1*b1;
               Append(~Gens,Y1);
            end for;
            array:=[E!1: i in [1..d]];
            w:=PrimitiveElement(E);
            if IsOmega then
               array[1]:=w^2;
               array[d]*:=w^(-2*q^(deg div 2));
            else
               array[1]:=w^(p^e+1);
               array[d]*:=w^(-(p^e+1)*p^(e*deg));
            end if;
            S:=m*DiagonalMatrix(E,array)*m^-1;
            suss:=BlockMatrix(d,d,[&+[CompanionMatrix(f)^(k-1)*Eltseq(S[j1,j2],F)[k]:
                         k in [1..deg]]: j1,j2 in [1..d]]);
            Y1:=InsertBlock(Y,suss,pos,pos);
            Y1:=b1^-1*Y1*b1;
            Append(~Gens,Y1);
         else
            for j in [1..Ngens(GU(d,E))] do
               S:=m*GU(d,E).j*m^-1;
               suss:=BlockMatrix(d,d,[&+[CompanionMatrix(f)^(k-1)*Eltseq(S[j1,j2],F)[k]:
                         k in [1..deg]]: j1,j2 in [1..d]]);
               Y1:=InsertBlock(Y,suss,pos,pos);
               Y1:=b1^-1*Y1*b1;
               if special then
                  if type eq "unitary" then
                     l:=Log(DetC,Determinant(Y1)^-1);
                     Y1*:=CorrectSp^l;
 	          else
		     if Determinant(Y1) eq -1 then
                        Y1*:=CorrectSp;
                     end if;
                  end if;
               end if;
               if IsOmega then
                  Y1*:=CorrectO^SpinN(GL(n,F)!Y1,Q,p);
               end if;
               Append(~Gens,Y1);
            end for;
         end if;
         pos+:=d*deg;
         Card*:=CardinalityOfClassicalGroup("unitary",d,p^(Degree(F)*deg div 2));
      end if;
   end for;

   // correcting cardinality in Special and Omega case
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

   H:=sub<GL(n,F)|Gens>;
   H`FactoredOrder:=Card;
   H`Order:=Integers()!Card;

   return H;
end function;

intrinsic InternalSemisimpleCentralizer (G :: GrpMat, g:: GrpMatElt) -> GrpMat 
{Centralizer of semisimple element in classical group G}
   require IsSemisimple (g): "Input element is not semisimple";
   return SSCentralizer (G, g);
end intrinsic;

intrinsic InternalSemisimpleCentraliser (G :: GrpMat, g:: GrpMatElt) -> GrpMat 
{Centraliser of semisimple element in classical group G}
   return InternalSemisimpleCentralizer (G, g); 
end intrinsic;

freeze;

import "../card.m": CardinalityOfClassicalGroup;
import "../form.m": FormForCompanionMatrix, ConjugatePolynomial;

// returns the list of semisimple conjugacy classes of GU(n,F)
// each output element has the form < m,c,X >, where
// X is the representative, m = order(X), c = class size of X;

// if OnlyPolynomials=true, then every output element is a list of 4-uples <f,m,t,B>, where
// the f's are the elementary divisors of X, m = multiplicity of f as el.div.,
// t = 0 (f=f* of degree 1), t=1 (f ne f*), t=2 (f=f* of degree>1)
// B is a form preserved by the companion matrix of f if t=2 (otherwise it does not matter)
// the parameter OnlyPolynomials is useful for the code Gen-Classes.m
// if f ne f*, they are both el.div., but only one of them appears in the list

SSClassesGU:=function(n,F: OnlyPolynomials:=false)

   if Type(F) eq RngIntElt then
      F:=GF(F^2);
   end if;
   vero,q:=IsSquare(#F);
   if not vero then
      error "#F must be a square";
   end if;
   e:=Degree(F) div 2;
   p:=Characteristic(F);
   w:=PrimitiveElement(F);

   Explicit:= not OnlyPolynomials;
   ConjClasses:=[* *];
   t:=PolynomialRing(F).1;
   // ConjPol(f) = dual polynomial of f
   ConjPol:=ConjugatePolynomial(true);
   Gr:=GL(n,F);

   if n eq 1 then
      if Explicit then
         for j in [1..q+1] do
            Append(~ConjClasses,[<(q+1) div Gcd(q+1,j), 1, Gr![w^(j*(q-1))]>]);
         end for;
      else
         for j in [1..q+1] do
            Append(~ConjClasses,[<t-w^(j*(q-1)),1,0,IdentityMatrix(F,1)>]);
         end for;
      end if;
      return ConjClasses;
   end if;

   m:=(n-1) div 2;
   // S[i] contains all elementary divisors of dimension i (p eq (t pm 1)^2, pp* or p = p*)
   // S[1] = 0 (f = f*, deg(f) = 1), 1 (f ne f*) or 2 (f eq f*, deg(f) > 1)
   // S[2] = its matrix, S[3] matrix of the form
   // S[4] = degree of the el.div., S[5] = order(S[2])

   // if OnlyPolynomials=true, then S[1]=0,1,2 as above, 
   // S[2]=polynomial, S[3]=matrix of the form (only f=f* is useful)
   S:=[*[]: i in [1..m]*];
   
   // first step: compute cardinality of GU(n,q)
   Card := CardinalityOfClassicalGroup ("unitary", n, q);

   //remember all possible elementary divisors of degree less than m
   for i in [1..(m div 2)] do
      if i eq 1 then      
         X:={{@x, ConjPol(x)@}: x in AllIrreduciblePolynomials(F,i) | x ne t};
      else
         X:={{@x, ConjPol(x)@}: x in AllIrreduciblePolynomials(F,i)};
      end if;
      for x in X  do
         f:=x[1];
         if #x eq 1 then       //begin construction matrix of the form preserved by f=f*
            C:=CompanionMatrix(f);
            if i eq 1 then
               if Explicit then
                  Append(~S[i],<0,C,IdentityMatrix(F,1),i,Order(C)>);
               else
                  Append(~S[i],<0,f,IdentityMatrix(F,1)>);
               end if;
            else
               B:=FormForCompanionMatrix(f,"GU");
               if Explicit then
                  Append(~S[i],<2,C,B,i,Order(C)>);
               else
                  Append(~S[i],<2,f,B>);
               end if;
            end if;
         else
            if Explicit then
               C:=CompanionMatrix(f);
               ord:=Order(C);
               C:=DiagonalJoin(C,Transpose(FrobeniusImage(C,e))^-1);
               h:=Degree(f);
               B:=BlockMatrix(2,2,[0,IdentityMatrix(F,h),IdentityMatrix(F,h),0]);
               Append(~S[2*i],<1,C,B,i,ord>);
            else
               Append(~S[2*i],<1,f,IdentityMatrix(F,2*i)>);
            end if;
         end if;
      end for;
   end for;
   for i in [(m div 2)+1..m] do
      if IsOdd(i) then
         k:=i div 2;
         R:=CartesianPower(F,k);
         for L in R do
            for s in {w^(j*(q-1)): j in [1..q+1]} do   //unique possible constant terms for p=p*
               //need to add [0] for the case k=0
               f:=&+([0] cat [L[j]*t^j+s*L[j]^q*t^(i-j): j in [1..k]]);   
               f:=f+s+t^i;
               if IsIrreducible(f) then
                  C:=CompanionMatrix(f);
                  if i eq 1 then
                     if Explicit then
                        Append(~S[i],<0,C,IdentityMatrix(F,1),i,Order(C)>);
                     else
                        Append(~S[i],<0,f,IdentityMatrix(F,i)>);
                     end if;
                  else
                     B:=FormForCompanionMatrix(f, "GU");
                     if Explicit then
                        Append(~S[i],<2,C,B,i,Order(C)>);
                     else
                        Append(~S[i],<2,f,B>);
                     end if;
                  end if;
               end if;
            end for;
         end for;
      end if;
   end for;

   // for every partition of n, assign all possible lists of elementary divisors 
   // whose sequence of dimensions is exactly the partition
   Omega:=RestrictedPartitions(n,{1..m});
   if q eq 2 then                                  
       //need this passage because #S[2] is empty if q=2
      Omega:=RestrictedPartitions(n,{1..m} diff {2});
   end if;
   for P in Omega do
      array:=[Multiplicity(P,i): i in [1..m]];
      R:=<>;
      //create all possible distributions of the blocks of a 
      // given dimension to the memorized el. div.               
      for i in [1..m] do
         Shelp:=[];
         ni:=#S[i];
         si:=array[i];
         if ni eq 0 then
            Shelp:=[[]];
         else
            sumi:=ni+si;
            set:={k: k in [1..sumi-1]};
            for y in Subsets(set,ni-1) do
               if IsEmpty(y) then
                  if ni eq 1 then
                     seq:=[];       // need this for the case q=2
                  else
                     seq:=[<1,si>];
                     det:=S[i][1][6]^si;
                  end if;
               else
                  x:=SetToSequence(y);
                  Sort(~x);
                  Insert(~x,1,0);
                  Append(~x,sumi);
                  seq:=[];
                  for j in [1..ni] do
                     if x[j+1]-x[j] gt 1 then
   	                Append(~seq,<j, x[j+1]-x[j]-1>);
                     end if;
                  end for;
               end if;
               //Shelp contains all possible distributions of el. divisors of dimension i
               Append(~Shelp,seq);       
            end for;
         end if;
         Append(~R,Shelp);
      end for;                      //end creation R

      // c[i] = [<a_j,b_j>: j]; the a_j-th el.div. of dimension i has multiplicity b_j
      C:=CartesianProduct(R);
      for c in C do
         if Explicit then
            Form:=Random(MatrixAlgebra(F,0));
            Repr:=Random(MatrixAlgebra(F,0));
            card:=Card;
            order:=1;
            for i in [1..m] do
               for j in [1..#c[i]] do
                  pos:=c[i][j][1];
                  cij:=c[i][j][2];
                  type:=S[i][pos][1];
                  deg:=S[i][pos][4];
                  for k in [1..cij] do
                     Form:=DiagonalJoin(Form,S[i][pos][3]);
                     Repr:=DiagonalJoin(Repr,S[i][pos][2]);
                  end for;
                  // divide |GU(n,q)| by the cardinality of the centralizer of x
                  if type eq 0 then
                     if cij gt 1 then
                        card/:=SequenceToFactorization([<p,e*cij*(cij-1) div 2>]);
                     end if;
                     for k in [1..cij] do
                        card/:=Factorization(q^k-(-1)^k);
                     end for;
                  elif type eq 2 then
                     if cij gt 1 then
                        card/:=SequenceToFactorization([<p,deg*e*cij*(cij-1) div 2>]);
                     end if;
                     for k in [1..cij] do
                        card/:=Factorization(q^(deg*k)-(-1)^k);
                     end for;
                  else
                     if cij gt 1 then
                        card/:=SequenceToFactorization([<p,deg*e*cij*(cij-1)>]);
                     end if;
                     for k in [1..cij] do
                        card/:=Factorization(q^(2*k*deg)-1);
                     end for;
                  end if;
                  order:=Lcm(order,S[i][pos][5]);
               end for;
            end for;
            M:=TransformForm(Form,"unitary": Restore:=false);
            Repr:=M^-1*Repr*M;
            Append(~ConjClasses,<order, Integers()!card,Gr!Repr>);
         else
            Cclass:=[**];
            for i in [1..m] do
               for j in [1..#c[i]] do
                  ind:=c[i][j][1];
                  Append(~Cclass,<S[i][ind][2],c[i][j][2],S[i][ind][1],S[i][ind][3]>);
               end for;
            end for;
            Append(~ConjClasses,Cclass);
         end if;
      end for;
   end for;
   // end creation conjugacy classes with blocks of dimension at most m

   // begin creation conjugacy classes with blocks of dimension gt m
   for i in [m+1..n] do
      T:=[];                 
      //T contains elementary divisors of dimension i (both p=p* and pp*)
      if IsOdd(i) then
         k:=i div 2;
         if k eq 0 then
            for s in {w^(j*(q-1)): j in [1..q+1]} do
             if Explicit then
               Append(~T,<0,s*IdentityMatrix(F,1),IdentityMatrix(F,1),1,Order(s)>);
             else
               Append(~T,<0,t-s,IdentityMatrix(F,i)>);
             end if;
            end for;
         else
            R:=CartesianPower(F,k);
            for L in R do
               for s in {w^(j*(q-1)): j in [1..q+1]} do      
                  //unique possible constant terms for p=p*
                  f:=&+([0] cat [L[j]*t^j+s*L[j]^q*t^(i-j): j in [1..k]]);
                  f:=f+s+t^i;
                  if IsIrreducible(f) then
                     C:=CompanionMatrix(f);
                     B:=FormForCompanionMatrix(f, "GU");
                     if Explicit then
                        Append(~T,<2,C,B,i,Order(C)>);
                     else
                        Append(~T,<2,f,B>);
                     end if;
                  end if;
               end for;
            end for;
         end if;
      else
         k:=i div 2;
         if k eq 1 then
            X:={{@x, ConjPol(x)@}: x in AllIrreduciblePolynomials(F,k)| x ne t};
         else
            X:={{@x, ConjPol(x)@}: x in AllIrreduciblePolynomials(F,k)};
         end if;
         for x in X do
            if #x eq 2 then
               f:=x[1];
               if Explicit then
               C:=CompanionMatrix(f);
               ord:=Order(C);
               C:=DiagonalJoin(C,Transpose(FrobeniusImage(C,e))^-1);
               B:=BlockMatrix(2,2,[0,IdentityMatrix(F,k),IdentityMatrix(F,k),0]);
               Append(~T,<1,C,B,k,ord>);
               else
                  Append(~T,<1,f,IdentityMatrix(F,i)>);
               end if;
            end if;
         end for;
      end if;
      m1:=Min(m,n-i);
      Omega:=RestrictedPartitions(n-i,{1..m1});
      if q eq 2 then
         Omega:=RestrictedPartitions(n-i,{1..m1} diff {2});
      end if;
      for P in Omega do           
         array:=[Multiplicity(P,j): j in [1..m1]];
         R:=<>;
         //create all possible distributions of the blocks of a 
         //given dimension to the memorized el. div.
         for j in [1..m1] do
            Shelp:=[];
            ni:=#S[j];
            si:=array[j];
            if ni eq 0 then
               Shelp:=[[]];                     
            else
               sumi:=ni+si;
               set:={k: k in [1..sumi-1]};
               for y in Subsets(set,ni-1) do
                  if IsEmpty(y) then
                     if ni eq 1 then
                        seq:=[];                // need this for the case q=2
                     else
                        seq:=[<1,si>];
                        det:=S[i][1][6]^si;
                     end if;
                  else
                     x:=SetToSequence(y);
                     Sort(~x);
                     Insert(~x,1,0);
                     Append(~x,sumi);
                     seq:=[];
                     for k in [1..ni] do
                        if x[k+1]-x[k] gt 1 then
  	          	   Append(~seq,<k,x[k+1]-x[k]-1>);
                        end if;
                     end for;
                  end if;
                  Append(~Shelp,seq);
               end for;
            end if;
            Append(~R,Shelp);
         end for;                                    //end creation R

         // c[i] = [<a_j,b_j>: j]: the a_j-th el.div. of dimension i has multiplicity b_j
         C:=CartesianProduct(R);
         for c in C do
            if Explicit then
               Form:=Random(MatrixAlgebra(F,0));
               Repr:=Random(MatrixAlgebra(F,0));
               card:=Card;
               order:=1;
               for j1 in [1..m1] do
                  for j2 in [1..#c[j1]] do
	             pos:=c[j1][j2][1];
                     cij:=c[j1][j2][2];
                     type:=S[j1][pos][1];
                     deg:=S[j1][pos][4];
                     for k in [1..cij] do
                        Form:=DiagonalJoin(Form,S[j1][pos][3]);
                        Repr:=DiagonalJoin(Repr,S[j1][pos][2]);
                     end for;
                     // divide |GU(n,q)| by the cardinality of the centralizer of x
                     if type eq 0 then
                        if cij gt 1 then
                           card/:=SequenceToFactorization([<p,e*cij*(cij-1) div 2>]);
                        end if;
                        for k in [1..cij] do
                           card/:=Factorization(q^k-(-1)^k);
                        end for;
                     elif type eq 2 then
                        if cij gt 1 then
                           card/:=SequenceToFactorization([<p,deg*e*cij*(cij-1) div 2>]);
                        end if;
                        for k in [1..cij] do
                           card/:=Factorization(q^(deg*k)-(-1)^k);
                        end for;
                     else
                        if cij gt 1 then
                           card/:=SequenceToFactorization([<p,deg*e*cij*(cij-1)>]);
                        end if;
                        for k in [1..cij] do
                           card/:=Factorization(q^(2*k*deg)-1);
                        end for;
                     end if;
                     order:=Lcm(order,S[j1][pos][5]);
                  end for;
               end for;
               for x in T do
                  type:=x[1];
                  deg:=x[4];
                  Form1:=DiagonalJoin(Form,x[3]);
                  Repr1:=DiagonalJoin(Repr,x[2]);
                  M:=TransformForm(Form1,"unitary": Restore:=false);
                  Repr1:=M^-1*Repr1*M;
                  order1:=Lcm(order,x[5]);
                  if type eq 2 then
                     card1:=card/Factorization(q^deg+1);
                  else
                     card1:=card/Factorization(q^(2*deg)-1);
                  end if;
                  Append(~ConjClasses,<order1, Integers()!card1,Gr!Repr1>);
               end for;
            else
               Cclass:=[**];
               for j1 in [1..m1] do
                  for j2 in [1..#c[j1]] do
                     ind:=c[j1][j2][1];
                     Append(~Cclass,<S[j1][ind][2],c[j1][j2][2],S[j1][ind][1],S[j1][ind][3]>);
                  end for;
               end for;
               for x in T do
                  Append(~ConjClasses, Append(Cclass,<x[2],1,x[1],x[3]>));
               end for;
            end if;
         end for;
      end for;
      if IsEven(n) and i eq n div 2 then
         T1:=T;
      end if;
   end for;

   //final case: with 2 elementary divisors of dimensions n/2 (case n even)
   if IsEven(n) then
      s:=#T1;
      for i in [1..s] do
         if Explicit then
            card:=Card;
            Form:=DiagonalJoin(T1[i][3],T1[i][3]);
            Repr:=DiagonalJoin(T1[i][2],T1[i][2]);
            M:=TransformForm(Form,"unitary": Restore:=false);
            Repr:=M^-1*Repr*M;
            type:=T1[i][1];
            deg:=T1[i][4];
            if type eq 0 or type eq 2 then
               card/:=SequenceToFactorization([<p,deg*e>]);  // it should be deg*e*2*(2-1)/2
               card/:=Factorization(q^deg+1);
               card/:=Factorization(q^(2*deg)-1);
            else
               card/:=SequenceToFactorization([<p,deg*e*2>]);
               card/:=Factorization(q^(deg*2)-1);
               card/:=Factorization(q^(deg*4)-1);
            end if;
            Append(~ConjClasses,<T1[i][5],Integers()!card,Gr!Repr>);
            for j in [i+1..s] do
               card:=Card;
               Form:=DiagonalJoin(T1[i][3],T1[j][3]);
               Repr:=DiagonalJoin(T1[i][2],T1[j][2]);
               M:=TransformForm(Form,"unitary": Restore:=false);
               Repr:=M^-1*Repr*M;
               type:=T1[i][1];
               deg:=T1[i][4];
               if type eq 0 or type eq 2 then
                  card/:=Factorization(q^deg+1);
               else
                  card/:=Factorization(q^(2*deg)-1);
               end if;
               type:=T1[j][1];
               deg:=T1[j][4];
               if type eq 0 or type eq 2 then
                  card/:=Factorization(q^deg+1);
               else
                  card/:=Factorization(q^(2*deg)-1);
               end if;
               Append(~ConjClasses,<Lcm(T1[i][5],T1[j][5]),Integers()!card,Gr!Repr>);
            end for;
         else
            Append(~ConjClasses,[<T1[i][2],2,T1[i][1],T1[i][3]>]);
            for j in [i+1..s] do
               Append(~ConjClasses,[*<T1[i][2],1,T1[i][1],T1[i][3]>,<T1[j][2],1,T1[j][1],T1[j][3]>*]);
            end for;
         end if;
      end for;
   end if;

   return ConjClasses;
end function;

freeze;

import "../card.m": CardinalityOfClassicalGroup;
import "../form.m": FormForCompanionMatrix, ConjugatePolynomial;

// returns the list of semisimple conjugacy classes of SU(n,F)
// each output element has the form < m,c,X >, where
// X is the representative, m = order(X), c = class size of X;

SSClassesSU:=function(n,F)
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

   ConjClasses:=[];

   t:=PolynomialRing(F).1;
   // ConjPol(f) = dual polynomial of f
   ConjPol:=ConjugatePolynomial(true);
   Gr:=GL(n,F);

   if n eq 1 then
      Append(~ConjClasses, [<1,1,Identity(Gr)>]);
      return ConjClasses;
   end if;

   m:=(n-1) div 2;
   // S[i] contains all elementary divisors of dimension i (p eq (t pm 1)^2, pp* or p = p*)
   // S[1] = 0 (f = f*, deg(f) = 1), 1 (f ne f*) or 2 (f eq f*, deg(f) > 1)
   // S[2] = its matrix, S[3] matrix of the form
   // S[4] = degree of the el.div., S[5] = order(S[2])
   // S[6] = Determinant(S[2])
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
         if #x eq 1 then       
            //begin construction matrix of the form preserved by f=f*
            C:=CompanionMatrix(f);
            B:=FormForCompanionMatrix(f, "SU");
            if i eq 1 then
               Append(~S[i],<0,C,B,i,Order(C),-Eltseq(f)[1]>);
            else
               Append(~S[i],<2,C,B,i,Order(C),-Eltseq(f)[1]>);
            end if;
         else
            C:=CompanionMatrix(f);
            ord:=Order(C);
            C:=DiagonalJoin(C,Transpose(FrobeniusImage(C,e))^-1);
            h:=Degree(f);
            B:=BlockMatrix(2,2,[0,IdentityMatrix(F,h),IdentityMatrix(F,h),0]);
            Append(~S[2*i],<1,C,B,i,ord,Eltseq(f)[1]^(1-q)>);
         end if;
      end for;
   end for;

   for i in [(m div 2)+1..m] do
      if IsOdd(i) then
         k:=i div 2;
         R:=CartesianPower(F,k);
         for L in R do
            for s in {w^(j*(q-1)): j in [1..q+1]} do   
               //unique possible constant terms for p=p*
               f:=&+([0] cat [L[j]*t^j+s*L[j]^q*t^(i-j): j in [1..k]]);   
               //need to add [0] for the case k=0
               f:=f+s+t^i;
               if IsIrreducible(f) then
                  C:=CompanionMatrix(f);
                  B:=FormForCompanionMatrix(f, "SU");
                  if i eq 1 then
                     Append(~S[i],<0,C,B,i,Order(C),-s>);
                  else
                     Append(~S[i],<2,C,B,i,Order(C),-s>);
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
      //need this because #S[2] is empty if q=2
      Omega:=RestrictedPartitions(n,{1..m} diff {2});
   end if;
   for P in Omega do
      array:=[Multiplicity(P,i): i in [1..m]];
      R:=<>;
      //create all possible distributions of the blocks of a 
      //given dimension to the memorized el. div.               
      for i in [1..m] do
         Shelp:=[];
         ni:=#S[i];
         si:=array[i];
         // seq = <[<a1,b1>,...,<an,bn>],d> means the 
         // el.div. S[i][ai] appears bi times. d is the determinant
         if ni eq 0 then
            Shelp:=[<[],1>];
         else
            sumi:=ni+si;
            set:={k: k in [1..sumi-1]};
            for y in Subsets(set,ni-1) do
               det:=1;
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
                  for j in [1..ni] do
                     if x[j+1]-x[j] gt 1 then
   	                Append(~seq,<j, x[j+1]-x[j]-1>);
                        det*:=S[i][j][6]^(x[j+1]-x[j]-1);
                     end if;
                  end for;
               end if;
               //Shelp contains all possible distributions of el. divisors of dimension i
               Append(~Shelp,<seq,det>);       
            end for;
         end if;
         Append(~R,Shelp);
      end for;                                    //end creation R

      // c[i] = [[<a_j,b_j>: j],[det]]: the a_j-th el.div. of dimension i has multiplicity b_j, 
      // det = determinant of &*[ai^bi]
      C:=CartesianProduct(R);
      for c in C do
         Form:=Random(MatrixAlgebra(F,0));
         Repr:=Random(MatrixAlgebra(F,0));
         card:=Card;
         order:=1;
         det:=&*[c[i][2]: i in [1..m]];
         if det eq 1 then
            for i in [1..m] do
               for j in [1..#c[i][1]] do
                  pos:=c[i][1][j][1];
                  cij:=c[i][1][j][2];
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
         end if;
      end for;
   end for;
   // end creation conjugacy classes with blocks of dimension at most m

   //begin creating conjugacy classes with blocks of dimension gt m
   for i in [m+1..n] do
      T:=[];                 
      //T contains elementary divisors of dimension i (both p=p* and pp*)
      if IsOdd(i) then
         k:=i div 2;
         if k eq 0 then
            for s in {w^(j*(q-1)): j in [1..q+1]} do
               Append(~T,<0,s*IdentityMatrix(F,1),IdentityMatrix(F,1),1,Order(s),s>);
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
                     B:=FormForCompanionMatrix(f, "SU");
                     Append(~T,<2,C,B,i,Order(C),-s>);
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
               C:=CompanionMatrix(f);
               ord:=Order(C);
               C:=DiagonalJoin(C,Transpose(FrobeniusImage(C,e))^-1);
               B:=BlockMatrix(2,2,[0,IdentityMatrix(F,k),IdentityMatrix(F,k),0]);
               Append(~T,<1,C,B,k,ord,Eltseq(f)[1]^(1-q)>);
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
            Form:=Random(MatrixAlgebra(F,0));
            Repr:=Random(MatrixAlgebra(F,0));
            card:=Card;
            order:=1;
            det:=1;
            for j1 in [1..m1] do
               for j2 in [1..#c[j1]] do
         	  pos:=c[j1][j2][1];
                  cij:=c[j1][j2][2];
                  type:=S[j1][pos][1];
                  deg:=S[j1][pos][4];
                  for k in [1..cij] do
                     Form:=DiagonalJoin(Form,S[j1][pos][3]);
                     Repr:=DiagonalJoin(Repr,S[j1][pos][2]);
                     det*:=S[j1][pos][6];
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
            det:=det^-1;
            for x in T do
               if x[6] eq det then
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
               end if;
            end for;
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
         det:=T1[i][6];
         if det^2 eq 1 then
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
         end if;
         for j in [i+1..s] do
            if det*T1[j][6] eq 1 then
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
            end if;
         end for;
      end for;
   end if;

   return ConjClasses;
end function;

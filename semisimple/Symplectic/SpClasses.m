freeze;

import "../card.m": CardinalityOfClassicalGroup;
import "../form.m": ConjugatePolynomial;

// return the list of semisimple conjugacy classes of Sp(n,F)
// each output element has the form < m,c,X >, where
// X is the representative, m = order(X), c = class size of X;

// if OnlyPolynomials=true, then every output element is a list of 4-uples <f,m,t,B>, where
// the f's are the elementary divisors of X, m = multiplicity of f as el.div.,
// t = 0 (f=f* of degree 1), t=1 (f ne f*), t=2 (f=f* of degree>1)
// B is a form preserved by the companion matrix of f if t=2 (otherwise it does not matter)
// the parameter OnlyPolynomials is useful for the code Gen-Classes.m
// if f ne f*, they are both el.div., but only one of them appears in the list

SSClassesSp:=function(n,F: OnlyPolynomials:=false)

   ConjClasses:=[];
   if IsOdd(n) then
      error "n must be even";
   end if;

   Explicit:= not OnlyPolynomials;
   if Type(F) eq RngIntElt then
      F:=GF(F);
   end if;
   p:=Characteristic(F);
   Deg:=Degree(F);
   ConjPol:=ConjugatePolynomial(false);

   Gr:=GL(n,F);
   m:=n div 2;
   m1:=m div 2;
   q:=#F;
   t:=PolynomialRing(F).1;

   // first step: compute cardinality of Sp(n,F)
   if Explicit then
      Card := CardinalityOfClassicalGroup ("symplectic", n, q);
   end if;

   // case n=2 treated separately
   if n eq 2 then
      Ip:= Explicit select <1,1,Gr!IdentityMatrix(F,2)> else [<t-1,2,0,IdentityMatrix(F,2)>];
      Append(~ConjClasses,Ip);
      if p ne 2 then
         Im:= Explicit select <2,1,Gr!(-IdentityMatrix(F,2))> else [<t+1,2,0,IdentityMatrix(F,2)>];
         Append(~ConjClasses,Im);
      end if;
      X:=[x: x in F];
      Exclude(~X,0);
      Exclude(~X,1);
      Exclude(~X,-1);
      cont:=1;
      while cont le #X do
         w:=X[cont];
         Exclude(~X,w^-1);
         if Explicit then
            Append(~ConjClasses,<Order(-w),Integers()!Card/(q-1),Gr!Matrix(F,2,2,[-w,0,0,-w^-1])>);
         else
            Append(~ConjClasses, [<t+w,1,1,IdentityMatrix(F,2)>]);
         end if;
         cont+:=1;
      end while;
      for u in F do
         f:=t^2-u*t+1;
         if IsIrreducible(f) then
            x:=CompanionMatrix(f);
            B:=Matrix(F,2,2,[0,1,-1,0]);
            if Explicit then
               Append(~ConjClasses, <Order(x),Integers()!Card/(q+1),Gr!x>);
            else
               Append(~ConjClasses, [<f,1,2,B>]);
            end if;
         end if;
      end for;
      return ConjClasses;
   end if;

   // S[i] contains all elementary divisors of dimension (2*i) (p eq (t pm 1)^2, pp* or p = p*)
   // S[1] = 0 (f = t pm 1), 1 (f ne f*) or 2 (f eq f*)
   // S[2] = its matrix, S[3] matrix of the form
   // S[4] = nrows(S[2]), S[5] = order(S[2])

   // if OnlyPolynomials = true, then S[1]=0,1,2 like above, 
   // S[2]=polynomial, S[3]=matrix of the form (only f=f* is useful)
   S:=[*[]: i in [1..m1]*];
   if Explicit then
      x:=IdentityMatrix(F,2);
      B:=StandardAlternatingForm(2,F);
      Append(~S[1],<0,x,B,1,1>);
      if p ne 2 then
         x:=-IdentityMatrix(F,2);
         B:=StandardAlternatingForm(2,F);
         Append(~S[1],<0,x,B,1,2>);
      end if;
   else
      Append(~S[1],<0,t-1,IdentityMatrix(F,2)>);
      if Characteristic(F) ne 2 then
         Append(~S[1],<0,t+1,IdentityMatrix(F,2)>);
      end if;
   end if;

   //first part: remember all the possible elementary divisors of degree at most m
   for i in [1..m1] do  
      if i eq 1 then                        
         Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,i) | x ne t and x ne t+1 and x ne t-1};
      else
         Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,i)};
      end if;
      X:=[<a[1],#a>: a in Y];
      for x in X do
         //begin construction matrix of the form preserved by f=f*
         if x[2] eq 1 then
            f:=x[1];
            C:=CompanionMatrix(f);
            c:=[];
            deg:=Degree(f);
            h:=deg div 2;
            for l in [1..h-1] do
               c[l]:=C[deg,l+1];
               if l gt 1 then
                  c[l]+:= &+[C[deg,j+1]*c[l-j]: j in [1..l-1]];
               end if;
            end for;
            Insert(~c,1,1);
            d:=[];
            for i in [1..h] do
               d:=d cat c;
               Prune(~c);
            end for;
            A:=UpperTriangularMatrix(F,d);
            B:=BlockMatrix(2,2,[0,A,-Transpose(A),0]);
            //end construction matrix of the form
            if Explicit then
               Append(~S[i div 2],<2,C,B,i,Order(C)>);
            else
               Append(~S[i div 2],<2,x[1],B>);
            end if;
	 else
            if Explicit then
               f:=x[1];
               C:=CompanionMatrix(f);
               ord:=Order(C);
               C:=DiagonalJoin(C,Transpose(C^-1));
               h:=Degree(f);
               B:=BlockMatrix(2,2,[0,IdentityMatrix(F,h),-IdentityMatrix(F,h),0]);
               Append(~S[i],<1,C,B,i,ord>);
            else
               Append(~S[i],<1,x[1],IdentityMatrix(F,2*i)>);
            end if;
         end if;
      end for;
   end for;

   for i in [m1+2-(m1 mod 2)..m by 2] do
      k:=i div 2;
      for L in CartesianPower(F,k) do
         f:=&+[L[j]*(t^j+t^(i-j)): j in [1..k]];
         f+:=1+t^i-L[k]*t^k;
         if IsIrreducible(f) then
            C:=CompanionMatrix(f);
            c:=[];
            deg:=Degree(f);
            h:=deg div 2;
            for l in [1..h-1] do
               c[l]:=C[deg,l+1];
               if l gt 1 then
                  c[l]+:= &+[C[deg,j+1]*c[l-j]: j in [1..l-1]];
               end if;
            end for;
            Insert(~c,1,1);
            d:=[];
            for acaso in [1..h] do
               d:=d cat c;
               Prune(~c);
            end for; 
            A:=UpperTriangularMatrix(F,d);
            B:=BlockMatrix(2,2,[0,A,-Transpose(A),0]);
            if Explicit then
               Append(~S[k],<2,C,B,i,Order(C)>);
            else
               Append(~S[k],<2,f,B>);
            end if;
         end if;
      end for;
   end for;

   // for every partition of n, assign all possible lists of elementary divisors 
   // whose sequence of dimensions is exactly the partition
   Omega:=RestrictedPartitions(m,{1..m1});
   for P in Omega do
      array:=[Multiplicity(P,i): i in [1..m]];
      R:=<>;
      // create all possible distributions of the blocks of a given 
      // dimension to the remembered el. div.               
      for i in [1..m1] do
         Shelp:=[];
         ni:=#S[i];
         si:=array[i];
         if si eq 0 then
 	    Append(~Shelp,[]);
         else
            sumi:=ni+si;
            set:={k: k in [1..sumi-1]};
            for y in Subsets(set,ni-1) do
   	       if IsEmpty(y) then
  	          seq:=[<1,si>];
               else
	          x:=SetToSequence(y);
                  Sort(~x);
                  Insert(~x,1,0);
                  Append(~x,sumi);
                  seq:=[];
                  for k in [1..ni] do
                     if x[k+1]-x[k] gt 1 then
                        Append(~seq, <k, x[k+1]-x[k]-1>);
                     end if;
                  end for;
               end if;
               Append(~Shelp,seq);
            end for;
         end if;
         Append(~R,Shelp);
      end for;             //end creation R

      // c[i] = [<a_j,b_j>: j]; means the a_j-th el.div. of dimension i has multiplicity b_j
      C:=CartesianProduct(R);
      for c in C do
         if Explicit then
            Form:=Random(MatrixAlgebra(F,0));
            Repr:=Random(MatrixAlgebra(F,0));
            card:=Card;
            // order:= order of the element in the class
            order:=1;                         
            for i in [1..m1] do
               for j in [1..#c[i]] do
                  pos:=c[i][j][1];
                  cij:=c[i][j][2];
                  type:=S[i][pos][1];
                  deg:=S[i][pos][4];
                  for k in [1..cij] do
                     Form:=DiagonalJoin(Form,S[i][pos][3]);
                     Repr:=DiagonalJoin(Repr,S[i][pos][2]);
                  end for;
                  // dividing |Sp(n,F)| by the cardinality of the centralizer of x
                  if type eq 0 then
                     card/:=SequenceToFactorization([<p,Deg*cij^2>]);
                     for k in [1..cij] do
                        card/:=Factorization(q^(2*k)-1);
                     end for;
                  elif type eq 2 then
                     if cij gt 1 then
                        card/:=SequenceToFactorization([<p,deg*Deg*cij*(cij-1) div 4>]);
                     end if;
                     for k in [1..cij] do
                        card/:=Factorization(q^(deg*k div 2)-(-1)^k);
                     end for;
                  else
                     if cij gt 1 then
                        card/:=SequenceToFactorization([<p,deg*Deg*cij*(cij-1) div 2>]);
                     end if;
                     for k in [1..cij] do
                        card/:=Factorization(q^(deg*k)-1);
                     end for;
                  end if;
                  order:=Lcm(order,S[i][pos][5]);
               end for;
            end for;
            M:=TransformForm(Form,"symplectic": Restore:=false);
            Repr:=M^-1*Repr*M;
            Append(~ConjClasses,<order,Integers()!card,Gr!Repr>);
         else
            Cclass:=[**];
            for i in [1..m1] do
               for j in [1..#c[i]] do
                  ind:=c[i][j][1];
                  if S[i][ind][1] eq 0 then
                     Append(~Cclass,<S[i][ind][2],c[i][j][2]*2,S[i][ind][1],S[i][ind][3]>);
                  else
                     Append(~Cclass,<S[i][ind][2],c[i][j][2],S[i][ind][1],S[i][ind][3]>);
                  end if;
               end for;
            end for;
            Append(~ConjClasses,Cclass);
         end if;
      end for;
   end for;
   // end creation conjugacy classes with blocks of dimensions at most m

   // second part: elements with one el.div. of degree gt m and lt n
   for i in [m1+1..m-1] do
      T:=[];
      Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,i)};
      X:=[<a[1],#a>: a in Y];
      for x in X do
         if Explicit then
            if x[2] eq 2 then
               f:=x[1];
               C:=CompanionMatrix(f);
               ord:=Order(C);
               C:=DiagonalJoin(C,Transpose(C^-1));
               h:=Degree(f);
               B:=BlockMatrix(2,2,[0,IdentityMatrix(F,h),-IdentityMatrix(F,h),0]);
               Append(~T,<1,C,B,i,ord>);
            end if;
         else
            if x[2] eq 2 then
               Append(~T,<1,x[1],IdentityMatrix(F,2*i)>);
            end if;
         end if;
      end for;
      for L in CartesianPower(F,i) do
         f:=&+[L[j]*(t^j+t^(2*i-j)): j in [1..i]];
         f+:=1+t^(2*i)-L[i]*t^i;
         if IsIrreducible(f) then
            C:=CompanionMatrix(f);
            c:=[];
            deg:=Degree(f);
            h:=deg div 2;
            for l in [1..h-1] do
               c[l]:=C[deg,l+1];
               if l gt 1 then
                  c[l]+:= &+[C[deg,j+1]*c[l-j]: j in [1..l-1]];
               end if;
            end for;
            Insert(~c,1,1);
            d:=[];
            for acaso in [1..h] do
               d:=d cat c;
               Prune(~c);
            end for; 
            A:=UpperTriangularMatrix(F,d);
            B:=BlockMatrix(2,2,[0,A,-Transpose(A),0]);
            if Explicit then
               Append(~T,<2,C,B,2*i,Order(C)>);
            else
               Append(~T,<2,f,B>);
            end if;
         end if;
      end for;

      Omega:=Partitions(m-i);
      for P in Omega do
         array:=[Multiplicity(P,i): i in [1..m]];
         R:=<>;
         // create all possible distributions of the blocks of a 
         // given dimension to the memorized el. div.               
         for i in [1..m1] do
            Shelp:=[];
            ni:=#S[i];
            si:=array[i];
            if si eq 0 then
               Append(~Shelp,[]);
            else
               sumi:=ni+si;
               set:={k: k in [1..sumi-1]};
               for y in Subsets(set,ni-1) do
   	          if IsEmpty(y) then
		     seq:=[<1,si>];
                  else
     	             x:=SetToSequence(y);
                     Sort(~x);
                     Insert(~x,1,0);
                     Append(~x,sumi);
                     seq:=[];
                     for k in [1..ni] do
                        if x[k+1]-x[k] gt 1 then
                           Append(~seq, <k, x[k+1]-x[k]-1>);
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
               order:=1;                         // order:= order of the element in the class
               for i in [1..m1] do
                  for j in [1..#c[i]] do
                     pos:=c[i][j][1];
                     cij:=c[i][j][2];
                     type:=S[i][pos][1];
                     deg:=S[i][pos][4];
                     for k in [1..cij] do
                        Form:=DiagonalJoin(Form,S[i][pos][3]);
                        Repr:=DiagonalJoin(Repr,S[i][pos][2]);
                     end for;
                     // dividing |Sp(n,F)| by the cardinality of the centralizer of x
                     if type eq 0 then
                        card/:=SequenceToFactorization([<p,Deg*cij^2>]);
                        for k in [1..cij] do
                           card/:=Factorization(q^(2*k)-1);
                        end for;
                     elif type eq 2 then
                        if cij gt 1 then
                           card/:=SequenceToFactorization([<p,deg*Deg*cij*(cij-1) div 4>]);
                        end if;
                        for k in [1..cij] do
                           card/:=Factorization(q^(deg*k div 2)-(-1)^k);
                        end for;
                     else
                        if cij gt 1 then
                           card/:=SequenceToFactorization([<p,deg*Deg*cij*(cij-1) div 2>]);
                        end if;
                        for k in [1..cij] do
                           card/:=Factorization(q^(deg*k)-1);
                        end for;
                     end if;
                     order:=Lcm(order,S[i][pos][5]);
                  end for;
               end for;
               for x in T do
                  type:=x[1];
                  deg:=x[4];
                  Form1:=DiagonalJoin(Form,x[3]);
                  Repr1:=DiagonalJoin(Repr,x[2]);
                  M:=TransformForm(Form1,"symplectic": Restore:=false);
                  Repr1:=M^-1*Repr1*M;
                  order1:=Lcm(order,x[5]);
                  if type eq 2 then
                     card1:=card/Factorization(q^(deg div 2)+1);
                  else
                     card1:=card/Factorization(q^deg-1);
                  end if;
                  Append(~ConjClasses,<order1, Integers()!card1, Gr!Repr1>);
               end for;
            else
               Cclass:=[**];
               for i in [1..m1] do
                  for j in [1..#c[i]] do
                     ind:=c[i][j][1];
                     if S[i][ind][1] eq 0 then
                        Append(~Cclass,<S[i][ind][2], c[i][j][2]*2, S[i][ind][1], S[i][ind][3]>);
                     else
                        Append(~Cclass,<S[i][ind][2],c[i][j][2],S[i][ind][1],S[i][ind][3]>);
                     end if;
                  end for;
               end for;
               for x in T do
                  Append(~ConjClasses, Append(Cclass,<x[2],1,x[1],x[3]>));
               end for;
            end if;
         end for;
      end for;
   end for;

   // last part: elements with a unique el.div. of degree n
   Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,m)};
   X:=[<a[1],#a>: a in Y];
   for x in X do
      if Explicit then
         if x[2] eq 2 then
            f:=x[1];
            C:=CompanionMatrix(f);
            ord:=Order(C);
            C:=DiagonalJoin(C,Transpose(C^-1));
            B:=BlockMatrix(2,2,[0,IdentityMatrix(F,m),-IdentityMatrix(F,m),0]);
            M:=TransformForm(B,"symplectic": Restore:=false);
            card:=Card/Factorization(q^(Degree(f))-1);
            Append(~ConjClasses,<ord, Integers()!card, Gr!(M^-1*C*M)>);
         end if;
      else
         if x[2] eq 2 then
            Append(~ConjClasses,[*<x[1],1,1,IdentityMatrix(F,n)>*]);
         end if;
      end if;
   end for;
   for L in CartesianPower(F,m) do
      f:=&+[L[i]*(t^i+t^(n-i)): i in [1..m]];
      f+:=1+t^n-L[m]*t^m;
      if IsIrreducible(f) then
         C:=CompanionMatrix(f);
         c:=[];
         deg:=Degree(f);
         h:=deg div 2;
         for l in [1..h-1] do
            c[l]:=C[deg,l+1];
            if l gt 1 then
               c[l]+:= &+[C[deg,j+1]*c[l-j]: j in [1..l-1]];
            end if;
         end for;
         Insert(~c,1,1);
         d:=[];
         for acaso in [1..h] do
            d:=d cat c;
            Prune(~c);
         end for; 
         A:=UpperTriangularMatrix(F,d);
         B:=BlockMatrix(2,2,[0,A,-Transpose(A),0]);
         M:=TransformForm(B,"symplectic": Restore:=false);
         if Explicit then
            card:=Card/Factorization(q^h+1);
            Append(~ConjClasses, <Order(C), Integers()!card, Gr!(M^-1*C*M)>);
         else
            Append(~ConjClasses,[*<f,1,2,B>*]);
         end if;
      end if;
   end for;

   return ConjClasses;
end function;

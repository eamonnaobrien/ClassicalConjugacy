freeze;

import "../card.m": CardinalityOfClassicalGroup;
import "../form.m": ConjugatePolynomial;

// Returns the list of semisimple conjugacy classes of GO(n,F), 
// n and |F| odd
// each output element has the form < m,c,X >, where
// X is the representative, m = order(X), c = class size of X;

// if OnlyPolynomials=true, then every output element is a list of 4-uples <f,m,t,B>, where
// the f's are the elementary divisors of X, m = multiplicity of f as el.div.,
// t = 0 (f=f* of degree 1), t=1 (f ne f*), t=2 (f=f* of degree>1)
// B is a form preserved by the companion matrix of f if t=2 (otherwise it does not matter)
// the parameter OnlyPolynomials is useful for the code Gen-Classes.m
// if f ne f*, they are both el.div., but only one of them appears in the list

GOClasses:=function(n,F: OnlyPolynomials:=false)

   ConjClasses:=[];
   if IsEven(n) then
      error "n must be odd";
   end if;
   if n lt 3 then
      error "Invalid dimension -- should be at least 3";
   end if;

   if Type(F) eq RngIntElt then
      F:=GF(F);
   end if;
   if Characteristic(F) eq 2 then
      error "Field must have odd characteristic";
   end if;

   Explicit:= not OnlyPolynomials;
   t:=PolynomialRing(F).1;
   Gr:=GL(n,F);

   m:=n div 2;
   q:=#F;
   indtype:=0;
   if q mod 4 eq 3 then
      indtype:=1;
   end if;
   ConjPol:=ConjugatePolynomial(false);

   // S[i+1] contains all el.div. of dimension (2*i) (pp* or p = p*)
   // S[1] of dimension 1 (p = t pm 1)
   // for x in S[i]:
   // x[1] = 0 (f = t pm 1), 1 (f ne f*) or 2 (f eq f*)
   // x[2] = its matrix, x[3] matrix of the form
   // x[4] = nrows(S[2]) or nrows(S[2])/2 (case pp*), x[5] = order(x[2])

   // if OnlyPolynomials=true, then S[1]=0,1,2 like above, S[2]=polynomial, 
   // S[3]=matrix of the form (only f=f* is useful)
   S:=[*[]: i in [1..n div 4 +1]*];
   x:=IdentityMatrix(F,1);
   w:=PrimitiveElement(F);
   if Explicit then
      Append(~S[1],<0,x,x,1,1>);
      Append(~S[1],<0,-x,x,1,2>);
   else
      Append(~S[1],<0,t-1, IdentityMatrix(F,1)>);
      Append(~S[1],<0,t+1, IdentityMatrix(F,1)>);
   end if;

   p:=Characteristic(F);
   Deg:=Degree(F);
   Card:=Factorization(1);

   if Explicit then 
      // first step: compute cardinality of GO(n,F)
      Card := CardinalityOfClassicalGroup ("orthogonal", n, q);

      // FactCard[1][i] = |GOPlus(i,F)|, FactCard[2][i] = |GOMinus(i,F)| 
      // or simply |GO(i,F)| if i is odd
      L1 := <>;
      L2 := <>;
      for  i in [1..n] do
         if IsOdd (i) then
           a := CardinalityOfClassicalGroup ("orthogonal", i, q);
           Append (~L1, a);
           Append (~L2, a);
        else
           b := CardinalityOfClassicalGroup ("orthogonalplus", i, q);
           Append (~L1,b);
           c := CardinalityOfClassicalGroup ("orthogonalminus", i, q);
           Append (~L2,c);
         end if;
      end for;
      FactCard:=[L1,L2];
    end if;

   //remember all possible elementary divisors of degree less than n div 2
   for i in [1..n div 4] do
      if i eq 1 then                        
         Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,i) | 
                x ne t and x ne t+1 and x ne t-1};
      else
         Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,i)};
      end if;
      X:=[<a[1],#a>: a in Y];
      for x in X do
         //begin construction matrix of the form preserved by p=p*
         if x[2] eq 1 then
            f:=x[1];
            C:=CompanionMatrix(f);
            c:=[];
            deg:=Degree(f);
            h:=deg div 2;
            c:=[1,C[deg,2]];
            if h eq 1 then
               c:=[1,C[deg,2]/2];
            end if;
            if h gt 1 then
               c[3]:=C[deg,2]*c[2]+C[deg,3]-1;
            end if;
            if h gt 2 then
               for l in [3..h] do
	          c[l+1]:=&+[C[deg,j+1]*c[l-j+1]: j in [1..l]];
               end for;
            end if;
            Reverse(~c);
            c:=c cat[0: i in [1..h-1]];
            d:=[];
            for i in [1..deg] do
               d:=c cat d;
               Remove(~c,1);
            end for;
            B:=SymmetricMatrix(F,d);
            //end construction matrix of the form
            if Explicit then
               Append(~S[(i div 2)+1],<2,C,B,i,Order(C)>);
            else
               Append(~S[i div 2 +1],<2,f,B>);
            end if;
         else
            f:=x[1];
            if Explicit then
               C:=CompanionMatrix(f);
               ord:=Order(C);
               C:=DiagonalJoin(C,Transpose(C^-1));
               h:=Degree(f);
               B:=BlockMatrix(2,2,[0,IdentityMatrix(F,h),IdentityMatrix(F,h),0]);
               Append(~S[i+1],<1,C,B,i,ord>);
            else
               Append(~S[i+1],<1,f,IdentityMatrix(F,2*i)>);
            end if;
         end if;
      end for;
   end for;

   for i in [(n div 4)+2-((n div 4) mod 2)..(n div 4)*2 by 2] do
      k:=i div 2;
      for L in CartesianPower(F,k) do
         f:=&+[L[j]*(t^j+t^(i-j)): j in [1..k]];
         f:=f+1+t^i-L[k]*t^k;
         if IsIrreducible(f) then
            C:=CompanionMatrix(f);
            c:=[];
            deg:=Degree(f);
            h:=deg div 2;
            c:=[1,C[deg,2]];
            if h eq 1 then
               c:=[1,C[deg,2]/2];
            end if;
            if h gt 1 then
               c[3]:=C[deg,2]*c[2]+C[deg,3]-1;
            end if;
            if h gt 2 then
               for l in [3..h] do
         	  c[l+1]:=&+[C[deg,j+1]*c[l-j+1]: j in [1..l]];
               end for;
            end if;
            Reverse(~c);
            c:=c cat[0: i in [1..h-1]];
            d:=[];
            for i in [1..deg] do
               d:=c cat d;
               Remove(~c,1);
            end for;
            B:=SymmetricMatrix(F,d);
            if Explicit then
               Append(~S[i div 2+1],<2,C,B,i,Order(C)>);
            else
               Append(~S[i div 2+1],<2,f,B>);
            end if;
         end if;
      end for;
   end for;

   // for every partition of n, assign all possible lists of el.div.
   // whose sequence of dimensions is exactly the partition
   Omega:=RestrictedPartitions(n,{1} join {x: x in [2..m by 2]});
   for P in Omega do
      array:=[Multiplicity(P,1)] cat [Multiplicity(P,i): i in [2..m by 2]];
      R:=<>;                           
      for i in [1..n div 4 +1] do
         Shelp:=[];
         ni:=#S[i];
         si:=array[i];
         sumi:=ni+si;
         set:={k: k in [1..sumi-1]};
         for y in Subsets(set,ni-1) do
            if IsEmpty(y) then
               if si eq 0 then
                  seq:=[];
               else
                  seq:=[<1,si>];
               end if;
            else
               x:=SetToSequence(y);
               Sort(~x);
               Insert(~x,1,0);
               Append(~x, sumi);
               seq:=[];
               for k in [1..ni] do
  	          if x[k+1]-x[k] gt 1 then
                      Append(~seq, <k, x[k+1]-x[k]-1>);
                   end if;
               end for;
            end if;
            Append(~Shelp,seq);
         end for;
         Append(~R,Shelp);
      end for;

      // c[i] = [<a_j,b_j>: j]: the a_j-th el.div. of dimension i has multiplicity b_j
      C:=CartesianProduct(R);
      for c in C do
         if Explicit then
            Form:=ZeroMatrix(F,0,0);
            Repr:=ZeroMatrix(F,0,0);
            card:=Card;
            order:=1;
            for i in [1..n div 4+1] do
               for j in [1..#c[i]] do
               pos:=c[i][j][1];
               cij:=c[i][j][2];
               type:=S[i][pos][1];
               deg:=S[i][pos][4];
               for k in [1..cij] do
            	  Form:=DiagonalJoin(Form,S[i][pos][3]);
                  Repr:=DiagonalJoin(Repr,S[i][pos][2]);
               end for;
               // dividing |O(n,F)| by the cardinality of the centralizer of x
               if type eq 0 then
                  card/:=FactCard[1+indtype*(cij mod 4 div 2)][cij];
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
            M:=TransformForm(Form,"orthogonal": Restore:=false);
            Append(~ConjClasses,<order,Integers()!card, Gr!(M^-1*Repr*M)>);
            //conj.cl. in GL splitting in more conj.cl. in GO
            if #c[1] ge 2 then
               c1:=c[1][1][2];   // multiplicity of t-1
               c2:=c[1][2][2];   // multiplicity if t+1
               if c1 ge 1 and c2 ge 1 then
                  if IsEven(c1) then
                     Form[1][1]:=w;
                     card*:=FactCard[1+indtype*(c1 mod 4 div 2)][c1];
                     card/:=FactCard[2-indtype*(c1 mod 4 div 2)][c1];
                  else
                    Form[c1+1][c1+1]:=w;
                    card*:=FactCard[1+indtype*(c2 mod 4 div 2)][c2];
                    card/:=FactCard[2-indtype*(c2 mod 4 div 2)][c2];
                  end if;
                  M:=TransformForm(Form,"orthogonal": Restore:=false);
                  Append(~ConjClasses,<order, Integers()!card,Gr!(M^-1*Repr*M)>);
               end if;
            end if;
         else
            Cclass:=[**];
            for i in [1..n div 4+1] do
               for j in [1..#c[i]] do
               ind:=c[i][j][1];
               Append(~Cclass, <S[i][ind][2],c[i][j][2],S[i][ind][1],S[i][ind][3]>);
               end for;
            end for;
            Append(~ConjClasses,Cclass);
         end if;
      end for;
   end for;
   // end creation conjugacy classes with blocks of dimension at most n div 2

   //begin constructing conjugacy classes with blocks of dimension gt n div 2
   for i in [n div 4 +1..n div 2] do
      //T contains elementary divisors of dimension 2*i
      T:=[];
      if i eq 1 then                        
         Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,i) |
                 x ne t and x ne t+1 and x ne t-1};
      else
         Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,i)};
      end if;
      X:=[<a[1],#a>: a in Y];
      for x in X do
         if x[2] eq 2 then
            if Explicit then
               C:=CompanionMatrix(x[1]);
               ord:=Order(C);
               C:=DiagonalJoin(C,Transpose(C^-1));
               B:=BlockMatrix(2,2,[0,IdentityMatrix(F,i),IdentityMatrix(F,i),0]);
               Append(~T,<1,C,B,i,ord>);
            else
               Append(~T,<1,x[1],IdentityMatrix(F,2*i)>);
            end if;
         end if;
      end for;
      for L in CartesianPower(F,i) do
         f:=&+[L[j]*(t^j+t^(2*i-j)): j in [1..i]];
         f:=f+1+t^(2*i)-L[i]*t^i;
         if IsIrreducible(f) then
            C:=CompanionMatrix(f);
            c:=[];
            deg:=Degree(f);
            h:=deg div 2;
            c:=[1,C[deg,2]];
            if h eq 1 then
               c:=[1,C[deg,2]/2];
            end if;
            if h gt 1 then
               c[3]:=C[deg,2]*c[2]+C[deg,3]-1;
            end if;
            if h gt 2 then
               for l in [3..h] do
              	  c[l+1]:=&+[C[deg,j+1]*c[l-j+1]: j in [1..l]];
               end for;
            end if;
            Reverse(~c);
            c:=c cat[0: i in [1..h-1]];
            d:=[];
            for i in [1..deg] do
               d:=c cat d;
               Remove(~c,1);
            end for;
            B:=SymmetricMatrix(F,d);
            if Explicit then
               Append(~T,<2,C,B,2*i,Order(C)>);
            else
               Append(~T,<2,f,B>);
            end if;
	 end if;
      end for;

      Omega:=RestrictedPartitions(n-2*i,{1} join {x: x in [2..n-2*i by 2]});
      for P in Omega do           
         array:=[Multiplicity(P,1)] cat [Multiplicity(P,j): j in [2..n div 2 by 2]];
         R:=<>;                           
         for j in [1..n div 4+1] do
            Shelp:=[];
            ni:=#S[j];
            si:=array[j];
            sumi:=si+ni;
            set:={k: k in [1..ni+si-1]};
            for y in Subsets(set,ni-1) do
               if IsEmpty(y) then
                  if si eq 0 then
                     seq:=[];
                  else
              	     seq:=[<1,si>];
                  end if;
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
            Append(~R,Shelp);
         end for;

         // c[i] = [<a_j,b_j>: j]: the a_j-th el.div. of dimension i has multiplicity b_j
         C:=CartesianProduct(R);
         for c in C do
            if Explicit then
               Form:=ZeroMatrix(F,0,0);
               Repr:=ZeroMatrix(F,0,0);
               card:=Card;
               order:=1; 
               for j1 in [1..n div 4+1] do
                  for j2 in [1..#c[j1]] do
                     pos:=c[j1][j2][1];
                     cij:=c[j1][j2][2];
                     type:=S[j1][pos][1];
                     deg:=S[j1][pos][4];
                     for k in [1..cij] do
                  	Form:=DiagonalJoin(Form,S[j1][pos][3]);
                        Repr:=DiagonalJoin(Repr,S[j1][pos][2]);
                     end for;
                     // dividing |GO(n,F)| by the cardinality of the centralizer of x
                     if type eq 0 then
                        card/:=FactCard[1+indtype*(cij mod 4 div 2)][cij];
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
                     order:=Lcm(order,S[j1][pos][5]);
                  end for;
               end for;
               for x in T do
                  type:=x[1];
                  deg:=x[4];
                  Form1:=DiagonalJoin(Form,x[3]);
                  Repr1:=DiagonalJoin(Repr,x[2]);
                  M:=TransformForm(Form1,"orthogonal": Restore:=false);
                  order1:=Lcm(order,x[5]);
                  if type eq 2 then
                     card1:=card/Factorization(q^(deg div 2)+1);
                  else
                     card1:=card/Factorization(q^deg-1);
                  end if;
                  Append(~ConjClasses,<order1, Integers()!card1, Gr!(M^-1*Repr1*M)>);
                  //conj.cl. in GL splitting in more conj.cl. in GO
                  if #c[1] ge 2 then
                     c1:=c[1][1][2];   // multiplicity of t-1
                     c2:=c[1][2][2];   // multiplicity if t+1
                     if c1 ge 1 and c2 ge 1 then
                        if IsEven(c1) then
                           Form1[1][1]:=w;
                           card1*:=FactCard[1+indtype*(c1 mod 4 div 2)][c1];
                           card1/:=FactCard[2-indtype*(c1 mod 4 div 2)][c1];
                        else
                           Form1[c1+1][c1+1]:=w;
                           card1*:=FactCard[1+indtype*(c2 mod 4 div 2)][c2];
                           card1/:=FactCard[2-indtype*(c2 mod 4 div 2)][c2];
                        end if;
                        M:=TransformForm(Form1,"orthogonal": Restore:=false);
                        Append(~ConjClasses,<order1, Integers()!card1,Gr!(M^-1*Repr1*M)>);
                     end if;
                  end if;
               end for;
            else
               Cclass:=[**];
               for j1 in [1..n div 4+1] do
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
   end for;

   return ConjClasses;
end function;

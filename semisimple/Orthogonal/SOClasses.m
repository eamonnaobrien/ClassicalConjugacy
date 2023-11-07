freeze;

import "../card.m": CardinalityOfClassicalGroup;
import "../form.m": ConjugatePolynomial;

// Return the list of semisimple conjugacy classes of SO(n,F), 
// n and |F| odd
// A class is identified with a triple <m,n,X >, 
// with X representative of the class in SO(n,F),
// m = Order(X), n = cardinality of the class
// In all comments, el.div. = elementary divisors

// Elements of SO(n,F) are the elements of GO(n,F) whose 
// el.div. t+1 has even multiplicity.
// Thus el.div. t-1 and t+1 with multiplicity 2 are considered 
// together with other el.div. of dimension 2.
// At the end a block of dimension 1 of el.div. t-1 is added

SOClasses:=function(n,F)

   ConjClasses:=[];
   if IsEven(n) then
      error "n must be odd";
   end if;
   if n lt 3 then
      error "invalid dimension---should be at least 3";
   end if;

   if Type(F) eq RngIntElt then
      F:=GF(F);
   end if;
   if Characteristic(F) eq 2 then
      error "Char(F) must be even";
   end if;

   t:=PolynomialRing(F).1;
   Gr:=GL(n,F);

   m:=n div 2;
   q:=#F;
   // indicator of type (for compute cardinality)
   indtype:=0;
   if q mod 4 eq 3 then
      indtype:=1;
   end if;
   ConjPol:=ConjugatePolynomial(false);

   // S[i] contains all el.div. of dimension (2*i) (pp* or p = p*)
   // S[1] contains also t-1 (multiplicity 2) and t+1 (multiplicity 2)
   // for x in S[i]:
   // x[1] = 0 (f = t pm 1), 1 (f ne f*) or 2 (f eq f*)
   // x[2] = its matrix, x[3] matrix of the form
   // x[4] = nrows(S[2]) or nrows(S[2])/2 (case pp*), x[5] = order(x[2])
   S:=[*[]: i in [1..n div 4 +1]*];
   x:=IdentityMatrix(F,2);
   y:=DiagonalMatrix(F,[-1,1]);
   w:=PrimitiveElement(F);
   if n gt 4 then
      Append(~S[1],<0,x,y,1,1>);
      Append(~S[1],<0,-x,y,1,2>);
   end if;

   p:=Characteristic(F);
   Deg:=Degree(F);

   // first step: compute cardinality of GO(n,F)
   Card := CardinalityOfClassicalGroup ("orthogonal", n, q);
   // FactCard[1][i] = |GOPlus(i,F)|, FactCard[2][i] = |GOMinus(i,F)| or simply |GO(i,F)| if i is odd
   L1 := <>;
   L2 := <>;
   for i in [1..n] do
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
         if x[2] eq 1 then
            //begin construction matrix of the form preserved by p=p*
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
            Append(~S[i div 2],<2,C,B,i,Order(C)>);
         else
            f:=x[1];
            C:=CompanionMatrix(f);
            ord:=Order(C);
            C:=DiagonalJoin(C,Transpose(C^-1));
            h:=Degree(f);
            B:=BlockMatrix(2,2,[0,IdentityMatrix(F,h),IdentityMatrix(F,h),0]);
            Append(~S[i],<1,C,B,i,ord>);
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
            Append(~S[i div 2],<2,C,B,i,Order(C)>);
         end if;
      end for;
   end for;

   // for every partition of n, assign all possible lists of el.div. 
   // whose sequence of dimensions is exactly the partition
   Omega:=RestrictedPartitions(m,{x: x in [1..m div 2]});
   for P in Omega do
      array:=[Multiplicity(P,i): i in [1..m div 2]];
      R:=<>;                           
      for i in [1..m div 2] do
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
         Form:=ZeroMatrix(F,0,0);
         Repr:=ZeroMatrix(F,0,0);
         card:=Card;
         order:=1;
         for i in [1..m div 2] do
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
                  card/:=FactCard[1][cij*2];
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
         // adding the t-1 el.div.
         Form:=DiagonalJoin(Form,IdentityMatrix(F,1));
         Repr:=DiagonalJoin(Repr,IdentityMatrix(F,1));
         if #c[1] ge 1 and c[1][1][1] eq 1 then    // i.e. if t-1 was already an el.div.
            cij:=c[1][1][2];                       // cij = "old" multiplicity of t-1 / 2
            card*:=FactCard[1][cij*2];
            card/:=FactCard[1][cij*2+1];
            M:=TransformForm(Form,"orthogonal": Restore:=false);
            Append(~ConjClasses,<order,Integers()!card,Gr!(M^-1*Repr*M)>);
            if #c[1] ge 2 and c[1][2][1] eq 2 then    // i.e. if t+1 is el.div.
               cij:=c[1][2][2];                       // cij = multiplicity of t+1 /2
               Form[2*c[1][1][2]+1][2*c[1][1][2]+1]:=-w;
               card*:=FactCard[1][cij*2];
               card/:=FactCard[2][cij*2];
               M:=TransformForm(Form,"orthogonal": Restore:=false);
               Append(~ConjClasses, <order,Integers()!card,Gr!(M^-1*Repr*M)>);
            end if;
         else
            card/:=SequenceToFactorization([<2,1>]);
            M:=TransformForm(Form,"orthogonal": Restore:=false);
            Append(~ConjClasses, <order, Integers()!card, Gr!(M^-1*Repr*M)>);
            if #c[1] ge 1 and c[1][1][1] eq 2 then     // i.e. if t+1 is el.div.
               cij:=c[1][1][2];                        // cij = multiplicity of t+1 /2
               Form[1][1]:=-w;
               card*:=FactCard[1][cij*2];
               card/:=FactCard[2][cij*2];
               M:=TransformForm(Form,"orthogonal": Restore:=false);
               Append(~ConjClasses, <order,Integers()!card,Gr!(M^-1*Repr*M)>);
            end if;
         end if;
      end for;
   end for;
   // end creation conjugacy classes with blocks of dimension at most n div 2

   //begin creation conjugacy classes with blocks of dimension gt n div 2
   for i in [m div 2 +1..m] do
      //T contains elementary divisors of dimension 2*i (both p=p* and pp*)
      T:=[];
      if i eq 1 then                        
         Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,i) | 
                x ne t and x ne t+1 and x ne t-1};
         Append(~T,<0,IdentityMatrix(F,2),DiagonalMatrix(F,[1,-1]),1,1>);
         Append(~T,<0,-IdentityMatrix(F,2),DiagonalMatrix(F,[1,-1]),1,2>);
      else
         Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,i)};
      end if;
      X:=[<a[1],#a>: a in Y];
      for x in X do
         if x[2] eq 2 then
            C:=CompanionMatrix(x[1]);
            ord:=Order(C);
            C:=DiagonalJoin(C,Transpose(C^-1));
            B:=BlockMatrix(2,2,[0,IdentityMatrix(F,i),IdentityMatrix(F,i),0]);
            Append(~T,<1,C,B,i,ord>);
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
            Append(~T,<2,C,B,2*i,Order(C)>);
	 end if;
      end for;

      Omega:=RestrictedPartitions(m-i,{x: x in [1..m-i]});
      for P in Omega do           
         array:=[Multiplicity(P,j): j in [1..m]];
         R:=<>;                           
         for j in [1..n div 4] do
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

         // c[i] = [<a_j,b_j>: j]; means the a_j-th el.div. of dimension i has multiplicity b_j
         C:=CartesianProduct(R);
         for c in C do
            if i eq m then
               for x in T do
                  if x[1] eq 0 and x[5] eq 1 then         // i.e. if the el.div. is t-1
                     Append(~ConjClasses,<1,1,Gr!IdentityMatrix(F,n)>);
                  else
                     Form:=DiagonalJoin(IdentityMatrix(F,1),x[3]);
                     Repr:=DiagonalJoin(IdentityMatrix(F,1),x[2]);
                     M:=TransformForm(Form,"orthogonal": Restore:=false);
                     card:=Card;
                     type:=x[1];
                     order:=x[5];
                     deg:=x[4];
                     if type eq 0 then
                        card/:=FactCard[1][2];     // this case holds only if n=3, so cij=1
                     elif type eq 1 then
                        card/:=Factorization(q^deg-1);
                     else
                        card/:=Factorization(q^(deg div 2)+1);
                     end if;
                     card/:=SequenceToFactorization([<2,1>]);
                     Append(~ConjClasses, <order, Integers()!card, Gr!(M^-1*Repr*M)>);
                     if x[1] eq 0 and x[5] eq 2 then            // the el.div. is t+1
                        Form[2,2]*:=w;
                        card*:=FactCard[1][2];
                        card/:=FactCard[2][2];
                        M:=TransformForm(Form,"orthogonal": Restore:=false);
                        Append(~ConjClasses, <order, Integers()!card, Gr!(M^-1*Repr*M)>);
                     end if;
                  end if;
              end for;
            else
               Form:=ZeroMatrix(F,0,0);
               Repr:=ZeroMatrix(F,0,0);
               card:=Card;
               order:=1; 
               for j1 in [1..n div 4] do
                  for j2 in [1..#c[j1]] do
                     pos:=c[j1][j2][1];
                     cij:=c[j1][j2][2];
                     type:=S[j1][pos][1];
                     deg:=S[j1][pos][4];
                     for k in [1..cij] do
                        Form:=DiagonalJoin(Form,S[j1][pos][3]);
                        Repr:=DiagonalJoin(Repr,S[j1][pos][2]);
                     end for;
                     // dividing |SO(n,F)| by the cardinality of the centralizer of x
                     if type eq 0 then
                        card/:=FactCard[1][cij*2];
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
                  order1:=Lcm(order,x[5]);
                  if type eq 2 then
                     card1:=card/Factorization(q^(deg div 2)+1);
                  else
                     card1:=card/Factorization(q^deg-1);
                  end if;
                  Form1:=DiagonalJoin(Form1,IdentityMatrix(F,1));
                  Repr1:=DiagonalJoin(Repr1,IdentityMatrix(F,1));
                  if #c[1] ge 1 and c[1][1][1] eq 1 then        // if t-1 was already an el.div.
                     cij:=c[1][1][2];                           // cij = "old" multiplicity of t-1 / 2
                     card1*:=FactCard[1][cij*2];
                     card1/:=FactCard[1][cij*2+1];
                     M:=TransformForm(Form1,"orthogonal": Restore:=false);
                     Append(~ConjClasses,<order1,Integers()!card1,Gr!(M^-1*Repr1*M)>);
                     if #c[1] ge 2 and c[1][2][1] eq 2 then     // if t+1 is el.div.
                        cij:=c[1][2][2];                        // cij = multiplicity of t+1 /2
                        Form1[2*c[1][1][2]+1][2*c[1][1][2]+1]:=-w;
                        card1*:=FactCard[1][cij*2];
                        card1/:=FactCard[2][cij*2];
                        M:=TransformForm(Form1,"orthogonal": Restore:=false);
                        Append(~ConjClasses, <order1,Integers()!card1,Gr!(M^-1*Repr1*M)>);
                     end if;
                  else
                     card1/:=SequenceToFactorization([<2,1>]);
                     M:=TransformForm(Form1,"orthogonal": Restore:=false);
                     Append(~ConjClasses, <order1, Integers()!card1, Gr!(M^-1*Repr1*M)>);
                     if #c[1] ge 1 and c[1][1][1] eq 2 then     // if t+1 is el.div.
                        cij:=c[1][1][2];                        // cij = multiplicity of t+1 /2
                        Form1[1][1]:=-w;
                        card1*:=FactCard[1][cij*2];
                        card1/:=FactCard[2][cij*2];
                        M:=TransformForm(Form1,"orthogonal": Restore:=false);
                        Append(~ConjClasses, <order1,Integers()!card1,Gr!(M^-1*Repr1*M)>);
                     end if;
                  end if;
               end for;
            end if;
         end for;
      end for;
   end for;

   return ConjClasses;
end function;

freeze;

import "../card.m": CardinalityOfClassicalGroup;
import "../form.m": ConjugatePolynomial;

// Returns the list of semisimple conjugacy classes of GO(n,F), n even, |F| odd
// each output element has the form < m,c,X >, where
// X is the representative, m = order(X), c = class size of X;

// if OnlyPolynomials=true, then every output element is a list of 4-uples <f,m,t,B>, where
// the f's are the elementary divisors of X, m = multiplicity of f as el.div.,
// t = 0 (f=f* of degree 1), t=1 (f ne f*), t=2 (f=f* of degree>1)
// B is a form preserved by the companion matrix of f if t=2 (otherwise it does not matter)
// the parameter OnlyPolynomials is useful for the code Gen-Classes.m
// if f ne f*, they are both el.div., but only one of them appears in the list

GOpmClasses:=function(n,F,type: OnlyPolynomials:=false)

   if Type(F) eq RngIntElt then
      F:=GF(F);
   end if;
   ConjClasses:=[* *];
   q:=#F;
   Gr:=GL(n,F);
   Deg:=Degree(F);
   p:=Characteristic(F);
   ConjPol:=ConjugatePolynomial(false);

   if IsEven(q) then
      error "char F must be odd";
   end if;

   if IsOdd(n) then
      error "n must be even";
   end if;

   if not type in {"plus", "minus"} then
      error "type must be either plus or minus";
   end if;

   Explicit:= not OnlyPolynomials;
   t:=PolynomialRing(F).1;
   w:=PrimitiveElement(F);
   Card:=1;
   m:=n div 2;

   if type eq "plus" then
      type1:="orthogonalplus";
   else
      type1:="orthogonalminus";
   end if;

   // first step: compute cardinality of GO(n,F)
   if Explicit then 
      call := type eq "plus" select "orthogonalplus" else "orthogonalminus";
      Card := CardinalityOfClassicalGroup (call, n, q);
   end if;

   // case n=2 treated separately
   if n eq 2 then
      Ip:= Explicit select <1,1,Gr!IdentityMatrix(F,2)> else [<t-1,2,0,IdentityMatrix(F,2)>];
      Im:= Explicit select <2,1,Gr!(-IdentityMatrix(F,2))> else [<t+1,2,0,IdentityMatrix(F,2)>];
      Append(~ConjClasses,Ip);
      Append(~ConjClasses,Im);
      if Explicit then
         if type eq "plus" then
            Append(~ConjClasses,<2,Integers()!Card/4,Gr!Matrix(F,2,2,[0,w,w^-1,0])>);
            Append(~ConjClasses,<2,Integers()!Card/4,Gr!Matrix(F,2,2,[0,w^2,w^-2,0])>);
         else
   	    repr:=Matrix(F,2,2,[1,0,0,-1]);
            if q mod 4 eq 1 then
               x1:=Matrix(F,2,2,[1,0,0,w]);
               x2:=Matrix(F,2,2,[w,0,0,1]);
            else
               x1:=Matrix(F,2,2,[1,0,0,1]);
               x2:=Matrix(F,2,2,[w,0,0,w]);
            end if;
            M:=TransformForm(x1,"orthogonalminus": Restore:=false);
            Append(~ConjClasses,<2,Integers()!Card/4,Gr!(M^-1*repr*M)>);
            M:=TransformForm(x2,"orthogonalminus": Restore:=false);
            Append(~ConjClasses,<2,Integers()!Card/4,Gr!(M^-1*repr*M)>);
         end if;
      else
         Append(~ConjClasses, [<t-1,1,0,IdentityMatrix(F,1)>, <t+1,1,0,IdentityMatrix(F,1)>]);
      end if;
      if type eq "plus" then
         X:=[x: x in F];
         Exclude(~X,0);
         Exclude(~X,1);
         Exclude(~X,-1);
         cont:=1;
         while cont le #X do
	    w:=X[cont];
            Exclude(~X,w^-1);
            if Explicit then
               Append(~ConjClasses,<Order(-w),Integers()!Card/(q-1),
                                  Gr!Matrix(F,2,2,[-w,0,0,-w^-1])>);
            else
               Append(~ConjClasses, [<t+w,1,1,IdentityMatrix(F,2)>]);
            end if;
            cont+:=1;
         end while;
      else
         for u in F do
            f:=t^2-u*t+1;
            if IsIrreducible(f) then
               x:=CompanionMatrix(f);
               B:=Matrix(F,2,2,[1,u/2,u/2,1]);
               M:=TransformForm(B,"orthogonalminus": Restore:=false);
               if Explicit then
                  Append(~ConjClasses, <Order(x),Integers()!Card/(q+1),Gr!(M^-1*x*M)>);
               else
                  Append(~ConjClasses, [<f,1,2,B>]);
               end if;
            end if;
         end for;
      end if;
      return ConjClasses;
   end if;
   //end separate case n=2

   //begin general case
   m1:=m div 2;
   // Sp[i] contains all el.div. of dimension (2*i) and type "orthogonalplus"
   // for x in Sp[i]:
   // x[1] = 0 (f = t pm 1), 1 (f ne f*) or 2 (f eq f*)
   // x[2] = its matrix, x[3] matrix of the form
   // x[4] = nrows(S[2]) or nrows(S[2])/2 (case pp*), x[5] = order(x[2])
   // Sm same for type "orthogonalminus"
   Sm:=[*[]: i in [1..m1]*];
   Sp:=[*[]: i in [1..m1]*];
   // MultSp[i] = #Sp[i], MultSm[i] = #Sm[i]
   MultSp:=[0: i in [1..m1]];
   MultSm:=[0: i in [1..m1]];

   // if OnlyPolynomials=true, then 
   // Sp[1]=0,1,2 like above, Sp[2]=polynomial, 
   // Sp[3]=matrix of the form (only f=f* is useful)

   if Explicit then 
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

   // memorizing all possible elementary divisors of degree less than m div 2
   for i in [1..m1] do
      if i eq 1 then                        
         Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,i) |
                x ne t and x ne t+1 and x ne t-1};
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
            h:=i div 2;
            c:=[1,C[i,2]];
            if h eq 1 then
               c:=[1,C[i,2]/2];
            end if;
            if h gt 1 then
               c[3]:=C[i,2]*c[2]+C[i,3]-1;
            end if;
            if h gt 2 then
               for l in [3..h] do
                  c[l+1]:=&+[C[i,j+1]*c[l-j+1]: j in [1..l]];
               end for;
            end if;
            Reverse(~c);
            c:=c cat[0: v in [1..h-1]];
            d:=[];
            for v in [1..i] do
               d:=c cat d;
               Remove(~c,1);
            end for;
            B:=SymmetricMatrix(F,d);
            //end construction matrix of the form  
            if Explicit then
               Append(~Sm[i div 2],<2,C,B,i,Order(C)>);
            else
               Append(~Sm[i div 2],<2,f,B>);
            end if;
            MultSm[i div 2]+:=1;
         else
            if Explicit then
               f:=x[1];
               C:=CompanionMatrix(f);
               ord:=Order(C);
               C:=DiagonalJoin(C,Transpose(C^-1));
               B:=BlockMatrix(2,2,[0,IdentityMatrix(F,i),IdentityMatrix(F,i),0]);
               Append(~Sp[i],<1,C,B,i,ord>);
            else
               Append(~Sp[i],<1,x[1],IdentityMatrix(F,2*i)>);
            end if;
            MultSp[i]+:=1;
         end if;
      end for;
   end for;

   for i in [m1+2-(m1 mod 2)..m by 2] do
      k:=i div 2;
      R:=CartesianPower(F,k);
      for L in R do
         f:=&+[L[j]*(t^j+t^(i-j)): j in [1..k]];
         f:=f+1+t^i-L[k]*t^k;
         if IsIrreducible(f) then
            //begin construction matrix of the form
            C:=CompanionMatrix(f);
            c:=[];
            c:=[1,C[i,2]];
            if k eq 1 then
               c:=[1,C[i,2]/2];
            end if;
            if k gt 1 then
               c[3]:=C[i,2]*c[2]+C[i,3]-1;
            end if;
            if k gt 2 then
               for l in [3..k] do
                  c[l+1]:=&+[C[i,j+1]*c[l-j+1]: j in [1..l]];
               end for;
            end if;
            Reverse(~c);
            c:=c cat[0: v in [1..k-1]];
            d:=[];
            for v in [1..i] do
               d:=c cat d;
               Remove(~c,1);
            end for;
            B:=SymmetricMatrix(F,d);
            //end construction matrix of the form  
            if Explicit then
               Append(~Sm[k],<2,C,B,i,Order(C)>);
            else
               Append(~Sm[k],<2,f,B>);
            end if;
            MultSm[k]+:=1;
         end if;
      end for;
   end for;

   // FIRST PART: classes with el.div. of degree at most m
   Omega:=RestrictedPartitions(m,{1..m1});
   for P1 in Omega do
      //mult:= (multiplicity of t-1 + multiplicity of t+1)/2
      for mult in [1..m1] do
         if mult in P1 then
            P:=Exclude(P1,mult);
            array:=[Multiplicity(P,i): i in [1..m1]];
            R:=<>;                           
            for i in [1..m1] do
               Shelp:=[];
               ni:=MultSp[i]+MultSm[i];
               si:=array[i];
               sumi:=ni+si;
               set:={k: k in [1..sumi-1]};
               for y in Subsets(set,ni-1) do
                  if IsEmpty(y) then
                     if IsEmpty(set) then
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
            // a_j-th el.div. of Sp[i] if a_j <= MultSp[i],
            // otherwise is the (a_j-MultSp[i])-th el. div. of Sm[i]
            // in this first part Sp[i] and Sm[i] are concatenated in a unique list.
            C:=CartesianProduct(R);
            for c in C do
               if Explicit then
                  sign:=1;
                  order:=1;
                  card:=Card;
                  Form:=Random(MatrixAlgebra(F,0));
                  Repr:=Random(MatrixAlgebra(F,0));
                  for i in [1..m1] do
                     for j in [1..#c[i]] do
                        pos:=c[i][j][1];
                        if pos le MultSp[i] then
                           cij:=c[i][j][2];
                           deg:=Sp[i][pos][4];
                           for k in [1..cij] do
                              Form:=DiagonalJoin(Form,Sp[i][pos][3]);
                              Repr:=DiagonalJoin(Repr,Sp[i][pos][2]);
                           end for;
                           // dividing by cardinality of the centralizer
                           if cij gt 1 then
                              card/:=SequenceToFactorization([<p,Deg*deg*cij*(cij-1) div 2>]);
                           end if;
                           for k in [1..cij] do
                              card/:=Factorization(q^(deg*k)-1);
                           end for;
                           order:=Lcm(order,Sp[i][pos][5]);
                        else
                           pos-:=MultSp[i];
                           cij:=c[i][j][2];
                           deg:=Sm[i][pos][4];
                           for k in [1..cij] do
                              Form:=DiagonalJoin(Form,Sm[i][pos][3]);
                              Repr:=DiagonalJoin(Repr,Sm[i][pos][2]);
                              sign*:=-1;
                           end for;
                           // dividing by cardinality of the centralizer
                           if cij gt 1 then
                              card/:=SequenceToFactorization([<p,Deg*cij*(cij-1)*deg div 4>]);
                           end if;
                           for k in [1..cij] do
                              card/:=Factorization(q^(deg*k div 2)-(-1)^k);
                           end for;
                           order:=Lcm(order,Sm[i][pos][5]);
                        end if;
                     end for;
                  end for;
                  //last part: add elementary divisors t+1 and t-1 and correct sign
                  B1:=DiagonalJoin([Matrix(F,2,2,[1,0,0,-1]): v in [1..mult]]);
                  ind:=0;
                  if (sign eq -1 and type eq "plus") or (sign eq 1 and type eq "minus") then
                     B1[2*mult,2*mult]:=-w;
                     card1:=card/FactCard[2][2*mult];
                     ind:=1;
                  else
                     card1:=card/FactCard[1][2*mult];
                  end if;
                  B2:=B1;
                  B2[1,1]*:=w;B2[2*mult,2*mult]*:=w;
                  M1:=TransformForm(DiagonalJoin(Form,B1),type1: Restore:=false);
                  M2:=TransformForm(DiagonalJoin(Form,B2),type1: Restore:=false);
                  Suss:=IdentityMatrix(F,2*mult);
                  Append(~ConjClasses,<order,Integers()!card1,Gr!(M1^-1*DiagonalJoin(Repr,Suss)*M1)>);
                  order:=Lcm(2,order);      // 2 = order of el.div. t+1
                  Append(~ConjClasses,<order,Integers()!card1,Gr!(M1^-1*DiagonalJoin(Repr,-Suss)*M1)>);
                  for v in [1..2*mult-1] do
                     Suss[v,v]:=-1;
                     card1:=card/(FactCard[1][v]*FactCard[1+ind][2*mult-v]);
                     Append(~ConjClasses,<order,Integers()!card1,Gr!(M1^-1*DiagonalJoin(Repr,Suss)*M1)>);
                     card1:=card/(FactCard[2][v]*FactCard[2-ind][2*mult-v]);
                     Append(~ConjClasses,<order,Integers()!card1,Gr!(M2^-1*DiagonalJoin(Repr,Suss)*M2)>);
                  end for;
               else
                  Cclass:=[**];
                  for i in [1..m1] do
                     for j in [1..#c[i]] do
                        pos:=c[i][j][1];
                        if pos le MultSp[i] then
                           Append(~Cclass,<Sp[i][pos][2],c[i][j][2],Sp[i][pos][1],Sp[i][pos][3]>);
                        else
                           pos-:=MultSp[i];
                           Append(~Cclass,<Sm[i][pos][2],c[i][j][2],Sm[i][pos][1],Sm[i][pos][3]>);
                        end if;
                     end for;
                  end for;
                  for v in [1..2*mult-1] do
                     Cclass1:=Cclass;
                     Append(~Cclass1,<t-1,v,0,IdentityMatrix(F,1)>);
                     Append(~Cclass1,<t+1,2*mult-v,0,IdentityMatrix(F,1)>);
                     Append(~ConjClasses,Cclass1);
                  end for;
                  Append(~ConjClasses, Append(Cclass,<t-1,2*mult,0,IdentityMatrix(F,1)>));
                  Append(~ConjClasses, Append(Cclass,<t+1,2*mult,0,IdentityMatrix(F,1)>));
               end if;
            end for;   
         end if;
      end for;
      // end part with el.div. of degree less than m and at least one is t+1 or t-1

      // second part: all el.div. of degree less than m and different from t+1 and t-1
      // this is the only case in which we need to keep track of the sign,
      // because it cannot be corrected by the el.div. t-1, t+1 or an el.div. of degree greater than m
      P:=P1;
      set:={i: i in P|Multiplicity(P,i) gt 0};
      Mult:=[Multiplicity(P,i): i in [1..m1]];
      start:=0;
      if type eq "minus" then
         start:=1;
      end if;
      // i = # of el. div. of sign minus
      for i in [start..&+Mult by 2] do
         for S in Subsets(set,i) do
            R:=[];
            for v in [1..m1] do
               if Mult[v] gt 0 then 
                  Si:=[];
                  start2:=0;
                  if v in S then
                     start2:=1;
                  end if;
                  for j in [start2..Mult[v] by 2] do
                     seq:=[Mult[v]-j,j];
                     Append(~Si,seq);
                  end for;
                  Append(~R,Si);
               else
                  Append(~R,[[0,0]]);
               end if;
            end for;
            C:=CartesianProduct(R);
            // an element of C is a m1-tuple whose elements are [a+_i,a-_i],
            // a+_i = # of el. div. of degree 2i and sign +
            // a-_i = # of el. div. of degree 2i and sign -
         
            for c in C do
               if c[1][1] eq 0 or MultSp[1] ne 0 then  // need this when F=GF(3)
                  R1:=<>;
                  for j in [1..m1] do
                     Shelp:=[];
                     ni:=MultSp[j];
                     si:=c[j][1];
                     sumi:=ni+si;
                     if si eq 0 then
	   	        Shelp:=[[]];
                     else
                        set1:={v: v in [1..sumi-1]};
                        for y in Subsets(set1,ni-1) do
                           if IsEmpty(y) then
                              if IsEmpty(set) then
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
                              for v in [1..ni] do
                                 if x[v+1]-x[v] gt 1 then
                                    Append(~seq,<v,x[v+1]-x[v]-1>);
                                 end if;
                              end for;
                           end if;
                           Append(~Shelp,seq);
                        end for;
                     end if;
                     Append(~R1,Shelp);
                  end for;
                  Cp:=CartesianProduct(R1);  
                  R1:=<>;
                  for j in [1..m1] do
                     Shelp:=[];
                     ni:=MultSm[j];
                     si:=c[j][2];
                     sumi:=si+ni;
                     if si eq 0 then
                        Shelp:=[[]];
                     else
                        set1:={v: v in [1..sumi-1]};
                        for y in Subsets(set1,ni-1) do
                           if IsEmpty(y) then
                              if IsEmpty(set1) then
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
                              for v in [1..ni] do
                                 if x[v+1]-x[v] gt 1 then
                                    Append(~seq,<v,x[v+1]-x[v]-1>);
                                 end if;
                              end for;
                           end if;
                           Append(~Shelp,seq);
                        end for;
                     end if;
                     Append(~R1,Shelp);
                  end for;
                  Cm:=CartesianProduct(R1);

                  // cp[i] = [<a_j,b_j>: j]: the a_j-th el.div. of Sp[i] has multiplicity b_j
                  // cm[i] = [<a_j,b_j>: j]: the a_j-th el.div. of Sm[i] has multiplicity b_j
                  for cp in Cp do
                     for cm in Cm do
                        if Explicit then
                           Form:=Random(MatrixAlgebra(F,0));
                           Repr:=Random(MatrixAlgebra(F,0));
                           card:=Card;
                           order:=1;
                           for j1 in [1..m1] do
                              for j2 in [1..#cp[j1]] do
                                 pos:=cp[j1][j2][1];
                                 cij:=cp[j1][j2][2];
                                 deg:=Sp[j1][pos][4];
                                 for j3 in [1..cij] do
                                    Form:=DiagonalJoin(Form,Sp[j1][pos][3]);
                                    Repr:=DiagonalJoin(Repr,Sp[j1][pos][2]);
                                 end for;
                                 // dividing by cardinality of the centralizer
                                 if cij gt 1 then
                                    card/:=SequenceToFactorization([<p,Deg*deg*cij*(cij-1) div 2>]);
                                 end if;
                                 for k in [1..cij] do
                                    card/:=Factorization(q^(deg*k)-1);
                                 end for;
                                 order:=Lcm(order,Sp[j1][pos][5]);
                              end for;
                           end for;
                           for j1 in [1..m1] do
                              for j2 in [1..#cm[j1]] do
                                 pos:=cm[j1][j2][1];
                                 cij:=cm[j1][j2][2];
                                 deg:=Sm[j1][pos][4];
                                 for j3 in [1..cij] do
                                    Form:=DiagonalJoin(Form,Sm[j1][pos][3]);
                                    Repr:=DiagonalJoin(Repr,Sm[j1][pos][2]);
                                 end for;
                                 // dividing by cardinality of the centralizer
                                 if cij gt 1 then
                                    card/:=SequenceToFactorization([<p,Deg*cij*(cij-1)*deg div 4>]);
                                 end if;
                                 for k in [1..cij] do
                                    card/:=Factorization(q^(deg*k div 2)-(-1)^k);
                                 end for;
                                 order:=Lcm(order,Sm[j1][pos][5]);
                              end for;
                           end for;
                           M:=TransformForm(Form,type1: Restore:=false);
                           Append(~ConjClasses,<order,Integers()!card,Gr!(M^-1*Repr*M)>);
                        else
                           Cclass:=[**];
                           for j1 in [1..m1] do
                              for j2 in [1..#cp[j1]] do
                                 pos:=cp[j1][j2][1];
                                 Append(~Cclass,<Sp[j1][pos][2],cp[j1][j2][2],Sp[j1][pos][1],Sp[j1][pos][3]>);
                              end for;
                           end for;
                           for j1 in [1..m1] do
                              for j2 in [1..#cm[j1]] do
                                 pos:=cm[j1][j2][1];
                                 Append(~Cclass,<Sm[j1][pos][2],cm[j1][j2][2],Sm[j1][pos][1],Sm[j1][pos][3]>);
                              end for;
                           end for;
                           Append(~ConjClasses,Cclass);
                        end if;
                     end for;
                  end for;
               end if;
            end for;
         end for;
      end for;             
   end for;
   // end creation conjugacy classes with blocks of dimension at most m1

   // SECOND PART: classes with at least one el.div. of degree greater than m
   for i in [m1+1..m-1] do
      // T contains elementary divisors of dimension 2*i (both p=p* and pp*)
      Tp:=[];
      Tm:=[];
      if i eq 1 then                        
         Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,i) |
                  x ne t and x ne t+1 and x ne t-1};
      else
         Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,i)};
      end if;
      X:=[<a[1],#a>: a in Y];
      for x in X do
         f:=x[1];
         if Explicit then
            if x[2] eq 2 then
               C:=CompanionMatrix(f);
               ord:=Order(C);
               C:=DiagonalJoin(C,Transpose(C^-1));
               B:=BlockMatrix(2,2,[0,IdentityMatrix(F,i),IdentityMatrix(F,i),0]);
               Append(~Tp,<1,C,B,i,ord>);
            end if;
         else
            if x[2] eq 2 then
               Append(~Tp,<1,f,IdentityMatrix(F,2*i)>);
            end if;
         end if;
      end for;
      R:=CartesianPower(F,i);
      for L in R do
         f:=&+[L[j]*(t^j+t^(2*i-j)): j in [1..i]];
         f:=f+1+t^(2*i)-L[i]*t^i;
         if IsIrreducible(f) then
            C:=CompanionMatrix(f);
            c:=[];
            c:=[1,C[2*i,2]];
            if i eq 1 then
               c:=[1,C[2*i,2]/2];
            end if;
            if i gt 1 then
               c[3]:=C[2*i,2]*c[2]+C[2*i,3]-1;
            end if;
            if i gt 2 then
               for l in [3..i] do
                  c[l+1]:=&+[C[2*i,j+1]*c[l-j+1]: j in [1..l]];
               end for;
            end if;
            Reverse(~c);
            c:=c cat[0: v in [1..i-1]];
            d:=[];
            for v in [1..2*i] do
               d:=c cat d;
               Remove(~c,1);
            end for;
            B:=SymmetricMatrix(F,d);
            if Explicit then
               Append(~Tm,<2,C,B,2*i,Order(C)>);
            else
               Append(~Tm,<2,f,B>);
            end if;
 	 end if;
      end for;

      // first part: one of the el.div. of degree <m is t+1 or t-1.
      // In such a case, the sign is corrected when the el.div. t=1 or t-1 is added
      m2:=m-i;
      Omega:=RestrictedPartitions(m-i,{1..m2});
      for P1 in Omega do
         // mult:=multiplicity of t-1 + multiplicity of t+1
         for mult in [1..m2] do
            if not mult in P1 then continue; end if;
            P:=Exclude(P1,mult);           
            array:=[Multiplicity(P,j): j in [1..m2]];
            R:=<>;                           
            for j in [1..m2] do
               Shelp:=[];
               ni:=MultSp[j]+MultSm[j];
               si:=array[j];
               sumi:=ni+si;
               set:={k: k in [1..sumi-1]};
               for y in Subsets(set,ni-1) do
                  if IsEmpty(y) then
                     if IsEmpty(set) then
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
            // a_j-th el.div. of Sp[i] if a_j <= MultSp[i],
            // otherwise is the (a_j-MultSp[i])-th el. div. of Sm[i]
            C:=CartesianProduct(R);
            for c in C do
               if Explicit then
                  sign:=1;
                  order:=1;
                  card:=Card;
                  Form:=Random(MatrixAlgebra(F,0));
                  Repr:=Random(MatrixAlgebra(F,0));
                  for j1 in [1..m2] do
                     for j2 in [1..#c[j1]] do
                        pos:=c[j1][j2][1];
                        if pos le MultSp[j1] then
                           cij:=c[j1][j2][2];
                           kind:=Sp[j1][pos][1];
                           deg:=Sp[j1][pos][4];
                           for k in [1..cij] do
                              Form:=DiagonalJoin(Form,Sp[j1][pos][3]);
                              Repr:=DiagonalJoin(Repr,Sp[j1][pos][2]);
                           end for;
                           // dividing by cardinality of the centralizer
                           if cij gt 1 then
                              card/:=SequenceToFactorization([<p,Deg*deg*cij*(cij-1) div 2>]);
                           end if;
                           for k in [1..cij] do
                              card/:=Factorization(q^(deg*k)-1);
                           end for;
                           order:=Lcm(order,Sp[j1][pos][5]);
                        else
    		           pos-:=MultSp[j1];
                           cij:=c[j1][j2][2];
                           kind:=Sm[j1][pos][1];
                           deg:=Sm[j1][pos][4];
                           for k in [1..cij] do
                              Form:=DiagonalJoin(Form,Sm[j1][pos][3]);
                              Repr:=DiagonalJoin(Repr,Sm[j1][pos][2]);
                              sign*:=-1;
                           end for;
                           // dividing by cardinality of the centralizer
                           if cij gt 1 then
                              card/:=SequenceToFactorization([<p,Deg*cij*(cij-1)*deg div 4>]);
                           end if;
                           for k in [1..cij] do
                              card/:=Factorization(q^(deg*k div 2)-(-1)^k);
                           end for;
                           order:=Lcm(order,Sm[j1][pos][5]);
                        end if;
                     end for;
                  end for;
                  // last part: add the el.div. of degree >m and then t+1 and t-1
                  B1:=DiagonalJoin([Matrix(F,2,2,[1,0,0,-1]): v in [1..mult]]);
                  ind:=0;
                  if (sign eq -1 and type eq "plus") or (sign eq 1 and type eq "minus") then
                     B1[2*mult,2*mult]:=-w;
                     ind:=1;
                  end if;
                  B2:=B1;
                  B2[1,1]*:=w;B2[2*mult,2*mult]*:=w;
                  deg:=Tp[1][4];
                  // card1 is the same for every element in Tp, so compute it just one time
                  card1:=card/Factorization(q^deg-1);
                  for x in Tp do
                     order1:=Lcm(order,x[5]);
                     Form1:=DiagonalJoin(Form,x[3]);
                     Repr1:=DiagonalJoin(Repr,x[2]);
                     Suss:=IdentityMatrix(F,2*mult);
                     M1:=TransformForm(DiagonalJoin(Form1,B1),type1: Restore:=false);
                     M2:=TransformForm(DiagonalJoin(Form1,B2),type1: Restore:=false);
                     card2:=card1/FactCard[1+ind][2*mult];
                     Append(~ConjClasses,<order1,Integers()!card2,Gr!(M1^-1*DiagonalJoin(Repr1,Suss)*M1)>);
                     order1:=Lcm(order1,2);   // 2 = order of el.div. t+1
                     Append(~ConjClasses,<order1,Integers()!card2,Gr!(M1^-1*DiagonalJoin(Repr1,-Suss)*M1)>);
                     for v in [1..2*mult-1] do
                        Suss[v,v]:=-1;
                        card2:=card1/(FactCard[1][v]*FactCard[1+ind][2*mult-v]);
                        Append(~ConjClasses,<order1,Integers()!card2,Gr!(M1^-1*DiagonalJoin(Repr1,Suss)*M1)>);
                        card2:=card1/(FactCard[2][v]*FactCard[2-ind][2*mult-v]);
                        Append(~ConjClasses,<order1,Integers()!card2,Gr!(M2^-1*DiagonalJoin(Repr1,Suss)*M2)>);
                     end for;
                  end for;
                  sign*:=-1;
                  ind:=0;
                  B1:=DiagonalJoin([Matrix(F,2,2,[1,0,0,-1]): v in [1..mult]]);
                  if (sign eq -1 and type eq "plus") or (sign eq 1 and type eq "minus") then
                     B1[2*mult,2*mult]:=-w;
                     ind:=1;
                  end if;
                  B2:=B1;
                  B2[1,1]*:=w;B2[2*mult,2*mult]*:=w;
                  deg:=Tm[1][4];
                  // card1 is the same for every element in Tm, so compute it just one time
                  card1:=card/Factorization(q^(deg div 2)+1);
                  for x in Tm do
                     order1:=Lcm(order,x[5]);
                     Form1:=DiagonalJoin(Form,x[3]);
                     Repr1:=DiagonalJoin(Repr,x[2]);
                     M1:=TransformForm(DiagonalJoin(Form1,B1),type1: Restore:=false);
                     M2:=TransformForm(DiagonalJoin(Form1,B2),type1: Restore:=false);
                     Suss:=IdentityMatrix(F,2*mult);
                     card2:=card1/FactCard[1+ind][2*mult];
                     Append(~ConjClasses,<order1,Integers()!card2,Gr!(M1^-1*DiagonalJoin(Repr1,Suss)*M1)>);
                     order1:=Lcm(order1,2);   // 2 = order of el.div. t+1
                     Append(~ConjClasses,<order1,Integers()!card2,Gr!(M1^-1*DiagonalJoin(Repr1,-Suss)*M1)>);
                     for v in [1..2*mult-1] do
                        Suss[v,v]:=-1;
                        card2:=card1/(FactCard[1][v]*FactCard[1+ind][2*mult-v]);
                        Append(~ConjClasses,<order1,Integers()!card2,Gr!(M1^-1*DiagonalJoin(Repr1,Suss)*M1)>);
                        card2:=card1/(FactCard[2][v]*FactCard[2-ind][2*mult-v]);
                        Append(~ConjClasses,<order1,Integers()!card2,Gr!(M2^-1*DiagonalJoin(Repr1,Suss)*M2)>);
                     end for;
                  end for;
               else
                  Cclass:=[**];
                  for j1 in [1..m2] do
                     for j2 in [1..#c[j1]] do
                        pos:=c[j1][j2][1];
                        if pos le MultSp[j1] then
                           Append(~Cclass,<Sp[j1][pos][2],c[j1][j2][2],Sp[j1][pos][1],Sp[j1][pos][3]>);
                        else
                           pos-:=MultSp[j1];
                           Append(~Cclass,<Sm[j1][pos][2],c[j1][j2][2],Sm[j1][pos][1],Sm[j1][pos][3]>);
                        end if;
                     end for;
                  end for;
                  for x in Tp do
                     Cclass1:=Append(Cclass,<x[2],1,x[1],x[3]>);
                     Append(~ConjClasses,Append(Cclass1,<t-1,2*mult,0,IdentityMatrix(F,2*mult)>));
                     Append(~ConjClasses,Append(Cclass1,<t+1,2*mult,0,IdentityMatrix(F,2*mult)>));
                     for v in [1..2*mult-1] do
                        Append(~ConjClasses, Cclass1 cat [*<t-1,v,0,IdentityMatrix(F,1)>,<t+1,2*mult-v,0,IdentityMatrix(F,1)>*]);
                     end for;
                  end for;
                  for x in Tm do
                     Cclass1:=Append(Cclass,<x[2],1,x[1],x[3]>);
                     Append(~ConjClasses,Append(Cclass1,<t-1,2*mult,0,IdentityMatrix(F,2*mult)>));
                     Append(~ConjClasses,Append(Cclass1,<t+1,2*mult,0,IdentityMatrix(F,2*mult)>));
                     for v in [1..2*mult-1] do
                        Append(~ConjClasses, Cclass1 cat [*<t-1,v,0,IdentityMatrix(F,1)>,<t+1,2*mult-v,0,IdentityMatrix(F,1)>*]);
                     end for;
                  end for;
               end if;
            end for;
         end for;

         // second part: there is an el.div. of degree >m or the multiplicities of t+1 and t-1 are >m
         // in such a case the sign is corrected when the last el.div. is added
         P:=P1;
         array:=[Multiplicity(P,j): j in [1..m2]];
         R:=<>;                           
         for j in [1..m2] do
            Shelp:=[];
            ni:=MultSp[j]+MultSm[j];
            si:=array[j];
            sumi:=si+ni;
            set:={k: k in [1..sumi-1]};
            for y in Subsets(set,ni-1) do
               if IsEmpty(y) then
                  if sumi eq 1 then
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
         // a_j-th el.div. of Sp[i] if a_j <= MultSp[i],
         // otherwise is the (a_j-MultSp[i])-th el. div. of Sm[i]
         C:=CartesianProduct(R);
         for c in C do
            if Explicit then
               sign:=1;
               order:=1;
               card:=Card;
               Form:=Random(MatrixAlgebra(F,0));
               Repr:=Random(MatrixAlgebra(F,0));
               for j1 in [1..m2] do
                  for j2 in [1..#c[j1]] do
                     pos:=c[j1][j2][1];
                     if pos le MultSp[j1] then
   	                cij:=c[j1][j2][2];
                        deg:=Sp[j1][pos][4];
                        for k in [1..cij] do
                           Form:=DiagonalJoin(Form,Sp[j1][pos][3]);
                           Repr:=DiagonalJoin(Repr,Sp[j1][pos][2]);
                        end for;
                        // dividing by cardinality of the centralizer
                        if cij gt 1 then
                           card/:=SequenceToFactorization([<p,Deg*deg*cij*(cij-1) div 2>]);
                        end if;
                        for k in [1..cij] do
                           card/:=Factorization(q^(deg*k)-1);
                        end for;
                        order:=Lcm(order,Sp[j1][pos][5]);
                     else
		        pos-:=MultSp[j1];
                        cij:=c[j1][j2][2];
                        kind:=Sm[j1][pos][1];
                        deg:=Sm[j1][pos][4];
                        for k in [1..cij] do
                           Form:=DiagonalJoin(Form,Sm[j1][pos][3]);
                           Repr:=DiagonalJoin(Repr,Sm[j1][pos][2]);
                           sign*:=-1;
                        end for;
                        if cij gt 1 then
                           card/:=SequenceToFactorization([<p,Deg*cij*(cij-1)*deg div 4>]);
                        end if;
                        for k in [1..cij] do
                           card/:=Factorization(q^(deg*k div 2)-(-1)^k);
                        end for;
                        order:=Lcm(order,Sm[j1][pos][5]);
                     end if;
                  end for;
               end for;
               // first case: add el.div. of degree >m.
               if (sign eq -1 and type eq "plus") or (sign eq 1 and type eq "minus") then
                  card1:=card/Factorization(q^(Tm[1][4] div 2)+1);
                  for x in Tm do
                     Form1:=DiagonalJoin(Form,x[3]);
                     Repr1:=DiagonalJoin(Repr,x[2]);
                     M:=TransformForm(Form1,type1: Restore:=false);
                     Append(~ConjClasses,<Lcm(order,x[5]),Integers()!card1, Gr!(M^-1*Repr1*M)>);
                  end for;
               else
                  // card1 is the same for every element in Tp
                  card1:=card/Factorization(q^(Tp[1][4])-1);
                  for x in Tp do
                     Form1:=DiagonalJoin(Form,x[3]);
                     Repr1:=DiagonalJoin(Repr,x[2]);
                     M:=TransformForm(Form1,type1: Restore:=false);
                     Append(~ConjClasses,<Lcm(order,x[5]),Integers()!card1, Gr!(M^-1*Repr1*M)>);
                  end for;
               end if;
               // second case: add t+1 and t-1 with multiplicity >m.
               B1:=DiagonalJoin([Matrix(F,2,2,[1,0,0,-1]): v in [1..i]]);
               ind:=0;
               if (sign eq -1 and type eq "plus") or (sign eq 1 and type eq "minus") then
                  B1[2*i,2*i]:=-w;
                  ind:=1;
               end if;
               B2:=B1;
               B2[1,1]*:=w;B2[2*i,2*i]*:=w;
               M1:=TransformForm(DiagonalJoin(Form,B1),type1: Restore:=false);
               M2:=TransformForm(DiagonalJoin(Form,B2),type1: Restore:=false);
               Suss:=IdentityMatrix(F,2*i);
               card1:=card/FactCard[1+ind][2*i];
               Append(~ConjClasses,<order,Integers()!card1,Gr!(M1^-1*DiagonalJoin(Repr,Suss)*M1)>);
               order:=Lcm(2,order);      // 2 = order of el.div. t+1
               Append(~ConjClasses,<order,Integers()!card1,Gr!(M1^-1*DiagonalJoin(Repr,-Suss)*M1)>);
               for v in [1..2*i-1] do
                  Suss[v,v]:=-1;
                  card1:=card/(FactCard[1][v]*FactCard[1+ind][2*i-v]);
                  Append(~ConjClasses,<order,Integers()!card1,Gr!(M1^-1*DiagonalJoin(Repr,Suss)*M1)>);
                  card1:=card/(FactCard[2][v]*FactCard[2-ind][2*i-v]);
                  Append(~ConjClasses,<order,Integers()!card1,Gr!(M2^-1*DiagonalJoin(Repr,Suss)*M2)>);
               end for;
            else
               Cclass:=[**];
               sign:=1;
               for j1 in [1..m2] do
                  for j2 in [1..#c[j1]] do
                     pos:=c[j1][j2][1];
                     if pos le MultSp[j1] then
                        Append(~Cclass,<Sp[j1][pos][2],c[j1][j2][2],Sp[j1][pos][1],Sp[j1][pos][3]>);
                     else
                        pos-:=MultSp[j1];
                        Append(~Cclass,<Sm[j1][pos][2],c[j1][j2][2],Sm[j1][pos][1],Sm[j1][pos][3]>);
                        sign*:=(-1)^c[j1][j2][2];
                     end if;
                  end for;
               end for;
               if (sign eq -1 and type eq "plus") or (sign eq 1 and type eq "minus") then
                  for x in Tm do
                     Append(~ConjClasses,Append(Cclass,<x[2],1,x[1],x[3]>));
                  end for;
               else
                  for x in Tp do
                     Append(~ConjClasses,Append(Cclass,<x[2],1,x[1],x[3]>));
                  end for;
               end if;
               Append(~ConjClasses,Append(Cclass,<t-1,2*i,0,IdentityMatrix(F,1)>));
               Append(~ConjClasses,Append(Cclass,<t+1,2*i,0,IdentityMatrix(F,1)>));
               for v in [1..2*i-1] do
                  Append(~ConjClasses,Cclass cat [*<t-1,v,0,IdentityMatrix(F,1)>,<t+1,2*i-v,0,IdentityMatrix(F,1)>*]);
               end for;
            end if;
         end for;
      end for;
   end for;

   //part with a unique el. div. deg(pp*)=n or deg(p)=n with p=p*
   if type eq "plus" then
      Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,m)};
      X:=[<a[1],#a>: a in Y];
      for x in X do
	 f:=x[1];
	 if x[2] eq 2 then
            if Explicit then
               C:=CompanionMatrix(f);
               ord:=Order(C);
               C:=DiagonalJoin(C,Transpose(C^-1));
               B:=BlockMatrix(2,2,[0,IdentityMatrix(F,m),IdentityMatrix(F,m),0]);
               M:=TransformForm(B,"orthogonalplus": Restore:=false);
               Append(~ConjClasses,<ord,Integers()!(Card/Factorization(q^m-1)),Gr!(M^-1*C*M)>);
            else
               Append(~ConjClasses,[*<f,1,1,IdentityMatrix(F,n)>*]);
            end if;
         end if;
      end for;
   else
      R:=CartesianPower(F,m);
      for L in R do
         f:=&+[L[j]*(t^j+t^(n-j)): j in [1..m]];
         f:=f+1+t^n-L[m]*t^m;
         if IsIrreducible(f) then
            C:=CompanionMatrix(f);
            c:=[1,C[n,2]];
            c[3]:=C[n,2]*c[2]+C[n,3]-1;
            for l in [3..m] do
               c[l+1]:=&+[C[n,j+1]*c[l-j+1]: j in [1..l]];
            end for;
            Reverse(~c);
            c:= c cat [0: v in [1..m-1]];
            d:=[];
            for v in [1..n] do
               d:=c cat d;
               Remove(~c,1);
            end for;
            B:=SymmetricMatrix(F,d);
            if Explicit then
               M:=TransformForm(B,"orthogonalminus": Restore:=false);
               Append(~ConjClasses,<Order(C),Integers()!(Card/Factorization(q^m+1)),Gr!(M^-1*C*M)>);
            else
               Append(~ConjClasses,[*<f,1,2,B>*]);
            end if;
         end if;
      end for;
   end if;

   //part with t+1 and t-1 as unique el.div.
   if Explicit then
      Append(~ConjClasses,<1,1,Gr!IdentityMatrix(F,n)>);
      Append(~ConjClasses,<2,1,Gr!(-IdentityMatrix(F,n))>);
      B1:=DiagonalJoin([Matrix(F,2,2,[1,0,0,-1]): i in [1..m]]);
      ind:=0;
      if type eq "minus" then
         B1[n,n]:=-w;
         ind:=1;
      end if;
      B2:=B1;
      B2[1,1]*:=w;B2[n,n]*:=w;
      Suss:=IdentityMatrix(F,n);
      M1:=TransformForm(B1,type1: Restore:=false);
      M2:=TransformForm(B2,type1: Restore:=false);
      for v in [1..n-1] do
         Suss[v,v]:=-1;
         card:=Card/(FactCard[1][v]*FactCard[1+ind][n-v]);
         Append(~ConjClasses,<2,Integers()!card,Gr!(M1^-1*Suss*M1)>);
         card:=Card/(FactCard[2][v]*FactCard[2-ind][n-v]);
         Append(~ConjClasses,<2,Integers()!card,Gr!(M2^-1*Suss*M2)>);
      end for;
   else
      Append(~ConjClasses,[*<t-1,n,0,IdentityMatrix(F,1)>*]);
      Append(~ConjClasses,[*<t+1,n,0,IdentityMatrix(F,1)>*]);
      for v in [1..n-1] do
         Append(~ConjClasses, [* <t-1,v,0,IdentityMatrix(F,1)>, <t+1,n-v,0,IdentityMatrix(F,1)>*]);
      end for;
   end if;

   return ConjClasses;
end function;

freeze;

import "../card.m": CardinalityOfClassicalGroup;
import "../form.m": SFC, ConjugatePolynomial;

// Return the list of semisimple conjugacy classes of GO(n,F), 
// n even, |F| even
// A class is identified with a triple < m,n,X >,
// with X representative of the class in GO(n,F), 
// m = Order(X), n = class size
// In all comments, el.div. = elementary divisors

GOClasses_Char2:=function(n,F,type)

   ConjClasses:=[];
   if Type(F) eq RngIntElt then
      F:=GF(F);
   end if;
   q:=#F;
   Gr:=GL(n,F);
   Deg:=Degree(F);
   p:=Characteristic(F);
   m:=n div 2;
   ConjPol:=ConjugatePolynomial(false);

   if IsOdd(q) then
      error "charF must be even";
   end if;

   if IsOdd(n) then
      error "n must be even";
   end if;

   if not type in {"plus", "minus"} then
      error "type must be either plus or minus";
   end if;

   t:=PolynomialRing(F).1;
   w:=PrimitiveElement(F);

   if type eq "plus" then
      type1:="orthogonalplus";
   else
      type1:="orthogonalminus";
   end if;
   FormPlus:=StandardQuadraticForm(2,F);
   FormMinus:=StandardQuadraticForm(2,F: Minus);

   // computation of |GO(n,q)|
   call := type eq "plus" select "orthogonalplus" else "orthogonalminus";
   Card := CardinalityOfClassicalGroup (call, n, q);

   // case n=2 treated separately
   if n eq 2 then
      Append(~ConjClasses,<1,1,Gr!IdentityMatrix(F,2)>);
      if type eq "plus" then
         X:=[x: x in F];
         Exclude(~X,0);
         Exclude(~X,1);
         cont:=1;
         while cont le #X do
	    w:=X[cont];
            Exclude(~X,w^-1);
            Append(~ConjClasses,<Order(w),Integers()!Card/(q-1),Gr!Matrix(F,2,2,[-w,0,0,-w^-1])>);
            cont+:=1;
         end while;
      else
         for u in F do
            f:=t^2-u*t+1;
            if IsIrreducible(f) then
               x:=CompanionMatrix(f);
               B:=Matrix(F,2,2,[1,u,0,1]);
               m:=TransformForm(B,"orthogonalminus": Restore:=false);
               Append(~ConjClasses,<Order(x),Integers()!Card/(q+1),Gr!(m^-1*x*m)>);
            end if;
         end for;
      end if;

      return ConjClasses;
   end if;
   //end separate case n=2

   //begin general case
   m1:=m div 2;
   // Sp[i] contains all e.div. of dimension (2*i) and type "orthogonalplus"
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

   // remember factored cardinality of GOpm(2m,q)
   // FactCard[1][i] = factored cardinality of GOPlus(2i,q)
   // FactCard[2][i] = factored cardinality of GOMinus(2i,q)
   L1 := <>;
   L2 := <>;
   for i in [2..n by 2] do
      a := CardinalityOfClassicalGroup ("orthogonalplus", i, q);
      Append (~L1,a);
      b := CardinalityOfClassicalGroup ("orthogonalminus", i, q);
      Append (~L2,b);
   end for;
   FactCard := [L1, L2];

   //remember all possible elementary divisors of degree less than m div 2
   for i in [1..m1] do
      if i eq 1 then                        
         Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,i) |
                 x ne t and x ne t+1};
      else
         Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,i)};
      end if;
      X:=[<a[1],#a>: a in Y];
      for x in X do
         //begin construction matrix of the form preserved by f=f*
         if x[2] eq 1 then
            f:=x[1];
            C:=CompanionMatrix(f);
            if i eq 2 then
               B:=Matrix(F,2,2,[1,-Coefficients(f)[2],0,1]);
            else
               Z,w:=SFC(f);
               _,v:=IsConsistent(Z,w);
               v:=Eltseq(v);
               Insert(~v,1,1);
               v:= [0: j in [1..i div 2-1]] cat v;
               vect:=v;
               Prune(~v);
               while #v gt 0 do
                  vect cat:=v;
                  Prune(~v);
               end while;
               B:=UpperTriangularMatrix(vect);
            end if;
            Append(~Sm[i div 2],<2,C,B,i,Order(C)>);
            MultSm[i div 2]+:=1;
         else
            f:=x[1];
            C:=CompanionMatrix(f);
            ord:=Order(C);
            C:=DiagonalJoin(C,Transpose(C^-1));
            B:=BlockMatrix(2,2,[0,IdentityMatrix(F,i),0,0]);
            Append(~Sp[i],<1,C,B,i,ord>);
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
            C:=CompanionMatrix(f);
            if i eq 2 then
               B:=Matrix(F,2,2,[1,-Coefficients(f)[2],0,1]);
            else
               Z,w:=SFC(f);
               _,v:=IsConsistent(Z,w);
               v:=Eltseq(v);
               Insert(~v,1,1);
               v:= [0: j in [1..i div 2-1]] cat v;
               vect:=v;
               Prune(~v);
               while #v gt 0 do
                  vect cat:=v;
                  Prune(~v);
               end while;
               B:=UpperTriangularMatrix(vect);
            end if;
            Append(~Sm[k],<2,C,B,i,Order(C)>);
            MultSm[k]+:=1;
         end if;
      end for;
   end for;

   // FIRST PART: classes with el.div. of degree at most m
   Omega:=RestrictedPartitions(m,{1..m1});
   for P1 in Omega do
      //mult:=multiplicity of t+1 / 2
      for mult in [1..m1] do
         if not mult in P1 then continue; end if;
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

         // c[i] = [<a_j,b_j>: j]; 
         // means the a_j-th el.div. of dimension i has multiplicity b_j
         // a_j-th el.div. of Sp[i] if a_j <= MultSp[i],
         // otherwise is the (a_j-MultSp[i])-th el. div. of Sm[i]
         // in this first part Sp[i] and Sm[i] are concatenated in a unique list.
         C:=CartesianProduct(R);
         for c in C do
            sign:=1;
            card:=Card;
            order:=1;
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
                     if cij gt 1 then
                        card/:=SequenceToFactorization([<p,Deg*deg*cij*(cij-1) div 4>]);
                     end if;
                     for k in [1..cij] do
                        card/:=Factorization(q^(deg*k div 2)-(-1)^k);
                     end for;
                     order:=Lcm(order,Sm[i][pos][5]);
                  end if;
               end for;
            end for;
            //last part: adding elementary divisors t+1 and correct sign
            Repr:=DiagonalJoin(Repr,IdentityMatrix(F,2*mult));
            B:=DiagonalJoin([FormPlus: j in [1..mult]]);
            if (sign eq -1 and type eq "plus") or (sign eq 1 and type eq "minus") then
               InsertBlock(~B,FormMinus,1,1);
               card/:=FactCard[2][mult];
            else
               card/:=FactCard[1][mult];
            end if;
            Form:=DiagonalJoin(Form,B);
            M:=TransformForm(Form,type1: Restore:=false);
            Append(~ConjClasses,<order,Integers()!card, Gr!(M^-1*Repr*M)>);
         end for;   
      end for;
      // end part with el.div. of degree less than m and at least one is t+1

      // second part: all el.div. of degree less than m and different from t+1
      // this is the only case in which we need to keep track of the sign
      P:=P1;
      set:={i: i in P|Multiplicity(P,i) gt 0};
      Mult:=[Multiplicity(P,i): i in [1..m1]];
      start:=0;
      if type eq "minus" then start:=1; end if;
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
            // an element of C is a m1-tuple whose elements are [a+_i,a-_i], where
            // a+_i = # of el. div. of degree 2i and sign +
            // a-_i = # of el. div. of degree 2i and sign -
         
            for c in C do
               if c[1][1] eq 0 or MultSp[1] ne 0 then       // need this when F=GF(2)
                  if n le 6 or (n gt 6 and (c[2][1] eq 0 or MultSp[2] ne 0)) then
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
                                 if cij gt 1 then
                                    card/:=SequenceToFactorization([<p,Deg*deg*cij*(cij-1) div 4>]);
                                 end if;
                                 for k in [1..cij] do
                                    card/:=Factorization(q^(deg*k div 2)-(-1)^k);
                                 end for;
                                 order:=Lcm(order,Sm[j1][pos][5]);
                              end for;
                           end for;
                           M:=TransformForm(Form,type1: Restore:=false);
                           Append(~ConjClasses,<order,Integers()!card,Gr!(M^-1*Repr*M)>);
                        end for;
                     end for;
                  end if;
               end if;
            end for;
         end for;
      end for;             
   end for;
   // end creating conjugacy classes with blocks of dimension at most m1

   // SECOND PART: classes with at least one el.div. of degree greater than m
   for i in [m1+1..m-1] do
      // TP (resp. TM) contains el.div. of dimension 2*i type pp*, p ne p* (resp. p=p*)
      Tp:=[];
      Tm:=[];
      if i eq 1 then                        
         Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,i) | 
                  x ne t and x ne t+1};
      else
         Y:={{@x, ConjPol(x) @}: x in AllIrreduciblePolynomials(F,i)};
      end if;
      X:=[<a[1],#a>: a in Y];
      for x in X do
         f:=x[1];
         if x[2] eq 2 then
            C:=CompanionMatrix(f);
            ord:=Order(C);
            C:=DiagonalJoin(C,Transpose(C^-1));
            B:=BlockMatrix(2,2,[0,IdentityMatrix(F,i),0,0]);
            Append(~Tp,<1,C,B,i,ord>);
         end if;
      end for;
      R:=CartesianPower(F,i);
      for L in R do
         f:=&+[L[j]*(t^j+t^(2*i-j)): j in [1..i]];
         f:=f+1+t^(2*i)-L[i]*t^i;
         if IsIrreducible(f) then
            C:=CompanionMatrix(f);
            if i eq 1 then
               B:=Matrix(F,2,2,[1,-Coefficients(f)[2],0,1]);
            else
               Z,w:=SFC(f);
               _,v:=IsConsistent(Z,w);
               v:=Eltseq(v);
               Insert(~v,1,1);
               v:= [0: j in [1..i-1]] cat v;
               vect:=v;
               Prune(~v);
               while #v gt 0 do
                  vect cat:=v;
                  Prune(~v);
               end while;
               B:=UpperTriangularMatrix(vect);
            end if;
            Append(~Tm,<2,C,B,2*i,Order(C)>);
 	 end if;
      end for;

      // First part: one of the el.div. of degree <m is t+1 or t-1.
      // In such a case, the sign is corrected when the el.div. t=1 or t-1 is added
      m2:=m-i;
      Omega:=RestrictedPartitions(m-i,{1..m2});
      for P1 in Omega do
         //mult:=multiplicity of t+1 /2
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
                           card/:=SequenceToFactorization([<p,Deg*deg*cij*(cij-1) div 4>]);
                        end if;
                        for k in [1..cij] do
                           card/:=Factorization(q^(deg*k div 2)-(-1)^k);
                        end for;
                        order:=Lcm(order,Sm[j1][pos][5]);
                     end if;
                  end for;
               end for;
               // last part: add the el.div. of degree >m and then t+1
               for x in Tp do
                  Form1:=DiagonalJoin(Form,x[3]);
                  Repr1:=DiagonalJoin(Repr,x[2]);
                  card1:=card/Factorization(q^x[4]-1);
                  order1:=Lcm(order,x[5]);
                  Repr1:=DiagonalJoin(Repr1,IdentityMatrix(F,2*mult));  //last part: adding t+1
                  B1:=DiagonalJoin([FormPlus: j1 in [1..mult]]);
                  if (sign eq -1 and type eq "plus") or (sign eq 1 and type eq "minus") then
                     InsertBlock(~B1,FormMinus,1,1);
                     card1/:=FactCard[2][mult];
                  else
                     card1/:=FactCard[1][mult];
                  end if;
                  M1:=TransformForm(DiagonalJoin(Form1,B1),type1: Restore:=false);
                  Append(~ConjClasses,<order1,Integers()!card1,Gr!(M1^-1*Repr1*M1)>);
               end for;
               sign*:=-1;
               for x in Tm do
                  Form1:=DiagonalJoin(Form,x[3]);
                  Repr1:=DiagonalJoin(Repr,x[2]);
                  card1:=card/Factorization(q^(x[4] div 2)+1);
                  order1:=Lcm(order,x[5]);
                  Repr1:=DiagonalJoin(Repr1,IdentityMatrix(F,2*mult));  //last part: adding t+1
                  B1:=DiagonalJoin([FormPlus: j1 in [1..mult]]);
                  if (sign eq -1 and type eq "plus") or (sign eq 1 and type eq "minus") then
                     InsertBlock(~B1,FormMinus,1,1);
                     card1/:=FactCard[2][mult];
                  else
                     card1/:=FactCard[1][mult];
                  end if;
                  M1:=TransformForm(DiagonalJoin(Form1,B1),type1: Restore:=false);
                  Append(~ConjClasses,<order1,Integers()!card1,Gr!(M1^-1*Repr1*M1)>);
               end for;
            end for;
         end for;

         // second part: there is an el.div. of degree >m or the multiplicity of t+1 is >m
         // in such a case the sign is corrected when the last el.div. is corrected
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

         // c[i] = [<a_j,b_j>: j]: the a_j-th el.div. of dimension i has multiplicity b_j
         // a_j-th el.div. of Sp[i] if a_j <= MultSp[i],
         // otherwise is the (a_j-MultSp[i])-th el. div. of Sm[i]
         C:=CartesianProduct(R);
         for c in C do
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
                     deg:=Sm[j1][pos][4];
                     for k in [1..cij] do
                        Form:=DiagonalJoin(Form,Sm[j1][pos][3]);
                        Repr:=DiagonalJoin(Repr,Sm[j1][pos][2]);
                        sign*:=-1;
                     end for;
                     if cij gt 1 then
                        card/:=SequenceToFactorization([<p,Deg*deg*cij*(cij-1) div 4>]);
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
               for x in Tm do
                  Form1:=DiagonalJoin(Form,x[3]);
                  Repr1:=DiagonalJoin(Repr,x[2]);
                  card1:=card/Factorization(q^(x[4] div 2)+1);
                  M:=TransformForm(Form1,type1: Restore:=false);
                  Append(~ConjClasses,<Lcm(order,x[5]),Integers()!card1, Gr!(M^-1*Repr1*M)>);
               end for;
            else
               for x in Tp do
                  Form1:=DiagonalJoin(Form,x[3]);
                  Repr1:=DiagonalJoin(Repr,x[2]);
                  card1:=card/Factorization(q^x[4]-1);
                  M:=TransformForm(Form1,type1: Restore:=false);
                  Append(~ConjClasses,<Lcm(order,x[5]),Integers()!card1, Gr!(M^-1*Repr1*M)>);
               end for;
            end if;
            // second case: add t+1 with multiplicity >m.
            Repr:=DiagonalJoin(Repr,IdentityMatrix(F,2*i));  //last part: adding t+1
            B1:=DiagonalJoin([FormPlus: j1 in [1..i]]);
            if (sign eq -1 and type eq "plus") or (sign eq 1 and type eq "minus") then
               InsertBlock(~B1,FormMinus,1,1);
               card/:=FactCard[2][i];
            else
               card/:=FactCard[1][i];
            end if;
            M1:=TransformForm(DiagonalJoin(Form,B1),type1: Restore:=false);
            Append(~ConjClasses,<order,Integers()!card,Gr!(M1^-1*Repr*M1)>);
         end for;
      end for;
   end for;

   //part with a unique el. div. deg(pp*)=n or deg(p)=n with p=p*
   if type eq "plus" then
      Y:={{@x, ConjPol(x) @}: 
               x in AllIrreduciblePolynomials(F,m)};
      X:=[<a[1],#a>: a in Y];
      for x in X do
	 f:=x[1];
	 if x[2] eq 2 then
            C:=CompanionMatrix(f);
            ord:=Order(C);
            C:=DiagonalJoin(C,Transpose(C^-1));
            B:=BlockMatrix(2,2,[0,IdentityMatrix(F,m),0,0]);
            M:=TransformForm(B,"orthogonalplus": Restore:=false);
            Append(~ConjClasses,<ord,Integers()!(Card/Factorization(q^m-1)),Gr!(M^-1*C*M)>);
         end if;
      end for;
   else
      R:=CartesianPower(F,m);
      for L in R do
         f:=&+[L[j]*(t^j+t^(n-j)): j in [1..m]];
         f:=f+1+t^n-L[m]*t^m;
         if IsIrreducible(f) then
            C:=CompanionMatrix(f);
            if n eq 2 then
               B:=Matrix(F,2,2,[1,-Coefficients(f)[2],0,1]);
            else
               Z,w:=SFC(f);
               _,v:=IsConsistent(Z,w);
               v:=Eltseq(v);
               Insert(~v,1,1);
               v:= [0: j in [1..n div 2-1]] cat v;
               vect:=v;
               Prune(~v);
               while #v gt 0 do
                  vect cat:=v;
                  Prune(~v);
               end while;
               B:=UpperTriangularMatrix(vect);
            end if;
            M:=TransformForm(B,"orthogonalminus": Restore:=false);
            Append(~ConjClasses,<Order(C),Integers () ! (Card/Factorization(q^m+1)),Gr!(M^-1*C*M)>);
         end if;
      end for;
   end if;

   //part with t+1 as unique el.div.
   Append(~ConjClasses,<1,1,Identity(Gr)>);

   return ConjClasses;
end function;

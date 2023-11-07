freeze;

import "GLCentralizer.m": StdEm;
import "GLCentralizerOrder.m": GLCentralizerOrder;

// returns the smallest k such that (m+k(q-1),q^r-1)=(m,q-1)
PresOrder:=function(q,r,m)  
   g:=Gcd(q-1,m);
   k:=0;
   while Gcd(m+k*(q-1),q^r-1) ne g do
      k+:=1;
   end while;
   return m+k*(q-1);
end function;

// x is an element of S = SL(d, q); determine its centraliser 
SLCentralizer := function (S, x)          
   gl := Generic (S);
   if exists{s: s in Generators (S) | Determinant (s) ne 1} then
      error "Group is not SL";
   end if;
   if Determinant (x) ne 1 then 
      error "Element does not have determinant 1";
   end if;

   F := CoefficientRing (S);
   n := Nrows (x);
   a, b, c := JordanForm (x);

   T := {@ c[i]: i in [1..#c] @};  //begin semisimple part
   Gen := {@@};
   for j in [1..#T] do
      E := ext<F | T[j][1]: Optimize := false>;
      m := Multiplicity (c, T[j]);
      Gr := SL (m, E);
      pos := &+[Multiplicity (c, T[k]) * Degree (T[k][1]) * T[k][2]: 
                  k in [1..j]] - m * Degree (T[j][1]) * T[j][2];
      //creation elements of single blocks of SL
      for k in [1..Ngens(Gr)] do
         r := BlockMatrix(m,m, [StdEm(ScalarMatrix(E,T[j][2],(Gr.k)[l1][l2]),F): l1, l2 in [1..m]]);
         Include (~Gen, gl!InsertBlock (IdentityMatrix (F, n), r, pos+1, pos+1));
      end for;
      w:=PrimitiveElement(E);                                  
      // creation elements in single blocks of determinant non 1 over the larger field
      r:=IdentityMatrix(E,m*T[j][2]);
      for k in [1..T[j][2]] do
         r[k,k]:=w^(IntegerRing()!((#F-1)/Gcd(T[j][2],#F-1)));
      end for;
      r:=StdEm(r,F);
      Include (~Gen, gl!InsertBlock (IdentityMatrix (F, n), r, pos+1, pos+1));
   end for;           //first set of generators
  
   if #F ne 2 then 
      R:=Integers(#F-1);   
      //second set of generators: for which determinant of single block is nonzero
      A:=Matrix(R,#T,1,[T[i][2]: i in [1..#T]]);
      zero:=Matrix(R,1,1,[0]);
      _,_,K:=IsConsistent(A,zero);
      w:=PrimitiveElement(F);
      for k in [1..Ngens(K)] do
         array:=<>;
         for j in [1..#T] do
            E:=ext<F|T[j][1]: Optimize := false>;
            m:=Multiplicity(c,T[j]);
            t:=PrimitiveElement(E);
            t:=t^PresOrder(#F,Degree(T[j][1]),Log(Norm(t,F),w));            
            // end construction of primitive element t of E of norm w
            mat:=IdentityMatrix(E,m*T[j][2]);
            u:=t^(IntegerRing()!PresOrder(#F,Degree(T[j][1]),(K.k)[j]));
            for h in [1..T[j][2]] do
               mat[h,h]:=u;
            end for;
            mat:=GL(m*T[j][2],E)!mat;
            Append(~array,StdEm(mat,F));
         end for;
         Include(~Gen, gl!DiagonalJoin(array));
      end for;
   end if;
   //end semisimple part

   for j in [1..#T] do  //begin internal blocks
      m := T[j][2];
      if m gt 1 then
         E := ext<F | T[j][1]: Optimize := false>;
         mu := Multiplicity (c, T[j]);
         u := StdEm (Matrix(E,1,1,[PrimitiveElement(E)]), F);
         pos := 1;
         if j gt 1 then
            pos +:= &+[Degree (T[i][1]) * T[i][2] *
                       Multiplicity (c, T[i]): i in [1..j-1]];
         end if;
         for k in [1..m-1] do
            for h in [1..Degree (E)] do
               r := IdentityMatrix (F, n);
               for i in [1..m-k] do
                  InsertBlock (~r, u^(h-1), pos+(i-1) * Degree (E, F), 
                     pos + (i+k-1) * Degree (E, F));
               end for;
               Include (~Gen, gl!r);
            end for;
         end for;
      end if;
   end for;  //end internal blocks

   r := IdentityMatrix (F, n);   //begin external blocks
   w:=PrimitiveElement(F);
   pos := 1;
   for i in [1..#c-1] do
      if c[i][1] eq c[i+1][1] and c[i][2] ne c[i+1][2] then
         li := Degree (c[i][1]) * c[i][2];
         lj := Degree (c[i+1][1]) * c[i+1][2];
         for k in [0..Degree(F)-1] do
            Include (~Gen, gl!InsertBlock (r, w^k*IdentityMatrix (F, Min (li, lj)), pos, pos + li + Max (0, lj - li)));
            Include (~Gen, gl!InsertBlock (r, w^k*IdentityMatrix (F, Min (li, lj)), pos+li, pos+Max (li-lj, 0)));
         end for;
      end if;
      pos +:= Degree (c[i][1])*c[i][2];
   end for;   //end external blocks

   //begin construction of generalized Jordan form matrix
   r := DiagonalJoin (<DiagonalJoin ([CompanionMatrix (c[i][1]): 
                        j in [1..c[i][2]]]): i in [1..#c]>);
   pos := 1;
   for i in [1..#c] do
      if c[i][2] ge 2 then
         for j in [1..c[i][2]-1] do
            InsertBlock (~r, IdentityMatrix (F, Degree (c[i][1])), 
               pos + (j-1) * Degree (c[i][1]), pos+j*Degree (c[i][1]));
         end for;
      end if;
      pos +:= Degree (c[i][1]) * c[i][2];
   end for;  //end construction generalized Jordan form matrix

   _,B,_:=JordanForm(x);
   _,C,_:=JordanForm(Generic (S) !r);
   
   H := sub<Generic (S) | Gen>;
   H := H^(GL(n,F)!(C^-1*B));
   order := GLCentralizerOrder (S, x: JF := c);
   H`FactoredOrder := order;
   H`Order := Integers ()!order;
   return H, H`Order;
end function;

freeze;

import "../form.m": IndicateType, SpinN, ConjugatePolynomial;

// element of SO which is not in Omega
SOElement:=function(n,F:Minus:=false)
   if Minus then
      assert exists(y){x : x in Generators(SOMinus(n,F)) |
         SpinN (x, StandardQuadraticForm(n,F: Minus, Variant:="Default"), #F) eq 1};
   elif IsOdd (n) then
      assert exists(y){x : x in Generators(SO(n,F)) |
         SpinN (x, StandardQuadraticForm(n,F: Variant:="Default"), #F) eq 1};
   else
      assert exists(y){x : x in Generators(SOPlus(n,F)) |
         SpinN (x, StandardQuadraticForm(n,F: Variant:="Default"), #F) eq 1};
   end if;
   return y;
end function;

// element of GO^type(n,q) of determinant -1 
// (in the standard Magma copy)
GOElement:=function(n,q: Minus:=false)
   if Minus then 
      assert exists(y){x : x in Generators (GOMinus(n,q)) | Determinant (x) eq -1};
   elif IsOdd (n) then
      if n eq 1 then  
         y := GL(1, q) ![-1]; 
      else
         assert exists(y){x : x in Generators (GO(n,q)) | Determinant (x) eq -1}; 
      end if;
   else 
      assert exists(y){x : x in Generators (GOPlus(n,q)) | Determinant (x) eq -1};
   end if;
   return y;
end function;

// creation CorrectSp = correct special case
// CorrectSp is a matrix in the centralizer of the 
// first elementary divisor with det(CorrectSp) ne 1

CorrectSpecial:=function(c,F,n,q,p,e,type,A,b1: Semisimple:=false)
   sgn:=1;
   if type eq "symplectic" then
      sgn:=F!(-1);
   end if;
   t:=PolynomialRing(F).1;
   ConjPol:=ConjugatePolynomial(type eq "unitary");
   Star:=func<M: exp:=e| Transpose(FrobeniusImage(M,exp))>;
   FirstHasDim1:=false;

   if type eq "unitary" then
      f:=c[1][1];
      d:=c[1][2];
      deg:=Degree(f);
      CorrectSp:=IdentityMatrix(F,n);
      if f eq ConjPol(f) and deg eq 1 then
         B1:=Submatrix(A,1,1,d,d);
         if d eq 1 then
            w:=PrimitiveElement(F);
            y:=w^(p^e-1)*IdentityMatrix(F,1);
         else
            w:=PrimitiveElement(F);
            y:=IdentityMatrix(F,d);
            y[1,1]:=w^(p^e);
            y[d,d]:=w^(-1);
            m:=TransformForm(B1,"unitary": Restore:=false);
            y:=m*y*m^-1;
         end if;
      elif f ne ConjPol(f) then
         B1:=Submatrix(A,1,d*deg+1,d*deg,d*deg);
         C:=CompanionMatrix(f);
         E:=ext<F|f: Optimize := false>;
         w:=PrimitiveElement(E);
         C:=&+[C^(i-1)*Eltseq(w,F)[i]: i in [1..deg]];
         y:=IdentityMatrix(F,d*deg);
         InsertBlock(~y,C,1,1);
         y:=DiagonalJoin(y,Star(B1)*Star(y^-1)*Star(B1^-1));
      else
         C:=CompanionMatrix(f);
         H:=GL(deg,F);
         _,T:=IsConjugate(H,H!C^-1,H!Star(C));
         if Determinant(T+sgn*Star(T)) eq 0 then
            T:=C*T+sgn*Star(C*T);
         else
            T:=T+sgn*Star(T);
         end if;
         T:=T^-1;
         T:=DiagonalJoin([T: j in [1..d]]);
         B1:=Submatrix(A,1,1,d*deg,d*deg)*T;
         E<a>:=ext<F|f: Optimize := false>;
         H1:=ZeroMatrix(E,d,d);    // H1 = matrix B1 over the smaller field
         for j1,j2 in [1..d] do
            H1[j1,j2]:=&+[a^(k-1)*B1[deg*(j1-1)+1,deg*(j2-1)+k]: k in [1..deg]];
         end for;
         w:=PrimitiveElement(E);
         exp:=p^(e*deg)-1;                
         suss:=IdentityMatrix(E,d);
         if d eq 1 then
            suss[1,1]:=w^(p^(e*deg)-1);
         else
            m:=TransformForm(H1,"unitary": Restore:=false);
            suss[1,1]:=w^(p^(e*deg));
            suss[d,d]:=w^-1;
            suss:=m*suss*m^-1;
         end if;
         y:=BlockMatrix(d,d,[&+[C^(k-1)*Eltseq(suss[j1,j2],F)[k]: 
                             k in [1..deg]]: j1,j2 in [1..d]]);
      end if;
      InsertBlock(~CorrectSp,y,1,1);
      CorrectSp:=b1^-1*CorrectSp*b1;
      DetC:=Determinant(CorrectSp);
   else
      f:=c[1][1];
      if p eq 2 or (f ne t+1 and f ne t-1) then
         CorrectSp:=IdentityMatrix(F,n);        
         // in such a case, every element has determinant +1
      else
         if Semisimple then                 
            // in this case is easier to get an element in the centralizer
            d:=c[1][2];
            CorrectSp:=IdentityMatrix(F,n);
            B1:=Submatrix(A,1,1,d,d);
            type1:=IndicateType(B1);
            if type1 eq "orthogonalminus" then
               m:=TransformForm(B1,"orthogonalminus": Restore:=false);
               y:=m*GOElement(d,q: Minus)*m^-1;
            else
               m:=TransformForm(B1,type1: Restore:=false);
               y:=m*GOElement(d,q)*m^-1;
            end if;
            InsertBlock(~CorrectSp,y,1,1);          // YX=XY, detY = -1
         else
            d:=c[1][2];
            pos:=1;
            Exit:=false;       
            // Exit= true if there exists an odd element 
            // in c[i][2] and c[i][1] = t pm 1
            if true in [IsOdd(k): k in d] then
               Exit:=true;
            else
               if #c gt 1 and c[2][1] in {t+1,t-1} then
                  d:=c[2][2];
                  if true in [IsOdd(k): k in d] then
                     pos+:= &+c[1][2];
                     f:=c[2][1];
                     FirstHasDim1:=true;
                     Exit:=true;
                  end if;
               end if;
            end if;
            if Exit then
               B1:=Submatrix(A,pos,pos,&+d,&+d);
               type1:=IndicateType(B1);
               m:=TransformForm(B1,type1);
               y:=IdentityMatrix(F,&+d);
               pos1:=1;
               for d1 in d do
                  for j in [1..d1-1] do
                     y[pos1,pos1+1]:=-ConstantCoefficient(f);
                     pos1+:=1;
                  end for;
                  pos1+:=1;
               end for;
               y:=GL(&+d,q)!(m^-1*y*m);
               case type1:
                  when "orthogonalplus":
                     MyH := GOPlus(&+d,q); MyH`ClassicalType:="GO+";
                     Cent:=InternalUnipotentCentralizer(MyH,y);
                  when "orthogonalminus":
                     MyH := GOMinus(&+d,q); MyH`ClassicalType:="GO-";
                     Cent:=InternalUnipotentCentralizer(MyH,y);
                  when "orthogonal", "orthogonalcircle":
                     if &+d eq 1 then
                        Cent:=sub<GL(1,q)|-IdentityMatrix(F,1)>;
                     else
                        MyH := GO(&+d,q); MyH`ClassicalType:="GO";
                        Cent:=InternalUnipotentCentralizer(MyH,y);
                     end if;
               end case;
               for j in [1..Ngens(Cent)] do
                  if Determinant(Cent.j) eq -1 then
                     CorrectSp:=InsertBlock(IdentityMatrix(F,n),m*Cent.j*m^-1,pos,pos);
                     break j;
                  end if;
               end for;
            else
               CorrectSp:=IdentityMatrix(F,n);
            end if;
         end if;
      end if;
      CorrectSp:=b1^-1*CorrectSp*b1;
   end if;

   return CorrectSp, FirstHasDim1;
end function;

// creation CorrectO = correct Omega case
// CorrectO is a matrix in the centralizer of the 
// first elementary divisor with Det(CorrectO)=1, SpinorNorm(CorrectO)=1

CorrectOmega:=function(c,F,n,q,p,e,type,A,b1: Semisimple:=false)

   if Semisimple eq false then
      pr:=PrimitiveElement(F);
      z:=IdentityMatrix(F,n);
      if n eq 2 then
         z := SOElement (2, F: Minus := type eq "Omega-");
      else
         if IsOdd(q) then
            z[1,1]:=pr;
            z[n,n]:=pr^-1;
         else
            z[1,1]:=0; z[n,n]:=0;
            z[n,1]:=1; z[1,n]:=1;
         end if;
      end if;

      return z, false;
   end if;

   sgn:=1;
   if type eq "symplectic" then
      sgn:=F!(-1);
   end if;
   t:=PolynomialRing(F).1;
   ConjPol:=ConjugatePolynomial(type eq "unitary");
   Star:=func<M: exp:=e| Transpose(FrobeniusImage(M,exp))>;

   FirstHasDim1:=false;
   if IsEven(p) then
      if c[1][1] ne t+1 then
         CorrectO:=IdentityMatrix(F,n);   
         // in this case every element of the centralizer has spinor norm=0
      else
         CorrectO:=IdentityMatrix(F,n);
         d:=c[1][2];
         B1:=Submatrix(A,1,1,d,d);
         w:=PrimitiveElement(F);
         type1:=IndicateType(B1);
         if type1 eq "orthogonalplus" then
            m:=TransformForm(B1,"orthogonalplus": Restore:=false);
            // y:=IdentityMatrix(F,d);
            // y[d div 2, d div 2]:=0; y[d div 2+1, d div 2+1]:=0;
            // y[d div 2, d div 2+1]:=1; y[d div 2+1, d div 2]:=1;
            y := SOElement (d,F);
         else
            m:=TransformForm(B1,"orthogonalminus": Restore:=false);
            // y:=IdentityMatrix(F,d);
            // y[d div 2 +1, d div 2]:=1;           // y in SO, y not in Omega
            y := SOElement (d,F: Minus:=true);
         end if;
         y:=m*y*m^-1;
         InsertBlock(~CorrectO,y,1,1);   // YX=XY, SpinorNorm(Y) = 1
         CorrectO:=b1^-1*CorrectO*b1;
      end if;
   else
      f:=c[1][1];
      d:=c[1][2];
      pos:=1;
      // there are no elements of spinor norm 1 and determinant 1 in GO(1,q), 
      // so the correction has to be made on the second elementary divisor
      if d eq 1 and f in {t+1,t-1} then
         f:=c[2][1];
         d:=c[2][2];
         FirstHasDim1:=true;
         pos:=2;
      end if;
      CorrectO:=IdentityMatrix(F,n);
      deg:=Degree(f);
      if f eq t+1 or f eq t-1 then
         B1:=Submatrix(A,pos,pos,d,d);
         if IsOdd(d) then
            m:=TransformForm(B1,"orthogonal": Restore:=false);
            // w:=PrimitiveElement(F);
            // y:=IdentityMatrix(F,d);
            // y[1,1]:=w; y[d,d]:=w^-1;  
            // y in SO, y not in Omega
            y := SOElement (d, F);
         elif IndicateType(B1) eq "orthogonalplus" then
            m:=TransformForm(B1,"orthogonalplus": Restore:=false);
            // w:=PrimitiveElement(F);
            // y:=IdentityMatrix(F,d);
            // y[1,1]:=w; y[d,d]:=w^-1;  
            // y in SO, y not in Omega
            y := SOElement (d, F);
         else
            m:=TransformForm(B1,"orthogonalminus": Restore:=false);
            y:=IdentityMatrix(F,d);
            //generating element of SOMinus(2,q) subset SOMinus(d,q)
            w:=PrimitiveElement(F);
            E:=ext<F|t^2-w: Optimize := false>;
            l:=PrimitiveElement(E);
            T:=l+l^q;
            N:=l^(q+1);
            b:=(l-l^q)/l^((q+1) div 2);
            a1:=(T^2-2*N)/(2*N);
            a2:=T*b/(2*N);
            y[d div 2,d div 2]:=a1;
            y[d div 2, d div 2 +1]:=a2;
            y[d div 2+1, d div 2]:=a2*N;
            y[d div 2+1, d div 2+1]:=a1;
            B2:=DiagonalMatrix(F,[1: i in [1.. d div 2]] cat [-1: i in [1..d div 2]]);
            B2:=InsertBlock(B2,Matrix(F,2,2,[1,0,0,-l^(q+1)]), d div 2, d div 2);
            m1:=TransformForm(B2, "orthogonalminus": Restore:=false);
            y:=m1^-1*y*m1;
         end if;
         y:=m*y*m^-1;
      elif f ne ConjPol(f) then
         B1:=Submatrix(A,pos,d*deg+pos,d*deg,d*deg);
         E<a>:=ext<F|f: Optimize := false>;
         y:=&+[CompanionMatrix(f)^(i-1)*Eltseq(PrimitiveElement(E),F)[i]: i in [1..deg]];
         y:=DiagonalJoin(y,IdentityMatrix(F,deg*(d-1)));
         y:=DiagonalJoin(y,Star(B1^-1*y^-1*B1));
      else
         C:=CompanionMatrix(f);
         H:=GL(deg,F);
         _,T:=IsConjugate(H,H!C^-1,H!Star(C));
         if Determinant(T+sgn*Star(T)) eq 0 then
            T:=C*T+sgn*Star(C*T);
         else
            T:=T+sgn*Star(T);
         end if;
         T:=DiagonalJoin([T: j in [1..d]]);
         B1:=Submatrix(A,pos,pos,d*deg,d*deg)*T^-1;
         E<a>:=ext<F|f: Optimize := false>;
         // H1 = matrix B1 over the smaller field
         H1:=ZeroMatrix(E,d,d);
         for j1,j2 in [1..d] do
            H1[j1,j2]:=&+[a^(k-1)*B1[deg*(j1-1)+1,deg*(j2-1)+k]: k in [1..deg]];
         end for;
         w:=PrimitiveElement(E);
         suss:=IdentityMatrix(E,d);
         if d eq 1 then
            suss[1,1]:=w^(#F^(deg div 2)-1);
         else
            m:=TransformForm(H1,"unitary": Restore:=false);
            suss[1,1]:=w^(#F^(deg div 2)); suss[d,d]:=w^-1;
            suss:=m*suss*m^-1;
         end if;
         y:=BlockMatrix(d,d,[&+[C^(k-1)*Eltseq(suss[j1,j2],F)[k]: k in [1..deg]]: j1,j2 in [1..d]]);
      end if;
      InsertBlock(~CorrectO,y,pos,pos);
      CorrectO:=b1^-1*CorrectO*b1;
   end if;

   return CorrectO, FirstHasDim1;
end function;

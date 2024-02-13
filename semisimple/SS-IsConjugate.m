freeze;

import "form.m": DetermineForm, IsElementOf, IndicateType, SpinN, ConjugatePolynomial;
import "Centralizer/Correctors.m": GOElement, SOElement;

// X* := conjugate transpose of X
// return Y s.t. B1=Y B2 Y*,
// where Y* considered as matrix in GU(n,ext<GF(q)|f>) and not in GL(n*deg(f),GF(q))

SwitchMatrix:=function(B1,B2,f)
   F:=BaseRing(B1);
   K<a>:=ext<F|f: Optimize := false>;
   d:=Degree(K,F);
   n:=Nrows(B1) div d;

   s1:=ZeroMatrix(K,n,n);
   s2:=ZeroMatrix(K,n,n);
   for i,j in [1..n] do
      s1[i,j]:=&+[a^(k-1)*B1[d*(i-1)+1,d*(j-1)+k]: k in [1..d]];
      s2[i,j]:=&+[a^(k-1)*B2[d*(i-1)+1,d*(j-1)+k]: k in [1..d]];
   end for;
   m1:=TransformForm(s1,"unitary": Restore:=false);
   m2:=TransformForm(s2,"unitary": Restore:=false);
   suss:=m1*m2^-1;
   Y:=ZeroMatrix(F,n*d,n*d);
   for i,j in [1..n] do
   for h,k in [1..d] do
      Y[d*(i-1)+h,d*(j-1)+k]:=Eltseq(K!(a^(h-1)*suss[i,j]),F)[k];
   end for;
   end for;

   return Y;
end function;

// return z in G such that z^-1*x*z = y;
// works only for x1,x2 semisimple
// works for G = Sp, GU, SU, GO, SO, Omega
// exclude orthogonal groups in odd dimension and even characteristic

SSIsConjugate:=function(G,x2,x1)

   F:=BaseRing(G);
   n:=Nrows(x1);
   p:=Characteristic(F);
   M:=MatrixAlgebra(F,n);
   t:=PolynomialRing(F).1;

   B,type,sgn,special,IsOmega,Q:=DetermineForm(G,x1);
   if assigned Q then 
      special2, IsOmega2 := IsElementOf (G, x2, type, B, Q);
   else 
      special2, IsOmega2 := IsElementOf (G, x2, type, B, []);
   end if;
   if (special2 ne special) or (IsOmega2 ne IsOmega) then 
      error "Both elements do not lie in same input group";
   end if;

   e := type eq "unitary" select Degree (F) div 2 else 0;

   //conjugate transpose matrix
   Star:=func<M: exp:=e| Transpose(FrobeniusImage(M,exp))>;
   //conjugate polynomial
   ConjPol:=ConjugatePolynomial(type eq "unitary");

   a1,b1,r1:=JordanForm(x1);
   a2,b2,r2:=JordanForm(x2);

   if a1 ne a2 then return false,_; end if;

   // Little change in Jordan Form:
   // now c1 = [<f_i,m_i>, i], with m_i = multiplicity of el. div. f_i
   // need to put t+1 and t-1 at the end of the list
   Set1:={x: x in r1};
   Set2:={x: x in r2};
   c1:=[<x[1],Multiplicity(r1,x)>: x in Set1 | x[1] ne t-1 and x[1] ne t+1];
   c2:=[<x[1],Multiplicity(r2,x)>: x in Set2 | x[1] ne t-1 and x[1] ne t+1];
   for x in Set1 do
      if x[1] eq t-1 or x[1] eq t+1 then
         Append(~c1,<x[1],Multiplicity(r1,x)>);
         Append(~c2,<x[1],Multiplicity(r2,x)>);
      end if;
   end for;

   X:=ZeroMatrix(F,0,0);
   i:=1;
   while i le #c1 do
      f:=c1[i][1];
      d:=c1[i][2];
      if f eq ConjPol(f) then
         X:=DiagonalJoin(X,DiagonalJoin([CompanionMatrix(f): j in [1..d]]));
      else
         X:=DiagonalJoin(X,DiagonalJoin([CompanionMatrix(f): j in [1..d]]));
         X:=DiagonalJoin(X,DiagonalJoin([Star(CompanionMatrix(f))^-1: j in [1..d]]));
         Exclude(~c1, <ConjPol(f),d>);
      end if;
      i+:=1;
   end while;
   _,bX,_:=JordanForm(X);
   d1:=bX^-1*b1;
   d2:=bX^-1*b2;

   if assigned Q and IsEven (p) then 
      A1:=d1*Q*Star(d1);
      A2:=d2*Q*Star(d2);
   else 
      A1:=d1*B*Star(d1);
      A2:=d2*B*Star(d2);
   end if;

   // method: compute an easy form X, and compute d1, d2 s.t. d1 x1 d1^-1 = X = d2 x2 d2^-1. 
   // Thus X is isometry for A1,A2 defined above. 
   // Compute Y such that YA2Y* = A1. 
   // The conjugating element is d2^-1Y^-1d1.

   if type in {"orthogonalplus", "orthogonalminus", "orthogonal", "orthogonalcircle"} and p ne 2 then
      if Determinant(M!x1-1) eq 0 and Determinant(M!x1+1) eq 0 then
         k:=c1[#c1][2];      // the last element in c1 is t-1 or t+1
         B1:=Submatrix(A1,n-k+1,n-k+1,k,k);
         B2:=Submatrix(A2,n-k+1,n-k+1,k,k);
         if not IsSquare(Determinant(B1)*Determinant(B2)) then
	    return false,_;
         end if;
      end if;
   end if;

   // turn the matrices A1, A2 into upper triangular matrices in quadratic case
   if type in {"orthogonalplus", "orthogonalminus", "orthogonal", "orthogonalcircle"} and p eq 2 then
      for i in [1..n] do
         for j in [i+1..n] do
            A1[i,j]+:=A1[j,i];
            A2[i,j]+:=A2[j,i];
            A1[j,i]:=0;
            A2[j,i]:=0;
         end for;
      end for;
   end if;

   // create conjugating element in GO / Sp / GU
   Y:=ZeroMatrix(F,n,n);
   pos:=1;
   i:=1;
   while i le #c1 do
      f:=c1[i][1];
      d:=c1[i][2];
      if f eq ConjPol(f) and Degree(f) eq 1 then
         B1:=Submatrix(A1,pos,pos,d,d);
         B2:=Submatrix(A2,pos,pos,d,d);
         type1:=type;
         if type ne "unitary" and type ne "symplectic" then
            type1:=IndicateType(B1);
         end if;
         m1:=TransformForm(B1,type1: Restore:=false);
         m2:=TransformForm(B2,type1: Restore:=false);
         InsertBlock(~Y,m1*m2^-1,pos,pos);
         pos+:=d;
      elif f ne ConjPol(f) then
         ni:=Degree(f)*d;
         if type ne "unitary" and type ne "symplectic" and p eq 2 then
            Y1:=Submatrix(A1,pos,pos+ni,ni,ni);
            Y2:=Submatrix(A2,pos,pos+ni,ni,ni);
         else
            Y1:=Submatrix(A1,pos,pos+ni,ni,ni);
            Y2:=Submatrix(A2,pos,pos+ni,ni,ni);
         end if;
         Y1:=Y1*Y2^-1;
         Y1:=DiagonalJoin(Y1,IdentityMatrix(F,ni));
         InsertBlock(~Y,Y1,pos,pos);
         pos+:=2*ni;
      else
         ni:=Degree(f)*d;
         R:=CompanionMatrix(f);
         H:=GL(Degree(f),F);
         _,T:=IsConjugate(H,H!R^-1,H!Star(R));
         if Determinant(T+sgn*Star(T)) eq 0 then
            T:=R*T+sgn*Star(R*T);
         else
            T:=T+sgn*Star(T);
         end if;
         T:=DiagonalJoin([T: j in [1..d]]);
         B1:=Submatrix(A1,pos,pos,ni,ni)*T^-1;
         B2:=Submatrix(A2,pos,pos,ni,ni)*T^-1;
         if type ne "unitary" and type ne "symplectic" and p eq 2 then
            B1+:=Transpose(Submatrix(A1,pos,pos,ni,ni))*T^-1;
            B2+:=Transpose(Submatrix(A2,pos,pos,ni,ni))*T^-1;
         end if;
         Y1:=SwitchMatrix(B1,B2,f);
         InsertBlock(~Y,Y1,pos,pos);
         pos+:=ni;
      end if;
      i+:=1;
   end while;

   // in the special case, if det Z ne 1, then need to be multiplied by Y
   // such that x1 Y = Y x1 and det Y = det Z^-1
   Z:=d2^-1*Y^-1*d1;
   if special or IsOmega then
      if Determinant(Z) ne 1 then
         if type eq "unitary" then
            f:=c1[1][1];
            d:=c1[1][2];
            det:=Determinant(Z)^-1;
            deg:=Degree(f);
            Y:=IdentityMatrix(F,n);
            if f eq ConjPol(f) and deg eq 1 then
               B1:=Submatrix(A1,1,1,d,d);
               if d eq 1 then
                  y:=det*IdentityMatrix(F,1);
               else
                  w:=PrimitiveElement(F);
                  l:=Log(w,det) div (p^e-1);
                  y:=IdentityMatrix(F,d);
                  y[1,1]:=w^(l*p^e);
                  y[d,d]:=w^(-l);
                  m:=TransformForm(B1,"unitary": Restore:=false);
                  y:=m*y*m^-1;
               end if;
            elif f ne ConjPol(f) then
               B1:=Submatrix(A1,1,d*deg+1,d*deg,d*deg);
               C:=CompanionMatrix(f);
               E:=ext<F|f: Optimize := false>;
               w:=PrimitiveElement(E);
               C:=&+[C^(i-1)*Eltseq(w,F)[i]: i in [1..deg]];
               l:=Log(Determinant(C),det) div (p^e-1);
               y:=IdentityMatrix(F,d*deg);
               InsertBlock(~y,C^-l,1,1);
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
               T:=DiagonalJoin([T: j in [1..d]]);
               B1:=Submatrix(A1,1,1,d*deg,d*deg)*T^-1;
               E<a>:=ext<F|f: Optimize := false>;
               // H1 = matrix B1 over the smaller field
               H1:=ZeroMatrix(E,d,d);
               for j1,j2 in [1..d] do
                  H1[j1,j2]:=&+[a^(k-1)*B1[deg*(j1-1)+1,deg*(j2-1)+k]: k in [1..deg]];
               end for;
               m:=TransformForm(H1,"unitary": Restore:=false);
               w:=PrimitiveElement(E);
               l:=Log(Norm(w^(p^(e*deg)-1),F),det);
               suss:=IdentityMatrix(E,d);
               if d eq 1 then
                  suss[1,1]:=w^(p^(e*deg)-1);
               else
                  m:=TransformForm(H1,"unitary": Restore:=false);
                  suss[1,1]:=w^(p^(e*deg));
                  suss[d,d]:=w^-1;
                  suss:=m*suss*m^-1;
               end if;
               suss:=suss^l;
               y:=BlockMatrix(d,d,[&+[C^(k-1)*Eltseq(suss[j1,j2],F)[k]: k in [1..deg]]: j1,j2 in [1..d]]);
            end if;
            InsertBlock(~Y,y,1,1);
            Y:=d1^-1*Y*d1;
            Z:=Z*Y;
         else
            if Determinant(M!x1-1) ne 0 and Determinant(M!x1+1) ne 0 then
	       return false,_;
            else
               Y:=IdentityMatrix(F,n);
               d:=c1[#c1][2];
               B1:=Submatrix(A1,n-d+1,n-d+1,d,d);
               if IsOdd(d) then
                  m:=TransformForm(B1,"orthogonal": Restore:=false);
                  // y:=IdentityMatrix(F,d);
                  // y[d div 2+1, d div 2+1]:=-1;
                  // element of determinant -1
                  y:=GOElement(d,F);
                  y:=m*y*m^-1;
               elif IsSquare((F!-1)^(d div 2)*Determinant(B1)) then
                  m:=TransformForm(B1,"orthogonalplus": Restore:=false);
                  // y:=IdentityMatrix(F,d);
                  // y[1,1]:=0; y[1,d]:=1; y[d,1]:=1; y[d,d]:=0;
                  // element of determinant -1
                  y:=GOElement(d,F);
                  y:=m*y*m^-1;
               else
                  m:=TransformForm(B1,"orthogonalminus": Restore:=false);
                  // y:=IdentityMatrix(F,d);
                  // y[d div 2+1, d div 2+1]:=-1;
                  // element of determinant -1
                  y:=GOElement(d,F:Minus:=true);
                  y:=m*y*m^-1;
               end if;
               InsertBlock(~Y,y,n-d+1,n-d+1);       // YX=XY, detY = -1
               // following should hold 
               // assert X*Y eq Y*X
               Y:=d1^-1*Y*d1;
               Z:=Z*Y;
            end if;
         end if;
      end if;
   end if;

   // in the omega case, if SpinorNorm(Z) ne 0, then need to be multiplied by Y
   // such that x1 Y = Y x1 and SpinorNorm(Y) ne 0
   if IsOmega then
      if SpinN(GL(n,F)!Z,Q,p) ne 0 then
         if IsEven(p) then
            if Determinant(M!x1+1) ne 0 then
	       return false,_;
            else
               Y:=IdentityMatrix(F,n);
               d:=c1[#c1][2];
               B1:=Submatrix(A1,n-d+1,n-d+1,d,d);
               w:=PrimitiveElement(F);
               if WittIndex(QuadraticSpace(B1)) eq d div 2 then
                  type1:="orthogonalplus";
               else
                  type1:="orthogonalminus";
               end if;
               // y in SO, y not in Omega
               if type1 eq "orthogonalplus" then
                  m:=TransformForm(B1,"orthogonalplus": Restore:=false);
                  // y:=IdentityMatrix(F,d);
                  // y[d div 2, d div 2]:=0; y[d div 2+1, d div 2+1]:=0;
                  // y[d div 2, d div 2+1]:=1; y[d div 2+1, d div 2]:=1;
                  y:=SOElement (d,F);
               else
                  m:=TransformForm(B1,"orthogonalminus": Restore:=false);
                  // y:=IdentityMatrix(F,d);
                  // y[d div 2+1, d div 2]:=1;       
                  y:=SOElement (d,F: Minus:=true);
               end if;
               y:=m*y*m^-1;
               InsertBlock(~Y,y,n-d+1,n-d+1);   // YX=XY, SpinorNorm(Y) = 1
               Y:=d1^-1*Y*d1;
               Z:=Z*Y;
            end if;
         else
            f:=c1[1][1];
            d:=c1[1][2];
            pos:=1;
            // the case d*Degree(f)=1 is hard to manage, so better to avoid it
            if d eq 1 and f in {t+1,t-1} then
               f:=c1[2][1];
               d:=c1[2][2];
               pos:=2;
            end if;
            Y:=IdentityMatrix(F,n);
            if f eq t+1 or f eq t-1 then
               B1:=Submatrix(A1,pos,pos,d,d);
               if IsOdd(d) then
                  m:=TransformForm(B1,"orthogonal": Restore:=false);
                  // w:=PrimitiveElement(F);
                  // y:=IdentityMatrix(F,d);
                  // y[1,1]:=w;   y[d,d]:=w^-1;            
                  // y in SO, y not in Omega
                  y:=SOElement (d,F);
               elif IsSquare((F!-1)^(d div 2)*Determinant(B1)) then
                  m:=TransformForm(B1,"orthogonalplus": Restore:=false);
                  w:=PrimitiveElement(F);
                  y:=IdentityMatrix(F,d);
                  // y[1,1]:=w;   y[d,d]:=w^-1;            
                  // y in SO, y not in Omega
                  y:=SOElement (d,F);
               else
                  m:=TransformForm(B1,"orthogonalminus": Restore:=false);
                  y:=IdentityMatrix(F,d);
                  //generating element of SOMinus(2,q) subset SOMinus(d,q)
                  w:=PrimitiveElement(F);
                  E:=ext<F|t^2-w: Optimize := false>;
                  q:=#F;
                  l:=PrimitiveElement(E);
                  T:=l+l^q;
                  N:=l^(q+1);
                  b:=(l-l^q)/l^((q+1) div 2);
                  a1:=(T^2-2*N)/(2*N);
                  a2:=T*b/(2*N);
                  y[d div 2,d div 2]:=a1;
                  y[d div 2, d div 2+1]:=a2;
                  y[d div 2+1, d div 2]:=a2*N;
                  y[d div 2+1, d div 2+1]:=a1;
                  B2:=DiagonalMatrix(F,[1: i in [1..d div 2]] cat [-1: i in [1..d div 2]]);
                  B2:=InsertBlock(B2,Matrix(F,2,2,[1,0,0,-l^(q+1)]), d div 2, d div 2);
                  m1:=TransformForm(B2, "orthogonalminus": Restore:=false);
                  y:=m1^-1*y*m1;
               end if;
               y:=m*y*m^-1;
            elif f ne ConjPol(f) then
               B1:=Submatrix(A1,pos,d*Degree(f)+pos,d*Degree(f),d*Degree(f));
               E<a>:=ext<F|f: Optimize := false>;
               y:=&+[CompanionMatrix(f)^(i-1)*Eltseq(PrimitiveElement(E),F)[i]: i in [1..Degree(f)]];
               y:=DiagonalJoin(y,IdentityMatrix(F,Degree(f)*(d-1)));
               y:=DiagonalJoin(y,Star(B1^-1*y^-1*B1));
            else
               C:=CompanionMatrix(f);
               H:=GL(Degree(f),F);
               _,T:=IsConjugate(H,H!C^-1,H!Star(C));
               if Determinant(T+sgn*Star(T)) eq 0 then
                  T:=C*T+sgn*Star(C*T);
               else
                  T:=T+sgn*Star(T);
               end if;
               T:=DiagonalJoin([T: j in [1..d]]);
               B1:=Submatrix(A1,pos,pos,d*Degree(f),d*Degree(f))*T^-1;
               E<a>:=ext<F|f: Optimize := false>;
               // H1 = matrix B1 over the smaller field
               H1:=ZeroMatrix(E,d,d);
               for j1,j2 in [1..d] do
                  H1[j1,j2]:=&+[a^(k-1)*B1[Degree(f)*(j1-1)+1,Degree(f)*(j2-1)+k]: k in [1..Degree(f)]];
               end for;
               w:=PrimitiveElement(E);
               suss:=IdentityMatrix(E,d);
               if d eq 1 then
                  suss[1,1]:=w^(#F^(Degree(f) div 2)-1);
               else
                  m:=TransformForm(H1,"unitary": Restore:=false);
                  suss[1,1]:=w^(#F^(Degree(f) div 2)); suss[d,d]:=w^-1;
                  suss:=m*suss*m^-1;
               end if;
               y:=BlockMatrix(d,d,[&+[C^(k-1)*Eltseq(suss[j1,j2],F)[k]: k in [1..Degree(f)]]: j1,j2 in [1..d]]);
            end if;
            InsertBlock(~Y,y,pos,pos);
            Y:=d1^-1*Y*d1;
            Z:=Z*Y;
         end if;
      end if;
   end if;

   return true, GL(n,F)!Z;
end function;

intrinsic InternalSemisimpleIsConjugate (G:: GrpMat, g:: GrpMatElt, h:: GrpMatElt) -> GrpMatElt 
{if semisimple g and h are conjugate in classical group G, return true and 
conjugating element, else false}
   require IsSemisimple (g) and IsSemisimple (h): "Both elements must be semisimple";
   return SSIsConjugate (G, g, h);
end intrinsic;

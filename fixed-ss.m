freeze;

import "semisimple/form.m": IndicateType, FormForCompanionMatrix, 
  CheckSplitOmega, SpinN, ConjugatePolynomial;
import "semisimple/card.m": CardinalityOfClassicalGroup;
import "unipotent/good-char.m": GUUnipotentBlock;
import "unipotent/Centraliser-Order.m": UnipotentCentralizerOrder;
import "Gen-Classes.m": IsometryGroupCardinality;
import "semisimple/Centralizer/Correctors.m": GOElement, SOElement;

// make a label for an el. div. of type 1 or 2 
// similar to that for el. div. of type 0
LabelHomogenize := function (L, F, type)
   if type in {"SU", "GU"} then
      L1 := Multiset ([a: a in L]);
   elif IsEven (#F) then
      Z := Integers ();
      L1 := <Sort ([a: a in L]), [Z |], [Z |], [Z |], 1>;
   else
      L1 := Multiset ([<a, F!1>: a in L]);
   end if;
   return L1;
end function;

// return the label of the other class in GO with same Jordan form
ChangeClassLabel:=function(L,F,pr)
   setl:=L;
   
   arr_dim := [x[1]: x in L | IsOdd(x[1]) ];
   set_dim := { < x, Multiplicity (arr_dim, x) > : x in arr_dim };
   for x in set_dim do
      if IsOdd (x[2]) then
         if < x[1], pr > in setl then
            Exclude (~setl, < x[1], pr >);
            Include (~setl, < x[1], F!1 >);
         else
            Exclude (~setl, < x[1], F!1 >);
            Include (~setl, < x[1], pr >);
         end if;
      end if;
   end for;
   
   return setl;
end function;

// change the label of a unipotent element in GO (n, q) for odd n 
// by switching all the discriminants
// if DoIt eq false, then return L without changing it
ChangeLabel := function (L, F, pr, DoIt)
   if not DoIt then
      return L;
   else
      setl := ChangeClassLabel (L[3], F, pr);
      return <L[1], L[2], Multiset (setl)>;
   end if;
end function;

// return an element in GO with determinant -1 in the centralizer 
// of the semisimple part defined by c, where c, L are the lists 
// described in AllUnipotentElementsOfS

AddClass := function (type, L, c, m, F, n: IsOmega := false)
   pos := 1;
   done := false;

   Y := IdentityMatrix (F, n);
   for i in [1..#c] do
      if L[i][3] eq 0 then
         if IsOmega then
            d := L[i][2];
            z := IdentityMatrix (F, d);
            if d eq 1 then
               pos +:= 1;
            elif d eq 2 then
               z := SOElement (2, F: Minus := IndicateType (c[i][4]) eq "orthogonalminus");
               InsertBlock (~Y, z, pos, pos);
               done := true;
               break i;
            else
               if IsOdd (#F) then
                  pr := PrimitiveElement (F);
                  z[1, 1] := pr;
                  z[d, d] := pr^-1;
               else
                  z[1, 1] := 0; z[d, d] := 0;
                  z[d, 1] := 1; z[1, d] := 1;
               end if;
               InsertBlock (~Y, z, pos, pos);
               done := true;
               break i;
            end if;
         elif type eq "SU" then
            w := PrimitiveElement (F);
            _, q := IsSquare (#F);
            k := L[i][2];
            if k eq 1 then
               Y[1, 1] := w^(q-1);
            else
               Y[1, 1] := w^q;
               Y[k, k] := w^-1;
            end if;
            done := true;
            break i;
         else
            if L[i][2] eq 2 then
               z := GOElement (2, F: Minus := IndicateType (c[i][4]) eq "orthogonalminus");
               InsertBlock (~Y, z, pos, pos);
            else
               // an element of det -1
               Y[pos, pos] := 0; Y[pos+L[i][2]-1, pos+L[i][2]-1] := 0;
               Y[pos, pos+L[i][2]-1] := 1; Y[pos+L[i][2]-1, pos] := 1;
            end if;
            done := true;
            break i;
         end if;
      elif L[i][3] eq 1 then
         if IsOmega or type eq "SU" then
            f := L[i][1];
            d := Degree (f);
            C := CompanionMatrix (f);
            E<l> := ext<F|f: Optimize := false>;
            w := PrimitiveElement (E);
            y := &+[Eltseq (w, F)[j]*C^(j-1): j in [1..d]];
            InsertBlock (~Y, y, pos, pos);
            if type eq "SU" then
               e := Degree (F) div 2;
               InsertBlock (~Y, Transpose (FrobeniusImage (y^-1, e)), pos+L[i][2]*d, pos+L[i][2]*d);
            else
               InsertBlock (~Y, Transpose (y^-1), pos+L[i][2]*d, pos+L[i][2]*d);
            end if;
            done := true;
            break i;
         else
            pos +:= 2*L[i][2]*Degree (L[i][1]);
         end if;
      else
         if IsOmega or type eq "SU" then
            f := L[i][1];
            d := Degree (f);
            k := L[i][2];
            C := CompanionMatrix (f);
            E<l> := ext<F|f: Optimize := false>;
            w := PrimitiveElement (E);
            if type eq "SU" then
               _, q := IsSquare (#F);
               q := q^d;
            else
               q := (#F)^(d div 2);
            end if;
            if k eq 1 then
               w := w^(q-1);
               y := &+[Eltseq (w, F)[j]*C^(j-1): j in [1..d]];
               InsertBlock (~Y, y, pos, pos);
 	    else
	       y := &+[Eltseq (w^q, F)[j]*C^(j-1): j in [1..d]];
               InsertBlock (~Y, y, pos, pos);
               y := &+[Eltseq (w^-1, F)[j]*C^(j-1): j in [1..d]];
               InsertBlock (~Y, y, pos+d*(k-1), pos+d*(k-1));
            end if;
            done := true;
            break i;
         else
            pos +:= L[i][2]*Degree (L[i][1]);
         end if;
      end if;
   end for;

   // this happens only when x^2-1 is nonsingular and IsOmega eq false
   if done eq false then
      if n eq 2 then
         Y := GOElement (2, F: Minus := type in {"SO-", "Omega-"});
      else
         Y[1,1] := 0; Y[1,n] := 1;
         Y[n,1] := 1; Y[n,n] := 0;
      end if;
   else
     Y := m^-1*Y*m;
   end if;

   return Y;
end function;

// L is a vector [ <f1, m1>, <f2, m2>, ... , <fk, mk>], 
// where f_i irreducible polynomial, m_i its multiplicity;
// if f_i neq f_i*, the function provides automatically 
// to put the elementary divisor f_i*;

// elements of L could also have the form <fi, mi, type, Bi>, 
// with type = 0, 1, 2 (resp. (t pm 1), ff* and f=f*) and 
// Bi matrix of the form preserved by f_i
// if missing, this data is added at the start of the code;

// the function returns all conjugacy classes having semisimple part 
// described by L in the standard MAGMA copy;
// if the parameter SameSSPart is true, then the semisimple part is 
// the same for all the representatives.

// Assumptions: 
// StandardSymmetricForm (n, q: Variant := "Default") 
// for odd n and q the determinant is GF(q) ! ((-1)^((n-1) div 2) * (1/2))
//
// _, _, _, _, Forms := UnipotentClasses ("GO", n, q); 
// for odd n and odd q, the elements in Forms have square determinant 
// this is checked in UnipotentClasses 

AllUnipotentElementsOfS := function (type, L: SameSSPart := false, DataArray := <>, CardOfG := 1)

   F := BaseRing (L[1][1]);
   q := #F;
   p := Characteristic (F);
   e := Degree (F) div 2;
   unitary := 1;
   if type in {"GU", "SU"} then
      _, q := IsSquare (q);
      unitary := q;
      Star := func<M : exp := e | Transpose (FrobeniusImage (M, exp))>;
   else
      Star := func<M | Transpose (M)>;
   end if;
   pr := PrimitiveElement (F);
   t := PolynomialRing (F).1;
   ConjPol := ConjugatePolynomial (unitary eq q);

   // add information if L is incomplete
   information := false;
   if #L[1] eq 4 then
      information := true;
   end if;
   if information eq false then
      L1 := [**];
      for x in L do
         f := x[1];
         if f eq ConjPol (f) then
            if Degree (f) eq 1 then
               y := <f, x[2], 0, IdentityMatrix (F, 1)>;
            else
               y := <f, x[2], 2, FormForCompanionMatrix (f, type)>;
            end if;
         else
            y := <f, x[2], 1, IdentityMatrix (F, 2)>;
         end if;
         // the value of y[4] is important only if y[3]=2
         Append (~L1, y);
      end for;
      L := L1;
   end if;
   n := &+[Degree (x[1])*x[2]* (1+x[3] mod 2): x in L];  // dimension

   // AddClasses = matrix in GU(n, q) with determinant w^(q-1)
   if type eq "Sp" then
      sgn := F!-1;
   else
      sgn := F!1;
   end if;
   if type eq "SU" then
      det := 1;
      for x in L do
         if x[3] eq 1 then
            det *:= Determinant (CompanionMatrix (x[1]))^((1-q)*x[2]);
         else
            det *:= Determinant (CompanionMatrix (x[1]))^x[2];
         end if;
      end for;
      if det ne 1 then
         return [**], [**];
      else
         AddClasses := IdentityMatrix (F, n);
         AddClasses[1,1] := pr^-1;
         AddClasses[n,n] := pr^q;
      end if;
   end if;

   if type eq "GO+" or (type eq "SO+" and IsEven (q)) then type := "O+"; end if;
   if type eq "GO-" or (type eq "SO-" and IsEven (q)) then type := "O-"; end if;
   if type eq "GO" then type := "O"; end if;

   quadratic := false;
   if type in {"O+", "O-", "Omega+", "Omega-"} and IsEven (q) then
      quadratic := true;
   end if;

   // need this constant for 1-dimensional symmetric forms
   Stdform1 := SameSSPart select 2 else 1;

   // AddClasses = matrix in GO(n, q) with determinant -1
   special := false;
   if type in {"SO", "SO+", "SO-", "Omega", "Omega+", "Omega-"} then
      special := true;
      if n eq 2 then
         AddClasses := GOElement (2, F: Minus := type in {"SO-", "Omega-"});
      else
         AddClasses := IdentityMatrix (F, n);
         AddClasses[1,1] := 0; AddClasses[n,n] := 0;
         AddClasses[1,n] := 1; AddClasses[n,1] := 1;
      end if;
   end if;
   R := <>;

   Double := false;
   if type in {"O+", "O-", "O", "SO+", "SO-", "SO", "Omega+", "Omega-", "Omega"} then
      ThereIsPlus := false;
      ThereIsMinus := false;
      sign := 1;
      for x in L do
         if x[3] eq 0 then
            if ConstantCoefficient (x[1]) eq 1 then
               ThereIsMinus := true;
               if special and IsOdd (x[2]) then
                  return [**], [**];
               end if;
            else
               ThereIsPlus := true;
            end if;
         elif x[3] eq 2 then
            sign *:= (-1)^x[2];
         end if;
      end for;
      if ThereIsPlus and ThereIsMinus then
         R1 := <>;  
         R1label := <>;         
         // corresponding to the two types of subspaces of t+1 and t-1
         Double := true;
      end if;
   end if;

   // check if the semisimple part is in Omega
   if type in {"Omega", "Omega+", "Omega-"} and IsOdd (q) then
      SN := GF (2)!0;          // spinor norm
      for i in [1..#L] do
         x := L[i];
         if x[3] eq 0 then
            if ConstantCoefficient (x[1]) eq 1 then
               if ThereIsPlus then
                  PosMinus := i;
               else
                  if (sign eq -1 xor type eq "Omega+") xor IsEven (x[2]* (q-1) div 4) then
                     SN +:= 1;
                  end if;
               end if;
            else
               if ThereIsMinus then
                  PosPlus := i;
               end if;
            end if;
         elif x[3] eq 1 and IsOdd (x[2]) then
            C := CompanionMatrix (x[1]);
            if not IsSquare (Determinant (C)) then
               SN +:= 1;
            end if;
         elif x[3] eq 2 and IsOdd (x[2]) then
            C := CompanionMatrix (x[1]);
            if not IsDivisibleBy ((q^(Degree (x[1]) div 2)+1) div 2, Order (C)) then
               SN +:= 1;
            end if;
         end if;
      end for;
      if not Double and SN eq 1 then          
         // in such a case the semisimple part has spinor norm 1
         return [**], [**];
      end if;
      if Double then
         TypeOfMinus := (SN eq 0 xor IsOdd ((q-1)*L[PosMinus][2] div 4)) select "plus" else "minus";
         TypeOfPlus := ((type eq "Omega+" xor sign eq -1) xor TypeOfMinus eq "minus") select "plus" else "minus";
      end if;
   end if;

   is_omega := false;
   if type in {"Omega", "Omega+", "Omega-"} then
      is_omega := true;
      z := IdentityMatrix (F, n);
      if n eq 2 then
         z := SOElement (2, F: Minus := type eq "Omega-");
      else
         if IsOdd (q) then
            z[1,1] := pr;
            z[n,n] := pr^-1;
         else
            z[1,1] := 0; z[n,n] := 0;
            z[n,1] := 1; z[1,n] := 1;
         end if;
      end if;
      AddClassesOmega := z;
   end if;

   // save unipotent classes
   if type in {"O+", "O-", "O", "SO+", "SO-", "SO", "Omega+", "Omega-", "Omega"} then
      UCp := DataArray[1];
      UCpRepr := DataArray[2];
      UCpForm := DataArray[3];
      UCpT := DataArray[4];
      UCpL := DataArray[5];
      UCm := DataArray[6];
      UCmRepr := DataArray[7];
      UCmForm := DataArray[8];
      UCmT := DataArray[9];
      UCmL := DataArray[10];
      if IsOdd (q) and type notin {"SO+", "SO-", "Omega+", "Omega-"} then
         UC := DataArray[11];
         UCRepr := DataArray[12];
         UCForm := DataArray[13];
         UCT := DataArray[14];
         UCL := DataArray[15];
      end if;
   elif type in {"Sp", "SU", "GU"} then
      UC := DataArray[1];
      UCRepr := DataArray[2];
      UCForm := DataArray[3];
      UCT := DataArray[4];
      UCL := DataArray[5];
   end if;

// multiply by a non-square scalar the form corresponding to f = t \pm 1 with even multiplicity
// whenever the discriminant of the global assembled form does not fit the discriminant of the standard Magma form;
// without this passage, the unipotent label computed on the eigenspace(f) would switch classes when f^d has odd multiplicity for 
// at least two odd values of d
   if type in {"O", "SO", "Omega"} then
      DetForm := 1;    // 1 if square, -1 otherwise
      MultToChange := 0;

      for l in L do
         if q mod 4 eq 1 then
            if l[3] eq 2 and IsOdd(l[2]) then DetForm *:= -1; end if;
         else
            if IsOdd(l[2]) and ((l[3] eq 2 and Degree(l[1]) mod 4 eq 0) or (l[3] eq 1 and IsOdd(Degree(l[1])))) then DetForm *:= -1; end if;
         end if;
         if l[3] eq 0 and IsEven(l[2]) then MultToChange := l[2]; end if;
      end for;
// condition for Determinant(StandardSymmetricForm(n,q)) to be a square
      if (((q mod 8 in {1,3} and n mod 4 eq 3) or (q mod 8 in {1,7} and n mod 4 eq 1)) xor DetForm eq -1) xor (q mod 4 eq 3 and MultToChange mod 4 eq 2) then
         for i in [1..#UCmForm] do
            for j in [1..#UCmForm[i]] do
               UCmForm[i][j]*:=pr;
            end for;
         end for;
      else
         for i in [1..#UCpForm] do
            for j in [1..#UCpForm[i]] do
               UCpForm[i][j]*:=pr;
            end for;
         end for;
      end if;
   end if;


   if type eq "Sp" then
      UCL := <{@ <x>: x in l @}: l in UCL>;
   end if;         // add "ns" for consistency with the others

   // CardOfG: cardinality of the group of isometries
   // computed if not passed as parameter
   if Type (CardOfG) eq RngIntElt then
      CardOfG := IsometryGroupCardinality (type, n, q);
   end if;

   // TypeOfMinus := sign of the form correspondent to the el.div. t+1
   // TypeOfPlus := sign of the form correspondent to the el.div. t-1
   // if both t+1 and t-1 are el.div., then SN is the spinor norm of the part of degree gt 1
   // AddClassesOmega = element in SO with SpinorNorm 1 to write classes in SO splitting in Omega

   ConjClasses := [**];
   ConjLabel := [**];

   for x in L do
      f := x[1];
      ind := x[3];
      case ind:
         when 0:
            d := x[2];
            w := -ConstantCoefficient (x[1]);
            if type in {"GU", "SU"} then
	       M := MatrixAlgebra (F, d);
	       ord := Order (w);
               card := CardinalityOfClassicalGroup ("GU", d, q);
               if SameSSPart then
                  Repr := UC[d];
                  T := UCT[d];
                  B := StandardHermitianForm (d, q);
                  Form := [B: j in [1..#Repr]];
                  label := UCL[d];
               else
                  Repr := UCRepr[d];
                  Form := UCForm[d];
                  T := UCT[d];
                  label := UCL[d];
               end if;
               label := {@ LabelHomogenize (l, F, type): l in label @};
               label := {@ <0, f, l> : l in label @};
               if type eq "SU" then
                  S := [<ord*Repr[j][1], <Repr[j][2], card>, w*M!Repr[j][3], Form[j], Gcd (T[j]), label[j]>: 
                      j in [1..#Repr]];
               else
                  S := [<ord*Repr[j][1], <Repr[j][2], card>, w*M!Repr[j][3], Form[j], label[j]>: j in [1..#Repr]];
               end if;
               Append (~R, S);
            elif quadratic then
               if type in {"O+", "Omega+"} xor sign eq -1 then
                  if is_omega and d eq 2 then 
                     label := <0, f, UCpL[1][1]>; //these three 
                     S := [<1, <1, FactoredOrder (OmegaPlus (2, q))>, IdentityMatrix (F, 2), 
                                StandardQuadraticForm (2, q: Variant := "Default"), label>];
                  else
                     if SameSSPart then
                        Repr := UCp[d div 2];
                        StdForm := StandardQuadraticForm (d, q: Variant := "Default");
                        Form := [StdForm: i in [1..#Repr]];
                        label := {@ <0, f, l>: l in UCpL[d div 2] @};
                     else
                        Repr := UCpRepr[d div 2];
                        Form := UCpForm[d div 2];
                        label := {@ <0, f, l>: l in UCpL[d div 2] @};
                     end if;
                     if is_omega then
                        card := CardinalityOfClassicalGroup ("Omega+", d, q);
                     else
                        card := CardinalityOfClassicalGroup ("GO+", d, q);
                     end if;
                     S := [<Repr[j][1], <Repr[j][2], card>, Repr[j][3], Form[j], Repr[j][1], label[j]>: j in [1..#Repr]];
                  end if;
 	       else
                  if is_omega and d eq 2 then
                     label := <0, f, UCmL[1][1]>;
 		     S := [<1, <1, FactoredOrder (OmegaMinus (2, q))>, IdentityMatrix (F, 2), 
                                StandardQuadraticForm (2, q: Minus, Variant := "Default"), label>];
                  else
                     if SameSSPart then
                        Repr := UCm[d div 2];
                        StdForm := StandardQuadraticForm (d, q: Minus, Variant := "Default");
                        Form := [StdForm: i in [1..#Repr]];
                        label := {@ <0, f, l>: l in UCmL[d div 2] @};
                     else
                        Repr := UCmRepr[d div 2];
                        Form := UCmForm[d div 2];
                        label := {@ <0, f, l>: l in UCmL[d div 2] @};
                     end if;
                     if is_omega then
                        card := CardinalityOfClassicalGroup ("Omega-", d, q);
                     else
                        card := CardinalityOfClassicalGroup ("GO-", d, q);
                     end if;
                     S := [<Repr[j][1], <Repr[j][2], card>, Repr[j][3], Form[j], label[j]>: j in [1..#Repr]];
                  end if;
               end if; 
               Append (~R, S);
            elif type in {"Omega+", "Omega-"} then
               if (w eq 1 and ThereIsMinus) or (w eq -1 and ThereIsPlus) then
                  typeofx := w eq 1 select TypeOfPlus else TypeOfMinus;
                  if typeofx eq "plus" then
                     Repr := UCpRepr[d div 2];
                     Form := UCpForm[d div 2];
                     T := UCpT[d div 2];
                     label := {@ <0, f, l[1]>: l in UCpL[d div 2] @};
                     type1 := "orthogonalplus";  IsMinus := false;
		  else
                     Repr := UCmRepr[d div 2];
                     Form := UCmForm[d div 2];
                     T := UCmT[d div 2];
                     label := {@ <0, f, l[1]>: l in UCmL[d div 2] @};
                     type1 := "orthogonalminus"; IsMinus := true;
                  end if;
               else
                  if type eq "Omega+" xor sign eq -1 then
                     Repr := UCpRepr[d div 2];
                     Form := UCpForm[d div 2];
                     T := UCpT[d div 2];
                     label := {@ <0, f, l[1]>: l in UCpL[d div 2] @};
                     type1 := "orthogonalplus";  IsMinus := false;
                  else
                     Repr := UCmRepr[d div 2];
                     Form := UCmForm[d div 2];
                     T := UCmT[d div 2];
                     label := {@ <0, f, l[1]>: l in UCmL[d div 2] @};
                     type1 := "orthogonalminus";  IsMinus := true;
                  end if;
               end if;
               card := CardinalityOfClassicalGroup (type1, d, q);
               if SameSSPart then
                  S := [];
                  StdForm := StandardSymmetricForm (d, q: Minus := IsMinus, Variant := "Default");
                  for j in [1..#Repr] do
                     m := TransformForm (Form[j], type1: Restore := false);
                     if w eq 1 then
                        Append (~S, <Repr[j][1], <Repr[j][2], card>, Repr[j][3], Form[j], 
                                     T[j], m^-1*Repr[j][3]*m, StdForm, label[j]>);
                     else
                        Append (~S, <2*Repr[j][1], <Repr[j][2], card>, -Repr[j][3], Form[j], 
                                     T[j], -m^-1*Repr[j][3]*m, StdForm, label[j]>);
                     end if;
                  end for;
               else
                  if w eq 1 then
                     S := [<Repr[j][1], <Repr[j][2], card>, Repr[j][3], Form[j], 
                            T[j], label[j]>: j in [1..#Repr]];
                  else
                     S := [<2*Repr[j][1], <Repr[j][2], card>, -Repr[j][3], Form[j], 
                            T[j], label[j]>: j in [1..#Repr]];
                  end if;
               end if;
               Append (~R, S);
            elif type in {"O+", "O-", "SO+", "SO-"} then
               if (w eq -1 and ThereIsPlus) or (w eq 1 and ThereIsMinus) then
                  if d eq 1 then
                     is2sq := SameSSPart or q mod 8 in {1, 7} select F!1 else pr;     
                     // 2 is a square in GF(q) iff q mod 8 = 1 or 7
                     if w eq 1 then
                        Sp := [<1, <1, Factorization (2)>, IdentityMatrix (F, 1), 
                                Stdform1*IdentityMatrix (F, 1), [1], <0, f, {* <1, is2sq> *}>>];
                        Sm := [<1, <1, Factorization (2)>, IdentityMatrix (F, 1), 
                                Stdform1*pr*IdentityMatrix (F, 1), [1], <0, f, {* <1, pr/is2sq> *}>>];
                     else
                        Sp := [<2, <1, Factorization (2)>, -IdentityMatrix (F, 1), 
                                Stdform1*IdentityMatrix (F, 1), [1], <0, f, {* <1, is2sq> *}>>];
                        Sm := [<2, <1, Factorization (2)>, -IdentityMatrix (F, 1), 
                                Stdform1*pr*IdentityMatrix (F, 1), [1], <0, f, {* <1, pr/is2sq> *}>>];
                     end if;
                  elif IsEven (d) then
                     if SameSSPart then
                        Repr := UCp[d div 2];
                        T := UCpT[d div 2];
                        StdForm := StandardSymmetricForm (d, q: Variant := "Default");
                        Form := [StdForm: i in [1..#Repr]];
                        label := {@ <0, f, l[1]>: l in UCpL[d div 2] @};
                     else
                        Repr := UCpRepr[d div 2];
                        Form := UCpForm[d div 2];
                        T := UCpT[d div 2];
                        label := {@ <0, f, l[1]>: l in UCpL[d div 2] @};
                     end if;
                     card := CardinalityOfClassicalGroup ("GO+", d, q);
                     if w eq 1 then
                        Sp := [<Repr[j][1], <Repr[j][2], card>, Repr[j][3], Form[j], 
                                T[j], label[j]>: j in [1..#Repr]];
                     else
                        Sp := [<2*Repr[j][1], <Repr[j][2], card>, -Repr[j][3], Form[j], 
                                T[j], label[j]>: j in [1..#Repr]];
                     end if;
                     if SameSSPart then
                        Repr := UCm[d div 2];
                        T := UCmT[d div 2];
                        StdForm := StandardSymmetricForm (d, q: Minus, Variant := "Default");
                        Form := [StdForm: i in [1..#Repr]];
                        label := {@ <0, f, l[1]>: l in UCmL[d div 2] @};
                     else
                        Repr := UCmRepr[d div 2];
                        Form := UCmForm[d div 2];
                        T := UCmT[d div 2];
                        label := {@ <0, f, l[1]>: l in UCmL[d div 2] @};
                     end if;
                     card := CardinalityOfClassicalGroup ("GO-", d, q);
                     if w eq 1 then
                        Sm := [<Repr[j][1], <Repr[j][2], card>, Repr[j][3], Form[j], 
                                T[j], label[j]>: j in [1..#Repr]];
                     else
                        Sm := [<2*Repr[j][1], <Repr[j][2], card>, -Repr[j][3], Form[j], 
                                T[j], label[j]>: j in [1..#Repr]];
                     end if;
	          else
                     if SameSSPart then
                        Repr := UC[d div 2+1];
                        T := UCT[d div 2+1];
                        StdForm := StandardSymmetricForm (d, q: Variant := "Default");
                        Form := [StdForm: i in [1..#Repr]];
                        label := {@ <0, f, l[1]>: l in UCL[d div 2+1] @};
                     else
                        Repr := UCRepr[d div 2+1];
                        Form := UCForm[d div 2+1];
                        T := UCT[d div 2+1];
                        label := {@ <0, f, l[1]>: l in UCL[d div 2+1] @};
                     end if;
                     delta := SameSSPart select 1 else (-1)^(d div 2);
                     DoIt := q mod 4 eq 3 and d mod 4 eq 3;       
                     // equivalent condition to not IsSquare (Determinant (delta*Form[j]))
                     card := CardinalityOfClassicalGroup ("GO", d, q);
                     if w eq 1 then
                        Sp := [<Repr[j][1], <Repr[j][2], card>, Repr[j][3], delta*Form[j], 
                                T[j], ChangeLabel (label[j], F, pr, DoIt)>: j in [1..#Repr]];
                        Sm := [<Repr[j][1], <Repr[j][2], card>, Repr[j][3], delta*pr*Form[j], 
                                T[j], ChangeLabel (label[j], F, pr, not DoIt)>: j in [1..#Repr]];
                     else
                        Sp := [<2*Repr[j][1], <Repr[j][2], card>, -Repr[j][3], delta*Form[j], 
                                T[j], ChangeLabel (label[j], F, pr, DoIt)>: j in [1..#Repr]];
                        Sm := [<2*Repr[j][1], <Repr[j][2], card>, -Repr[j][3], delta*pr*Form[j], 
                                T[j], ChangeLabel (label[j], F, pr, not DoIt)>: j in [1..#Repr]];
                     end if;
                  end if;
                  if w eq 1 or ((type in {"O+", "SO+"} xor sign eq -1) xor (q mod 4 eq 3 and IsOdd (d))) then
                     Append (~R, Sp);
                     Append (~R1, Sm);
                  else
                     Append (~R, Sm);
                     Append (~R1, Sp);
                  end if;
               else
		  if type in {"O+", "SO+"} xor sign eq -1 then
                     if SameSSPart then
                        Repr := UCp[d div 2];
                        T := UCpT[d div 2];
                        StdForm := StandardSymmetricForm (d, q: Variant := "Default");
                        Form := [StdForm: i in [1..#Repr]];
                        label := {@ <0, f, l[1]>: l in UCpL[d div 2] @};
                     else
                        Repr := UCpRepr[d div 2];
                        Form := UCpForm[d div 2];
                        T := UCpT[d div 2];
                        label := {@ <0, f, l[1]>: l in UCpL[d div 2] @};
                     end if;
                     card := CardinalityOfClassicalGroup ("GO+", d, q);
                     if w eq 1 then
                        S := [<Repr[j][1], <Repr[j][2], card>, Repr[j][3], Form[j], 
                               T[j], label[j]>: j in [1..#Repr]];
                     else
                        S := [<2*Repr[j][1], <Repr[j][2], card>, -Repr[j][3], Form[j], 
                               T[j], label[j]>: j in [1..#Repr]];
                     end if;
                     Append (~R, S);
		  else
                     if SameSSPart then
                        Repr := UCm[d div 2];
                        T := UCmT[d div 2];
                        StdForm := StandardSymmetricForm (d, q: Minus, Variant := "Default");
                        Form := [StdForm: i in [1..#Repr]];
                        label := {@ <0, f, l[1]>: l in UCmL[d div 2] @};
                     else
                        Repr := UCmRepr[d div 2];
                        Form := UCmForm[d div 2];
                        T := UCmT[d div 2];
                        label := {@ <0, f, l[1]>: l in UCmL[d div 2] @};
                     end if;
                     card := CardinalityOfClassicalGroup ("GO-", d, q);
                     if w eq 1 then
                        S := [<Repr[j][1], <Repr[j][2], card>, Repr[j][3], Form[j], 
                               T[j], label[j]>: j in [1..#Repr]];
                     else
                        S := [<2*Repr[j][1], <Repr[j][2], card>, -Repr[j][3], Form[j], 
                               T[j], label[j]>: j in [1..#Repr]];
                     end if;
                     Append (~R, S);
                  end if;
               end if;
	    else
	       w := -ConstantCoefficient (f);
               if d eq 1 then
                  lambda := q mod 8 in {1, 7} select F!1 else pr;
                  temp := type in {"SU", "GU"} select 1 else <1, lambda>;
                  S := [<Order (w), <1, Factorization (2)>, w*IdentityMatrix (F, 1), 
                        IdentityMatrix (F, 1), {* 1 *}, <0, f, {* temp *}>>];
               else
	          ord := Order (w);
                  if type eq "Sp" then
                     type1 := "Sp";
                  elif type in {"GU", "SU"} then
                     type1 := "GU";
                  else
                     type1 := "GO";
                  end if;
                  M := MatrixAlgebra (F, d);
                  if type in {"O", "SO", "Omega"} and IsEven (d) then
                     Sp := [];
                     Sm := [];
                     if type eq "Omega" then
                        if TypeOfMinus eq "plus" then
                           Repr := UCpRepr[d div 2];
                           Form := UCpForm[d div 2];
                           T := UCpT[d div 2];
                           label := {@ <0, f, l[1]>: l in UCpL[d div 2] @};
                           card := CardinalityOfClassicalGroup ("GO+", d, q);
                           if SameSSPart then
                              StdForm := StandardSymmetricForm (d, q: Variant:="Default");
                              for j in [1..#Repr] do
                                 m := TransformForm (Form[j], "orthogonalplus": Restore := false);
                                 Append (~Sp, <ord*Repr[j][1], <Repr[j][2], card>, w*M!Repr[j][3], Form[j], 
                                               T[j], w*M! (m^-1*Repr[j][3]*m), StdForm, label[j]>);
                              end for;
                           else
                              Sp := [<ord*Repr[j][1], <Repr[j][2], card>, w*M!Repr[j][3], Form[j], 
                                     T[j], label[j]>: j in [1..#Repr]];
                           end if;
                        else
                           Repr := UCmRepr[d div 2];
                           Form := UCmForm[d div 2];
                           T := UCmT[d div 2];
                           label := {@ <0, f, l[1]>: l in UCmL[d div 2] @};
                           card := CardinalityOfClassicalGroup ("GO-", d, q);
                           if SameSSPart then
                              StdForm := StandardSymmetricForm (d, q: Minus, Variant := "Default");
                              for j in [1..#Repr] do
                                 m := TransformForm (Form[j], "orthogonalminus": Restore := false);
                                 Append (~Sp, <ord*Repr[j][1], <Repr[j][2], card>, w*M!Repr[j][3], Form[j], 
                                               T[j], w*M! (m^-1*Repr[j][3]*m), StdForm, label[j]>);
                              end for;
                           else
                              Sp := [<ord*Repr[j][1], <Repr[j][2], card>, w*M!Repr[j][3], Form[j], 
                                      T[j], label[j]>: j in [1..#Repr]];
                           end if;
                        end if;
		     else
                        if SameSSPart then
                           Repr := UCp[d div 2];
                           T := UCpT[d div 2];
                           label := {@ <0, f, l[1]>: l in UCpL[d div 2] @};
                           StdForm := StandardSymmetricForm (d, q: Variant := "Default");
                           Form := [StdForm: i in [1..#Repr]];
                        else
                           Repr := UCpRepr[d div 2];
                           Form := UCpForm[d div 2];
                           T := UCpT[d div 2];
                           label := {@ <0, f, l[1]>: l in UCpL[d div 2] @};
                        end if;
                        card := CardinalityOfClassicalGroup ("GO+", d, q);
                        Sp := [<ord*Repr[j][1], <Repr[j][2], card>, w*M!Repr[j][3], Form[j], 
                                T[j], label[j]>: j in [1..#Repr]];
                        if SameSSPart then
                           Repr := UCm[d div 2];
                           T := UCmT[d div 2];
                           StdForm := StandardSymmetricForm (d, q: Minus, Variant := "Default");
                           Form := [StdForm: i in [1..#Repr]];
                           label := {@ <0, f, l[1]>: l in UCmL[d div 2] @};
                        else
                           Repr := UCmRepr[d div 2];
                           Form := UCmForm[d div 2];
                           T := UCmT[d div 2];
                           label := {@ <0, f, l[1]>: l in UCmL[d div 2] @};
                        end if;
                        card := CardinalityOfClassicalGroup ("GO-", d, q);
                        Sm := [<ord*Repr[j][1], <Repr[j][2], card>, w*M!Repr[j][3], Form[j], 
                                T[j], label[j]>: j in [1..#Repr]];
                     end if;
                     S := Sp cat Sm;
		  else
                     if SameSSPart then
                        if type eq "Omega" then
                           Repr := UCRepr[d div 2+1];
                           Form := UCForm[d div 2+1];
                           T := UCT[d div 2+1];
                           label := {@ <0, f, l[1]>: l in UCL[d div 2+1] @};
                           S := [];
                           if (q mod 8 in {1,3} and d mod 4 eq 3) or (q mod 8 in {1,7} and d mod 4 eq 1) then
                              coeff := 1;
                           else
                              coeff := pr;
                           end if;
                           // multiplication by coeff needed to have Discriminant(StdForm) = square
                           StdForm := coeff*StandardSymmetricForm (d, q: Variant:="Default");
                           card := CardinalityOfClassicalGroup ("GO", d, q);
                           for j in [1..#Repr] do
                              m := TransformForm (Form[j], "orthogonal": Restore := false);
                              Append (~S, <ord*Repr[j][1], <Repr[j][2], card>, w*M!Repr[j][3], Form[j], 
                                           T[j], w*M! (m^-1*Repr[j][3]*m), StdForm, label[j]>);
                           end for;
                        else
                           if type1 eq "Sp" then
                              Repr := UC[d div 2];
                              T := UCT[d div 2];
                              StdForm := StandardAlternatingForm (d, q);
                              Form := [StdForm: i in [1..#Repr]];
                              label := {@ <0, f, l[1]>: l in UCL[d div 2] @};
                           elif type1 eq "GU" then
                              StdForm := StandardHermitianForm (d, q);
                              Form := [StdForm: i in [1..#Repr]];
                              label := {@ <0, f, l[1]>: l in UCL[d div 2] @};
                           else
                              Repr := UC[d div 2+1];
                              T := UCT[d div 2+1];
                              StdForm := StandardSymmetricForm (d, q: Variant := "Default");
                              Form := [StdForm: i in [1..#Repr]];
                              label := {@ <0, f, l[1]>: l in UCL[d div 2+1] @};
                           end if;
                        end if;
                     else
                        Repr := UCRepr[(d+1) div 2];
                        Form := UCForm[(d+1) div 2];
                        T := UCT[ (d+1) div 2];
                        label := {@ <0, f, l[1]>: l in UCL[ (d+1) div 2] @};
                     end if;
                     if not SameSSPart or type ne "Omega" then
                        card := CardinalityOfClassicalGroup (type1, d, q);
                        S := [<ord*Repr[j][1], <Repr[j][2], card>, w*M!Repr[j][3], Form[j], 
                            T[j], label[j]> : j in [1..#Repr]];
                     end if;
                  end if;
               end if;
               Append (~R, S);
            end if;
         when 1:
            h := Degree (f);
            C := CompanionMatrix (f);
            ord := Order (C);
            d := x[2];          // multiplicity in the semisimple part
            S := [];
            if type eq "Sp" then
               Form := BlockMatrix (2, 2, [0, IdentityMatrix (F, d*h), -IdentityMatrix (F, d*h), 0]);
            elif quadratic then
               Form := BlockMatrix (2, 2, [0, IdentityMatrix (F, d*h), 0, 0]);
            else
               Form := BlockMatrix (2, 2, [0, IdentityMatrix (F, d*h), IdentityMatrix (F, d*h), 0]);
            end if;
            Repr, T := UnipotentClasses ("GL", d, (#F)^h);
            card := CardinalityOfClassicalGroup ("GL", d, (#F)^h);
            for i in [1..#Repr] do
	       Y := BlockMatrix (d, d, [IdentityMatrix (F, h)*Repr[i][3][j1, j2]: j1, j2 in [1..d]]);
               for j in [1..d] do
                  InsertBlock (~Y, C, h*(j-1)+1, h*(j-1)+1);
               end for;
               if type in {"GU", "SU"} then
                  Y := DiagonalJoin (Y, Transpose (FrobeniusImage (Y, e)^-1));
               else
                  Y := DiagonalJoin (Y, Transpose (Y^-1));
               end if;
               ord1 := Repr[i][1]*ord;
               label := <1, f*ConjPol (f), LabelHomogenize (T[i], F, type)>;
               Append (~S, <ord1, <Repr[i][2], card>, Y, Form, Gcd (T[i]), label>);
            end for;
            Append (~R, S);
            if Double then Append (~R1, S); end if;
         when 2:
            h := Degree (f);
            C := CompanionMatrix (f);
            H := GL (h, F);
            d := x[2];
            P := Partitions (d);
            S := [];
            K<w> := ext<F|f: Optimize := false>;
            ord := Order (w);
            if type in {"GU", "SU"} then
               card := CardinalityOfClassicalGroup ("GU", d, q^h);
            else
               card := CardinalityOfClassicalGroup ("GU", d, q^(h div 2));
            end if;
            for P1 in P do
               if SameSSPart then
                  u := DiagonalJoin (<GUUnipotentBlock (j, K): j in P1>);
                  B := DiagonalJoin (<ReverseRows (IdentityMatrix (K, j)): j in P1>);
                  card1 := UnipotentCentralizerOrder ("GU", GU(d, K), u, B: JF := P1);
                  m := TransformForm (B, "unitary": Restore := false);
                  u := m^-1*u*m;
                  Y := BlockMatrix (d, d, [&+[C^(k-1)*Eltseq (u[j1, j2], F)[k]: k in [1..h]]: j1, j2 in [1..d]]);
                  Y *:= DiagonalJoin ([C: i in [1..d]]);
                  Form := ZeroMatrix (F, d*h, d*h);
                  for i in [1..d] do
                     InsertBlock (~Form, x[4], h* (i-1)+1, (d-i)*h+1);
                  end for;
               else
                  Y := DiagonalJoin (<GUUnipotentBlock (j, K): j in P1>);
                  B := DiagonalJoin (<ReverseRows (IdentityMatrix (K, j)): j in P1>);
                  card1 := UnipotentCentralizerOrder ("GU", GU (d, K), Y, B: JF := P1);
                  Y := w*Y;
                  Y := BlockMatrix (d, d, [&+[C^(k-1)*Eltseq (Y[j1, j2], F)[k]: k in [1..h]]: j1, j2 in [1..d]]);
                  Form := ZeroMatrix (F, d*h, d*h);
                  pos := 1;
                  for i in P1 do
                     for j in [1..i] do
                        InsertBlock (~Form, x[4], pos+h* (j-1), pos+h* (i-j));
                     end for;
                     pos +:= i*h;
                  end for;
               end if;
               ord1 := ord*p^Ceiling (Log (p, Maximum (P1))); 
               label := <2, f, LabelHomogenize (P1, F, type)>;
               Append (~S, <ord1, <Integers ()! (card/card1), card>, Y, Form, Gcd (P1), label>);
            end for;
            Append (~R, S);
            if Double then Append (~R1, S); end if;
      end case;
   end for;

   C := CartesianProduct (R);
   for c in C do
      c1 := c;
      Card := CardOfG;
      // elements of c1 are assembled in the representatives, 
      // elements of c: need to check if the class splits into two classes in Omega
      for i in [1..#c1] do
         if #c1[i] eq 8 then
            c1[i][3] := c1[i][6];
            c1[i][4] := c1[i][7];
         end if;
         Card /:= c1[i][2][2];
      end for;
      Repr := DiagonalJoin (<c1[i][3]: i in [1..#L]>);
      Form := DiagonalJoin (<c1[i][4]: i in [1..#L]>);
      XLabel := {* c1[i][#c1[i]]: i in [1..#L] *};
      ord := Lcm ([c1[i][1]: i in [1..#L]]);
      card := &*([c1[i][2][1]: i in [1..#L]]);
      card *:= Integers ()!Card;
      if type eq "Sp" then
         m := TransformForm (Form, "symplectic": Restore := false);
      elif type in {"SU", "GU"} then
         m := TransformForm (Form, "unitary": Restore := false);
      elif type in {"O", "SO", "Omega"} then
         m := TransformForm (Form, "orthogonal": Restore := false);
      elif type in {"O+", "SO+", "Omega+"} then
         m := TransformForm (Form, "orthogonalplus": Restore := false);
      else
         m := TransformForm (Form, "orthogonalminus": Restore := false);
      end if;
      if type eq "SU" then
         GCD := Gcd ([c[i][5]: i in [1..#L]]);
         GCD := Gcd (GCD, q+1);
         card div:= GCD;
         Repr := m^-1*Repr*m;
         // modify AddClasses: we want AddClass in the centralizer 
         // of the semisimple part to maintain the same semisimple part
         if SameSSPart then
            s := AddClass (type, L, c1, m, F, Nrows (Repr));
         else
            s := AddClasses;
         end if;
         for i in [0..GCD-1] do
            Append (~ConjClasses, <ord, card, s^-i*Repr*s^i>);
            Append (~ConjLabel, <XLabel, i>);
         end for;
      elif type in {"Omega+", "Omega-"} and IsEven (q) then
         if {ThereIsPlus, ThereIsMinus} eq {false} then
            Append (~ConjClasses, <ord, card, AddClassesOmega^-1*m^-1*Repr*m*AddClassesOmega>);
            Append (~ConjLabel, <XLabel, "t">);
            Append (~ConjLabel, <XLabel, "id">);
         else
            Append (~ConjLabel, <XLabel, "ns">);
         end if;
         Append (~ConjClasses, <ord, card, m^-1*Repr*m>);
      elif special and type ne "SO" then
         if type eq "Omega" then
            SplitClassesSO := false;
         else
            SplitClassesSO := true;
            for i in [1..#L] do
               if L[i][3] eq 0 then
                  if false in {IsEven (y): y in c[i][5]} then
                     SplitClassesSO := false;
                     break i;
                  end if;
               end if;
            end for;
         end if;
         s := AddClasses;
         SplitClassesOmega := false;
         if type in {"Omega+", "Omega", "Omega-"} then
            SplitClassesOmega := CheckSplitOmega (c, F, L);
            // modify AddClasses: we want AddClass in the centralizer 
            // of the semisimple part to maintain the same ss part
            if SameSSPart then
	       z := AddClass (type, L, c1, m, F, Nrows (Repr): IsOmega);
            else
               z := AddClassesOmega;
            end if;
         end if;
         if SplitClassesSO then
            // modify AddClasses: we want AddClass in the centralizer 
            // of the semisimple part to maintain the same ss part
            card div:= 2;
            if SameSSPart then
	       s := AddClass (type, L, c1, m, F, Nrows (Repr));
            end if;
            if SplitClassesOmega then
               card div:= 2;
               Append (~ConjClasses, <ord, card, z^-1*m^-1*Repr*m*z>);
               Append (~ConjClasses, <ord, card, s^-1*z^-1*m^-1*Repr*m*z*s>);
               Append (~ConjLabel, <XLabel, "t">);
               Append (~ConjLabel, <XLabel, "ts">);
            end if;
            Append (~ConjClasses, <ord, card, m^-1*Repr*m>);
            Append (~ConjClasses, <ord, card, s^-1*m^-1*Repr*m*s>);
            Append (~ConjLabel, <XLabel, "id">);
            Append (~ConjLabel, <XLabel, "s">);
	 else
            if SplitClassesOmega then
               card div:= 2;
               Append (~ConjClasses, <ord, card, z^-1*m^-1*Repr*m*z>);
               Append (~ConjLabel, <XLabel, "t">);
               Append (~ConjLabel, <XLabel, "id">);
            else
               Append (~ConjLabel, <XLabel, "ns">);
            end if;
	    Append (~ConjClasses, <ord, card, m^-1*Repr*m>);
         end if;
      else
         Append (~ConjClasses, <ord, card, m^-1*Repr*m>);
         if special then XLabel := <XLabel, "ns">; end if;
         Append (~ConjLabel, XLabel);
      end if;
   end for;

   if Double and type in {"O+", "O-", "SO+", "SO-"} then
      C := CartesianProduct (R1);
      for c in C do
	 Card := CardOfG;
         for i in [1..#L] do Card /:= c[i][2][2]; end for;
         Repr := DiagonalJoin (<c[i][3]: i in [1..#L]>);
         Form := DiagonalJoin (<c[i][4]: i in [1..#L]>);
         XLabel := {* c[i][#c[i]]: i in [1..#L] *};
         ord := Lcm ([c[i][1]: i in [1..#L]]);
         card := &*([c[i][2][1]: i in [1..#L]]);
         card *:= Integers ()!Card;
         if type in {"O+", "SO+"} then
            m := TransformForm (Form, "orthogonalplus": Restore := false);
         else
            m := TransformForm (Form, "orthogonalminus": Restore := false);
         end if;
         Append (~ConjClasses, <ord, card, m^-1*Repr*m>);
         if special then XLabel := <XLabel, "ns">; end if;
         Append (~ConjLabel, XLabel);
      end for;
   end if;

   ConjClasses := [<c[1], c[2], GL (n, F)!c[3]>: c in ConjClasses];
   return ConjClasses, ConjLabel;
end function;

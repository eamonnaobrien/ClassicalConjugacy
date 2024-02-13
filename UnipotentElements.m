freeze;

import "semisimple/form.m": DetermineForm, ConjugatePolynomial;
import "fixed-ss.m": AllUnipotentElementsOfS;
import "Gen-Classes.m": UCComputation;
import "size.m": GroupType, MyIsIn;

intrinsic ClassesForFixedSemisimple (G:: GrpMat, x:: GrpMatElt) -> [], {@ @}
{Given a semisimple element x of classical group G which preserves a form, 
 return representatives and labels of conjugacy classes in G with semisimple part x}

   require IsSemisimple (x): "Input element is not semisimple"; 
   require Generic (Parent (x)) cmpeq Generic (G): "Input element is not in group"; 
   // require x in G: "Element not in group";
   require MyIsIn (G, x): "Input element is not in group";

   if IsTrivial (G) then return [<1, 1, G.0>], _; end if;

   F := BaseRing (G);

   if IsAbelian (G) and Degree (G) eq 2 and #F in {2, 3} and #G eq 2 then 
      if #F eq 3 then return [<1, 1, x>], _;  
      else C := Classes (G); C := [C[i]: i in [1..#C]]; return C, _;
      end if;
   end if;

   flag, gp_type := GroupType (G);
   if flag and gp_type in {"GL", "SL"} then
      error "Input group is one of GL or SL";
   end if;
   ValidTypes := {"Sp", "SU", "GU", "Omega+", "Omega-", "Omega",
                  "SO+", "SO-", "SO", "GO+", "GO-", "GO"};
   require flag and gp_type in ValidTypes: "Type must be one of ", ValidTypes;

   n := Degree (G); F := BaseRing (G);
   if IsOdd (n) and IsEven (#F) and gp_type eq "GO" then
      error "Function does not apply to this case";
   end if;

   // data for unipotent classes is computed just once 
   // and passed as argument to AllUnipotentElementsOfS
   B, type, sgn, special, IsOmega, Q := DetermineForm (G, x);

   e := type eq "unitary" select Degree (F) div 2 else 0;
   p := Characteristic (F);
   q := type eq "unitary" select p^e else #F;

   //conjugate transpose matrix
   Star := func<M: exp := e| Transpose (FrobeniusImage (M, exp))>;
   //conjugate polynomial
   ConjPol := ConjugatePolynomial (type eq "unitary");

   _, _, c := JordanForm (x);
   L1 := [<c[1][1], c[1][2]>];
   for i in [2..#c] do
      ThereIsNot := true;
      f := c[i][1];
      fd := ConjPol (f);
      for j in [1..#L1] do
         if L1[j][1] eq f then
            ThereIsNot := false;
            L1[j][2] +:= c[i][2];
            break j;
         elif L1[j][1] eq fd then
            ThereIsNot := false;
         end if;
      end for;
      if ThereIsNot then
         Append (~L1, <c[i][1], c[i][2]>);
      end if;
   end for;

   MaxMult := 0;  // max multiplicity of elementary divisors f=f*, deg (f)=1
   for c in L1 do
      f := c[1];
      if Degree (f) eq 1 and f eq ConjPol (f) then
         MaxMult := Max (MaxMult, c[2]);
      end if;
   end for;

   case type:
      when "unitary":
         type1 := "GU";
         if special then type1 := "SU"; end if;
         UC, UCRepr, UCForm, UCT, UCL := UCComputation ("GU", MaxMult, q);
         DataArray := <UC, UCRepr, UCForm, UCT, UCL>;

      when "symplectic":
         type1 := "Sp";
         UC, UCRepr, UCForm, UCT, UCL := UCComputation ("Sp", MaxMult, q);
         DataArray := <UC, UCRepr, UCForm, UCT, UCL>;

      when "orthogonalplus":
         type1 := "GO+";
         if special then type1 := "SO+"; end if;
         if IsOmega then type1 := "Omega+"; end if;
         if IsOmega and IsEven (p) then
            UCp, UCpRepr, UCpForm, UCpT, UCpL := UCComputation ("Omega+", MaxMult, q);
            UCm, UCmRepr, UCmForm, UCmT, UCmL := UCComputation ("Omega-", MaxMult, q);
         else
            UCp, UCpRepr, UCpForm, UCpT, UCpL := UCComputation ("O+", MaxMult, q);
            UCm, UCmRepr, UCmForm, UCmT, UCmL := UCComputation ("O-", MaxMult, q);
         end if;
         if not special and IsOdd (p) then
            UC, UCRepr, UCForm, UCT, UCL := UCComputation ("O", MaxMult, q);
            DataArray := <UCp, UCpRepr, UCpForm, UCpT, UCpL, UCm, UCmRepr, UCmForm, UCmT, UCmL, 
                          UC, UCRepr, UCForm, UCT, UCL>;
         else
            DataArray := <UCp, UCpRepr, UCpForm, UCpT, UCpL, UCm, UCmRepr, UCmForm, UCmT, UCmL>;
         end if;

      when "orthogonalminus":
         type1 := "GO-";
         if special then type1 := "SO-"; end if;
         if IsOmega then type1 := "Omega-"; end if;
         if IsOmega and IsEven (p) then
            UCp, UCpRepr, UCpForm, UCpT, UCpL := UCComputation ("Omega+", MaxMult, q);
            UCm, UCmRepr, UCmForm, UCmT, UCmL := UCComputation ("Omega-", MaxMult, q);
         else
            UCp, UCpRepr, UCpForm, UCpT, UCpL := UCComputation ("O+", MaxMult, q);
            UCm, UCmRepr, UCmForm, UCmT, UCmL := UCComputation ("O-", MaxMult, q);
         end if;
         if not special and IsOdd (p) then
            UC, UCRepr, UCForm, UCT, UCL := UCComputation ("O", MaxMult, q);
            DataArray := <UCp, UCpRepr, UCpForm, UCpT, UCpL, UCm, UCmRepr, 
                          UCmForm, UCmT, UCmL, UC, UCRepr, UCForm, UCT, UCL>;
         else
            DataArray := <UCp, UCpRepr, UCpForm, UCpT, UCpL, UCm, UCmRepr, UCmForm, UCmT, UCmL>;
         end if;

      when "orthogonal", "orthogonalcircle":
         type1 := "GO";
         if special then type1 := "SO"; end if;
         if IsOmega then type1 := "Omega"; end if;
         UCp, UCpRepr, UCpForm, UCpT, UCpL := UCComputation ("O+", MaxMult, q);
         UCm, UCmRepr, UCmForm, UCmT, UCmL := UCComputation ("O-", MaxMult, q);
         UC, UCRepr, UCForm, UCT, UCL := UCComputation ("O", MaxMult, q);
         DataArray := <UCp, UCpRepr, UCpForm, UCpT, UCpL, UCm, UCmRepr, 
                       UCmForm, UCmT, UCmL, UC, UCRepr, UCForm, UCT, UCL>;
   end case;
   
   X, X_labels := AllUnipotentElementsOfS (type1, L1: SameSSPart, DataArray := DataArray);

   // orthogonal in characteristic 2?
   if assigned Q and p eq 2 then 
      m := TransformForm (Q, type: Restore := false);
   else
      m := TransformForm (B, type: Restore := false);
   end if;
  
   for i in [1..#X] do
      y := X[i][3];
      if IsSemisimple (y) then
         flag, z := InternalSemisimpleIsConjugate (G, x, m*y*m^-1);
         if flag then
            break i;
         end if;
      end if;
   end for;
   if type in {"unitary", "symplectic"} then
      Y := [<a[1], a[2], GL (n, F)! (z*m*a[3]*m^-1*z^-1)>: a in X];
   else
      // in the orthogonal case AllUnipotentElementsOfS returns both 
      // semisimple classes in GO, so we need to pick only one of them
      Y := [];
      for a in X do
         y := z*m*a[3]*m^-1*z^-1;
         s := MultiplicativeJordanDecomposition (y);
         if s eq x then // s = semisimple part of y
	    Append (~Y, <a[1], a[2], y>);
         end if;
      end for;
   end if;

   return Y, {@ l: l in X_labels @};
end intrinsic;

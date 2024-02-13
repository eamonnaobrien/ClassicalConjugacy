freeze;

import "even/Omega-even-general.m": OrthogonalEvenDecideConjugacy;
import "even/Sp-even-general.m": SpEvenDecideConjugacy;
import "odd/GU-general.m": SUDecideConjugacy, GUDecideConjugacy;
import "odd/Sp-odd-general.m": SpDecideConjugacy;
import "odd/Orthogonal-odd-general.m": OrthogonalDecideConjugacy; 
import "../util.m": MySpinorNorm, FixesQuadraticForm;
import "../central/sl.m": SLUnipotentCentraliser;
import "../central/su.m": MyUnitary_UnipotentCentraliser;
import "../central/odd-sp.m":  SpUnipotentCentraliser_Odd;
import "../central/even-sp.m": SpUnipotentCentraliser_Even;
import "../central/odd-orthogonal.m":  MyOrthogonalCentraliser_Odd;
import "../central/even-orthogonal.m": MyOrthogonalCentraliser_Even;
import "../../size.m": GroupType;

// centraliser in G of g 

MyUnipotentCentraliser := function (G, g: Limit := 10, type := false)
   if IsCentral (G, g) then return true, G; end if;

   F := BaseRing (G); 
   if Degree (G) eq 2 and #F in {2, 4} then return false, _; end if;

   if type cmpeq false then 
      flag, type := GroupType (G); 
      if not flag then error "Input group is probably not classical"; end if;
   end if;

   omega := type in {"Omega+", "Omega-", "Omega"};
   special := type in {"SO+", "SO-", "SO"};
   orthogonal := type in {"GO+", "GO-", "GO"};

   F := BaseRing (G);
   if (omega or special or orthogonal) then 
      if IsEven (#F) then 
         flag, form, form_type := QuadraticForm (G);
         V := QuadraticSpace (form);
         apply := DicksonInvariant (V, g) eq 0; 
         if not apply then 
            vprint Classes: "Element must be in Omega -- must do brute force computation "; 
            return false, _; 
         end if;
         str := form_type eq "orthogonalplus" select "orth+" else "orth-";
         V := QuadraticSpace (form);
      else 
         flag, str, form := OrthogonalForm (G);
      end if;

   elif type in {"GU", "SU"} then  
      flag, form := UnitaryForm (G);
      str := "unitary";

   elif type eq "Sp" then 
      flag, form := SymplecticForm (G);
      str := "symplectic";
   end if;

   if type in {"GL", "SL"} then 
      return true, SLUnipotentCentraliser (G, g); 

   elif type in {"GU", "SU"} then 
      C, r, f := MyUnitary_UnipotentCentraliser (G, g);
      _, sigma := StandardHermitianForm (Degree (G), Isqrt (#F));
      V := UnitarySpace (f, sigma);
      I := IsometryGroup (V);
      fct := GUDecideConjugacy;

   elif type eq "Sp" then 
      if IsEven (#F) then 
         C, r, f := SpUnipotentCentraliser_Even (G, g, form);
         I := IsometryGroup (f);
         fct := SpEvenDecideConjugacy;
      else
         C, r, f := SpUnipotentCentraliser_Odd (G, g, form);
         I := IsometryGroup (f);
         fct := SpDecideConjugacy;
      end if;

   elif (omega or special or orthogonal) then 
      if IsEven (#F) then  
         C, r, f := MyOrthogonalCentraliser_Even (G, g, form, type);
         assert FixesQuadraticForm (r, f);
         V := QuadraticSpace (f);
         I := IsometryGroup (V);
         fct := OrthogonalEvenDecideConjugacy;
      else 
         C, r, f := MyOrthogonalCentraliser_Odd (G, g, form);
         I := IsometryGroup (f);
         fct := OrthogonalDecideConjugacy;
      end if;
   else
      error "Type of group incorrect in MyUnipotentCentraliser";
   end if;

   assert IsCentral (C, r);
   
   tr_I := TransformForm (f, str);
   tr_G := TransformForm (form, str);

   CB := tr_G * tr_I^-1;
   s := g^CB;

   flag, c := fct (I, r, s);
   assert flag;
   D := C^c;
   E := D^(CB^-1);

   assert assigned C`FactoredOrder;
   E`FactoredOrder := C`FactoredOrder;
   E`Order := C`Order;
   assert IsCentral (E, g);
   return true, E;
end function;

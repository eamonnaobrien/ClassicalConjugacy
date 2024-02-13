freeze;

import "../central/sl.m": GLParameters, SLParameters;
import "odd/GU-general.m": SUParameters, GUParameters;
import "../central/odd-orthogonal.m":GLOLabel_OrthogonalOdd;
import "odd/SO-Omega-conjugacy.m": GLOLabel_SOOdd, GLOLabel_OmegaOdd; 
import "../central/odd-sp.m": GLOLabel_SpOdd;
import "even/even-label.m": SpO_EvenLabel;

import "../../linear/SL-IsConjugate.m": GLIsConjugate, SLIsConjugate; 
import "odd/GU-general.m": SUDecideConjugacy, GUDecideConjugacy;
import "odd/Orthogonal-odd-general.m": OrthogonalDecideConjugacy; 
import "odd/SO-Omega-conjugacy.m": SODecideConjugacy, OmegaDecideConjugacy;
import "odd/Sp-odd-general.m": SpDecideConjugacy;
import "even/Sp-even-general.m": SpEvenDecideConjugacy;
import "even/Omega-even-general.m": OrthogonalEvenDecideConjugacy;
import "../../size.m": GroupType;

// label for g in G -- 
// for SU in all char the SU parameter may not be correct but point
// instead to another SU rep
// for SO / Omega in odd char, the relevant part may not be correct
// nor unique, and point instead to another rep in SO / Omega
// in both cases the "wrong" rep is GU/GO conjugate to the correct rep 
//
// if IsometryLabel is true, then, for odd characteristic unitary and 
// orthogonal groups, we only compute the label for g in the relevant 
// isometry group, not G; this is much cheaper, also the label does 
// not identify the class in G precisely

MyUnipotentClassLabel := function (G, g: Limit := 10, type := false, IsometryLabel := false)

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
         flag, form := QuadraticForm (G);
         label, add := SpO_EvenLabel (g, form: Orthogonal := true, 
                        Omega := type in {"Omega+", "Omega-"});
         label := <label, add>;
      else
         flag, _, form := OrthogonalForm (G);
         if orthogonal or ((special or omega) and IsometryLabel) then
            label := GLOLabel_OrthogonalOdd (g, form);
         else 
            if special then label := GLOLabel_SOOdd (G, g, form);
            elif omega then label := GLOLabel_OmegaOdd (G, g, form); end if;
         end if;
      end if;

   elif (type eq "GU") or (type eq "SU" and IsometryLabel) then 
      label := GUParameters (g);

   elif type eq "SU" then  
      label := SUParameters (G, g); 

   elif type eq "Sp" then 
      flag, form := SymplecticForm (G);
      if IsEven (#F) then
         label := SpO_EvenLabel (g, form);
      else
         label := GLOLabel_SpOdd (g, form);    
      end if;

   elif type eq "SL" then 
      label := SLParameters (G, g);

   elif type eq "GL" then 
      label := GLParameters (g);
   end if;

   return label, type, omega, special, orthogonal;
end function;

// if g and h are conjugate in G then return 
// true and conjugating element, else false

MyUnipotentIsConjugate := function (G, g, h) 
   if g eq h then return true, g^0; end if;
   if Order (g) ne Order (h) then return false, _; end if;
   if IsAbelian (G) and g ne h then return false, _; end if;

   label_g, type, omega, special, orthogonal := 
      MyUnipotentClassLabel (G, g: IsometryLabel := true);
   label_h := MyUnipotentClassLabel (G, h: IsometryLabel := true);

   if label_g ne label_h then return false, _; end if;

   F := BaseRing (G);
   q := #F;

   if type eq "GU" then 
      f, c := GUDecideConjugacy (G, g, h); 

   elif type eq "SU" then 
      f, c := SUDecideConjugacy (G, g, h); 

   elif omega or special or orthogonal then 
      if IsOdd (q) then 
         if orthogonal then 
            f, c := OrthogonalDecideConjugacy (G, g, h);
         elif special then 
            f, c := SODecideConjugacy (G, g, h);
         elif omega then 
            f, c := OmegaDecideConjugacy (G, g, h);
         end if;
      else 
         f, c := OrthogonalEvenDecideConjugacy (G, g, h: InOmega := omega);
      end if;

   elif type eq "Sp" then 
      if IsOdd (q) then 
         f, c := SpDecideConjugacy (G, g, h);
      else 
         f, c := SpEvenDecideConjugacy (G, g, h);
      end if;

   elif type eq "SL" then 
      f, c := SLIsConjugate (G, g, h);

   elif type eq "GL" then 
      f, c := GLIsConjugate (G, g, h);

   else
      error "Type incorrect in MyUnipotentIsConjugate";
   end if;
   if f then return true, c; else return false, _; end if;
end function;

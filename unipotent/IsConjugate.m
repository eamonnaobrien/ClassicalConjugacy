freeze;

import "conjugation/is-conjugate.m": MyUnipotentIsConjugate;

intrinsic InternalUnipotentIsConjugate (G:: GrpMat, x:: GrpMatElt, y:: GrpMatElt) -> GrpMatElt 
{if unipotent elements x and y are conjugate in classical group G, 
 then return true and conjugating element, else false}

   require Generic (G) cmpeq Generic (Parent (x)): "Element is not in group";
   require Generic (G) cmpeq Generic (Parent (y)): "Element is not in group";
   require IsUnipotent (x) and IsUnipotent (y): "Elements must be unipotent";

   if x eq y then return true, G.0; end if;
   if Order (x) ne Order (y) then return false, _; end if;

   F := BaseRing (G);
   if not IsStandardGF (F) then 
      H := Embed (G);
      if assigned G`ClassicalType then H`ClassicalType := G`ClassicalType; end if;
      K := BaseRing (H);
      a := Embed (x, K);
      b := Embed (y, K);
      flag, z := MyUnipotentIsConjugate (H, a, b);
      if flag then z := Embed (z, F); end if;
   else
      flag, z := MyUnipotentIsConjugate (G, x, y);
   end if;

   if flag then 
      return flag, z;
   else
      return flag, _; 
   end if;
end intrinsic;

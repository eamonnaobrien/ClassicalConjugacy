freeze;

import "conjugation/centraliser.m": MyUnipotentCentraliser;

intrinsic InternalUnipotentCentralizer (G:: GrpMat, x:: GrpMatElt) -> GrpMat 
{Centraliser of unipotent element in classical group}

   require Generic (G) cmpeq Generic (Parent (x)): "Element is not in group";
   require IsUnipotent (x): "Element must be unipotent";

   if IsCentral (G, x) then return G; end if;

   d := Nrows (x); F := BaseRing (x);
   // "\n In InternalUnipotentCentralizer", Degree (G), Order (x);
   x := GL(d, F) ! x;
   if Degree (G) eq 1 then 
      O := Lcm ([Order (G.i): i in [1..Ngens (G)]]);
      fac := Factorisation (O);
      G`FactoredOrder := fac;
      G`Order := O;
      return G;
   else 
      if not IsStandardGF (F) then
         H, phi := Embed (G);
         if assigned G`ClassicalType then H`ClassicalType := G`ClassicalType; end if;
         K := BaseRing (H);
         y := Embed (x, K);
         flag, CH := MyUnipotentCentraliser (H, Generic (H)!y);
         if flag then 
             C := Embed (CH, F); 
             C`FactoredOrder := CH`FactoredOrder; C`Order := CH`Order; 
         end if;
      else
         flag, C := MyUnipotentCentraliser (G, Generic (G)!x);
      end if;
      if flag then return C; end if;
      C := LMGCentralizer (G, Generic(G)!x); 
      f := LMGFactoredOrder (C);
      return C;
   end if;
end intrinsic;

intrinsic InternalUnipotentCentraliser (G:: GrpMat, x:: GrpMatElt) -> GrpMat 
{"} // "
   return InternalUnipotentCentralizer (G, x);
end intrinsic;

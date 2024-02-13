freeze;

import "Omega_Char2.m": OmegaClasses_Char2;
import "OmegaClasses.m": OmegaClasses;
import "SOClasses.m": SOClasses;
import "GOClasses.m": GOClasses;
import "GO_Char2.m": GOClasses_Char2;
import "OmegapmClasses.m":OmegapmClasses;
import "SOpmClasses.m":SOpmClasses;
import "GOpmClasses.m":GOpmClasses;

// returns the list of semisimple conjugacy classes of G, 
// where G is any orthogonal group in the standard magma copy 
// (except odd dimension and even characteristic, that produces an error message). 
// The type of the orthogonal group (whether "orthogonalplus" or "orthogonalminus", 
// special or not, Omega or not) is decided by the parameters.

SSClassesO:=function(n,F: Minus:=false, Special:=false, Omega:=false)

   if Type(F) eq RngIntElt then
      F:=GF(F);
   end if;
   p:=Characteristic(F);
   type:="plus";
   if Minus then
      type:="minus";
   end if;
   if IsOdd(n) then
      if p eq 2 then
         error "Case odd dimension and even characteristic not supported";
      end if;
      if Omega then
         return OmegaClasses(n,F);
      elif Special then
         return SOClasses(n,F);
      else
         return GOClasses(n,F);
      end if;
   else
      if p eq 2 then
         if Omega then
            return OmegaClasses_Char2(n,F,type);
         else
            return GOClasses_Char2(n,F,type);
         end if;
      else
         if Omega then
            return OmegapmClasses(n,F,type);
         elif Special then
            return SOpmClasses(n,F,type);
         else
            return GOpmClasses(n,F,type);
         end if;
      end if;
   end if;
end function;

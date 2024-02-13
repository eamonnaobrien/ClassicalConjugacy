freeze;

import "Unitary/SUClasses.m": SSClassesSU;
import "Unitary/GUClasses.m": SSClassesGU;
import "Symplectic/SpClasses.m": SSClassesSp;
import "Orthogonal/OClasses.m": SSClassesO;

intrinsic SemisimpleClasses (type:: MonStgElt, n:: RngIntElt, q:: RngIntElt) -> []
{Semisimple conjugacy classes of the classical group of supplied type, rank and field size}

   ValidTypes := ["Sp", "SU", "GU", "Omega+", "Omega-", "Omega",
                  "SO+", "SO-", "SO", "GO+", "GO-", "GO", "O+", "O-", "O"];
   require type in ValidTypes: "Type must be one of ", ValidTypes;
   require n gt 0: "Degree must be positive";
   require IsPrimePower (q): "Invalid field size";

   if type in {"O", "SO", "Omega"} then
      require IsOdd (n): "Degree must be odd";
   elif type in { "GO+", "O+", "SO+", "Omega+", 
                  "GO-", "O-", "SO-", "Omega-", "Sp"} then 
      require IsEven (n): "Degree must be even";
   end if;
 
   if type in {"GU", "SU"} then
      F := GF(q^2);
      if type eq "SU" then
         return SSClassesSU (n, F);
      else
         return SSClassesGU (n, F);
      end if;
   end if;

   F := GF(q);

   if type eq "Sp" then
      return SSClassesSp (n, F);
   end if;

   if IsOdd (q) then
      if type eq "GO+" or type eq "O+" then
         return SSClassesO (n, F);
      end if;
      if type eq "GO-" or type eq "O-" then
         return SSClassesO (n, F: Minus);
      end if;
      if type eq "GO" or type eq "O" then
         return SSClassesO (n, F);
      end if;

      if type eq "SO+" then
         return SSClassesO (n, F: Special);
      end if;
      if type eq "SO-" then
         return SSClassesO (n, F: Minus, Special);
      end if;
      if type eq "SO" then
         return SSClassesO (n, F: Special);
      end if;

      if type eq "Omega+" then
         return SSClassesO (n, F: Omega);
      end if;
      if type eq "Omega-" then
         return SSClassesO (n, F: Minus, Omega);
      end if;
      if type eq "Omega" then
         return SSClassesO (n, F: Omega);
      end if;
   else
      require IsEven (n) and IsEven (q): "Odd degree and even characteristic case not considered";
      if type in {"GO+", "O+", "SO+"} then
         return SSClassesO (n, F);
      end if;
      if type in {"GO-", "O-", "SO-"} then
         return SSClassesO (n, F: Minus);
      end if;
      if type eq "Omega+" then
         return SSClassesO (n, F: Omega);
      end if;
      if type eq "Omega-" then
         return SSClassesO (n, F: Minus, Omega);
      end if;
   end if;
end intrinsic;

intrinsic SemisimpleClasses (type:: MonStgElt, n:: RngIntElt, F:: FldFin) -> []
{Semisimple conjugacy classes of the classical group of supplied type, rank and field}
   return SemisimpleClasses (type, n, #F);
end intrinsic;

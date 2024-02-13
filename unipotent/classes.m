freeze;

import "good-char.m": SLUnipotentReps, GLUnipotentReps, 
   SUUnipotentReps, GUUnipotentReps, SpUnipotentReps;
import "odd-char.m": OrthogonalUnipotentReps;
import "even-char.m": EvenUnipotentReps; 
 
intrinsic UnipotentClasses (type:: MonStgElt, d:: RngIntElt, q:: RngIntElt:
   Rewrite := true) -> [], [], [], [], []
{Unipotent conjugacy classes of the classical group of supplied type and rank
defined over field of given size}

   ValidTypes := ["SL", "GL", "Sp", "SU", "GU", "Omega+", "Omega-", "Omega",
                  "SO+", "SO-", "SO", "GO+", "GO-", "GO", "O+", "O-", "O"];
   require type in ValidTypes: "Type must be one of ", ValidTypes;
   require d gt 0: "Degree must be positive";
   require IsPrimePower (q): "Invalid field size";

   if type eq "GO+" or (type eq "SO+" and IsEven (q)) then type := "O+"; end if;
   if type eq "GO-" or (type eq "SO-" and IsEven (q)) then type := "O-"; end if;
   if type eq "GO" then type := "O"; end if;

   if type in {"O", "SO", "Omega"} then
      require IsOdd (d): "Degree must be odd"; 
      if IsEven (q) then 
         error "Case not considered";
      end if;
   end if;

   if type in {"Omega+", "SO+", "O+"} then 
      epsilon := 1; 
      require IsEven (d): "Degree must be even"; 
   end if;
   if type in {"Omega-", "SO-", "O-"} then 
      require IsEven (d): "Degree must be even"; 
      epsilon := -1; 
   end if;
   if type in {"Omega", "SO", "O"} then 
      require IsOdd (d): "Degree must be odd"; 
      epsilon := 0; 
   end if;
   
   if type eq "SL" then
      R, T := SLUnipotentReps (d, q);
   elif type eq "GL" then
      R, T := GLUnipotentReps (d, q);
   elif type eq "SU" then 
      R, reps, forms, T := SUUnipotentReps (d, q: Rewrite := Rewrite);
   elif type eq "GU" then 
      R, reps, forms, T := GUUnipotentReps (d, q: Rewrite := Rewrite);
   elif type eq "Sp" then 
      require IsEven (d): "Degree must be even"; 
      if IsEven (q) then 
         R, reps, forms, T := EvenUnipotentReps (type, d, q: Rewrite := Rewrite);
      else 
         R, reps, forms, T, L := SpUnipotentReps (d, q: Rewrite := Rewrite); 
      end if;
   elif type in {"Omega+", "Omega", "Omega-"} then 
      if IsOdd (q) then 
         R, reps, forms, T, L := OrthogonalUnipotentReps (d, q, epsilon: Special := true, Perfect := true, Rewrite := Rewrite);
      else
         R, reps, forms, T := EvenUnipotentReps (type, d, q: Rewrite := Rewrite);
      end if;
   elif type in {"SO+", "SO-", "SO"} then 
      if IsOdd (q) then 
         R, reps, forms, T, L := OrthogonalUnipotentReps (d, q, epsilon: Special := true, Perfect := false, Rewrite := Rewrite);
      else
         R, reps, forms, T := EvenUnipotentReps (type, d, q: Rewrite := Rewrite);
      end if;
   elif type in {"O+", "O-", "O"} then 
      if IsOdd (q) then 
         R, reps, forms, T, L := OrthogonalUnipotentReps (d, q, epsilon: Special := false, Perfect := false, Rewrite := Rewrite);
         // code for writing down all classes in fixed-ss.m assumes this! 
         if type in {"O"} then
            assert forall{f: f in forms | IsSquare (Determinant (f))};
         end if;
      else
         R, reps, forms, T := EvenUnipotentReps (type, d, q: Rewrite := Rewrite);
      end if;
   end if;

   if type in {"GL", "SL"} then 
      return R, T, _, _,  _;
   elif type in {"Sp", "O+", "O-", "O", "SO+", "SO-", "SO", 
                  "Omega+", "Omega", "Omega-"} and IsOdd (q) then 
      return R, L, T, reps, forms;
   else 
      return R, T, T, reps, forms;
   end if;
end intrinsic;

intrinsic UnipotentClasses (type:: MonStgElt, d:: RngIntElt, F:: FldFin:
   Rewrite := true) -> [], [], [], [], []
{Unipotent conjugacy classes of the classical group of supplied type and rank defined
over given field}

   return UnipotentClasses (type, d, #F);
end intrinsic;

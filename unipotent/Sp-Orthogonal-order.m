freeze;

// orders of centralisers in semisimple and orthogonal groups

// GO -- generators for semisimple piece 

GO_SSOrder_Odd := function (VBeta, T, q) 
   order := 1;
   W := T[1]; 
   for a in Set (W) do
      d := #[x: x in W | x eq a];
      C := ChevalleyGroup ("C", d, q);
      order *:= #C;
   end for;

   V := T[2];
   V := [2 * x + 1: x in V];
   values_V := [v : v in Set (V)];
   Sort (~values_V);
   for a in values_V do 
      beta := [b[2] : b in VBeta | b[1] eq a];
      M := DiagonalMatrix (GF(q), beta);
      if Nrows (M) gt 1 then
         if IsEven (Nrows (M)) then 
            epsilon := (-1)^(Nrows (M) div 2) * Determinant (M);
            type := IsSquare (epsilon) select "plus" else "minus";
            ord := type eq "plus" select  #GOPlus (Nrows (M), q)
                                    else #GOMinus (Nrows (M), q);
         else 
            ord := #GO (Nrows (M), q);
         end if;
         order *:= ord;
      else
         order *:= 2;
      end if;
   end for;
    
   return order;
end function;

GOCentraliserDimension_Odd := function (m)
   dim := [m[i][1]: i in [1..#m]];
   mult := [m[i][2]: i in [1..#m]];
   ParallelSort (~dim, ~mult);

   a := [(dim[i] - 1) * mult[i]^2: i in [1..#m] | IsOdd (dim[i])]; 
   a := #a gt 0 select &+a / 2 else 0;
   b := [(dim[i] - 1) * mult[i]^2: i in [1..#m] | IsEven (dim[i])]; 
   b := #b gt 0 select &+b / 2 else 0;
   c := [mult[i]: i in [1..#m] | IsEven (dim[i])]; 
   c := #c gt 0 select &+c / 2 else 0;
   
   d := 0;
   for i in [1..#m] do 
      x := [dim[i] * mult[i] * mult[j]: j in [i + 1..#m]];
      d +:= #x eq 0 select 0 else &+x;
   end for;
   return Integers () ! (a + b - c + d);
end function;

GO_ConvertT := function (T)
   V := []; W := [];
   for a in Set (T) do 
      m := Multiplicity (T, a);
      if IsOdd (a) then
         b := (a - 1) div 2;
         V cat:= [b: i in [1..m]];
      else
         W cat:= [a: i in [1..m div 2]];
      end if;
   end for;
   Sort (~V); Reverse (~V);
   Sort (~W); Reverse (~W);
   return [W, V];
end function;

OrthogonalUnipotentCentraliserOrder_Odd := function (type, VBeta, T, split, q) 
   s := MultisetToSequence (T);
   m := [<x, #[y: y in s | y eq x]>: x in Set (s)];
   dim := GOCentraliserDimension_Odd (m);
   T_new := GO_ConvertT (T);
   a := GO_SSOrder_Odd (VBeta, T_new, q);
   o :=  a * q^dim;
   if type in {"GO", "GO+", "GO-", "O", "O+", "O-"} then
      return o;
   elif type in {"SO+", "Omega+"} and forall{x : x in Set (T) | IsEven (x)} then
      return o;
   else
      if type in {"SO+", "SO-", "SO"} then return o div 2; end if;
      if split eq true then return o div 2; end if;
      return o div 4;
   end if;
end function;

// Sp generators for semisimple piece 

SpSSOrder_Odd := function (VBeta, T, q) 
   order := 1;

   W := T[1]; 
   for a in Set (W) do
      d := #[x: x in W | x eq a];
      order *:= ChevalleyGroupOrder ("C", d, q);
   end for;

   V := T[2];
   values_V := [v : v in Set (V)];
   Sort (~values_V);
   for a in values_V do 
      beta := [b[2] : b in VBeta | b[1] eq 2 * a];
      M := DiagonalMatrix (GF(q), beta);
      if Nrows (M) eq 1 then 
         order *:= 2;
      else 
         if IsEven (Nrows (M)) then 
            epsilon := (-1)^(Nrows (M) div 2) * Determinant (M);
            type := IsSquare (epsilon) select "plus" else "minus";
            ord := type eq "plus" select #GOPlus (Nrows (M), q)
                   else #GOMinus (Nrows (M), q);
         else 
            ord := #GO (Nrows (M), q);
         end if;
         order *:= ord;
      end if;
   end for;
    
   return order;
end function;

// dimension of unipotent subgroup of centraliser
SpCentraliserDimension_Odd := function (m)
   dim := [m[i][1]: i in [1..#m]];
   mult := [m[i][2]: i in [1..#m]];
   ParallelSort (~dim, ~mult);

   a := [(dim[i] - 1) * mult[i]^2: i in [1..#m] | IsOdd (dim[i])];
   a := #a gt 0 select &+a / 2 else 0;

   b := [(dim[i] - 1) * mult[i]^2: i in [1..#m] | IsEven (dim[i])];
   b := #b gt 0 select &+b / 2 else 0;

   c := [mult[i]: i in [1..#m] | IsEven (dim[i])];
   c := #c gt 0 select &+c / 2 else 0;

   d := 0;
   for i in [1..#m] do
      x := [dim[i] * mult[i] * mult[j]: j in [i + 1..#m]];
      d +:= #x eq 0 select 0 else &+x;
   end for;
   assert IsIntegral (a + b + c + d);
   return Integers() ! (a + b + c + d);
end function;

SpConvertT := function (T)
   V := []; W := [];
   for a in Set (T) do 
      m := Multiplicity (T, a);
      if IsEven (a) then
         b := a div 2;
         V cat:= [b: i in [1..m]];
      else
         W cat:= [a div 2: i in [1..m div 2]];
      end if;
   end for;
   Sort (~V); 
   Sort (~W); 
   return [W, V];
end function;

SpUnipotentCentraliserOrder_Odd := function (T, VBeta, q) 
   s := MultisetToSequence (T);
   m := [<x, #[y: y in s | y eq x]>: x in Set (s)];
   T := SpConvertT (T);
   a := SpSSOrder_Odd (VBeta, T, q);
   dim := SpCentraliserDimension_Odd (m);
   return a * q^dim;
end function;

// C_G (u) where u is determined by data in T 

CentraliserDimension_Even := function (type, T)
   W := T[1] cat T[1] cat T[3] cat T[3];
   Sort (~W); Reverse (~W);
   V := T[2] cat T[4];
   V := [2 * v : v in V];
   dim := 0;
   Chi := [];
   for i in [1..#V] do
      d := V[i]; 
      value := type eq "Sp" select d div 2 else (d + 2) div 2;
      Append (~Chi, value);
   end for;
   for i in [1..#W] do
      d := W[i]; 
      pos := Position (V, d);
      if pos ne 0 then 
         value := type eq "Sp" select d div 2 else (d + 2) div 2;
         Append (~Chi, value);
      else 
         value := type eq "Sp" select Floor ((W[i] - 1) / 2) else Floor ((W[i] + 1) / 2);
         Append (~Chi, value);
      end if;
   end for;
   V cat:= W;
   assert #Chi eq #V;
   ParallelSort (~V, ~Chi); Reverse (~V); Reverse (~Chi);
   dim := &+[i * V[i] - Chi[i]: i in [1..#V]];
   return dim, V, Chi;
end function;

// centraliser structure for element determined by T

CentraliserStructure_Even := function (type, T, q)
   W := T[1] cat T[3];
   V := T[2] cat T[4];
   Sort (~V);
    
   M := Multiset (W);

   A := [Multiplicity (M, s): s in Set (M) | IsEven (s)];
   L := [* <"C", a, q>: a in A *];

   if type eq "Sp" then 
      S := {w: w in W | w eq 1 or 
               (IsOdd (w) and exists{v: v in V | Abs (w - 2 * v) eq 1})};
   else 
      S := {w: w in W | (IsOdd (w) and exists{v: v in V | Abs (w - 2 * v) eq 1})};
   end if;
   A := [Multiplicity (M, s): s in S];
   L cat:= [* <"C", a, q>: a in A *];

   T3 := Set (T[3]);
   T := {w : w in W | IsOdd (w) and not (w in S)};
   T := [t: t in T];
   A := [Multiplicity (M, t): t in T];
   for i in [1..#A] do 
      a := A[i];
      t := T[i];
      Minus := [w: w in T3 | w eq t];
      sign := IsOdd (#Minus) select "-" else "+";
      name := "O" cat sign;
      L cat:= [* <name, a, q> *];
   end for;
      
   t := #[j: j in [1..#V - 1] | V[j + 1] - V[j] ge 2];
   delta := ((#V eq 0) or (type eq "Sp" and 1 in V)) select 0 else 1;
   power := t + delta; 
   if power gt 0 then 
      L cat:= [* <19, 2^power, 0> *];
   end if;
    
   return L;
end function;

// order of centraliser of unipotent element 
// in GO / Omega^\epsilon (d, q) where q is even 

Orthogonal_MyDimension := function (str)
   type := str[1];
   r := str[2];
   q := str[3];
   if type cmpeq 19 then return 0; end if;
   if type cmpeq "C" then return 2*r^2 + r; end if;
   if type cmpeq "O+" then return 2*r^2 - r; end if;
   if type cmpeq "O-" then return 2*r^2 - r; end if;
   if type cmpeq "O" then return 2*r^2 + r; end if;
end function;

Orthogonal_MyBlockDimension := function (block)
   if #block eq 0 then return 0; end if;
   return &+[Orthogonal_MyDimension (s): s in block];
end function;

Orthogonal_Dimension_Even := function (q, t) 
   X := CentraliserDimension_Even ("Omega-", t);
   S := CentraliserStructure_Even ("Omega-", t, q);
   Y := Orthogonal_MyBlockDimension (S);
   return S, X - Y;
end function;

Orthogonal_Order := function (S, z, q)
   order := q^z;
   for t in S do
      tup := t;
      if tup[1] cmpeq 19 then ord := tup[2];
      elif tup[1] cmpeq "O-" then ord := #GOMinus (2 * tup[2], tup[3]);
      elif tup[1] cmpeq "O+" then ord := #GOPlus (2 * tup[2], tup[3]);
      else ord := ChevalleyGroupOrder (tup[1], tup[2], tup[3]);
      end if;
      order *:= ord;
   end for;
   return order;
end function;

OrthogonalUnipotentCentraliserOrder_Even := function (type, T, q) 
   assert IsEven (q);
   S, z := Orthogonal_Dimension_Even (q, T);
   k := Orthogonal_Order (S, z, q);
   if type eq "Omega-" then
      if T[#T] eq -1 then return k; else return k div 2; end if;
   elif type eq "Omega+" then 
      if #T[2] eq 0 and #T[4] eq 0 and #T[3] eq 0 and 
         forall{x: x in Set (T[1]) | IsEven (x)} then return k; end if;
      return k div 2;
   elif type in {"O+", "O-", "GO-", "SO-", "GO+", "SO+"} then 
      return k;
   else 
      error "type";
   end if;
end function;

OrthogonalUnipotentCentraliserOrder := function (type, T, VBeta, split, q)
   if IsEven (q) then
      return OrthogonalUnipotentCentraliserOrder_Even (type, T, q);
   else
      return OrthogonalUnipotentCentraliserOrder_Odd (type, VBeta, T, split, q);
   end if;
end function;

SpMyDimension := function (str)
   type := str[1];
   r := str[2];
   q := str[3];
   if type cmpeq 19 then return 0; end if;
   if type cmpeq "C" then return 2*r^2 + r; end if;
   if type cmpeq "O+" then return 2*r^2 - r; end if;
   if type cmpeq "O-" then return 2*r^2 - r; end if;
   if type cmpeq "O" then return 2*r^2 + r; end if;
end function;

SpBlockDimension := function (block)
   if #block eq 0 then return 0; end if;
   return &+[SpMyDimension (s): s in block];
end function;

SpCentraliserDimension_Even := function (t, q)
   X := CentraliserDimension_Even ("Sp", t);
   S := CentraliserStructure_Even ("Sp", t, q);
   Y := SpBlockDimension (S);
   return X - Y, S;
end function;

SpUnipotentCentraliserOrder_Even := function (T, q)
   dim, S := SpCentraliserDimension_Even (T, q);
   order := 1;
   for t in S do
      tup := t;
      if tup[1] cmpeq 19 then ord := tup[2];
      elif tup[1] cmpeq "O-" then ord := #GOMinus (2 * tup[2], tup[3]);
      elif tup[1] cmpeq "O+" then ord := #GOPlus (2 * tup[2], tup[3]);
      else ord := ChevalleyGroupOrder (tup[1], tup[2], tup[3]);
      end if;
      order *:= ord;
   end for;
   return order * q^dim;
end function;

SpUnipotentCentraliserOrder := function (T, VBeta, q)
   if IsEven (q) then
      return SpUnipotentCentraliserOrder_Even (T, q);
   else
      return SpUnipotentCentraliserOrder_Odd (T, VBeta, q);
   end if;
end function;

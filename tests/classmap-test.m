// SetVerbose ("STCS", 2);
// SetVerbose ("RandomSchreier", 2);

// supporting function
SelectGroup1 := function (type, n, q)
   case type:
      when "GO+":
         G := GOPlus (n, q);
      when "GO":
         G := GO (n, q);
      when "GO-":
         G := GOMinus (n, q);
      when "SO+":
         G := SOPlus (n, q);
      when "SO":
         G := SO (n, q);
      when "SO-":
         G := SOMinus (n, q);
      when "Omega+":
         G := OmegaPlus (n, q);
      when "Omega":
         G := Omega (n, q);
      when "Omega-":
         G := OmegaMinus (n, q);
      when "Sp":
         G := Sp (n, q);
      when "GU":
         G := GU (n, q);
      when "SU":
         G := SU (n, q);
   end case;

   return G;
end function;


// start testing class map

for type in ["GU","SU"] do
   type;
   printf("\n");
   for n in [2,3,4,5,6] do
      for q in [2,3,4] do
         X,L:=ClassicalClasses(type,n,q);
         G := SelectGroup1 (type, n, q);
         eta := ClassicalClassMap (G, X, L);
         Arr:=[eta (x[3]^Random (G)): x in X];
         type, n, q;
         assert Arr eq [1..#L];
      end for;
   end for;
end for;

for type in ["GO", "SO", "Omega"] do
   type;
   printf("\n");
   for n in [3,5,7,9] do
      for q in [3,5,7,9] do
         X,L:=ClassicalClasses(type,n,q);
         G := SelectGroup1(type,n,q); 
         eta := ClassicalClassMap (G, X, L);
         Arr:=[eta (x[3]^Random (G)): x in X];
         type, n, q;
         assert Arr eq [1..#L];
      end for;
   end for;
end for;

for type in ["GO+","SO+","Omega+","GO-","SO-","Omega-","Sp"] do
   type;
   printf("\n");
   for n in [4,6,8] do
      for q in [2,3,4,5,7,8,9] do
         X,L:=ClassicalClasses(type,n,q);
         G := SelectGroup1(type,n,q); 
         eta := ClassicalClassMap (G, X, L);
         Arr:=[eta (x[3]^Random (G)): x in X];
         type, n, q;
         assert Arr eq [1..#L];
      end for;
   end for;
end for;

// start testing centralizer cardinality

for type in ["GU","SU"] do
   type;

   printf("\n");
   for n in [3,4,5,6] do
      for q in [2,3] do
         G := SelectGroup1(type,n,q); 
         X,L:=ClassicalClasses(type,n,q);
         C:=#SelectGroup1(type,n,q);
         SW := [i: i in [1..#L] |  X[i][2] ne C div Integers()!ClassicalCentraliserOrder(G,X[i][3])];
         type, n,q;
         assert #SW eq 0;
      end for;
   end for;
end for;

for type in ["GO+","SO+","Omega+","GO-","SO-","Omega-","Sp"] do
   type;
   printf("\n");
   for n in [2,4,6,8] do
      for q in [2,3,4,5,7,8] do
         G := SelectGroup1(type,n,q); 
         X,L:=ClassicalClasses(type,n,q);
         C:=#SelectGroup1(type,n,q);
tp := IsIrreducible (G) eq false select type else false;
         SW := [i: i in [1..#L] |  X[i][2] ne C div
Integers()!ClassicalCentraliserOrder(G,X[i][3])];
         type, n,q;
         assert #SW eq 0;
      end for;
   end for;
end for;

for type in ["GO","SO","Omega"] do
   type;
   printf("\n");
   for n in [3,5,7,9] do
      for q in [3,5,7,9] do
         X,L:=ClassicalClasses(type,n,q);
         G := SelectGroup1(type,n,q); 
         C:=#SelectGroup1(type,n,q);
         SW := [i: i in [1..#L] |  X[i][2] ne C div
Integers()!ClassicalCentraliserOrder(G,X[i][3])];
         type,n,q;
         assert #SW eq 0;
      end for;
   end for;
end for;

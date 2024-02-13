AttachSpec ("../Classes.spec");

SelectGroup := function (type, n, q)
   case type:
      when "GO+":
         G := GOPlus(n, q); G`ClassicalType := "GO+";
      when "GO":
         G := GO (n, q); G`ClassicalType := "GO";
      when "GO-":
         G := GOMinus(n, q); G`ClassicalType := "GO-";
      when "SO+":
         G := SOPlus(n, q); G`ClassicalType := "SO+";
      when "SO":
         G := SO(n, q); G`ClassicalType := "SO";
      when "SO-":
         G := SOMinus(n, q); G`ClassicalType := "SO-";
      when "Omega+":
         G := OmegaPlus(n, q); G`ClassicalType := "Omega+";
      when "Omega":
         G := Omega(n, q); G`ClassicalType := "Omega";
      when "Omega-":
         G := OmegaMinus(n, q); G`ClassicalType := "Omega-";
      when "Sp":
         G := Sp(n, q); G`ClassicalType := "Sp";
      when "GU":
         G := GU(n, q); G`ClassicalType := "GU";
      when "SU":
         G := SU(n, q); G`ClassicalType := "SU";
   end case;

   return G;
end function;


for type in ["GO+","GO-","SO+","SO-","Omega+","Omega-"] do
   for n in [2,4, 6] do
      for q in [2,3,4,5,7,8] do
         type, n, q;
         X,L := ClassicalConjugacyClasses (type, n, q);
         G := SelectGroup (type, n, q);
         SX := [ x[3]: x in X | IsSemisimple (x[3]) ];
         phi := ClassicalClassMap(G,X,L);
         Y := [ ClassesForFixedSemisimple (G, x) : x in SX ];
         Z := &cat(Y);
         assert #Z eq #X;
         assert { phi (x[3]): x in Z } eq { 1..#X };
      end for;
   end for;
end for;


for type in ["GU","SU"] do
   if type eq "GU" then start := 1; else start := 2; end if;
   for n in [start..5] do
      for q in [2,3,4,5] do
         type, n, q;
         X,L := ClassicalConjugacyClasses (type, n, q);
         G := SelectGroup (type, n, q);
         SX := [ x[3]: x in X | IsSemisimple (x[3]) ];
         phi := ClassicalClassMap(G,X,L);
         Y := [ ClassesForFixedSemisimple (G, x) : x in SX ];
         Z := &cat(Y);
         assert #Z eq #X;
         assert { phi (x[3]): x in Z } eq { 1..#X };
      end for;
   end for;
end for;

for type in ["GO","SO","Omega"] do
   for n in [3,5,7,9] do
      for q in [3,5,7] do
         type, n, q;
         X,L := ClassicalConjugacyClasses (type, n, q);
         G := SelectGroup (type, n, q);
         SX := [ x[3]: x in X | IsSemisimple (x[3]) ];
         phi := ClassicalClassMap(G,X,L);
         Y := [ ClassesForFixedSemisimple (G, x) : x in SX ];
         Z := &cat(Y);
         assert #Z eq #X;
         assert { phi (x[3]): x in Z } eq { 1..#X };
      end for;
   end for;
end for;

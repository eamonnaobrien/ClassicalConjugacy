AttachSpec ("../Classes.spec");

// check classes; centraliser and order; also conjugation 
SetVerbose ("CompositionTree", 0);
CountSS := true; // if true, construct unipotent elements for each ss-rep 

Z := Integers ();

// how much work?  
// run over relevant dimensions from start .. last 
start := 2;
last := 8;

// separate for unitary case 
last_U := 6;

TestMap := true;

"Linear groups";
for d in [start..last - 2] do
  for q in [2,3,4] do
     G := SL (d, q);
     X := Classes (G);
     "linear", d, q, "#X is", #X;
     for i in [1..#X] do 
     g := X[i][3];
     x := Random (G);
     flag, h := ClassicalIsConjugate (G, g, g^x);
     assert flag;
     assert h in G;
     if not (g^(h) eq g^x) then "Conjugation failed"; end if;;
     C := ClassicalCentralizer (G, g);
     assert forall{j: j in [1..Ngens (C)] | C.j in G};
     assert IsCentral (C, g);
     o := LMGFactoredOrder (C);
     a := ClassicalClassSize (G, g);
     assert a eq X[i][2];
     CO := ClassicalCentraliserOrder (G, g);
     assert o eq CO;
     end for;
  end for;
end for;

"Symplectic groups";
for d in [start..last by 2] do
   for q in [2,3,4,5,8] do
     G := Sp (d, q);
     X := Classes (G);
     "symplectic", d, q, "#X is", #X;
     eta := ClassicalClassMap (G);
     for i in [1..#X] do 
     g := X[i][3];
     x := Random (G);
     flag, h := ClassicalIsConjugate (G, g, g^x);
     assert flag;
     assert h in G;
     assert g^(h) eq g^x;
     C := ClassicalCentralizer (G, g);
     assert forall{j: j in [1..Ngens (C)] | C.j in G};
     assert IsCentral (C, g);
     o := LMGFactoredOrder (C);
     a := ClassicalClassSize (G, g);
     assert a eq X[i][2];
     CO := ClassicalCentraliserOrder (G, g);
     assert o eq CO;
     j := eta (X[i][3]^Random (G));
     assert j eq i;
     end for;
     "Construct unipotent for each ss d =", d, "q = ", q;
     Y:=[ClassesForFixedSemisimple (G, X[l][3]):  l in [1..#X] | IsSemisimple (X[l][3])]; 
     count := &+[#y: y in Y];
     assert count eq #X;
  end for;
end for;

"GO -";
 for d in [start..last by 2] do
   for q in [2,3,4,5] do
     G := GOMinus (d, q);
     X := Classes (G);
     "GO-", d, q, "#X is", #X;
     "Set up class map";
     eta := ClassicalClassMap (G);
     for i in [1..#X] do 
     g := X[i][3];
     x := Random (G);
     flag, h := ClassicalIsConjugate (G, g, g^x);
     assert flag;
     // assert h in G;
     assert g^(h) eq g^x;
     C := ClassicalCentralizer (G, g);
     // assert forall{j: j in [1..Ngens (C)] | C.j in G};
     o := LMGFactoredOrder (C);
     a := ClassicalClassSize (G, g);
     assert a eq X[i][2];
     CO := ClassicalCentraliserOrder (G, g);
     assert o eq CO;
     j := eta (X[i][3]^Random (G));
     assert j eq i;
     end for;
     if CountSS then 
     "Construct unipotent for each ss d =", d, "q = ", q;
     Y:=[ClassesForFixedSemisimple (G, X[l][3]):  l in [1..#X] | IsSemisimple (X[l][3])]; 
     count := &+[#y: y in Y];
     assert count eq #X;
     end if;
  end for;
end for;

"GO +";
for d in [start..last by 2] do
  for q in [2, 3,4,5] do
     G := GOPlus (d, q);
     X := Classes (G);
"Set up class map";
     eta := ClassicalClassMap (G);
     for i in [1..#X] do 
     g := X[i][3];
     x := Random (G);
     flag, h := ClassicalIsConjugate (G, g, g^x);
     assert flag;
     // assert h in G;
     assert g^(h) eq g^x;
     C := ClassicalCentralizer (G, g);
     // assert forall{j: j in [1..Ngens (C)] | C.j in G};
     assert IsCentral (C, g);
     o := LMGFactoredOrder (C);
     a := ClassicalClassSize (G, g);
     assert a eq X[i][2];
     CO := ClassicalCentraliserOrder (G, g);
     assert o eq CO;
     j := eta (X[i][3]^Random (G));
     assert i eq j;
     end for;
     if CountSS then 
     "Construct unipotent for each ss d =", d, "q = ", q;
     Y:=[ClassesForFixedSemisimple (G, X[l][3]):  l in [1..#X] | IsSemisimple (X[l][3])]; 
     count := &+[#y: y in Y];
     assert count eq #X;
      end if;
  end for;
end for;

"SO -";
for d in [start..last by 2] do
  for q in [2,3,4,5] do
     G := SOMinus (d, q);
     X := Classes (G);
     "SO-", d, q, "#X is", #X;
"Set up class map";
     eta := ClassicalClassMap (G);
     for i in [1..#X] do 
     g := X[i][3];
     x := Random (G);
     flag, h := ClassicalIsConjugate (G, g, g^x);
     assert flag;
     // assert h in G;
     assert g^(h) eq g^x;
     C := ClassicalCentralizer (G, g);
     // assert forall{j: j in [1..Ngens (C)] | C.j in G};
     assert IsCentral (C, g);
     o := LMGFactoredOrder (C);
     a := ClassicalClassSize (G, g);
     assert a eq X[i][2];
     CO := ClassicalCentraliserOrder (G, g);
     assert o eq CO;
     j := eta (X[i][3]^Random (G));
     assert i eq j;
     end for;
    if CountSS then 
     "Construct unipotent for each ss d =", d, "q = ", q;
     Y:=[ClassesForFixedSemisimple (G, X[l][3]):  l in [1..#X] | IsSemisimple (X[l][3])]; 
     count := &+[#y: y in Y];
     assert count eq #X;
     end if;
  end for;
end for;

"SO +";
for d in [start..last by 2] do
  for q in [2,3,4,5] do
     G := SOPlus (d, q);
     X := Classes (G);
     "SO+", d, q, "#X is", #X;
     // if not (d eq 2 and (IsOdd (q) or q in {2})) then 
"Set up class map";
     eta := ClassicalClassMap (G);
     for i in [1..#X] do 
     g := X[i][3];
     x := Random (G);
     flag, h := ClassicalIsConjugate (G, g, g^x);
     assert flag;
     // assert h in G;
     assert g^(h) eq g^x;
     C := ClassicalCentralizer (G, g);
     // assert forall{j: j in [1..Ngens (C)] | C.j in G};
     assert IsCentral (C, g);
     o := LMGFactoredOrder (C);
     a := ClassicalClassSize (G, g);
     assert a eq X[i][2];
     CO := ClassicalCentraliserOrder (G, g);
     assert o eq CO;
     j := eta (X[i][3]^Random (G));
     assert i eq j;
     end for;
     if CountSS  then 
     "Construct unipotent for each ss d =", d, "q = ", q;
     Y:=[ClassesForFixedSemisimple (G, X[l][3]):  l in [1..#X] | IsSemisimple (X[l][3])]; 
     count := &+[#y: y in Y];
     assert count eq #X;
     end if;
  end for;
end for;


"Omega +";
for d in [start..last by 2] do
  for q in [2,3,4,5,8] do
     G := OmegaPlus (d, q);
     X := Classes (G);
     "Omega+", d, q, "#X is", #X;
"Set up class map";
     eta := ClassicalClassMap (G);
     for i in [1..#X] do 
     g := X[i][3];
     x := Random (G);
     flag, h := ClassicalIsConjugate (G, g, g^x);
     assert flag;
     // assert h in G;
     assert g^(h) eq g^x;
     C := ClassicalCentralizer (G, g);
     // assert forall{j: j in [1..Ngens (C)] | C.j in G};
     assert IsCentral (C, g);
     o := LMGFactoredOrder (C);
     a := ClassicalClassSize (G, g);
     assert a eq X[i][2];
     CO := ClassicalCentraliserOrder (G, g);
     assert o eq CO;
     j := eta (X[i][3]^Random (G));
     assert i eq j;
     end for;
     if CountSS then 
     "Construct unipotent for each ss d =", d, "q = ", q;
     Y:=[ClassesForFixedSemisimple (G, X[l][3]):  l in [1..#X] | IsSemisimple (X[l][3])]; 
     count := &+[#y: y in Y];
     assert count eq #X;
     end if;
  end for;
end for;

"Omega -";
for d in [start..last by 2] do
  for q in [2,3,4,5,8] do
     G := OmegaMinus (d, q);
     X := Classes (G);
     "Omega-", d, q, "#X is", #X;
     // if not (d eq 2) then 
     if TestMap then 
"Set up class map";
     eta := ClassicalClassMap (G);
     end if;
     for i in [1..#X] do 
     g := X[i][3];
     x := Random (G);
     flag, h := ClassicalIsConjugate (G, g, g^x);
     assert flag;
     // assert h in G;
     assert g^(h) eq g^x;
     C := ClassicalCentralizer (G, g);
     // assert forall{j: j in [1..Ngens (C)] | C.j in G};
     assert IsCentral (C, g);
     o := LMGFactoredOrder (C);
     a := ClassicalClassSize (G, g);
     assert a eq X[i][2];
     CO := ClassicalCentraliserOrder (G, g);
     assert o eq CO;
     j := eta (X[i][3]^Random (G));
     assert i eq j;
     end for;
     if CountSS then 
     "Construct unipotent for each ss d =", d, "q = ", q;
     Y:=[ClassesForFixedSemisimple (G, X[l][3]):  l in [1..#X] | IsSemisimple (X[l][3])]; 
     count := &+[#y: y in Y];
     assert count eq #X;
     end if;
  end for;
end for;

"GO";
for d in [start+1..last+1 by 2] do
  for q in [3,5,7] do
     G := GO (d, q);
     X := Classes (G);
     "GO", d, q, "#X is", #X;
"Set up class map";
     eta := ClassicalClassMap (G);
     for i in [1..#X] do 
     g := X[i][3];
     x := Random (G);
     flag, h := ClassicalIsConjugate (G, g, g^x);
     assert flag;
     // assert h in G;
     assert g^(h) eq g^x;
     C := ClassicalCentralizer (G, g);
     // assert forall{j: j in [1..Ngens (C)] | C.j in G};
     assert IsCentral (C, g);
     o := LMGFactoredOrder (C);
     a := ClassicalClassSize (G, g);
     assert a eq X[i][2];
     CO := ClassicalCentraliserOrder (G, g);
     assert o eq CO;
     j := eta (X[i][3]^Random (G));
     assert i eq j;
     end for;
     if CountSS then 
     "Construct unipotent for each ss d =", d, "q = ", q;
     Y:=[ClassesForFixedSemisimple (G, X[l][3]):  l in [1..#X] | IsSemisimple (X[l][3])]; 
     count := &+[#y: y in Y];
     assert count eq #X;
     end if;
  end for;
end for;


"SO";
for d in [start+1..last + 1 by 2] do
  for q in [3,5,7,9] do
    // if q eq 3 and d eq 3 then continue; end if;
     G := SO (d, q);
     X := Classes (G);
     "SO", d, q, "#X is", #X;
     "Setup class map";
     eta := ClassicalClassMap (G);
     for i in [1..#X] do 
     g := X[i][3];
     x := Random (G);
     flag, h := ClassicalIsConjugate (G, g, g^x);
     assert flag;
     // assert h in G;
     assert g^(h) eq g^x;
     C := ClassicalCentralizer (G, g);
     // assert forall{j: j in [1..Ngens (C)] | C.j in G};
     assert IsCentral (C, g);
     o := LMGFactoredOrder (C);
     a := ClassicalClassSize (G, g);
     assert a eq X[i][2];
     CO := ClassicalCentraliserOrder (G, g);
     assert o eq CO;
     j := eta (X[i][3]^Random (G));
     assert i eq j;
     end for;
     if CountSS then 
     "Construct unipotent for each ss d =", d, "q = ", q;
     Y:=[ClassesForFixedSemisimple (G, X[l][3]):  l in [1..#X] | IsSemisimple (X[l][3])]; 
     count := &+[#y: y in Y];
     assert count eq #X;
     end if;
  end for;
end for;

"Omega";
for d in [start+1..last+1 by 2] do
  for q in [3,5,7,9] do
     if q in { 3, 5} and d eq 3 then continue; end if;
     G := Omega (d, q);
     X := Classes (G);
     "Omega", d, q, "#X is", #X;
     "Set up class map";
     eta := ClassicalClassMap (G);
     for i in [1..#X] do 
     g := X[i][3];
     x := Random (G);
     flag, h := ClassicalIsConjugate (G, g, g^x);
     assert flag;
     //  assert h in G;
     assert g^(h) eq g^x;
     C := ClassicalCentralizer (G, g);
     // assert forall{j: j in [1..Ngens (C)] | C.j in G};
     assert IsCentral (C, g);
     o := LMGFactoredOrder (C);
     a := ClassicalClassSize (G, g);
     assert a eq X[i][2];
     CO := ClassicalCentraliserOrder (G, g);
     assert o eq CO;
     j := eta (X[i][3]^Random (G));
     assert i eq j;
     end for;
     "Construct unipotent for each ss d =", d, "q = ", q;
     Y:=[ClassesForFixedSemisimple (G, X[l][3]):  l in [1..#X] | IsSemisimple (X[l][3])]; 
     count := &+[#y: y in Y];
     assert count eq #X;
  end for;
end for;

"Unitary GU";
for d in [start - 1..last_U] do
  for q in [2,3,4,5] do
     G := GU (d, q);
     X := Classes (G);
     d, q, "#X is", #X;
     eta := ClassicalClassMap (G);
     for i in [1..#X] do 
     g := X[i][3];
     x := Random (G);
     flag, h := ClassicalIsConjugate (G, g, g^x);
     assert flag;
     assert h in G;
     assert g^(h) eq g^x;
     C := ClassicalCentralizer (G, g);
     assert forall{j: j in [1..Ngens (C)] | C.j in G};
     assert IsCentral (C, g);
     o := LMGFactoredOrder (C);
     a := ClassicalClassSize (G, g);
     assert a eq X[i][2];
     CO := ClassicalCentraliserOrder (G, g);
     assert o eq CO;
     if TestMap then 
     j := eta (X[i][3]^Random (G));
     assert i eq j;
     end if;
     end for;
     "Construct unipotent for each ss d =", d, "q = ", q;
     Y:=[ClassesForFixedSemisimple (G, X[l][3]):  l in [1..#X] | IsSemisimple (X[l][3])]; 
     count := &+[#y: y in Y];
     assert count eq #X;
  end for;
end for;

"Unitary SU";
for d in [start..last_U] do
  for q in [2,3,4,5] do
     G := SU (d, q);
     X := Classes (G);
     d, q, "#X is", #X;
     eta := ClassicalClassMap (G);
     for i in [1..#X] do 
     g := X[i][3];
     x := Random (G);
     flag, h := ClassicalIsConjugate (G, g, g^x);
     assert flag;
     assert h in G;
     assert g^(h) eq g^x;
     C := ClassicalCentralizer (G, g);
     assert forall{j: j in [1..Ngens (C)] | C.j in G};
     assert IsCentral (C, g);
     o := LMGFactoredOrder (C);
     a := ClassicalClassSize (G, g);
     CO := ClassicalCentraliserOrder (G, g);
     assert a eq X[i][2];
     assert o eq CO;
     j := eta (X[i][3]^Random (G));
     end for;
     "Construct unipotent for each ss d =", d, "q = ", q;
     Y:=[ClassesForFixedSemisimple (G, X[l][3]):  l in [1..#X] | IsSemisimple (X[l][3])]; 
     count := &+[#y: y in Y];
     assert count eq #X;
  end for;
end for;

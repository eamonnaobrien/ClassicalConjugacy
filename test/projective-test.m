AttachSpec ("../Classes.spec");
// some test code for projective class functions

q := 8; d := 4; 
G:=Sp (d, q);
time X, P, phi, Y := ProjectiveClassicalClasses ("Sp", d, q);
for i in [1..100] do
i;
a := Random (P);
b := a^Random (P);
am := a @@ phi;
bm := b @@ phi;
f, cm := ProjectiveClassicalIsConjugate (G, am, bm);
c := phi (cm);
assert a^c eq b;
end for;
 for i in [2..#Y] do
PC := ProjectiveClassicalCentraliser (G, Y[i][3]);
i;
D := PC @ phi;
assert phi (Y[i][3]) eq X[i][3]; assert IsCentral (D, X[i][3]);
end for;


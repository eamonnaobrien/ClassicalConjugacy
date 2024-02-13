freeze;

// G = GL(n,q) or SL(n,q)
// compute the factored order of the centralizer of x in G
// if the JordanForm of x is known, the function can be 
// called with the parameter JF

GLCentralizerOrder := function (G, x: JF := [])

   F := CoefficientRing (G);
   q := #F;
   n := Nrows (x);
   if JF eq [] then 
      _, _, c := JordanForm (x);
   else
      c := JF;
   end if;

   // check if special case holds
   SLOrder := forall{x: x in Generators (G) | Determinant (x) eq 1};

   S := {@ c[i]: i in [1..#c] @};
   r := FactoredOrder (GL(Multiplicity(c, S[1]), q^(Degree(c[1][1]))));
   i := 2;
   while i le #S do
      r *:= FactoredOrder (GL(Multiplicity(c, S[i]), q^(Degree(S[i][1]))));
      i +:= 1;
   end while;
   if SLOrder then 
       d := Gcd ([S[i][2]: i in [1..#S]]);
       d := Gcd (d, q-1);
       r /:= Factorization (q-1);
       r *:= Factorization (d);
   end if;
   
   g := 0;
   i := 1;
   while i le #S do
      j := i+1;
      g +:= Degree(S[i][1]) * (S[i][2] - 1) * Multiplicity(c, S[i])^2;
      while j le #S and S[i][1] eq S[j][1] do
         //we know that c[i][2] <= c[j][2] for i<j
         g +:= 2 * Degree(S[j][1]) * S[i][2] *
               Multiplicity(c, S[i]) * Multiplicity(c, S[j]);     
         j +:= 1;
      end while;
      i +:= 1;
   end while;
   g := Factorization (q^g);
   return r * g;
end function;

SLCentralizerOrder := function (G, x: JF := [])
   return GLCentralizerOrder (G, x: JF := JF);
end function;

freeze;

// if x and y are conjugate in GL, then returns true and z in SL 
// such that z^-1*x*z=y, otherwise returns false
GLIsConjugate := function (G, x, y)
   Jx, B, c := JordanForm (x);
   Jy, C, _ := JordanForm (y);
   if Jx eq Jy then 
      return true, Generic (G)! (B^-1 * C);
   else 
      return false, _;
   end if;
end function;

// if x and y are conjugate in SL, then returns true and z in SL 
// such that z^-1*x*z=y, otherwise returns false
SLIsConjugate := function (S, x, y)
   ax, B, c := JordanForm (x);
   ay, C, _ := JordanForm (y);
   m := #c;
   answer := false;
   if ax ne ay then return false, _; end if;

   F := CoefficientRing (S);
   n := Nrows (x);
   if #F eq 2 then
      return true, GL(n, F)!(B^-1*C);
   end if;
   d := Gcd (Gcd ([c[i][2]: i in [1..m]]), #F-1);
   R := IntegerRing (#F-1);
   w := PrimitiveElement (F);
   s := B^-1*C;
   f := Log (w, Determinant (s));
   answer := d ne #F - 1 select IsDivisibleBy (R!f, R!d) else (R!f eq 0);
      
   if answer then
      // construct matrix Y commuting with the JordanForm 
      // and such that det Y = det (s)^-1 = w^-f
      Form := ZeroMatrix (F, 0, 0);
      for i in [1..m] do
         deg := Degree (c[i][1]);
         X := DiagonalJoin ([CompanionMatrix (c[i][1]): j in [1..c[i][2]]]);
         for j in [1..deg * (c[i][2]-1)] do
            X[j, deg+j] := 1;
         end for;
         Form := DiagonalJoin (Form, X);
      end for;
      // Form = modified Jordan Form of X
      _, bX, _ := JordanForm (Form);
      A := Matrix (R, m, 1, [c[i][2]: i in [1..m]]);
      W := Matrix (R, 1, 1, [-f]);
      v := Solution (A, W);
      Y := ZeroMatrix (F, 0, 0);
      for i in [1..m] do
         E<a> := ext<F|c[i][1]: Optimize := false>;
         t := PrimitiveElement (E);
         g := Log (Norm (t, F), w);
         X := CompanionMatrix (c[i][1]);
         X := &+[X^(j-1) * Eltseq (t, F)[j]: j in [1..Degree (c[i][1])]];
         X := X^(Integers ()!(g*v[1][i]));
         Y := DiagonalJoin (Y, DiagonalJoin ([X: j in [1..c[i][2]]]));
      end for;
      s := B^-1*bX*Y*bX^-1*C;
      s := GL(n, F) ! s;
      return true, s; 
   else 
      return answer, _; 
   end if;
end function;

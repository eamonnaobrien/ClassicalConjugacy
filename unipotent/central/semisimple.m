freeze;

// generators for semisimple part of centraliser for SL and SU

ListParts := function (X)
   if #X eq 0 then return X; end if;
   X := [[x]: x in X];
   k := 1;
   repeat 
      strip := [X[i][k] : i in [1..#X]];
      d := Minimum ([s: s in strip | s ne 0]);
      for i in [1..#X] do
         if X[i][k] ge d then
            X[i][k +1] := X[i][k] - d;
            X[i][k] := d; 
         else 
            X[i][k +1] := 0;
         end if;
     end for;
     k +:= 1;
     strip := [X[i][k] : i in [1..#X]];
   until #{x: x in strip | x ne 0} le 1;
   return X;
end function;

SemisimpleData := function (W)
   wt := [W[i][1]: i in [1..#W]];
   m := [W[i][2]: i in [1..#W]];

   odd := [m[i]: i in [1..#m] | IsOdd (wt[i])];
   odd := ListParts (odd);

   even := [m[i]: i in [1..#m] | IsEven (wt[i])];
   even := ListParts (even);

   result := []; n_odd := 0; n_even := 0;
   for  i in [1..#wt] do
      if IsOdd (wt[i]) then n_odd +:= 1; Append (~result, odd[n_odd]); end if;
      if IsEven (wt[i]) then n_even +:= 1; Append (~result, even[n_even]); end if;
   end for;

   return result, odd, even;
end function;

// W is weight data for unipotent matrix in SL or SU 
// write down semisimple centraliser of corresponding rep 

SemisimpleMatrices := function (W, q: Type := "Linear")
   result, odd, even := SemisimpleData (W);

   d := &+[W[i][2]: i in [1..#W]];
   wt := [W[i][1]: i in [1..#W]];
   even := [i: i in [1..#wt] | IsEven (wt[i])];
   odd := [i: i in [1..#wt] | IsOdd (wt[i])];  

   X := [&+x: x in result];
   d := &+X;
   pos := [[1..X[1]]];
   pos cat:= [[&+[X[i]: i in [1..j-1]] + x : x in [1..X[j]]]: j in [2..#X]];

   I := [];
   for r in [1..#result] do 
      res := result[r];
      res := [x : x in res | x gt 0];
      I[r] := [];
      for j in [1..#res] do 
         offset := j gt 1 select &+[res[k]: k in [1..j - 1]] else 0;
         Append (~I[r], [pos[r][offset + l]: l in [1..res[j]]]);
      end for;
   end for;

   Strip := function (I, index)
      a := [x[index] : x in I | #x ge index];
      b := [#x: x in a];
      assert #Set (b) le 1;
      return a, Set (b);
   end function;

   MyGU := function (d, q)
      MA := MatrixAlgebra (GF(q), d);
      form := Identity (MA);
      tr := TransformForm (form, "unitary");
      G := GU (d, Isqrt (q));
      return G^(tr^-1);
   end function;

   ProcessStrip := function (strip, dim, d, q: Type := "Linear")
      S := Type eq "Linear" select GL(dim, q) else MyGU(dim, q);
      MA := MatrixAlgebra (GF(q), d);
      M := MatrixAlgebra (GF(q), dim);
      gens := [MA | ];
      for j in [1..Ngens (S)] do 
         z := Identity (MA);
         for i in [1..#strip] do
            a := strip[i][1]; 
            InsertBlock (~z, M!S.j, a, a);
         end for;
         // det := Determinant (z);
         // "Take n-th root", m := &+[#x: x in strip];
         Append (~gens, z);
      end for;
      return gens;
   end function;

   if Type ne "Linear" then q := q^2; end if;

   S := [];
   ell := Maximum ([#x: x in I]);
   for k in [1..ell] do 
      strip_even, dim := Strip ([I[i]: i in even], k);
      if #Set (dim) ne 0 then 
         dim := Rep (dim);
         A:= ProcessStrip (strip_even, dim, d, q: Type := Type);
      else A := [];
      end if;
      strip_odd, dim := Strip ([I[i]: i in odd], k);
      if #Set (dim) ne 0 then 
         dim := Rep (dim);
         B := ProcessStrip (strip_odd, dim, d, q: Type := Type);
      else   
         B := [];
      end if;
      M := A cat B;
      if #M gt 0 then 
         Append (~S, M);
      end if;
   end for;
   return sub<GL(d, q) | &cat (S)>, S;
end function;

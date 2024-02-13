freeze;

// building blocks

MySpinorNorm := function (g, form)
   // assert IsSymmetric (form);
   value := Determinant (g) eq 1 and SpinorNorm (g, form + Transpose (form)) eq 0 select 0 else 1;
   return value;
end function;

NonSquare := function (K)
  return PrimitiveElement (K);
  // assert exists(k){ x : x in K | IsSquare (x) eq false};
  // return k;
end function;

ChooseAlpha := function (q)
   P<x> := PolynomialRing (GF (q));
   assert exists(alpha){alpha: alpha in GF(q) | IsIrreducible (x^2 + x + alpha)};
   return alpha;
end function;

MySort := function (m)
   X := [m[i][1] * m[i][2]: i in [1..#m]];
   Y := [[1..X[1]]];
   Y cat:= [[&+[X[i]: i in [1..j-1]] + x : x in [1..X[j]]]: j in [2..#X]];

   C := func<x, y | y[1] - x[1]>;
   Sort (~m, C, ~p);

   p := Eltseq (p);
   L := [];
   for i in [1..#p] do
      L[i] := Y[p[i]];
   end for;
   L := &cat (L);
   return m, L;
end function;

CayleyTransform := function (u)
   d := Nrows (u);
   F := BaseRing (u);
   MA := MatrixAlgebra (F, d);
   u := MA!u;
   return (u^0 - u) * (u^0 + u)^-1;
end function;

MyCommutatorSpace := function (V, U, gens)
   return sub< V | [v - v * g: g in gens, v in Basis (U)]>;
end function;

CentralisedSpace := function (g)
   G := Parent (g);
   F := CoefficientRing (G);
   A := MatrixAlgebra (F, Degree (G));
   a := A!g;
   N := NullSpace (a - Identity (A));
   // vprint Except: "Nullspace has dimension ", Dimension (N);
   return N;
end function;

/* write down perp space of U meet Space wrt Form; Form is
   defined only on Space and not on the full vector space */

PerpSpace := function (Form, U, Space)
   W := U meet Space;
   F := BaseRing (U);
   d := Degree (U);
   r := Dimension (W);
   L := [Eltseq (w) : w in Basis (W)];
   W := KMatrixSpace (F, d, r) !  &cat [[L[i][j] : i in [1..r]]: j in [1..d]];
   return NullSpace (Form * W) meet Space;
end function;

// perp space for S

MyPerpSpace := function (S, form)
   d := Nrows (form);
   K := BaseRing (Parent (form));
   V := VectorSpace (K, d, form);
   L := [Eltseq (w) : w in Basis (S)];
   r := Dimension (S);
   // if r eq 0 then return sub<V| >; end if;
   W := KMatrixSpace (K, d, r) !  &cat [[L[i][j] : i in [1..r]]: j in [1..d]];
   N := NullSpace (form * W);
   N := sub< V | [N.i: i in [1..Dimension (N)]]>;
   return N;
end function;

MyInnerProduct := function (form, u, v, q)
   F := BaseRing (form);
   d := Nrows (form);
   MA := KMatrixSpace (F, d, 1);
   a := u * form * MA!Eltseq (v);
   return a[1];
end function;

MyDiagonalJoin := function (L)
   if #L eq 0 then return L; end if;
   assert #L ne 0;
   A := L[1];
   for i in [2..#L] do
      A := DiagonalJoin (A, L[i]);
   end for;
   return A;
end function;

FixesForm := function (r, form)
   d := Nrows (form); F := BaseRing (Parent (form));
   G := MatrixAlgebra (F, d);
   return G!r * G!form * G!Transpose (r) eq form;
end function;

FixesUnitaryForm := function (x, form)
   F := BaseRing (form);
   e := Degree (F) div 2;
   MA := MatrixAlgebra (F, Nrows (x));
   x := MA!x;
   return x*form*Transpose(FrobeniusImage(x, e)) eq form;
end function;

// Convert quadratic form to an upper triangular matrix
function NormaliseQuadForm(form)
   n := NumberOfRows(form);
   assert NumberOfColumns(form) eq n;
   newForm := ZeroMatrix(CoefficientRing(form), n, n);
    
   for i in [1 .. n] do
      for j in [i .. n] do
         if not i eq j then
            newForm[i][j] := form[i][j] + form[j][i];
	 else
	    newForm[i][j] := form[i][j];
         end if;
      end for;
   end for;
    
   return newForm;
end function;

// does g preserve quadratic form?
FixesQuadraticForm := function (g, form)
   n_form := NormaliseQuadForm (form);
   new_form := NormaliseQuadForm (g * form * Transpose (g));
   return n_form eq new_form;
end function;

JordanBlock := function (d, q)
   M := MatrixAlgebra (GF(q), d);
   A := Identity (M);
   for i in [1..d - 1] do
      A[i][i + 1] := 1;
   end for;
   return A;
end function;

MyInsert := function (M, N, a, b)
   for i in [1..Nrows (N)] do 
      for j in [1..Ncols (N)] do 
         M[a[i], b[j]] := N[i, j];
      end for;
   end for;
   return M;
end function;

Q_value := function (form, v)
   V :=  Matrix (v) * form * Transpose (Matrix (v));
   return V[1][1];
end function;

// compute kernel of hom from G to cyclic group C 
// images of generators of G in C are listed in image
KernelOfHom := function (G, C, image)
   if #C eq 1 then return G; end if;
   n, a := XGCD (image cat [#C]);
   g := &*[G.i^a[i] : i in [1 .. Ngens(G)]];
   // generators of kernel as normal subgroup
   H := [G.i * g^(-image[i] div n) : i in [1 .. Ngens(G)]];
   // add in conjugates to generate kernel as subgroup
   K := [g^(#C div n)] cat [H[i]^(g^u) : i in [1 .. #H], u in [0 .. #C - 1]];
   return sub<Generic (G) | K>;
end function;


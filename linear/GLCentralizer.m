freeze;

import "GLCentralizerOrder.m": GLCentralizerOrder;

//matrix in E = F_q^r --> matrix in F_q
StdEm := function (A, F)
  return WriteMatrixOverSmallerField(A,F);
end function;

// x is an element of G = GL(d, q); determine its centraliser 
GLCentralizer := function (G, x)          //need StdEm
   gl := Generic (G);
   F := CoefficientRing (G);
   n := Nrows (x);
   a, b, c := JordanForm (x);

   Set := {@ c[i]: i in [1..#c] @};  //begin semisimple part
   Gen := {@@};
   for j in [1..#Set] do
      E := ext<F | Set[j][1]: Optimize := false>;
      m := Multiplicity (c, Set[j]);
      Gr := GL (m, E);
      pos := &+[Multiplicity (c, Set[k]) * Degree (Set[k][1]) * Set[k][2]: 
                  k in [1..j]] - m * Degree (Set[j][1]) * Set[j][2];
      for k in [1..Ngens (Gr)] do
            r := BlockMatrix(m,m, [StdEm(ScalarMatrix(E,Set[j][2],(Gr.k)[l1][l2]),F): l1, l2 in [1..m]]);
         Include (~Gen, gl!InsertBlock (IdentityMatrix (F, n), r, pos+1, pos+1));
      end for;
   end for;   //end semisimple part

   for j in [1..#Set] do  //begin internal blocks
      m := Set[j][2];
      if m gt 1 then
         E := ext<F | Set[j][1]: Optimize := false>;
         mu := Multiplicity (c, Set[j]);
         u := StdEm (Matrix(E,1,1,[PrimitiveElement(E)]), F);
         pos := 1;
         if j gt 1 then
            pos +:= &+[Degree (Set[i][1]) * Set[i][2] *
                       Multiplicity (c, Set[i]): i in [1..j-1]];
         end if;
         for k in [1..m-1] do
            for h in [1..Degree (E)] do
               r := IdentityMatrix (F, n);
               for i in [1..m-k] do
                  InsertBlock (~r, u^(h-1), pos+(i-1) * Degree (E, F), 
                     pos + (i+k-1) * Degree (E, F));
               end for;
               Include (~Gen, gl!r);
            end for;
         end for;
      end if;
   end for;  //end internal blocks

   r := IdentityMatrix (F, n);   //begin external blocks
   pos := 1;
   for i in [1..#c-1] do
      if c[i][1] eq c[i+1][1] and c[i][2] ne c[i+1][2] then
         li := Degree (c[i][1]) * c[i][2];
         lj := Degree (c[i+1][1]) * c[i+1][2];
         Include (~Gen, gl!InsertBlock (r, IdentityMatrix (F, Min (li, lj)), 
                   pos, pos + li + Max (0, lj - li)));
         Include (~Gen, gl!InsertBlock (r, 
            IdentityMatrix (F, Min (li, lj)), pos+li, pos+Max (li-lj, 0)));
      end if;
      pos +:= Degree (c[i][1])*c[i][2];
   end for;   //end external blocks

   //begin construction of generalized Jordan form matrix
   r := DiagonalJoin (<DiagonalJoin ([CompanionMatrix (c[i][1]): 
                        j in [1..c[i][2]]]): i in [1..#c]>);
   pos := 1;
   for i in [1..#c] do
      if c[i][2] ge 2 then
         for j in [1..c[i][2]-1] do
            InsertBlock (~r, IdentityMatrix (F, Degree (c[i][1])), 
               pos + (j-1) * Degree (c[i][1]), pos+j*Degree (c[i][1]));
         end for;
      end if;
      pos +:= Degree (c[i][1]) * c[i][2];
   end for;  //end construction generalized Jordan form matrix

   _,B,_:=JordanForm(x);
   _,C,_:=JordanForm(gl!r);

   H := sub<gl | Gen>;
   H := H^(gl!(C^-1*B));
   order := GLCentralizerOrder (gl, x: JF := c);
   H`FactoredOrder := order;
   H`Order := Integers ()!order;
   return H, H`Order;
end function;

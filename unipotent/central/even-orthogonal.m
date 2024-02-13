freeze;

import "../util.m": MyDiagonalJoin, MyInsert, KernelOfHom;
import "../even-char.m": SetupRep;
import "../Sp-Orthogonal-order.m": OrthogonalUnipotentCentraliserOrder_Even; 
import "../conjugation/even/even-label.m": SpO_EvenLabel; 
import "even-sp.m": SetupBlocks, LargerMatGroup, WeightsToLabel;

// q even
// code to set up centraliser of special rep in GO or Omega 

// Q (w0) = Q (x0) = beta 
Omega_A1 := function (d, q, w_mi, w_0, x_0, x_i, l, beta)
   MA := MatrixAlgebra (GF(q), d);
   A := Identity (MA);
   A[w_mi, x_0] := l;
   A[w_mi, x_i] := l^2 * beta;
   A[w_0, x_i] := l;
   return A;
end function;

// Q (w0) = Q (x0) = beta 
Omega_A2 := function (d, q, x_mi, w_0, x_0, w_i, l, beta) 
   MA := MatrixAlgebra (GF(q), d);
   A := Identity (MA);
   A[x_mi, x_0] := l;
   A[x_mi, w_i] := l^2 * beta;
   A[w_0, w_i] := l;
   return A;
end function;

// Q (w0) = Q (x0) = beta 
Omega_A3 := function (d, q, w_mi, x_0, w_0, x_i, l, beta)
   MA := MatrixAlgebra (GF(q), d);
   A := Identity (MA);
   A[w_mi, w_0] := l;
   A[w_mi, x_i] := l^2 * beta;
   A[x_0, x_i] := l;
   return A;
end function;

// Q (w0) = Q (x0) = beta 
Omega_A4 := function (d, q, x_mi, x_0, w_0, w_i, l, beta)
   MA := MatrixAlgebra (GF(q), d);
   A := Identity (MA);
   A[x_mi, w_0] := l;
   A[x_mi, w_i] := l^2 * beta;
   A[x_0, w_i] := l;
   return A;
end function;

Omega_B1 := function (d, q, w_mi, x_j, w_mj, x_i, l)
   MA := MatrixAlgebra (GF(q), d);
   A := Identity (MA);
   A[w_mi, w_mj] := l;
   A[x_j, x_i] := l;
   return A;
end function;

Omega_B2 := function (d, q, w_mi, w_j, x_mj, x_i, l)
   MA := MatrixAlgebra (GF(q), d);
   A := Identity (MA);
   A[w_mi, x_mj] := l;
   A[w_j, x_i] := l;
   return A;
end function;

Omega_B3 := function (d, q, x_mi, x_j, w_mj, w_i, l)
   MA := MatrixAlgebra (GF(q), d);
   A := Identity (MA);
   A[x_mi, w_mj] := l;
   A[x_j, w_i] := l;
   return A;
end function;

// Q(vm1) = alpha 
Omega_C2C5 := function (d, q, w_m1, v_m1, v1, x1, a, b, alpha)
   MA := MatrixAlgebra (GF(q), d);
   A := Identity (MA);
   A[w_m1, v_m1] := a;
   A[w_m1, v1] := b;
   A[w_m1, x1] := b * (a + b) + a^2 * alpha;
   A[v_m1, x1] := b;
   A[v1, x1] := a;
   return A;
end function;

Omega_C1 := function (d, q, w_mi, vj, v_mj, xi, l)
   MA := MatrixAlgebra (GF(q), d);
   A := Identity (MA);
   A[w_mi, v_mj] := l;
   A[vj, xi] := l;
   return A;
end function;

Omega_C4 := function (d, q, x_mi, vj, v_mj, wi, l)
   MA := MatrixAlgebra (GF(q), d);
   A := Identity (MA);
   A[x_mi, v_mj] := l;
   A[vj, wi] := l;
   return A;
end function;

Omega_D4 := function (d, q,  v_m1, w0, v1, v1_dash, vm1_dash, x0, a, b, c, dd)
   MA := MatrixAlgebra (GF(q), d);
   A := Identity (MA);
   A[v_m1, w0] := a;
   A[v_m1, x0] := b;
   A[v_m1, v1] := c;
   A[v_m1, v1_dash] := dd;
   A[vm1_dash, w0] := a;
   A[vm1_dash, x0] := b;
   A[vm1_dash, v1] := dd;
   A[vm1_dash, v1_dash] := c;
   A[w0, v1] := b;
   A[w0, v1_dash] := b;
   A[x0, v1] := a;
   A[x0, v1_dash] := a;
   return A;
end function;

Omega_D3 := function (d, q,  v_m1, v1, v1_dash, vm1_dash, c, dd)
   MA := MatrixAlgebra (GF(q), d);
   A := Identity (MA);
   A[v_m1, v1] := c;
   A[v_m1, v1_dash] := dd;
   A[vm1_dash, v1] := dd;
   A[vm1_dash, v1_dash] := c;
   return A;
end function;

Omega_D2 := function (d, q, v_mi, vi, vi_dash, vmi_dash, l)
   MA := MatrixAlgebra (GF(q), d);
   A := Identity (MA);
   A[v_mi, vi_dash] := l;
   A[vmi_dash, vi] := l;
   return A;
end function;

// alpha = Q (w0) 
Omega_D1 := function (d, q, v_mi, w0, x0, vi, a, b, alpha) 
   MA := MatrixAlgebra (GF(q), d);
   A := Identity (MA);
   A[v_mi, w0] := a;
   A[v_mi, x0] := b;
   A[v_mi, vi] := ((a^2 + b^2) * alpha + a * b);
   A[w0, vi] := b;
   A[x0, vi] := a;
   return A;
end function;

Omega_MatB := function (d, q, mi, j, i, mj, lambda)
   MA := MatrixAlgebra (GF (q), d);
   A := Identity (MA);
   A[mi, mj] := lambda;
   A[j, i] := lambda;
   return A;
end function;

// Q (vm1) = beta 
Omega_MatC := function (d, q, mi, m1, one, i, a, b, beta)
   MA := MatrixAlgebra (GF (q), d);
   A := Identity (MA);
   A[mi, m1] := a;
   A[mi, one] := b;
   A[mi, i] := b * (a + b) + a^2 * beta;
   A[m1, i] := b;
   A[one, i] := a;
   return A;
end function;

Omega_Mat14 := function (d, q,  v_m1, v1, vm1_dash, v1_dash, 
                         vm1_2dash, v1_2dash) 
   MA := MatrixAlgebra (GF(q), d);
   A := Identity (MA);
   A[v_m1, v1_dash] := 1; 
   A[v_m1, v1_2dash] := 1; 

   A[vm1_dash, v1] := 1;
   A[vm1_dash, v1_2dash] := 1; 

   A[vm1_2dash, v1] := 1;
   A[vm1_2dash, v1_dash] := 1;
   return A;
end function;

Opposites := function (W, N)
   weight := [W[i][1]: i in [1..#W]];

   mult := [W[i][2] : i in [1..#W]];
   full := [[weight[i]: j in [1..mult[i]]]: i  in [1..#weight]]; 
   full := &cat (full);

   w_list := [i : i in [1..#full] | Substring (N[i], 1, 1) eq "w"];
   x_list := [i : i in [1..#full] | Substring (N[i], 1, 1) eq "x"];
   v_list := [i : i in [1..#full] | Substring (N[i], 1, 1) eq "v"];

   v_list_minus := [i: i in v_list | full[i] lt 0];
   w_list_minus := [i: i in w_list | full[i] lt 0];
   x_list_minus := [i: i in x_list | full[i] lt 0];

   w_list_zero := [i: i in w_list | full[i] eq 0];
   x_list_zero := [i: i in x_list | full[i] eq 0];

   x_list_plus := [i: i in x_list | full[i] gt 0];
   v_list_plus := [i: i in v_list | full[i] gt 0];
   w_list_plus := [i: i in w_list | full[i] gt 0];

   // record opposites
   J := []; K := [];
   for w in weight do
      A := [i: i in [1..#full] | full[i] eq w and N[i][1] eq "v"];
      B := [i: i in [1..#full] | full[i] eq -w and N[i][1] eq "v"];
      for i in [1..#A] do
         a := A[i]; b := B[i];
         J[a] := b;
         J[b] := a;
      end for;

      A := [i: i in [1..#full] | full[i] eq w and N[i][1] eq "w"];
      B := [i: i in [1..#full] | full[i] eq -w and N[i][1] eq "w"];
      for i in [1..#A] do
         a := A[i]; b := B[i];
         J[a] := b;
         J[b] := a;
      end for;

      A := [i: i in [1..#full] | full[i] eq w and N[i][1] eq "x"];
      B := [i: i in [1..#full] | full[i] eq -w and N[i][1] eq "x"];
      for i in [1..#A] do
         a := A[i]; b := B[i];
         J[a] := b;
         J[b] := a;
      end for;
   end for;

   return J, full,
      w_list, x_list, v_list, 
      v_list_minus, w_list_minus, x_list_minus,
      w_list_zero, x_list_zero, 
      x_list_plus, v_list_plus, w_list_plus; 
end function;

// Setup Q parabolic subgroup for q even 
// Q_form: value of quadratic form on basis elements 
// Two labels are listed for the generators: 
// the first refers to original notes and labels given there; 
// the second of the form (n) or (n)-m is its number in the monograph

GO_QSubgroup_Even := function (W, q, N, Q_form)
   weight := [W[i][1]: i in [1..#W]];

   mult := [W[i][2] : i in [1..#W]];
   d := &+mult;

   // J records opposites 
   J, full, 
      w_list, x_list, v_list, 
      v_list_minus, w_list_minus, x_list_minus, 
      w_list_zero, x_list_zero, 
      x_list_plus, v_list_plus, w_list_plus := Opposites (W, N);

   F := GF(q);
   Gens := [];

   // "A1 -- (1)-1";
   B := Basis (F); 
   gens := []; 
   for a in [1..#w_list_minus] do 
      i := w_list_minus[a];
      ii := x_list_minus[a];
      for b in [1..#w_list_zero] do
         j := w_list_zero[b];
         beta := Q_form[j];
         for lambda in B do 
            g := Omega_A1 (d, q, i, j, x_list_zero[b], J[ii], lambda, beta);
            Append (~gens, g);
         end for;
      end for;
   end for;
   Append (~Gens, gens);
   
   // "A3 -- (1)-2";
   gens := [];
   for a in [1..#w_list_minus] do 
      i := w_list_minus[a];
      ii := x_list_minus[a];
      for b in [1..#x_list_zero] do
         j := x_list_zero[b];
         beta := Q_form[j];
         for lambda in B do  
            g:= Omega_A3 (d, q, i, j, w_list_zero[b], J[ii], lambda, beta);
            Append (~gens, g);
         end for;
      end for;
   end for;
   Append (~Gens, gens);

   // "A2 -- (1)-3";
   gens := [];
   for a in [1..#x_list_minus] do 
      i := x_list_minus[a];
      ii := w_list_minus[a];
      for b in [1..#w_list_zero] do
         j := w_list_zero[b];
         beta := Q_form[j];
         for lambda in B do  
            g := Omega_A2 (d, q, i, j, x_list_zero[b], J[ii], lambda, beta); 
            Append (~gens, g);
         end for;
      end for;
   end for;
   Append (~Gens, gens);

   // "A4 -- (1)-4";
   gens := [];
   for a in [1..#x_list_minus] do 
      i := x_list_minus[a];
      ii := w_list_minus[a];
      for b in [1..#x_list_zero] do
         j := x_list_zero[b];
         beta := Q_form[j];
         for lambda in B do  
            g := Omega_A4 (d, q, i, j, w_list_zero[b], J[ii], lambda, beta); 
            Append (~gens, g);
         end for;
      end for;
   end for;
   Append (~Gens, gens);

   // "B1 -- (2)-1";
   gens := [];
   for a in [1..#w_list_plus] do 
      i := w_list_plus[a];
      ii := x_list_plus[a];
      for b in [1..#x_list_plus] do
         j := x_list_plus[b];
         if full[j] lt full[i] then 
            jj := w_list_plus[b];
            for lambda in B do 
               g := Omega_B1 (d, q, J[i], j, J[jj], ii, lambda);
               Append (~gens, g);
            end for;
         end if;
      end for;
   end for;
   Append (~Gens, gens);

   // "Second B1 -- (2)-1";
   gens := [];
   for a in [1..#w_list_plus] do 
      i := w_list_plus[a];
      ii := x_list_plus[a];
      for b in [1..#x_list_minus] do
         j := x_list_minus[b];
         if full[j] lt full[i] then 
            jj := w_list_minus[b];
            for lambda in B do 
               g := Omega_B1 (d, q, J[i], j, J[jj], ii, lambda);
               Append (~gens, g);
            end for;
         end if;
      end for;
   end for;
   Append (~Gens, gens);

   // "Third B1 -- (2)-1";
   gens := [];
   for a in [1..#w_list_minus] do 
      i := w_list_minus[a];
      ii := x_list_minus[a];
      for b in [1..#x_list_minus] do
         j := x_list_minus[b];
         if full[j] lt full[i] then 
            jj := w_list_minus[b];
            for lambda in B do 
               g := Omega_B1 (d, q, J[i], j, J[jj], ii, lambda);
               Append (~gens, g);
            end for;
          end if;
      end for;
   end for;
   Append (~Gens, gens);

   // "B2 -- (2)-2";
   gens := [];
   for a in [1..#w_list_minus] do 
      i := w_list_minus[a];
      ii := x_list_minus[a];
      for b in [1..#w_list_plus] do
         j := w_list_plus[b];
         jj := x_list_plus[b];
         if full[j] lt Abs (full[i]) then 
            for lambda in B do 
               g := Omega_B2 (d, q, i, j, J[jj], J[ii], lambda); 
               Append (~gens, g);
            end for;
         end if;
      end for;
   end for;
   Append (~Gens, gens);

   // "Second B2 -- (2)-2";
   gens := [];
   for a in [1..#w_list_minus] do 
      i := w_list_minus[a];
      ii := x_list_minus[a];
      for b in [1..#w_list_minus] do
         j := w_list_minus[b];
         jj := x_list_minus[b];
         if Abs (full[j]) lt Abs (full[i]) then 
            for lambda in B do 
               g := Omega_B2 (d, q, i, j, J[jj], J[ii], lambda); 
               Append (~gens, g);
            end for;
         end if;
      end for;
   end for;
   Append (~Gens, gens);

   // "B3 -- (2)-3";
   gens := [];
   for a in [1..#x_list_plus] do 
      i := x_list_plus[a];
      ii := w_list_plus[a];
      for b in [1..#x_list_plus] do
         j := x_list_plus[b];
         jj := w_list_plus[b];
         if full[j] lt full[i] then 
            for lambda in B do 
               g := Omega_B3 (d, q, J[i], j, J[jj], ii, lambda); 
               Append (~gens, g);
            end for;
         end if;
      end for;
   end for;
   Append (~Gens, gens);

   // "Second B3 -- (2)-3";
   gens := [];
   for a in [1..#x_list_plus] do 
      i := x_list_plus[a];
      ii := w_list_plus[a];
      for b in [1..#x_list_minus] do
         j := x_list_minus[b];
         jj := w_list_minus[b];
         if Abs (full[j]) lt full[i] then 
            for lambda in B do 
               g := Omega_B3 (d, q, J[i], j, J[jj], ii, lambda); 
               Append (~gens, g);
            end for;
         end if;
      end for;
   end for;
   Append (~Gens, gens);

   // "C1 w_mi v_j -- (4)-1"; 
   B := Basis (F);
   gens := [];
   for a in [1..#w_list_minus] do
      i := w_list_minus[a];
      ii := x_list_minus[a];
      for b in [1..#v_list] do
         j := v_list[b];
         if full[j] in {-1, 1} or full[j] ge Abs(full[i]) then continue; end if;
         for lambda in B do 
            g := Omega_C1 (d, q, i, j, J[j], J[ii], lambda);
            Append (~gens, g);
         end for;
      end for;
   end for;
   Append (~Gens, gens);

   // "Second C1 v_mi w_j -- (4)-1";  
   B := Basis (F);
   gens := [];
   for a in [1..#v_list_minus] do
      i := v_list_minus[a];
      if full[i] in {-1} then continue; end if;
      for b in [1..#w_list] do
         j := w_list[b];
         jj := x_list[b];
         if full[j] in {0} or full[j] ge Abs(full[i]) then continue; end if;
         for lambda in B do 
            g := Omega_C1 (d, q, j, i, J[i], J[jj], lambda);
            Append (~gens, g);
         end for;
      end for;
   end for;
   Append (~Gens, gens);

   // "C4 x_mi v_j -- (4)-2";
   B := Basis (F);
   gens := [];
   for a in [1..#x_list_minus] do
      i := x_list_minus[a];
      ii := w_list_minus[a];
      for b in [1..#v_list] do
         j := v_list[b];
         if full[j] in {-1, 1} or full[j] ge Abs(full[i]) then continue; end if;
         for lambda in B do 
            g := Omega_C4 (d, q, i, j, J[j], J[ii], lambda);
            Append (~gens, g);
         end for;
      end for;
   end for;
   Append (~Gens, gens);

   // "Second C4 v_mi x_j -- (4)-2";
   B := Basis (F);
   gens := [];
   for a in [1..#v_list_minus] do
      i := v_list_minus[a];
      if full[i] in {-1} then continue; end if;
      for b in [1..#x_list] do
         j := x_list[b];
         jj := w_list[b];
         if full[j] in {0} or full[j] ge Abs(full[i]) then continue; end if;
         for lambda in B do 
            g := Omega_C4 (d, q, j, i, J[i], J[jj], lambda);
            Append (~gens, g);
         end for;
      end for;
   end for;
   Append (~Gens, gens);

   // "C2 and C3 (a=0) -- (5)-1"
   B := Basis (F);
   gens := [];
   for a in [1..#w_list_minus] do
      i := w_list_minus[a];
      ii := x_list_minus[a];
      // if full[i] eq -1 then B_1 := [0]; else B_1 := F; end if;
      if full[i] eq -1 then B_1 := [0]; else B_1 := Basis (F); end if;
      for b in [1..#v_list_minus] do
         j := v_list_minus[b];
         if full[j] eq -1 then 
            alpha := Q_form[j];
            for lambda in B_1 do 
               for mu in B do 
                  g := Omega_C2C5 (d, q, i, j, J[j], J[ii], lambda, mu, alpha);
                  Append (~gens, g);
               end for;
            end for;
         end if;
      end for;
   end for;
   Append (~Gens, gens);

   // "C5 and C6 (a=0) -- (5)-2"
   gens := [];
   B := Basis (F);
   for a in [1..#x_list_minus] do
      i := x_list_minus[a];
      ii := w_list_minus[a];
      if full[i] eq -1 then B_1 := [0]; else B_1 := Basis (F); end if;
      for b in [1..#v_list_minus] do
         j := v_list_minus[b];
         if full[j] eq -1 then 
            alpha := Q_form[j];
            for lambda in B_1 do 
               for mu in B do 
                  g := Omega_C2C5 (d, q, i, j, J[j], J[ii], lambda, mu, alpha);
                  Append (~gens, g);
               end for;
            end for;
         end if;
      end for;
   end for;
   Append (~Gens, gens);

   // D4 v_m1 v_m1' w0 x0 v1 v1' -- (9)
   B := Basis (F) cat [F!0];
   B1 := Basis (F);
   gens := [];
   for a in [1..#v_list_minus] do
      vm1 := v_list_minus[a];
      v1 := J[vm1];
      if full[vm1]  eq -1 then
         for b in [a + 1..#v_list_minus] do
            vm1_dash := v_list_minus[b];
            if full[vm1_dash] eq -1  then
               v1_dash := J[vm1_dash];
               for k in [1..#w_list_zero] do
                  w0 := w_list_zero[k];
                  gamma := Q_form[w0];
                  for l in [1..#x_list_zero] do
                     x0 := x_list_zero[k];
                     for cc in B do
                           for aa in B do 
                              for bb in B1 do
                                 dd := Sqrt (aa*bb + cc^2 + cc + (aa^2 + bb^2) * gamma); 
                                 C := Omega_D4 (d, q, vm1, w0, v1, v1_dash, vm1_dash, x0, aa, bb, cc, dd);
                                 Append (~gens, C);
                              end for;
                        end for;
                     end for;
                  end for;
               end for;
            end if;
         end for;
      end if;
   end for;
   Append (~Gens, gens);

   // D3 v_m1 v_m1' v1 v1' -- (8)
   B := Basis (F);
   gens := [];
   for a in [1..#v_list_minus] do 
      vm1 := v_list_minus[a];
      v1 := J[vm1];
      if full[vm1] ne -1 then continue; end if;
      for b in [a + 1..#v_list_minus] do 
         vm1_dash := v_list_minus[b];
         if full[vm1_dash] ne -1 then continue; end if;
         v1_dash := J[vm1_dash];
         for cc in B do
            dd := Sqrt (cc + cc^2);
            C := Omega_D3 (d, q, vm1, v1, v1_dash, vm1_dash, cc, dd);
            Append (~gens, C);
         end for;
      end for;
   end for;
   Append (~Gens, gens);

   // D2 v_mi v_mi' vi vi' where i > 1  -- (6)-2
   B := Basis (F);
   gens := [];
   for a in [1..#v_list_minus] do 
      vmi := v_list_minus[a];
      vi := J[vmi];
      if full[vmi] lt -1 then 
         for b in [a + 1..#v_list_minus] do 
            vmi_dash := v_list_minus[b];
            if full[vmi_dash] lt -1  then 
               vi_dash := J[vmi_dash];
               for l in B do
                  C := Omega_D2 (d, q, vmi, vi, vi_dash, vmi_dash, l);
                  Append (~gens, C);
               end for;
            end if;
         end for;
      end if;
   end for;
   Append (~Gens, gens);

   // D1 v_mi w0 x0 vi where i > 1  -- (6)-1
   B := Basis (F);
   gens := [];
   for a in [1..#v_list_minus] do
      v_mi := v_list_minus[a];
      if full[v_mi] eq -1 then continue; end if;
      vi := J[v_mi];
      for b in [1..#w_list_zero] do
         w0 := w_list_zero[b];
         alpha := Q_form[w0];
         for c in [1..#x_list_zero] do
            x0 := x_list_zero[b];
            for lambda in B do
               for mu in B do
                 g := Omega_D1 (d, q, v_mi, w0, x0, vi, lambda, mu, alpha);
                 Append (~gens, g);
              end for;
            end for;
         end for;
      end for;
   end for;
   Append (~Gens, gens);

   // "MatB v blocks: vmi vmj vi vj for i > 1" -- (3)
   B := Basis (F);
   gens := [];
   for a in [1..#v_list_plus] do
      i := v_list_plus[a];
      if full[i] eq 1 then continue; end if; 
      for b in [1..#v_list_plus] do
         j := v_list_plus[b];
         if full[j] in {1} or full[j] ge full[i] then continue; end if;
         for lambda in B do 
            g := Omega_MatB (d, q, J[i], j, v_list_plus[a], J[j], lambda);
            Append (~gens, g);
         end for;
      end for;
      for b in [1..#v_list_minus] do
         j := v_list_minus[b];
         if full[j] in {-1} or Abs (full[j]) ge full[i] then continue; end if;
         for lambda in B do 
            g := Omega_MatB (d, q, J[i], j, v_list_plus[a], J[j], lambda);
            Append (~gens, g);
         end for;
      end for;
   end for;
   Append (~Gens, gens);
  
   // "MatC v blocks: vmi vm1 v1 vi for i > 1" --(7) 
   gens := [];
   B:= Basis (F);
   for a in [1..#v_list_minus] do
      i := v_list_minus[a];
      if full[i] eq -1 then break a; end if;
      for b in [a + 1..#v_list_minus] do
         j := v_list_minus[b];
         beta := Q_form[j];
         if full[j] eq -1 then 
            for lambda in B do 
               for mu in B do 
                  g := Omega_MatC (d, q, i, j, J[j], J[i], lambda, mu, beta);
                  Append (~gens, g);
               end for;
            end for;
         end if;
      end for;
   end for;
   Append (~Gens, gens);

   // "Mat14" v_m1 v_m1' v_m1'' v_1 v_1' v_1''  -- (10) 
   gens := [];
   B := Basis (F);
   for a in [1..#v_list_minus] do 
      vmi := v_list_minus[a];
      vi := J[vmi];
      if full[vmi] eq -1 then 
         for b in [a + 1..#v_list_minus] do 
            vmi_dash := v_list_minus[b];
            if full[vmi_dash] eq -1 then 
               vi_dash := J[vmi_dash];
               for c in [b + 1..#v_list_minus] do 
                  vmi_2dash := v_list_minus[c];
                  if full[vmi_2dash] eq -1 then 
                     vi_2dash := J[vmi_2dash];
                     for l in B do
                        C := Omega_Mat14 (d, q, vmi, vi, vmi_dash, vi_dash, 
                                          vmi_2dash, vi_2dash);
                        Append (~gens, C);
                     end for;
                  end if;
               end for;
            end if;
         end for;
      end if;
   end for;
   Append (~Gens, gens);

   return sub<GL(d, q) | &cat Gens>, Gens;
end function;

GO_CentraliserDimension_Even := function (W)
   n := &+[W[i][2]: i in [1..#W]] div 2;
   m := &+[x[2]^2: x in W | x[1] lt 0];
   z := [x[2]: x in W | x[1] eq 0];
   if #z gt 0 then l := (z[1] div 2); else l := 0; end if;
   u := 2*l^2 - l + m;
   return (2 * n^2 - n - u) div 2;
end function;

// semisimple generators for centraliser of unipotent element 
// of GO (d, q) where q is even

// second case
Setup_Omega := function (d, q, n)
   G := OmegaPlus (d, q);
   Q := MatrixAlgebra (GF(q), 2) ! [0,1,0,0];
   a := d div 2;
   form := MyDiagonalJoin ([Q: i in [1..a]]);
   tr := TransformForm (form, "orth+");
   G := G^(tr^-1);
   gens := [G.i: i in [1..Ngens (G)]];
   assert n mod d eq 0; 
   s := n div d;
   large := [DiagonalJoin ([gens[i]: j in [1..s]]): i in [1..#gens]];
   return large;
end function;

TwoAdditional := function (d, q, W, X, w0, x0, v1, v1_dash, vm1, vm1_dash)
   MA := MatrixAlgebra (GF(q), d);
   L := [];
   m1 :=  Identity (MA);
   m1[w0,x0] := 1;
   m1[w0,v1_dash] := 1;
   m1[vm1_dash,x0] := 1;
   for i in [1..#W] do
      wi := W[i]; xi := X[i];
      m1[wi,xi] := 1;
   end for;
   Append (~L, m1);

   B := Identity (MA);
   m2 := Identity (MA);
   m2[x0, w0] := 1;
   m2[x0, v1] := 1;
   m2[vm1, w0] := 1;
   for i in [1..#W] do
      wi := W[i]; xi := X[i];
      m2[xi, wi] := 1;
   end for;
   Append (~L, m2);
   return L;
 end function;

// two additional gens for second case  
Case2 := function (d, q, N, I, J)
    
    W := [i: i in I | N[i][1] eq "w" and N[i][2] eq 0];
    w0 := W[1]; 
    W := [i: i in I | N[i][1] eq "w" and N[i][2] ne 0];

    X := [i: i in I | N[i][1] eq "x" and N[i][2] eq 0];
    x0 := X[1]; 
    X := [i: i in I | N[i][1] eq "x" and N[i][2] ne 0];

    assert exists(v1){j : j in J[1] | N[j][1] eq "v" and N[j][2] eq 1};
    assert exists(vm1){j : j in J[1] | N[j][1] eq "v" and N[j][2] eq -1};
    assert exists(v1_dash){j : j in J[2] | N[j][1] eq "v" and N[j][2] eq 1};
    assert exists(vm1_dash){j : j in J[2] | N[j][1] eq "v" and N[j][2] eq -1};
    L := TwoAdditional (d, q, W, X, w0, x0, v1, v1_dash, vm1, vm1_dash);
    return L;
end function;

// third case
Case3 := function (s, d, q, beta) 
   assert d mod s eq 0;
   a := s div 2;
   R := MatrixAlgebra (GF(q), 2) ! [beta,1,0,beta];
   if a - 1 gt 0 then
      Q := MatrixAlgebra (GF(q), 2) ! [0,1,0,0];
      form := MyDiagonalJoin ([Q: i in [1..a - 1]]);
      form := MyDiagonalJoin ([* form, R *]);
   else
      form := R;
   end if;
   V := QuadraticSpace(form);
   G := IsometryGroup (V);
   MA := MatrixAlgebra (GF(q), s);
   small := [MA!G.i: i in [1..Ngens (G)]];
   m := d div s;
   L := [MyDiagonalJoin ([small[i] : j in [1..m]]): i in [1..#small]];
   return L, G;
end function;
   
// case 4 
Case4 := function (d, q, I, J, form)
   v := [];
   for i in [1..#I] do
      v cat:= [I[i], J[i]];
   end for;
   r := #v div 2;
   vm := [v[i]: i in [1..r]];
   vp := [v[i]: i in [r + 1..#v]];
      
   v := vm cat vp;
   MA := MatrixAlgebra (GF(q), d);
   MB := MatrixAlgebra (GF(q), 2);

   A_list := [];
   F := GF (q);
   for a in Basis (F) do 
      A := Identity (MA);
      B := MB![a + 1, a, a, a + 1];
      for i in [1..#v by 2] do 
         A := MyInsert (A, B, [v[i], v[i + 1]], [v[i], v[i + 1]]); 
      end for;
      beta := form[vm[#vm], vm[#vm]]; 
      B := MB![a^2 * beta, a^2 * beta,
               a^2 * beta, a^2 * beta];
      A := MyInsert (A, B, [vm[#vm-i]: i in [1,0]], [vp[i]: i in [1..2]]);
      Append (~A_list, A);
   end for;
   return A_list;
end function;

Case5 := function (d, q, beta, wm1, w1)
   CreateMat := function (q)
      MB := MatrixAlgebra (GF(q), 4);
      B := Identity (MB);
      B[1,3] := 1; B[1,4] := 1;
      B[2,3] := 1; B[2,4] := 1;
      B[3,1] := 1; B[3,2] := 1;
      B[4,1] := 1; B[4,2] := 1;
      return B;
   end function;
   
   B := CreateMat (q); 
   MA := MatrixAlgebra (GF (q), d);
   A := Zero (MA);
   for i in [1..Nrows (A) div 4] do
      j := (i - 1) * 4 + 1;
      InsertBlock (~A, B, j, j);
   end for;

   CreateMat2 := function (q, beta)
      MB := MatrixAlgebra (GF(q), 4);
      B := Zero (MB);
      B[1,2] := beta; 
      B[2,1] := beta;
      B[3,1] := beta; B[3,2] := beta;
      B[4,1] := beta; B[4,2] := beta;
      return B;
   end function;
   
   B := CreateMat2 (q, beta); 
   InsertBlock (~A, B, wm1, w1);
   return A;
end function;

FindIndices := function (L, type, dim: Alpha := false) 
   if type eq "W" then good := {"w", "x"}; else good := {"v"}; end if;
   if Alpha then 
      I := [i : i in [1..#L] | L[i][1] in good and L[i][3] eq dim and L[i][5] eq true];
   else 
      I := [i : i in [1..#L] | L[i][1] in good and L[i][3] eq dim];
   end if;
      
   nmr :={L[i][4]: i in I};
   nmr := [x : x in nmr];
   Sort (~nmr);
   return [[i : i in I | L[i][4] eq s]: s in nmr];
end function;

// generators and order for semisimple part of centraliser
// set up semisimple generators
GO_SSGenerators_Even := function (r, P, phi, tau, N, N1, form, T, q: 
   OmegaOnly := false)

   d := Nrows (r);

   W := T[1]; V := T[2]; W_alpha := T[3]; V_alpha := T[4];

   MA := MatrixAlgebra (GF (q), d);

   // first case -- similar to Sp even characteristic 
   // Section 5.2.2 of monograph 
   Gens := [];
   u := phi (r);
   for m in Set (W) do
      if IsEven (m) then
         a := #[x : x in W | x eq m];
         strings := {s cat IntegerToString (m): s in {"w", "x"}};
         I := [i : i in [1..#N1] | N1[i] in strings];
         B, sf := SetupBlocks (I, q, a, form: type := "orthogonal");
         B := LargerMatGroup (d, q, B, I);
         gens := [];
         for i in [1..Ngens (B)] do
            flag, vi := IsConjugate (P, u, phi (r^B.i));
            assert flag;
            h := vi @ tau;
            Append (~gens, h);
         end for;
         gens := [B.i * gens[i]^-1: i in [1..#gens]];
         assert forall{x : x in gens | Order ((x, r)) eq 1};
         Append (~Gens, gens);
      end if;
   end for;
   Gens1 := &cat Gens;
   // "Case 1: Number of gens is ", #Gens;

   // Section 5.2.4 of monograph 
   W_list := Set (W cat W_alpha);
   W_list := {w : w in W_list | IsOdd (w)};
   Gens2 := [];
   Gens := [];
   for rank in W_list do
      I := FindIndices (N, "W", rank);
      J := FindIndices (N, "V", (rank - 1) div 2);
      if #J eq 0 then 
         J := FindIndices (N, "V", (rank + 1) div 2);
      end if;
      if #I eq 0 or #J eq 0 then continue; end if;
      K := [FindIndices (N, "V", r): r in V cat V_alpha]; 
      K := &cat (K);
      a := #I;
      I_all := &cat (I);
      index := [i : i in I_all | N[i][1] cat IntegerToString (N[i][2]) eq "w0" or 
                                 N[i][1] cat IntegerToString (N[i][2]) eq "x0"];
      assert #index gt 0;
      S := Setup_Omega (#index, q, #I_all);
      gens := [];
      Sort (~I_all);
      for i in [1..#S] do 
         B := Identity (MA);
         l := MyInsert (B, S[i], I_all, I_all);
         Append (~gens, l);
      end for;
      Gens cat:= gens;
      for j in [1..#J] do
         for k in [1..#K] do 
            if J[j] eq K[k] then continue k; end if;
            Gens cat:= Case2 (d, q, N, I[1], [J[j], K[k]]);
         end for;
      end for;
   end for;
   Gens := [GL(d, q) ! x: x in Gens];
   // "Case 2: Number of gens is ", #Gens;
   u := phi (r);
   A := [v @ tau where _, v := IsConjugate (P, u, phi (r^l)): l in Gens];
   Gens2 := [Gens[i] * A[i]^-1: i in [1..#Gens]];

   // case 3 
   // Section 5.2.4 of monograph 
   Gens3 := [];
   Gens := []; 
   W_list := W cat W_alpha;
   W_list := {w : w in W_list | IsOdd (w)};
   W_list := [x: x in W_list];
   Sort (~W_list);

   for rank in W_list do 
      J := FindIndices (N, "V", (rank - 1) div 2);
      if #J gt 0 then continue; end if;

      J := FindIndices (N, "V", (rank + 1) div 2);
      if #J gt 0 then continue; end if;

      // W(rank) and W_alpha (rank) 
      I  := FindIndices (N, "W", rank);
      a := #I;
      I := &cat (I);
      I_index := [i : i in I | N[i][1] cat IntegerToString (N[i][2]) eq "w0" or
                               N[i][1] cat IntegerToString (N[i][2]) eq "x0"];
      beta := form[I_index[#I_index - 1], I_index[#I_index - 1]];
      S := Case3 (#I_index, #I, q, beta);
      gens := [];
      Sort (~I);
      for s in [1..#S] do
         B := Identity (MA);
         l := MyInsert (B, S[s], I, I);
         Append (~gens, l);
      end for;
      Append (~Gens, gens);
   end for;
   
   Gens := &cat (Gens);
   Gens := [GL(d, q) ! x: x in Gens];
   // "Case 3: Number of gens is ", #Gens;
   u := phi (r);
   A := [v @ tau where _, v := IsConjugate (P, u, phi (r^l)): l in Gens];
   Gens3 := [Gens[i] * A[i]^-1: i in [1..#Gens]];

   // which elements lie outside of Omega?
   if OmegaOnly then 
      index := [i: i in [1..#Gens3] | SpinorNorm (Gens3[i], form) eq 1];
      go_elements := [Gens3[i]: i in index];
      assert forall{x: x in go_elements | Order ((r, x)) eq 1};
      Gens3 := [Gens3[i]: i in [1..#Gens3] | not (i in index)];
   else
      go_elements := [];
   end if;

   // case 4 
   // Section 5.2.6 of monograph 
   // Step 2 of construction of unipotent radical R 
   Gens := []; 
   PP := {};
   for rank in Set (V) do 
      // all V(rank) and V_alpha (rank) 
      total := FindIndices (N, "V", rank);
      // all V_alpha (rank) 
      J := FindIndices (N, "V", rank: Alpha := true);
      // all V(rank) 
      I := [x : x in total | not (x in J)];
      J := total;
      if #I gt 0 and #J gt 0 then 
         for i in [1..#I] do
            for j in [1..#J] do
               if I[i] eq J[j] then continue j; end if;
               if {I[i], J[j]} in PP then continue; end if;
               Include (~PP, {I[i], J[j]});
               Gens cat:= Case4 (d, q, I[i], J[j], form);
            end for;
         end for;
      end if;
   end for;
   Gens := [GL(d, q) ! x: x in Gens];
   // "Case 4: Number of gens is ", #Gens;
   u := phi (r);
   A := [v @ tau where _, v := IsConjugate (P, u, phi (r^l)): l in Gens];
   Gens4 := [Gens[i] * A[i]^-1: i in [1..#Gens]];

   // Case 5 = case 4'' in Martin's notes 
   // Section 5.2.6 of monograph 
   // Step 3 of construction of unipotent radical R 
   W_list := {w : w in W | IsEven (w)};
   Gens := [];
   for rank in W_list do 
      if not (rank div 2 in V cat V_alpha) then continue; end if;

      A_total := FindIndices (N, "W", rank);
      // all W_alpha (rank)
      A_alpha := FindIndices (N, "W", rank: Alpha := true);
      // all W(rank)
      A := [x : x in A_total | not (x in A_alpha)];

      B_total := FindIndices (N, "V", rank div 2);
      Sort (~B_total);
      // all V_alpha (rank)
      B_alpha := FindIndices (N, "V", rank div 2: Alpha := true);
      // all V(rank)
      B := [x : x in B_total | not (x in B_alpha)];
      Sort (~B);

      PP := {};
      for a in A do 
         for b in B do 
            for c in B_total do 
               if c eq b then continue; end if;
               if {b, c} in PP then continue; end if;
               Include (~PP, {b,c});
               index := a cat b cat c;
               Sort (~index);
               Wm := [i: i in index | N[i][1] eq "w" and  N[i][2] lt 0];
               wm1 := Position (index, Wm[#Wm]);
               Wp := [i: i in index | N[i][1] eq "w" and  N[i][2] gt 0];
               w1 := Position (index, Wp[1]);
               Vm := [i: i in index | N[i][1] eq "v" and  N[i][2] lt 0];
               vm1_dash := Vm[#Vm];
               beta := form[vm1_dash, vm1_dash]; 
               m := Case5 (#a + #b + #c, q, beta, wm1, w1);
               M := Identity (MA);
               M := MyInsert (M, m, index, index);
               Append (~Gens, M);
            end for;
         end for;
      end for;
   end for;
   Gens := [GL(d, q) ! x: x in Gens];
   // "Case 5: Number of gens is ", #Gens;
   u := phi (r);
   A := [v @ tau where _, v := IsConjugate (P, u, phi (r^l)): l in Gens];
   Gens5 := [Gens[i] * A[i]^-1: i in [1..#Gens]];

   // case 6 
   // Section 5.2.5 of monograph 
   V_list := V cat V_alpha;
   V_list := Set (V_list);
   V_list := [x : x in V_list];
   Sort (~V_list);
   gens := [];
   for i in [1..#V_list] do 
      rank := V_list[i]; 
      I := FindIndices (N, "V", rank);
      for j in [1..#I] do 
         u1 := ExtractBlock (r, I[j], I[j]);
         g := Identity (MA);
         u := MyInsert (g, u1, I[j], I[j]);
         Append (~gens, u);
       end for;
   end for;
   if OmegaOnly eq false then 
      Gens6 := gens;
   else 
      gens cat:= go_elements;
      Gens6 := &cat[[gens[i] * gens[j]^-1: j in [i + 1..#gens]]: i in [1..#gens]];
   end if;
   Gens6 := [GL(d, q) ! g: g in Gens6];
   // "Case 6: Number of gens is ", #Gens6;

   H := sub<GL(d, q) | Gens1, Gens2, Gens3, Gens4, Gens5, Gens6>;
   assert IsCentral (H, r);

   return H;
end function;

GO_ClassRep_Even := function (rep, form, m, T, q) 
   // "GO even characteristic: label function";

   for i in [1..#m] do
      if IsOdd (m[i][1]) and IsOdd (m[i][2]) then 
         "Bad Jordan form description"; 
         return false, _, _; 
      end if;
   end for;
   d := &+[m[i][1] * m[i][2] : i in [1..#m]];
   W := T[1]; V := T[2]; W_alpha := T[3]; V_alpha := T[4];
   
   R := []; N := [];
   for i in [1..4] do
      if #T[i] gt 0 then 
         A := T[i]; 
         if i in {1, 3} then 
            for k in [1..#A] do 
               r := A[k];
               offset := #[x : x in [A[j]: j in [1..k - 1]] | x eq r];
               if i eq 3 then 
                   offset +:= #[x : x in [T[1][j]: j in [1..#T[1]]] | x eq r];
               end if;
               alpha := i eq 3 select true else false;
               L := [-(r - 1) .. (r - 1) by 2];
               Append (~R, L cat L); 
               Append (~N, [<"w", L[i], r, offset + 1, alpha>: i in [1..#L]] cat 
                           [<"x", L[i], r, offset + 1, alpha>: i in [1..#L]]);
            end for;
         else
            for k in [1..#A] do 
               r := 2 * A[k];
               offset := #[x : x in [A[j]: j in [1..k - 1]] | x eq r div 2];
               if i eq 4 then 
                  offset +:= #[x : x in [T[2][j]: j in [1..#T[2]]] | x eq r div 2];
               end if;
               alpha := i eq 4 select true else false;
               L := [-(r - 1) .. (r - 1) by 2];
               Append (~R, L); 
               Append (~N, [<"v", L[i], r div 2, offset + 1, alpha>: i in [1..#L]]);
            end for;
         end if;
      end if;
   end for;
       
   W := Set (&cat (R));
   W := [x : x in W];
   Sort (~W);

   L := &cat (R);
   N := &cat (N);
   pos := &cat[[i : i in [1..#L] | L[i] eq c]: c in W];
   
   S := Sym (d);
   P := PermutationMatrix (GF(q), S!pos);
   N := [N[i]: i in pos];

   M := [];
   for i in [1..#N] do 
      r := N[i][1] in {"v"} select 2 * N[i][3] else N[i][3];
      M[i] := N[i][1] cat IntegerToString (r);
   end for;

   Wt := [<w, #[x : x in L | x eq w]>: w in W];
   return P * rep * P^-1, P * form * Transpose (P), P, M, Wt, N;
end function;

GO_ConvertToSpecialRep_Even := function (g, form, T)
   d := Nrows (g);
   q := #BaseRing (g);
   J, CB, b := JordanForm (g);
   s := [b[i][2]: i in [1..#b]];
   m := [<x, #[y: y in s | y eq x]>: x in Set (s)];
   r, form, CB, m, Wt, N := GO_ClassRep_Even (g, form, m, T, q);
   r := GL(d, q) ! r;
   CB := GL(d, q) ! CB;
   return r, form, CB, m, Wt, N;
end function;

TweakRep := function (d, q, r, f, T, L)
   W := T[1]; V := T[2]; W_alpha := T[3]; V_alpha := T[4];
   MA := MatrixAlgebra (GF (q), d);
   CB := Identity (MA);
   for dim in W_alpha do  
      I_all := FindIndices (L, "W", dim: Alpha := true); 
      I_all := [I: I in I_all | #I gt 2];
      for I in I_all do 
         flag := exists(wm2){i : i in I | L[i][1] eq "w" and L[i][2] eq -2};
         flag :=  exists(w0){i : i in I | L[i][1] eq "w" and L[i][2] eq 0};
         flag :=  exists(x0){i : i in I | L[i][1] eq "x" and L[i][2] eq 0};
         flag :=  exists(x2){i : i in I | L[i][1] eq "x" and L[i][2] eq 2};
         CB[wm2, w0] := 1;
         CB[x0, x2] := 1;
       end for;
   end for;
   CB := GL(d, q) ! CB;
   return CB * r * CB^-1, CB * f * Transpose (CB), CB;
end function;

// matrix to conjugate W to W_dash 
Translate_W_to_Wdash := function (k, d, q)
   assert d ge 2 * k;

   MB := MatrixAlgebra (GF(q), 2 * k);
   B := Identity (MB);
   B[k, k+1] := 1; B[k,k] := 0;
   B[k+1, k] := 1; B[k+1,k+1] := 0;

   MA := MatrixAlgebra (GF(q), d);
   A := Zero (MA);
   InsertBlock (~A, B, 1, 1);
   for i in [2*k + 1..d] do A[i,i] := 1; end for;
   return GL(d, q)!A;
end function;

// return centraliser of special rep r of g in GO or Omega based on type 
// g must be in Omega, not in GO
// T parameter list for g = class rep from paper, NOT a conjugate of it 

OrthogonalUnipotentCentraliserRep := function (G, g, f, T, type: 
   Verify := false, OrderOnly := false);

   d := Degree (G); q := #BaseRing (G);

   OmegaOnly := type in {"Omega+", "Omega-"}; 

   order := OrthogonalUnipotentCentraliserOrder_Even (type, T, q);
   if OrderOnly then return order, _, _; end if;

   if IsIdentity (g) then return G, g, f, g^0; end if;

   // split class in Omega+: replace rep by +1 version 
   if type eq "Omega+" and T[#T] eq -1 then 
      // change W_alpha rep to W rep
      t := Translate_W_to_Wdash (T[1][1], d, q);
      g := g^t;
   else
      t := g^0;
   end if;
   
   r, form, CB1, m, Wt, N := GO_ConvertToSpecialRep_Even (g, f, T);

   Q_values := [form[i,i]: i in [1..Nrows (form)]];
   U := GO_QSubgroup_Even (Wt, q, m, Q_values);
   // check U is contained in Omega 
   assert forall{i: i in [1..Ngens (U)] | SpinorNorm (U.i, form) eq 0};
   assert IsUnipotent (U);
   Q := UnipotentMatrixGroup (U);
   P, phi, tau := PCPresentation (Q);

   r, form, CB2 := TweakRep (d, q, r, form, T, N);
   // assert phi (r) in P;
   CP := Centraliser (P, phi (r));
   C := CP @ tau;
   assert IsCentral (C, r);

   // "Unipotent radical of centraliser has factored order ", FactoredOrder (C);

   qdim := GO_CentraliserDimension_Even (Wt);
   assert Ilog (2, q) * qdim ge NPCgens (P); 
   // "qdim is ", qdim;

   Add := GO_SSGenerators_Even (r, P, phi, tau, N, m, form, T, q: OmegaOnly := OmegaOnly);

   C := sub<GL(d, q) | C, Add>;
   assert IsCentral (C, r);
   // "Ngens for centraliser:", Ngens (C), Ngens (Add);

   if Verify then 
      "Centraliser order is ", order;
      assert LMGOrder (C) eq order;
   else 
      O := Factorisation (order);
      C`FactoredOrder := O;
      C`Order := order;
   end if;

   CB := CB2 * CB1 * t^-1;
   return C, r, form, CB;
end function;

OrthogonalUnipotentCentraliser_Even := function (G, g, form, type)
   q := #BaseRing (G);
   label := SpO_EvenLabel (g, form: Orthogonal := true);
   T := WeightsToLabel (label);
   rep, form_rep := SetupRep ("O", q, T[1], T[2], T[3], T[4], T[5]);
   V := QuadraticSpace (form_rep);
   I := IsometryGroup (V);
   C, r, f, CB := OrthogonalUnipotentCentraliserRep (I, rep, form_rep, T, type);
   return C, r, f, CB;
end function;

// centraliser of g in GO or Omega -- note g must be in Omega 
MyOrthogonalCentraliser_Even := function (S, g, form, type)
   V := QuadraticSpace (form);
   P := IsometryGroup (V);
   G, r, f, CB := OrthogonalUnipotentCentraliser_Even (P, g, form, type);

   if forall{x: x in Generators (S) | DicksonInvariant (V, x) eq 0} then
      C := AbelianGroup ([2]);
      V := QuadraticSpace (f);
      phi := hom <Generic (G) -> C | x :-> DicksonInvariant (V, x)>;
      images := [phi (G.i): i in [1..Ngens (G)]];
      I := sub<C | images>;
      images := [Eltseq (I!x): x in images];
      images := &cat (images);
      order := G`FactoredOrder;
      G := KernelOfHom (G, I, images);
      G`FactoredOrder := order / FactoredOrder (I);
      G`Order := Integers ()!(order / FactoredOrder (I));
   end if;

   return G, r, f, CB;
end function;

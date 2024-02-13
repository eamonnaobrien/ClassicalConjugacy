freeze;

import "../fixed-ss.m": ChangeClassLabel;

// return true if det (StandardSymmetricForm(n,q)) is a square, false otherwise
_is_square := func<n,q | ((q mod 8 in {1,3} and n mod 4 eq 3) or (q mod 8 in {1,7} and n mod 4 eq 1))>;

// if X,L = ClassRepresentativesGO(n,q) then 
// TurnCorrectLabel(toNameEven(L[i])) = IsometryGroupClassLabel("GO",X[i]) for every i in [1..#X]

// how it works: it switches the unipotent labels of the (t+1)- and (t-1)-eigenspaces with ChangeClassLabel
// the one in odd dim is switched whenever its discriminant is not a square
// the one in even dim is switched whenever the global discriminant (before the correction above) 
// is not the same as the discriminant of the standard Magma form
TurnCorrectLabel := function (L, n, F)

   DetForm := 1;    // 1 if square, -1 otherwise
   q := #F;
   pr := PrimitiveElement (F);
   ThereIsEven := false;

   for l in L do
      case l[1]:
         when 0:
            discr := GF(q)!1;
            dim := 0;
            for x in l[3] do
               if x[2] ne 0 then 
                  discr *:= 2*x[2]*(-1)^((x[1]-1) div 2);
               end if;
               dim +:= x[1];
            end for;
            if IsOdd(dim) then
               if not IsSquare(discr) then
                  DetForm *:= -1;
                  Exclude (~L, l);
                  Include (~L, < l[1], l[2], ChangeClassLabel (l[3], F, pr) >) ;
               end if;
            else
               ThereIsEven := true;
               if not IsSquare(discr) then DetForm *:= -1; end if;
               EvenLabelToChange := l;
            end if;
         when 1:
            if q mod 4 eq 3 and Degree(l[2]) mod 4 eq 2 and IsOdd(&+[y[1]: y in l[3]]) then
               DetForm *:= -1;
            end if;
         when 2:
            if q mod 4 eq 1 then 
               if IsOdd(&+[y[1]: y in l[3]]) then DetForm *:= -1; end if;
            else
               if IsOdd(&+[y[1]: y in l[3]]) and Degree(l[2]) mod 4 eq 0 then DetForm *:= -1; end if;
            end if;
      end case;
   end for;

   if ThereIsEven and (_is_square(n,q) xor DetForm eq 1) then
      Exclude (~L, EvenLabelToChange);
      Include (~L, < EvenLabelToChange[1], EvenLabelToChange[2], ChangeClassLabel (EvenLabelToChange[3], F, pr) >) ;
   end if;

   return L;
end function;

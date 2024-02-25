freeze;

import "linear/GLCentralizerOrder.m": SLCentralizerOrder, GLCentralizerOrder; 
import "unipotent/Centraliser-Order.m": UnipotentCentraliserOrder;
import "semisimple/Centralizer/SSCentralizerOrder.m": SSCentralizerOrder;
import "semisimple/form.m": ConjugatePolynomial;
import "unipotent/util.m": MySpinorNorm;
import "CentralizerOrder.m": MyCentraliserOrder;
import "Gen-Label.m": TransformMatrix, StandardGroup;

// code prepared by Eamonn O'Brien and Don Taylor
// builds on RecogniseClassical returning boolean and precise name 

// return quadratic form when G is orthogonal and reducible 
FormsReducibleCase := function (G, type)
   F := BaseRing (G);
   // assert #F gt 2;

   d := Degree (G);
   assert d eq 2;

   if IsEven (#F) then 
      J := InvariantQuadraticForms (G);
      assert #J eq 1;
      return true, J[1];
   end if;

   J := InvariantBilinearForms (G);
   MA := MatrixAlgebra (F, d);
   S := sub<KMatrixSpace (F, d, d) | J>;
   flag := exists (s){s: s in S | Determinant (s) ne 0 and
                      SymmetricBilinearFormType (MA!s) eq type}; 
   if flag then 
      return true, SymmetricToQuadraticForm (MA!s); 
   else 
      return false, _; 
   end if;
end function;

// return "GO+", "SO+", "Omega+" as type for G; same for O- and O
OrthogonalType := function (G)
   type := ClassicalType (G);
   if Type(type) eq BoolElt or 
      type notin {"orthogonalminus", "orthogonalplus", "orthogonalcircle"} then
      return false, _;
   end if;

   vprint Classical, 2 : "+entering OrthogonalType";
   d := Degree (G); 
   F := BaseRing (G);
   q := #F;
   if IsIrreducible (G) then 
      preserves_form, form := QuadraticForm (G);
   else
      preserves_form, form := FormsReducibleCase (G, type);
   end if;
   if preserves_form then
      if IsOdd(q) then
         J := form + Transpose(form);
         V := VectorSpace(GF(2),2);
         X := sub< V | [DicksonInvariant(g)*V.1 + SpinorNorm(g,J)*V.2 : 
                 g in Generators(G) ] >;
         m := #X;
         if not assigned G`FactoredOrder then
            ord := case< type | "orthogonalplus"  : FactoredOrder(OmegaPlus(d,q)),
                                "orthogonalminus" : FactoredOrder(OmegaMinus(d,q)),
                                          default : FactoredOrder(Omega(d,q)) >;
            G`FactoredOrder := ord * Factorisation(m);
         end if;
         if m eq 4 then
            type := case< type | "orthogonalplus" : "GO+", "orthogonalminus" : "GO-",
                       default : "GO" >;
         elif m eq 1 then
            type := case< type | "orthogonalplus" : "Omega+", "orthogonalminus" : "Omega-",
                       default : "Omega" >;
         else
            if forall{g : g in Generators(G) | DicksonInvariant(g) eq 0} then
               type := case< type | "orthogonalplus" : "SO+", "orthogonalminus" : "SO-",
                       default : "SO" >;
            else
               type := case< type | "orthogonalplus" : "ExtOmega+", "orthogonalminus" : "ExtOmega-",
                       default : "ExtOmega" >;
            end if;
         end if;
      else // characteristic 2.  GO == SO.  If d is odd, GO == SO == Omega
         J := form;
         if IsOdd(d) then // this will never happen (trapped by ClassicalType)
            type := "GO";
            if not assigned G`FactoredOrder then G`FactoredOrder := FactoredOrder(GO(d,q)); end if;
         elif forall{g : g in Generators(G) | DicksonInvariant(g) eq 0} then
            if not assigned G`FactoredOrder then 
               G`FactoredOrder := case< type | "orthogonalplus"  : FactoredOrder(OmegaPlus(d,q)),
                                       "orthogonalminus" : FactoredOrder(OmegaMinus(d,q)),
                                        default : FactoredOrder(Omega(d,q)) >;
            end if;
            type := case< type | "orthogonalplus" : "Omega+", "orthogonalminus" : "Omega-",
                       default : "" >;
         else
            if not assigned G`FactoredOrder then 
               G`FactoredOrder := case< type | "orthogonalplus"  : FactoredOrder(GOPlus(d,q)),
                                       "orthogonalminus" : FactoredOrder(GOMinus(d,q)),
                                        default : FactoredOrder(GO(d,q)) >;
            end if;
            type := case< type | "orthogonalplus" : "GO+", "orthogonalminus" : "GO-",
                       default : "" >;
         end if;
      end if;
   else
      qforms := SemiInvariantQuadraticForms(G);
      if IsEmpty(qforms) then return false, _; end if;
      form := qforms[1,2,1];
      factors := qforms[1,1];
      if IsOdd(d) and IsEven(q) then // this will never happen (trapped by ClassicalType)
        U, phi := UnitGroup(F);
        X := sub< U | [ factors[i]@@phi : i in [1..Ngens(G)]] >;
        type := (#X eq q - 1) select "CGO" else "ExtOmega";
      else
        J := IsEven(q) select form else form + Transpose(form);
        if assigned G`ClassicalName and G`ClassicalName in 
           ["ConformalOrthogonal","ConformalOrthogonalPlus","ConformalOrthogonalMinus"] then
           type := case < G`ClassicalName |
             "ConformalOrthogonalPlus" : "CGO+",
             "ConformalOrthogonalMinus" : "CGO-",
             default : "CGO" >;
        else
           ord := case< type | "orthogonalplus" : OrderCGOPlus(d,q),
                               "orthogonalminus" : OrderCGOMinus(d,q),
                               default : OrderCGO(d,q) >;
           gord := assigned G`Order select G`Order else LMGOrder(G);
           type := (ord eq gord) select 
              case< type | "orthogonalplus" : "CGO+", "orthogonalminus" : "CGO-",
                      default : "CGO" >
              else
              case< type | "orthogonalplus" : "ExtOmega+", "orthogonalminus" : "ExtOmega-",
                      default : "ExtOmega" >;
        end if;
      end if;
   end if;

   return type, J;
end function;

// return type GL / SL / GU / SU / Sp / GO+ / SO+ / Omega+ / ... for G
GroupType := function (G) 

   if assigned G`ClassicalType then 
      return true, G`ClassicalType;
   end if;

   d := Degree (G); F := BaseRing (G); q := #F;
   if d eq 1 then
      if not IsSquare (q) then return true, "GL"; end if;
      flag := UnitaryForm (G);
      if flag then return true, "GU"; else return true, "GL"; end if;
   end if;

   if d le 8 and q le 9 then Limit := 4; else Limit := 2; end if;
   nmr := 0;
   repeat
      flag := RecognizeClassical (G : NumberOfElements := 30);
      nmr +:= 1;
   until flag or nmr ge Limit;
   if not flag then
      vprint Classical : "Input group appears not to be classical";
      return false, _;
   end if;

   type := ClassicalType (G);
   if type in {"orthogonalminus", "orthogonalplus", "orthogonalcircle"} then
      type := OrthogonalType (G);
      if Type(type) eq BoolElt then return false,_; end if; 
   elif d eq 2 and type eq "linear" and SymplecticForm (G) then  
      if not assigned G`FactoredOrder then G`FactoredOrder := FactoredOrder(Sp(d,q)); end if;
      type := "Sp";
   elif type eq "unitary" then // G contains SU
      ok, q0 := IsSquare(q); assert ok;
      if UnitaryForm(G) then // GU contains G
         m := LCM([Order(Determinant(g)) : g in Generators(G)]);
         if not assigned G`FactoredOrder then
            G`FactoredOrder := FactoredOrder(SU(d,q0)) * Factorisation(m);
         end if;
         type := case< m | 1 : "SU", q0 + 1 : "GU", default : "ExtSU" >;
      else
         flag, form, factors := UnitaryForm(G : Scalars); assert flag;
         F0 := Universe(factors);
         U, phi := UnitGroup(F);
         U0, psi := UnitGroup(F0);
         D, p1, p2 := DirectSum(U0,U);
         X := sub< D | [ p1(factors[i]@@psi) + p2(Determinant(G.i)@@phi) : 
                       i in [1..Ngens(G)] ] >;
         m := #X;
         if not assigned G`FactoredOrder then
            G`FactoredOrder := FactoredOrder(SU(d,q0)) * Factorisation(m);
         end if;
         type := case< m | q - 1 : "CGU", GCD(d,q0 - 1) : "CSU", default : "AltSU" >;
      end if;
   elif type eq "symplectic" then
      if SymplecticForm(G) then
         if not assigned G`FactoredOrder then G`FactoredOrder := FactoredOrder(Sp(d,q)); end if;
         type := "Sp";
      else
         flag, form, factors := SymplecticForm(G : Scalars); assert flag;
         m := LCM([Order(f) : f in factors]);
         if not assigned G`FactoredOrder then
            G`FactoredOrder := FactoredOrder(Sp(d,q)) * Factorisation(m);
         end if;
         type := (m eq q - 1) select "CSp" else "ExtSp";
      end if;
   elif type eq "linear" then
      m := LCM([Order(Determinant(g)) : g in Generators(G)]);
      if not assigned G`FactoredOrder then
         G`FactoredOrder := FactoredOrder(SL(d,q)) * Factorisation(m);
      end if;
      type := case< m | 1 : "SL", q - 1 : "GL", default : "ExtSL" >;
   end if;

   G`ClassicalType := type;
   return true, type;
end function;

RecogniseGOEven := function (G)
   d := Degree (G); F := BaseRing (G); q := #F;
   p := Characteristic (F);

   // difficult cases 
   if q eq 2 then 
      if d eq 3 then
	  BSGS(G);
	  if #G eq 6 and IdentifyGroup (G) cmpeq <6, 1> then
	      G`ClassicalType := "GO"; 
	      return true, "GO"; 
          end if;
      end if;
      if d eq 5 then
	  BSGS(G);
	  if #G eq 720 and IdentifyGroup (G) cmpeq <720, 763> then
	      G`ClassicalType := "GO"; 
	      return true, "GO"; 
	  end if;
      end if;
   end if;
     
   // check that G is isomorphic to Sp(d - 1, q)
   flag, type := LieType (G, p);
   if d eq 3 then 
      if not (flag and type eq <"A", d div 2, q>) then 
         return false, _;
      end if;
   else 
      if not (flag and type eq <"C", d div 2, q>) then 
         return false, _;
      end if;
   end if;
   forms := InvariantQuadraticForms(G);
   if not IsEmpty(forms) then
      tp := "GO";
      if not assigned G`FactoredOrder then G`FactoredOrder := FactoredOrder(GO(d,q)); end if;
   else
      // quick check if G is standard
      Q := StandardQuadraticForm(d,q);
      if forall{ g : g in Generators(G) | IsQuadFormSimilarity(Q,g) } then
         factors := [];
         for i := 1 to Ngens(G) do
            g := G.i;
            Q_ := EnsureUpperTriangular(g*Q*Transpose(g));
            assert exists(j,k){ <j,k> : j in [1..k], k in [1..d] | Q[j,k] ne 0 };
            Append(~factors, Q_[j,k] / Q[j,k] );
         end for;
      else
         qforms := SemiInvariantQuadraticForms(G);
         if IsEmpty(qforms) then return false, _; end if;
         factors := qforms[1,1];
      end if;
      U, phi := UnitGroup(F);
      X := sub< U | [ factors[i]@@phi : i in [1..Ngens(G)]] >;
      m := #X;
      if not assigned G`FactoredOrder then
         G`FactoredOrder := FactoredOrder(GO(d,q)) * Factorisation(m);
      end if;
      tp := (m eq q - 1) select "CGO" else "ExtOmega";
   end if;
   G`ClassicalType := tp; 
   return true, tp;
end function;

intrinsic ClassicalGroupType (G :: GrpMat[FldFin]) -> BoolElt, MonStgElt
{if G is identified as a classical group in its natural representation,
 then return true and classical type of group}

   vprint Classical, 2 : "+entering ClassicalGroupType";
   if assigned G`ClassicalType then return true, G`ClassicalType; end if;
   if IsTrivial (G) then 
     vprint Classical : "Group is trivial -- cannot decide type"; 
     return false, _; 
   end if;

   d := Degree (G); 
   F := BaseRing(G);
   q := #F;
   if d le 3 and q le 4 then BSGS(G); end if;

   if d eq 2 and q le 4 then 
      type := ClassicalType (G);
      if type cmpeq false then 
        vprint Classical: "Group appears not to be classical";
        return false, _;
      end if;
      gord := #G;
      if gord eq 2 then
         if q eq 2 and type eq "orthogonalplus" then 
            G`ClassicalType := "SO+"; return true, "SO+"; 
         elif q eq 3 and type eq "orthogonalminus" then
            G`ClassicalType := "Omega-"; return true, "Omega-"; 
         end if;
      elif gord eq 3 then 
         if q eq 2 and type eq "orthogonalminus" then 
            G`ClassicalType := "Omega-"; return true, "Omega-";
         elif q eq 4 and type eq "orthogonalplus" then 
            G`ClassicalType := "Omega+"; return true, "Omega+";
         end if;
      elif gord eq 4 then
         if q eq 3 and type eq "orthogonalminus" and IdentifyGroup (G) cmpeq <4, 1> then 
            G`ClassicalType := "SO-"; return true, "SO-";
         elif q eq 3 and type eq "orthogonalplus" and IdentifyGroup (G) cmpeq <4, 2> then 
            G`ClassicalType := "GO+"; return true, "GO+";
         end if;
      elif gord eq 5 then // q must be 4, only one class of subgroups of order 5
         G`ClassicalType := "Omega-"; return true, "Omega-"; 
      elif gord eq 6 then
         if q eq 2 then
            G`ClassicalType := "GL"; return true, "GL"; 
         elif q eq 4 then
            if G eq GOPlus (2, 4) then
               G`ClassicalType := "GO+";
               return true, "GO+"; 
            elif G eq SU(2, 2) then
               G`ClassicalType := "SU";
               return true, "SU";
            else
               vprint Classical: "Cannot decide type";
               return false, _; 
            end if;
         end if;
      elif gord eq 8 then // q must be 3, three classes of subgroups of order 8
         if type eq "orthogonalminus" then
            G`ClassicalType := "GO-"; return true, "GO-"; 
         end if;
      elif gord eq 10 then // q must be 4, only one class of subgroups of order 10
         G`ClassicalType := "GO-"; return true, "GO-"; 
      elif q eq 4 and IsIrreducible (G) and IdentifyGroup (G) cmpeq <18, 3> then 
         G`ClassicalType := "GU"; return true, "GU"; 
      elif gord eq 24 then // q must be 3
         G`ClassicalType := "SL"; return true, "SL"; 
      elif q in {3, 4} and IsIrreducible (G) and IdentifyGroup (G) in {<48, 29>, <180, 19>} 
         and type eq "linear" then 
            G`ClassicalType := "GL"; return true, "GL"; 
      end if;
      vprint Classical: "Cannot decide type";
      return false, _;
   end if;

   // recognise GO(2n + 1, 2^k) 
   if IsOdd (d) and IsEven (q) and not IsIrreducible (G) then 
      flag, type := RecogniseGOEven (G); 
   else 
      flag, type := GroupType (G);
   end if;
   if flag then 
      G`ClassicalType := type; return true, type; 
   else 
      vprint Classical: "Cannot decide type"; 
      return false, _; 
   end if;
end intrinsic;

// G conjugate of natural copy of classical group
// decide if x is in G

MyIsIn := function (G, x: Add := {})

   if IsTrivial (G) then return x in G; end if;
   d := Degree (G); q := #BaseRing (G);
   if d eq 2 and q le 4 then return x in G; end if;
   if d eq 2 and not IsIrreducible (G) then return x in G; end if;

   flag, type := ClassicalGroupType (G); 

   ValidTypes := {"Sp", "SU", "GU", "Omega+", "Omega-", "Omega", 
                  "O+", "O-", "O", "SO+", "SO-", "SO", "GO+", "GO-", "GO"};
   if (not flag) or (flag and type notin ValidTypes join Add) then 
      error "Type of input group must be one of ", ValidTypes;
   end if;

   if IsOdd (d) and IsEven (q) and type eq  "GO" then 
      error "Function does not apply to this case";
   end if;

   if type eq "GL" then
      return Determinant (x) ne 0;
   elif type eq "SL" then
      return Determinant (x) eq 1;
   end if;
   CB := TransformMatrix (G);
   q0 := type in {"SU", "GU"} select Isqrt (q) else q;
   H := StandardGroup (type, d, q0);
   return x^CB in H;
end function;

// we are not able to write down centralisers for elements outside 
// of Omega in even char
IsApplicable := function (G, g, type)
   if type notin {"SO+", "SO-", "SO", "GO+", "GO-", "GO"} then return true; end if;
   if IsOdd (#BaseRing (G)) then return true; end if;
   flag, form, type := QuadraticForm (G);
   V := QuadraticSpace (form);
   return DicksonInvariant (V, g) eq 0;
end function;

// size of conjugacy class of g in GU or SU 
UnitaryClassSize := function (g, special) 
   c := Factorization (1);
   _, _, b := JordanForm (g);
   _, q := IsSquare (#BaseRing (g));
   ConjPol := ConjugatePolynomial (true);

   JF := [];
   SPoly1 := {x[1]: x in b};
   SPoly := {};
   for f in SPoly1 do
      if f eq ConjPol (f) then
         Include (~SPoly, f);
      else
         if ConjPol (f) notin SPoly then
            Include (~SPoly, f);
         end if;
      end if;
   end for;
   gcd := 0;
   for f in SPoly do
      JF := {* x[2]: x in b | x[1] eq f *};
      // the values passed to UnipotentCentraliserOrder are not important, except for JF
      if f eq ConjPol (f) then
         G1 := GU(2, q^Degree(f));
         X := Identity (G1);
         c *:= UnipotentCentraliserOrder ("GU", G1, X, X: JF := MultisetToSequence (JF));
      else
         G1 := GL(2, q^(2*Degree(f)));
         X := Identity (G1);
         c *:= UnipotentCentraliserOrder ("GL", G1, X, X: JF := MultisetToSequence (JF));
      end if;
      gcd := Gcd (gcd, Gcd (JF));
   end for;
   if special then
      gcd := Gcd (gcd, q+1);
      c *:= Factorization (gcd);
      c /:= Factorization (q+1);
      end if;
   return c;
end function;

intrinsic ClassicalClassSize (G:: GrpMat, g:: GrpMatElt) -> RngIntElt
{Size of conjugacy class of g in classical group G}

   require Generic (Parent (g)) cmpeq Generic (G): "Input element is not in group";
   require MyIsIn (G, g: Add := {"GL", "SL"}): "Input element is not in group";
 
   if IsCentral (G, g) then return 1; end if;

   d := Degree (G); q := #BaseRing (G); 
   if d eq 2 and q le 4 then return #Class (G, g); end if;

   flag, type := ClassicalGroupType (G);
   ValidTypes := {"SL", "GL", "Sp", "SU", "GU", "Omega+", "Omega-", "Omega",
                  "SO+", "SO-", "SO", "GO+", "GO-", "GO"};
   require flag and type in ValidTypes: "Type of group must be one of ", ValidTypes;

   if type eq "GO" and IsOdd (d) and IsEven (q) then
      error "Function does not apply to this case";
   end if;

   CB := TransformMatrix (G);

   if type cmpeq "SL" then 
      c := SLCentralizerOrder (G, g);
   elif type cmpeq "GL" then 
      c := GLCentralizerOrder (G, g);
   elif type in {"GU", "SU"} then 
      c := UnitaryClassSize (g^CB, type cmpeq "SU");
   elif IsSemisimple (g) then 
      // Gr := G^CB; Gr`ClassicalType := G`ClassicalType;
      // unitary case considered above so q is correct 
      Gr := StandardGroup (type, d, q); Gr`ClassicalType := G`ClassicalType;
      c := SSCentralizerOrder (Gr, g^CB);
   elif IsUnipotent (g) and type eq "Sp" then 
      _, form := SymplecticForm (G);
      c := UnipotentCentraliserOrder ("Sp", G, g, form);
   elif IsUnipotent (g) and IsApplicable (G, g, type) then 
      type, form := OrthogonalType (G);
      c := UnipotentCentraliserOrder (type, G, g, form);
   else
      c := MyCentraliserOrder (type, g^CB);
   end if;
   return Integers () ! (FactoredOrder (G) / c);
end intrinsic;

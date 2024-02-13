AddAttribute(GrpMat,"SpinHom"); AddAttribute(GrpMat,"SpinInvHom");
AddAttribute(GrpMat,"SpinHomImage"); AddAttribute(GrpMat,"SpinCentre");
AddAttribute(GrpMat,"SpinLifts");
forward CheckTauAndPhi; forward SanityChecks;

intrinsic SpinClasses(G :: GrpMat) -> SeqEnum, SeqEnum
{Conjugacy classes of spin group G}

    if HasAttribute(G, "Classes") then
      cl  := Classes(G);
      return cl, [ClassCentralizer(G,i) : i in [1..#cl]];
    end if;

    havehoms := assigned G`SpinHom and assigned G`SpinInvHom and
                assigned G`SpinHomImage and assigned G`SpinCentre;
    if havehoms then
      tau := G`SpinHom; phi := G`SpinInvHom;
      H := G`SpinHomImage; ZG := G`SpinCentre;
    else
      T := CompositionTree (G);
      vprint Classes, 1: "Got composition tree";
      S, a, b := CompositionTreeSeries (G);
      phi := b[#b];
      tau := a[#a];
      ZG := LMGCentre (G);
      H := Codomain(tau);
      TH := CompositionTree(H);
      ZH := LMGCentre(H);
      SanityChecks(G,H,ZG,ZH);

      if #ZH gt 1 then
        CheckTauAndPhi(G,H,ZG,ZH,~tau,~phi);
      end if;
      G`SpinHom := tau; G`SpinInvHom := phi;
      G`SpinHomImage := H; G`SpinCentre := ZG;
    end if; //if havehoms

    repeat 
       z := Random (ZG);
    until z ne G.0 and Function(tau)(z) eq H.0;

    ccH := ConjugacyClasses(H);

    reps := [];

    HClassCt:=0;
    vprint Classes, 1: #ccH,"classes of orthogonal group to lift";
    invlifts := [];
    for c in ccH do
        HClassCt+:=1;
        vprint Classes, 2: "  lifting class number",HClassCt;
        C := Centralizer (H, c[3]);
        cG := Function (phi)(c[3]);
        splits := true;
        centralizerGens := [];
        for x in Generators (C) do
            xG := Function (phi)(x);
            if (cG, xG) ne G.0 then
                if splits then
                   sG := xG;
                   centralizerGens cat:= [sG*cg*sG^-1 : cg in centralizerGens];
                   splits := false;
                else Append (~centralizerGens, xG*sG^-1);
                end if;
                Append (~centralizerGens, xG^2);
            else
                Append (~centralizerGens, xG);
                if not splits then
                   Append (~centralizerGens, sG*xG*sG^-1);
                end if;
            end if;
        end for;
        vprint Classes, 2: "Does this class split?", splits;

        cent := sub<Generic (G) | ZG, centralizerGens>;
        if splits then
           centord := 2*#C;
           Append (~reps, <cG, c[2], cent, HClassCt>);
           Append(~reps, <z*cG, c[2], cent, HClassCt>);
        else
           centord := #C;
           Append(~reps, <cG, 2*c[2], cent, HClassCt>);
        end if;
        cent`Order := centord;
    end for;

    vprint Classes, 1: "Group has", #reps, "classes";
    R := [<Order (r[1]), r[2], r[1], r[3], r[4]>: r in reps];
    S:= [[R[i][1], R[i][2]]: i in [1..#R]];
    ParallelSort (~S, ~R);
    classes := [<r[1],r[2],r[3]> : r in R];
    cents := [r[4] : r in R];
    G`SpinLifts := [ [ i : i in [1..#classes] | R[i][5] eq hno] :
                       hno in [1..#ccH] ];
    G`Classes := <classes, cents>;
    return classes, cents;
end intrinsic;

intrinsic SpinConjugacyClasses(G :: GrpMat) -> SeqEnum, SeqEnum
{Conjugacy classes of spin group G}
   return SpinClasses(G);
end intrinsic;

intrinsic SpinIsConjugate(G :: GrpMat, g :: GrpMatElt, h :: GrpMatElt) ->
                                  BoolElt, GrpMatElt
{Are elements g,h of spin group G conjugate in G?}
    havehoms := assigned G`SpinHom and assigned G`SpinInvHom and
                assigned G`SpinHomImage;
    if havehoms then
      tau := G`SpinHom; phi := G`SpinInvHom; H := G`SpinHomImage;
    else
      T := CompositionTree (G);
      vprint Classes, 1: "Got composition tree";
      S, a, b := CompositionTreeSeries (G);
      phi := b[#b];
      tau := a[#a];
      ZG := LMGCentre (G);
      H := Codomain(tau);
      TH := CompositionTree(H);
      ZH := LMGCentre(H);
      SanityChecks(G,H,ZG,ZH);
  
      if #ZH gt 1 then
        CheckTauAndPhi(G,H,ZG,ZH,~tau,~phi);
      end if;
      G`SpinHom := tau; G`SpinInvHom := phi;
      G`SpinHomImage := H; G`SpinCentre := ZG;
    end if; //if havehoms

    tau := Function(tau); phi := Function(phi);
    isc, elt := ClassicalIsConjugate(H,tau(g),tau(h));
    if not isc then return false,_; end if;
    celt1 := phi(elt);
    g := g^celt1; //not tau(g) = tau(h)
    CH := Centraliser(H,tau(h));
    //if g and h are conjugate then they are conjugate by generator of CH
    for gen in Generators(CH) do if g^phi(gen) eq h then
      return true, celt1*phi(gen);
    end if; end for;
    return false, _;
end intrinsic;

intrinsic SpinCentraliser(G :: GrpMat, g :: GrpMatElt) -> GrpMat
{Centraliser of element g of spin group G}
    havehoms := assigned G`SpinHom and assigned G`SpinInvHom and
                assigned G`SpinHomImage and assigned G`SpinCentre;
    if havehoms then
      tau := G`SpinHom; phi := G`SpinInvHom;
      H := G`SpinHomImage; ZG := G`SpinCentre;
    else
      T := CompositionTree (G);
      vprint Classes, 1: "Got composition tree";
      S, a, b := CompositionTreeSeries (G);
      phi := b[#b];
      tau := a[#a];
      ZG := LMGCentre (G);
      H := Codomain(tau);
      TH := CompositionTree(H);
      ZH := LMGCentre(H);
      SanityChecks(G,H,ZG,ZH);
  
      if #ZH gt 1 then
        CheckTauAndPhi(G,H,ZG,ZH,~tau,~phi);
      end if;
      G`SpinHom := tau; G`SpinInvHom := phi;
      G`SpinHomImage := H; G`SpinCentre := ZG;
    end if; //if havehoms

    tau := Function(tau); phi := Function(phi);
    CH := Centraliser(H,tau(g));
    centralizerGens := [];
    splits := true;
    for cH in Generators(CH) do
      cG := phi(cH);
      if (cG, g) ne G.0 then
        if splits then
           sG := cG;
           centralizerGens cat:= [sG*cg*sG^-1 : cg in centralizerGens];
           splits := false;
        else Append (~centralizerGens, cG*sG^-1);
        end if;
        Append (~centralizerGens, cG^2);
      else
        Append (~centralizerGens, cG);
        if not splits then
          Append (~centralizerGens, sG*cG*sG^-1);
        end if;
      end if;
    end for;
    vprint Classes, 2: "Does this class split?", splits;
    return sub<Generic (G) | ZG, centralizerGens>;
end intrinsic;

intrinsic SpinCentralizer(G :: GrpMat, g :: GrpMatElt) -> GrpMat
{Centraliser of element g of spin group G}
   return SpinCentraliser(G,g);
end intrinsic;

intrinsic SpinClassMap(G :: GrpMat) -> Map
{The class map of spin group G}
  cl := SpinClasses(G);
  tau := G`SpinHom; phi := G`SpinInvHom;
  H := G`SpinHomImage; ZG := G`SpinCentre; lifts := G`SpinLifts;
  repeat 
    z := Random (ZG);
  until z ne G.0 and Function(tau)(z) eq H.0;
  clH := ClassicalClasses(H); CMH := ClassicalClassMap(H);
  CMfn := function(g)
    h := Function(tau)(g); cnoh := Function(CMH)(h); hrep := clH[cnoh][3];
    isc, elt := ClassicalIsConjugate(H, h, hrep); assert isc;
    g := g^Function(phi)(elt);
    poss := lifts[cnoh];
    for clno in poss do
      if g eq cl[clno][3] then return clno; end if;
    end for;
    assert #poss eq 1 and g*z eq cl[poss[1]][3];
    return poss[1];
  end function;
  
  return map< Generic(G) -> {1..#cl} | x :-> CMfn(x) >; 
end intrinsic;

CheckTauAndPhi := procedure(G,H,ZG,ZH,~tau,~phi)
      //make sure tau is a homomorphism
      vprint Classes,2: "  testing if tau is a homomorphism";
      flag, Grels := CompositionTreeVerify(G); assert flag;
      NG := CompositionTreeNiceGroup(G); ng := Ngens(NG);
      ims := [Function(tau)(NG.i) : i in [1..ng]];
      ishom := Set(Evaluate(Grels,ims)) eq {Id(H)};
      
      if not ishom then
        vprint Classes,2: "tau is not a homomorphism";
        CZH := CartesianPower(ZH,ng);
        for cg in CZH do
          newims := [ims[i]*cg[i] : i in [1..ng]];
          ishom := Set(Evaluate(Grels,newims)) eq {Id(H)};
          if ishom then
            tau := map< Generic(G) -> Generic(H) |
                g :-> Evaluate(w, newims)
                    where _, w := CompositionTreeElementToWord(G,g) >;
            vprint Classes,2: "tau is now a homomorphism";
            break;
          end if;
        end for;
      end if;

      //make sure phi is inverse of tau
      vprint Classes,2: "testing if phi is an inverse of tau";
      isinv := true;
      repeat izh := Random (ZG); until Function(tau)(izh) ne H.0;
      NH := CompositionTreeNiceGroup(H); nh := Ngens(NH);
      invims := [Function(phi)(NH.i) : i in [1..nh]];
      for i in [1..nh] do
        if Function(tau)(invims[i]) ne NH.i then
          vprint Classes,2: "phi is not an inverse of tau";
          isinv := false;
          invims[i] *:= izh;
        end if;
      end for;
      if not isinv then
          phi := map< Generic(H) -> Generic(G) |
              g :-> Evaluate(w, invims)
                    where _, w := CompositionTreeElementToWord(H,g) >;
      end if;
      vprint Classes,2: "phi is now an inverse to tau";
end procedure;

SanityChecks := procedure(G,H,ZG,ZH);
  //basic sanity cheks
      if Dimension(H) lt 7 then
         error "Dimension of spin group must be at least 7";
      end if;
      if IsEven(#BaseRing(H)) then
         error "Characteristic of spin group must be odd";
      end if;
      if not FormType(H) in
         {"orthogonalplus","orthogonalminus","orthogonalcircle"} then
        error "Wrong form type for spin group";
      end if;
      if #G ne #H*2 or #ZG ne #ZH*2 then
        error "This is not a spin group";
      end if;
end procedure;

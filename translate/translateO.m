freeze;

/* 2021-01-14
 * Translation between my conjugacy class names and those of Giovanni
 * for finite orthognal groups
 *
 * Use  tagToNameO(mu)  to convert my name to Giovanni's
 * Use  nameToTagO(nm)  to convert Giovanni's name to mine
 *
 */

import "CorrectLabel.m": TurnCorrectLabel;

// The sign of the unipotent or negative unipotent of type <e,m> in GF(q)
// for orthogonal groups
sgnO := function(e,m,q)
  error if IsEven(e), "e must be odd";
  error if IsEven(q), "q must be odd";
  if m mod 4 eq 0 or q mod 8 eq 1 then return 1; end if;
  case q mod 8:
    when 3:
      val := m mod 4 eq 3 select 1 else -1;
    when 5:
      val := m mod 4 eq 2 select 1 else -1;
    when 7:
      val := m mod 4 eq 1 select 1 else -1;
  end case;
  return val;
end function;

changeSign := function(mu)
  nu := {@ @};
  for polpart in mu do
    f, plist := Explode(polpart);
    newlst := (Degree(f) gt 1) select plist else
      [IsOdd(e*m) select < -e,m > else em : em in plist | true 
        where e,m is Explode(em) ];
    Include(~nu,<f,newlst> );
  end for;
  return nu;
end function;

// The functions invToWittType and theSign have been copied from GOConjugacy.m
// import "GOConjugacy.m" : invToWittType, theSign
invToWittType := function(inv)
  q := #BaseRing(Parent(inv[1,1]));
  qmod4 := q mod 4 eq 1;
  W := AbelianGroup(GrpAb,qmod4 select [2,2] else [4]);
  w := W!0;
  omega := qmod4 select W.1 + W.2 else 2*W.1;
  for pol_part in inv do
    f, lambda := Explode(pol_part);
    if IsIrreducible(f) then
      for mu in lambda do
        e, m := Explode(mu);
        if Degree(f) eq 1 then
          if IsOdd(e) then
            if IsEven(m) then
              if e lt 0 then w +:= omega; end if;
            else
              if e gt 0 then w +:= W.1;
                        else w +:= qmod4 select W.2 else 3*W.1;
              end if;
            end if;
          end if;
        else // Degree(f) greater than 1
          w +:= e*m*omega;
        end if;
      end for;
    end if;
  end for;
  return w;
end function;

theSign := function(inv)
  w := invToWittType(inv);
  W := Parent(w);
  return w in {W!0,W.1} select 1 else -1;
end function;


tagDim := function(mu)
  d := 0;
  for polpart in mu do
    f, lambda := Explode(polpart);
    d_ := 0;
    for em in lambda do
      e, m := Explode(em);
      d_ +:= Abs(e)*m;
    end for;
    d +:= Degree(f)*d_;
  end for;
  return d;
end function;



nmDim := function(nm)
  d := 0;
  for term in nm do
    tp, f, mu := Explode(term);
    labels := [ Append(pp,m) : pp -> m in mu ];
    d_ := 0;
    for eam in labels do
      e,a,m := Explode(eam);
      if tp eq 0 and IsEven(e) then m *:= 2; end if;
      d_ +:= e*m;
    end for;
    d +:= Degree(f)*d_;
  end for;
  return d;
end function;



// The De Franceschi label of a set mu of pairs <f,pi>, where f is a *-irreducible
// polynomial and pi is a (signed) partition for an even dimensional orthogonal 
// group over GF(q), q odd
toNameEven := function(mu)
  name := {* *};
  F := BaseRing(mu[1,1]);
  q := #F;
  z := PrimitiveElement(F);
  for polpart in mu do
    f, lambda := Explode(polpart);
    tp := (Degree(f) eq 1) select 0 else IsIrreducible(f) select 2 else 1;
    label := {* *};
    for pp in lambda do
      e, m := Explode(pp);
      if tp gt 0 then
        Include(~label,<e,F!1>^^m);
      elif IsEven(e) then
        Include(~label,<e,F!0>^^(m div 2));
      else
        ee := Abs(e);
        ss := sgnO(ee,m,q);
        if e*ss gt 0 then
          Include(~label,<ee,F!1>^^m);
        else
          Include(~label,<ee,z>);
          if m gt 1 then
            Include(~label,<ee,F!1>^^(m-1));
          end if;
        end if;
      end if;
    end for;
    Include(~name,<tp,f,label>);
  end for;
  return name;
end function;

tagToNameO := function(mu)
  n := tagDim(mu);
  if IsEven(n) then return toNameEven(mu); end if;
  F := BaseRing(mu[1,1]);
  label := toNameEven(mu); 
  return TurnCorrectLabel(label, n, F);
  // g := RepresentativeMatrixO(mu);
  // return IsometryGroupClassLabel("GO",g);
end function;

sigil := ["s","ns","id"];
tagToNameSO := function(mu)
  if Type(mu) eq Tup then 
    xi, sgn := Explode(mu);
    nm := < tagToNameO(xi), sigil[sgn+2] >;
  else
    nm := < tagToNameO(mu), "ns" >;
  end if;
  return nm;
end function;


// The sequence representing the function from *-irreducible polynomials to
// signed partitions corresponding to the De Franceschi label nm in an
// orthogonal group over GF(q), q odd.  If the dimension is odd, further
// processing is necessary.
toTag := function(nm)
  tag := {@ @};
  F := BaseRing(Rep(nm)[2]);
  q := #F;
  for term in nm do
    ptn := [];
    tp, f, mu := Explode(term);
// Convert mu to triples < e, alpha, m >
    labels := [ Append(pp,m) : pp -> m in mu ];
    Sort(~labels);
    prev := <0,0>; // previous value of <e,m>
    for eam in labels do
      e, alpha, m := Explode(eam);
      if tp gt 0 then
        Append(~ptn, <e,m>);
      elif IsEven(e) then
        Append(~ptn,<e,2*m>);
      else
        ss := sgnO(e,m,q);
        if e eq prev[1] then
          mm := prev[2]+m;
          ss := sgnO(e,mm,q);
          // replace the top of the stack
          ptn[#ptn] := < -ss*e,mm >;
          prev := <0,0>;
        elif alpha eq 1 then
          Append(~ptn,< ss*e,m >);
          prev := <e,m>;
        else
          Append(~ptn,< -ss*e,m >);
          prev := <e,m>;
        end if;
      end if;
    end for;
    Include(~tag, < f, ptn > );
  end for;
  return tag;
end function;

nameToTagO := function(nm)
  tag := toTag(nm);
  if IsOdd(nmDim(nm)) then
    if theSign(tag) eq -1 then tag := changeSign(tag); end if;
  end if;
  return tag;
end function;

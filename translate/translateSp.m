freeze;

/* 2020-11-14
 * Translation between my conjugacy class names and those of Giovanni
 * for finite symplectic groups
 */

// The sign of the unipotent or negative unipotent of type <e,m> in GF(q)
// The argument u is true for unipotents, false for the negative of unipotents
sgnSp := function(u,e,m,q)
  error if not IsEven(e), "e must be even";
  if m mod 4 eq 0 or q mod 8 eq 1 then return 1; end if;
  if u then
    case q mod 8:
      when 3:
        val := (m+e) mod 4 eq 3 select 1 else -1;
      when 5:
        val := m mod 4 eq 2 select 1 else -1;
      when 7:
        val := (m+e) mod 4 eq 1 select 1 else -1;
    end case;
  else
    case q mod 8:
      when 3:
        val := (m+e) mod 4 eq 1 select 1 else -1;
      when 5:
        val := m mod 4 eq 2 select 1 else -1;
      when 7:
        val := (m+e) mod 4 eq 3 select 1 else -1;
    end case;
  end if;
  return val;
end function;

// From Milnor symplectic signed partitions to Giovanni De Franceschi names
tagToNameSp := function(mu)
  tag := {* *};
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
      elif IsOdd(e) then
        Include(~label,<e,F!0>^^(m div 2));
      else
        a0 := Coefficient(f,0);
        ss := sgnSp(a0 ne F!1,e,m,q);
        if ss eq 1 then
          if e gt 0 then
            Include(~label,<e,F!1>^^m);
          else
            Include(~label,<-e,z>);
            if m gt 1 then
              Include(~label,<-e,F!1>^^(m-1));
            end if;
          end if;
        else
          if e lt 0 then
            Include(~label,<-e,F!1>^^m);
          else
            Include(~label,<e,z>);
            if m gt 1 then
              Include(~label,<e,F!1>^^(m-1));
            end if;
          end if;
        end if;
      end if;
    end for;
    Include(~tag,<tp,f,label>);
  end for;
  return tag;
end function;

// From Giovanni De Franceschi names to Milnor symplectic signed partitions
nameToTagSp := function(nm)
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
      elif IsOdd(e) then
        Append(~ptn,<e,2*m>);
      else
        a0 := Coefficient(f,0);
        ss := sgnSp(a0 ne F!1,e,m,q);
        if e eq prev[1] then
          mm := prev[2]+m;
          ss := sgnSp(a0 ne F!1,e,mm,q);
          // replace the top of the stack
          ptn[#ptn] := <-ss*e,mm>;
          prev := <0,0>;
        elif alpha eq 1 then
          if ss gt 0 then
            Append(~ptn,<e,m>);
          else
            Append(~ptn,<-e,m>);
          end if;
          prev := <e,m>;
        else
          if ss gt 0 then
            Append(~ptn,<-e,m>);
          else
            Append(~ptn,<e,m>);
          end if;
          prev := <e,m>;
        end if;
      end if;
    end for;
    Include(~tag, < f, ptn > );
  end for;
  return tag;
end function;



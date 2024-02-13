tagToNameGU := function(mu)
  tag := {* *};
  F := BaseRing(mu[1,1]);
  q := #F;
  for polpart in mu do
    f, lambda := Explode(polpart);
    tp := (Degree(f) eq 1) select 0 else IsIrreducible(f) select 2 else 1;
    label := {* *};
    for pp in lambda do
      e, m := Explode(pp);
      Include(~label, e^^m);
    end for;
    Include(~tag, <tp,f,label>);
  end for;
  return tag;
end function;

tagToNameSU := func< xi |
  < tagToNameGU(mu), ndx > where mu, ndx is Explode(xi) >;


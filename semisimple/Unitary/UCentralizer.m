freeze;

// x = semisimple element in G=GU(n,q) or SU(n,q) 
// if not semisimple the result could be wrong)
// return the factored order of the centralizer of x in G
SSCentralizerOrderU:=function(G,x)
   return SSCentralizerOrder(G,x);
end function;

// returns the centralizer of g in G and compute its Order and FactoredOrder
// G must be GU or SU and g must be semisimple, 
// otherwise the result may be wrong (there are no checks)

SSCentralizerU:=function(G,g)
   H:=SSCentralizer(G,g);
   H`FactoredOrder:=SSCentralizerOrderU(G,g);
   H`Order:=Integers()!FactoredOrder(H);
   return H;
end function;

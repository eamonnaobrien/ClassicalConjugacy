freeze;

// x = semisimple element in Sp(n,q)
// returns factored order of Centralizer(Sp(n,q),x)
// if x is not semisimple, the result may be wrong

SSCentralizerOrderSp:=function(G,x)
   return SSCentralizerOrder (G,x);
end function;

// returns the centralizer of g in G and assigns Order and FactoredOrder
// requires functions CentralizerSS.m, SpCentralizerOrder.m
// G must be Sp(n,F) and g must be semisimple, otherwise the result may be wrong

SSCentralizerSp:=function(G,g)
   H:=SSCentralizer(G,g);
   H`FactoredOrder:=SSCentralizerOrderSp(G,g);
   H`Order:=Integers()!FactoredOrder(H);
   return H;
end function;

freeze;

// x = semisimple element in G, where G is any orthogonal group 
// except odd dimension and even characteristic
// returns factored order of Centralizer(G,x)
SSCentralizerOrderO:=function(G,x)
   return SSCentralizerOrder (G,x);
end function;

// Returns the centralizer of g in G and assigns Order and FactoredOrder.
// G must be any orthogonal group (not even char and odd dimension)
// and g must be semisimple, otherwise the result may be wrong

SSCentralizerO:=function(G,g)
   H:=SSCentralizer(G,g);
   H`FactoredOrder:=SSCentralizerOrderO(G,g);
   H`Order:=Integers()!FactoredOrder(H);
   return H;
end function;

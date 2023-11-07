freeze;

// returns z in G such that z^-1*x*z = y
// G is any orthogonal group, except odd dimension and even characteristic
// works only for x,y semisimple

SSIsConjugateO:=function(G,x,y)
   return SSIsConjugate(G,x,y);
end function;

freeze;

// order of classical group 

CardinalityOfClassicalGroup:=function(type,n,q)
   _,p,e:=IsPrimePower(q);
   m:= n div 2;
   
   if IsOdd(n) then
      if type in {"orthogonalplus","orthogonalminus","O+","O-","GO+","GO-"} then
         type:="GO";
      elif type in {"SO+","SO-"} then
         type:="SO";
      elif type in {"Omega+","Omega-"} then
         type:="Omega";
      end if;
   end if;
   
   C:=Factorization(1);
   case type:
      when "linear","GL","SL":
         if n gt 1 then
            C*:=SequenceToFactorization([<p,e*n*(n-1) div 2>]);
         end if;
         for i in [1..n] do
            C*:=Factorization(q^i-1);
         end for;
         if type eq "SL" then
            C/:=Factorization(q-1);
         end if;
      when "symplectic","Sp":
         C*:=SequenceToFactorization([<p,e*m^2>]);
         for i in [1..m] do
            C*:=Factorization(q^(2*i)-1);
         end for;
      when "unitary","GU","SU":
         if n gt 1 then
            C*:=SequenceToFactorization([<p,e*n*(n-1) div 2>]);
         end if;
         for i in [1..n] do
            C*:=Factorization(q^i-(-1)^i);
         end for;
         if type eq "SU" then
            C/:=Factorization(q+1);
         end if;
      when "orthogonalplus","O+","GO+","SO+","Omega+":
         C*:=SequenceToFactorization([<2,1>]);
         if m gt 1 then
            C*:=SequenceToFactorization([<p,e*m*(m-1)>]);
         end if;
         C*:=Factorization(q^m-1);
         for i in [1..m-1] do
            C*:=Factorization(q^(2*i)-1);
         end for;
         if type eq "Omega+" then
            C/:=SequenceToFactorization([<2,1>]);
            if IsOdd(q) then
               C/:=SequenceToFactorization([<2,1>]);
            end if;
         elif type eq "SO+" and IsOdd(p) then
               C/:=SequenceToFactorization([<2,1>]);
         end if;
      when "orthogonal", "orthogonalcircle", "O","GO","SO","Omega":
         C*:=SequenceToFactorization([<2,1>]);
         if m ge 1 then
            C*:=SequenceToFactorization([<p,e*m^2>]);
         end if;
         for i in [1..m] do
            C*:=Factorization(q^(2*i)-1);
         end for;
         if type eq "Omega" then
            C/:=SequenceToFactorization([<2,1>]);
            if IsOdd(q) then
               C/:=SequenceToFactorization([<2,1>]);
            end if;
         elif type eq "SO" and IsOdd(p) then
               C/:=SequenceToFactorization([<2,1>]);
         end if;
      when "orthogonalminus","O-","GO-","SO-","Omega-":
         C*:=SequenceToFactorization([<2,1>]);
         if m gt 1 then
            C*:=SequenceToFactorization([<p,e*m*(m-1)>]);
         end if;
         C*:=Factorization(q^m+1);
         for i in [1..m-1] do
            C*:=Factorization(q^(2*i)-1);
         end for;
         if type eq "Omega-" then
            C/:=SequenceToFactorization([<2,1>]);
            if IsOdd(q) then
               C/:=SequenceToFactorization([<2,1>]);
            end if;
         elif type eq "SO-" and IsOdd(p) then
               C/:=SequenceToFactorization([<2,1>]);
         end if;
   end case;

   return C;
end function;

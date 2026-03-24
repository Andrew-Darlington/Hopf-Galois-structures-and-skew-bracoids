// Helper function to find small generating set
SmallGeneratingSet := function (U: NmrTrials := 5)
   n := Ngens (U);
   d := 2;
   c := 0; 
   o := #U;
   while d lt n do
      L := sub<Generic (U) | [Random(U): i in [1..d]]>;
      RandomSchreier (L);
      l := Order(L);
      if o eq l then
         return L;
      end if;
      c +:= 1;
      if c eq NmrTrials then
         c := 0;
         d +:= 1;
      end if;
   end while;
   return U;
end function;
 
// Find small generating set for A 
MyGeneratingSet := function (G, A: Limit := 2, Max := 5)
   ng := Ngens (A);
   ntrial := 0;
   repeat
      ntrial +:= 1; 
      if ng ge Limit then
         prep, P := PermutationRepresentation (A);
         P_small := SmallGeneratingSet (P);
         if Ngens (P_small) lt ng then
            A_gens := [P_small.i @@ prep : i in [1..Ngens(P_small)]];
            A := sub<A | A_gens>;
            P := P_small;
            ng := Ngens (P);
         end if;
      end if;
   until ntrial gt Max or ng le Limit;
   return A, P;
end function;
 
NumOfAutomorphisms := function (G)
   A := AutomorphismGroup (G: UsePCGroup := true);
   A, P := MyGeneratingSet (G, A);
   ng := Ngens (A);
   "Number of generators of A is now ", ng;
   
   S0 := Stabiliser (G, 1);
   "Size of stabiliser is ", #S0;
   Gprime_keys := {@ CanonicalInvariant (S0) @};
   perms := [[] : i in [1..ng]];
 
   j := 1;
   while j le #Gprime_keys do
     S := sub< G | Gprime_keys[j]>;
     for i in [1..ng] do
       im := (A.i)(S);
       key := CanonicalInvariant (im);
       pos := Position (Gprime_keys, key);
       if pos eq 0 then
         Include (~Gprime_keys, key);
         if #Gprime_keys mod 10000 eq 0 then 
           "j, #Gprime ", j, #Gprime_keys;
         end if;
         Include (~Gprime_keys, key);
         pos := #Gprime_keys;
       end if;
       Append (~perms[i], pos);
     end for;
     j +:= 1;
   end while;
 
   "Size of class is ", #Gprime_keys;
   pgp := sub<Sym (#Gprime_keys) | [perms[i]: i in [1..ng]]>;
   perm_elts := [pgp!perms[i] : i in [1..ng]];
 
   act := hom<P -> pgp | perm_elts>;
   Q := Stabiliser(pgp, 1) @@ act;
   
   return #Q,Gprime_keys;
end function;
 
TransGroup := function (params)
   G,_,N,hol,i,id:=Explode(params);
   n:=#N;

   CN := Centraliser (Sym (n), N);
 
   intfields := #IntermediateSubgroups (G, Stabiliser (G, 1)) + 2;
   subGst := 0;
   for H in AllSubgroups (N) do
      if G subset Normalizer (hol, H) then
         subGst := subGst+1;
      end if;
   end for;
   if G`Order eq n then
     if intfields eq subGst then
       isAC := CN subset G;
       props:=<true,true,isAC>; 
     else
       props:=<true,false,false>;
     end if;
	stabs:={@ [] @};
	ordaut:=#AutomorphismGroup(G);
   else
      numaut,stab := NumOfAutomorphisms (G);
      if intfields eq subGst then
        isAC := CN subset G;
        props:=<false,true,isAC>; 
      else
        props:=<false,false,false>;
     end if;
	stabs:=stab;
	ordaut:= numaut;
   end if;
     return [*id, stabs, ordaut, props*];
end function;
 
host := "host.name";// needs to be same as for manager
port := 10200;
DistributedWorker (host, port, TransGroup);
quit;

// here is a simple version of enumeration code which
// can be run in serial mode to process a single group

// Helper function to find small generating set
SmallGeneratingSet := function (U: NmrTrials := 5)
   n := Ngens (U);
   d := 2; c := 0; 
   o := #U;
   while d lt n do
      L := sub<Generic(U) | [Random(U): i in [1..d]]>;
      RandomSchreier (L);
      l := #L;
      if o eq l then return L; end if;
      c +:= 1;
      if c eq NmrTrials then c := 0; d +:= 1; end if;
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

NumOfAutomorphisms := function (G: Verbose := false) 
   A := AutomorphismGroup (G: UsePCGroup := true);
   A, P := MyGeneratingSet (G, A);
   ng := Ngens (A);
   if Verbose then "Number of generators of A is now ", ng; end if;
   
   S0 := Stabiliser (G, 1);
   if Verbose then "Size of stabiliser is ", #S0; end if;
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
               if Verbose then "j, #Gprime ", j, #Gprime_keys; end if;
            end if;
            Include (~Gprime_keys, key);
            pos := #Gprime_keys;
         end if;
         Append (~perms[i], pos);
      end for;
      j +:= 1;
   end while;

   if Verbose then "Size of class is ", #Gprime_keys; end if;
   pgp := sub<Sym (#Gprime_keys) | [perms[i]: i in [1..ng]]>;
   perm_elts := [pgp!perms[i] : i in [1..ng]];

   act := hom<P -> pgp | perm_elts>;
   Q := Stabiliser(pgp, 1) @@ act;
   return #Q;
end function;

TestGroup := function (params: Verbose := false) 
   G := params[1];
   len := params[2];
   N := params[3];
   hol := params[4];
   intfields := #IntermediateSubgroups (G, Stabiliser (G, 1)) + 2;
   if Verbose then "intfields is ", intfields; end if;
   hgs1 := 0;
   hgs2 := 0;
   hgs3 := 0;
   hgs4 := 0;
   sb1 := 0;
   sb2 := 0;
   sb3 := 0;
   n := #N;
   CN := Centraliser (Sym (n), N);
   ohol := #hol;
   subGst := 0;
   SN := AllSubgroups (N);
   for H in SN do 
      if G subset Normalizer (hol, H) then
         subGst := subGst+1;
      end if;
   end for;
   if #G eq n then
      s := (#AutomorphismGroup(G))*(len)/(ohol/n);
      hgs1 := hgs1+s;
      hgs2 := hgs2+s;
      sb1 := sb1+1;
      sb2 := sb2+1;
      if intfields eq subGst then
         hgs4 := hgs4+s;
         if CN subset G then
            hgs3 := hgs3+s;
            sb3 := sb3+1;
         end if;
      end if;
   else
      a := NumOfAutomorphisms (G: Verbose := Verbose);
      s := (a*(len))/(ohol/n);
      hgs1 := hgs1+s;
      sb1 := sb1+1;
      if intfields eq subGst then
         hgs4 := hgs4+s;
         if CN subset G then
            hgs3 := hgs3+s;
            sb3 := sb3+1;
         end if;
      end if;
   end if;
   return [hgs1, hgs2, hgs3, hgs4, sb1, sb2, sb3];
end function;

// process SmallGroup (order, nmr)
ProcessGroup := function (order, nmr: Verbose := false);
   if Verbose then "\nProcess group ", order, "#", nmr; end if;
   N := SmallGroup (order, nmr);
   n := Order (N);
   hol, f := Holomorph (N);
   N := f(N);
   if Verbose then "Order hol ", #hol; end if;
   if Verbose then "compute subgroups"; end if;
   t := Subgroups (hol: OrderMultipleOf := n, IsTransitive:=true);
   I := [<x`subgroup, x`length, N, hol>: x in t];
   //here we sum by multiplying out by the sizes of the conjugacy classes.
   if Verbose then "# of subgroups is ", #I; end if;
   
   Z := [];
   for  i in [1..#I] do 
      Z[i] := TestGroup (I[i]: Verbose := Verbose);
   end for;
   
   L := [z: z in Z];
   
   r1 := &+[L[i][1]: i in [1..#L]];
   r2 := &+[L[i][2]: i in [1..#L]];
   r3 := &+[L[i][3]: i in [1..#L]];
   r4 := &+[L[i][4]: i in [1..#L]];
   r5 := &+[L[i][5]: i in [1..#L]];
   r6 := &+[L[i][6]: i in [1..#L]];
   r7 := &+[L[i][7]: i in [1..#L]];
   results := [r1, r2, r3, r4, r5, r6, r7];
   if Verbose then "Results for group", order, "#", nmr, " are :", results; end if;
   
   return results;
end function;

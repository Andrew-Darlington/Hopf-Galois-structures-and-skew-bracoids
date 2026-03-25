Attach("attributes.m");

MaxTransitiveGroupId := 30;

//======================================================================
//======================================================================
TransSubs := function (n,i,id)
   N := SmallGroup (n, i);
   hol, f := Holomorph (N);
   N:=f(N);
   t := Subgroups (hol : OrderMultipleOf := n, IsTransitive := true);
   I := [];
   for x in t do
      G := x`subgroup;
      G`Length := x`length;
      G`Type := i;
      G`Id := id;
      Append(~I,G);
      id+:=1;
   end for;
   return I,N,hol,id;
end function;
//======================================================================
//======================================================================
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
   
   return #Q,Gprime_keys;
end function;
 
TransGroup := function (G, N, hol: Verbose := false)
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
      numaut,stab := NumOfAutomorphisms (G: Verbose := Verbose);
      if intfields eq subGst then
        isAC := CN subset G;
        props:=<false,true,isAC>; 
      else
        props:=<false,false,false>;
     end if;
	stabs:=stab;
	ordaut:= numaut;
   end if;
     return stabs, ordaut, props;
end function;
//======================================================================
//======================================================================
// partition collection of groups S up to isomorphism 
NonIsom := function (S)
   if #S le 1 then return S, [i : i in [1..#S]]; end if;
   D := [S[1]];
   for i in [2..#S] do
      if forall {j : j in [1..#D] | 
            IsIsomorphic (S[i], D[j]) eq false} then 
         Append (~D, S[i]);
      end if;
   end for;
   Bins := [[i: i in [1..#S] | IsIsomorphic (S[i], D[j])]: j in [1..#D]];
   return Bins;
end function;

// merge existing "equivalence" classes of subgroups in A up to isomorphism 
MergeClasses := function (A, classes)
   n := #classes;
   processed := {@ @};  
   new_classes := [];
   
   for i in [1..n] do
      if i in processed then continue i; end if;
      
      // Start a new merged class with class i
      current_class := classes[i];
      Include (~processed, i);
      
      // Representative for isomorphism testing
      rep_idx := Rep(classes[i]);
      G := A[rep_idx];
      
      // Check all remaining unprocessed classes
      for j in [i+1..n] do
         if j in processed then continue j; end if;
         
         rep_idx_j := Rep(classes[j]);
         H := A[rep_idx_j];
         
         if IsIsomorphic (G, H) then
            current_class cat:= classes[j];
            Include (~processed, j);
         end if;
      end for;
      
      Append(~new_classes, Sort (current_class));
   end for;
   
   Sort (~new_classes);
   return new_classes;
end function;

// partition groups in S by isomorphism type using IdentifyGroup 
MyBins := function (S)
   if CanIdentifyGroup (#Rep (S)) then 
      ids := [IdentifyGroup (s): s in S];
      index := [[i: i in [1..#ids] | ids[i] eq j]: j in Set (ids)];
      return true, Sort (index);
   else 
      index := [[1..#S]];
      return false, index;
   end if;
end function;

// partition bins using TransitiveGroupIdentification and isomorphism merge 
MyTransitiveBins := function (S)
   if Degree (Rep (S)) le MaxTransitiveGroupId then 
      ids := [a where a := TransitiveGroupIdentification (s): s in S];
      index := [[i: i in [1..#ids] | ids[i] eq j]: j in Set (ids)];
      index := MergeClasses (S, index);
      return true, Sort (index);
   else 
      index := [[1..#S]];
      return false, index;
   end if;
   return index;
end function;

// identify different presentations in S 
DifferentOnes := function (S)
   if #S le 1 then return S, [i : i in [1..#S]]; end if;
   D := [S[1]];
   for i in [2..#S] do
      if forall {j : j in [1..#D] | 
            IsIdenticalPresentation (S[i], D[j]) eq false} then 
        Append (~D, S[i]);
      end if;
   end for;
   Bins := [[i: i in [1..#S] | IsIdenticalPresentation (S[i], D[j])]: j in [1..#D]];
   return Bins;
end function;

// partition p-groups up to isomorphism using Standard Presentation 
MyStandard := function (P)
   standard := []; maps := [* *];
   for i in [1..#P] do
      S, phi := PCGroup (P[i]);
      T, eta := StandardPresentation (S);
      maps[i] := phi * eta;
      Append (~standard, T);
   end for;
   bins := DifferentOnes (standard);
   return standard, maps, bins; 
end function;

// isomorphism map from D[i] to D[j] 
IsomMap := function (standard, maps, i, j);
   // delta is the identity isomorphism between two identical groups  
   f, delta := IsIsomorphic (standard[i], standard[j]);
   gamma := maps[i] * delta * maps[j]^-1;
   return gamma;
end function;

// order and perm group id for S 
GroupIds := function (S)
    try
       id := IdentifyGroup (S);
    catch e;
       id := "unknown";
    end try;
    try
       permid := TransitiveGroupIdentification (S);
    catch e;
       permid := "unknown";
    end try;
    return id, permid;
end function;

// By default use StandardPresentation if order or bin size is large enough
TransEquiv := function (D: Verbose := false, Min_Order := 16, BIN_SIZE := 4, Standard := true)

   rep := D[1];
   if Verbose then "Order of subgroups is ", #rep; end if;
   if Verbose then "Number of subgroups is ", #D; end if;

   if CanIdentifyGroup (#rep) then 
      if Verbose then "Partition using IdGroup strategy"; end if;
      success, bins := MyBins (D);
   elif Degree (rep) le MaxTransitiveGroupId then 
      if Verbose then "Partition using IdTrans and refine to isom strategy"; end if;
      success, bins := MyTransitiveBins (D);
   else 
      if Verbose then "Default strategy: no known isomorphisms among subgroups"; end if;
      success := false;
      bins := [[i: i in [1..#D]]];
   end if;

   if Verbose then "After Order id and Transitive id, # of bins is ", #bins; end if;
   if Verbose then "Sizes of bins are ", [#b: b in bins]; end if;

   // if no partition into isomorphism types from previous strategies 
   // for p-groups, then use StandardPresentation to do this 
   standard_setup := Standard and IsPrimePower (#rep) and 
                     #rep ge Min_Order and not success; 
   if standard_setup then 
      if Verbose then "Now apply Standard Presentation strategy for p-groups"; end if;
      t := Cputime ();
      standard, maps, bins := MyStandard (D);
      if Verbose then "Total time to standardise ", Cputime (t); end if;
      if Verbose then "After Standard, # of bins is ", #bins;  end if;
      if Verbose then "After Standard, sizes of bins are ", [#b: b in bins]; 
end if;
   end if;

total := 0;

   // groups which have already been sorted into equivalence classes
   used := { }; 
   classes := [];

   for m in [1..#bins] do
      bin := bins[m];
      Sort (~bin);
      if Verbose then "\nProcess bin", m, "of size ", #bin; end if;

      use_standard_maps := false;
      if Standard and not standard_setup and 
         (IsPrimePower (#rep) and #rep ge Min_Order and #bin gt BIN_SIZE) then 
         if Verbose then "Setup standard presentations for this bin"; end if;
         t := Cputime ();
         T := [D[i]: i in bin];
         standard, maps := MyStandard (T);
         if Verbose then "Time to standardise bin of size ", #bin, " is ", Cputime (t); end if;
         total +:= Cputime (t);
         assert #{SmallGroupEncoding (x): x in standard} eq 1;
         use_standard_maps := true;
      end if;

      // run over each group in bin 
      for a in [1..#bin] do 
         k := bin[a];
         if k in used then continue a; end if;

         G1 := D[k];
         if Verbose then "k = ", k; end if;

         // id, permid := GroupIds (G1[1]`transgroup);

         stab := Stabiliser (G1, 1);

         // need to run from G1 to end
         equivclass := [G1`Id];
         s := G1`Length;
         Include (~used, k);
         for b in [a + 1..#bin] do 
            j := bin[b];
            if j in used then continue b; end if;

            G2 := D[j];
            if not use_standard_maps then 
               bool, isom := IsIsomorphic (G1, G2);
               if not bool then continue b; end if;
            else 
               isom := IsomMap (standard, maps, Position (bin, k), Position (bin, j));
            end if;
            im := isom (stab);
            if CanonicalInvariant (im) in G2`Stabs then
               s +:= G2`Length;
               Append (~equivclass, G2`Id);
               Include (~used, j);
            end if;
         end for;

         if #equivclass gt 0 then
            Append (~classes, <s,equivclass>);
            if Verbose then "new equivalence class has length ", #equivclass; end if;
            if Verbose then "# of used groups so far is ", #used; end if;
            if Verbose then "# of equivalence classes so far is ", #classes; end if;
         end if;
      end for;
   end for;

   if Verbose then "Total time in Standard is ", total; end if;

   if Verbose then "Number of equivalence classes is ", #classes; end if;
   return classes;
end function;
//======================================================================
//======================================================================
NumOfType := function (EquivClass,n: Verbose := false)
   oEC:=#EquivClass;
   HGS_Sbracoid_list := [**];
   
   j := 1;
   for i in [1..NumberOfSmallGroups (n)] do
      ordautN := #AutomorphismGroup (SmallGroup(n,i));
      if j le oEC and EquivClass[j][1] eq i then
         EC:=EquivClass[j];
         hgstot := 0;
         hgsbc := 0;
         hgsac := 0;
         totgrps := 0;
         grps:=[];
         grpsAC:=[];
         grpsBC:=[];
         while j le oEC and EquivClass[j][1] eq i do
            EC:=EquivClass[j];
            grp:=EC[5];
            Append(~grps,grp);
            s:=EC[2];
            props:=EC[4];
            totgrps := totgrps + s;
             hgstot := hgstot + s;
            if props[2] then
               hgsbc := hgsbc + s;
               Append(~grpsBC,grp);
               if props[3] then
                  hgsac := hgsac + s;
                   Append(~grpsAC,grp);
               end if;
            end if;
            j := j+1;
         end while;
         EC:=EquivClass[j-1];
         ordautG := EC[3];
         factor := ordautG/ordautN;
         hgstot:= hgstot*factor;
         hgsac := hgsac*factor;
         hgsbc := hgsbc*factor;
         sbtot := #grps;
         sbac := #grpsAC;
         Append (~HGS_Sbracoid_list,<i,grps,grpsBC,grpsAC,totgrps,hgstot,hgsbc,hgsac,sbtot,sbac>);
      end if;
   end for;
   return EquivClass[j-1][4][1],HGS_Sbracoid_list;
end function;
//======================================================================
//======================================================================
/*
   given an integer n, outputs a list of all transitive subgroups G 
   (of Hol(N) for each N) with the following data:
   - the set of images of G' under Aut(G)
   - |Aut(G, G')|
   - the number of (transitive) subgroups conjugate to G
   - whether G is a regular subgroup
   - whether G corresponds to an almost classical(ly Galois) structure
   - whether G corresponds to a HGS admitting bijective correspondence
   - the identifier i such that N=SmallGroup(n,i) is the type admitted by G
*/
Data := function (n: Verbose := false)
   id := 1;
   Z := [];
   for i in [1..NumberOfSmallGroups(n)] do
      TS,N,hol,id := TransSubs(n,i,id);
      for k in [1..#TS] do
         G := TS[k];
         stabs, ordaut, props := TransGroup(G,N,hol: Verbose := Verbose);
         G`Stabs := stabs;
         G`Ordaut := ordaut;
         G`Props := props;
         Append(~Z,G);
      end for;
   end for;
   return Z;
end function;
  
//sorts the transitive subgroups into permutation isomorphism classes
TransEquivalenceClasses := function (n: Verbose := false)
    
    D := Data (n: Verbose := Verbose);
    ords := {G`Order : G in D};
    if Verbose then "ords is ", ords; end if;
    
    Z1 := [];
    for d in ords do
       Z1 := Z1 cat TransEquiv([G : G in D | G`Order eq d]: Verbose := Verbose);
    end for;
    
    Z2 := [];
    for G in D do
       delete G`Stabs;
       Append(~Z2,G);
    end for;
    delete D;

   return Z1,Z2;
end function;
  
//MAIN function, returns a database of HGSs & SBs of degree n with attached data
NumAll := function (n: Verbose := false)
   TE,Groups := TransEquivalenceClasses (n: Verbose := Verbose);
   
   X := [];
   for r in TE do
      IDs := r[2];
      EquivClass := [];
      for j in IDs do
         G := Groups[j];
         Append(~EquivClass,<G`Type,G`Length,G`Ordaut,G`Props,j>);
      end for;
      EC,HGS_SB := NumOfType(EquivClass,n: Verbose := Verbose);
      Append(~X,<r[1],EC,[x : x in HGS_SB]>);
   end for;
   delete TE;
   if Verbose then "# of X is ", #X, "\n"; end if;
   
   RESULTS := "Results-" cat IntegerToString (n);
   GROUPS := "Grps-" cat IntegerToString (n);
   
   return X;
end function;

/*
for n in [2..100] do 
   if n in {32,48,64,80,81,96} then continue; end if;
   "\nProcess order n = ", n;
   L := NumAll (n);
   System ("rm -rf logs/worker*-*.log");
//   System ("rm -r logs/manager*-*.log");
end for;
*/

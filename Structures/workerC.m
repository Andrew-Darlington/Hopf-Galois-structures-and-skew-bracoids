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
   if Degree (Rep (S)) le 47 then 
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

// isomorphism map from subs[i] to subs[j] 
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
TransEquiv := function (params: Min_Order := 16, BIN_SIZE := 4, Standard := true)
   D := params;

   subs := [G[1]: G in D];
   rep := subs[1];
   "Order of subgroups is ", #rep;
   "Number of subgroups is ", #subs;

   if CanIdentifyGroup (#rep) then 
      "Partition using IdGroup strategy";
      success, bins := MyBins (subs);
   elif Degree (rep) le 47 then 
      "Partition using IdTrans and refine to isom strategy";
      success, bins := MyTransitiveBins (subs);
   else 
      "Default strategy: no known isomorphisms among subgroups";
      success := false;
      bins := [[i: i in [1..#subs]]];
   end if;

   "After Order id and Transitive id, # of bins is ", #bins;
   "Sizes of bins are ", [#b: b in bins];

   // if no partition into isomorphism types from previous strategies 
   // for p-groups, then use StandardPresentation to do this 
   standard_setup := Standard and IsPrimePower (#rep) and 
                     #rep ge Min_Order and not success; 
   if standard_setup then 
      "Now apply Standard Presentation strategy for p-groups";
      t := Cputime ();
      standard, maps, bins := MyStandard (subs);
      "Total time to standardise ", Cputime (t);
      "After Standard, # of bins is ", #bins; 
      "After Standard, sizes of bins are ", [#b: b in bins];
   end if;

total := 0;

   // groups which have already been sorted into equivalence classes
   used := { }; 
   classes := [];

   for m in [1..#bins] do
      bin := bins[m];
      Sort (~bin);
      "\nProcess bin", m, "of size ", #bin;

      use_standard_maps := false;
      if Standard and not standard_setup and 
         (IsPrimePower (#rep) and #rep ge Min_Order and #bin gt BIN_SIZE) then 
         "Setup standard presentations for this bin";
         t := Cputime ();
         T := [subs[i]: i in bin];
         standard, maps := MyStandard (T);
         "Time to standardise bin of size ", #bin, " is ", Cputime (t);
         total +:= Cputime (t);
         assert #{SmallGroupEncoding (x): x in standard} eq 1;
         use_standard_maps := true;
      end if;

      // run over each group in bin 
      for a in [1..#bin] do 
         k := bin[a];
         if k in used then continue a; end if;

         G1 := D[k];
         "k = ", k;

         // id, permid := GroupIds (G1[1]`transgroup);

         stab := Stabiliser (G1[1], 1);

         // need to run from G1 to end
         equivclass := [G1[4]];
         s := G1[2];
         Include (~used, k);
         for b in [a + 1..#bin] do 
            j := bin[b];
            if j in used then continue b; end if;

            G2 := D[j];
            if not use_standard_maps then 
               bool, isom := IsIsomorphic (G1[1], G2[1]);
               if not bool then continue b; end if;
            else 
               isom := IsomMap (standard, maps, Position (bin, k), Position (bin, j));
            end if;
            im := isom (stab);
            if CanonicalInvariant (im) in G2[3] then
               s +:= G2[2];
               Append (~equivclass, G2[4]);
               Include (~used, j);
            end if;
         end for;

         if #equivclass gt 0 then
            Append (~classes, <s,equivclass>);
            "new equivalence class has length ", #equivclass;
            "# of used groups so far is ", #used;
            "# of equivalence classes so far is ", #classes;
         end if;
      end for;
   end for;

   "Total time in Standard is ", total;

   "Number of equivalence classes is ", #classes;
   return classes;
end function;
 
host := "host.name"; // needs to be same as for manager
port := 10400;
DistributedWorker (host, port, TransEquiv);
quit;

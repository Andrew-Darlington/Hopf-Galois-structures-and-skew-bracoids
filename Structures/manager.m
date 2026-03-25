Nmr_Workers := 8;

SetLogFile ("logs/manager.log");
// you need to change this to hostname of machine, also in worker file
host := "host.name";
base_port:= 10000;


/*
   given an integer n, outputs a list of all transitive subgroups G 
   (of Hol(N) for each N) with the following data:
   - the set of images of G' under Aut(G)
   - |Aut(G, G')|
   - the number of (transitive) subgroups conjugate to G
   - whether G is a regular subgroup
   - whether G corresponds to an almost classical(ly Galois) structure
   - whether G corresponds to a HGS admitting bijective correspondence
   - the type, N, admitted by G
   - the group ID of N
*/
Data := function (n)   
   
   socket := Socket (: LocalHost := host, LocalPort := base_port); 
   I1 := [<n, i> : i in [1..NumberOfSmallGroups (n)]];
   for i in [1..Minimum (Nmr_Workers, #I1)] do
      command := "magma workerA.m > logs/workerA-" cat IntegerToString(i) cat ".log 2 &";
      System (command);
   end for;
   Z1 := DistributedManager (socket, I1);
   delete I1;
   
   I2 := Flat(Z1);
   delete Z1;
   // "# of I2 cases is ", #I2;
   System ("pgrep -f 'magma.*worker' | xargs -r kill -9 2>/dev/null || true");
   
   id:=1;
   I2new:=[];
   for z in I2 do
   	znew:=Append(z,id);
   	Append(~I2new,znew);
   	id+:=1;
   end for;
   delete I2;
   socketB := Socket (: LocalHost := host, LocalPort := base_port+200);

   for i in [1..Nmr_Workers] do
      command := "magma workerB.m > logs/workerB-" cat IntegerToString(i) cat ".log 2 &";
      System (command);
   end for;
   Z2 := DistributedManager (socketB, I2new); //returns id, stabs, ordaut, props
   System ("pgrep -f 'magma.*worker' | xargs -r kill -9 2>/dev/null || true");
   
   Z:=[];
   for j in [1..#I2new] do
   	i2:=I2new[j];
   	z2:=Z2[j];
   	
   	G:=i2[1];
   	G`Length:=i2[2];
   	G`Stabs:=z2[2];
   	G`Ordaut:=z2[3];
   	G`Props:=z2[4];
   	G`Type:=i2[5];
   	G`Id:=i2[6];
   	
   	Append(~Z,G);
   end for;
   delete I2new;
   delete Z2;
   return Z;
end function;
  
//sorts the transitive subgroups into permutation isomorphism classes
TransEquivalenceClasses := function (n)
    
    D := Data (n);
    ords := {G`Order : G in D};
    // "ords is ", ords;

    I3 := [[<G,G`Length,G`Stabs,G`Id> : G in D | G`Order eq d] : d in ords];
    

    socketC := Socket (: LocalHost := host, LocalPort := base_port+400); 

    // "# of I3 cases is ", #I3;

    for i in [1..Nmr_Workers] do
       command := "magma workerC.m > logs/workerC-" cat IntegerToString(i) cat ".log 2 &";
       System (command);
    end for;
    Z3 := DistributedManager (socketC, I3);
    delete I3;
    Z3:=Flat(Z3);

    System ("pgrep -f 'magma.*worker' | xargs -r kill -9 2>/dev/null || true");

   // list of equivalence classes along with size of each one
   
   Z:=[];
   j:=1;
   f:=func<x,y | x`Id - y`Id>;
   Sort(~D,f);
   for G in D do
   	delete G`Stabs;
   	Append(~Z,G);
   end for;
   delete D;
   return Z,Z3;
end function;
  
//MAIN function, returns a database of HGSs & SBs of degree n with attached data
NumAll := function (n)

   tt := Cputime (); 
   Attach("attributes.m");

   Groups,TE := TransEquivalenceClasses (n);
   
   I4:=[];
   for r in TE do
   	IDs:=r[2];
   	EquivClass:=[];
   	for j in IDs do
   		G:=Groups[j];
   		Append(~EquivClass,<G`Type,G`Length,G`Ordaut,G`Props,j>);
   	end for;
   	Append(~I4,<EquivClass,r[1],n>);
   end for;
   delete TE;
   // "# of I4 cases is ", #I4;

   socketD := Socket (: LocalHost := host, LocalPort := base_port+600);

  for i in [1..Nmr_Workers] do
      command := "magma workerD.m > logs/workerD-" cat IntegerToString(i) cat ".log 2 &";
      System (command);
   end for;

   Z4 := DistributedManager (socketD, I4);
   delete I4;
   System ("pgrep -f 'magma.*worker' | xargs -r kill -9 2>/dev/null || true");
   Z4 := Flat(Z4);
   "# of X is ", #Z4, "\n";
   X := [<z[1], z[2], [x:x in z[3]]>: z in Z4];
   delete Z4;
   
   manager_time := Cputime (tt);
   output := Pipe("grep -h 'Total time:' logs/work*-*.log | awk '{sum += $3} END {print sum}'", ""); 
   total_time := eval StripWhiteSpace(output);
   
   RESULTS := "Results-" cat IntegerToString (n);
   TIME := "Time-" cat IntegerToString (n);
   GROUPS := "Grps-" cat IntegerToString (n);
   
   fprintf "results/times/" cat TIME, "%o %.2o %o\n", "CPU time for manager is", manager_time, "seconds";
   fprintf "results/times/" cat TIME, "%o %.2o %o\n", "CPU time across all workers is", total_time, "seconds";
   fprintf "results/times/" cat TIME, "%o %.2o %o", "Total time is", manager_time + total_time, "seconds";
   
   PrintFileMagma ("results/" cat RESULTS, X);
   PrintFileMagma ("results/transgrps/" cat GROUPS, Groups);
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

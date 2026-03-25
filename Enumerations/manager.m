Nmr_Workers := 8;

// uncomment these values if you want to process group directly in magma session;
// retain the "  " 
// order := "81";
// nmr := "2";
name := "logs/manager-" cat nmr cat ".log";

SetLogFile (name);
SetEchoInput (true);
SetVerbose("ManagerWorker", 1);
// you need to change this to hostname of machine, also in worker file
socket := Socket(: LocalHost := "host.name", LocalPort := 10000);

tt := Cputime ();

i := StringToInteger (nmr);
order := StringToInteger (order);
if not (i in [1..NumberOfSmallGroups (order)]) then 
   "No such group of this order"; quit;
end if;

"\n\n Process group ", i;
N := SmallGroup (order, i);
n := Order(N);
hol, f := Holomorph (N);
N := f(N);
"Order hol ", #hol;
"compute subgroups";
time t := Subgroups(hol:OrderMultipleOf := n, IsTransitive:=true);

I := [<x`subgroup, x`length, N, hol>: x in t];
//here we sum by multiplying out by the sizes of the conjugacy classes.
"# of subgroups is ", #I;

delete t;

manager_time := Cputime (tt);

work_items := I;

for i in [1..Nmr_Workers] do
command := "magma worker.m > logs/worker-" cat IntegerToString(i) cat ".log 2 &";
System(command);
end for;

print "Workers started. Beginning computation...";
Z := DistributedManager(socket, work_items);

L := [z: z in Z];

delete Z;

// System ("grep error *.log");

r1 := &+[L[i][1]: i in [1..#L]];
r2 := &+[L[i][2]: i in [1..#L]];
r3 := &+[L[i][3]: i in [1..#L]];
r4 := &+[L[i][4]: i in [1..#L]];
r5 := &+[L[i][5]: i in [1..#L]];
r6 := &+[L[i][6]: i in [1..#L]];
r7 := &+[L[i][7]: i in [1..#L]];
results := [r1, r2, r3, r4, r5, r6, r7];
"Results for group", order, "#", i, " are :", results;
RESULTS := "results/Results-" cat IntegerToString (order);
PrintFileMagma (RESULTS, results);

output := Pipe("grep -h 'Total time:' logs/worker*-*.log | awk '{sum += $3} END {print sum}'", "");
total_time := eval StripWhiteSpace(output);  // Evaluates as a rational
printf "CPU time for manager is %.2o seconds\n", manager_time;
printf "Total CPU time across all workers: %.2o seconds\n", total_time;

quit;

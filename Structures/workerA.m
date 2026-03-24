TransSubs := function (params)
   n,i := Explode(params);
   "\n *** n is ", n;
   N := SmallGroup (n, i);
   hol, f := Holomorph (N);
   N:=f(N);
   t := Subgroups (hol : OrderMultipleOf := n, IsTransitive := true);
   I := [<x`subgroup, x`length, N, hol, i>: x in t];
//   I := [<x`subgroup,x`length>: x in t];
   return I;
end function;

host := "host.name";// needs to be same as for manager
port := 10000;
DistributedWorker(host, port, TransSubs);
quit;

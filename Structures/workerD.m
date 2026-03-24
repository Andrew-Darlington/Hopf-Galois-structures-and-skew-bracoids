NumOfType := function (params)
   EquivClass,size,n := Explode(params);
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
   return <size,EquivClass[j-1][4][1],HGS_Sbracoid_list>;
end function;
 
host := "host.name";// needs to be same as for manager
port := 10600;
DistributedWorker (host, port, NumOfType);
quit;

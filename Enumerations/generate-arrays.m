// Magma script to generate ORDERS and M_VALUES arrays for parent script

//x := 2; y:=31;
//x := 33; y := 47;

list := [2..15];
//Exclude (~list, 128);
//Exclude (~list, 160);
//Exclude (~list, 192);

//printf "Generating arrays for orders %o to %o\n\n", x, y;

// Build the arrays
orders := [];
m_values := [];

for order in list do
    num_groups := NumberOfSmallGroups(order);
    Append(~orders, order);
    Append(~m_values, num_groups);
end for;

// Print in bash array format
printf "# Paste these lines into your parent script:\n";
printf "ORDERS=(";
for i in [1..#orders] do
    printf "%o", orders[i];
    if i lt #orders then
        printf " ";
    end if;
end for;
printf ")\n";

printf "M_VALUES=(";
for i in [1..#m_values] do
    printf "%o", m_values[i];
    if i lt #m_values then
        printf " ";
    end if;
end for;
printf ")\n\n";

quit;

output := Pipe("grep -h 'Total CPU time across' logs/manager-*.log | awk '{sum += $7} END {printf \"%.0f\", sum}'", "");
grand_total := StringToInteger(StripWhiteSpace(output));
printf "Grand total CPU time: %o seconds\n", grand_total;

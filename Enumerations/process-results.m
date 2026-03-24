// read data from each file in results and report column sums 
// for each group order n 

// the display produced for each degree n corresponds to the relevant line 
// for given degree n in the enumeration table but beware: 
// the ordering of the data is the following and differs from 
// that listed in the table
// 
// Total   Regular  AC     BC     Total      Regular      AC           
// #HGS     #Gal    #HGS  #HGS  #Sbracoids  #Sbraces    #Sbracoids 

ReportResult := function (filename)

// Read the entire file as a string
file_content := Read(filename);

// Split into lines manually
lines := [];
current_line := "";
for i in [1..#file_content] do
    if file_content[i] eq "\n" then
        if #current_line gt 0 then
            Append(~lines, current_line);
        end if;
        current_line := "";
    else
        current_line cat:= file_content[i];
    end if;
end for;
// Don't forget the last line if file doesn't end with newline
if #current_line gt 0 then
    Append(~lines, current_line);
end if;

// Initialize column sums
num_cols := 0;
col_sums := [];

// Process each line
for line in lines do
    // Skip empty lines or lines without data
    if #line eq 0 or Position(line, "[") eq 0 then
        continue;
    end if;
    
    // Find the position of the pipe character
    pipe_pos := Position(line, "|");
    if pipe_pos eq 0 then
        continue;
    end if;
    
    // Extract everything after the pipe and before the closing bracket
    bracket_pos := Position(line, "]");
    if bracket_pos eq 0 then
        continue;
    end if;
    
    // Get the substring with just the numbers
    numbers_str := Substring(line, pipe_pos + 1, bracket_pos - pipe_pos - 1);
    
    // Remove spaces
    cleaned := "";
    for i in [1..#numbers_str] do
        if numbers_str[i] ne " " then
            cleaned cat:= numbers_str[i];
        end if;
    end for;
    
    // Split by comma and convert to integers
    nums := Split(cleaned, ",");
    row := [StringToInteger(n) : n in nums | n ne ""];
    
    // Initialize column sums on first row
    if #col_sums eq 0 then
        num_cols := #row;
        col_sums := [0 : i in [1..num_cols]];
    end if;
    
    // Add to column sums
    for i in [1..#row] do
        col_sums[i] +:= row[i];
    end for;
end for;

return col_sums;
end function;


string1 := "Total | Regular  | AC   | BC   | Total      |  Regular  | AC";        
string2 := "#HGS  |  #Gal    | #HGS | #HGS | #Sbracoids |  #Sbraces | #Sbracoids"; 

"Data for each degree n is displayed in following sequence:";
string1;
string2;
"\n";

// set first and last 
first := 2; last := 16; 
for n in [first..last] do
if n in {64, 96} then continue; end if;
str := IntegerToString (n);
filename := "results/Results-" cat str;
result := ReportResult (filename);
"n = ", n, result;
end for;

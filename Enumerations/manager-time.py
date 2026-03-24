#!/usr/bin/env python3
"""
Script to extract and sum CPU times from log files.
Searches for lines matching "CPU time for manager is X.XX seconds"
Supports file patterns like manager*.log
"""

import re
import sys
import glob

def extract_cpu_times_from_file(file_path):
    """Extract all CPU times from a single file."""
    pattern = r'CPU time for manager is ([\d.]+) seconds'
    times = []
    
    try:
        with open(file_path, 'r') as f:
            for line in f:
                match = re.search(pattern, line)
                if match:
                    times.append(float(match.group(1)))
        return times
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return []

def format_time(seconds):
    """Convert seconds to hours:minutes:seconds format."""
    hours = int(seconds // 3600)
    minutes = int((seconds % 3600) // 60)
    secs = seconds % 60
    return f"{hours}h {minutes}m {secs:.2f}s"

def main():
    if len(sys.argv) < 2:
        print("Usage: python cpu_time_sum.py <file_pattern>")
        print("Examples:")
        print("  python cpu_time_sum.py manager*.log")
        print("  python cpu_time_sum.py manager-10.log")
        print("  python cpu_time_sum.py logs/manager*.log")
        sys.exit(1)
    
    pattern = sys.argv[1]
    
    # Expand the file pattern
    files = sorted(glob.glob(pattern))
    
    if not files:
        print(f"No files found matching pattern: {pattern}")
        sys.exit(1)
    
    print(f"Found {len(files)} file(s) matching '{pattern}'")
    print("-" * 50)
    
    all_times = []
    file_summaries = []
    
    for file_path in files:
        times = extract_cpu_times_from_file(file_path)
        if times:
            file_total = sum(times)
            all_times.extend(times)
            file_summaries.append((file_path, len(times), file_total))
            print(f"{file_path}: {len(times)} entries, {file_total:.2f}s total")
    
    if not all_times:
        print("\nNo CPU times found in any files.")
        return
    
    print("\n" + "=" * 50)
    print(f"SUMMARY")
    print("=" * 50)
    print(f"Total files processed:  {len(file_summaries)}")
    print(f"Total CPU time entries: {len(all_times)}")
    print(f"Total CPU time:         {sum(all_times):.2f} seconds")
    print(f"Equivalent to:          {format_time(sum(all_times))}")
    print("=" * 50)
    
    # Optional: show statistics
    if all_times:
        print(f"\nStatistics:")
        print(f"  Min time:  {min(all_times):.2f}s")
        print(f"  Max time:  {max(all_times):.2f}s")
        print(f"  Avg time:  {sum(all_times)/len(all_times):.2f}s")

if __name__ == "__main__":
    main()

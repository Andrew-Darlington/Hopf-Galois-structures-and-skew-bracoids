import re
import json
from pathlib import Path
from collections import defaultdict

class MagmaLogExtractor:
    def __init__(self, log_dir):
        """Extract results and timing info from Magma manager log files."""
        self.log_dir = Path(log_dir)
        self.group_data = {}  # Keyed by (group_order, group_number)
    
    def extract_from_file(self, filepath):
        """Extract all relevant information from a single log file."""
        try:
            with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            
            data = {'filename': filepath.name}
            
            # Extract "Results for group" information
            results_pattern = r'Results for group\s+(\d+)\s+#\s+(\d+)\s+are\s*:\s*\[\s*([\d,\s]+)\s*\]'
            results_match = re.search(results_pattern, content)
            
            if results_match:
                data['group_order'] = int(results_match.group(1))
                data['group_number'] = int(results_match.group(2))
                numbers_str = results_match.group(3)
                data['results_array'] = [int(x.strip()) for x in numbers_str.split(',')]
            
            # Extract manager CPU time
            manager_pattern = r'CPU time for manager is\s+([\d.]+)\s+seconds'
            manager_match = re.search(manager_pattern, content)
            if manager_match:
                data['manager_time'] = float(manager_match.group(1))
            
            # Extract total worker CPU time
            worker_pattern = r'Total CPU time across all workers:\s+([\d.]+)\s+seconds'
            worker_match = re.search(worker_pattern, content)
            if worker_match:
                data['worker_time'] = float(worker_match.group(1))
            
            return data if 'group_order' in data else None
            
        except Exception as e:
            print(f"Error reading {filepath}: {e}")
            return None
    
    def extract_all(self, pattern="logs/manager*.log"):
        """Extract information from all manager log files."""
        log_files = sorted(self.log_dir.glob(pattern))
        
        if not log_files:
            print(f"No files matching '{pattern}' found in {self.log_dir}")
            return
        
        for log_file in log_files:
            data = self.extract_from_file(log_file)
            if data:
                key = (data['group_order'], data['group_number'])
                self.group_data[key] = data
        
        print(f"Extracted data from {len(self.group_data)} files\n")
    
    def calculate_totals(self):
        """Calculate sums across all groups."""
        if not self.group_data:
            return None
        
        totals = {
            'total_manager_time': 0,
            'total_worker_time': 0,
            'total_results': None,
            'num_groups': len(self.group_data)
        }
        
        # Determine the length of results arrays
        first_data = next(iter(self.group_data.values()))
        if 'results_array' in first_data:
            array_length = len(first_data['results_array'])
            totals['total_results'] = [0] * array_length
        
        # Sum everything
        for data in self.group_data.values():
            if 'manager_time' in data:
                totals['total_manager_time'] += data['manager_time']
            
            if 'worker_time' in data:
                totals['total_worker_time'] += data['worker_time']
            
            if 'results_array' in data and totals['total_results'] is not None:
                for i, val in enumerate(data['results_array']):
                    if i < len(totals['total_results']):
                        totals['total_results'][i] += val
        
        totals['grand_total_time'] = totals['total_manager_time'] + totals['total_worker_time']
        
        return totals
    
    def print_report(self):
        """Print comprehensive report."""
        if not self.group_data:
            print("No data to report")
            return
        
        print("=" * 80)
        print("MAGMA LOG EXTRACTION REPORT")
        print("=" * 80)
        print()
        
        # Determine the common group_order
        group_orders = set(data['group_order'] for data in self.group_data.values())
        if len(group_orders) == 1:
            print(f"Group Order: {group_orders.pop()}")
        else:
            print(f"Warning: Multiple group orders found: {sorted(group_orders)}")
        print()
        
        # Report for each group
        print("INDIVIDUAL GROUP RESULTS:")
        print("-" * 80)
        
        for (order, number), data in sorted(self.group_data.items()):
            print(f"\nGroup {order} #{number}")
            
            if 'results_array' in data:
                print(f"  Results: {data['results_array']}")
            
            if 'manager_time' in data:
                print(f"  Manager time:  {data['manager_time']:>8.2f} seconds")
            
            if 'worker_time' in data:
                print(f"  Worker time:   {data['worker_time']:>8.2f} seconds")
            
            if 'manager_time' in data and 'worker_time' in data:
                total = data['manager_time'] + data['worker_time']
                print(f"  Total time:    {total:>8.2f} seconds")
        
        # Print totals
        print()
        print("=" * 80)
        print("TOTALS ACROSS ALL GROUPS:")
        print("=" * 80)
        
        totals = self.calculate_totals()
        
        print(f"\nNumber of groups: {totals['num_groups']}")
        
        if totals['total_results']:
            print(f"\nSum of results arrays: {totals['total_results']}")
        
        print(f"\nTotal manager time:  {totals['total_manager_time']:>10.2f} seconds")
        print(f"Total worker time:   {totals['total_worker_time']:>10.2f} seconds")
        print(f"Grand total time:    {totals['grand_total_time']:>10.2f} seconds")
        print()
    
    def save_report(self, output_file=None):
        """Save report to a text file."""
        import sys
        from io import StringIO
        
        # Determine output filename from group order if not specified
        if output_file is None:
            if not self.group_data:
                output_file = "reports/magma_report.txt"
            else:
                # Get group order from first entry
                first_data = next(iter(self.group_data.values()))
                order = first_data.get('group_order', 'unknown')
                output_file = f"reports/Report-{order}.txt"
        
        # Capture print output
        old_stdout = sys.stdout
        sys.stdout = report_output = StringIO()
        
        self.print_report()
        
        sys.stdout = old_stdout
        report_text = report_output.getvalue()
        
        # Write to file
        with open(output_file, 'w') as f:
            f.write(report_text)
        
        print(f"Report saved to {output_file}")
        
        return report_text
    
    def to_json(self, filepath="magma_data.json"):
        """Save all data including totals to JSON."""
        output = {
            'individual_groups': [],
            'totals': self.calculate_totals()
        }
        
        for (order, number), data in sorted(self.group_data.items()):
            output['individual_groups'].append({
                'group_order': order,
                'group_number': number,
                'filename': data['filename'],
                'results_array': data.get('results_array'),
                'manager_time': data.get('manager_time'),
                'worker_time': data.get('worker_time'),
                'total_time': (data.get('manager_time', 0) + data.get('worker_time', 0))
            })
        
        with open(filepath, 'w') as f:
            json.dump(output, f, indent=2)
        
        print(f"Data saved to {filepath}")


# Main execution
if __name__ == "__main__":
    # Initialize extractor
    extractor = MagmaLogExtractor(log_dir=".")
    
    # Extract from all manager*.log files
    extractor.extract_all(pattern="logs/manager*.log")
    
    # Print report to console
    # extractor.print_report()
    
    # Optionally save outputs
    extractor.save_report()  # Will automatically use Report-{order}.txt
    extractor.to_json("magma_data.json")

# compare_files_ignore_time.py

import re

file1 = "no_pred.txt"
file2 = "with_pred.txt"

# Regex to remove "Time <number>:" prefix
time_re = re.compile(r'^Time \d+: ?')

with open(file1) as f1, open(file2) as f2:
    for lineno, (line1, line2) in enumerate(zip(f1, f2), start=1):
        # Remove time prefix
        l1_clean = time_re.sub('', line1).strip()
        l2_clean = time_re.sub('', line2).strip()
        
        if l1_clean != l2_clean:
            print(f"First difference at line {lineno}:")
            print(f"  {file1}: {l1_clean}")
            print(f"  {file2}: {l2_clean}")
            break
    else:
        print("Files are identical (ignoring time) up to the length of the shorter file.")

import os
import subprocess
import csv
import re
import time

# Base directories containing all benchmark folders
BASE_DIRS = [r"examples\JAVA-SVCOM", r"examples\C-SVCOM"]

# JayHorn + Z3 paths
NATIVE_LIB = r"C:\am21\Float_Z3_jayhorn\jayhorn\jayhorn\native_lib"
JAYHORN_JAR = r"C:\am21\Float_Z3_jayhorn\jayhorn\jayhorn\build\libs\jayhorn.jar"

# CSV file to store results
csv_file_path = 'benchmark_results.csv'
csv_headers = ['Benchmark Name', 'Total Execution Time (ms)', 'Result', 'Solver Time (ms)']

benchmarks_data = []

# Run benchmarks
for base_dir in BASE_DIRS:
    for folder_name in os.listdir(base_dir):
        folder_path = os.path.join(base_dir, folder_name)

        if not os.path.isdir(folder_path):
            continue

        classes_dir = os.path.join(folder_path, "classes")
        src_dir = os.path.join(folder_path, "src")

        if not (os.path.isdir(classes_dir) and os.path.isdir(src_dir)):
            continue

        print(f"▶ Running JayHorn on: {folder_name}")

        cmd = [
            "java",
            f"-Djava.library.path={NATIVE_LIB}",
            "-jar", JAYHORN_JAR,
            "-j", classes_dir,
            "-src", src_dir,
            "-rounding-encoding", "loop-based",
            "-normalization-encoding", "loop-based",
            "-solver", "spacer",
            "-solution",
            "-full-cex",
            "-print-horn",
        ]

        env = os.environ.copy()
        env["PATH"] = NATIVE_LIB + ";" + env["PATH"]

        start_time = time.time()
        process = subprocess.Popen(
            cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            env=env, text=True
        )

        process_output = [line for line in process.stdout]
        process.wait()
        end_time = time.time()

        # Defaults
        result = "UNKNOWN"
        solver_time_ms = None
        total_time_ms = (end_time - start_time) * 1000

        # Parse output
        for line in process_output:
            # Look for "Spacer takes ..."
            if "Spacer takes" in line:
                match = re.search(r'([\d.]+)\s*ms', line)
                if match:
                    solver_time_ms = float(match.group(1))

            # Result: SAFE or UNSAFE
            if line.strip() in ("SAFE", "UNSAFE"):
                result = line.strip()

            # Total time in secs (from JayHorn "Total time: x.xxx secs")
            if "Total time:" in line:
                match = re.search(r'([\d.]+)\s*secs', line)
                if match:
                    total_time_ms = float(match.group(1)) * 1000

        benchmarks_data.append([
            folder_name,
            round(total_time_ms, 2),
            result,
            solver_time_ms if solver_time_ms is not None else ""
        ])

        print(f"  ✔ {folder_name} -> {result}, total={round(total_time_ms,2)} ms, solver={solver_time_ms or 'N/A'}")

# Write results to CSV
with open(csv_file_path, mode='w', newline='', encoding='utf-8') as file:
    writer = csv.writer(file)
    writer.writerow(csv_headers)
    writer.writerows(benchmarks_data)

print(f"\n✅ All benchmarks processed. Results saved to {csv_file_path}")

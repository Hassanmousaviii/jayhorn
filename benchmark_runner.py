import os
import subprocess
import csv
import re
import time
from concurrent.futures import ProcessPoolExecutor, as_completed

# --- CONFIGURATION ---
BASE_DIRS = [r"examples\JAVA-SVCOM", r"examples\C-SVCOM"]
NATIVE_LIB = r"C:\am21\Float_Z3_jayhorn\jayhorn\jayhorn\native_lib"
JAYHORN_JAR = r"C:\am21\Float_Z3_jayhorn\jayhorn\jayhorn\build\libs\jayhorn.jar"
CSV_FILE_PATH = 'benchmark_results.csv'

TIMEOUT_SECONDS = 2 * 60
MAX_WORKERS = 1

LOOP_BASED = "loop-based"
LOOP_FREE = "loop-free"
ENCODINGS = [LOOP_BASED, LOOP_FREE]


def run_benchmark(task_info):
    """Run a single benchmark with specific encodings and save its output."""
    base_dir, folder_name, rounding_enc, norm_enc = task_info
    folder_path = os.path.join(base_dir, folder_name)

    classes_dir = os.path.join(folder_path, "classes")
    src_dir = os.path.join(folder_path, "src")
    
    # Create unique output file names so the 4 runs don't overwrite each other
    output_filename = f"output_R_{rounding_enc}_N_{norm_enc}.txt"
    output_file_path = os.path.join(folder_path, output_filename)

    # Validate folders
    if not (os.path.isdir(classes_dir) and os.path.isdir(src_dir)):
        return None

    cmd = [
        "java",
        f"-Djava.library.path={NATIVE_LIB}",
        "-jar", JAYHORN_JAR,
        "-j", classes_dir,
        "-src", src_dir,
        "-rounding-encoding", rounding_enc,
        "-normalization-encoding", norm_enc,
        "-solver", "spacer",
        # "-solution",
        # "-full-cex",
        # "-print-horn",
    ]

    env = os.environ.copy()
    env["PATH"] = NATIVE_LIB + ";" + env["PATH"]

    result = "UNKNOWN"
    solver_time_ms = ""
    total_time_ms = 0.0
    stdout = ""

    start_wall_clock = time.time()

    try:
        process = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            env=env,
            text=True,
            encoding='utf-8',
            errors='replace'
        )

        try:
            stdout, _ = process.communicate(timeout=TIMEOUT_SECONDS)
            end_wall_clock = time.time()
            total_time_ms = (end_wall_clock - start_wall_clock) * 1000

            for line in stdout.splitlines():
                # --- UPDATED PARSING LOGIC FOR SOLVER TIME ---
                if "Spacer takes" in line:
                    # Captures the numeric value AND the unit following it
                    match = re.search(r'Spacer takes\s+([\d.]+)\s*(\S+)', line)
                    if match:
                        val = float(match.group(1))
                        unit = match.group(2).lower()
                        
                        # Convert parsed time to milliseconds (ms)
                        if unit == "ms":
                            solver_time_ms = str(val)
                        # elif unit in ["?s", "us", "μs"]:
                        #     # Convert microseconds to milliseconds
                        #     solver_time_ms = str(round(val / 1000.0, 5))
                        elif unit in ["?s","s", "sec", "secs"]:
                            # Convert seconds to milliseconds
                            solver_time_ms = str(round(val * 1000.0, 2))
                        else:
                            # Fallback just in case an unknown unit appears
                            solver_time_ms = f"{val} {unit}"

                clean_line = line.strip()
                if clean_line in ("SAFE", "UNSAFE"):
                    result = clean_line

                if "Total time:" in line:
                    match = re.search(r'([\d.]+)\s*secs', line)
                    if match:
                        total_time_ms = float(match.group(1)) * 1000

        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()
            result = "TIMEOUT"
            total_time_ms = TIMEOUT_SECONDS * 1000
            stdout += "\n\n=== TIMEOUT ===\nBenchmark exceeded time limit."

    except Exception as e:
        result = "ERROR"
        stdout += f"\n\n=== ERROR ===\n{str(e)}"

    # Write specific run output inside the benchmark folder
    try:
        with open(output_file_path, "w", encoding="utf-8", errors="replace") as f:
            f.write(stdout)
    except Exception as e:
        print(f"Warning: Failed to write {output_filename} for {folder_name}: {e}")

    return [folder_name, rounding_enc, norm_enc, round(total_time_ms, 2), result, solver_time_ms]


def main():
    tasks = []
    for b_dir in BASE_DIRS:
        if not os.path.exists(b_dir):
            print(f"Warning: Directory not found: {b_dir}")
            continue
        
        for folder in os.listdir(b_dir):
            # Create 4 tasks for each benchmark covering all combinations
            for rounding_enc in ENCODINGS:
                for norm_enc in ENCODINGS:
                    tasks.append((b_dir, folder, rounding_enc, norm_enc))

    print(f"Starting parallel run for {len(tasks)} tasks (4 per benchmark)...")
    print(f"Timeout set to {TIMEOUT_SECONDS // 60} minutes per benchmark task.")

    results_data = []

    with ProcessPoolExecutor(max_workers=MAX_WORKERS) as executor:
        future_to_benchmark = {
            executor.submit(run_benchmark, t): t for t in tasks
        }

        for future in as_completed(future_to_benchmark):
            res = future.result()
            if res:
                results_data.append(res)
                print(f"  Finished: {res[0]} [R: {res[1]}, N: {res[2]}] -> {res[4]} ({res[3]} ms), solver took:{res[5]} ms")

    # Added columns to reflect the configurations
    headers = ['Benchmark Name', 'Rounding', 'Normalization', 'Total Time (ms)', 'Result', 'Solver Time (ms)']
    with open(CSV_FILE_PATH, mode='w', newline='', encoding='utf-8') as file:
        writer = csv.writer(file)
        writer.writerow(headers)
        writer.writerows(results_data)

    print(f"\nAll processing complete. Results written to: {CSV_FILE_PATH}")


if __name__ == "__main__":
    main()

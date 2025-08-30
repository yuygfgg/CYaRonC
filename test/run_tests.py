import os
import subprocess
import sys
from glob import glob

# Configuration
COMPILER_PATH = "./build/cyaronc"
LLI_PATH = "lli"
TEST_DIR = "test"
OUT_LL_FILE = "out.ll"
ERR_LOG_FILE = "err.log"


def main():
    """
    Builds the compiler and runs all tests.
    """
    # Build the compiler
    print("Building the compiler...")
    try:
        # Use absolute path for build directory
        build_dir = os.path.abspath(
            os.path.join(os.path.dirname(__file__), "..", "build")
        )
        compiler_path_abs = os.path.join(build_dir, "cyaronc")

        subprocess.run(
            ["cmake", "--build", build_dir], check=True, capture_output=True, text=True
        )
    except (subprocess.CalledProcessError, FileNotFoundError) as e:
        print("Compiler build failed.")
        if isinstance(e, subprocess.CalledProcessError):
            print(e.stderr)
        else:
            print(e)
        sys.exit(1)

    print("--- Running tests ---")

    test_files = sorted(glob(os.path.join(os.path.abspath(TEST_DIR), "*.cyaron")))

    if not test_files:
        print(f"No test files found in {os.path.abspath(TEST_DIR)}")
        sys.exit(1)

    try:
        for test_file in test_files:
            run_single_test(test_file, compiler_path_abs)
    finally:
        if os.path.exists(OUT_LL_FILE):
            os.remove(OUT_LL_FILE)
        if os.path.exists(ERR_LOG_FILE):
            os.remove(ERR_LOG_FILE)

    print("--- All tests passed ---")


def run_single_test(test_file, compiler_path):
    """
    Runs a single test case.
    """
    print(f"Running {test_file}...")

    with open(test_file, "r") as f:
        expected = f.readline().lstrip("#").strip()

    is_invalid_test = "invalid" in os.path.basename(test_file)

    if is_invalid_test:
        # Expecting a non-zero exit code from the compiler
        result = subprocess.run(
            [compiler_path, test_file, OUT_LL_FILE], capture_output=True, text=True
        )

        if result.returncode == 0:
            print(f"{test_file} FAILED: Expected a non-zero exit code, but got 0")
            sys.exit(1)

        error_log = result.stderr
        with open(ERR_LOG_FILE, "w") as f:
            f.write(error_log)

        if expected in error_log:
            print(f"{test_file} PASSED")
        else:
            print(f"{test_file} FAILED: Did not find expected error message.")
            print(f"Expected to find: '{expected}'")
            print("Compiler output:")
            print(error_log)
            sys.exit(1)
    else:
        # Expecting a zero exit code from the compiler and correct output from lli
        try:
            _ = subprocess.run(
                [compiler_path, test_file, OUT_LL_FILE],
                check=True,
                capture_output=True,
                text=True,
            )
        except subprocess.CalledProcessError as e:
            print(f"{test_file} FAILED: Compiler returned a non-zero exit code.")
            print(e.stderr)
            sys.exit(1)

        try:
            lli_result = subprocess.run(
                [LLI_PATH, OUT_LL_FILE], check=True, capture_output=True, text=True
            )
            output = lli_result.stdout.strip()

            if output == expected:
                print(f"{test_file} PASSED")
            else:
                print(f"{test_file} FAILED")
                print(f"Expected: '{expected}'")
                print(f"Got:      '{output}'")
                sys.exit(1)

        except (subprocess.CalledProcessError, FileNotFoundError) as e:
            print(f"{test_file} FAILED: 'lli' execution failed.")
            if isinstance(e, subprocess.CalledProcessError):
                print(e.stderr)
            else:
                print(
                    "'lli' command not found. Please ensure LLVM is installed and in your PATH."
                )
            print(e)
            sys.exit(1)


if __name__ == "__main__":
    os.chdir(os.path.join(os.path.dirname(__file__), ".."))
    main()

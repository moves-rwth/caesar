import csv
import glob
import os
import re
import shlex
import subprocess
import time
from dataclasses import dataclass
from typing import List, Optional, Tuple


def default_caesar_path(crate_path: str) -> str:
    candidates = [
        "/usr/local/bin/caesar",
        os.path.join(crate_path, "target", "release", "caesar"),
        os.path.join(crate_path, "target", "debug", "caesar"),
    ]
    for candidate in candidates:
        if os.path.exists(candidate):
            return candidate
    return candidates[0]


CRATE_PATH = os.path.abspath(os.environ.get("CRATE_PATH", os.getcwd()))
CAESAR_PATH = os.environ.get("CAESAR_PATH", default_caesar_path(CRATE_PATH))


# ----------------------------
# ANSI colors
# ----------------------------

GREEN = "\033[92m"
RED = "\033[91m"
YELLOW = "\033[93m"
BLUE = "\033[94m"
RESET = "\033[0m"


# ----------------------------
# Command representations
# ----------------------------

class TestCommand:
    pass


@dataclass
class Run(TestCommand):
    cmd: str


@dataclass
class Xfail(TestCommand):
    cmd: str


@dataclass
class Ignore(TestCommand):
    cmd: str


# ----------------------------
# Test file parsing
# ----------------------------

@dataclass
class TestFile:
    commands: List[TestCommand]

    @staticmethod
    def parse(path: str) -> "TestFile":
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()

        regex = re.compile(r"//\s*(RUN|XFAIL|IGNORE): ([^\r\n]*)")
        commands: List[TestCommand] = []

        for match in regex.finditer(content):
            kind, arg = match.groups()

            arg = arg.replace("@caesar", CAESAR_PATH)
            arg = arg.replace("@file", path)

            if kind == "RUN":
                commands.append(Run(arg))
            elif kind == "XFAIL":
                commands.append(Xfail(arg))
            elif kind == "IGNORE":
                commands.append(Ignore(arg))

        return TestFile(commands)

    def run(self) -> Tuple[bool, Optional[float], Optional[str], Optional[str]]:
        """
        Returns:
            (success, elapsed_ms, error_message, command_str)
        """
        output = None
        command_str = None
        xfail = False
        ignore = False
        elapsed_ns = 0

        for cmd in self.commands:
            if isinstance(cmd, Run):
                if output is not None:
                    return False, None, "Test contains multiple RUN commands", None

                try:
                    args = shlex.split(cmd.cmd)
                except ValueError as e:
                    return False, None, f"Could not parse RUN command: {e}", cmd.cmd

                start = time.perf_counter_ns()
                try:
                    result = subprocess.run(
                        args,
                        capture_output=True,
                        text=True,
                        cwd=CRATE_PATH,
                    )
                except Exception as e:
                    return False, None, f"Execution failed: {e}", cmd.cmd

                elapsed_ns = time.perf_counter_ns() - start

                output = result
                command_str = cmd.cmd

            elif isinstance(cmd, Xfail):
                xfail = True

                if output is None:
                    return False, None, "XFAIL without preceding RUN", None

                if output.returncode == 0:
                    return False, None, "XFAIL command succeeded unexpectedly", command_str

            elif isinstance(cmd, Ignore):
                ignore = True

        if not xfail:
            if output is not None:
                if output.returncode != 0:
                    return (
                        False,
                        None,
                        f"Stdout:\n{output.stdout}\n\nStderr:\n{output.stderr}",
                        command_str
                    )
            elif not ignore:
                return False, None, "Test file contains no commands", None

        elapsed_ms = elapsed_ns / 1_000_000
        return True, elapsed_ms, None, command_str

    def ignored(self) -> bool:
        return any(isinstance(cmd, Ignore) for cmd in self.commands)

    def expects_failure(self) -> bool:
        return any(isinstance(cmd, Xfail) for cmd in self.commands)


# ----------------------------
# Test discovery + runner
# ----------------------------

def get_test_name(path: str) -> str:
    return os.path.relpath(path, CRATE_PATH)

def main():
    pattern = os.path.join(CRATE_PATH, "tests", "**", "*.heyvl")
    test_files = sorted(glob.glob(pattern, recursive=True))

    results = []

    csv_path = os.path.join(CRATE_PATH, "benchmark-results.csv")
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["name", "status", "runtime_ms"])

        for path in test_files:
            name = get_test_name(path)

            test = TestFile.parse(path)

            if test.ignored():
                print(f"{BLUE}[SKIP]{RESET} {name}")
                results.append((name, "skipped", None))
                writer.writerow([name, "skipped", ""])
                continue

            # Print RUNNING without newline
            print(f"{YELLOW}[RUNNING]{RESET} {name} ...", end="", flush=True)

            success, elapsed_ms, error, command = test.run()
            expects_failure = test.expects_failure()

            # Clear the line and return carriage
            print("\r\033[K", end="")  # \033[K clears the line

            if success:
                if expects_failure:
                    status = "xfailed"
                    label = "XFAIL"
                    color = GREEN
                else:
                    status = "passed"
                    label = "PASS"
                    color = GREEN

                print(f"{color}[{label}]{RESET} {name} ({elapsed_ms:.3f} ms)")
                if command:
                    print(f"  ↳ {command}")
                results.append((name, status, elapsed_ms))
                writer.writerow([name, status, f"{elapsed_ms:.3f}"])

            else:
                print(f"{RED}[FAIL]{RESET} {name}")
                if command:
                    print(f"  ↳ {command}")
                if error:
                    print(error)
                results.append((name, "failed", None))
                writer.writerow([name, "failed", ""])

    # Summary
    total = len(results)
    passed = sum(1 for r in results if r[1] == "passed")
    xfailed = sum(1 for r in results if r[1] == "xfailed")
    failed = sum(1 for r in results if r[1] == "failed")
    skipped = sum(1 for r in results if r[1] == "skipped")

    print("\n--- Summary ---")
    print(f"Total:  {total}")
    print(f"{GREEN}Passed:{RESET} {passed}")
    print(f"{GREEN}XFailed:{RESET} {xfailed}")
    print(f"{RED}Failed:{RESET} {failed}")
    print(f"{BLUE}Skipped:{RESET} {skipped}")

    print(f"\nResults written to {csv_path}")
    if failed > 0:
        exit(1)


if __name__ == "__main__":
    main()

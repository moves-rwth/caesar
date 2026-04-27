import os
import glob
import re
import shlex
import subprocess
import time
from dataclasses import dataclass
from typing import List, Optional, Tuple

CRATE_PATH = os.environ.get("CRATE_PATH", os.getcwd())
CAESAR_PATH = os.environ.get("CAESAR_PATH", "target/debug/caesar")


# ----------------------------
# ANSI colors
# ----------------------------

GREEN = "\033[92m"
RED = "\033[91m"
YELLOW = "\033[93m"
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

        regex = re.compile(r"//\s*(RUN|XFAIL|IGNORE): (.*)")
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

                args = shlex.split(cmd.cmd)

                start = time.perf_counter_ns()
                try:
                    result = subprocess.run(
                        args,
                        capture_output=True,
                        text=True
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


# ----------------------------
# Test discovery + runner
# ----------------------------

def get_test_name(path: str) -> str:
    return os.path.relpath(path, CRATE_PATH)

def main():
    pattern = os.path.join(CRATE_PATH, "tests", "**", "*.heyvl")
    test_files = glob.glob(pattern, recursive=True)

    results = []

    for path in test_files:
        name = get_test_name(path)

        # Print RUNNING without newline
        print(f"{YELLOW}[RUNNING]{RESET} {name} ...", end="", flush=True)

        test = TestFile.parse(path)
        success, elapsed_ms, error, command = test.run()

        # Clear the line and return carriage
        print("\r\033[K", end="")  # \033[K clears the line

        if success:
            print(f"{GREEN}[PASS]{RESET} {name} ({elapsed_ms:.3f} ms)")
            if command:
                print(f"  ↳ {command}")
            results.append((name, True, elapsed_ms))
        else:
            print(f"{RED}[FAIL]{RESET} {name}")
            if command:
                print(f"  ↳ {command}")
            if error:
                print(error)
            results.append((name, False, None))

    # Summary
    total = len(results)
    passed = sum(1 for r in results if r[1])
    failed = total - passed

    print("\n--- Summary ---")
    print(f"Total:  {total}")
    print(f"{GREEN}Passed:{RESET} {passed}")
    print(f"{RED}Failed:{RESET} {failed}")

    if failed > 0:
        exit(1)


if __name__ == "__main__":
    main()
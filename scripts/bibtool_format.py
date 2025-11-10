#!/usr/bin/env python
import subprocess
import sys
import hashlib
from enum import Enum
from pathlib import Path


class ProcessResult(Enum):
    SUCCESS_FORMATTED = "formatted"
    SUCCESS_UNCHANGED = "unchanged"
    ERROR = "error"


BIBTOOL_ARGS = [
    "--preserve.key.case=on",
    "--preserve.keys=on",
    "--pass.comments=on",
    "--print.use.tab=off",
    "-s",
]


def file_hash(file: Path) -> str | None:
    try:
        with open(file, "rb") as f:
            content = f.read()
        return hashlib.sha256(content).hexdigest()
    except FileNotFoundError:
        print(f"Error: File not found: {file}", file=sys.stderr)
        return None
    except PermissionError:
        print(f"Error: Permission denied: {file}", file=sys.stderr)
        return None
    except OSError as e:
        print(f"Error reading {file}: {e}", file=sys.stderr)
        return None


def bibtool_format_file(file: Path) -> ProcessResult:
    original_hash = file_hash(file)
    if original_hash is None:
        return ProcessResult.ERROR

    process: subprocess.CompletedProcess[str] = subprocess.run(
        ["bibtool", *BIBTOOL_ARGS, "-i", str(file), "-o", str(file)],
        capture_output=True,
        text=True,
    )

    if process.returncode != 0:
        print(f"Failed: {file}", file=sys.stderr)
        if process.stderr:
            print(f"Error output: {process.stderr}", file=sys.stderr)
        return ProcessResult.ERROR

    new_hash = file_hash(file)
    if new_hash is None:
        return ProcessResult.ERROR

    if original_hash != new_hash:
        print(f"Formatted: {file}")
        return ProcessResult.SUCCESS_FORMATTED

    return ProcessResult.SUCCESS_UNCHANGED


def bibtool_format(files: list[Path]) -> int:
    print(f"Checking style in {len(files)} files with bibtool.")

    formatted_files: list[Path] = []
    failed_files: list[Path] = []

    for file in files:
        result = bibtool_format_file(file)
        if result == ProcessResult.SUCCESS_FORMATTED:
            formatted_files.append(file)
        elif result == ProcessResult.ERROR:
            failed_files.append(file)

    if formatted_files:
        print(f"\nFormatted {len(formatted_files)} file(s):")
        for file in formatted_files:
            print(f"  - {file}")

    if failed_files:
        print(f"\nFailed to process {len(failed_files)} file(s):", file=sys.stderr)
        for file in failed_files:
            print(f"  - {file}", file=sys.stderr)

    return 1 if failed_files else 0


def main() -> None:
    file_args: list[str] = sys.argv[1:]
    if not file_args:
        print("Usage: bibtool_format.py <file1.bib> <file2.bib> ...", file=sys.stderr)
        sys.exit(1)

    files: list[Path] = [Path(f) for f in file_args]
    sys.exit(bibtool_format(files))


if __name__ == "__main__":
    main()

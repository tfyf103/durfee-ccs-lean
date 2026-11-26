"""Check the published file digests from any working directory."""

from hashlib import sha256
from pathlib import Path, PurePosixPath
import sys


root = Path(__file__).resolve().parents[1]
checked = set()
for entry in (root / "SHA256SUMS").read_text(encoding="utf-8").splitlines():
    expected, separator, filename = entry.partition("  ")
    relative = PurePosixPath(filename)
    if (not separator or not filename or relative.is_absolute() or ".." in relative.parts
            or "\\" in filename or ":" in filename or filename in checked):
        sys.exit(f"Invalid checksum entry: {entry}")
    path = root.joinpath(*relative.parts)
    if sha256(path.read_bytes()).hexdigest() != expected:
        sys.exit(f"SHA-256 mismatch: {filename}")
    checked.add(filename)

if not checked:
    sys.exit("The checksum manifest is empty.")
print(f"SHA-256 verified for {len(checked)} files.")

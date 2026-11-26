# Durfee polynomials and the Canfield–Corteel–Savage conjecture in Lean

This repository contains the Lean 4 formalization of *Real zeros of Durfee polynomials: Proof of the Canfield–Corteel–Savage conjecture*, manuscript version v28. The main proof is in [DurfeeCCS/Main.lean](DurfeeCCS/Main.lean). [Theorem and equation index](review/theorems.md) maps the conjecture, all 17 numbered results, and equation (14) to Lean. [paper-map.tsv](paper-map.tsv) records the full correspondence, including unnumbered statements and table rows. [The audit results](review/step14/targets.tsv) also list the finite computation targets.

## Reproduce the Lean proof

Install Git and [Lean through Elan](https://lean-lang.org/install/). From a fresh clone or the extracted archive root, run the following commands in order.

```sh
lean --version
lake --version
lake exe cache get
lake build DurfeeCCS.ReviewAll
lake env leanchecker --fresh DurfeeCCS.ReviewAll
```

[lean-toolchain](lean-toolchain) pins Lean **4.36.0** (revision `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`). The tested release bundles **Lake 5.0.0-src+611c117** and **leanchecker**. [lake-manifest.json](lake-manifest.json) pins all nine dependency revisions, including mathlib at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. [Mathlib's cache command](https://github.com/leanprover-community/mathlib4#downloading-cached-build-files) downloads prebuilt dependencies. If the cache download is unavailable, Lake can build the pinned dependencies from source. The first dependency setup needs network access.

The build checks the Lean proof sources, including the bundled finite certificates. The final command rechecks the transitive import closure in a fresh kernel environment. The checker can exit successfully with empty output. In the recorded Windows x86-64 run, the clean project build took about 46 minutes with the pinned dependency cache and the kernel replay took about 63 minutes. See the [recorded commands and exit codes](review/step14-verification.txt).

## Check the source package, coverage and axioms

Use Python 3.10 or newer for these optional checks. The recorded run used Python 3.12.14 and its standard library.

```sh
python review/check_package.py
python review/check_step13.py --output repro/audit
python review/generate_step05_certificates.py review/step05-witnesses.jsonl --verify
```

The second command needs a completed Lean build. It checks the public manuscript index, the finite certificate inventory, and the types and axiom dependencies of 1,243 Lean declarations. The expected report is 495 passing targets, 19 historical or bibliographic records, and zero unverified targets or unexpected axioms. The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`. The [recorded summary](review/step14/summary.json), [types](review/step14/types.log), and [axiom output](review/step14/axioms.log) are included.

The [manuscript hashes](paper/SHA256SUMS) identify the exact PDF and TeX used for the internal source audit. This package contains the [anchor index](review/manuscript-anchors.tsv), so the commands above can run independently of the manuscript files. If you already have both exact originals, pass their containing directory to the audit's manuscript mode.

```sh
python review/check_step13.py --paper-dir path/to/manuscript --output repro/audit-with-manuscript
```

That mode verifies the exact manuscript file hashes and derives the anchors from the TeX again. On Windows, use `py -3` if the Python launcher is available in place of `python`.

## Regenerate the finite certificate sources

Run the standard-library generators into a separate directory. The raw witnesses cover $1 \le n \le 6400$. The verifier checks all 6,400 coefficient sums, 325,403 signs, and 319,011 order comparisons using exact integer arithmetic.

```sh
python review/generate_step05_certificates.py repro/witnesses.jsonl
python review/generate_step05_certificates.py repro/witnesses.jsonl --verify --shards-out repro/witness-shards.tsv
python review/generate_step05_coefficients.py --source repro/witnesses.jsonl --destination repro/lean
python review/generate_step05_shards.py repro/witnesses.jsonl --output repro/lean
```

Generated Lean sources can be compared with the corresponding files under [DurfeeCCS/Step05](DurfeeCCS/Step05). The retained per-shard build records use `lake` in place of the original absolute executable path. Their public log digests bind the redacted copies. Original source and compiled-artifact digests were retained for provenance.

## Provenance

The Lean proof files and dependency pins match internal frozen commit `fa3aea526f230e0b923522d1212583e24aa3b8ef` byte for byte. The final independent build and replay evidence came from internal commit `e91247f88239cd20ed578e8133792fe0f62938c6`. This is a standalone source snapshot with its own Git history. [SHA256SUMS](SHA256SUMS) lists the public package files.

"""Audit the public coverage index and Lean axiom dependencies after building ReviewAll."""

import argparse
import csv
import hashlib
import json
import math
import re
import subprocess
import sys
import tempfile
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

from manuscript_index import EQUATION_IDS, FIELDS, RESULT_IDS, SOURCE_DIGESTS, TABLE_ROWS

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = ("id", "coverage", "lean_names", "note")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
STATES = {"exact", "partial", "open", "reference"}
PROOF_KINDS = {"result", "conjecture", "equation", "table", "claim", "computation", "finite"}
NAME = re.compile(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)+\Z")
AXIOMS = re.compile(
    r"^'([^\r\n]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\r?$",
    re.MULTILINE,
)
KIND = re.compile(r"STEP13_DECL_KIND ([^\s]+) (theorem|other) ([^\s]+)$")
WITNESS_SHA256 = "57cd7557ee95169632c663a5685c34dcfa78f171f477f2d3975c38b55d1e330c"
NUMBERED_IDS = RESULT_IDS | {"C1.1"}
UNNUMBERED_KINDS = Counter({
    "citation": 14, "claim": 95, "computation": 13, "definition": 32, "history": 19,
})
FINITE_IDS = {
    "K05-ColumnSpecifications", "K05-Aggregate", "K05-Soundness", "K05-PartitionTotals",
    "K07-ElementaryEnclosures", "K07-FirstSaddleRows", "K07-SaddleEndpointGrid",
    "K07-SaddleInitialEndpoints", "K07-MainArcRows", "K07-MinorArcGridCover",
    "K07-MinorArcBlockArithmetic", "K07-MinorArcSmallArithmetic", "K07-MinorArcTailArithmetic",
    "K07-MinorArcRowAssembly", "K07-ModeGrid", "K07-OppositeHalfEndpoints",
    "K07-OuterTableEndpoints", "K10-OuterBesselSmall", "K10-OuterCoefficientThresholds",
    "K10-OuterPreprocessing", "K10-OuterFarNumerics", "K10-OuterPhaseEndpoints",
}


class AuditInputError(ValueError):
    """The index, manifest, or archived evidence is incomplete."""


@dataclass(frozen=True)
class Target:
    identifier: str
    kind: str
    page: str
    coverage: str
    declarations: tuple[str, ...]
    note: str


def require(condition, message):
    if not condition:
        raise AuditInputError(message)


def read_tsv(path, fields=None, key="id"):
    with path.open(encoding="utf-8-sig", newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if fields is not None:
            require(tuple(reader.fieldnames or ()) == tuple(fields), f"{path}: wrong header")
        result = {}
        for row in reader:
            require(None not in row and all(value is not None for value in row.values()),
                    f"{path}:{reader.line_num}: invalid columns")
            identity = row.get(key)
            require(identity and identity not in result, f"{path}:{reader.line_num}: duplicate/missing {key}")
            result[identity] = row
        return result


def read_manuscript_anchors(paper_dir):
    records = read_tsv(ROOT / "review" / "manuscript-anchors.tsv",
                       ("destination", "tex_anchor_line", "page"), "destination")
    anchors = {name: (int(row["tex_anchor_line"]), int(row["page"])) for name, row in records.items()}
    require(len(anchors) == 172 and all(line > 0 and 1 <= page <= 55 for line, page in anchors.values()),
            "Published anchor inventory differs from the frozen manuscript")
    if paper_dir is None:
        return anchors

    for name, digest in SOURCE_DIGESTS.items():
        require(hashlib.sha256((paper_dir / name).read_bytes()).hexdigest() == digest,
                f"Frozen manuscript hash mismatch: {name}")
    extracted = {}
    page = 0
    tex = paper_dir / "Durfee_CCS_v28.tex"
    for line_number, line in enumerate(tex.read_text(encoding="utf-8").splitlines(), 1):
        if line.strip() == r"\StartPage":
            page += 1
        match = re.match(r"^\\Destination\{paper-([^}]+)\}", line)
        if match:
            extracted[match[1]] = (line_number, page)
    require(page == 55 and extracted == anchors, "Frozen manuscript destination inventory differs")
    return anchors


def check_index(rows, paper_dir):
    by_kind = {}
    for key, row in rows.items():
        by_kind.setdefault(row["kind"], set()).add(key)
    for kind, expected in [("result", RESULT_IDS), ("conjecture", {"C1.1"}), ("equation", EQUATION_IDS)]:
        require(by_kind.get(kind) == expected, f"Numbered {kind} index differs from the manuscript")
    tables = Counter(int(rows[key]["page"]) for key in by_kind.get("table", ()))
    require(tables == TABLE_ROWS, "Printed table inventory differs from the manuscript")
    unnumbered = Counter({kind: len(entries) for kind, entries in by_kind.items()
                          if kind not in {"result", "conjecture", "equation", "table"}})
    require(unnumbered == UNNUMBERED_KINDS, "Unnumbered inventory differs from the reviewed index")
    reviewed = read_tsv(ROOT / "review" / "statement-review.tsv")
    require(rows.keys() == reviewed.keys(), "Coverage index and original statement review have different IDs")
    anchors = read_manuscript_anchors(paper_dir)
    for key, row in rows.items():
        reference = (int(row["tex_anchor_line"]), int(re.match(r"\d+", row["page"])[0]))
        require(anchors.get(row["pdf_destination"]) == reference, f"{key}: incorrect manuscript anchor")
        if row["kind"] in {"result", "conjecture"}:
            require(row["pdf_destination"] == "theorem." + key[1:], f"{key}: wrong theorem")
        if row["kind"] == "equation":
            require(row["pdf_destination"] == f"equation.{int(key[1:])}", f"{key}: wrong formula")


def read_targets(rows, reviewed):
    missing, extra = rows.keys() - reviewed.keys(), reviewed.keys() - rows.keys()
    require(not (missing or extra),
            f"Review manifest has missing IDs {sorted(missing)} and unexpected IDs {sorted(extra)}")
    targets = []
    for key, row in rows.items():
        record = reviewed[key]
        state = record["coverage"]
        require(state in STATES, f"{key}: unknown coverage status {state!r}")
        note = record["note"].strip()
        names = tuple(name.strip() for name in record["lean_names"].replace("；", ";").split(";")
                      if name.strip())
        require(len(set(names)) == len(names) and all(NAME.fullmatch(name) for name in names),
                f"{key}: duplicate or invalid qualified Lean names {names}")
        require(state != "exact" or names, f"{key}: exact coverage requires a Lean declaration")
        require(state == "exact" or note, f"{key}: {state} requires a review note")
        require(state != "reference" or row["kind"] in {"history", "citation", "claim"},
                f"{key}: cannot classify {row['kind']} as a reference")
        require(state != "reference" or row["pdf_destination"] not in
                {"theorem." + item[1:] for item in NUMBERED_IDS},
                f"{key}: numbered conclusion cannot be waived")
        targets.append(Target(key, row["kind"], row["page"], state, names, note))
    return targets


def stage05_inventory():
    """Check the archived numeric data and name every Lean block that certifies it."""
    prefix = "DurfeeCCS.Step05."
    review = ROOT / "review"
    witness_path = review / "step05-witnesses.jsonl"
    witness_data = witness_path.read_bytes()
    require(hashlib.sha256(witness_data).hexdigest() == WITNESS_SHA256, "Original witness hash differs")
    lines = witness_data.splitlines(keepends=True)
    require(len(lines) == 6400, "Original witness count differs")
    witness_fields = ("n_first", "n_last", "rows", "signs", "orderings", "partition_sums", "sha256_raw_jsonl")
    witnesses = read_tsv(review / "step05-witness-shards.tsv", witness_fields, "n_first")
    require(len(witnesses) == 100, "Expected 100 archived witness ranges")
    targets = []
    archived_modules = {}
    totals = Counter()
    for shard in range(100):
        lo, hi = 64 * shard + 1, 64 * (shard + 1)
        row = witnesses.get(str(lo))
        require(row is not None, f"Missing witness range {lo} to {hi}")
        block = lines[lo - 1:hi]
        expected_signs = sum(max(0, math.isqrt(n) - 2) for n in range(lo, hi + 1))
        expected_orderings = sum(max(0, math.isqrt(n) - 3) for n in range(lo, hi + 1))
        observed = tuple(int(row[name]) for name in witness_fields[:-1])
        require(observed == (lo, hi, 64, expected_signs, expected_orderings, 64),
                f"Incorrect witness counts in {lo} to {hi}")
        require(hashlib.sha256(b"".join(block)).hexdigest() == row["sha256_raw_jsonl"],
                f"Incorrect witness shard hash in {lo} to {hi}")
        totals.update({"rows": 64, "signs": expected_signs, "orderings": expected_orderings,
                       "partition_sums": 64})
        suffix = f"{shard:03d}"
        for category in ("Shard", "Range"):
            archived_modules[prefix + category + suffix] = ("step05-build", str(lo), str(hi))
        targets.append(Target(
            "K05-block" + suffix, "finite", "53–54", "exact",
            tuple(prefix + name + suffix for name in ("signs", "coefficients", "coverage")),
            f"{lo} ≤ n ≤ {hi}",
        ))
    require(totals == {"rows": 6400, "signs": 325403, "orderings": 319011, "partition_sums": 6400},
            "Global certificate counts differ")
    for group in range(1, 11):
        archived_modules[prefix + f"CoeffCheck{group:02d}"] = ("step05-coeff-build", "", "")
    archived_modules[prefix + "Columns"] = ("step05-coeff-build", "", "")
    ledger = read_tsv(review / "step05-kernel-shards.tsv", key="module")
    require(ledger.keys() == archived_modules.keys(), "Archived Stage 05 kernel module inventory differs")
    for name, (directory, lo, hi) in archived_modules.items():
        row = ledger[name]
        record_dir = review / directory
        metadata = json.loads((record_dir / f"{name}.json").read_text(encoding="utf-8"))
        require((row["lower_n"], row["upper_n"], row["exit_code"]) == (lo, hi, "0")
                and metadata["exit_code"] == 0 and metadata["module"] == name,
                f"{name}: archived record does not confirm successful checking")
        source = ROOT.joinpath(*name.split(".")).with_suffix(".lean")
        log = record_dir / f"{name}.log"
        for key, path in (("source_sha256", source), ("log_sha256", log)):
            require(hashlib.sha256(path.read_bytes()).hexdigest() == row[key] == metadata[key],
                    f"{name}: archived {key} mismatch")
        require(metadata["artifact_sha256"] == row["artifact_sha256"],
                f"{name}: archived artifact hash mismatch")
    for column in range(1, 81):
        name = prefix + f"coefficientColumn{column}"
        targets.append(Target(
            f"K05-coeffColumn{column:02d}", "finite", "53–54", "exact",
            (name + "_checked", name + "_spec", name + "_length"), f"Durfee coefficient column d={column}",
        ))
    return targets, {**totals, "n_min": 1, "n_max": 6400, "blocks": 100, "kernel_records": len(ledger),
                     "coefficient_columns": 80}


KIND_COMMAND = """
open Lean Elab Command
elab "#step13_decl_kind " identifier:ident : command => do
  let name := identifier.getId
  let env ← getEnv
  let some info := env.find? name
    | throwError "unknown constant '{name}'"
  let kind := match info with
    | .thmInfo _ => "theorem"
    | _ => "other"
  let sourceModule := match env.getModuleIdxFor? name with
    | some index => env.allImportedModuleNames[index.toNat]!
    | none => env.mainModule
  logInfo m!"STEP13_DECL_KIND {name} {kind} {sourceModule}"
set_option pp.fullNames true
"""


def source_text(import_name, declarations, phase, preamble):
    source = [f"import {import_name}", "", preamble]
    if phase == "types":
        source.append(KIND_COMMAND)
        for name in declarations:
            source.extend((f"#step13_decl_kind {name}", f"#check {name}"))
    else:
        source.extend(f"#print axioms {name}" for name in declarations)
    return "\n".join(source) + "\n"


def run_lean(lake, declarations, output, import_name="DurfeeCCS.ReviewAll", preamble=""):
    observations = {}
    exit_codes = {}
    output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="input-", dir=output) as temp:
        for phase in ("axioms", "types"):
            source = Path(temp) / ("Step13" + phase.title() + ".lean")
            source.write_text(source_text(import_name, declarations, phase, preamble), encoding="utf-8")
            result = subprocess.run([lake, "env", "lean", str(source)], cwd=ROOT,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)
            stdout = result.stdout.decode("utf-8", errors="replace")
            # Preserve the complete output and give errors a stable generated filename.
            stdout = stdout.replace(str(source), source.name).replace(source.as_posix(), source.name)
            (output / f"{phase}.log").write_bytes(stdout.encode("utf-8"))
            exit_codes[phase] = result.returncode
            parsed = {}
            matches = (AXIOMS.finditer(stdout) if phase == "axioms"
                       else (match for line in stdout.splitlines() if (match := KIND.search(line))))
            for match in matches:
                name, value, *module = match.groups()
                require(name in declarations and name not in parsed, f"{phase}: unexpected or duplicate {name}")
                parsed[name] = (frozenset(item.strip() for item in (value or "").split(",") if item.strip())
                                if phase == "axioms" else (value, module[0]))
            if result.returncode and not (parsed or "unknown constant" in stdout.lower()
                                          or "unknown identifier" in stdout.lower()):
                raise AuditInputError(f"Lean {phase} command failed. Read {output / (phase + '.log')}")
            observations[phase] = parsed
    return observations["axioms"], observations["types"], exit_codes


def classify(target, axioms, declarations):
    problems = []
    for name in target.declarations:
        if name not in axioms:
            problems.append(f"{name}: missing axiom output")
        elif axioms[name] - ALLOWED_AXIOMS:
            problems.append(f"{name}: disallowed axioms {', '.join(sorted(axioms[name] - ALLOWED_AXIOMS))}")
        if name not in declarations:
            problems.append(f"{name}: missing declaration/type output")
    if target.coverage == "exact" and target.kind in PROOF_KINDS:
        theorem_names = {name for name in target.declarations
                         if name in declarations and declarations[name][0] == "theorem"}
        if target.kind in {"result", "conjecture"}:
            if not target.declarations or target.declarations[0] not in theorem_names:
                problems.append("primary declaration of numbered conclusion must be a theorem")
        elif not theorem_names:
            problems.append("exact proposition requires at least one theorem")
    if problems:
        return "fail", problems
    return {"exact": "pass", "partial": "partial", "open": "open", "reference": "reference"}[target.coverage], []


def write_tsv(path, header, rows):
    with path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
        writer.writerow(header)
        writer.writerows(rows)


def map_comparison(target, original, modules):
    if original is None:
        return "finite_inventory"
    old_names = tuple(name.strip() for name in original["lean_name"].replace("；", ";").split(";")
                      if NAME.fullmatch(name.strip()))
    if target.declarations != old_names:
        return "reviewed_name_override"
    if old_names and modules.get(old_names[0], "").startswith("DurfeeCCS."):
        actual_source = modules[old_names[0]].replace(".", "/") + ".lean"
        if actual_source not in original["proof_location"]:
            return "reviewed_source_override"
    return "indexed"


def audit(lake, manifest, finite, output, paper_dir):
    rows = read_tsv(ROOT / "paper-map.tsv", FIELDS)
    check_index(rows, paper_dir)
    targets = read_targets(rows, read_tsv(manifest, SCHEMA))
    extra = read_tsv(finite, SCHEMA)
    require(FINITE_IDS <= extra.keys(), f"Missing finite inventory entries {sorted(FINITE_IDS - extra.keys())}")
    require(all(re.fullmatch(r"K(?:05|07|10)-[A-Za-z0-9-]+", key) for key in extra),
            "Finite supplemental IDs have an invalid prefix")
    finite_rows = {key: {"kind": "finite", "page": ""} for key in extra}
    generated, finite_summary = stage05_inventory()
    targets.extend(generated)
    targets.extend(read_targets(finite_rows, extra))
    require(len({target.identifier for target in targets}) == len(targets), "Duplicate combined target IDs")
    names = sorted({name for target in targets for name in target.declarations})
    axioms, declarations, codes = run_lean(lake, names, output)
    result_rows = []
    totals = Counter()
    counts = {}
    bindings = Counter()
    modules = {name: module for name, (_, module) in declarations.items()}
    for module in modules.values():
        if module.startswith("DurfeeCCS."):
            source = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
            require(source.is_file(), f"Located declaration in missing project source {source}")
    for target in targets:
        verdict, problems = classify(target, axioms, declarations)
        totals[verdict] += 1
        counts.setdefault(target.kind, Counter())[verdict] += 1
        obligations = {name: sorted(axioms[name]) if name in axioms else None for name in target.declarations}
        original = rows.get(target.identifier)
        comparison = map_comparison(target, original, modules)
        bindings[comparison] += 1
        result_rows.append((target.identifier, target.kind, target.page, target.coverage, verdict,
                            ";".join(target.declarations), json.dumps(obligations, ensure_ascii=False),
                            target.note, " | ".join(problems), comparison,
                            original["lean_name"] if original else "",
                            original["proof_location"] if original else "",
                            json.dumps({name: modules.get(name) for name in target.declarations},
                                       ensure_ascii=False)))
    write_tsv(output / "targets.tsv",
              ("id", "kind", "page", "coverage", "verdict", "lean_names", "axioms", "note", "problems",
               "map_comparison", "original_lean_names", "original_proof_location", "source_modules"),
              result_rows)
    write_tsv(output / "declarations.tsv", ("lean_name", "kind", "source_module", "axioms", "verdict"),
              ((name, *declarations.get(name, ("", "")),
                json.dumps(sorted(axioms[name])) if name in axioms else "",
                "pass" if name in declarations and name in axioms and not axioms[name] - ALLOWED_AXIOMS else "fail")
               for name in names))
    require(not any(codes.values()) or totals["fail"], "Unexpected nonzero Lean exit without a reported failure")
    report = {"manuscript_input": "original_files" if paper_dir is not None else "published_anchor_index",
              "manuscript_rows": len(rows), "target_rows": len(targets), "requested_declarations": len(names),
              "axiom_outputs": len(axioms), "declaration_types": len(declarations),
              "unexpected_axioms": sorted(set().union(*axioms.values()) - ALLOWED_AXIOMS),
              "binding_comparison": dict(bindings),
              "numbered_results": len(RESULT_IDS), "conjectures": 1, "formulae": len(EQUATION_IDS),
              "tables": sum(TABLE_ROWS.values()), "step05": finite_summary, "verdicts": dict(totals),
              "by_kind": {kind: dict(value) for kind, value in counts.items()}, "lean_exit_codes": codes,
              "unverified_ids": [row[0] for row in result_rows if row[4] in {"fail", "partial", "open"}]}
    (output / "summary.json").write_bytes((json.dumps(report, ensure_ascii=False, indent=2) + "\n").encode("utf-8"))
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return int(bool(report["unverified_ids"]))


def self_test(lake, output):
    proof = "DurfeeCCS.p_one"
    no_axioms = "Step13Test.kernelChecked"
    unsafe = "Step13Test.unsafeProof"
    sorry_proof = "Step13Test.placeholderProof"
    placeholder = "Step13Test.uninhabitedLabel"
    missing = "Step13Test.missingProof"
    preamble = """
namespace Step13Test
theorem kernelChecked : True := True.intro
axiom unsupported : False
theorem unsafeProof : False := unsupported
theorem placeholderProof : False := by sorry
def uninhabitedLabel : Prop := False
end Step13Test
"""
    ax, kinds, codes = run_lean(lake, [proof, no_axioms, unsafe, sorry_proof, placeholder, missing],
                               output, "DurfeeCCS.Degree", preamble)
    expected = {proof: "pass", no_axioms: "pass", unsafe: "fail", sorry_proof: "fail",
                placeholder: "fail", missing: "fail"}
    rows = []
    for name, expected_verdict in expected.items():
        actual, problems = classify(Target(name, "result", "", "exact", (name,), ""), ax, kinds)
        require(actual == expected_verdict, f"Self-test failed for {name}: {actual}, {problems}")
        rows.append((name, expected_verdict, actual, " | ".join(problems)))
        print(f"{name}: {actual}")
    require(ax.get(no_axioms) == frozenset() and "Step13Test.unsupported" in ax.get(unsafe, ()),
            "Self-test did not observe the empty or disallowed axiom dependency")
    require("sorryAx" in ax.get(sorry_proof, ()), "Self-test did not observe sorryAx")
    require(missing not in ax and missing not in kinds and all(codes.values()),
            "Self-test did not observe the missing declaration")
    try:
        read_targets({"R1.2": {"kind": "result", "page": "2"}}, {})
    except AuditInputError as error:
        require("missing IDs" in str(error), "Self-test rejected the omitted row for the wrong reason")
        rows.append(("omitted R1.2", "invalid", "invalid", str(error)))
    else:
        raise AuditInputError("Self-test accepted an omitted manuscript row")
    print("Omitted manifest row: rejected")
    write_tsv(output / "verdicts.tsv", ("fixture", "expected", "observed", "problems"), rows)
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="Lake executable")
    parser.add_argument("--manifest", type=Path, default=ROOT / "review" / "step14-targets.tsv")
    parser.add_argument("--finite", type=Path, default=ROOT / "review" / "step13-finite.tsv")
    parser.add_argument("--output", type=Path, default=ROOT / "repro" / "audit")
    parser.add_argument("--paper-dir", type=Path, help="also verify the exact original PDF and TeX in this directory")
    parser.add_argument("--self-test", action="store_true", help="test a checked theorem and invalid examples")
    args = parser.parse_args()
    try:
        if args.self_test:
            return self_test(args.lake, args.output.resolve() / "self-test")
        return audit(args.lake, args.manifest.resolve(), args.finite.resolve(), args.output.resolve(), args.paper_dir)
    except (ValueError, TypeError, KeyError, IndexError, OSError) as error:
        print(f"Audit could not complete: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())

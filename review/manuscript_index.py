"""Identifiers and digests of the frozen v28 manuscript."""

SOURCE_DIGESTS = {
    "Durfee_CCS_v28.tex": "62678397918e3f89e5ecc16c876f583e8f0a9f1e4a77f45818839637832a4302",
    "Durfee_CCS_v28.pdf": "089b8cfd4606ec2749ee6086f214247a5743029d89644bf70fef0f4ac65d340d",
}
RESULT_IDS = {"R1.2", "R1.3", *(f"R3.{i}" for i in range(1, 12)), *(f"R4.{i}" for i in range(1, 5))}
EQUATION_IDS = {f"E{i:02}" for i in range(1, 78)}
FIELDS = ("id", "kind", "page", "source_locator", "hypotheses", "conclusion", "lean_name",
          "proof_location", "dependencies", "status", "pdf_destination", "tex_anchor_line", "statement_review")
TABLE_ROWS = {20: 3, 22: 3, 23: 3, 30: 9, 34: 17, 36: 2, 38: 2, 43: 5}

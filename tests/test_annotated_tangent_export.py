import gzip
import json
import struct
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path

from proof_certificate.export_annotated_tangent import (
    CANONICAL_KEYS,
    MAGIC,
    exact_ldl,
    export_forest,
    export_root,
    normalize_payload,
    parse_ball,
)


def ball(midpoint: str, radius: str = "1e-20") -> str:
    return f"[{midpoint} +/- {radius}]"


def sample_payload(path: str = "1"):
    box = [[4000 + i, 4000 + i] for i in range(6)]
    terms = []
    for index, (start, span) in enumerate(CANONICAL_KEYS):
        # Positive rank-one terms, with the six singleton terms ensuring PD.
        coefficient = Fraction(index + 1, 64)
        terms.append(
            {
                "start": start,
                "span": span,
                "coefficient_ratio": [coefficient.numerator, coefficient.denominator],
            }
        )
    return {
        "root": 0,
        "path": path,
        "box": box,
        "hessian_terms": terms,
        "ldl_pivots": [ball("1") for _ in range(6)],
        "midpoints": [[2 * (4000 + i) + 1, 8000] for i in range(6)],
        "radii": [[1, 8000] for _ in range(6)],
        "value": ball("0.01"),
        "gradient": [ball("0") for _ in range(6)],
        "lower": ball("0.01"),
        "target": "509/100000",
    }


class AnnotatedTangentExportTests(unittest.TestCase):
    def test_ball_is_an_exact_rational_interval(self):
        self.assertEqual(
            parse_ball("[1.25 +/- 2.5e-2]", "test"),
            (Fraction(49, 40), Fraction(51, 40)),
        )

    def test_exact_ldl_reconstructs(self):
        terms = [(i, 1, Fraction(i + 1, 7)) for i in range(6)]
        lower, diagonal, matrix = exact_ldl(terms)
        self.assertEqual(lower, [[Fraction(i == j) for j in range(6)] for i in range(6)])
        self.assertEqual(diagonal, [Fraction(i + 1, 7) for i in range(6)])
        self.assertEqual([matrix[i][i] for i in range(6)], diagonal)

    def test_payload_has_exact_geometry_ldl_and_margin(self):
        payload = normalize_payload(sample_payload(), 17)
        self.assertEqual(payload["id"], 17)
        self.assertEqual(len(payload["hessian_terms"]), 20)
        self.assertEqual(len(payload["ldl"]["diagonal"]), 6)
        margin = Fraction(*payload["affine_margin"])
        self.assertGreater(margin, 0)

    def test_under_target_payload_is_rejected(self):
        payload = sample_payload()
        payload["value"] = ball("0")
        with self.assertRaisesRegex(ValueError, "misses target"):
            normalize_payload(payload, 0)

    def test_leaf_tags_and_dense_payload_index(self):
        events = [
            {"root": 0, "path": "", "split": 0},
            {"root": 0, "path": "0", "leaf": True, "kind": "interval"},
            {"root": 0, "path": "1", "leaf": True, "kind": "tangent"},
        ]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            event_path = root / "events.jsonl.gz"
            tangent_path = root / "tangent.jsonl.gz"
            with gzip.open(event_path, "wt", encoding="utf-8") as stream:
                for event in events:
                    stream.write(json.dumps(event) + "\n")
            with gzip.open(tangent_path, "wt", encoding="utf-8") as stream:
                stream.write(json.dumps(sample_payload()) + "\n")
            exported = export_root(event_path, tangent_path)
        self.assertTrue(exported.topology.startswith(MAGIC))
        self.assertEqual(exported.nodes, 3)
        self.assertEqual(exported.tangent_leaves, 1)
        header = len(MAGIC) + 1 + 4 + 8 + 8
        # After the header: split coordinate 0, regular leaf,
        # tangent leaf, then its dense big-endian evidence index zero.
        self.assertEqual(exported.topology[header : header + 3], bytes([2, 0, 1]))
        self.assertEqual(
            struct.unpack(">Q", exported.topology[header + 3 : header + 11])[0], 0
        )

    def test_forest_uses_global_dense_payload_indices(self):
        events = [
            {"path": "", "split": 0},
            {"path": "0", "leaf": True, "kind": "interval"},
            {"path": "1", "leaf": True, "kind": "tangent"},
        ]
        with tempfile.TemporaryDirectory() as directory:
            trace = Path(directory)
            for root in range(2):
                with gzip.open(
                    trace / f"root-{root:06d}.events.jsonl.gz", "wt", encoding="utf-8"
                ) as stream:
                    for event in events:
                        stream.write(json.dumps({"root": root, **event}) + "\n")
                payload = sample_payload()
                payload["root"] = root
                with gzip.open(
                    trace / f"root-{root:06d}.tangent.jsonl.gz", "wt", encoding="utf-8"
                ) as stream:
                    stream.write(json.dumps(payload) + "\n")
            exported = export_forest(trace, roots=2)
        self.assertEqual([payload["id"] for payload in exported.payloads], [0, 1])
        self.assertEqual(exported.nodes, 6)
        self.assertEqual(exported.tangent_leaves, 2)


if __name__ == "__main__":
    unittest.main()

import hashlib
import json
import unittest
from pathlib import Path

from proof_certificate.export_interval_tree import (
    Leaf,
    Split,
    encode,
    encode_forest,
    encode_root_boxes,
    forest_from_events,
    tree_from_events,
    validate_blob,
    validate_root_blob,
    validate_tokens,
)


class IntervalTreeExportTests(unittest.TestCase):
    def test_binary_roundtrip_counts(self):
        tree = Split(0, Split(0, Leaf(), Leaf()), Split(0, Leaf(), Leaf()))
        self.assertEqual(validate_blob(encode(tree, 1)), (1, 1, 7, 3, 4))

    def test_path_events_reconstruct_tree(self):
        events = [
            {"path": "", "split": 1},
            {"path": "0", "leaf": True},
            {"path": "1", "split": 0},
            {"path": "10", "leaf": True},
            {"path": "11", "leaf": True},
        ]
        tree = tree_from_events(events, 2)
        self.assertEqual(validate_blob(encode(tree, 2)), (2, 1, 5, 2, 3))

    def test_root_indexed_events_reconstruct_forest(self):
        events = [
            {"root": 1, "path": "", "split": 0},
            {"root": 0, "path": "", "leaf": True},
            {"root": 1, "path": "0", "leaf": True},
            {"root": 1, "path": "1", "leaf": True},
        ]
        forest = forest_from_events(events, q=1, roots=2)
        self.assertEqual(
            validate_blob(encode_forest(forest, 1)), (1, 2, 4, 1, 3)
        )

    def test_missing_forest_root_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "missing events for root 1"):
            forest_from_events(
                [{"root": 0, "path": "", "leaf": True}], q=1, roots=2
            )

    def test_incomplete_preorder_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "incomplete tree"):
            validate_tokens([1, 0], q=1)

    def test_trailing_node_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "trailing node"):
            validate_tokens([0, 0], q=1)

    def test_unreachable_event_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "unreachable"):
            tree_from_events(
                [
                    {"path": "", "leaf": True},
                    {"path": "0", "leaf": True},
                ],
                q=1,
            )

    def test_root_box_roundtrip_and_validation(self):
        boxes = [[[1, 3], [5, 8]], [[0, 0], [9, 12]]]
        blob = encode_root_boxes(boxes, q=2)
        self.assertEqual(validate_root_blob(blob), (2, 2))
        inverted = bytearray(blob)
        # First low endpoint is bytes 13..16 and first high is 17..20.
        inverted[13:21] = (4).to_bytes(4, "big") + (3).to_bytes(4, "big")
        with self.assertRaisesRegex(ValueError, "inverted root interval"):
            validate_root_blob(bytes(inverted))

    def test_committed_production_roots_reconstruct_exactly(self):
        repository = Path(__file__).resolve().parents[1]
        root_json = repository / "certificates/weighted-p1-grid4000.roots.json"
        root_binary = repository / "certificates/weighted-p1-grid4000.roots.bin"
        boxes = json.loads(root_json.read_text())["roots"]
        blob = root_binary.read_bytes()
        self.assertEqual(validate_root_blob(blob), (6, 324))
        self.assertEqual(blob, encode_root_boxes(boxes, q=6))
        self.assertEqual(
            hashlib.sha256(blob).hexdigest(),
            "1f929f32b8c4d19f956b78c74461edfb0104af2118f5e1fb8708d691e7ffe692",
        )


if __name__ == "__main__":
    unittest.main()

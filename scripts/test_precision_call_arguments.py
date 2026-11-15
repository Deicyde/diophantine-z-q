"""Negative controls for the natural-polynomial argument certificate."""
import copy
from pathlib import Path
import tempfile
import unittest

from check_precision_call_arguments import certify, check_file


def fixture():
    return {"format": "hierarchical-natural-diophantine-circuit-v1",
            "variableDomain": "nonnegative integers", "variableCount": 5, "root": 5,
            "variables": [{"index": 0, "node": 1}, {"index": 4, "node": 2}],
            "nodes": [{"op": "const", "args": ["2"]},
                      {"op": "var", "args": [0]}, {"op": "var", "args": [4]},
                      {"op": "add", "args": [0, 1]}, {"op": "mul", "args": [2, 3]},
                      {"op": "call", "args": [0, 4, 0, 3, 1]}],
            "templates": [{"parameterCount": 3, "witnessCount": 3}],
            "witnessBlocks": [{"start": 1, "length": 3, "template": 0}]}


class CallArgumentTests(unittest.TestCase):
    def test_sparse_variables_and_private_offset_are_not_node_edges(self):
        result = certify(fixture())
        self.assertEqual(result["calls"], 1)
        self.assertEqual(result["certified_nodes"], 5)
        self.assertFalse(result["call_outputs_assumed_nonnegative"])

    def test_invalid_reference_types_ranges_and_forward_edges(self):
        for ref in (-1, True, 1.0, "1", 5, 500):
            for position in (1, 2, 3):
                with self.subTest(ref=ref, position=position):
                    data = fixture()
                    data["nodes"][-1]["args"][position] = ref
                    with self.assertRaises(ValueError):
                        certify(data)
        data = fixture()
        data["nodes"][3]["args"][0] = 3
        with self.assertRaisesRegex(ValueError, "forward reference"):
            certify(data)

    def test_negative_constant_argument_is_not_certified(self):
        data = fixture()
        data["nodes"][0]["args"] = ["-1"]
        with self.assertRaisesRegex(ValueError, "Uncertified call argument"):
            certify(data)

    def test_each_slot_and_arithmetic_propagate_failure(self):
        for slot in (1, 2, 3):
            data = fixture()
            data["nodes"].insert(5, {"op": "const", "args": ["-1"]})
            data["nodes"][-1]["args"][slot] = 5
            with self.subTest(slot=slot), self.assertRaisesRegex(ValueError, "Uncertified call argument"):
                certify(data)
        for op in ("add", "mul"):
            data = fixture()
            data["nodes"].insert(5, {"op": "const", "args": ["-1"]})
            data["nodes"].insert(6, {"op": op, "args": [0, 5]})
            data["nodes"][-1]["args"][1] = 6
            with self.subTest(op=op), self.assertRaisesRegex(ValueError, "Uncertified call argument"):
                certify(data)

    def test_unrelated_negative_constant_is_allowed(self):
        data = fixture()
        data["nodes"].append({"op": "const", "args": ["-1"]})
        self.assertTrue(certify(data)["passed"])

    def test_call_output_cannot_justify_another_calls_arguments(self):
        data = fixture()
        data["variableCount"] = 8
        data["witnessBlocks"].append({"start": 5, "length": 3, "template": 0})
        data["nodes"].append({"op": "call", "args": [0, 5, 0, 3, 5]})
        with self.assertRaisesRegex(ValueError, "Uncertified call argument"):
            certify(data)

    def test_call_output_through_arithmetic_is_not_certified(self):
        for op in ("add", "mul"):
            data = fixture()
            data["variableCount"] = 8
            data["witnessBlocks"].append({"start": 5, "length": 3, "template": 0})
            data["nodes"].extend([{"op": op, "args": [0, 5]},
                                  {"op": "call", "args": [0, 6, 0, 3, 5]}])
            with self.subTest(op=op), self.assertRaisesRegex(ValueError, "Uncertified call argument"):
                certify(data)

    def test_private_offset_can_exceed_node_index(self):
        data = fixture()
        data["variableCount"] = 21
        data["templates"][0]["witnessCount"] = 10
        data["variables"] = [{"index": 0, "node": 0}]
        data["nodes"] = [{"op": "var", "args": [0]},
                         {"op": "call", "args": [0, 0, 0, 0, 1]},
                         {"op": "call", "args": [0, 0, 0, 0, 11]}]
        data["root"] = 2
        data["witnessBlocks"] = [{"start": 1, "length": 10, "template": 0},
                                  {"start": 11, "length": 10, "template": 0}]
        self.assertEqual(certify(data)["calls"], 2)

    def test_malformed_constants_and_large_lexical_constant(self):
        for value in (2, "+2", "1.5", "-", "1e4", "02", "٢"):
            data = fixture()
            data["nodes"][0]["args"] = [value]
            with self.subTest(value=value), self.assertRaises(ValueError):
                certify(data)
        data = fixture()
        data["nodes"][0]["args"] = ["9" * 100000]
        self.assertTrue(certify(data)["passed"])

    def test_bad_binding_domain_template_and_block(self):
        cases = []
        data = fixture(); data["variables"][0]["node"] = 0; cases.append(data)
        data = fixture(); data["variables"].append(copy.deepcopy(data["variables"][0])); cases.append(data)
        data = fixture(); data["variableDomain"] = "integers"; cases.append(data)
        data = fixture(); data["templates"][0]["parameterCount"] = 2; cases.append(data)
        data = fixture(); data["witnessBlocks"][0]["start"] = 2; cases.append(data)
        data = fixture(); data["nodes"][-1]["args"][4] = 10; cases.append(data)
        data = fixture(); data["nodes"][3]["op"] = "subtract"; cases.append(data)
        data = fixture(); data["variableCount"] += 1; cases.append(data)
        data = fixture(); data["witnessBlocks"][0]["start"] = 0; cases.append(data)
        data = fixture(); data["witnessBlocks"].append(copy.deepcopy(data["witnessBlocks"][0])); cases.append(data)
        data = fixture(); data["variables"][1]["index"] = 1; cases.append(data)
        data = fixture(); data["root"] = len(data["nodes"]); cases.append(data)
        for data in cases:
            with self.subTest(data=data), self.assertRaises(ValueError):
                certify(data)

    def test_unbound_source_fails_before_acceptance(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "changed.json"
            path.write_text("{}", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "hash mismatch"):
                check_file(path)


if __name__ == "__main__":
    unittest.main()

"""Certify natural polynomial arguments of the frozen precision power calls.

This is a sufficient syntactic test, not a decision procedure for polynomial
positivity. A certified node is a nonnegative constant, a declared natural
variable, or a sum/product of certified nodes. Call outputs are never certified.
Induction on node order therefore proves that every certified node is a
polynomial with nonnegative integer coefficients in the explicit source
variables, without any assumption that a private power block vanishes.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re


SOURCE_SHA256 = "f3e163f5c60b972c98b48647274f956dd7d78428e27ddc0543574a5f18120b8c"
DECIMAL = re.compile(r"-?(?:0|[1-9][0-9]*)", re.ASCII)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def natural(value):
    return type(value) is int and value >= 0


def certify(document):
    """Check the property on a parsed circuit; fixtures need no frozen hash."""
    require(document.get("format") == "hierarchical-natural-diophantine-circuit-v1",
            "Unsupported circuit format")
    require(document.get("variableDomain") == "nonnegative integers", "Variables must be natural")
    total = document.get("variableCount")
    require(natural(total), "Invalid variable count")
    nodes, variables = document.get("nodes"), document.get("variables")
    templates, blocks = document.get("templates"), document.get("witnessBlocks")
    require(all(type(x) is list for x in (nodes, variables, templates, blocks)), "Missing circuit lists")
    root = document.get("root")
    require(natural(root) and root < len(nodes), "Invalid root")
    declared = {}
    allocation = []
    for row in variables:
        require(type(row) is dict, "Invalid variable declaration")
        index, node = row.get("index"), row.get("node")
        require(natural(index) and index < total and index not in declared, "Invalid or duplicate variable index")
        require(natural(node) and node < len(nodes), "Invalid variable node")
        declared[index] = node
        allocation.append((index, index + 1))
    for block in blocks:
        require(type(block) is dict, "Invalid private block")
        start, length, template = block.get("start"), block.get("length"), block.get("template")
        require(natural(start) and natural(length) and length > 0 and
                natural(template) and template < len(templates), "Invalid private block dimensions")
        allocation.append((start, start + length))
    endpoint = 0
    for start, stop in sorted(allocation):
        require(start == endpoint and stop <= total, "Overlapping allocation or variable-count gap")
        endpoint = stop
    require(endpoint == total, "Variable-count gap")
    certified, seen_variables, call_count = [], set(), 0
    argument_nodes = set()
    for index, node in enumerate(nodes):
        require(type(node) is dict, f"Invalid node {index}")
        op, args = node.get("op"), node.get("args")
        require(type(args) is list, f"Invalid arguments at node {index}")
        good = False
        if op == "const":
            require(len(args) == 1 and type(args[0]) is str and DECIMAL.fullmatch(args[0]),
                    f"Invalid decimal constant at node {index}")
            good = not args[0].startswith("-") or args[0] == "-0"
        elif op == "var":
            require(len(args) == 1 and natural(args[0]) and declared.get(args[0]) == index,
                    f"Undeclared or misbound variable at node {index}")
            seen_variables.add(args[0])
            good = True
        elif op in {"add", "mul"}:
            require(len(args) == 2, f"Invalid arithmetic arity at node {index}")
            require(all(natural(ref) and ref < index for ref in args),
                    f"Malformed or forward reference at node {index}")
            good = all(certified[ref] for ref in args)
        elif op == "call":
            # Slots: template, result parameter, base, exponent, private-variable offset.
            require(len(args) == 5 and all(natural(x) for x in args), f"Invalid call at node {index}")
            template, *references, start = args
            require(template < len(templates), f"Unknown call template at node {index}")
            spec = templates[template]
            require(type(spec) is dict and spec.get("parameterCount") == 3,
                    f"Call must have three parameters at node {index}")
            length = spec.get("witnessCount")
            require(natural(length) and start + length <= total, f"Invalid private block at node {index}")
            require(call_count < len(blocks) and blocks[call_count] ==
                    {"start": start, "length": length, "template": template},
                    f"Private block metadata mismatch at node {index}")
            require(all(ref < index for ref in references), f"Malformed or forward call reference at node {index}")
            for slot, ref in enumerate(references, 1):
                require(certified[ref], f"Uncertified call argument at node {index}, slot {slot}, reference {ref}")
            argument_nodes.update(references)
            call_count += 1
            # Even if a call happens to be a sum of squares, do not use its value
            # to certify later arguments. This prevents circular reasoning.
        else:
            raise ValueError(f"Unsupported operation at node {index}: {op!r}")
        certified.append(bool(good))
    require(seen_variables == set(declared), "Variable declaration has no matching node")
    require(call_count == len(blocks), "Unused private block metadata")
    return {"passed": True, "nodes": len(nodes), "explicit_natural_variables": len(declared),
            "calls": call_count, "argument_occurrences": 3 * call_count,
            "distinct_argument_nodes": len(argument_nodes),
            "certified_nodes": sum(certified), "call_outputs_assumed_nonnegative": False,
            "scope": "Syntactic natural-polynomial arguments only; not correctness of the power relation or the arithmetic theorem."}


def check_file(path):
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    require(digest == SOURCE_SHA256, "Frozen precision circuit hash mismatch")
    result = certify(json.loads(raw))
    require(result["nodes"] == 293620 and result["calls"] == 15845, "Unexpected frozen circuit counts")
    return {"source_sha256": digest, **result}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path(__file__).resolve().parents[1] /
                        "construction/precision-natural-polynomial.json")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    result = check_file(args.source)
    text = json.dumps(result, indent=2) + "\n"
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()

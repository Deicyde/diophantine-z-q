# Clean reproduction comparison correction

All three requested commands exited zero in the clean checkout. The initial
postprocessing assertion demanded byte equality against the author control
receipt and failed. The failed wrapper stdout/stderr are retained alongside
this note. This was a receipt-comparison failure, not a failing mathematical
case or Lean command.

Inspection found exactly one differing JSON field: `python` was `3.12.3` in
the author receipt and `3.13.12` in the clean run. Every substantive field and
input hash matched. The entire clean output is byte-identical to the separately
authored reviewer's earlier Python 3.13.12 output. No output was edited and no
mathematical tolerance was introduced. The final receipt records both the
failed author byte comparison and the successful exact substantive/reviewer
comparisons. All 17 native receipt files, four `.olean` hashes and protocol
stdout matched byte for byte. This metadata correction required no proof or
checker source change and no additional computation of the mathematical cases.

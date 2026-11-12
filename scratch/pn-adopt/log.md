# pn-adopt log

## Step 1 (split)
- `ZInQKernel/Hypotheses/TYZInputs.lean`: PropN.lean L1–2 (imports), L31–128 (gNat, gi, twoTwoI,
  LemmaTwoEight, GenusData, TYZInputs), closed with `end ZInQ.PropN`.
- `ZInQKernel/RouteK/PropN.lean`: imports GaussianInt + Hypotheses.TYZInputs; L31–36 header
  (noncomputable section, namespace, open), L130–1680 verbatim.
- diff of concatenated bodies against the scratch file: only blank lines differ.
- Only comment change: section header "The four lemmas (statements fixed; proofs `sorry`)" ->
  "The four lemmas".

## Step 2 (docstrings)
- New module docstrings in both files (lines ≤ 100).

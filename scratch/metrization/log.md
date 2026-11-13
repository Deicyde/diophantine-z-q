# metrization results log

Start 2026-11-13 04:08 PST. Base 2dd83306 (wip/integrate-w36b). Targets (verbatim from
scratch/g0-heightadd/part_heightadd.lean, part_prod.lean): `ZInQ.G0HeightAdd.MetrizationDimUnique`,
`MetrizationExists`, `ProductMetrizationGeo`.

## Run 1: ExtLine.lean (Mathlib only) — COMPILED 04:15 (3 min 10 s wall, load 28; 0 errors)
- `ZInQ.Metrization.eq_of_finrank_one`: for `R` comm ring, `F` a field, flat `R`-algebra, any
  `R`-module `C`, `0 < g`, `0 < g'`, `finrank F (F ⊗_R ⋀^g C) = 1`, `finrank F (F ⊗_R ⋀^{g'} C) = 1`
  ⇒ `g = g'`. Axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
  Proof: for `g < g + n`, pick `v` with `1 ⊗ ιMulti v ≠ 0` in `F ⊗ ⋀^{g+n}`, split `v = append a b`,
  swap one entry between `a` and `b`; right multiplication by `ιMulti b`, `ιMulti b'` separates
  `1 ⊗ ιMulti a` and `1 ⊗ ιMulti a'`, contradicting `finrank = 1` (flatness keeps
  `1 ⊗ ιMulti v ≠ 0` in `F ⊗ ⋀C`).

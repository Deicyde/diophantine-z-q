# eichler-bound (fleet summary)

**Result: `gonzalezRotgerProp56X6` comes off with no new leaf.** The only half the chain reads,
`GR56.R5fpCountLe` (`#CM(R) ≤ 2^b h(R)`), is now a theorem from the three textbook fields already in
`OpenTextbookLeaves12`:

* `EichlerBound.r5fpCountLe_proof : UniformizationLeafAll → GAGAMorphism → MumfordTorsionAlgClosed → GR56.R5fpCountLe`
* `EichlerBound.eichlerOptEmbBound6`: `#(OptEmb k R / 𝒪^×) ≤ 2^{inertCount6 k} · #Pic R` for the maximal order of
  `(2, −3 | ℚ)` and every order of conductor prime to 6. This is proved outright, in place of the GLUE-rated leaf
  `EichlerOptEmbCount6`.

How: an explicit injection `Emb/𝒪^× ↪ Pic(R) × T`, `#T = 2^b`. The ingredients are:
* class number one of `𝒪` (the Euclidean algorithm);
* intertwiner lattices `J ∩ 𝒪` between two embeddings, and their lattice classes sent to `Pic R` by Mathlib's
  `Submodule.unitsToPic`;
* "no bad prime": a sympy polynomial certificate plus a minor descent at `ℓ ∤ 6`, and the uniformizers `i`, `j`
  with types at 2 and 3.

All finite checks are `decide`, `ring` or `omega`.

**Compiles** (standard axioms only, no `sorry`):
* `ZInQKernel/Contrib/OneProof/R5fpCountLe.lean` (imports `GR56Lattice`) and the helpers
  `ZInQKernel/Contrib/OneProof/EichlerBound/*.lean` (2457 lines in total, all new files);
* the bypass `scratch/eichler-bound/BypassFold.lean`, whose `frozenTarget_E` has the research bundle without
  `gonzalezRotgerProp56X6` and with no added field;
* `#discharges` output recorded.

**Counts** (`autofold --dry-run`, count-only spec `scratch/eichler-bound/autofold.json`, no leaves):
* `34/11 on 45 → 33/11 on 44` against the tree;
* `33/12 → 33/11` with the row re-rated GLUE, i.e. **−1**.

**Remains:**
* the integrator lands the bypass, either by rerunning `gen_bypass.py` at fold time or by a hand fold;
* the lower half of Eichler's count (equality) is not needed by the chain and was not formalized.

Report: `docs/research/eichler-bound.md`.

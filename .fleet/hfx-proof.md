# hfx-proof (final)

**Result: `hfx` discharged outright, with no new leaf.** `ZInQ.Contrib.HfxProof.tyzTestVectorExists :
H29Split.TYZTestVectorExists` is proved in `ZInQKernel/Contrib/OneProof/TYZTestVectorExists.lean`. That is TYZ's
`π_ℤ^{U_n}` having a nonzero generator, for every squarefree `1 < n ≡ 1, 3 (mod 8)` and every admissible `τ`.
Helpers are in `ZInQKernel/Contrib/OneProof/HfxProof/` (15 files). `#discharges` gives:
`DISCHARGES [hfx] ... still assumes: [] axioms: [propext, Classical.choice, Quot.sound]`
(`scratch/hfx-proof/Discharges-output.txt`). Finite checks use `decide +kernel` only. No sorry or native_decide.

Route (the proposed one):
* `B̂^× = B^× Ô_B^×`, from the Euclidean Hurwitz order (fork PR #39's approximation).
* TYZ Lemma 2.5 surjectivity: every unit of B̂ lies in one of the 8 double cosets.
* Merges by explicit elements of `K^×`.
* Separations by a 2-adic obstruction through t21-proof's global step.
* Finite tables over the residues of `τ(√−n)`:
  * `n ≡ 3`: 64 residues; orbits of sizes 2 and 6; generator values −3, 1.
  * `n ≡ 1`: 32 residues; `K_2` is ramified, so the uniformizer `1 + ω` is needed; orbits of sizes 2, 2, 4;
    generator values 1, −1, 0.
* Rank one by counting.

What compiles: everything above, plus `scratch/hfx-proof/FoldCheck.lean`. The latter is `frozenTarget` without
`hfx`, and also without `hfx` and `hT21`; both have standard axioms.

Dependencies: the branch merges origin/wip/t21-proof (T21Proof helpers) and
origin/proof/hp23-hurwitz-ab-20261116 (PR #39). The integrator needs both.

Fold: autofold refuses, because `hfx` is a top-level argument of `frozenTarget`. The manual fold is in the
report §5; the spec is in `scratch/hfx-proof/autofold.json`.

What remains: nothing for this task.
* Side observation: test vectors are now explicit (`f = ±F`). So `hP23` is immediate for `n ≡ 3`. For `n ≡ 1`
  it needs a `χ₀`/nrd-mod-4 argument (SPECULATIVE, not done).

Report: docs/research/hfx-proof.md. Log: scratch/hfx-proof/log.md.

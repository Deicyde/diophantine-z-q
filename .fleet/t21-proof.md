# t21-proof (final)

**Result: `hT21` discharged outright, with no new leaf.** `ZInQ.Contrib.T21Proof.tyzThm21At31 : H29Split.TYZThm21At31`
(TYZ Theorem 2.1 at n = 3, (3, 1)) is proved in `ZInQKernel/Contrib/OneProof/TYZThm21At31.lean`; helpers are in
`ZInQKernel/Contrib/OneProof/T21Proof/`. `#discharges`: `DISCHARGES [hT21] ... still assumes: [] axioms: [propext,
Classical.choice, Quot.sound]` (`scratch/t21-proof/Discharges-output.txt`). Finite checks use `decide +kernel` only.

Route:
* Cl(Q(√−3)) = 1, so the class sum is f_3(1).
* torsionOrder = 6, from Mathlib.
* f_3(1) = ±3 for every admissible τ and test vector, by a Brandt computation (`testVector_one`: the double-coset
  function −3·[B^×H] + 1·[else] lies in π_ℤ^{U_3}, with a local mod-4 obstruction for the other six classes).
* 0 < ‖𝓛(m)²‖ < 4 at m = 1, 3, from rigorous enclosures:
  * 0.09 ≤ Re L(C_1,1), ‖L(C_1,1)‖ ≤ 1.26;
  * 0.14 ≤ Re L(C_3,1), ‖L(C_3,1)‖ ≤ 2.9;
  * these come from Hecke's continuation, the four-nearest-lattice-point closed form of Λ_{a,b}(1) with an explicit
    tail bound, and kernel-checked rational certificates.
* Hence ℓ(1), ℓ(3) = ±1.

What compiles: all of the above, each module in under 25 s.

Fold: autofold.py refuses because `hT21` is a top-level argument of `frozenTarget`, not a bundle field. The manual fold
(drop the binder and pass `tyzThm21At31`) is checked in `scratch/t21-proof/FoldCheck.lean`, which compiles with the
standard axioms. Spec: `scratch/t21-proof/autofold.json`.

What remains: nothing for this task. The integrator applies the manual fold and regenerates OPEN.md/kinds.tsv.
Report: docs/research/t21-proof.md; log: scratch/t21-proof/log.md.

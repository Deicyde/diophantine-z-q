# infra-smooth-dim results log

Base f90cf864 + merge origin/wip/mul-rigidity (60a480e0).

## Targets (verbatim statements)
- `LeafQM.AV.Pin.SmoothStalkDimOne` (scratch/curve-facts/CurveFacts.lean:539)
- `ZInQ.DefFaltings.HodgeLattice.TangentDimAtOrigin` (scratch/hodge-lattice/HodgeLattice.lean:1144)
- mul-rigidity: its dimension input `QuasiFiniteEndSurjective` is already a theorem there (VERIFIED, docs/research/mul-rigidity.md row `quasiFiniteEndSurjective`); nothing left for this task.

## Compile log
- run1 MaxHeight.lean: `InfraSmoothDim.height_isMaximal_mvPolynomial` (k field, ι finite, M maximal in MvPolynomial ι k ⇒ M.height = Nat.card ι): 0 errors, axioms [propext, Classical.choice, Quot.sound] (VERIFIED)

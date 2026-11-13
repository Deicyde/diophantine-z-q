# alg-frob-red (fleet summary)

**Result.** `FrobTrace.AlgFrobRed` (frob-trace's AV-side glue under G14's Tate bridge; copied verbatim, unchanged) is
proved from: leaf candidates `GoodRedCofinite` (good reduction outside finitely many primes; EGA IV §8, Serre–Tate 1968
§1) and `SmoothGeomConnIntegral` (smooth + quasi-compact + geometrically connected ⇒ geometrically integral); the
existing kernel leaf I2-Red (`PkgI2.ReductionTorsionBijective`); and two glue Props, `FExtendGen` (I2-NMP extends F to the
abelian scheme over Spec(σ⁻¹|O_w), fixing 0, restricting to F on the generic fibre) and `AbsFrob` (the absolute Frobenius of a char-p scheme exists and is natural on affine points;
standard, not in Mathlib). Theorems: `AlgFrobRedRed.algFrobRed_of_gen`, `tateBridge35_of_gen` (with I3.M0 gives
`G14Bridge.TateBridge35`).

**Proved in Lean** (scratch/alg-frob-red/part_red.lean): conjugating the place; isolating S; the special fibre is an
abelian variety; residue characteristic, units ℓⁿ; O_w is a DVR; valuative criterion (Mathlib); κ(v) ≅ κ(w)‾
(residue field algebraically closed and algebraic); reduction is a homomorphism (adjunction Over.map ⊣ Over.pullback);
transport of I2-Red from L‾ to ℚ̄ and the special fibre; σ = Frob on κ(v) and σ⁻¹|O_w = Frob⁻¹ on κ(w); the twisted Frobenius Fr ≫ F̄ on the special fibre (from AbsFrob); the lift of f x from the generic-fibre extension; rigidity (mul-rigidity's proof, copied).

**Compiles.** `lake env lean scratch/alg-frob-red/AlgFrobRed.lean` (build.sh: verbatim copies of frob-trace's parts and
mul-rigidity's Rigidity.lean + part_red.lean): exit 0, no sorry, 87 axiom prints all
[propext, Classical.choice, Quot.sound]. One model review of the first split: all Props true, none vacuous.

**Remains.** Glue `FExtendGen` (from I2-NMP: conjugate model, F over Spec σ⁻¹|_L, Spec ℚ̄ → Spec L epi) and `AbsFrob`
(needs the absolute Frobenius of schemes, absent in Mathlib 4.35); the two leaf candidates.
Report: docs/research/alg-frob-red.md.

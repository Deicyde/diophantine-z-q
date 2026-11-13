# alg-frob-red (fleet summary)

**Result.** `FrobTrace.AlgFrobRed` (frob-trace's glue under G14's Tate bridge; copied verbatim, unchanged) is proved
from five named Props: leaf candidates `GoodRedCofinite` (good reduction outside finitely many primes; EGA IV §8,
Serre–Tate 1968 §1) and `SmoothGeomConnIntegral` (smooth + quasi-compact + geometrically connected ⇒ geometrically
integral), and glue `RedTorsionQbar` (leaf I2-Red transported to ℚ̄ / the special fibre), `FExtend` (leaf I2-NMP
extending F to the abelian scheme over Spec σ⁻¹) and `FrobMorph` (absolute Frobenius of the special fibre twisted by F̄).
`AlgFrobRedRed.algFrobRed_of_five` and `tateBridge35_of_five` (with I3.M0) give `G14Bridge.TateBridge35`.

**Proved in Lean** (scratch/alg-frob-red/part_red.lean): conjugation of the place; isolation of S; the special fibre is
an abelian variety; residue characteristic and units ℓⁿ; valuative criterion (existence/uniqueness of lifts, Mathlib);
`ResidueAlgClosed` and `ResidueAlgebraic` (κ(v) ≅ κ(w)‾); `RedRelMul` (reduction is a homomorphism, via the adjunction
Over.map ⊣ Over.pullback); σ = Frob on κ(v); rigidity (mul-rigidity's proof, copied).

**Compiles.** `lake env lean scratch/alg-frob-red/AlgFrobRed.lean` (assembled by build.sh from verbatim copies of
frob-trace's parts and mul-rigidity's Rigidity.lean): exit 0, no sorry, 64 axiom prints all
[propext, Classical.choice, Quot.sound]. One model review: all twelve new Props true, none vacuous.

**Remains.** The three glue Props (RedTorsionQbar from I2-Red by transport + O_w DVR; FExtend from I2-NMP via the conjugate
model; FrobMorph needs absolute Frobenius, absent from Mathlib 4.35) and the two leaf candidates. Report:
docs/research/alg-frob-red.md.

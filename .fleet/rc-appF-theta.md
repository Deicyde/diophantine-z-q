# rc-appF-theta: App F theta form at one stage, as the odd coefficient source (scoped stop)

**Main result (proved: no sorry, axioms only propext / Classical.choice / Quot.sound).**

`ThetaStage R` records the objects of (O.1)–(O.4) at one stage. For any such record, the phase-removed coefficients
`aθ n = H_M(mn)` satisfy the tree's `Odd.SourceHyp`. Over `ZMod (2^M)` this is the tree's `Odd.OddStageSource`, the input
of `Odd.O9_odd_stage` and `Odd.O11_odd_stage`.

- `H_M` is (O.4) as a finite sum with integer masses `c₀/|R_z^×|`.
- (O.6) is proved at every good prime by Elliot's Brandt computation (tex 8961–9100).
- `ap_mod` is taken as a hypothesis; it is proved for the curve as `GlueSweep.Odd.ap_mod_four_curve`.
- App G's depth enters as a hypothesis in the tree's `SourceHyp.depth` shape.

**Scoped stop.** No `ThetaStage` has yet been built from `(E, ℓ₀, M, L, λ_M)`. That needs quaternion and Eichler orders, the
adelic class set, local splittings, and supersingular reduction on `X₀(N)` with Hecke compatibility. None of it is in
Mathlib. The smallest faithful statement and a size estimate are in `docs/research/rc-appF-theta.md`.

The transformation law and holomorphy (tex 8623–9037) are not needed by any consumer of `OddStageSource` or
`ThetaComparison`, so I did not formalize them.

**New theorems** (all in `ZInQKernel/Contrib/OneProof/RC/AppF/`):

- `count0_primitive`, `count0_pdiv`, `count1_primitive`, `memNbr_two_pdiv`: the local counts of tex 9039–9058.
- `PFrame.neighbor_identity`: the per-class identity of tex 9059–9066.
- `mass_adjoint`, `brandt_transfer`, `brandt_identity`: tex 9067–9082, gap F-a written out.
- `ThetaStage.brandt`, `ThetaStage.recAt` (supplies `SourceHyp.recur`), `ThetaStage.aθ_zero` (supplies `SourceHyp.zero`).
- `ThetaStage.sourceHyp` and `ThetaStage.oddStageSource` (supply `OddStageSource`).
- `trivialStage`: the record's fields are consistent.
- Leaf: `VoightMainThm1461`, a PRINT at `Σ = {ℓ₀, ∞}`, locator UNVERIFIED.

**Manuscript check:** OK 12, gap filled 1, error 0, unverified 8. No error verdict.

**Known issues.**

- `OddStageSource` is fixed over `ZMod (2^M)`. Elliot's `𝒪/2^M𝒪` is larger when some `α_p` has order 4 or more.
  `sourceHyp` is generic over `R`; I recommend generalizing `OddStageSource` to match.
- The glue from `AppGEndpoints.OddMinimumF6` to `SourceHyp.depth` is missing. I estimate it as small.
- `OddStageSource` alone holds for `a = 0`. Non-vacuity comes from (O.7), which belongs to the cloud agent's lane.

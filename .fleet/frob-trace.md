# frob-trace (fleet summary)

**Result.** g14-trace's `G14Bridge.TateBridge35` (the linked Tate bridge at ℓ = 3, 5) is proved
from the existing leaf I3.M0 `PkgI3.TateModuleFree` and one new AV-side glue Prop,
`FrobTrace.AlgFrobRed`. Its conjunct `FrobTraceLink` therefore holds for the operators it builds.
Both statements are copied verbatim and unchanged; neither is false or vacuous.

`FrobTrace.tateBridge35_of_algFrobRed : PkgI3.TateModuleFree → AlgFrobRed → G14Bridge.TateBridge35`
is the composite of three proved steps:
- `algFrobOne_of_red : AlgFrobRed → AlgFrobOne`: `Ψ = ℚ_ℓ ⊗ T_ℓ(red)`, and `tateMap_bijective`
  (pure algebra) shows `T_ℓ(red)` is bijective.
- `algFrobLink_of_one : AlgFrobOne → AlgFrobLink`: one morphism `F_{σ_s}` per class
  `s ∈ Gal(L/ℚ)`; `S` is a finite union.
- `tateBridge35_of_algFrobLink`: it uses
  - unram-tate's operators `Tm_ℓ = opV(Θ∘m_{h·h⁻¹}∘Θ⁻¹)` at ℓ = 5, 3;
  - scalars in ℚ̄ from `scalarsQbar` (proved), with `βQ/a` and `βQ` algebraic;
  - the rescaling `g7Out_rescale`, which gives one common pair `aQ, βQ` at both primes;
  - `FrobTraceLink` via `frobCompare_opV_conjE`.

`AlgFrobRed` is GLUE, and the smallest of the three Props. Setting: `A/L` an abelian variety
and `F : A → A` a finite surjective morphism. Claim: there is a finite `S` such that, at a
Frobenius `gτg⁻¹` above `p ∉ S`, a reduction homomorphism `red : A(ℚ̄) → Ā(k̄)` with
`char k = p` intertwines `f = F∘-∘Spec(gτg⁻¹)` with some `α' ∈ End(Ā)`, and `red` is bijective
on ℓⁿ-torsion for every ℓ ≠ p. Mathematically it rests on:
- I2-Red, `PkgI2.ReductionTorsionBijective` (Serre–Tate);
- I2-NMP, `PkgI2.NeronMappingAbelianScheme`;
- rigidity;
- good reduction outside a finite set.

None of these implications is proved in Lean. One model review (no human review) found all
three glue Props true as stated, with `N = 1`, and not vacuous. It found two docstring slips,
both fixed.

**What compiles (VERIFIED).** `scratch/frob-trace/FrobTrace.lean` (`build.sh`: verbatim copies of
`scratch/unram-tate/TateBridge.lean` and `scratch/g14-trace/part_bridge.lean`, plus
`part_frob.lean`): exit 0, no `sorry`, all 26 `#print axioms` standard.
`scratch/frob-trace/FrobTraceAll.lean` (`build_all.sh`) adds verbatim copies of g14-trace's
`G14Trace.lean` parts to the same environment. It also compiles with exit 0, no `sorry` and all
58 axiom prints standard (it needs `lake build ZInQKernel.Main` first). It proves
`FrobTraceCompose.g12Spec_g14_of_G7Data`: from G7's data, the leaves I3.M0 and T7, the glue
`AlgFrobRed` and `DirichletOfFinite`, and G8-G12 (as hypotheses, in g0-mod-galois' shapes),
it gives data `D` with `G12Spec D ∧ G14TraceCompat D`. This composes `TateBridge35` with
g14-trace's consumer, which g14-trace had left in two separate files.

**What remains.** The glue `AlgFrobRed`, i.e. reduction of PkgI3 abelian varieties. Proving it
from I2-Red and I2-NMP needs spreading out, a PkgI3↔PkgI2 points translation, the reduction map
as a homomorphism, and Frobenius on points. Report: `docs/research/frob-trace.md`; log:
`scratch/frob-trace/log.md`.

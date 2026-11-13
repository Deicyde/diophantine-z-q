# frob-trace results log

## Setup (2026-11-13 ~06:00)
- Copies (verbatim): part_tate_src.lean = scratch/unram-tate/TateBridge.lean (= g0-mod-field ModField.lean L1-1036 + import RhoCont + section UnramTate);
  part_bridge_src.lean = scratch/g14-trace/part_bridge.lean (G14Bridge.FrobTraceLink, G14Bridge.TateBridge35, tateBridge_five_three_of_35).
- build.sh assembles FrobTrace.lean = `import ZInQKernel.HDecomp.C10.Link` + the two copies + part_frob.lean (this task).
- Built the imported kernel modules with `lake build` (exit 0, ~15 min).

## Run 1 (06:10): first compile of the draft
- `lake env lean scratch/frob-trace/FrobTrace.lean`: 2 errors (Algebra.IsAlgebraic.tower_top argument; a theorem without type). Fixed: `extendScalars (R := ℚ)`; removed the untyped composite.
## Run 2 (06:15): VERIFIED
- exit 0, 0 errors, no `sorry`, ~60 s. All `#print axioms` standard [propext, Classical.choice, Quot.sound], incl.
  FrobTrace.tateMapEquiv, conj_baseChange, frobCompare_opV_conjE, g7Out_rescale, scalarsQbar,
  tateBridge35_of_algFrobLink : PkgI3.TateModuleFree → AlgFrobLink → G14Bridge.TateBridge35.
- Remaining glue: `FrobTrace.AlgFrobLink` (points-level reduction mod p of the algebraic maps m_σ). Leaf: I3.M0 TateModuleFree.

## Run 3-5 (06:25-06:40): single-morphism glue
- New `FrobTrace.AlgFrobOne` (AlgFrobLink for one finite surjective scheme morphism F : A → A, f(x) = F ∘ x ∘ Spec(gτg⁻¹)).
- `algFrobLink_of_one : AlgFrobOne → AlgFrobLink` (one representative σ_s per s ∈ Gal(L/ℚ); m_{σ_s k} = F_{σ_s} ∘ x ∘ Spec(σ_s k); S = union over Gal(L/ℚ)).
- `tateBridge35_of_algFrobOne : PkgI3.TateModuleFree → AlgFrobOne → G14Bridge.TateBridge35`.
- Run 5: exit 0, no sorry, all axioms standard (VERIFIED).

## Run 6 (06:55): reduction-map glue
- New `FrobTrace.AlgFrobRed`: one group hom red : A(ℚ̄) → Ā(k̄) with red ∘ (N·f) = α' ∘ red, injective on ℓ-power torsion and
  ℓⁿ-torsion-surjective (with ℓⁿ-torsion preimages) for every prime ℓ ≠ p.
- `tateMap_bijective` (algebra: T_ℓ(r) bijective under these torsion conditions), `algFrobOne_of_red : AlgFrobRed → AlgFrobOne`
  (Ψ = ℚ_ℓ ⊗ T_ℓ(red)), `tateBridge35_of_algFrobRed : PkgI3.TateModuleFree → AlgFrobRed → G14Bridge.TateBridge35`.
- exit 0, no sorry, 26 axiom prints, all standard (VERIFIED).

## Review (07:20; one model review, read-only, no human review)
- Finding: AlgFrobLink, AlgFrobOne, AlgFrobRed true as stated (N = 1), not vacuous, not degenerate; S before ∀ p v τ g f;
  reduction at g(v). Docstring slips in AlgFrobLink (w = v ∩ L should be g(v) ∩ L; m_τ should be m_{gτg⁻¹}) fixed.
  Noted: TateBridge35 does not tie Tm_ℓ to m_σ (by design, as TateBridge), so FrobTraceLink constrains the chosen normalization.
## Composite (07:20, in progress)
- part_compose.lean: FrobTraceCompose.g12Spec_g14_of_G7Data; build_all.sh assembles FrobTraceAll.lean with verbatim copies of
  g14-trace's G14Trace.lean parts (*_g14.lean, cmp-identical). Needs oleans ModCurves.Glue, I3Linalg.TateBC, Conductor.Level (lake build running).

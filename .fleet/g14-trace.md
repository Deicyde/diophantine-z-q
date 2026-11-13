# g14-trace (fleet summary)

**Result.** `G0ModNewform.G14TraceCompat D` (r₃ and r₅ in one compatible system) is copied
verbatim and reduced, for the data `D` that G8 constructs, to:
- the leaf T7 (`PkgI3.CharPolyIndepOfEll`, Mumford §19 Thm 4);
- one new AV-side glue Prop, `G14Trace.FrobTraceLink A Tm₅ Tm₃`. At a Frobenius `τ` outside a
  finite set, `N·Tm_ℓ(τ)` is conjugate to `V_ℓ(α')` for one endomorphism `α'` of an abelian
  variety in characteristic `p`, at `ℓ = 3, 5` (the kernel's `GlueC10Link.FrobCompare`). It has a
  square form, `FrobSquaresLink`, which implies it (proved);
- a scalar link: the descent scalars at 3 and at 5 are `j_ℓ ∘ a` and `j_ℓ ∘ β` for one pair
  `a, β : G_ℚ → ℚ̄`.

The main theorem is `G14Trace.g14TraceCompat_of_link`. `g12Spec_g14_of_galois` and
`g12Spec_g14_of_linked` combine it with G12 to give `∃ D, G12Spec D ∧ G14TraceCompat D`: `ι₅` is
Pan's embedding, and `ι₃ := j₃ ∘ γ` with `ι₅ = j₅ ∘ γ` (`exists_comp_eq`, proved).

**Finding (interface defect, VERIFIED in Lean).** g0-mod-field's `TateBridge` gives the ℓ-adic
data at each `ℓ` separately. `G7Out` at one `ℓ` is invariant under `a ↦ χ·a` for any character
`χ` of `Gal(L'/ℚ)` (`g7Out_twist`), and that twist multiplies the traces by `χ`
(`trace_rho_twist`, `twist_obstruction`). So `G14TraceCompat` can fail for data that `TateBridge`, as stated, allows
(given a nontrivial character of `Gal(L'/ℚ)`, `r₃ ≇ r₃⊗χ` and a fixed `ι₃`). The correction is `G14Bridge.TateBridge35`: the linked form at `ℓ = 3, 5`, over
`G7Data` (also ties `β` to `G7Data`'s `β`). It contains `TateBridge`'s conclusions at 3 and 5
(proved).

**Compiles (VERIFIED).**
- `scratch/g14-trace/G14Trace.lean` (`build.sh`: g0-mod-newform copies plus `part_g14.lean`):
  exit 0, no sorry, 31 axiom prints, all `[propext, Classical.choice, Quot.sound]`.
- `scratch/g14-trace/G14Bridge.lean` (`build_bridge.sh`: ModField copy plus `part_bridge.lean`):
  exit 0, no sorry, standard axioms.

**Remains.**
- `FrobTraceLink` / `FrobSquaresLink` for the genuine `A/L'`. This is glue: good reduction,
  Serre–Tate reduction of `V_ℓ`, the Néron mapping property, and the relative Frobenius.
- `TateBridge35`: the Tate functor on G7's points-level data. It is glue, like `TateBridge`, and
  should replace `TateBridge` at 3 and 5.

One model review: no substantive defect; its minor points were applied and recompiled.
No new leaf. Report: `docs/research/g14-trace.md`; log: `scratch/g14-trace/log.md`.

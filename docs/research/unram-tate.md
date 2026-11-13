# unram-tate: the glue Props `UnramifiedSup` and `TateBridge` (g0-mod-field)

Task unram-tate, 2026-11-13. Lean: `scratch/unram-tate/` (`UnramSup.lean`, `QuatUnits.lean`,
`BCPoints.lean`, `TateBridge.lean`). Log: `scratch/unram-tate/log.md`. Both Props are copied
verbatim from `scratch/g0-mod-field/ModField.lean` (L704-706 and L1021-1035).

## 1. Result

* **`UnramifiedSup` is proved, with no leaf:** `UnramTate.unramifiedSup : UnramifiedSup`
  (`UnramSup.lean`). The same proof is repeated in `TateBridge.lean` as
  `unramifiedSup_mf : G0ModField.UnramifiedSup`. That file also gives g0-mod-field's composites
  without the hypothesis: `fieldDescentUnr'` and `modularConstituent_of_ranges_T14'`.
* **`TateBridge` is proved from the leaf I3.M0 `PkgI3.TateModuleFree` alone:**
  `UnramTate.tateBridge_of_tateModuleFree (hT : PkgI3.TateModuleFree) : G0ModField.TateBridge`
  (`TateBridge.lean`). This leaf is already in the bundle (Mumford, *Abelian Varieties* §18-19:
  `T_ℓ(A)` is free of rank `2 dim A`; locator as given in pkg-I3, UNVERIFIED here). It is used only
  for the continuity clause. No new leaf and no new glue Prop is left.

VERIFIED: `lake env lean` (Lean 4.35.0, Mathlib v4.35.0) on all four files gives exit 0, 0 errors
and no `sorry`. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for
`unramifiedSup`, `unramifiedSup_mf`, `modularConstituent_of_ranges_T14'`,
`matrixUnits_of_quat`, `opVHom`, `jO_sq`, `bcPt`, `bcPt_galAct`, `trPt_galAct`, `tatePoints`,
`endBaseChange`, `scalarTransfer`, `tateCont_of_tateModuleFree`, `resQEmbedding`,
`tateBridge_of_pieces` and `tateBridge_of_tateModuleFree`.

No statement was changed. Neither Prop is false or vacuous. `TateBridge` has real content: its
`G7Out` makes `ρ = β'⁻¹ a T` a continuous representation of `G_ℚ` on `ℚ̄_ℓ ⊗ V_ℓ(A_{L'})` that
extends the Tate representation of `G_{L'}`. A degenerate choice is ruled out: `β' ≠ 0` forces
`ε' ≠ 0`, and then `a(g)a(g⁻¹)c(g,g⁻¹) = ε'(g,g⁻¹)` forces every `T_g` to be invertible. The content
comes from `G7Data`'s descent datum (the maps `m_σ` on `A(ℚ̄)`). `TateBridge` applies the Tate
functor to that datum, as g0-mod-field §3 intended.

## 2. `UnramifiedSup` (proved)

Statement: for `E, K ⊆ ℚ̄` finite Galois over `ℚ` and `p : ℕ`, `UnramifiedAt E p →
UnramifiedAt K p → UnramifiedAt (E ⊔ K) p`. Here `UnramifiedAt` is glue-descent's: every prime of
`𝓞` containing `p` has `ramificationIdx ℤ = 1`.

Proof: let `M = E ⊔ K` and `Q ∋ p` be a prime of `𝓞 M`. Take `g` in Mathlib's inertia group
`Q.inertia Gal(M/ℚ)` and lift it to `s = g.liftNormal ℚ̄`. Then `s.restrictNormal E` lies in the
inertia group of `Q ∩ 𝓞 E`, where `𝓞 E → 𝓞 M` is `RingOfIntegers.mapRingHom` of the inclusion. That
inertia group is trivial, because `#I = e = 1`
(`Ideal.card_inertia_eq_ramificationIdxIn`, `Ideal.ramificationIdxIn_eq_ramificationIdx`). So `s`
fixes `E`, and likewise `K`. Hence `s` fixes `E ⊔ K` (`IntermediateField.le_iff_le`), so `g = 1`
and `e(Q) = #I(Q) = 1`. The argument covers every `p : ℕ` with no case split.

## 3. `TateBridge` (proved from leaf I3.M0)

`TateBridge.lean` contains `ModField.lean` L1-1036 verbatim, plus one extra import,
`ZInQKernel.HDecomp.I3Linalg.RhoCont`, followed by the section `UnramTate`.

**Assembly (`tateBridge_of_pieces`).** The inputs are `G7Data` (descent datum `m`, `a`, `ε` of
`A/L`; `β`; `G_{L'} = G_L ∩ ker β`), the QM model, and `Θ`, `h` from `TatePoints`. From these:
* `Tm g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)`, where `opV φ = ℚ̄_ℓ ⊗ ℚ_ℓ ⊗ T_ℓ(φ)` (pkg-I3's `Tate.map`
  base changed twice). It is a ring homomorphism `End(A(\bar K)) → End_{ℚ̄_ℓ}(Vb)` (`opVHom`).
* `c = ε' = n/d`, evaluated at the conjugated arguments. From `d·m_σm_τ = n·m_{στ}` this gives
  `Tm g Tm g' = c • Tm(gg')`. Also `a = 1` and `β'(g) = γ(hgh⁻¹)`, so `∂β' = c`.
* `Tm(resQ σ) = tate σ`. Here `hσ̃h⁻¹ ∈ G_{L'} ⊆ G_L` (`G_{L'}` is normal), so DescentDatum's
  clause `m_k = galAct k` applies, and `Θ` intertwines the actions. Also `a = β' = 1` on `G_{L'}`.
* The matrix units come from `I = opV(Θ∘ι(i)∘Θ⁻¹)` and `J = opV(Θ∘ι(j)∘Θ⁻¹)`, where `i² = 2`,
  `j² = -3`, `ij = -ji` in `𝒪 ⊆ (2,-3)_ℚ` (`iO_sq`, `jO_sq`, `iO_jO`) and `ι` is the QM structure
  base changed to `L`. The units are `e₀₀ = (1 + I/√2)/2`, `e₁₁ = 1 - e₀₀`, `e₀₁ = e₀₀J`,
  `e₁₀ = -(1/3)Je₀₀` (`matrixUnits_of_quat`). `Tm g` commutes with them by DescentDatum's
  commutation clause.
* Continuity: `ρ(g₀·resQ σ) = ρ(g₀)·tate σ` (glue-descent's `rho_map_mul`). `σ ↦ g₀·resQ σ` is an
  open embedding, and `σ ↦ f(tate σ v)` is continuous.

**The five pieces** (each first stated as a `def … : Prop`, then proved):

| piece | content | proof |
|---|---|---|
| `TatePoints` | `Θ : A(ℚ̄) ≅+ A_{L'}(\overline{L'})`, `h ∈ G_ℚ`, `Θ ∘ (h·resQ σ·h⁻¹) = σ ∘ Θ` | `tatePoints`. `bcPt : A_L(Ω) ≃* A(Ω)` comes from `Over.mapPullbackAdj`; it is multiplicative by `Functor.map_mul` and `MonObj.comp_mul`, and Galois-natural by `homEquiv_naturality_left_symm`. `trPt` is the transport along `φ = IsAlgClosure.equiv L' \overline{L'} ℚ̄`. `h = φ∘g`, with `g` from `resQ_comm'`. |
| `EndBaseChange` | ring hom `End_K(A) → End_L(A_L)` | `endBaseChange` (bp-qmmoduli's `endBC`, copied) |
| `ScalarTransfer` | `γ : G_ℚ → ℚ̄_ℓ^×` with `∂γ = n/d`, constant on `G_{L'}`-cosets, `1` on `G_{L'}` | `scalarTransfer`. `γ_ℂ = β/a`, and `γ_ℂ(σ)^r ∈ ℚ` where `r` is the order of `σ|_{L'}`, so every value is integral. `ℚ(γ_ℂ(G_ℚ))` is algebraic and maps into `ℚ̄_ℓ` by `IsAlgClosed.lift`. |
| `TateCont` | `σ ↦ f(ρ_ℓ(σ) v)` continuous on `ℚ̄_ℓ ⊗ V_ℓ(A)` | `tateCont_of_tateModuleFree`: **leaf I3.M0**, glue-rho-cont's `continuous_galRep_of_tateModuleFree`, induction on tensors, `IsModuleTopology.continuous_of_linearMap` |
| `ResQEmbedding` | `resQ L'` is an open embedding | `resQEmbedding`: continuous, injective (`g` is onto), `G_{L'}` compact, image `Fix(L')` open (`resQRange`) |

Group compatibility of base-change points (`bcPt`) is new. h5-glue's `ptsBaseChangeEquiv` is only
a bijection of sets. `BCPoints.lean` proves it standalone and imports only `HDecomp.Objects`.

## 4. Integration

* `UnramSup.lean` imports only `ZInQKernel.HDecomp.Descent.B2Glue` and can become an `HDecomp`
  module as it stands.
* The section `UnramTate` of `TateBridge.lean` can be appended to `ModField.lean`, which needs the
  extra import of `RhoCont`. Then `UnramifiedSup` and `TateBridge` leave the list of open glue
  for `ModularConstituent`. What remains of g0-mod-field's range is `FibreCoverExists` and
  `KernelFieldExists` (the latter is blocked by qm-pin), the B2 leaves, and `AfterG7`.
  `TateBridge` adds the leaf I3.M0. The copy of `endBC` duplicates bp-qmmoduli's; keep one.
* Pitfalls (VERIFIED):
  * In a file that opens `MonObj`, `mul_assoc`, `one_mul` and `mul_one` are ambiguous; use
    `_root_.`. `γ` and `ι` are tokens there.
  * `GQ` (`Field.absoluteGaloisGroup ℚ`) and `PkgI4.GQ` (`ℚ̄ ≃ₐ[ℚ] ℚ̄`) are defeq but break `rw`
    motives. The same holds for `AddMonoid.End M` against `M →+ M`, and `A.Pt Ω` against the
    underlying hom type. Restate terms at one type (`let m' : _ → AddMonoid.End _ := m`).
  * `AlgebraicClosure L'` already carries `Algebra L _` from `Algebra L L'`. A second `letI` gives
    an SMul diamond.
  * A type ascription `Continuous fun σ => A.galRep ℓ σ w` times out at `whnf`; leave it to
    inference.

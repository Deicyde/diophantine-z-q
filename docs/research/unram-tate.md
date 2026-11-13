# unram-tate: the glue Props `UnramifiedSup` and `TateBridge` (g0-mod-field)

Task unram-tate, 2026-11-13. Lean: `scratch/unram-tate/` (`UnramSup.lean`, `QuatUnits.lean`,
`TateBridge.lean`). Log: `scratch/unram-tate/log.md`. Both Props are copied verbatim from
`scratch/g0-mod-field/ModField.lean` (L704-706 and L1021-1035).

## 1. Result

* **`UnramifiedSup` is proved, with no leaf.** `UnramTate.unramifiedSup : UnramifiedSup`
  (`scratch/unram-tate/UnramSup.lean`).
* **`TateBridge` is reduced to one named glue Prop, `TatePoints`, plus the existing leaf I3.M0
  `PkgI3.TateModuleFree` (Mumford).** The reduction is proved:
  `UnramTate.tateBridge_of_tatePoints (hP : TatePoints) (hT : PkgI3.TateModuleFree) : G0ModField.TateBridge`
  (`scratch/unram-tate/TateBridge.lean`). Of the five glue pieces that the assembly
  `tateBridge_of_pieces` uses, four are proved here (`EndBaseChange`, `ScalarTransfer`,
  `TateCont` from the leaf, `ResQEmbedding`). The fifth, `TatePoints`, is stated in Lean and not
  proved (see §3 for the proof plan).

VERIFIED (compiled, Lean 4.35.0 / Mathlib v4.35.0, `lake env lean`, 0 errors, no `sorry`).
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `unramifiedSup`,
`matrixUnits_of_quat`, `opVHom`, `jO_sq`, `tateBridge_of_pieces`, `resQEmbedding`,
`tateCont_of_tateModuleFree`, `scalarTransfer`, `endBaseChange`, `tateBridge_of_points` and
`tateBridge_of_tatePoints`.

No statement was changed. Neither Prop is false or vacuous. `TateBridge` has real content: its
`G7Out` makes `ρ = β'⁻¹ a T` a continuous representation of `G_ℚ` on `ℚ̄_ℓ ⊗ V_ℓ(A_{L'})` that
extends the Tate representation of `G_{L'}`. A degenerate choice (for example `T_g = 0` off `G_{L'}`)
is ruled out: `β' ≠ 0` forces `ε' ≠ 0`, and then `a(g)a(g⁻¹)c(g,g⁻¹) = ε'(g,g⁻¹)` forces every
`T_g` to be invertible.

## 2. `UnramifiedSup` (proved)

Statement (verbatim): for `E, K ⊆ ℚ̄` finite Galois over `ℚ` and `p : ℕ`, `UnramifiedAt E p →
UnramifiedAt K p → UnramifiedAt (E ⊔ K) p`. Here `UnramifiedAt` is glue-descent's: every prime of `𝓞`
containing `p` has `ramificationIdx ℤ = 1`.

Proof: let `M = E ⊔ K` and `Q ∋ p` be a prime of `𝓞 M`. Take `g` in Mathlib's inertia group
`Q.inertia Gal(M/ℚ)` and lift it to `s = g.liftNormal ℚ̄`. Then `s.restrictNormal E` lies in the
inertia group of `Q ∩ 𝓞 E`, where `𝓞 E → 𝓞 M` is `RingOfIntegers.mapRingHom` of the inclusion. That
inertia group is trivial, because `#I = e = 1`
(`Ideal.card_inertia_eq_ramificationIdxIn`, `Ideal.ramificationIdxIn_eq_ramificationIdx`). So `s`
fixes `E`, and likewise `K`. Hence `s` fixes `E ⊔ K` (Galois connection
`IntermediateField.le_iff_le`), so `g = 1` and `e(Q) = #I(Q) = 1`. The argument covers every
`p : ℕ`, including `p = 0`, with no case split.

## 3. `TateBridge` (reduced)

`scratch/unram-tate/TateBridge.lean` contains `ModField.lean` L1-1036 verbatim, plus one extra
import, `ZInQKernel.HDecomp.I3Linalg.RhoCont`, followed by the section `UnramTate`.

**Construction (proved, `tateBridge_of_pieces`).** The inputs are `G7Data` (descent datum `m`,
`a`, `ε` of `A/L`; `β`; `G_{L'} = G_L ∩ ker β`), the QM model, and `Θ : A(ℚ̄) ≅ A_{L'}(\overline{L'})`
with `h ∈ G_ℚ` from `TatePoints`. From these:
* `Tm g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)`, where `opV φ = ℚ̄_ℓ ⊗ ℚ_ℓ ⊗ T_ℓ(φ)` (pkg-I3's `Tate.map`). It is a
  ring homomorphism `End(A(\bar K)) → End_{ℚ̄_ℓ}(Vb)` (`opVHom`, proved).
* `c = ε' = n/d`, evaluated at the conjugated arguments. From `d·m_σm_τ = n·m_{στ}` this gives
  `Tm g Tm g' = c • Tm(gg')`.
* `a = 1`, and `β'(g) = γ(hgh⁻¹)` with `γ` from `ScalarTransfer`, so `∂β' = c`.
* `Tm(resQ σ) = tate σ`. Here `hσ̃h⁻¹ ∈ G_{L'} ⊆ G_L` (`G_{L'}` is normal), so DescentDatum's
  clause `m_k = galAct k` applies, and `Θ` intertwines the actions. Also `a = β' = 1` on `G_{L'}`.
* The matrix units come from `I = opV(Θ∘ι(i)∘Θ⁻¹)` and `J = opV(Θ∘ι(j)∘Θ⁻¹)`, where `i² = 2`,
  `j² = -3`, `ij = -ji` in `𝒪` (`iO_sq`, `jO_sq`, `iO_jO`) and `ι` is the QM structure base changed
  to `L` (`EndBaseChange`). The units are `e₀₀ = (1 + I/√2)/2`, `e₁₁ = 1 - e₀₀`, `e₀₁ = e₀₀J`,
  `e₁₀ = -(1/3)Je₀₀` (`matrixUnits_of_quat`). `Tm g` commutes with them by DescentDatum's
  commutation clause.
* Continuity: `ρ(g₀·resQ σ) = ρ(g₀)·tate σ` (glue-descent's `rho_map_mul`). `σ ↦ g₀·resQ σ` is an
  open embedding (`ResQEmbedding`). `TateCont` gives the continuity of `σ ↦ f(tate σ v)`.

**The five pieces** (each a `def … : Prop` with a docstring; all are glue, none is a new leaf):

| piece | content | status |
|---|---|---|
| `TatePoints` | `Θ : A(ℚ̄) ≅+ A_{L'}(\overline{L'})` and `h ∈ G_ℚ` with `Θ ∘ (h·resQ σ·h⁻¹) = σ ∘ Θ` on points | **open** (plan below) |
| `EndBaseChange` | ring hom `End_K(A) → End_L(A_L)` | proved (`endBaseChange`, bp-qmmoduli's `endBC` copied) |
| `ScalarTransfer` | `γ : G_ℚ → ℚ̄_ℓ^×` with `∂γ = n/d`, constant on `G_{L'}`-cosets, `1` on `G_{L'}` | proved (`scalarTransfer`) |
| `TateCont` | `σ ↦ f(ρ_ℓ(σ) v)` continuous on `ℚ̄_ℓ ⊗ V_ℓ(A)` | proved from leaf I3.M0 (`tateCont_of_tateModuleFree`, via glue-rho-cont) |
| `ResQEmbedding` | `resQ L'` is an open embedding | proved (`resQEmbedding`) |

* `scalarTransfer`: `γ_ℂ = β/a` has `∂γ_ℂ = n/d`. `γ_ℂ(σ)^r ∈ ℚ`, where `r` is the order of `σ|_{L'}`
  (`AlgEquiv.restrictNormalHom`), so every value is integral over `ℚ`.
  `ℚ(γ_ℂ(G_ℚ)) ⊆ ℂ` is algebraic (`IntermediateField.isAlgebraic_adjoin`), and
  `ψ = IsAlgClosed.lift` sends it into `ℚ̄_ℓ`. No finiteness of the value set is needed.
* `resQEmbedding`: `Field.absoluteGaloisGroup.map` is a continuous homomorphism. It is injective,
  because the embedding `ℚ̄ → \overline{L'}` of `resQ_comm'` is onto. `G_{L'}` is compact, and its
  image `Fix(L')` is open (`resQRange`, `fixingSubgroup_isOpen`).

**Plan for `TatePoints` (glue, SPECULATIVE size about 150-250 lines).**
1. The points of the base change, `A_{L'}(Ω) ≃ A(Ω)`, come from `Over.mapPullbackAdj`
   (h5-glue's `ptsBaseChangeEquiv` builds this bijection for complex points) together with
   `(Over.map f).obj (Spec Ω/L') ≅ Spec Ω/L` (`Over.isoMk (Iso.refl _)`). The bijection is a group
   map: `homEquiv f = η ≫ G.map f`, and `Functor.map_mul` (used in `endBC`) together with
   `MonObj.comp_mul` gives multiplicativity.
2. Take `φ : \overline{L'} ≃ₐ[L'] ℚ̄` (`IsAlgClosure.equiv`). Precomposition with
   `Over.homMk (Spec.map φ)` is a group isomorphism `A(\overline{L'}) ≅ A(ℚ̄)`.
3. Galois compatibility follows from `Adjunction.homEquiv_naturality_left_symm` and
   `Spec.map_comp`, with `σ' = φσφ⁻¹`. Take `h = φ ∘ g`, where `g` is the embedding of `resQ_comm'`,
   so that `h·resQ σ·h⁻¹ = φσφ⁻¹`.

## 4. What compiles, what remains

* Compiles: all three files, with no `sorry` and standard axioms (VERIFIED).
* Remains: `TatePoints` (glue). `TateBridge` also uses the leaf I3.M0 `TateModuleFree`, which is
  already in the bundle.
* Integration: `UnramSup.lean` imports only `ZInQKernel.HDecomp.Descent.B2Glue`. Its proof can
  replace the hypothesis `hSup` in `fieldDescent(Unr)` and `modularConstituent_of_ranges(_T14)`.
  The section `UnramTate` of `TateBridge.lean` can be appended to `ModField.lean` as it stands
  (it needs the extra import of `RhoCont`). Its copy of `endBC` duplicates bp-qmmoduli's.
* Pitfalls (VERIFIED). In a file that opens `MonObj`, `mul_assoc`, `one_mul` and `mul_one` are
  ambiguous; use `_root_.`. `γ` and `ι` are tokens there. `GQ` (`Field.absoluteGaloisGroup ℚ`) and
  `PkgI4.GQ` (`ℚ̄ ≃ₐ[ℚ] ℚ̄`) are defeq but break `rw` motives, so keep one type per term. A type
  ascription `Continuous fun σ => A.galRep ℓ σ w` times out at `whnf`; leave it to inference.

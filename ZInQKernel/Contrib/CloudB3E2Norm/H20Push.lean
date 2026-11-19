import ZInQKernel.Contrib.CloudB3E2Norm.StageRing

/-!
# The coefficient push (H20) as one named statement

Manuscript `diophantine_zq.tex`:
* tex 2724–2727: `A_i = (ℤ/2^iℤ)[t]/t^i`, `M_i = (T_2E ⊗ A_i)(χ_hΨ_i)`;
* tex 3203–3215 (paragraph 7, "The actual coefficient push and its local conditions"): "Reduce
  `b_{I,a}` to `E[2^m]`, extend coefficients freely to `A`, and only now use the character `θ` of
  `Δ_f`. Under Shapiro, followed by the equivariant coefficient map
  `E[2^m] ⊗ A[Δ_f] → (E[2^m] ⊗ A)(θ)`, `v ⊗ [δ] ↦ θ(δ) v` (H20), obtain the class `P_{I,m}`
  over `K`";
* tex 3281–3290: "the two horizontal Artin terms in (4.1) become `θ(σ_q)` and `θ(σ_q)⁻¹`, giving
  `a_q − θ(σ_q) − θ(σ_q)⁻¹` on the class".

The cochain-level norm identity of this directory (`TransferNorm.lean` … `LocalIdentity.lean`) is
meaningful at the Shapiro level: a coefficient ring that does not kill the points' division, e.g.
`ℤ[Δ_f]` with the universal character `δ ↦ [δ]` (not `A[Δ_f]` with the manuscript's
`A = (ℤ/2^m)[t]/t^b`, which also kills `2^m`: the identity can be pushed there after its integral
proof, but not reproved there from the present transfer hypotheses). At the stage ring
`A_i` (`2^i = 0`) its transfer hypotheses force the points to vanish. The actual classes over `A_i`
with `θ = χ_h Ψ_i` are obtained by applying the coefficient map (H20) to the Selmer complexes
afterwards. This file names that step and proves that the norm identity survives it:

* **`H20CoefficientPush`** (Prop; kind ELLIOT/GLUE: the coefficient push of tex 3203–3215 with
  its local conditions, tex 3262–3270): a ring homomorphism `φ : k₁ →+* k₂` from the
  Shapiro-level ring to the stage ring (for the text, `[δ] ↦ θ(δ)`), `φ`-semilinear maps `Φ⁰`, `Φ¹`
  of the Selmer complexes in degrees `0`, `1` commuting with the differential, the point factors
  related by `e₂ = φ(e₁)` (for the text, `a_q − [σ_q] − [σ_q]⁻¹ ↦ a_q − θ(σ_q) − θ(σ_q)⁻¹`, tex
  3281–3290), and `Φ¹` carrying `z_R¹ ↦ z_R²` and `i₁(z_P¹) ↦ i₂(z_P²)`. (Only degrees `0`, `1`
  are recorded: those are the degrees the norm identity uses.)
* **`hzR_of_H20`** (PROVED): the norm identity with retained boundary at the Shapiro level and
  `H20CoefficientPush` give the norm identity with retained boundary at the stage level, boundary
  `Φ⁰(b)`.
* Non-vacuity: `nonVacuity_H20` (the identity push of any data to itself).

Kinds: definitions and PROVED; `H20CoefficientPush` is the open statement.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.Wiring

variable {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂]

/-- **The coefficient push (H20) on Selmer complexes** (Prop; tex 3203–3215, 3262–3270,
3281–3290; kind ELLIOT/GLUE). A ring homomorphism `φ : k₁ →+* k₂` (for the text:
`ℤ[Δ_f] → A_i`, `[δ] ↦ θ(δ)`, `θ = χ_h Ψ_i`) with `e₂ = φ(e₁)`, and `φ`-semilinear maps `Φ⁰`, `Φ¹`
of the Selmer complexes in degrees `0`, `1` (for the text: Shapiro followed by `v ⊗ [δ] ↦ θ(δ) v`,
applied to the global cochains and to the local conditions, which survive by tex 3262–3270)
commuting with the differential and carrying `z_R¹ ↦ z_R²` and `i₁(z_P¹) ↦ i₂(z_P²)`. -/
def H20CoefficientPush (D₁ : SelData k₁) {U₁ : GCx k₁} (f₁ : GHom U₁ D₁.U)
    (zR₁ : (selCx D₁).X 1) (zP₁ : (selCx (selRestrict D₁ f₁)).X 1) (e₁ : k₁)
    (D₂ : SelData k₂) {U₂ : GCx k₂} (f₂ : GHom U₂ D₂.U)
    (zR₂ : (selCx D₂).X 1) (zP₂ : (selCx (selRestrict D₂ f₂)).X 1) (e₂ : k₂) : Prop :=
  ∃ (φ : k₁ →+* k₂) (Φ₀ : (selCx D₁).X 0 →ₛₗ[φ] (selCx D₂).X 0)
    (Φ₁ : (selCx D₁).X 1 →ₛₗ[φ] (selCx D₂).X 1),
    e₂ = φ e₁ ∧
    (∀ b, Φ₁ ((selCx D₁).d 0 1 rfl b) = (selCx D₂).d 0 1 rfl (Φ₀ b)) ∧
    Φ₁ zR₁ = zR₂ ∧
    Φ₁ ((changeMap D₁ f₁).f 1 1 rfl zP₁) = (changeMap D₂ f₂).f 1 1 rfl zP₂

/-- **The norm identity survives the coefficient push** (PROVED): from
`z_R¹ = e₁ • i₁(z_P¹) + d b` at the Shapiro level and `H20CoefficientPush`, the stage-level
identity `z_R² = e₂ • i₂(z_P²) + d b'` holds (with `b' = Φ⁰(b)`). -/
theorem hzR_of_H20 (D₁ : SelData k₁) {U₁ : GCx k₁} (f₁ : GHom U₁ D₁.U)
    (zR₁ : (selCx D₁).X 1) (zP₁ : (selCx (selRestrict D₁ f₁)).X 1) (e₁ : k₁)
    (D₂ : SelData k₂) {U₂ : GCx k₂} (f₂ : GHom U₂ D₂.U)
    (zR₂ : (selCx D₂).X 1) (zP₂ : (selCx (selRestrict D₂ f₂)).X 1) (e₂ : k₂)
    (h₁ : ∃ b, zR₁ = e₁ • (changeMap D₁ f₁).f 1 1 rfl zP₁ + (selCx D₁).d 0 1 rfl b)
    (hpush : H20CoefficientPush D₁ f₁ zR₁ zP₁ e₁ D₂ f₂ zR₂ zP₂ e₂) :
    ∃ b, zR₂ = e₂ • (changeMap D₂ f₂).f 1 1 rfl zP₂ + (selCx D₂).d 0 1 rfl b := by
  obtain ⟨b, hb⟩ := h₁
  obtain ⟨φ, Φ₀, Φ₁, he, hd, hR, hP⟩ := hpush
  refine ⟨Φ₀ b, ?_⟩
  rw [← hR, hb, map_add, LinearMap.map_smulₛₗ, hP, hd, he]

/-- **Non-vacuity of `H20CoefficientPush`** (Kind: PROVED): the identity push (`φ = id`) of any
Selmer data and classes to themselves. -/
theorem nonVacuity_H20 (D : SelData k₁) {U : GCx k₁} (f : GHom U D.U) (zR : (selCx D).X 1)
    (zP : (selCx (selRestrict D f)).X 1) (e : k₁) :
    H20CoefficientPush D f zR zP e D f zR zP e :=
  ⟨RingHom.id _, LinearMap.id, LinearMap.id, rfl, fun _ => rfl, rfl, rfl⟩

end ZInQ.Contrib.CloudB3E2.NormCochain

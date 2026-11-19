import ZInQKernel.Contrib.CloudB3E2Norm.H20Push

/-!
# The coefficient push (H20): the ring map, the character, and the transfer

Manuscript `diophantine_zq.tex`, tex 3203–3215 ("Under Shapiro, followed by the equivariant
coefficient map `E[2^m] ⊗ A[Δ_f] → (E[2^m] ⊗ A)(θ)`, `v ⊗ [δ] ↦ θ(δ) v` (H20), obtain the class
`P_{I,m}` over `K`") and tex 3281–3290 ("the two horizontal Artin terms in (4.1) become `θ(σ_q)` and
`θ(σ_q)⁻¹`, giving `a_q − θ(σ_q) − θ(σ_q)⁻¹` on the class").

* `h20RingHom θ` (definition): the ring homomorphism `ℤ[Δ] → A`, `[δ] ↦ θ(δ)`, of a character
  `θ : Δ →* Aˣ` (Mathlib's `MonoidAlgebra.lift`); `h20RingHom_of` (PROVED).
* `univChar` (definition): the universal character `δ ↦ [δ]` of `Δ` in `ℤ[Δ]ˣ`;
  `h20RingHom_univChar` (PROVED): `φ ∘ univChar = θ`.
* **`eq_transport`** (PROVED): for any ring homomorphism `φ` with `φ ∘ θ₁ = θ₂` on `G/H`, the point
  factors correspond: `φ(e_q(θ₁)) = e_q(θ₂)` (`a_q − [σ_q] − [σ_q]⁻¹ ↦ a_q − θ(σ_q) − θ(σ_q)⁻¹`).
* **`transfer_coeff`** (PROVED): the twisted transfer commutes with a `φ`-semilinear equivariant
  coefficient map `c` (`c(ρ₁(g) x) = ρ₂(g) c(x)`): `c(𝒯_{θ₁}(b)) = 𝒯_{θ₂}(c ∘ b)` in every degree; in
  particular (`transfer_kummer_coeff`) the pushed transferred Kummer class of `Q` is the
  transferred Kummer class of `c(Q)`. This is the naturality of the twisted transfer in the
  coefficients, not itself `(H20) ∘ Shapiro = 𝒯_θ`: that identity (at one ring) is the tree's
  `coeff_shapiro_eq_transfer` (tex 3203–3250); naturality is what carries it along `φ`.
* `nonVacuity_h20Ring`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Central (pointFactor)

/-! ### The ring homomorphism of a character -/

section RingMap

variable {Δ : Type*} [CommGroup Δ] {A : Type*} [CommRing A]

/-- **The ring homomorphism `ℤ[Δ] → A`, `[δ] ↦ θ(δ)`** of a character `θ : Δ →* Aˣ` (tex 3207,
(H20)). Kind: definition. -/
def h20RingHom (θ : Δ →* Aˣ) : MonoidAlgebra ℤ Δ →+* A :=
  (MonoidAlgebra.lift ℤ A Δ ((Units.coeHom A).comp θ)).toRingHom

@[simp] theorem h20RingHom_of (θ : Δ →* Aˣ) (δ : Δ) :
    h20RingHom θ (MonoidAlgebra.of ℤ Δ δ) = θ δ := by
  simp [h20RingHom]

/-- **The universal character** `δ ↦ [δ]` of `Δ` with values in `ℤ[Δ]ˣ`. Kind: definition. -/
def univChar (Δ : Type*) [CommGroup Δ] : Δ →* (MonoidAlgebra ℤ Δ)ˣ :=
  (MonoidAlgebra.of ℤ Δ).toHomUnits

/-- **`φ ∘ univChar = θ`** (PROVED). -/
theorem h20RingHom_univChar (θ : Δ →* Aˣ) (δ : Δ) :
    h20RingHom θ ((univChar Δ δ : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ) = θ δ :=
  h20RingHom_of θ δ

end RingMap

/-! ### The point factor -/

section PointFactor

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal] {k₁ k₂ : Type*} [CommRing k₁]
  [CommRing k₂]

/-- **The point factor is transported by the ring map** (PROVED; tex 3281–3290): for `φ` with
`φ(θ₁(x)) = θ₂(x)`, `φ(a − θ₁(σ) − θ₁(σ)⁻¹) = a − θ₂(σ) − θ₂(σ)⁻¹`. -/
theorem eq_transport (φ : k₁ →+* k₂) (θ₁ : G ⧸ H →* k₁ˣ) (θ₂ : G ⧸ H →* k₂ˣ)
    (hφ : ∀ x, φ (θ₁ x : k₁) = θ₂ x) (a : ℤ) (σ : G) :
    φ (eq_ H θ₁ a σ) = eq_ H θ₂ a σ := by
  have hinv : ∀ x, φ (((θ₁ x)⁻¹ : k₁ˣ) : k₁) = ((θ₂ x)⁻¹ : k₂ˣ) := by
    intro x
    rw [← map_inv, ← map_inv, hφ]
  simp only [eq_, pointFactor, frobValue, frobValueInv, map_sub, map_intCast, hφ, hinv]

end PointFactor

/-! ### The transfer commutes with a semilinear coefficient map -/

section Transfer

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal] [Fintype (G ⧸ H)]
  (r : G ⧸ H → G) (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ)
  {k₁ k₂ : Type*} [CommRing k₁] [CommRing k₂] (φ : k₁ →+* k₂)
  {D₁ D₂ : Type*} [AddCommGroup D₁] [Module k₁ D₁] [AddCommGroup D₂] [Module k₂ D₂]
  (ρ₁ : G →* Module.End k₁ D₁) (ρ₂ : G →* Module.End k₂ D₂)
  (θ₁ : G ⧸ H →* k₁ˣ) (θ₂ : G ⧸ H →* k₂ˣ) (c : D₁ →ₛₗ[φ] D₂)

omit [Fintype (G ⧸ H)] in
/-- The coefficient map intertwines the twisted actions `R = θ ρ`. Kind: PROVED. -/
theorem coeff_R (hφ : ∀ x, φ (θ₁ x : k₁) = θ₂ x) (hc : ∀ g x, c (ρ₁ g x) = ρ₂ g (c x)) (g : G)
    (x : D₁) : c (R H ρ₁ θ₁ g x) = R H ρ₂ θ₂ g (c x) := by
  simp only [R, LinearMap.smul_apply, LinearMap.map_smulₛₗ, hφ, hc]

/-- **The twisted transfer commutes with a semilinear equivariant coefficient map** (PROVED; tex
3203–3250): `c(𝒯_{θ₁}(b)) = 𝒯_{θ₂}(c ∘ b)`. -/
theorem transfer_coeff (hφ : ∀ x, φ (θ₁ x : k₁) = θ₂ x) (hc : ∀ g x, c (ρ₁ g x) = ρ₂ g (c x))
    (n : ℕ) (b : (Fin n → H) → D₁) (g : Fin n → G) :
    c (T H r hr ρ₁ θ₁ n b g) = T H r hr ρ₂ θ₂ n (fun x => c (b x)) g := by
  simp only [T, map_sum, coeff_R H φ ρ₁ ρ₂ θ₁ θ₂ c hφ hc]

/-- **The pushed transferred Kummer class is the transferred Kummer class of the pushed point**
(PROVED). -/
theorem transfer_kummer_coeff (hφ : ∀ x, φ (θ₁ x : k₁) = θ₂ x)
    (hc : ∀ g x, c (ρ₁ g x) = ρ₂ g (c x)) (Q : D₁) (g : Fin 1 → G) :
    c (T H r hr ρ₁ θ₁ 1 (kummerCochain ρ₁ H Q) g) =
      T H r hr ρ₂ θ₂ 1 (kummerCochain ρ₂ H (c Q)) g := by
  rw [transfer_coeff H r hr φ ρ₁ ρ₂ θ₁ θ₂ c hφ hc]
  congr 1
  funext x
  simp only [kummerCochain, map_sub, hc]

/-- **The retained boundary is pushed to the retained boundary** (PROVED). -/
theorem retainedBoundaryT_coeff (HP HR : Subgroup G) [HP.Normal] [HR.Normal]
    [Fintype (G ⧸ HP)] [Fintype (G ⧸ HR)] (rP : G ⧸ HP → G) (rR : G ⧸ HR → G)
    (θP₁ : G ⧸ HP →* k₁ˣ) (θR₁ : G ⧸ HR →* k₁ˣ) (θP₂ : G ⧸ HP →* k₂ˣ) (θR₂ : G ⧸ HR →* k₂ˣ)
    (hφP : ∀ x, φ (θP₁ x : k₁) = θP₂ x) (hφR : ∀ x, φ (θR₁ x : k₁) = θR₂ x)
    (hc : ∀ g x, c (ρ₁ g x) = ρ₂ g (c x)) (a : ℤ) (σ : G) (QR QP : D₁) :
    c (retainedBoundaryT ρ₁ HP HR rP rR θP₁ θR₁ a σ QR QP) =
      retainedBoundaryT ρ₂ HP HR rP rR θP₂ θR₂ a σ (c QR) (c QP) := by
  simp only [retainedBoundaryT, wsum, map_sub, map_sum, LinearMap.map_smulₛₗ,
    coeff_R HR φ ρ₁ ρ₂ θR₁ θR₂ c hφR hc, coeff_R HP φ ρ₁ ρ₂ θP₁ θP₂ c hφP hc,
    eq_transport HP φ θP₁ θP₂ hφP]

end Transfer

/-! ### Non-vacuity -/

/-- **Non-vacuity**: for the trivial group `Δ` and the trivial character into `ℤ/4`, the ring map
`ℤ[Δ] → ℤ/4` sends `[1]` to `1`. Kind: PROVED. -/
theorem nonVacuity_h20Ring :
    h20RingHom (1 : Unit →* (ZMod 4)ˣ) (MonoidAlgebra.of ℤ Unit ()) = 1 := by
  rw [h20RingHom_of]; rfl

end ZInQ.Contrib.CloudB3E2.NormCochain

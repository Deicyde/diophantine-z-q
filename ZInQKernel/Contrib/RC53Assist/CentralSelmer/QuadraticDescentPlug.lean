import ZInQKernel.Contrib.RC53Assist.CentralSelmer.Comparison
import ZInQKernel.Contrib.RC53Assist.CentralSelmer.QuadraticDescent

/-!
# The genuine quadratic descent in the central Selmer comparison

`centralSelmerComparisonOfSpecializedModel` takes a group `S`, a bounded-defect map
`j : (Fin r → ℚ₂/ℤ₂) →+ S` and a bounded-defect map `f : S →+ fullSelmerProduct E E'`.
Here `S` and `f` are pinned to the genuine objects:

* `S = Sel_{2^∞}(E_ℓ/K)` for `K = ℚ(√k)` (`SelK ℓ k`): local triviality at every place of `K`
  of the image in `H¹(G_K, E_ℓ(ℚˢ))`;
* `f` is the corestriction pair `x ↦ (cor x, cor (ψ x))`, where `ψ : E_ℓ ≃ E_ℓ^{(k)}` is the
  twist isomorphism over `K`, followed by the identification of
  `Sel_{2^∞}(E_ℓ/ℚ) × Sel_{2^∞}(E_ℓ^{(k)}/ℚ)` with `fullSelmerProduct`;
* its kernel and cokernel are killed by `2` (`descentToProduct_boundedDefects`);
* consequently `V₂ Sel_{2^∞}(E_ℓ/K) ≅ V₂ Sel_{2^∞}(E_ℓ/ℚ) × V₂ Sel_{2^∞}(E_ℓ^{(k)}/ℚ)`
  (`ratTateSelKEquiv`), the identity `s₂(E/K) = s₂(E/ℚ) + s₂(E^{(k)}/ℚ)` of lines 2616--2626
  (`finrank_ratTate_selK`), and the eigenspace decomposition under the genuine action of
  `Gal(K/ℚ)` on `Sel_{2^∞}(E_ℓ/K)` (`ratTateSelKEigenspaceEquiv`), whose invariant and
  anti-invariant parts are `Sel_{2^∞}(E_ℓ/ℚ)` and `Sel_{2^∞}(E_ℓ^{(k)}/ℚ)` up to defects killed
  by `2` (`positiveDescent_boundedDefects`, `negativeDescent_boundedDefects`).

The universal-coefficient map `j` and the rational Kummer complex with its retained
quasi-isomorphism remain inputs.
-/

noncomputable section

namespace ZInQ.Manuscript.RC53Assist.QuadraticDescent

open ZInQ.Manuscript.RC53Assist.CentralSelmer ZInQ.Manuscript.RC.BaseZeroLimit
open ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC ZInQ.Contrib.CloudB3RC53
open TauCeti TauCeti.ContCohomology CategoryTheory Matrix

/-- Bounded defects are preserved by composing with an additive equivalence. -/
theorem boundedDefects_addEquiv_comp {M N P : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] (f : M →+ N) (e : N ≃+ P) (hf : BoundedDefects f) :
    BoundedDefects (e.toAddMonoidHom.comp f) := by
  obtain ⟨a, b, ha, hb, hk, hc⟩ := hf
  refine ⟨a, b, ha, hb, fun x hx => hk x ?_, fun y => ?_⟩
  · simpa using hx
  · obtain ⟨x, hx⟩ := hc (e.symm y)
    refine ⟨x, ?_⟩
    simp [hx]

/-- **The genuine quadratic descent map** `Sel_{2^∞}(E_ℓ/ℚ(√k)) → fullSelmerProduct`. -/
def descentToProduct (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) :
    SelK ℓ k →+ fullSelmerProduct (Ecurve ℓ) (Etw ℓ k) :=
  (fullSelmerProductAddEquiv (Ecurve ℓ) (Etw ℓ k)).symm.toAddMonoidHom.comp
    (quadraticDescent ℓ hk)

/-- The genuine quadratic descent map has bounded defects. -/
theorem descentToProduct_boundedDefects (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) :
    BoundedDefects (descentToProduct ℓ hk) :=
  boundedDefects_addEquiv_comp _ _ (quadraticDescent_boundedDefects ℓ hk)

/-- **The rational Tate module of `Sel_{2^∞}(E_ℓ/ℚ(√k))` is the product of the two rational
ones**, by the isomorphism induced by the genuine descent map. -/
def ratTateSelKEquiv (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) :
    RatTate (SelK ℓ k) ≃ₗ[ℚ_[2]]
      RatTate (selmerTwoPower (Ecurve ℓ)) × RatTate (selmerTwoPower (Etw ℓ k)) :=
  (ratTateEquivOfBoundedDefects (descentToProduct ℓ hk) (descentToProduct_boundedDefects ℓ hk)).trans
    (fullSelmerProductRatTateEquiv (Ecurve ℓ) (Etw ℓ k))

/-- **`s₂(E/K) = s₂(E/ℚ) + s₂(E^{(k)}/ℚ)`** (lines 2616--2626) for the genuine Selmer groups:
the rational Tate module of `Sel_{2^∞}(E_ℓ/ℚ(√k))` has dimension `r₁ + r₂`. -/
theorem finrank_ratTate_selK (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) {r₁ r₂ : ℕ}
    (h₁ : Z2Corank (selmerTwoPower (Ecurve ℓ)) r₁) (h₂ : Z2Corank (selmerTwoPower (Etw ℓ k)) r₂) :
    Module.finrank ℚ_[2] (RatTate (SelK ℓ k)) = r₁ + r₂ := by
  have := finiteDimensional_ratTate_prod_of_Z2Corank h₁ h₂
  rw [(ratTateSelKEquiv ℓ hk).finrank_eq, finrank_ratTate_prod_of_Z2Corank h₁ h₂]

/-- Under `SelmerCorankOneOverK ℓ k`, the full Selmer group over `K = ℚ(√k)` has rational
corank one, as in the hypothesis of the base-zero lemma. -/
theorem finrank_ratTate_selK_eq_one (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ))
    (hSel : SelmerCorankOneOverK ℓ k) : Module.finrank ℚ_[2] (RatTate (SelK ℓ k)) = 1 :=
  finrank_ratTate_selK ℓ hk hSel.1 hSel.2

/-- **The eigenspace decomposition of `V₂ Sel_{2^∞}(E_ℓ/ℚ(√k))` under `Gal(K/ℚ)`**, by the
sum-and-difference map of the genuine Galois involution. -/
def ratTateSelKEigenspaceEquiv (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) :
    RatTate (SelK ℓ k) ≃ₗ[ℚ_[2]]
      RatTate (positivePart (selKConj ℓ hk)) × RatTate (negativePart (selKConj ℓ hk)) :=
  ratTateEigenspaceEquiv (selKConj ℓ hk) (selKConj_selKConj ℓ hk)

theorem mem_positivePart_iff {S : Type*} [AddCommGroup S] (τ : S →+ S) (x : S) :
    x ∈ positivePart τ ↔ τ x = x := by
  rw [positivePart, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
    sub_eq_zero]

theorem mem_negativePart_iff {S : Type*} [AddCommGroup S] (τ : S →+ S) (x : S) :
    x ∈ negativePart τ ↔ τ x = -x := by
  rw [negativePart, AddMonoidHom.mem_ker, AddMonoidHom.add_apply, AddMonoidHom.id_apply,
    add_eq_zero_iff_eq_neg]

/-- Corestriction on the `Gal(K/ℚ)`-invariant part of `Sel_{2^∞}(E_ℓ/K)`. -/
def positiveDescent (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) :
    positivePart (selKConj ℓ hk) →+ selmerTwoPower (Ecurve ℓ) :=
  ((AddMonoidHom.fst _ _).comp (quadraticDescent ℓ hk)).comp (positivePart (selKConj ℓ hk)).subtype

/-- Twisted corestriction on the anti-invariant part of `Sel_{2^∞}(E_ℓ/K)`. -/
def negativeDescent (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) :
    negativePart (selKConj ℓ hk) →+ selmerTwoPower (Etw ℓ k) :=
  ((AddMonoidHom.snd _ _).comp (quadraticDescent ℓ hk)).comp (negativePart (selKConj ℓ hk)).subtype

theorem positiveDescent_apply (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ))
    (x : positivePart (selKConj ℓ hk)) :
    positiveDescent ℓ hk x = (quadraticDescent ℓ hk (x : SelK ℓ k)).1 :=
  rfl

theorem negativeDescent_apply (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ))
    (x : negativePart (selKConj ℓ hk)) :
    negativeDescent ℓ hk x = (quadraticDescent ℓ hk (x : SelK ℓ k)).2 :=
  rfl

theorem positiveDescent_ker (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ))
    (x : positivePart (selKConj ℓ hk)) (hx : positiveDescent ℓ hk x = 0) : 2 • x = 0 := by
  rw [positiveDescent_apply] at hx
  have hxτ : selKConj ℓ hk (x : SelK ℓ k) = x := (mem_positivePart_iff _ _).mp x.2
  apply Subtype.ext
  rw [AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero]
  exact quadraticDescent_fst_two_nsmul ℓ hk x hxτ hx

theorem positiveDescent_coker (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ))
    (y : selmerTwoPower (Ecurve ℓ)) : ∃ x, positiveDescent ℓ hk x = 2 • y := by
  obtain ⟨x, hxτ, hxy⟩ := quadraticDescent_exists_fst ℓ hk y
  have hmem : x ∈ positivePart (selKConj ℓ hk) := (mem_positivePart_iff _ _).mpr hxτ
  exact ⟨⟨x, hmem⟩, (positiveDescent_apply ℓ hk ⟨x, hmem⟩).trans hxy⟩

/-- **The invariant part of `Sel_{2^∞}(E_ℓ/K)` is `Sel_{2^∞}(E_ℓ/ℚ)` up to defects killed by
`2`.** -/
theorem positiveDescent_boundedDefects (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) :
    BoundedDefects (positiveDescent ℓ hk) :=
  ⟨2, 2, two_ne_zero, two_ne_zero, positiveDescent_ker ℓ hk, positiveDescent_coker ℓ hk⟩

theorem negativeDescent_ker (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ))
    (x : negativePart (selKConj ℓ hk)) (hx : negativeDescent ℓ hk x = 0) : 2 • x = 0 := by
  rw [negativeDescent_apply] at hx
  have hxτ : selKConj ℓ hk (x : SelK ℓ k) = -x := (mem_negativePart_iff _ _).mp x.2
  apply Subtype.ext
  rw [AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero]
  exact quadraticDescent_snd_two_nsmul ℓ hk x hxτ hx

theorem negativeDescent_coker (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ))
    (y : selmerTwoPower (Etw ℓ k)) : ∃ x, negativeDescent ℓ hk x = 2 • y := by
  obtain ⟨x, hxτ, hxy⟩ := quadraticDescent_exists_snd ℓ hk y
  have hmem : x ∈ negativePart (selKConj ℓ hk) := (mem_negativePart_iff _ _).mpr hxτ
  exact ⟨⟨x, hmem⟩, (negativeDescent_apply ℓ hk ⟨x, hmem⟩).trans hxy⟩

/-- **The anti-invariant part of `Sel_{2^∞}(E_ℓ/K)` is `Sel_{2^∞}(E_ℓ^{(k)}/ℚ)` up to defects
killed by `2`.** -/
theorem negativeDescent_boundedDefects (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) :
    BoundedDefects (negativeDescent ℓ hk) :=
  ⟨2, 2, two_ne_zero, two_ne_zero, negativeDescent_ker ℓ hk, negativeDescent_coker ℓ hk⟩

/-- **The eigenspace route**: `V₂ Sel_{2^∞}(E_ℓ/K) ≅ V₂ Sel_{2^∞}(E_ℓ/ℚ) × V₂ Sel_{2^∞}(E_ℓ^{(k)}/ℚ)`
through the `Gal(K/ℚ)`-eigenspaces. -/
def ratTateSelKEigenspaceProductEquiv (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) :
    RatTate (SelK ℓ k) ≃ₗ[ℚ_[2]]
      RatTate (selmerTwoPower (Ecurve ℓ)) × RatTate (selmerTwoPower (Etw ℓ k)) :=
  (ratTateSelKEigenspaceEquiv ℓ hk).trans
    (LinearEquiv.prodCongr
      (ratTateEquivOfBoundedDefects _ (positiveDescent_boundedDefects ℓ hk))
      (ratTateEquivOfBoundedDefects _ (negativeDescent_boundedDefects ℓ hk)))

/-- **The central comparison with the genuine quadratic Selmer group and descent map.**
Only the rational Kummer comparison and the universal-coefficient map remain as inputs. -/
def centralSelmerComparisonOfQuadraticDescent {ℓ : ℕ} {k : ℤ} (hk : ¬ IsSquare (k : ℚ))
    {m r : ℕ} (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT)
    (CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
    (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (hzero : CU.d 0 1 = 0) (hd : ∀ x, e2 ((CU.d 1 2).hom x) = Dm *ᵥ e1 x)
    (K : CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ)
    (i : K ⟶ scalarChangedComplex Rings.rhoT CU) [QuasiIsoAt i 1]
    (eK : K.homology 1 ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]))
    (j : (Fin r → Q2Z2) →+ SelK ℓ k) (hj : BoundedDefects j) :
    CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ k)) Dm :=
  centralSelmerComparisonOfSpecializedModel Dm CU e1 e2 hzero hd K i eK j hj
    (descentToProduct ℓ hk) (descentToProduct_boundedDefects ℓ hk)

/-- **The base-zero `hcentral` field from the genuine quadratic descent**, given the rational
Kummer comparison and the universal-coefficient map. -/
theorem hcentral_of_quadraticDescent {ℓ : ℕ} {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) {m r : ℕ}
    (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT)
    (CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
    (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (hzero : CU.d 0 1 = 0) (hd : ∀ x, e2 ((CU.d 1 2).hom x) = Dm *ᵥ e1 x)
    (K : CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ)
    (i : K ⟶ scalarChangedComplex Rings.rhoT CU) [QuasiIsoAt i 1]
    (eK : K.homology 1 ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]))
    (j : (Fin r → Q2Z2) →+ SelK ℓ k) (hj : BoundedDefects j)
    (hSel : SelmerCorankOneOverK ℓ k) : (Dm.map Rings.rhoT).rank = m :=
  hcentral_of_selmer hSel
    (centralSelmerComparisonOfQuadraticDescent hk Dm CU e1 e2 hzero hd K i eK j hj)

end ZInQ.Manuscript.RC53Assist.QuadraticDescent

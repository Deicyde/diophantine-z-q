import ZInQKernel.Contrib.OneProof.CarayolHerbrand
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Parity
import ZInQKernel.Contrib.TauCeti.NumberTheory.Cyclotomic.CyclotomicCharacter

noncomputable section

namespace CarayolDDT

open PkgI4 LadicCond

/-! ## Cyclotomic characters of `G_ℚ` -/

theorem natCard_rootsOfUnity_Qbar (N : ℕ) [NeZero N] : Nat.card (rootsOfUnity N Qbar) = N := by
  have : NeZero (N : ℚ) := ⟨Nat.cast_ne_zero.2 (NeZero.ne N)⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity Qbar N

/-- The mod-`N` cyclotomic character of `G_ℚ`. -/
def cycN (N : ℕ) [NeZero N] : GQ →* (ZMod N)ˣ :=
  (modularCyclotomicCharacter Qbar (natCard_rootsOfUnity_Qbar N)).comp
    (MulSemiringAction.toRingAut GQ Qbar)

/-- The `ℓ`-adic cyclotomic character of `G_ℚ`. -/
def cycL (ℓ : ℕ) [Fact ℓ.Prime] : GQ →* ℤ_[ℓ]ˣ :=
  (cyclotomicCharacter Qbar ℓ).comp (MulSemiringAction.toRingAut GQ Qbar)

/-! ## Complex conjugation -/

/-- Some `c ∈ G_ℚ` is an involution inverting every root of unity (complex conjugation). -/
theorem exists_complexConj :
    ∃ c : GQ, c * c = 1 ∧ ∀ (n : ℕ) (t : Qbar), t ^ n = 1 → n ≠ 0 → c t * t = 1 := by
  let ιC : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let φ : Qbar →ₐ[ℚ] ℂ := (Complex.conjAe.toAlgHom.restrictScalars ℚ).comp ιC
  have hrange : ∀ x : Qbar, φ x ∈ ιC.fieldRange := fun x =>
    DSCoeffExt.mem_fieldRange_of_isIntegral ιC
      ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map φ)
  choose g hg using hrange
  have hgι : ∀ x, ιC (g x) = φ x := hg
  have hφφ : ∀ z : ℂ, Complex.conjAe (Complex.conjAe z) = z := fun z => by simp
  -- `g` is a ring hom
  have hinj := ιC.toRingHom.injective
  let g' : Qbar →ₐ[ℚ] Qbar :=
    { toFun := g
      map_one' := hinj (by simp [hgι, φ])
      map_mul' := fun a b => hinj (by
        show ιC (g (a * b)) = ιC (g a * g b)
        rw [map_mul, hgι, hgι, hgι, map_mul])
      map_zero' := hinj (by simp [hgι, φ])
      map_add' := fun a b => hinj (by
        show ιC (g (a + b)) = ιC (g a + g b)
        rw [map_add, hgι, hgι, hgι, map_add])
      commutes' := fun q => hinj (by
        show ιC (g (algebraMap ℚ Qbar q)) = ιC (algebraMap ℚ Qbar q)
        rw [hgι, AlgHom.commutes, AlgHom.commutes]) }
  have hgg : ∀ x, g' (g' x) = x := fun x => hinj (by
    show ιC (g (g x)) = ιC x
    rw [hgι]
    simp only [φ, AlgHom.comp_apply, AlgHom.restrictScalars_apply]
    show Complex.conjAe.toAlgHom (ιC (g x)) = ιC x
    rw [hgι]
    simp [φ])
  let c : GQ := AlgEquiv.ofBijective g' ⟨fun a b h => by rw [← hgg a, ← hgg b, h],
    fun y => ⟨g' y, hgg y⟩⟩
  refine ⟨c, ?_, ?_⟩
  · ext x
    exact hgg x
  · intro n t ht hn
    apply hinj
    show ιC (g t * t) = ιC 1
    rw [map_mul, hgι, map_one]
    simp only [φ, AlgHom.comp_apply, AlgHom.restrictScalars_apply]
    have hz : (ιC t) ^ n = 1 := by rw [← map_pow, ht, map_one]
    have hnorm : ‖ιC t‖ = 1 := by
      have := congrArg (‖·‖) hz
      simp only [norm_pow, norm_one] at this
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this
    show (starRingEnd ℂ) (ιC t) * ιC t = 1
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    simp


/-- **`χ_ℓ(c) = -1`**: the `ℓ`-adic cyclotomic character of an automorphism inverting the roots of unity. -/
theorem cycL_eq_neg_one (ℓ : ℕ) [Fact ℓ.Prime] {c : GQ}
    (hc : ∀ (n : ℕ) (t : Qbar), t ^ n = 1 → n ≠ 0 → c t * t = 1) : cycL ℓ c = -1 := by
  have : NeZero (ℓ : ℚ) := ⟨Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero⟩
  exact TauCeti.cyclotomicCharacter_eq_neg_one ℓ fun n t ht =>
    hc _ t ht (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)

/-- The mod-`N` cyclotomic character of an automorphism inverting the roots of unity is `-1`. -/
theorem cycN_eq_neg_one (N : ℕ) [NeZero N] {c : GQ}
    (hc : ∀ (n : ℕ) (t : Qbar), t ^ n = 1 → n ≠ 0 → c t * t = 1) : cycN N c = -1 := by
  have key := modularCyclotomicCharacter.unique Qbar (natCard_rootsOfUnity_Qbar N)
    (MulSemiringAction.toRingAut GQ Qbar c) (c := (-1 : ZMod N)) (fun t ht => by
      have htN : (t : Qbar) ^ N = 1 := by
        have := (mem_rootsOfUnity N t).1 ht
        rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
      have h1 := hc N t htN (NeZero.ne N)
      have h2 : ((t ^ (-1 : ZMod N).val : Qbarˣ) : Qbar) * t = 1 := by
        rw [Units.val_pow_eq_pow_val, ← pow_succ]
        refine orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_pow_eq_one htN).trans ?_)
        rw [← ZMod.natCast_eq_zero_iff, Nat.cast_succ, ZMod.natCast_zmod_val, neg_add_cancel]
      have ht0 : (t : Qbar) ≠ 0 := t.ne_zero
      show c t = _
      exact mul_right_cancel₀ ht0 (h1.trans h2.symm))
  exact Units.ext (key.symm.trans (by simp))

/-! ## Parity of the nebentypus in weight 2 -/

open HeckeRing.GL2 in
theorem chi_neg_one_eq_one {N : ℕ} [NeZero N] (f : Newform N 2) : ((f.χ (-1) : ℂˣ) : ℂ) = 1 := by
  rw [TauCeti.char_neg_one_of_mem_cuspFormCharSpace f.mem_charSpace f.ne_zero]
  norm_num

/-! ## Absolute irreducibility implies irreducibility -/

theorem irreducible_of_absIrreducible {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    {ι : Type*} (M : ι → Matrix (Fin n) (Fin n) K)
    (h : ∀ W : Submodule L (Fin n → L),
      (∀ i, ∀ v ∈ W, ((M i).map (algebraMap K L)).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (W : Submodule K (Fin n → K)) (hW : ∀ i, ∀ v ∈ W, (M i).mulVec v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hb, ht⟩ := hcon
  let φ : (Fin n → K) → (Fin n → L) := fun v => algebraMap K L ∘ v
  let W' : Submodule L (Fin n → L) := Submodule.span L (φ '' W)
  have hmap : ∀ (A : Matrix (Fin n) (Fin n) K) (v : Fin n → K),
      (A.map (algebraMap K L)).mulVec (φ v) = φ (A.mulVec v) := by
    intro A v
    funext i
    simp only [φ, Function.comp_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
      map_mul]
  have hW' : ∀ i, ∀ v ∈ W', ((M i).map (algebraMap K L)).mulVec v ∈ W' := by
    intro i v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      rw [hmap]
      exact Submodule.subset_span ⟨_, hW i y hy, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact W'.add_mem hx hy
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact W'.smul_mem a hx
  rcases h W' hW' with h1 | h1
  · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    have : φ w ∈ W' := Submodule.subset_span ⟨w, hw, rfl⟩
    rw [h1, Submodule.mem_bot] at this
    apply hw0
    funext j
    have := congrFun this j
    simpa [φ] using this
  · obtain ⟨g, hg0, hle⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.2 ht)
    let r : Fin n → K := fun j => g (Pi.single j 1)
    have hgr : ∀ v, g v = ∑ j, v j * r j := by
      intro v
      conv_lhs => rw [show v = ∑ j, v j • Pi.single j (1 : K) by
        funext a; simp [Finset.sum_apply, Pi.single_apply]]
      simp [map_sum, r]
    obtain ⟨j0, hj0⟩ : ∃ j, r j ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hg0
      ext v
      simp [hgr, hc]
    let G : (Fin n → L) →ₗ[L] L :=
      { toFun := fun v => ∑ j, v j * algebraMap K L (r j)
        map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun a b => by simp [mul_assoc, Finset.mul_sum] }
    have hWG : W' ≤ LinearMap.ker G := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      have hy0 : g y = 0 := hle hy
      rw [hgr] at hy0
      show ∑ j, algebraMap K L (y j) * algebraMap K L (r j) = 0
      simp_rw [← map_mul, ← map_sum, hy0, map_zero]
    have : (Pi.single j0 1 : Fin n → L) ∈ W' := h1 ▸ Submodule.mem_top
    have h0 := hWG this
    rw [LinearMap.mem_ker] at h0
    simp only [G, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h0
    exact hj0 ((map_eq_zero_iff _ (algebraMap K L).injective).1 h0)

/-! ## Continuous ring homs out of `ℤ_ℓ` are unique -/

theorem padicInt_ringHom_ext {ℓ : ℕ} [Fact ℓ.Prime] {R : Type*} [Ring R] [TopologicalSpace R]
    [T2Space R] {ι ι' : ℤ_[ℓ] →+* R} (h : Continuous ι) (h' : Continuous ι') : ι = ι' := by
  have := (PadicInt.denseRange_intCast (p := ℓ)).equalizer h h' (funext fun z => by simp)
  exact RingHom.ext (congrFun this)

end CarayolDDT

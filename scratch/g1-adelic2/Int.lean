import ZInQKernel.Contrib.G1Adelic.FiniteAdele

/-!
# G1-adelic over Mathlib's `𝔸ᶠ[ℤ, ℚ]`: `ℤ̂`, `ℤ̂^×`, `𝒪̂ = 𝒪 ⊗ ℤ̂` and `N/𝔸ᶠ^×K₀`
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GlueVigneras
open scoped RestrictedProduct Quaternion TensorProduct

namespace G1Adelic.FA

/-- `ℤ̂` is the image of Mathlib's structure map `∏_v ℤ_v → 𝔸ᶠ[ℤ, ℚ]`. -/
theorem ZhatAF_eq_range_structureMap :
    ZhatAF = Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum ℤ =>
      v.adicCompletion ℚ) (fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
      Filter.cofinite) := by
  rw [RestrictedProduct.range_structureMap]
  rfl

/-- `ℤ̂` as a subring of `𝔸ᶠ[ℤ, ℚ]`. -/
noncomputable def ZhatSubAF : Subring AF where
  carrier := ZhatAF
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem _
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem _
  neg_mem' ha v := neg_mem (ha v)

theorem qcoord_algebraMap {R : Type*} [CommRing R] (a : R) :
    qcoord (algebraMap R ℍ[R, 2, 0, -3] a) = ![a, 0, 0, 0] := by
  funext k; fin_cases k <;> simp [qcoord, QuaternionAlgebra.algebraMap_eq]

theorem algebraMap_mem_OhatAF_iff (a : AF) : algebraMap AF HA a ∈ OhatAF ↔ a ∈ ZhatAF := by
  simp only [OhatAF, Set.mem_ofPred_eq, qcoord_algebraMap]
  constructor
  · intro h; simpa using h 0
  · intro h k
    fin_cases k
    · simpa using h
    all_goals exact ZhatSubAF.zero_mem

/-- `ℤ̂^×`, as central scalars of `(B ⊗ 𝔸ᶠ)^×`. -/
noncomputable def ZintAF : Subgroup HAˣ :=
  ZhatSubAF.toSubmonoid.units.map (Units.map (algebraMap AF HA : AF →* HA))

/-- **`𝔸ᶠ^× ∩ K₀ = ℤ̂^×`** over Mathlib's finite adeles. -/
theorem ZAF_inf_K0AF : ZAF ⊓ K0AF = ZintAF := by
  ext x
  simp only [Subgroup.mem_inf, ZAF, ZintAF, MonoidHom.mem_range, Subgroup.mem_map, K0AF,
    Submonoid.mem_units_iff]
  constructor
  · rintro ⟨⟨a, rfl⟩, h1, h2⟩
    refine ⟨a, ⟨?_, ?_⟩, rfl⟩
    · exact (algebraMap_mem_OhatAF_iff _).mp h1
    · rw [← map_inv] at h2
      exact (algebraMap_mem_OhatAF_iff _).mp h2
  · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨a, rfl⟩, (algebraMap_mem_OhatAF_iff _).mpr h1, ?_⟩
    rw [← map_inv]
    exact (algebraMap_mem_OhatAF_iff _).mpr h2

/-- **A3's count with `ℤ̂^×` named, over Mathlib's `𝔸ᶠ[ℤ, ℚ]`:**
`|Γ'| = [N : 𝔸ᶠ^× K₃] = [N : 𝔸ᶠ^× K₀] · [K₀ : ℤ̂^× K₃] = 4 · 36 = 144`. -/
theorem gamma_count_Zint_AF :
    (ZAF ⊔ K3AF).relIndex NAF = (ZAF ⊔ K0AF).relIndex NAF * (ZintAF ⊔ K3AF).relIndex K0AF ∧
      (ZAF ⊔ K0AF).relIndex NAF = 4 ∧ (ZintAF ⊔ K3AF).relIndex K0AF = 36 := by
  rw [← ZAF_inf_K0AF, gamma_order_AF, relIndex_eq_four_AF, relIndex_K3_AF]
  exact ⟨rfl, rfl, rfl⟩

/-! ### `𝒪̂` is the `ℤ̂`-span of the basis of `𝒪` -/

/-- N5's `ℤ`-basis `1, i, (1 + j)/2, (i + ij)/2` of the maximal order `𝒪 ⊆ B = ℍ[ℚ, 2, 0, -3]`. -/
noncomputable def eQ : Fin 4 → ℍ[ℚ, 2, 0, -3] :=
  ![1, ⟨0, 1, 0, 0⟩, ⟨1 / 2, 0, 1 / 2, 0⟩, ⟨0, 1 / 2, 0, 1 / 2⟩]

/-- The basis of `𝒪` in `B ⊗ 𝔸ᶠ`. -/
noncomputable def eAF (k : Fin 4) : HA := qmap (algebraMap ℚ AF) (eQ k)

theorem half_mul_two : algebraMap ℚ AF 2⁻¹ * 2 = 1 := by
  rw [← map_ofNat (algebraMap ℚ AF) 2, ← map_mul]; norm_num

theorem sum_qcoord (x : HA) : ∑ k, qcoord x k • eAF k = x := by
  have h := half_mul_two
  simp only [Fin.sum_univ_four, eAF, eQ, qcoord]
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp <;>
    first | linear_combination x.imJ * h | linear_combination x.imK * h

theorem qcoord_sum (a : Fin 4 → AF) : qcoord (∑ k, a k • eAF k) = a := by
  have h := half_mul_two
  funext k
  simp only [Fin.sum_univ_four, eAF, eQ]
  fin_cases k <;> simp [qcoord] <;>
    first | linear_combination a 2 * h | linear_combination a 3 * h

/-- **`𝒪̂ = 𝒪 ⊗ ℤ̂`**: `OhatAF` is the set of `ℤ̂`-combinations of N5's basis of `𝒪`. -/
theorem OhatAF_eq_span :
    OhatAF = {x | ∃ a : Fin 4 → AF, (∀ k, a k ∈ ZhatAF) ∧ x = ∑ k, a k • eAF k} := by
  ext x
  constructor
  · intro hx
    exact ⟨qcoord x, hx, (sum_qcoord x).symm⟩
  · rintro ⟨a, ha, rfl⟩ k
    rw [qcoord_sum]; exact ha k

/-! ### `N/(𝔸ᶠ^× K₀)` over Mathlib's finite adeles -/

theorem mem_sup_AF (y : BAˣ) : ThetaU y ∈ ZAF ⊔ K0AF ↔ y ∈ Zhat ⊔ K0 := by
  rw [← map_Zhat, ← map_K0, ← Subgroup.map_sup, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

/-- `Theta` on the normalizers: `N(𝒪̂) ⊆ B̂^×` and `N(𝒪̂) ⊆ (B ⊗ 𝔸ᶠ)^×`. -/
noncomputable def ThetaN : Nhat ≃* NAF :=
  (ThetaU.subgroupMap Nhat).trans (MulEquiv.subgroupCongr map_Nhat)

theorem ThetaN_val (y : Nhat) : ((ThetaN y : NAF) : HAˣ) = ThetaU y := rfl

theorem map_sup_subgroupOf :
    ((Zhat ⊔ K0).subgroupOf Nhat).map (ThetaN : Nhat →* NAF) = (ZAF ⊔ K0AF).subgroupOf NAF := by
  ext x
  obtain ⟨y, rfl⟩ := ThetaN.surjective x
  refine (Subgroup.mem_map_iff_mem (f := (ThetaN : Nhat →* NAF)) ThetaN.injective).trans ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, ThetaN_val, mem_sup_AF]

instance sup_subgroupOf_normal_AF : ((ZAF ⊔ K0AF).subgroupOf NAF).Normal :=
  map_sup_subgroupOf ▸ (sup_subgroupOf_normal.map _ ThetaN.surjective)

/-- **`N/(𝔸ᶠ^× K₀) ≃ B_2^×/ℚ_2^×𝒪_2^× × B_3^×/ℚ_3^×𝒪_3^×`** over `ℍ[𝔸ᶠ[ℤ, ℚ], 2, 0, -3]`. -/
noncomputable def quotEquivAF : NAF ⧸ (ZAF ⊔ K0AF).subgroupOf NAF ≃*
    ((Bp 2)ˣ ⧸ Hloc P2 hP2) × ((Bp 3)ˣ ⧸ Hloc P3 hP3) :=
  (QuotientGroup.congr _ _ ThetaN map_sup_subgroupOf).symm.trans quotEquiv

end G1Adelic.FA

/-! ### `B ⊗_ℚ 𝔸ᶠ = ℍ[𝔸ᶠ, 2, 0, -3]` -/

namespace G1Adelic.FA

section BaseChange

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- `ℍ[ℚ, 2, 0, -3] →ₐ[ℚ] ℍ[A, 2, 0, -3]`, coordinatewise. -/
noncomputable def qmapAlg : ℍ[ℚ, 2, 0, -3] →ₐ[ℚ] ℍ[A, 2, 0, -3] :=
  { qmap (algebraMap ℚ A) with
    commutes' := fun r => by
      show qmap (algebraMap ℚ A) (algebraMap ℚ _ r) = ((algebraMap ℚ A r : A) : ℍ[A, 2, 0, -3])
      ext <;> simp [QuaternionAlgebra.algebraMap_eq] }

/-- The base change map `A ⊗[ℚ] ℍ[ℚ, 2, 0, -3] →ₐ[A] ℍ[A, 2, 0, -3]`, `a ⊗ q ↦ a • q`. -/
noncomputable def bcHom : A ⊗[ℚ] ℍ[ℚ, 2, 0, -3] →ₐ[A] ℍ[A, 2, 0, -3] :=
  AlgHom.liftEquiv ℚ A _ _ (qmapAlg A)

theorem bcHom_tmul (a : A) (q : ℍ[ℚ, 2, 0, -3]) : bcHom A (a ⊗ₜ q) = a • qmap (algebraMap ℚ A) q :=
  rfl

theorem bcHom_basis (i : Fin 4) :
    bcHom A (Algebra.TensorProduct.basis A (QuaternionAlgebra.basisOneIJK (2 : ℚ) 0 (-3)) i) =
      QuaternionAlgebra.basisOneIJK (2 : A) 0 (-3) i := by
  rw [Algebra.TensorProduct.basis_apply, bcHom_tmul, one_smul]
  fin_cases i <;> ext <;> simp [QuaternionAlgebra.basisOneIJK]

theorem bcHom_bijective : Function.Bijective (bcHom A) := by
  let Bt := Algebra.TensorProduct.basis A (QuaternionAlgebra.basisOneIJK (2 : ℚ) 0 (-3))
  let e := Bt.equiv (QuaternionAlgebra.basisOneIJK (2 : A) 0 (-3)) (Equiv.refl _)
  have h : (bcHom A).toLinearMap = e.toLinearMap :=
    Bt.ext fun i => by
      rw [AlgHom.toLinearMap_apply, bcHom_basis, LinearEquiv.coe_coe, Module.Basis.equiv_apply]; rfl
  have h' : ⇑(bcHom A) = ⇑e := congrArg DFunLike.coe h
  rw [h']
  exact e.bijective

/-- **Base change** `A ⊗[ℚ] ℍ[ℚ, 2, 0, -3] ≃ₐ[A] ℍ[A, 2, 0, -3]`. -/
noncomputable def baseChange : A ⊗[ℚ] ℍ[ℚ, 2, 0, -3] ≃ₐ[A] ℍ[A, 2, 0, -3] :=
  AlgEquiv.ofBijective (bcHom A) (bcHom_bijective A)

end BaseChange

/-- **`B ⊗_ℚ 𝔸ᶠ ≃ B̂`**: Mathlib's `𝔸ᶠ[ℤ, ℚ] ⊗[ℚ] ℍ[ℚ, 2, 0, -3]` is isomorphic to t30-adelic's
restricted product `B̂ = Πʳ_p [B_p, 𝒪_p]`. -/
noncomputable def tensorEquivBA : AF ⊗[ℚ] ℍ[ℚ, 2, 0, -3] ≃+* BA :=
  (baseChange AF).toRingEquiv.trans Theta.symm

end G1Adelic.FA

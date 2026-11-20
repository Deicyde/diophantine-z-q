import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Chebotarev
import ZInQKernel.Contrib.TauCeti.NumberTheory.RamificationInertia.Unramified

/-! The two finite Galois cuts and the character cut are combined inside
`ℚ̄`. Chebotarev acts on this compositum (tex 9919–9921). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine NumberField PrintsArith Symbols
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open ZInQ.Contrib.ChebFD.C10 (toZbar frobLift)

abbrev jointCut (K₁ K₂ Kχ : IntermediateField ℚ Qbar) := K₁ ⊔ K₂ ⊔ Kχ

/-- The kernel of the joint quotient is the intersection of the three kernels. -/
theorem fixingSubgroup_jointCut (K₁ K₂ Kχ : IntermediateField ℚ Qbar) :
    (jointCut K₁ K₂ Kχ).fixingSubgroup =
      K₁.fixingSubgroup ⊓ K₂.fixingSubgroup ⊓ Kχ.fixingSubgroup := by
  rw [jointCut, IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_sup]

/-- Restriction presents the Galois group of the compositum as a quotient
of the absolute Galois group. -/
theorem joint_restriction_surjective (K₁ K₂ Kχ : IntermediateField ℚ Qbar)
    [IsGalois ℚ K₁] [IsGalois ℚ K₂] [IsGalois ℚ Kχ] :
    Function.Surjective (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar)
      (jointCut K₁ K₂ Kχ)) :=
  AlgEquiv.restrictNormalHom_surjective _

/-- Inertia at an absolute prime over an unramified rational prime fixes the
finite Galois field. The unramifiedness witness can be at any prime above it. -/
private theorem inertia_fixes_cut (K : IntermediateField ℚ Qbar)
    [FiniteDimensional ℚ K] [IsGalois ℚ K] {q : ℕ} (hq : q.Prime)
    (P : Ideal (𝓞 K)) [P.IsPrime] (hp : P.under ℤ = Ideal.span {(q : ℤ)})
    [Algebra.IsUnramifiedAt ℤ P] {Q : Ideal Zbar} (hQ : Q.IsMaximal)
    (hqQ : ((q : ℤ) : Zbar) ∈ Q) {n : GalQ} (hn : n ∈ Q.inertia GalQ) :
    n ∈ K.fixingSubgroup := by
  let : NumberField K := ⟨⟩
  let : IsGaloisGroup (K ≃ₐ[ℚ] K) ℤ (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (K ≃ₐ[ℚ] K) ℤ (𝓞 K) ℚ K
  let R := Q.comap (toZbar K)
  have hR : R.under ℤ = Ideal.span {(q : ℤ)} := by
    change Ideal.comap ((toZbar K).comp (algebraMap ℤ (𝓞 K))) Q = _
    rw [show (toZbar K).comp (algebraMap ℤ (𝓞 K)) = algebraMap ℤ Zbar by
      ext z
      simp, ← Ideal.under, under_eq_span_of_isMaximal hQ hq hqQ]
  have : Fact q.Prime := ⟨hq⟩
  let : P.LiesOver (Ideal.span {(q : ℤ)}) := ⟨hp.symm⟩
  let : Q.IsPrime := hQ.isPrime
  let : R.IsPrime := Ideal.IsPrime.comap _
  let : R.LiesOver (Ideal.span {(q : ℤ)}) := ⟨hR.symm⟩
  let : (Ideal.span {(q : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime q
  let : R.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal R (Ideal.span {(q : ℤ)})
  have hur := Ideal.isUnramifiedAt_of_isUnramifiedAt_of_isGaloisGroup
    (Ideal.span {(q : ℤ)}) P R (K ≃ₐ[ℚ] K)
  have hbot := (Ideal.isUnramifiedAt_iff_inertia_eq_bot_of_isMaximal
    (R := ℤ) (G := K ≃ₐ[ℚ] K) R).mp hur
  let res := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) K
  have hm : res n ∈ R.inertia (K ≃ₐ[ℚ] K) := by
    apply Ideal.mem_inertia.mpr
    intro a
    change toZbar K (res n • a - a) ∈ Q
    rw [map_sub]
    convert Ideal.mem_inertia.mp hn (toZbar K a) using 1
    congr 1
    apply Subtype.ext
    exact AlgEquiv.restrictNormal_commutes n K (a : K)
  rw [hbot, Subgroup.mem_bot] at hm
  rw [← K.restrictNormalHom_ker]
  exact hm

/-- Chebotarev in the compositum: at each selected prime the specified
element is an actual Frobenius in the compositum, and every absolute
Frobenius at that prime restricts to its conjugacy class there. Index the targets by `Fin 4` for the four
deletion representatives. -/
theorem joint_frobenius {ι : Type*} (K₁ K₂ Kχ : IntermediateField ℚ Qbar)
    [FiniteDimensional ℚ K₁] [FiniteDimensional ℚ K₂] [FiniteDimensional ℚ Kχ]
    [IsGalois ℚ K₁] [IsGalois ℚ K₂] [IsGalois ℚ Kχ]
    (avoid : Finset ℕ) (g : ι → GalQ) :
    ∃ q : ι → ℕ, ∀ j,
      (q j).Prime ∧ q j ∉ avoid ∧
      ∃ P : Ideal (𝓞 (jointCut K₁ K₂ Kχ)), ∃ _ : P.IsPrime,
        P.under ℤ = Ideal.span {(q j : ℤ)} ∧ Algebra.IsUnramifiedAt ℤ P ∧
        IsArithFrobAt ℤ (AlgEquiv.restrictNormal (g j) (jointCut K₁ K₂ Kχ)) P ∧
        ∀ σ, IsFrobAt σ (q j) → ∃ h n, n ∈ (jointCut K₁ K₂ Kχ).fixingSubgroup ∧
          σ = h * g j * h⁻¹ * n := by
  let K := jointCut K₁ K₂ Kχ
  have : FiniteDimensional ℚ K := by
    change FiniteDimensional ℚ (↑(K₁ ⊔ K₂ ⊔ Kχ) : Type)
    infer_instance
  have : Normal ℚ K := by
    change Normal ℚ (↑(K₁ ⊔ K₂ ⊔ Kχ) : Type)
    infer_instance
  have : IsGalois ℚ K := ⟨⟩
  have : NumberField K := ⟨⟩
  have single (j : ι) := ZInQ.Contrib.chebotarevExists K avoid
    (AlgEquiv.restrictNormal (g j) K)
  choose q hq using single
  refine ⟨q, fun j => ?_⟩
  obtain ⟨hp, ha, P, hP, hPq, hu, hf⟩ := hq j
  have := hP
  have := hu
  obtain ⟨f, hF, hres⟩ := frobLift K _ (q j) P hp hPq hu hf
  refine ⟨hp, ha, P, hP, hPq, hu, hf, fun σ hσ => ?_⟩
  obtain ⟨h, Q, hQ, hqQ, hn⟩ := IsFrobAt.exists_mul_inv_mem_inertia hp hσ
    ((isFrobAt_iff_c10 hp).mpr hF)
  let res := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) K
  have e : f⁻¹ * g j ∈ K.fixingSubgroup := by
    rw [← K.restrictNormalHom_ker]
    change res (f⁻¹ * g j) = 1
    rw [map_mul, map_inv, show res f = res (g j) from hres, inv_mul_cancel]
  have hleft := inertia_fixes_cut K hp P hPq hQ hqQ hn
  have hnorm : K.fixingSubgroup.Normal :=
    (InfiniteGalois.normal_iff_isGalois K).mpr inferInstance
  let a := σ * (h * f * h⁻¹)⁻¹
  refine ⟨a * h, a * (h * (f⁻¹ * g j)⁻¹ * h⁻¹),
    K.fixingSubgroup.mul_mem hleft (hnorm.conj_mem _ (K.fixingSubgroup.inv_mem e) h), ?_⟩
  dsimp [a]
  group

end ZInQ.Manuscript.RC.EvenJoin

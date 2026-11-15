import ZInQKernel.Contrib.SmoothFibre.Statement
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Localization.FractionRing

/-!
# smooth-fibre: `SmoothFibreReduced`, proved from Mathlib

* `isReduced_of_etale_of_isDomain`: an étale algebra over a domain `P` is reduced
  (it embeds, by flatness, into its base change to `Frac P`, which is étale over a field, hence
  reduced by `Algebra.FormallyUnramified.isReduced_of_field`).
* `isReduced_of_smooth_of_field`: a smooth algebra over a field is reduced (locally it is étale
  over a polynomial ring, `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`).
* `smoothFibreReduced : SmoothFibreReduced`: for `φ : R → A` smooth and `m` maximal, `m A` is
  radical (`A/mA ≃ A ⊗_R R/m` is smooth over the field `R/m`).
-/

namespace ZInQ.SmoothFibre

open TensorProduct

/-- An étale algebra over a domain is reduced. -/
theorem isReduced_of_etale_of_isDomain (P S : Type*) [CommRing P] [IsDomain P] [CommRing S]
    [Algebra P S] [Algebra.Etale P S] : IsReduced S := by
  let K := FractionRing P
  let f := Algebra.TensorProduct.includeRight (R := P) (A := K) (B := S)
  have hinj : Function.Injective f := by
    have : ⇑f = (LinearMap.rTensor S (Algebra.ofId P K).toLinearMap).comp
        (Algebra.TensorProduct.lid P S).symm.toLinearMap := by
      ext x; simp [f]
    rw [this]
    exact (Module.Flat.rTensor_preserves_injective_linearMap _
      (IsFractionRing.injective P K)).comp (Algebra.TensorProduct.lid P S).symm.injective
  have : IsReduced (K ⊗[P] S) := Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[P] S)
  exact isReduced_of_injective (f : S →+* K ⊗[P] S) hinj

/-- A smooth algebra over a field is reduced. -/
theorem isReduced_of_smooth_of_field (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] : IsReduced A := by
  refine ⟨fun x hx => ?_⟩
  by_contra hne
  let I : Ideal A := (Ideal.span {x} : Submodule A A).annihilator
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ I := h ▸ Submodule.mem_top
    rw [Submodule.mem_annihilator_span_singleton, one_smul] at h1
    exact hne h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hI
  have := hm.isPrime
  have : Algebra.IsSmoothAt k m := inferInstance
  obtain ⟨f, hf, n, inst, -, hst⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := m)
  have : IsReduced (Localization.Away f) :=
    isReduced_of_etale_of_isDomain (MvPolynomial (Fin n) k) _
  have h0 : algebraMap A (Localization.Away f) x = 0 := (hx.map _).eq_zero
  obtain ⟨⟨_, k', rfl⟩, hk⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f) x).1 h0
  apply hf
  apply hm.isPrime.mem_of_pow_mem k'
  apply hle
  rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  exact hk

/-- **`SmoothFibreReduced`, proved.** For a smooth ring map `φ : R → A` and a maximal ideal
`m ⊂ R`, the ideal `m A` is radical. -/
theorem smoothFibreReduced : SmoothFibreReduced := by
  intro R A _ _ φ hφ m hm
  let := φ.toAlgebra
  have : Algebra.Smooth R A := RingHom.smooth_algebraMap.1 hφ
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  have h1 : IsReduced ((R ⧸ m) ⊗[R] A) := isReduced_of_smooth_of_field (R ⧸ m) _
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot A m
  let e' := e.toRingEquiv.trans (Algebra.TensorProduct.comm R A (R ⧸ m)).toRingEquiv
  have h2 : IsReduced (A ⧸ m.map (algebraMap R A)) :=
    isReduced_of_injective (e' : A ⧸ m.map (algebraMap R A) →+* (R ⧸ m) ⊗[R] A) e'.injective
  exact (Ideal.isRadical_iff_quotient_reduced _).2 h2

end ZInQ.SmoothFibre

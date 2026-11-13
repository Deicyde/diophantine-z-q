import Mathlib

/-! # ts-hecke: ramification index × geometric fibre = degree (development file, Mathlib only)

For a finite Galois extension `E/F`, `F = Frac A` with `A` a principal ideal domain, `B` the
integral closure of `A` in `E`, `φ : A → Ω` (`Ω` algebraically closed of characteristic 0) with
nonzero kernel `P`, and a prime `Q` of `B` over `P`:
`e(Q) · #{ψ : B → Ω | ψ ∘ (A → B) = φ} = [E : F]`. -/

open Polynomial

namespace RamCount

variable {A F E Ω : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
  [Field F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra F E] [Algebra A E] [IsScalarTower A F E] [FiniteDimensional F E]
  [IsGalois F E] [CharZero F] [Field Ω] [IsAlgClosed Ω] [CharZero Ω]

/-- The fibre of `ψ ↦ ker ψ` over a prime `q` is the set of `A ⧸ P`-embeddings of `B ⧸ q`. -/
noncomputable def fiberEquiv {B : Type} [CommRing B] [Algebra A B] (φ : A →+* Ω)
    (q : (RingHom.ker φ).primesOver B) [q.1.IsMaximal]
    (f : {ψ : B →+* Ω // ψ.comp (algebraMap A B) = φ} → (RingHom.ker φ).primesOver B)
    (hf : ∀ ψ, (f ψ).1 = RingHom.ker ψ.1) :
    letI : Algebra (A ⧸ RingHom.ker φ) Ω :=
      (Ideal.Quotient.lift (RingHom.ker φ) φ (fun _ ha => RingHom.mem_ker.1 ha)).toAlgebra
    {ψ // f ψ = q} ≃ (B ⧸ q.1 →ₐ[A ⧸ RingHom.ker φ] Ω) :=
  letI : Algebra (A ⧸ RingHom.ker φ) Ω :=
    (Ideal.Quotient.lift (RingHom.ker φ) φ (fun _ ha => RingHom.mem_ker.1 ha)).toAlgebra
  letI : Field (B ⧸ q.1) := Ideal.Quotient.field q.1
  { toFun := fun ψ =>
      { toRingHom := Ideal.Quotient.lift q.1 ψ.1.1 (fun x hx => by
          have h : RingHom.ker ψ.1.1 = q.1 := (hf ψ.1).symm.trans (congrArg Subtype.val ψ.2)
          rw [← h] at hx; exact hx)
        commutes' := by
          intro r
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
          change ψ.1.1 (algebraMap A B a) = φ a
          exact congrArg (fun g : A →+* Ω => g a) ψ.1.2 }
    invFun := fun χ => ⟨⟨χ.toRingHom.comp (Ideal.Quotient.mk q.1), RingHom.ext fun a => by
        change χ (Ideal.Quotient.mk q.1 (algebraMap A B a)) = φ a
        exact χ.commutes (Ideal.Quotient.mk _ a)⟩, by
        apply Subtype.ext
        rw [hf]
        ext x
        simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
        rw [show (χ.toRingHom (Ideal.Quotient.mk q.1 x) = 0) ↔ Ideal.Quotient.mk q.1 x = 0 from
          map_eq_zero_iff χ.toRingHom χ.toRingHom.injective, Ideal.Quotient.eq_zero_iff_mem]⟩
    left_inv := fun ψ => by
      apply Subtype.ext; apply Subtype.ext
      ext x
      rfl
    right_inv := fun χ => by
      ext x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl }

theorem ramCount (φ : A →+* Ω) (hφ : RingHom.ker φ ≠ ⊥)
    (Q : Ideal (integralClosure A E)) [hQ : Q.IsPrime] (hQP : Q.under A = RingHom.ker φ) :
    Q.ramificationIdx A *
      {ψ : integralClosure A E →+* Ω | ψ.comp (algebraMap A (integralClosure A E)) = φ}.ncard =
      Module.finrank F E := by
  classical
  set P := RingHom.ker φ with hPdef
  haveI hPprime : P.IsPrime := RingHom.ker_isPrime φ
  haveI hPmax : P.IsMaximal := hPprime.isMaximal hφ
  haveI : Q.LiesOver P := ⟨hQP.symm⟩
  have hinjAE : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A F E]
    exact (algebraMap F E).injective.comp (IsFractionRing.injective A F)
  haveI : Module.IsTorsionFree A E := Module.isTorsionFree_iff_algebraMap_injective.2 hinjAE
  haveI : Module.Finite A (integralClosure A E) := IsIntegralClosure.finite A F E _
  haveI : Module.Free A (integralClosure A E) := IsIntegralClosure.module_free A F E _
  haveI : IsFractionRing (integralClosure A E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension A F E _
  have hrank : Module.finrank A (integralClosure A E) = Module.finrank F E :=
    IsIntegralClosure.rank A F E _
  haveI : SMulCommClass Gal(E/F) A E := ⟨fun g a x => by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply A F E, AlgEquiv.commutes]⟩
  haveI : IsGaloisGroup Gal(E/F) A (integralClosure A E) :=
    IsGaloisGroup.of_isFractionRing Gal(E/F) A (integralClosure A E) F E
  haveI : Fintype (P.primesOver (integralClosure A E)) :=
    (Algebra.QuasiFinite.finite_primesOver P).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (integralClosure A E)
  have he : ∀ q : P.primesOver (integralClosure A E),
      q.1.ramificationIdx A = Q.ramificationIdx A :=
    fun q => Ideal.ramificationIdx_eq_of_isGaloisGroup P q.1 Q Gal(E/F)
  -- the count of embeddings
  letI : Algebra (A ⧸ P) Ω := (Ideal.Quotient.lift P φ (fun _ ha => RingHom.mem_ker.1 ha)).toAlgebra
  letI : Field (A ⧸ P) := Ideal.Quotient.field P
  haveI : CharZero (A ⧸ P) := RingHom.charZero (algebraMap (A ⧸ P) Ω)
  let f : {ψ : integralClosure A E →+* Ω // ψ.comp (algebraMap A (integralClosure A E)) = φ} →
      P.primesOver (integralClosure A E) := fun ψ =>
    ⟨RingHom.ker ψ.1, RingHom.ker_isPrime _, ⟨by
      rw [Ideal.under, RingHom.comap_ker, ψ.2]⟩⟩
  have hcount : {ψ : integralClosure A E →+* Ω |
      ψ.comp (algebraMap A (integralClosure A E)) = φ}.ncard =
      ∑ q : P.primesOver (integralClosure A E), q.1.inertiaDeg A := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card {ψ : integralClosure A E →+* Ω //
      ψ.comp (algebraMap A (integralClosure A E)) = φ} = _
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f)]
    have hfib : ∀ q : P.primesOver (integralClosure A E),
        Nat.card {ψ // f ψ = q} = q.1.inertiaDeg A := by
      intro q
      haveI : q.1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q.1 P
      letI : Field (integralClosure A E ⧸ q.1) := Ideal.Quotient.field q.1
      rw [Nat.card_congr (fiberEquiv φ q f (fun _ => rfl)),
        AlgHom.natCard_of_splits (A ⧸ P) (integralClosure A E ⧸ q.1) Ω
          (fun _ => IsAlgClosed.splits _),
        Ideal.inertiaDeg_eq_of_isMaximal P q.1]
    haveI : ∀ q : P.primesOver (integralClosure A E), Finite {ψ // f ψ = q} := by
      intro q
      haveI : q.1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q.1 P
      letI : Field (integralClosure A E ⧸ q.1) := Ideal.Quotient.field q.1
      exact Finite.of_equiv _ (fiberEquiv φ q f (fun _ => rfl)).symm
    rw [Nat.card_sigma]
    exact Finset.sum_congr rfl fun q _ => hfib q
  rw [hcount, Finset.mul_sum, ← hrank, ← hsum]
  exact Finset.sum_congr rfl fun q _ => by rw [he q]

end RamCount

#print axioms RamCount.ramCount

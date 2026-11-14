import Mathlib

open Polynomial

/-- Values of two ring maps agreeing on invariants differ by an element of the group. -/
theorem exists_root_smul {A B K : Type*} [CommRing A] [CommRing B] [Algebra A B] [Field K]
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G B]
    [Algebra.IsInvariant A B G] (χ χ' : B →+* K)
    (hχ : χ.comp (algebraMap A B) = χ'.comp (algebraMap A B)) (b : B) :
    ∃ k : G, χ' b = χ (k • b) := by
  obtain ⟨P, hP0⟩ := Algebra.IsInvariant.charpoly_mem_lifts A B G b
  have hP : P.map (algebraMap A B) = MulSemiringAction.charpoly G b := hP0
  have h1 : P.eval₂ (χ'.comp (algebraMap A B)) (χ' b) = 0 := by
    rw [← Polynomial.hom_eval₂, ← Polynomial.eval_map, hP, MulSemiringAction.eval_charpoly,
      map_zero]
  rw [← hχ, ← Polynomial.eval_map, ← Polynomial.map_map, hP, MulSemiringAction.charpoly_eq,
    Polynomial.map_prod, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h1
  obtain ⟨k, -, hk⟩ := h1
  refine ⟨k, ?_⟩
  simpa [sub_eq_zero] using hk

theorem exists_comp_smul_eq {A B K : Type*} [CommRing A] [CommRing B] [Algebra A B] [Field K]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] (φ φ' : B →+* K)
    (h : φ.comp (algebraMap A B) = φ'.comp (algebraMap A B)) :
    ∃ g : G, ∀ b, φ' b = φ (g • b) := by
  classical
  cases nonempty_fintype G
  set Q := RingHom.ker φ with hQdef
  set Q' := RingHom.ker φ' with hQ'def
  have : Q.IsPrime := RingHom.ker_isPrime φ
  have : Q'.IsPrime := RingHom.ker_isPrime φ'
  have hunder : Q.under A = Q'.under A := by
    ext a
    simp only [Ideal.under, Ideal.mem_comap, Q, Q', RingHom.mem_ker]
    rw [← RingHom.comp_apply, h, RingHom.comp_apply]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G Q Q' hunder
  let ψ : B →+* K := φ'.comp (MulSemiringAction.toRingHom G B g)
  have hψ : ∀ b, ψ b = φ' (g • b) := fun _ => rfl
  have hkerψ : ∀ b, ψ b = 0 ↔ φ b = 0 := by
    intro b
    rw [hψ]
    change g • b ∈ Q' ↔ b ∈ Q
    rw [hg, Ideal.smul_mem_pointwise_smul_iff]
  have hψA : ψ.comp (algebraMap A B) = φ.comp (algebraMap A B) := by
    ext a
    change φ' (g • algebraMap A B a) = φ (algebraMap A B a)
    rw [smul_algebraMap]
    exact (congrArg (fun f : A →+* K => f a) h).symm
  set P := Q.under A
  have : Q.LiesOver P := ⟨rfl⟩
  let φb : B ⧸ Q →+* K := Ideal.Quotient.lift Q φ (fun b hb => hb)
  let ψb : B ⧸ Q →+* K := Ideal.Quotient.lift Q ψ (fun b hb => (hkerψ b).2 hb)
  have hφb : Function.Injective φb :=
    RingHom.lift_injective_of_ker_le_ideal _ _ (fun b hb => hb)
  have hψb : Function.Injective ψb :=
    RingHom.lift_injective_of_ker_le_ideal _ _ (fun b hb => (hkerψ b).1 hb)
  have hrange1 : ∀ x : B ⧸ Q, ∃ y : B ⧸ Q, ψb x = φb y := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨k, hk⟩ := exists_root_smul G φ ψ hψA.symm b
    exact ⟨Ideal.Quotient.mk Q (k • b), hk⟩
  have hrange2 : ∀ y : B ⧸ Q, ∃ x : B ⧸ Q, φb y = ψb x := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨k, hk⟩ := exists_root_smul G ψ φ hψA b
    exact ⟨Ideal.Quotient.mk Q (k • b), hk⟩
  choose τf hτf using hrange1
  choose τi hτi using hrange2
  have hτ1 : ∀ x, τi (τf x) = x := fun x => hψb (by rw [← hτi, ← hτf])
  have hτ2 : ∀ y, τf (τi y) = y := fun y => hφb (by rw [← hτf, ← hτi])
  let τ : (B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q) :=
    { toFun := τf
      invFun := τi
      left_inv := hτ1
      right_inv := hτ2
      map_mul' := fun x y => hφb (by rw [map_mul, ← hτf, ← hτf, ← hτf, map_mul])
      map_add' := fun x y => hφb (by rw [map_add, ← hτf, ← hτf, ← hτf, map_add])
      commutes' := by
        intro r
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        apply hφb
        rw [← hτf]
        change ψ (algebraMap A B a) = φ (algebraMap A B a)
        exact congrArg (fun f : A →+* K => f a) hψA }
  obtain ⟨s, hs⟩ := Ideal.Quotient.stabilizerHom_surjective G P Q τ
  have key : ∀ b, φ' (g • b) = φ ((s : G) • b) := by
    intro b
    have e1 : τ (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q ((s : G) • b) := by
      rw [← hs]
      rfl
    have e2 := hτf (Ideal.Quotient.mk Q b)
    change ψ b = φb (τ (Ideal.Quotient.mk Q b)) at e2
    rw [e1] at e2
    exact e2
  refine ⟨(s : G) * g⁻¹, fun b => ?_⟩
  have := key (g⁻¹ • b)
  rwa [smul_inv_smul, ← mul_smul] at this

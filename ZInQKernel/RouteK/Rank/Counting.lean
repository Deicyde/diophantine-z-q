import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Coset.Card

/-!
# Counting `A/2A`

`docs/research/pc-audit.md` RK9, abstractly: if `A` is a finitely generated abelian group whose
2-torsion `A[2]` has exactly 4 elements and `A` has an element of infinite order, then `A/2A` has
at least 8 elements (`eight_le_card_quotient_two`).

Proof: by the structure theorem `A ≅ ℤⁿ × T` with `T` finite, and `n ≥ 1`. The map
`A → ℤ/2 × T/2T`, `(v, t) ↦ (v₀ mod 2, t mod 2T)` is onto and kills `2A`, so
`#(A/2A) ≥ 2 · #(T/2T)`; for the finite group `T`, `#(T/2T) = #T[2]` (kernel and cokernel of
doubling have the same size), and `T[2] ⊇` the image of `A[2]` (as `ℤⁿ` is torsion-free).
-/

namespace ZInQ.RouteK.Rank

/-- In a finite abelian group, `#(T/2T) = #T[2]`. -/
theorem card_quotient_two_eq_card_ker {T : Type*} [AddCommGroup T] [Finite T] :
    Nat.card (T ⧸ (nsmulAddMonoidHom 2 : T →+ T).range) =
      Nat.card (nsmulAddMonoidHom 2 : T →+ T).ker := by
  set φ : T →+ T := nsmulAddMonoidHom 2
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.range
  have h2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv] at h2
  have hpos : 0 < Nat.card φ.range := Nat.card_pos
  have : Nat.card (T ⧸ φ.range) * Nat.card φ.range = Nat.card φ.ker * Nat.card φ.range := by
    rw [← h1, h2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem nsmul_two_eq_zero_of_zmod_two (z : ZMod 2) : 2 • z = 0 := by
  revert z; decide

/-- `ℤⁿ` has no 2-torsion. -/
theorem finsupp_int_eq_zero_of_two_nsmul {n : ℕ} {v : Fin n →₀ ℤ} (h : 2 • v = 0) : v = 0 := by
  ext i
  have := congrArg (fun w : Fin n →₀ ℤ => w i) h
  simp only [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  omega

/-- **RK9, counting.** A finitely generated abelian group with `#A[2] = 4` and an element of
infinite order has `#(A/2A) ≥ 8` (when `A/2A` is finite, which it always is). -/
theorem eight_le_card_quotient_two {A : Type*} [AddCommGroup A] [AddGroup.FG A]
    (h4 : Nat.card (nsmulAddMonoidHom 2 : A →+ A).ker = 4) (hinf : ∃ a : A, ¬IsOfFinAddOrder a)
    [Finite (A ⧸ (nsmulAddMonoidHom 2 : A →+ A).range)] :
    8 ≤ Nat.card (A ⧸ (nsmulAddMonoidHom 2 : A →+ A).range) := by
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  set T := DirectSum ι fun i => ZMod (p i ^ e i)
  have : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have : Finite T := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  -- `n ≥ 1`
  have hn : 0 < n := by
    obtain ⟨a, ha⟩ := hinf
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    apply ha
    have hfin : IsOfFinAddOrder (f a) := by
      have h1 : (f a).1 = 0 := Subsingleton.elim _ _
      have h2 : IsOfFinAddOrder (f a).2 := isOfFinAddOrder_of_finite _
      obtain ⟨m, hm, hm'⟩ := h2.exists_nsmul_eq_zero
      refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m, hm, ?_⟩
      refine Prod.ext (Subsingleton.elim _ _) ?_
      simpa using hm'
    simpa using f.symm.toAddMonoidHom.isOfFinAddOrder hfin
  set i₀ : Fin n := ⟨0, hn⟩
  set RT := (nsmulAddMonoidHom 2 : T →+ T).range
  -- the map `ρ : A → ℤ/2 × T/2T`
  let ρ₁ : ((Fin n →₀ ℤ) × T) →+ ZMod 2 :=
    (Int.castAddHom (ZMod 2)).comp ((Finsupp.applyAddHom i₀).comp (AddMonoidHom.fst _ _))
  let ρ₂ : ((Fin n →₀ ℤ) × T) →+ T ⧸ RT := (QuotientAddGroup.mk' RT).comp (AddMonoidHom.snd _ _)
  let ρ : A →+ ZMod 2 × (T ⧸ RT) := (ρ₁.prod ρ₂).comp f.toAddMonoidHom
  have hρ : Function.Surjective ρ := by
    rintro ⟨z, q⟩
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk'_surjective RT q
    refine ⟨f.symm (Finsupp.single i₀ k, t), ?_⟩
    simp [ρ, ρ₁, ρ₂]
  have hker : (nsmulAddMonoidHom 2 : A →+ A).range ≤ ρ.ker := by
    rintro _ ⟨a, rfl⟩
    rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, map_nsmul]
    ext
    · exact nsmul_two_eq_zero_of_zmod_two _
    · obtain ⟨t, ht⟩ := QuotientAddGroup.mk'_surjective RT (ρ a).2
      rw [Prod.smul_snd, ← ht, ← map_nsmul, Prod.snd_zero, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.eq_zero_iff]
      exact ⟨t, rfl⟩
  have hlift : Function.Surjective (QuotientAddGroup.lift _ ρ hker) := by
    intro y
    obtain ⟨a, rfl⟩ := hρ y
    exact ⟨a, rfl⟩
  have hcard1 := Nat.card_le_card_of_surjective _ hlift
  rw [Nat.card_prod, Nat.card_zmod, card_quotient_two_eq_card_ker] at hcard1
  -- `#A[2] ≤ #T[2]`
  have hcard2 : Nat.card (nsmulAddMonoidHom 2 : A →+ A).ker ≤
      Nat.card (nsmulAddMonoidHom 2 : T →+ T).ker := by
    let g : (nsmulAddMonoidHom 2 : A →+ A).ker → (nsmulAddMonoidHom 2 : T →+ T).ker :=
      fun a => ⟨(f a).2, by
        have ha := a.2
        rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at ha ⊢
        have := congrArg (fun x => (f x).2) ha
        simpa [map_nsmul] using this⟩
    refine Nat.card_le_card_of_injective g fun a b hab => ?_
    have hab' : (f a).2 = (f b).2 := congrArg Subtype.val hab
    have h1 : ∀ c : (nsmulAddMonoidHom 2 : A →+ A).ker, (f c).1 = 0 := fun c => by
      have hc := c.2
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at hc
      have := congrArg (fun x => (f x).1) hc
      simp only [map_nsmul, Prod.smul_fst, map_zero, Prod.fst_zero] at this
      exact finsupp_int_eq_zero_of_two_nsmul this
    apply Subtype.ext
    apply f.injective
    exact Prod.ext (by rw [h1 a, h1 b]) hab'
  omega

end ZInQ.RouteK.Rank

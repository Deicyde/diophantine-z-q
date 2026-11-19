import ZInQKernel.Contrib.OneProof.RC.Adelic.Coordinates

/-!
# Patching a finite set of local lattice modifications
Proved here, for tex 8464–8468. Approximation modulo a prime power, followed
by multiplication by a product of powers of the other primes, gives the required
local generators of the rational intersection.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Adelic

open Eichler Module QuaternionAlgebra

variable {a b : ℚ}

def intersection (A : (p : Prime) → Submodule ℤ_[p.val] (Bp p.val a b)) :
    Submodule ℤ (B a b) where
  carrier := {x | ∀ p, toLocal p.val x ∈ A p}
  zero_mem' := by simp
  add_mem' hx hy p := by rw [map_add]; exact (A p).add_mem (hx p) (hy p)
  smul_mem' n x hx p := by rw [map_zsmul]; exact (A p).toAddSubgroup.zsmul_mem (hx p) n

theorem localLattice_mono (p : Prime) {L M : Submodule ℤ (B a b)} (h : L ≤ M) :
    localLattice p.val L ≤ localLattice p.val M :=
  Submodule.span_mono (Set.image_mono h)

theorem localLattice_intersection_le (A : (p : Prime) → Submodule ℤ_[p.val] (Bp p.val a b))
    (p : Prime) : localLattice p.val (intersection A) ≤ A p :=
  Submodule.span_le.mpr (by rintro _ ⟨x, hx, rfl⟩; exact hx p)

theorem nat_isUnit (p : Prime) {m : ℕ} (h : ¬ p.val ∣ m) :
    IsUnit (m : ℤ_[p.val]) := by
  by_contra hn
  have hh := (IsLocalRing.mem_maximalIdeal (m : ℤ_[p.val])).mpr hn
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at hh
  exact h hh

/-- Integral vectors in the completion lift to rational lattice vectors modulo every power. -/
theorem approximate {L : Submodule ℤ (B a b)} (hL : FullLattice L) (p : Prime) (k : ℕ)
    {x : Bp p.val a b} (hx : x ∈ localLattice p.val L) :
    ∃ y ∈ L, ∃ w ∈ localLattice p.val L, x - toLocal p.val y = (p.val : ℤ_[p.val]) ^ k • w := by
  let e := hL.ratBasis (basisOneIJK a 0 b)
  have he : Submodule.span ℤ (Set.range e) = L := hL.span_ratBasis _
  rw [← he] at hx ⊢
  choose c hc using (mem_localLattice_basis p e x).mp hx
  let t (i : Fin 4) : ℤ := (PadicInt.toZModPow k (c i)).val
  let y := e.equivFun.symm fun i => (t i : ℚ)
  have hy (i : Fin 4) : e.repr y i = (t i : ℚ) :=
    congrFun (e.equivFun.apply_symm_apply _) i
  have hd (i : Fin 4) : ∃ d : ℤ_[p.val],
      c i - (t i : ℤ_[p.val]) = (p.val : ℤ_[p.val]) ^ k * d := by
    have hmem : c i - (t i : ℤ_[p.val]) ∈
        RingHom.ker (PadicInt.toZModPow k : ℤ_[p.val] →+* ZMod (p.val ^ k)) := by
      rw [RingHom.mem_ker, map_sub, map_intCast, sub_eq_zero]
      change _ = (((PadicInt.toZModPow k (c i)).val : ℤ) : ZMod (p.val ^ k))
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
    exact hmem
  choose d hd using hd
  let w := (localCoordinates p e).symm fun i => (d i : ℚ_[p.val])
  have hw : localCoordinates p e w = fun i => (d i : ℚ_[p.val]) :=
    (localCoordinates p e).apply_symm_apply _
  refine ⟨y, (e.mem_span_iff_repr_mem ℤ y).mpr (fun i => ⟨t i, (hy i).symm⟩),
    w, (mem_localLattice_basis p e w).mpr (fun i => ⟨d i, by rw [hw]⟩), ?_⟩
  apply (localCoordinates p e).injective
  rw [map_sub, localCoordinates_toLocal, ← IsScalarTower.algebraMap_smul ℚ_[p.val], map_smul, hw]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hy]
  rw [← hc]
  simpa using congrArg (algebraMap ℤ_[p.val] ℚ_[p.val]) (hd i)

/-- The finite set of primes dividing a nonzero natural number. -/
theorem finite_prime_dvd {n : ℕ} (hn : n ≠ 0) : {p : Prime | p.val ∣ n}.Finite :=
  ((n.primeFactors.finite_toSet).preimage Subtype.val_injective.injOn).subset
    (fun p hp => p.prop.mem_primeFactors hp hn)

set_option maxHeartbeats 2000000 in
/-- If each local modification lies inside the corresponding completion and contains
a specified prime-power multiple of it, with exponent zero outside a finite set,
the rational intersection is full and has exactly those completions. -/
theorem patch_inside {L : Submodule ℤ (B a b)} (hL : FullLattice L)
    (A : (p : Prime) → Submodule ℤ_[p.val] (Bp p.val a b)) (s : Finset Prime)
    (k : Prime → ℕ) (hk : ∀ p ∉ s, k p = 0)
    (hle : ∀ p, A p ≤ localLattice p.val L)
    (hge : ∀ (p : Prime) (x : Bp p.val a b), x ∈ localLattice p.val L → (p.val : ℤ_[p.val]) ^ k p • x ∈ A p) :
    FullLattice (intersection A) ∧
      ∀ p, localLattice p.val (intersection A) = A p := by
  classical
  have hs (q : Prime) {S : Finset Prime} (hq : q ∈ S ∨ k q = 0) :
      q.val ^ k q ∣ ∏ r ∈ S, r.val ^ k r := by
    rcases hq with hq | hq
    · exact Finset.dvd_prod_of_mem _ hq
    · simp [hq]
  have hmul (q : Prime) {m : ℕ} (hm : q.val ^ k q ∣ m) {x : Bp q.val a b}
      (hx : x ∈ localLattice q.val L) : (m : ℤ_[q.val]) • x ∈ A q := by
    obtain ⟨n, rfl⟩ := hm
    rw [Nat.cast_mul, Nat.cast_pow, mul_comm, mul_smul]
    exact (A q).smul_mem _ (hge q x hx)
  have hsub : intersection A ≤ L :=
    fun x hx => (mem_iff_all_local hL x).mpr (fun p => hle p (hx p))
  have hscalar (S : Finset Prime) {x : B a b} (hx : x ∈ L) (q : Prime)
      (hq : q ∈ S ∨ k q = 0) :
      toLocal q.val ((∏ r ∈ S, r.val ^ k r : ℕ) • x) ∈ A q := by
    simpa only [map_nsmul, Nat.cast_smul_eq_nsmul] using
      hmul q (hs q hq) ((mem_iff_all_local hL x).mp hx q)
  constructor
  · let _ := hL
    let m : ℕ := ∏ r ∈ s, r.val ^ k r
    have hm : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun r _ => pow_ne_zero _ r.prop.ne_zero
    refine ⟨Submodule.FG.of_le_of_isNoetherian hsub, top_unique ?_⟩
    rw [← hL.span_eq_top]
    apply Submodule.span_le.mpr
    intro x hx
    have hy : m • x ∈ intersection A := fun q =>
      hscalar s hx q (or_iff_not_imp_left.mpr (hk q))
    have h : m • x ∈ Submodule.span ℚ (intersection A : Set (B a b)) :=
      Submodule.subset_span (show m • x ∈ (intersection A : Set (B a b)) from hy)
    have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    let D : Submodule ℚ (B a b) := Submodule.span ℚ (intersection A : Set (B a b))
    have h' : (m : ℚ)⁻¹ • (m • x) ∈ D := D.smul_mem (m : ℚ)⁻¹ h
    have he : (m : ℚ)⁻¹ • (m • x) = x := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hm', one_smul]
    exact he ▸ h'
  · intro p
    refine le_antisymm (localLattice_intersection_le A p) ?_
    intro x hx
    let S := s.erase p
    let m : ℕ := ∏ r ∈ S, r.val ^ k r
    have hm : ¬ p.val ∣ m := by
      intro hd
      rw [p.prop.prime.dvd_finsetProd_iff] at hd
      obtain ⟨r, hr, hdr⟩ := hd
      have he := (Nat.dvd_prime r.prop).mp (p.prop.dvd_of_dvd_pow hdr)
      exact (Finset.ne_of_mem_erase hr) (Subtype.ext (he.resolve_left p.prop.ne_one).symm)
    obtain ⟨u, hu⟩ := nat_isUnit p hm
    have hp' (w : Bp p.val a b) (hw : w ∈ localLattice p.val L) :
        (p.val : ℤ_[p.val]) ^ k p • w ∈ localLattice p.val (intersection A) := by
      have hh (y : B a b) (hy : y ∈ L) : (m * p.val ^ k p) • y ∈ intersection A := by
        intro q
        rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[q.val]]
        apply hmul q _ ((mem_iff_all_local hL y).mp hy q)
        by_cases he : q = p
        · subst q
          exact dvd_mul_left _ _
        · exact (hs q (by
            by_cases ht : q ∈ s
            · exact Or.inl (Finset.mem_erase.mpr ⟨he, ht⟩)
            · exact Or.inr (hk q ht))).trans (dvd_mul_right _ _)
      let D := localLattice p.val (intersection A)
      have ht : ((m : ℤ_[p.val]) * (p.val : ℤ_[p.val]) ^ k p) • w ∈ D := by
        induction hw using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨y, hy, rfl⟩ := hz
          have h : toLocal p.val ((m * p.val ^ k p) • y) ∈ D :=
            Submodule.subset_span (Set.mem_image_of_mem (toLocal p.val) (hh y hy))
          simpa only [map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[p.val], Nat.cast_mul, Nat.cast_pow] using h
        | zero => simp
        | add z v _ _ hz hv => simpa only [smul_add] using D.add_mem hz hv
        | smul t z _ hz =>
          rw [smul_comm]
          exact D.smul_mem t hz
      have ht' := D.smul_mem (↑u⁻¹ : ℤ_[p.val]) ht
      rwa [← hu, smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at ht'
    obtain ⟨y, hy, w, hw, he⟩ := approximate hL p (k p) (hle p hx)
    have hyP : toLocal p.val y ∈ A p := by
      rw [← sub_sub_self x (toLocal p.val y), he]
      exact (A p).sub_mem hx (hge p w hw)
    have hyM : m • y ∈ intersection A := by
      intro q
      by_cases heq : q = p
      · subst q
        rw [map_nsmul]
        exact (A p).toAddSubmonoid.nsmul_mem hyP _
      · exact hscalar S hy q (by
          by_cases ht : q ∈ s
          · exact Or.inl (Finset.mem_erase.mpr ⟨heq, ht⟩)
          · exact Or.inr (hk q ht))
    have hyD : toLocal p.val y ∈ localLattice p.val (intersection A) := by
      have h : toLocal p.val (m • y) ∈ localLattice p.val (intersection A) :=
        Submodule.subset_span (Set.mem_image_of_mem (toLocal p.val) hyM)
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[p.val], ← hu] at h
      simpa [smul_smul] using (localLattice p.val (intersection A)).smul_mem (↑u⁻¹ : ℤ_[p.val]) h
    exact ((localLattice p.val (intersection A)).sub_mem_iff_left hyD).mp (he ▸ hp' w hw)


end ZInQ.Manuscript.RC.Adelic

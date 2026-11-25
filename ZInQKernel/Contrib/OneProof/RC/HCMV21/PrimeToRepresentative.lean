import ZInQKernel.Contrib.OneProof.RC.HCMV21.LeftIdealMirror

/-! Every class of locally principal left ideals of an order in a definite
quaternion algebra has an integral representative containing an integer prime
to a given prime `q`. A global element of the ideal approximates a local
generator at `q` modulo `q` (Nakayama's lemma over `ℤ_q`), so right division
by it makes the ideal locally trivial at `q`; clearing denominators away from
`q` keeps an integer prime to `q`. This is the arithmetic input that lets the
separable-scope candidates (ideals containing an integer prime to `q`) reach
every class. All proofs are Lean proofs. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open Eichler Adelic

variable {a b : ℚ}

section Local

variable (p : ℕ) [Fact p.Prime]

/-- The completion of a lattice as a set of local elements. -/
theorem mem_completion_iff' (R : Order a b) (s : Bp p a b) :
    s ∈ R.completion p ↔ s ∈ localLattice p R.lattice := by
  rw [← R.completion_toSubmodule]
  rfl

/-- Approximation modulo `p`: every element of a completed lattice is the image
of a global element of the lattice up to `p` times the completed lattice. -/
theorem exists_global_approx (L : Submodule ℤ (B a b)) {y : Bp p a b}
    (hy : y ∈ localLattice p L) :
    ∃ x ∈ L, y - toLocal p x ∈ (Ideal.span {(p : ℤ_[p])}) • localLattice p L := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, by rw [sub_self]; exact Submodule.zero_mem _⟩
  | zero => exact ⟨0, L.zero_mem, by rw [map_zero, sub_zero]; exact Submodule.zero_mem _⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨x, hx, h⟩ := hy
    obtain ⟨x', hx', h'⟩ := hy'
    refine ⟨x + x', L.add_mem hx hx', ?_⟩
    rw [map_add, add_sub_add_comm]
    exact Submodule.add_mem _ h h'
  | smul c y hy' hy =>
    obtain ⟨x, hx, h⟩ := hy
    let n : ℤ := (PadicInt.appr c 1 : ℤ)
    refine ⟨n • x, L.smul_mem n hx, ?_⟩
    have hc : c - (n : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])} := by
      have h1 := PadicInt.appr_spec 1 c
      rw [pow_one] at h1
      simpa [n] using h1
    have he : c • y - toLocal p (n • x) =
        c • (y - toLocal p x) + (c - (n : ℤ_[p])) • toLocal p x := by
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℤ_[p], smul_sub, sub_smul]
      abel
    rw [he]
    refine Submodule.add_mem _ (Submodule.smul_mem _ c h) ?_
    exact Submodule.smul_mem_smul hc (Submodule.subset_span ⟨x, hx, rfl⟩)

instance zpSMulMulAssoc : IsScalarTower ℤ_[p] (Bp p a b) (Bp p a b) :=
  ⟨fun c y t => by
    change ((c : ℚ_[p]) • y) * t = (c : ℚ_[p]) • (y * t)
    exact smul_mul_assoc _ _ _⟩

instance zpSMulCommClass : SMulCommClass ℤ_[p] (Bp p a b) (Bp p a b) :=
  ⟨fun c y t => by
    change (c : ℚ_[p]) • (y * t) = y * ((c : ℚ_[p]) • t)
    exact (mul_smul_comm _ _ _).symm⟩

/-- Right multiplication by a local element, as a `ℤ_p`-linear map. -/
def localMulRight (t : Bp p a b) : Bp p a b →ₗ[ℤ_[p]] Bp p a b where
  toFun y := y * t
  map_add' y z := add_mul _ _ _
  map_smul' c y := smul_mul_assoc _ _ _

theorem localLattice_fg {L : Submodule ℤ (B a b)} (hL : FullLattice L) :
    (localLattice p L).FG := by
  let e := hL.ratBasis (QuaternionAlgebra.basisOneIJK a 0 b)
  have he : Submodule.span ℤ (Set.range e) = L := hL.span_ratBasis _
  have h := localLattice_basis (⟨p, Fact.out⟩ : Prime) e
  rw [he] at h
  change localLattice p L = _ at h
  rw [h]
  exact Submodule.fg_span (Set.finite_range _)

theorem span_p_le_jacobson : Ideal.span {(p : ℤ_[p])} ≤ Ideal.jacobson ⊥ := by
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, PadicInt.maximalIdeal_eq_span_p]

end Local

namespace LeftIdeal

variable {R : Order a b}

theorem exists_ne_zero (I : LeftIdeal R) : ∃ x ∈ I.lattice, x ≠ 0 := by
  by_contra! h
  have he : I.lattice = ⊥ := le_bot_iff.mp fun x hx => by simpa using h x hx
  have ht := I.full.span_eq_top
  rw [he, Submodule.bot_coe, Submodule.span_zero_singleton] at ht
  exact bot_ne_top ht

/-- At every prime, a locally principal left ideal is generated over the
completed order by the image of one global element of the ideal. -/
theorem exists_local_generator (I : LeftIdeal R) (hI : I.LocallyPrincipal)
    (p : ℕ) [Fact p.Prime] :
    ∃ x ∈ I.lattice, (localLattice p I.lattice : Set (Bp p a b)) =
      (fun y : Bp p a b => y * toLocal p x) '' (R.completion p : Set (Bp p a b)) := by
  obtain ⟨g, hg⟩ := hI p
  have hmemI (y : Bp p a b) : y ∈ localLattice p I.lattice ↔
      ∃ s ∈ R.completion p, s * (g : Bp p a b) = y := by
    change y ∈ (localLattice p I.lattice : Set (Bp p a b)) ↔ _
    rw [hg]
    rfl
  have hg' : (g : Bp p a b) ∈ localLattice p I.lattice :=
    (hmemI _).mpr ⟨1, (R.completion p).one_mem, one_mul _⟩
  -- left stability of the completed ideal
  have hstab (s : Bp p a b) (hs : s ∈ R.completion p) (y : Bp p a b)
      (hy : y ∈ localLattice p I.lattice) : s * y ∈ localLattice p I.lattice := by
    obtain ⟨s', hs', rfl⟩ := (hmemI y).mp hy
    exact (hmemI _).mpr ⟨s * s', (R.completion p).mul_mem hs hs', mul_assoc _ _ _⟩
  obtain ⟨x, hx, happr⟩ := exists_global_approx p I.lattice hg'
  have hxI : toLocal p x ∈ localLattice p I.lattice := Submodule.subset_span ⟨x, hx, rfl⟩
  let Lx := (localLattice p R.lattice).map (localMulRight p (toLocal p x))
  have hle : localLattice p I.lattice ≤ Lx := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (localLattice_fg p I.full)
      (span_p_le_jacobson p)
    intro y hy
    obtain ⟨s, hs, rfl⟩ := (hmemI y).mp hy
    have hsplit : s * (g : Bp p a b) =
        s * toLocal p x + s * ((g : Bp p a b) - toLocal p x) := by
      rw [mul_sub]
      abel
    rw [hsplit]
    refine Submodule.add_mem_sup ⟨s, (mem_completion_iff' p R s).mp hs, rfl⟩ ?_
    rw [Submodule.ideal_span_singleton_smul] at happr ⊢
    obtain ⟨z, hz, hz'⟩ := happr
    rw [← hz']
    refine ⟨s * z, hstab s hs z hz, ?_⟩
    change (p : ℤ_[p]) • (s * z) = s * ((p : ℤ_[p]) • z)
    rw [mul_smul_comm]
  have hge : Lx ≤ localLattice p I.lattice := by
    rintro _ ⟨s, hs, rfl⟩
    exact hstab s ((mem_completion_iff' p R s).mpr hs) _ hxI
  refine ⟨x, hx, ?_⟩
  have heq := le_antisymm hle hge
  ext y
  change y ∈ localLattice p I.lattice ↔ _
  rw [heq]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, (mem_completion_iff' p R s).mpr hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, (mem_completion_iff' p R s).mp hs, rfl⟩

theorem toLocal_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (toLocal p : B a b → Bp p a b) := by
  intro x y h
  ext
  · have := congrArg QuaternionAlgebra.re h; simpa [toLocal] using this
  · have := congrArg QuaternionAlgebra.imI h; simpa [toLocal] using this
  · have := congrArg QuaternionAlgebra.imJ h; simpa [toLocal] using this
  · have := congrArg QuaternionAlgebra.imK h; simpa [toLocal] using this

/-- **Integral prime-to-`q` representatives.** Every locally principal left
ideal of an order in a definite algebra has a right translate contained in the
order and containing an integer prime to `q`. -/
theorem exists_integral_primeTo (I : LeftIdeal R) (hI : I.LocallyPrincipal)
    (ha : a < 0) (hb : b < 0) (q : ℕ) [Fact q.Prime] :
    ∃ u : (B a b)ˣ, (I.translate u).lattice ≤ R.lattice ∧
      ∃ m : ℕ, m.Coprime q ∧ (m : B a b) ∈ (I.translate u).lattice := by
  obtain ⟨x, hx, hgen⟩ := I.exists_local_generator hI q
  have hx0 : x ≠ 0 := by
    rintro rfl
    obtain ⟨y, hy, hy0⟩ := I.exists_ne_zero
    have hyl : toLocal q y ∈ (localLattice q I.lattice : Set (Bp q a b)) :=
      Submodule.subset_span ⟨y, hy, rfl⟩
    rw [hgen] at hyl
    obtain ⟨s, -, hs⟩ := hyl
    simp only [map_zero, mul_zero] at hs
    exact hy0 (toLocal_injective q (hs.symm.trans (map_zero _).symm))
  let v := unitOfNeZero ha hb x hx0
  let J₀ := I.translate v⁻¹
  have hv : (v : B a b) = x := rfl
  -- `1 ∈ J₀`
  have h1 : (1 : B a b) ∈ J₀.lattice := by
    rw [mem_translate, inv_inv, one_mul, hv]
    exact hx
  -- at `q`, `J₀` is locally the order
  have hJ₀q (y : B a b) (hy : y ∈ J₀.lattice) : toLocal q y ∈ localLattice q R.lattice := by
    rw [mem_translate, inv_inv, hv] at hy
    have hyl : toLocal q (y * x) ∈ (localLattice q I.lattice : Set (Bp q a b)) :=
      Submodule.subset_span ⟨_, hy, rfl⟩
    rw [hgen] at hyl
    obtain ⟨s, hs, hs'⟩ := hyl
    have hy' : toLocal q y * toLocal q x = s * toLocal q x := by rw [← map_mul, ← hs']
    have hxu : toLocal q x * toLocal q (↑v⁻¹ : B a b) = 1 := by
      rw [← map_mul, ← hv, Units.mul_inv, map_one]
    have : toLocal q y = s := by
      calc toLocal q y = toLocal q y * toLocal q x * toLocal q (↑v⁻¹ : B a b) := by
            rw [mul_assoc, hxu, mul_one]
        _ = s := by rw [hy', mul_assoc, hxu, mul_one]
    rw [this]
    exact (mem_completion_iff' q R s).mp hs
  -- a positive integer clearing denominators of `J₀`
  obtain ⟨D, hD, hDR⟩ := FullLattice.multiple_mem J₀.full R.full
    (QuaternionAlgebra.basisOneIJK a 0 b)
  set D₁ := D.natAbs with hD₁
  have hD₁0 : D₁ ≠ 0 := Int.natAbs_ne_zero.mpr hD
  have hD₁R (y : B a b) (hy : y ∈ J₀.lattice) : D₁ • y ∈ R.lattice := by
    rcases Int.natAbs_eq D with h | h
    · have := hDR y hy
      rw [h, natCast_zsmul] at this
      exact this
    · have := R.lattice.neg_mem (hDR y hy)
      rw [h, neg_smul, neg_neg, natCast_zsmul] at this
      exact this
  set e := D₁.factorization q
  set D' := D₁ / q ^ e with hD'
  have hsplitD : q ^ e * D' = D₁ := Nat.ordProj_mul_ordCompl_eq_self D₁ q
  have hD'cop : D'.Coprime q := (Nat.coprime_ordCompl (Fact.out : q.Prime) hD₁0).symm
  have hD'0 : D' ≠ 0 := by
    intro h
    rw [h, mul_zero] at hsplitD
    exact hD₁0 hsplitD.symm
  have hD'B : (D' : B a b) ≠ 0 := by
    intro h
    have h' : algebraMap ℚ (B a b) (D' : ℚ) = 0 := by rw [map_natCast]; exact h
    exact hD'0 (by exact_mod_cast (algebraMap ℚ (B a b)).injective (h'.trans (map_zero _).symm))
  let w := unitOfNeZero ha hb (D' : B a b) hD'B
  have hw : (w : B a b) = D' := rfl
  refine ⟨v⁻¹ * w, ?_, D', hD'cop, ?_⟩
  · intro y hy
    rw [← translate_translate, mem_translate] at hy
    set y₀ := y * (↑w⁻¹ : B a b) with hy₀
    have hyy : y = (D' : B a b) * y₀ := by
      calc y = y * (↑w⁻¹ : B a b) * w := by rw [mul_assoc, Units.inv_mul, mul_one]
        _ = y₀ * D' := by rw [hw]
        _ = (D' : B a b) * y₀ := (Nat.cast_commute D' y₀).eq.symm
    change y₀ ∈ J₀.lattice at hy
    apply (mem_iff_all_local R.full y).mpr
    intro p
    by_cases hpq : p.val = q
    · have h := hJ₀q y₀ hy
      rw [hyy, map_mul, map_natCast]
      have hpq' : (p : ℕ) = q := hpq
      subst hpq'
      have : ((D' : Bp p.val a b)) * toLocal p.val y₀ = (D' : ℤ_[p.val]) • toLocal p.val y₀ := by
        rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
      rw [this]
      exact Submodule.smul_mem _ _ h
    · have hR := hD₁R y₀ hy
      have hl : toLocal p.val (D₁ • y₀) ∈ localLattice p.val R.lattice :=
        Submodule.subset_span ⟨_, hR, rfl⟩
      have hqu : IsUnit ((q : ℤ_[p.val]) ^ e) := by
        apply IsUnit.pow
        apply PadicInt.isUnit_iff.mpr
        apply PadicInt.norm_natCast_eq_one_iff.mpr
        exact ((Nat.coprime_primes Fact.out p.property).mpr (Ne.symm hpq)).symm
      rw [hyy, map_mul, map_natCast]
      have hD₁l : toLocal p.val (D₁ • y₀) = ((q : ℤ_[p.val]) ^ e) • ((D' : ℤ_[p.val]) • toLocal p.val y₀) := by
        rw [map_nsmul, ← hsplitD, smul_smul, ← Nat.cast_pow, ← Nat.cast_mul,
          Nat.cast_smul_eq_nsmul]
      have hinv : (↑hqu.unit⁻¹ : ℤ_[p.val]) * (q : ℤ_[p.val]) ^ e = 1 := hqu.val_inv_mul
      have : ((D' : Bp p.val a b)) * toLocal p.val y₀ =
          (↑hqu.unit⁻¹ : ℤ_[p.val]) • toLocal p.val (D₁ • y₀) := by
        rw [hD₁l, smul_smul, hinv, one_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
      rw [this]
      exact Submodule.smul_mem _ _ hl
  · rw [← translate_translate, mem_translate]
    rw [show (D' : B a b) * (↑w⁻¹ : B a b) = 1 by rw [← hw, Units.mul_inv]]
    exact h1

end LeftIdeal

end ZInQ.Manuscript.RC.HCMV21

import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.AbVarBC.Dim
import Mathlib.FieldTheory.Finiteness

/-!
# t5-torsion, part 8: the Tate module from the torsion counts

`T5Torsion.TateFree.tate_linearEquiv`: if an abelian group `M` has `#M[ℓⁿ] = ℓ^{nr}` for every
`n`, then `T_ℓ M ≃ ℤ_ℓ^r` (the kernel's `PkgI3.Tate.T`). Hence the textbook leaf T26
(`PkgI3.TateModuleFree`) follows from T5 (`PkgI2.TorsionStructure`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace T5Torsion.TateFree

open PkgI3.Tate

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {M : Type*} [AddCommGroup M]

/-- `M[ℓⁿ]`. -/
abbrev tb (ℓ : ℕ) (M : Type*) [AddCommGroup M] (n : ℕ) : AddSubgroup M :=
  AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ)

theorem mem_tb {n : ℕ} {x : M} : x ∈ tb ℓ M n ↔ ℓ ^ n • x = 0 :=
  AddSubgroup.torsionBy.nsmul_iff

theorem pow_smul_add {x : ℕ → M} (hx : x ∈ T ℓ M) (m k : ℕ) : ℓ ^ k • x (m + k) = x m := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_smul, ← add_assoc, hx.2 (m + k), ih]

section Counts

variable (r : ℕ) (hcard : ∀ n : ℕ, Nat.card (tb ℓ M n) = ℓ ^ (n * r))
include hcard

theorem finite_tb (n : ℕ) : Finite (tb ℓ M n) :=
  Nat.finite_of_card_ne_zero (by rw [hcard n]; exact pow_ne_zero _ hℓ.out.ne_zero)

/-- Multiplication by `ℓ` maps `M[ℓⁿ⁺¹]` onto `M[ℓⁿ]` (counting). -/
theorem exists_lift (n : ℕ) (y : M) (hy : ℓ ^ n • y = 0) :
    ∃ x : M, ℓ ^ (n + 1) • x = 0 ∧ ℓ • x = y := by
  let f : tb ℓ M (n + 1) →+ tb ℓ M n :=
    { toFun := fun x => ⟨ℓ • x.1, mem_tb.2 (by
        rw [← mul_smul, ← pow_succ]; exact mem_tb.1 x.2)⟩
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  haveI := finite_tb r hcard (n + 1)
  haveI := finite_tb r hcard n
  have hker : Nat.card f.ker = ℓ ^ r := by
    rw [show ℓ ^ r = ℓ ^ (1 * r) by rw [_root_.one_mul], ← hcard 1]
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, mem_tb.2 (by
          have h : (f x.1).1 = 0 := congrArg Subtype.val (AddMonoidHom.mem_ker.1 x.2)
          rw [pow_one]; exact h)⟩
        invFun := fun y => ⟨⟨y.1, mem_tb.2 (by
          have h := mem_tb.1 y.2
          rw [pow_one] at h
          rw [pow_succ, mul_smul, h, smul_zero])⟩, AddMonoidHom.mem_ker.2 (by
          ext
          have h := mem_tb.1 y.2
          rw [pow_one] at h
          simpa [f] using h)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hrange : Nat.card f.range = Nat.card (tb ℓ M n) := by
    have h1 := AddSubgroup.card_mul_index f.ker
    rw [AddSubgroup.index_ker, hker, hcard (n + 1)] at h1
    rw [hcard n]
    have hpos : 0 < ℓ ^ r := pow_pos hℓ.out.pos r
    have : ℓ ^ ((n + 1) * r) = ℓ ^ r * ℓ ^ (n * r) := by rw [← pow_add]; ring_nf
    rw [this] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have htop : f.range = ⊤ := AddSubgroup.eq_top_of_card_eq _ hrange
  obtain ⟨x, hx⟩ := (AddMonoidHom.range_eq_top.1 htop) ⟨y, mem_tb.2 hy⟩
  exact ⟨x.1, mem_tb.1 x.2, congrArg Subtype.val hx⟩

/-- Every `y ∈ M[ℓ]` is the first term of an element of `T_ℓ M`. -/
theorem exists_tate_lift (y : M) (hy : ℓ • y = 0) : ∃ x : T ℓ M, x.1 1 = y := by
  let g : (k : ℕ) → {z : M // ℓ ^ (k + 1) • z = 0} := fun k =>
    Nat.rec ⟨y, by simpa using hy⟩
      (fun k z => ⟨(exists_lift r hcard (k + 1) z.1 z.2).choose,
        (exists_lift r hcard (k + 1) z.1 z.2).choose_spec.1⟩) k
  have hg : ∀ k, ℓ • (g (k + 1)).1 = (g k).1 := fun k =>
    (exists_lift r hcard (k + 1) (g k).1 (g k).2).choose_spec.2
  let x : ℕ → M := fun m => Nat.casesOn m 0 (fun k => (g k).1)
  have hx : x ∈ T ℓ M := by
    refine ⟨rfl, fun m => ?_⟩
    cases m with
    | zero => simpa [x, g] using hy
    | succ k => exact hg k
  exact ⟨⟨x, hx⟩, rfl⟩

end Counts

theorem zsmul_emod_of {m : ℕ} {z : M} (hz : m • z = 0) (c : ℤ) : (c % m) • z = c • z := by
  conv_rhs => rw [← Int.emod_add_mul_ediv c m]
  rw [add_zsmul, mul_comm, mul_zsmul, natCast_zsmul, hz, zsmul_zero, add_zero]

/-- The map `ℤ_ℓ^r → T_ℓ M`, `a ↦ ∑ aᵢ Xᵢ`, at level `n`. -/
theorem lc_apply {r : ℕ} (X : Fin r → T ℓ M) (a : Fin r → ℤ_[ℓ]) (n : ℕ) :
    (Fintype.linearCombination ℤ_[ℓ] X a).1 n =
      ∑ i, (PadicInt.toZModPow n (a i)).val • (X i).1 n := by
  rw [Fintype.linearCombination_apply]
  let E : T ℓ M →+ M := (Pi.evalAddMonoidHom (fun _ : ℕ => M) n).comp (T ℓ M).subtype
  change E (∑ i, a i • X i) = _
  rw [map_sum]
  rfl

section Main

variable (r : ℕ) (hcard : ∀ n : ℕ, Nat.card (tb ℓ M n) = ℓ ^ (n * r))
include hcard

omit hcard in
/-- A finite `𝔽_ℓ`-space of order `ℓ^r` has `r` elements independent over `ℤ` modulo `ℓ`. -/
theorem basis_of_card {V : Type*} [AddCommGroup V] [Module (ZMod ℓ) V] [Finite V]
    (hc : Nat.card V = ℓ ^ r) :
    ∃ e : Fin r → V, ∀ c : Fin r → ℤ, ∑ i, c i • e i = 0 → ∀ i, (ℓ : ℤ) ∣ c i := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI hfin : Module.Finite (ZMod ℓ) V := Module.Finite.of_finite
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := V)
  have hfr : Module.finrank (ZMod ℓ) V = r := by
    rw [hc, Nat.card_zmod] at h1
    exact (Nat.pow_right_injective hℓ.out.two_le h1).symm
  let b : Module.Basis (Fin r) (ZMod ℓ) V := Module.finBasisOfFinrankEq (ZMod ℓ) V hfr
  refine ⟨fun i => b i, fun c hc i => ?_⟩
  have hc' : ∑ j, (c j : ZMod ℓ) • b j = 0 := by
    simp only [Int.cast_smul_eq_zsmul]
    exact hc
  have := Fintype.linearIndependent_iff.mp b.linearIndependent (fun j => (c j : ZMod ℓ)) hc' i
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (c i) ℓ).mp this

/-- An `𝔽_ℓ`-basis of `M[ℓ]`, as elements of `M` with the independence over `ℤ` modulo `ℓ`. -/
theorem exists_basis : ∃ e : Fin r → M, (∀ i, ℓ • e i = 0) ∧
    ∀ c : Fin r → ℤ, ∑ i, c i • e i = 0 → ∀ i, (ℓ : ℤ) ∣ c i := by
  have hV : ∀ x : tb ℓ M 1, ℓ • x = 0 := fun x => Subtype.ext (by
    have h := mem_tb.1 x.2
    rw [pow_one] at h
    simpa using h)
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI : Finite (tb ℓ M 1) := finite_tb r hcard 1
  obtain ⟨e, he⟩ := @basis_of_card ℓ _ r (tb ℓ M 1) _ (AddCommGroup.zmodModule hV) _
    (by rw [hcard 1, _root_.one_mul])
  refine ⟨fun i => (e i).1, fun i => by
    have h := mem_tb.1 (e i).2
    rwa [pow_one] at h, fun c hc i => he c (Subtype.ext ?_) i⟩
  rw [AddSubgroup.val_finsetSum]
  simpa using hc

variable {r} (e : Fin r → M) (he : ∀ i, ℓ • e i = 0)
  (hind : ∀ c : Fin r → ℤ, ∑ i, c i • e i = 0 → ∀ i, (ℓ : ℤ) ∣ c i)
  (X : Fin r → T ℓ M) (hX : ∀ i, (X i).1 1 = e i)
include hind hX

/-- Independence at level `n`. -/
theorem dvd_of_sum_eq_zero (n : ℕ) :
    ∀ c : Fin r → ℤ, ∑ i, c i • (X i).1 n = 0 → ∀ i, (ℓ : ℤ) ^ n ∣ c i := by
  induction n with
  | zero => intro c _ i; simp
  | succ n ih =>
    intro c hc
    have h1 : ∑ i, c i • e i = 0 := by
      have h := congrArg (fun z => ℓ ^ n • z) hc
      simp only [smul_zero, Finset.smul_sum] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm, show n + 1 = 1 + n by ring, pow_smul_add (X i).2 1 n, hX]
    choose d hd using fun i => hind c h1 i
    have h2 : ∑ i, d i • (X i).1 n = 0 := by
      rw [← hc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hd i, mul_comm, mul_zsmul, natCast_zsmul, (X i).2.2 n]
    intro i
    obtain ⟨k, hk⟩ := ih d h2 i
    rw [hd i, hk, pow_succ]
    exact ⟨k, by ring⟩

/-- Every `y ∈ M[ℓⁿ]` is a `ℤ`-combination of the `X i` at level `n`. -/
theorem exists_coeffs (n : ℕ) (y : M) (hy : ℓ ^ n • y = 0) :
    ∃ c : Fin r → ℤ, ∑ i, c i • (X i).1 n = y := by
  haveI := finite_tb r hcard n
  let F : (Fin r → ZMod (ℓ ^ n)) → tb ℓ M n := fun c =>
    ⟨∑ i, ((c i).val : ℤ) • (X i).1 n, mem_tb.2 (by
      rw [Finset.smul_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [smul_comm, pow_smul_eq_zero (X i).2 n, smul_zero])⟩
  have hF : Function.Injective F := by
    intro c c' h
    have h1 : ∑ i, (((c i).val : ℤ) - (c' i).val) • (X i).1 n = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.2 (congrArg Subtype.val h)
    funext i
    have h2 := dvd_of_sum_eq_zero hcard e hind X hX n _ h1 i
    have h3 : (((c' i).val : ℤ) : ZMod (ℓ ^ n)) = (((c i).val : ℤ) : ZMod (ℓ ^ n)) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact_mod_cast h2
    simpa using h3.symm
  have hbij : Function.Bijective F := hF.bijective_of_nat_card_le (by
    rw [hcard n, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin,
      ← pow_mul])
  obtain ⟨c, hc⟩ := hbij.2 ⟨y, mem_tb.2 hy⟩
  exact ⟨fun i => ((c i).val : ℤ), congrArg Subtype.val hc⟩

/-- **`T_ℓ M ≅ ℤ_ℓ^r`.** -/
theorem lc_bijective : Function.Bijective (Fintype.linearCombination ℤ_[ℓ] X) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    funext i
    rw [← PadicInt.ext_of_toZModPow]
    intro n
    have h0 : ∑ j, (((PadicInt.toZModPow n (a j)).val : ℕ) : ℤ) • (X j).1 n = 0 := by
      have := congrArg (fun x : T ℓ M => x.1 n) ha
      rw [lc_apply X] at this
      refine (Finset.sum_congr rfl fun j _ => natCast_zsmul _ _).trans ?_
      rw [this]
      rfl
    obtain ⟨k, hk⟩ := dvd_of_sum_eq_zero hcard e hind X hX n _ h0 i
    have hlt := ZMod.val_lt (PadicInt.toZModPow n (a i))
    have hk' : (PadicInt.toZModPow n (a i)).val = ℓ ^ n * k.toNat := by
      have hk0 : 0 ≤ k := by
        by_contra hneg
        have : ((ℓ : ℤ) ^ n) * k < 0 :=
          mul_neg_of_pos_of_neg (pow_pos (by exact_mod_cast hℓ.out.pos) n) (lt_of_not_ge hneg)
        omega
      have : ((PadicInt.toZModPow n (a i)).val : ℤ) = ((ℓ ^ n * k.toNat : ℕ) : ℤ) := by
        push_cast; rw [Int.toNat_of_nonneg hk0]; exact hk
      exact_mod_cast this
    have hval : (PadicInt.toZModPow n (a i)).val = 0 := by
      rcases Nat.eq_zero_or_pos k.toNat with h | h
      · rw [hk', h, mul_zero]
      · exfalso
        have : ℓ ^ n ≤ ℓ ^ n * k.toNat := Nat.le_mul_of_pos_right _ h
        omega
    rw [ZMod.val_eq_zero] at hval
    rw [hval, Pi.zero_apply, map_zero]
  · intro y
    choose c hc using fun n => exists_coeffs hcard e hind X hX n (y.1 n) (pow_smul_eq_zero y.2 n)
    have hcomp : ∀ i n, (ℓ : ℤ) ^ n ∣ c (n + 1) i - c n i := by
      intro i n
      refine dvd_of_sum_eq_zero hcard e hind X hX n (fun j => c (n + 1) j - c n j) ?_ i
      simp only [sub_smul, Finset.sum_sub_distrib, hc n]
      rw [sub_eq_zero, ← y.2.2 n, ← hc (n + 1), Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← (X j).2.2 n, smul_comm]
    let a : Fin r → ℤ_[ℓ] := fun i =>
      PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => c n i) ℓ
        (hcomp i))
    have ha : ∀ i n, PadicInt.toZModPow n (a i) = (c n i : ZMod (ℓ ^ n)) := fun i n =>
      PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => c n i) ℓ (hcomp i) n
    refine ⟨a, Subtype.ext (funext fun n => ?_)⟩
    rw [lc_apply X, ← hc n]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha, ← natCast_zsmul, ZMod.val_intCast]
    exact zsmul_emod_of (pow_smul_eq_zero (X i).2 n) (c n i)

end Main

/-- **The Tate module from the counts**: `#M[ℓⁿ] = ℓ^{nr}` for all `n` gives `T_ℓ M ≃ ℤ_ℓ^r`. -/
theorem tate_linearEquiv (r : ℕ) (hcard : ∀ n : ℕ, Nat.card (tb ℓ M n) = ℓ ^ (n * r)) :
    Nonempty (T ℓ M ≃ₗ[ℤ_[ℓ]] (Fin r → ℤ_[ℓ])) := by
  obtain ⟨e, he, hind⟩ := exists_basis r hcard
  choose X hX using fun i => exists_tate_lift r hcard (e i) (he i)
  exact ⟨(LinearEquiv.ofBijective _ (lc_bijective hcard e hind X hX)).symm⟩

end T5Torsion.TateFree

/-! ## T26 (`PkgI3.TateModuleFree`) from T5 (`PkgI2.TorsionStructure`) -/

namespace T5Torsion.TateFree

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- `torsion (toGrp A) K̄ m` is `M[m]` for `M = Additive A(K̄)`. -/
def torsionEquivTb {k : Type} [Field k] (A : PkgI3.AbVar k) (ℓ n : ℕ) [Fact ℓ.Prime] :
    PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure k) (ℓ ^ n) ≃
      tb ℓ (Additive (A.Pt (AlgebraicClosure k))) n where
  toFun x := ⟨Additive.ofMul x.1, mem_tb.2 (congrArg Additive.ofMul x.2)⟩
  invFun y := ⟨Additive.toMul y.1, congrArg Additive.toMul (mem_tb.1 y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **T26 at one field from T5 at that field.** -/
theorem tateModuleFree_at {k : Type} [Field k]
    (hT : ∀ (A : Grp (Over (Spec (.of k)))) [PkgI2.IsAbelianVariety A] (g n : ℕ),
      topologicalKrullDim A.X.left = (g : WithBot ℕ∞) → 0 < n → (n : k) ≠ 0 →
        ∃ e : PkgI2.torsion A (AlgebraicClosure k) n ≃ (Fin (2 * g) → ZMod n),
          ∀ x y : PkgI2.torsion A (AlgebraicClosure k) n,
            ∀ h : x.1 * y.1 ∈ PkgI2.torsion A (AlgebraicClosure k) n, e ⟨x.1 * y.1, h⟩ = e x + e y)
    (A : PkgI3.AbVar k) (ℓ : ℕ) [Fact ℓ.Prime] (hℓk : (ℓ : k) ≠ 0) :
    Module.Free ℤ_[ℓ] (A.T ℓ) ∧ Module.Finite ℤ_[ℓ] (A.T ℓ) ∧
      ((Module.finrank ℤ_[ℓ] (A.T ℓ) : ℕ∞) : WithBot ℕ∞) = 2 * A.dim := by
  obtain ⟨g, hg⟩ := PkgI3.AbVar.dim_finite A
  have hcard : ∀ n : ℕ, Nat.card (tb ℓ (Additive (A.Pt (AlgebraicClosure k))) n) =
      ℓ ^ (n * (2 * g)) := by
    intro n
    obtain ⟨e, -⟩ := hT (ObjBridge.toGrp A) g (ℓ ^ n) hg
      (pow_pos (Fact.out : ℓ.Prime).pos n) (by push_cast; exact pow_ne_zero _ hℓk)
    rw [← Nat.card_congr (torsionEquivTb A ℓ n), Nat.card_congr e, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]
  obtain ⟨E⟩ := tate_linearEquiv (2 * g) hcard
  refine ⟨Module.Free.of_equiv E.symm, Module.Finite.equiv E.symm, ?_⟩
  rw [E.finrank_eq, Module.finrank_fin_fun]
  rw [hg]
  norm_cast

/-- **T26 from T5**: `T_ℓ(A)` is free of rank `2 dim A` over `ℤ_ℓ` for `ℓ ≠ char k`. -/
theorem tateModuleFree_of_torsionStructure (hT : PkgI2.TorsionStructure.{0}) :
    PkgI3.TateModuleFree := fun k _ A ℓ _ hℓk => tateModuleFree_at (hT k) A ℓ hℓk

end T5Torsion.TateFree

#print axioms T5Torsion.TateFree.tate_linearEquiv
#print axioms T5Torsion.TateFree.tateModuleFree_of_torsionStructure

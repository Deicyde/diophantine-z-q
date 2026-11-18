import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Determinant.Clearing

/-!
# RankCounts: the Smith count behind the budget (5.7), in the form consumed by (5.9)

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-fixed-field-budget`, tex 5355–5387, and
Proposition `ex:limits-fixed-field-clearing`, tex 5522–5541.

**Targets.** Lane RC7's assembly of (5.9), `fixed_field_clearing`
(`ZInQKernel/Contrib/OneProof/RC/Determinant/Output.lean`), takes the
budget (5.7) as the two hypotheses

    (hm : B.mTot ≤ dK + 5) (hh : B.hSmith ≤ hK + 2 * cE + 2 * tK)

about the central Smith data `B : SmithBlocks (MonoidAlgebra O G) O` of the remaining old complex.
RC7's `fixed_field_budget` (`Determinant/BudgetLength.lean`, same commit) proves the budget for
abstract numbers from the (5.7) exact sequences, leaving as hypotheses the links `hmodel`
(`rankTotal ≤ Σ dim H^i(D_c ⊗ 𝔽₂)`), `hsmith` (`rankTotal = 2 + 2m`) and `hh₁`
(`Σ length H^i(D_c)_tors = h₁`) between the Smith data and the cohomology of `D_c`.
This file proves those links and the two targets `hm`, `hh` in RC7's exact form
(`fixedFieldBudgetSmith_proof`), from RC7's (5.7) hypotheses (copied, same names) and the free
ranks of (5.7b).

**The central Smith complex.** Elliot (tex 5522–5527): `D_c = D_0 ⊗_Λ ℤ₂` has graded
decompositions `D^i = B_i ⊕ H_i ⊕ E_i`, lifted by constant `ℤ₂` basis changes, "where centrally the
only nonzero differentials are the Smith disks `E_i → B_{i+1}`"; RC7's `SmithBlocks` records the
diagonal central entries `s i j` of these disks. In these bases `D_c` *is* the explicit complex
`SmithCx.Cx` built here: `D^i = ℤ₂^{f_i} × ℤ₂^{m_{i-1}} × ℤ₂^{m_i}` with differential
`(x, y, z) ↦ (0, diag(s_i) z, 0)`. We compute its cohomology (`SmithCx.Hequiv`:
`H^i(D_c) ≅ ℤ₂^{f_i} × ℤ₂^{m_{i-1}} / diag(s_{i-1})`), the total torsion length
(`= B.hSmith`, tex 5382–5383, 5539–5541), the free ranks (`= f_i`), and the cohomology of
`D_c ⊗ 𝔽₂` (total dimension `Σ f_i + 2 m`, tex 5357–5359, 5379–5381).

**Hypotheses and their sources.**
* `B.n ≤ 3`: the complex lives in degrees `0, …, 3` ((5.7a); RC7's (5.9) uses `2 < B.n`).
* `hpos : ∀ i j, 1 ≤ (B.s i j).valuation`: the model of `C_old` is minimal at `(2, t)`
  ("by cancelling unit entries at its maximal ideal `(2,t)`", tex 5357–5359), so its central
  entries lie in `(2)`. (`ELLIOT` remark: tex 5379–5381 count "all its Smith disks, including
  those with `e = 0`"; in this minimal model there are none, and minimality is what makes the
  total rank equal the total dimension of the reduction mod two.)
* `fm, gm, hfg, h57a, hQ`: RC7's hypotheses of `total_rank_budget` ((5.7a) and the reduced long
  exact sequence of (5.7c)), with `HD k := H^k(D_c ⊗ 𝔽₂)` of the explicit complex.
* `e, i, j, δ, l, h57d, ht₁, ht₃, hh, hJ`: RC7's hypotheses of `fixed_field_torsion_budget`
  ((5.7b), (5.7d), definitions of `t_K, h_K`, `J_r = H²(Q_r)`), with `H^k D := H^k(D_c)` of the
  explicit complex. RC7's `[Subsingleton H0D]` is not needed (it is automatic for torsion here).
* `hr₁, hr₂`: the free ranks of `H¹(C_K)` and `H²(C_K)` are one (tex 5303–5311, "They both equal
  one"). These replace RC7's `hsmith`: they force one free generator in each of degrees one and
  two (tex 5379–5380) via `H¹(D_c) ≅ H¹(C_K)` and `H²(C_K) ↪ H²(D_c)`.

`SmithBlocks`, `Lam`, `mTot`, `hSmith` are RC7's own (`Determinant/Clearing.lean`, imported), so the
target statements are in RC7's exact types.

Kinds: all theorems PROVED. The identification of `D_c` with `SmithCx.Cx` in the bases of
`SmithBlocks` is the content of RC7's `SmithBlocks` input (GLUE/ELLIOT, tex 5522–5527).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.RankCounts

open ZInQ.Manuscript.RC.Determinant (Lam SmithBlocks)

/-! ## The explicit Smith complex over a commutative ring

`f i` free generators, `d i` disks `E_i → B_{i+1}` with diagonal entries `σ i`. -/

namespace SmithCx
variable (Z : Type) [CommRing Z]
def db (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => d i
abbrev Cx (f d : ℕ → ℕ) (i : ℕ) : Type := (Fin (f i) → Z) × (Fin (db d i) → Z) × (Fin (d i) → Z)
variable {Z} {f d : ℕ → ℕ}
def dif (σ : (i : ℕ) → Fin (d i) → Z) (i : ℕ) : Cx Z f d i →ₗ[Z] Cx Z f d (i + 1) :=
  LinearMap.prod 0 (LinearMap.prod
    ((Matrix.diagonal (σ i)).mulVecLin ∘ₗ LinearMap.snd Z _ _ ∘ₗ LinearMap.snd Z _ _) 0)
@[simp] theorem dif_apply (σ : (i : ℕ) → Fin (d i) → Z) (i : ℕ) (c : Cx Z f d i) :
    dif σ i c = (0, (Matrix.diagonal (σ i)).mulVec c.2.2, 0) := rfl
def prev (σ : (i : ℕ) → Fin (d i) → Z) : (i : ℕ) → Submodule Z (Cx Z f d i)
  | 0 => ⊥
  | i + 1 => LinearMap.range (dif σ i)
abbrev H (σ : (i : ℕ) → Fin (d i) → Z) (i : ℕ) : Type :=
  ↥(LinearMap.ker (dif (f := f) σ i)) ⧸ (prev σ i).comap (LinearMap.ker (dif σ i)).subtype
theorem dif_comp (σ : (i : ℕ) → Fin (d i) → Z) (i : ℕ) :
    (dif (f := f) σ (i+1)) ∘ₗ dif σ i = 0 := by
  apply LinearMap.ext; intro c
  rw [LinearMap.comp_apply, dif_apply]
  erw [dif_apply]
  simp; rfl
/-- the range of the previous disk differential in the boundary block -/
def Rr (σ : (i : ℕ) → Fin (d i) → Z) : (i : ℕ) → Submodule Z (Fin (db d i) → Z)
  | 0 => ⊥
  | i + 1 => LinearMap.range (Matrix.diagonal (σ i)).mulVecLin
abbrev Q (σ : (i : ℕ) → Fin (d i) → Z) (i : ℕ) : Type := (Fin (db d i) → Z) ⧸ Rr σ i

variable [IsDomain Z]
theorem mem_ker_dif (σ : (i : ℕ) → Fin (d i) → Z) (hσ : ∀ i j, σ i j ≠ 0) (i : ℕ) (c : Cx Z f d i) :
    c ∈ LinearMap.ker (dif σ i) ↔ c.2.2 = 0 := by
  rw [LinearMap.mem_ker, dif_apply]
  constructor
  · intro h
    have h2 := congrArg (fun x => x.2.1) h
    simp only [Prod.snd_zero, Prod.fst_zero] at h2
    funext j
    have := congrFun h2 j
    simp [Matrix.mulVec_diagonal] at this
    simpa using (mul_eq_zero.mp this).resolve_left (hσ i j)
  · intro h; simp [h]; rfl

/-- the comparison map `ker dᵢ → Fᵢ × Qᵢ` -/
def phi (σ : (i : ℕ) → Fin (d i) → Z) (i : ℕ) :
    LinearMap.ker (dif (f := f) σ i) →ₗ[Z] (Fin (f i) → Z) × Q σ i :=
  LinearMap.prod (LinearMap.fst Z _ _ ∘ₗ (LinearMap.ker (dif σ i)).subtype)
    ((Rr σ i).mkQ ∘ₗ LinearMap.fst Z _ _ ∘ₗ LinearMap.snd Z _ _ ∘ₗ (LinearMap.ker (dif σ i)).subtype)

omit [IsDomain Z] in
theorem phi_surjective (σ : (i : ℕ) → Fin (d i) → Z) (i : ℕ) :
    Function.Surjective (phi (f := f) σ i) := by
  rintro ⟨x, q⟩
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
  refine ⟨⟨(x, y, 0), ?_⟩, ?_⟩
  · rw [LinearMap.mem_ker, dif_apply]; simp; rfl
  · rfl

theorem ker_phi (σ : (i : ℕ) → Fin (d i) → Z) (hσ : ∀ i j, σ i j ≠ 0) (i : ℕ) :
    LinearMap.ker (phi (f := f) σ i) = (prev σ i).comap (LinearMap.ker (dif σ i)).subtype := by
  ext ⟨c, hc⟩
  have hc' := (mem_ker_dif σ hσ i c).mp hc
  obtain ⟨x, y, z⟩ := c
  simp only at hc'
  subst hc'
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  change ((x, (Rr σ i).mkQ y) : (Fin (f i) → Z) × Q σ i) = 0 ↔ _
  rw [Prod.mk_eq_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  cases i with
  | zero =>
    simp only [Rr, prev, Submodule.mem_bot]
    constructor
    · rintro ⟨rfl, rfl⟩; rfl
    · intro h; simp only [Prod.mk_eq_zero] at h; exact ⟨h.1, h.2.1⟩
  | succ i =>
    simp only [Rr, prev, LinearMap.mem_range, dif_apply]
    constructor
    · rintro ⟨rfl, w, hw⟩
      exact ⟨(0, 0, w), by rw [← hw]; rfl⟩
    · rintro ⟨w, hw⟩
      have h1 := congrArg (fun c : Cx Z f d (i + 1) => c.1) hw
      have h2 := congrArg (fun c : Cx Z f d (i + 1) => c.2.1) hw
      simp only at h1 h2
      exact ⟨h1.symm, w.2.2, h2⟩

def Hequiv (σ : (i : ℕ) → Fin (d i) → Z) (hσ : ∀ i j, σ i j ≠ 0) (i : ℕ) :
    H (f := f) σ i ≃ₗ[Z] (Fin (f i) → Z) × Q σ i :=
  (Submodule.quotEquivOfEq _ _ (ker_phi σ hσ i).symm).trans
    ((phi σ i).quotKerEquivOfSurjective (phi_surjective σ i))

open Submodule in
theorem Q_isTorsion (σ : (i : ℕ) → Fin (d i) → Z) (hσ : ∀ i j, σ i j ≠ 0) (i : ℕ) :
    Module.IsTorsion Z (Q σ i) := by
  intro q
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
  cases i with
  | zero =>
    refine ⟨1, ?_⟩
    have : y = 0 := funext fun j => (show Fin 0 from j).elim0
    simp [this]
  | succ i =>
    refine ⟨⟨∏ j, σ i j, mem_nonZeroDivisors_of_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun j _ => hσ i j)⟩, ?_⟩
    change (∏ j, σ i j) • (Rr σ (i+1)).mkQ y = 0
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    let y' : Fin (d i) → Z := y
    refine ⟨fun k => (∏ j ∈ Finset.univ.erase k, σ i j) * y' k, ?_⟩
    change (Matrix.diagonal (σ i)).mulVec (fun k => (∏ j ∈ Finset.univ.erase k, σ i j) * y' k) =
      (∏ j, σ i j) • y'
    funext k
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, ← mul_assoc,
      Finset.mul_prod_erase _ _ (Finset.mem_univ k)]

theorem torsion_prod_free {k : ℕ} {M : Type} [AddCommGroup M] [Module Z M]
    (hM : Module.IsTorsion Z M) :
    Submodule.torsion Z ((Fin k → Z) × M) = LinearMap.range (LinearMap.inr Z (Fin k → Z) M) := by
  ext ⟨a, b⟩
  rw [Submodule.mem_torsion_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨r, hr⟩
    have h1 := congrArg Prod.fst hr
    simp only [Prod.smul_mk, Prod.fst_zero] at h1
    refine ⟨b, ?_⟩
    have ha : a = 0 := by
      funext j
      have := congrFun h1 j
      simp only [Pi.smul_apply, Pi.zero_apply] at this
      exact (mul_eq_zero.mp this).resolve_left (nonZeroDivisors.coe_ne_zero r)
    simp [ha]
  · rintro ⟨c, hc⟩
    simp only [LinearMap.inr_apply, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨r, hr⟩ := @hM c
    exact ⟨r, by simp [hr]⟩

omit [IsDomain Z] in
theorem length_torsion_eq_of_equiv {M N : Type} [AddCommGroup M] [Module Z M] [AddCommGroup N]
    [Module Z N] (e : M ≃ₗ[Z] N) :
    Module.length Z (Submodule.torsion Z M) = Module.length Z (Submodule.torsion Z N) := by
  have hmap : (Submodule.torsion Z M).map (e : M →ₗ[Z] N) = Submodule.torsion Z N := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_torsion_iff]
    constructor
    · rintro ⟨y, ⟨r, hr⟩, rfl⟩
      refine ⟨r, ?_⟩
      rw [Submonoid.smul_def] at hr ⊢
      rw [LinearEquiv.coe_coe, ← map_smul, hr, map_zero]
    · rintro ⟨r, hr⟩
      refine ⟨e.symm x, ⟨r, ?_⟩, by simp⟩
      rw [Submonoid.smul_def] at hr ⊢
      rw [← map_smul, hr, map_zero]
  rw [(e.submoduleMap (Submodule.torsion Z M)).length_eq, hmap]

theorem length_torsion_H (σ : (i : ℕ) → Fin (d i) → Z) (hσ : ∀ i j, σ i j ≠ 0) (i : ℕ) :
    Module.length Z (Submodule.torsion Z (H (f := f) σ i)) = Module.length Z (Q σ i) := by
  rw [length_torsion_eq_of_equiv (Hequiv σ hσ i), torsion_prod_free (Q_isTorsion σ hσ i)]
  exact (LinearEquiv.ofInjective _ (LinearMap.inr_injective)).length_eq.symm

omit [IsDomain Z] in
theorem range_diagonal_eq_pi {k : ℕ} (s : Fin k → Z) :
    LinearMap.range (Matrix.diagonal s).mulVecLin =
      Submodule.pi Set.univ (fun j => (Ideal.span {s j} : Submodule Z Z)) := by
  ext v
  simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, Submodule.mem_pi, Set.mem_univ,
    true_implies]
  constructor
  · rintro ⟨w, rfl⟩ j
    rw [Matrix.mulVec_diagonal]
    exact Ideal.mem_span_singleton'.mpr ⟨w j, mul_comm _ _⟩
  · intro h
    choose w hw using fun j => Ideal.mem_span_singleton'.mp (h j)
    refine ⟨w, funext fun j => ?_⟩
    rw [Matrix.mulVec_diagonal, mul_comm, hw j]

omit [IsDomain Z] in
theorem length_quotient_diagonal {k : ℕ} (s : Fin k → Z) :
    Module.length Z ((Fin k → Z) ⧸ LinearMap.range (Matrix.diagonal s).mulVecLin) =
      ∑ j, Ring.ord Z (s j) := by
  rw [Submodule.quotEquivOfEq _ _ (range_diagonal_eq_pi s) |>.length_eq,
    (Submodule.quotientPi _).length_eq, Module.length_pi_of_fintype]
  rfl
end SmithCx

namespace SmithCx
variable {p : ℕ} [Fact p.Prime]
theorem ord_eq_valuation {x : ℤ_[p]} (hx : x ≠ 0) : Ring.ord ℤ_[p] x = (x.valuation : ℕ∞) := by
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [Ring.ord_mul_of_isUnit_left (Units.isUnit _),
    Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero PadicInt.prime_p.ne_zero),
    Ring.ord_of_irreducible PadicInt.irreducible_p]
  simp
variable {f d : ℕ → ℕ}
theorem length_Q_zero (σ : (i : ℕ) → Fin (d i) → ℤ_[p]) : Module.length ℤ_[p] (Q σ 0) = 0 := by
  have : Subsingleton (Q σ 0) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ a
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ b
    congr 1
    funext j; exact (show Fin 0 from j).elim0
  exact Module.length_eq_zero
theorem length_Q_succ (σ : (i : ℕ) → Fin (d i) → ℤ_[p]) (hσ : ∀ i j, σ i j ≠ 0) (i : ℕ) :
    Module.length ℤ_[p] (Q σ (i + 1)) = ((∑ j, (σ i j).valuation : ℕ) : ℕ∞) := by
  have := length_quotient_diagonal (σ i)
  change Module.length ℤ_[p] ((Fin (d i) → ℤ_[p]) ⧸ LinearMap.range (Matrix.diagonal (σ i)).mulVecLin) = _
  rw [this, Nat.cast_sum]
  exact Finset.sum_congr rfl fun j _ => ord_eq_valuation (hσ i j)
end SmithCx
namespace SmithCx
variable {Z : Type} [CommRing Z] [IsDomain Z] {f d : ℕ → ℕ}
theorem rank_Q (σ : (i : ℕ) → Fin (d i) → Z) (hσ : ∀ i j, σ i j ≠ 0) (i : ℕ) :
    Module.rank Z (Q σ i) = 0 := by
  rw [rank_eq_zero_iff]
  intro x
  obtain ⟨a, ha⟩ := @Q_isTorsion Z _ d _ σ hσ i x
  exact ⟨a, nonZeroDivisors.coe_ne_zero a, ha⟩
theorem finrank_H (σ : (i : ℕ) → Fin (d i) → Z) (hσ : ∀ i j, σ i j ≠ 0) (i : ℕ) :
    Module.finrank Z (H (f := f) σ i) = f i := by
  rw [(Hequiv σ hσ i).finrank_eq, Module.finrank]
  have hker : Module.rank Z (LinearMap.ker (LinearMap.fst Z (Fin (f i) → Z) (Q σ i))) = 0 := by
    rw [rank_eq_zero_iff]
    rintro ⟨⟨a, q⟩, hx⟩
    obtain ⟨r, hr⟩ := @Q_isTorsion Z _ d _ σ hσ i q
    rw [LinearMap.mem_ker, LinearMap.fst_apply] at hx
    subst hx
    refine ⟨r, nonZeroDivisors.coe_ne_zero r, ?_⟩
    ext
    · simp
    · simpa [Submonoid.smul_def] using hr
  have h := LinearMap.rank_range_add_rank_ker (LinearMap.fst Z (Fin (f i) → Z) (Q σ i))
  rw [hker, add_zero, LinearMap.range_eq_top.mpr LinearMap.fst_surjective, rank_top,
    rank_fin_fun] at h
  rw [← h]
  simp
end SmithCx
namespace SmithCx
variable {k : Type} [Field k] {f d : ℕ → ℕ}
theorem finrank_H_of_zero (σ : (i : ℕ) → Fin (d i) → k) (h0 : ∀ i j, σ i j = 0) (i : ℕ) :
    Module.finrank k (H (f := f) σ i) = f i + db d i + d i := by
  have hσ : σ = fun _ _ => 0 := funext fun i => funext fun j => h0 i j
  subst hσ
  have hdif : ∀ i, dif (f := f) (fun (i : ℕ) (_ : Fin (d i)) => (0 : k)) i = 0 := by
    intro i; apply LinearMap.ext; intro c
    rw [dif_apply]; simp; rfl
  have hprev : prev (f := f) (fun (i : ℕ) (_ : Fin (d i)) => (0 : k)) i = ⊥ := by
    cases i with
    | zero => rfl
    | succ i => simp only [prev, hdif, LinearMap.range_zero]
  have hbot : (prev (f := f) (fun (i : ℕ) (_ : Fin (d i)) => (0 : k)) i).comap
      (LinearMap.ker (dif (fun (i : ℕ) (_ : Fin (d i)) => (0 : k)) i)).subtype = ⊥ := by
    rw [hprev, Submodule.comap_bot, Submodule.ker_subtype]
  rw [(Submodule.quotEquivOfEqBot _ hbot).finrank_eq, hdif, LinearMap.ker_zero,
    finrank_top, Module.finrank_prod, Module.finrank_prod]
  simp [add_assoc]
end SmithCx

/-! ## RC7's central Smith data and the central Smith complex -/

open SmithCx

section SmithData
variable {S O : Type*} [CommRing S] [CommRing O] [Algebra Lam O] (B : SmithBlocks S O)
/-- disk sizes, padded by zero beyond `n` -/
def dd (i : ℕ) : ℕ := if i < B.n then B.m i else 0
theorem dd_of_lt {i : ℕ} (h : i < B.n) : (dd B) i = B.m i := by simp [dd, h]
theorem dd_of_ge {i : ℕ} (h : ¬ i < B.n) : (dd B) i = 0 := by simp [dd, h]
/-- central Smith entries, padded -/
noncomputable def σ (i : ℕ) (j : Fin ((dd B) i)) : ℤ_[2] :=
  if h : i < B.n then B.s i (Fin.cast ((dd_of_lt B) h) j) else 1
theorem σ_ne (i : ℕ) (j : Fin ((dd B) i)) : (σ B) i j ≠ 0 := by
  unfold σ; split_ifs with h
  · exact B.s_ne _ _
  · exact one_ne_zero
theorem sum_dd (hn : B.n ≤ 3) : ∑ i ∈ Finset.range 3, (dd B) i = B.mTot := by
  unfold SmithBlocks.mTot
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hn) (fun i hi3 hin => ?_)]
  · exact Finset.sum_congr rfl fun i hi => (dd_of_lt B) (Finset.mem_range.mp hi)
  · exact (dd_of_ge B) (fun h => hin (Finset.mem_range.mpr h))
theorem sum_val_σ (i : ℕ) (h : i < B.n) :
    ∑ j, ((σ B) i j).valuation = ∑ j, (B.s i j).valuation := by
  refine Fintype.sum_equiv (finCongr ((dd_of_lt B) h)) _ _ (fun j => ?_)
  simp [σ, h, finCongr]
theorem sum_val_σ_ge (i : ℕ) (h : ¬ i < B.n) : ∑ j, ((σ B) i j).valuation = 0 := by
  have : IsEmpty (Fin ((dd B) i)) := by rw [(dd_of_ge B) h]; infer_instance
  simp
theorem sum_sum_val_σ (hn : B.n ≤ 3) :
    ∑ i ∈ Finset.range 3, ∑ j, ((σ B) i j).valuation = B.hSmith := by
  unfold SmithBlocks.hSmith
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hn) (fun i hi3 hin => ?_)]
  · exact Finset.sum_congr rfl fun i hi => (sum_val_σ B) i (Finset.mem_range.mp hi)
  · exact (sum_val_σ_ge B) i (fun h => hin (Finset.mem_range.mpr h))
end SmithData
section SmithData
variable {S O : Type*} [CommRing S] [CommRing O] [Algebra Lam O] (B : SmithBlocks S O)
/-- `H^i(D_c)` of the central Smith complex -/
abbrev centralH (fr : ℕ → ℕ) (i : ℕ) : Type := H (f := fr) (σ B) i
/-- `H^i(D_c ⊗ 𝔽₂)` -/
abbrev centralRed (fr : ℕ → ℕ) (i : ℕ) : Type :=
  H (f := fr) (fun i j => PadicInt.toZMod ((σ B) i j)) i

theorem toZMod_σ_eq_zero (hpos : ∀ i j, 1 ≤ (B.s i j).valuation) (i : ℕ) (j : Fin ((dd B) i)) :
    PadicInt.toZMod ((σ B) i j) = (0 : ZMod 2) := by
  by_cases h : i < B.n
  · have hv : 1 ≤ ((σ B) i j).valuation := by simp only [σ, h, dite_true]; exact hpos _ _
    have hm : (σ B) i j ∈ Ideal.span {(2 : ℤ_[2]) ^ 1} :=
      (PadicInt.mem_span_pow_iff_le_valuation _ ((σ_ne B) i j) 1).mpr hv
    rw [pow_one] at hm
    have : (σ B) i j ∈ RingHom.ker (PadicInt.toZMod (p := 2)) := by
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]; exact_mod_cast hm
    exact this
  · exact ((show Fin 0 from ((dd_of_ge B) h) ▸ j).elim0)

theorem sum_finrank_centralRed (fr : ℕ → ℕ) (hn : B.n ≤ 3)
    (hpos : ∀ i j, 1 ≤ (B.s i j).valuation) :
    ∑ k : Fin 4, Module.finrank (ZMod 2) ((centralRed B) fr k) =
      ∑ k : Fin 4, fr k + 2 * B.mTot := by
  have h := fun k : ℕ => finrank_H_of_zero (f := fr) (fun i j => PadicInt.toZMod ((σ B) i j))
    ((toZMod_σ_eq_zero B) hpos) k
  simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [h 0, h 1, h 2, show ((3 : Fin 4) : ℕ) = 3 from rfl, h 3]
  have h3 : (dd B) 3 = 0 := (dd_of_ge B) (by omega)
  have hs := (sum_dd B) hn
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hs
  simp only [db, h3]
  omega

theorem sum_length_torsion_centralH (fr : ℕ → ℕ) (hn : B.n ≤ 3) :
    ∑ k : Fin 4, Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr k)) =
      (B.hSmith : ℕ∞) := by
  have h := fun k : ℕ => length_torsion_H (f := fr) (σ B) (σ_ne B) k
  simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [h 0, h 1, h 2, show ((3 : Fin 4) : ℕ) = 3 from rfl, h 3, length_Q_zero,
    length_Q_succ (σ B) (σ_ne B) 0, length_Q_succ (σ B) (σ_ne B) 1, length_Q_succ (σ B) (σ_ne B) 2,
    ← (sum_sum_val_σ B) hn]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_add]

theorem finrank_centralH (fr : ℕ → ℕ) (i : ℕ) :
    Module.finrank ℤ_[2] ((centralH B) fr i) = fr i := finrank_H (σ B) (σ_ne B) i
end SmithData
section Budget
theorem finrank_le_of_exact' {k : Type} [Field k] {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]
    [FiniteDimensional k V₁] [FiniteDimensional k V₂] [FiniteDimensional k V₃]
    (f : V₁ →ₗ[k] V₂) (g : V₂ →ₗ[k] V₃) (H : Function.Exact f g) :
    Module.finrank k V₂ ≤ Module.finrank k V₁ + Module.finrank k V₃ := by
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  rw [H.linearMap_ker_eq] at h1
  have h2 := LinearMap.finrank_range_le f
  have h3 := Submodule.finrank_le (LinearMap.range g)
  omega

variable {R : Type} [CommRing R]

theorem length_torsion_le_of_exact {N M P : Type} [AddCommGroup N] [Module R N] [AddCommGroup M]
    [Module R M] [AddCommGroup P] [Module R P] (i : N →ₗ[R] M) (j : M →ₗ[R] P)
    (hi : Function.Injective i) (hij : Function.Exact i j) :
    Module.length R (Submodule.torsion R M) ≤
      Module.length R (Submodule.torsion R N) + Module.length R P := by
  set T := Submodule.torsion R M
  let j' : T →ₗ[R] P := j ∘ₗ T.subtype
  have hlen : Module.length R T =
      Module.length R (LinearMap.ker j') + Module.length R (LinearMap.range j') :=
    Module.length_eq_add_of_exact (LinearMap.ker j').subtype j'.rangeRestrict
      (LinearMap.ker j').subtype_injective j'.surjective_rangeRestrict
      (by rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
  rw [hlen]
  refine add_le_add ?_ (Module.length_le_of_injective (LinearMap.range j').subtype
    (LinearMap.range j').subtype_injective)
  let φ : Submodule.torsion R N →ₗ[R] LinearMap.ker j' :=
    { toFun := fun x => ⟨⟨i x, by
          obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff (x : N)).mp x.2
          exact (Submodule.mem_torsion_iff _).mpr ⟨r, by
            rw [Submonoid.smul_def] at hr ⊢; rw [← map_smul, hr, map_zero]⟩⟩, by
          show j (i x) = 0
          exact (hij (i x)).mpr ⟨x, rfl⟩⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun r x => by ext; simp }
  refine Module.length_le_of_surjective φ ?_
  rintro ⟨⟨y, hyT⟩, hy⟩
  have hjy : j y = 0 := hy
  obtain ⟨x, rfl⟩ := (hij y).mp hjy
  refine ⟨⟨x, ?_⟩, rfl⟩
  obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff _).mp hyT
  refine (Submodule.mem_torsion_iff _).mpr ⟨r, hi ?_⟩
  rw [Submonoid.smul_def] at hr ⊢
  rw [map_smul, map_zero]
  exact hr

theorem length_torsion_le_length (M : Type) [AddCommGroup M] [Module R M] :
    Module.length R (Submodule.torsion R M) ≤ Module.length R M :=
  Module.length_le_of_injective _ (Submodule.torsion R M).subtype_injective
end Budget

section SmithData
variable {S O : Type*} [CommRing S] [CommRing O] [Algebra Lam O] (B : SmithBlocks S O)

theorem budget (fr : ℕ → ℕ) (hn : B.n ≤ 3) (hpos : ∀ i j, 1 ≤ (B.s i j).valuation)
    {HC HQ : Fin 4 → Type} [∀ k, AddCommGroup (HC k)] [∀ k, Module (ZMod 2) (HC k)]
    [∀ k, AddCommGroup (HQ k)] [∀ k, Module (ZMod 2) (HQ k)]
    [∀ k, FiniteDimensional (ZMod 2) (HC k)] [∀ k, FiniteDimensional (ZMod 2) (HQ k)]
    (fm : ∀ k : Fin 4, HC k →ₗ[ZMod 2] (centralRed B) fr k)
    (gm : ∀ k : Fin 4, (centralRed B) fr k →ₗ[ZMod 2] HQ k)
    (hfg : ∀ k, Function.Exact (fm k) (gm k))
    {dK : ℕ} (h57a : ∀ k, Module.finrank (ZMod 2) (HC k) = (![2, dK, dK, 2] : Fin 4 → ℕ) k)
    (hQ : ∑ k, Module.finrank (ZMod 2) (HQ k) ≤ 8)
    {H1C H2C J H3C : Type} [AddCommGroup H1C] [Module ℤ_[2] H1C] [AddCommGroup H2C]
    [Module ℤ_[2] H2C] [AddCommGroup J] [Module ℤ_[2] J] [AddCommGroup H3C] [Module ℤ_[2] H3C]
    (e : (centralH B) fr 1 ≃ₗ[ℤ_[2]] H1C)
    (i : H2C →ₗ[ℤ_[2]] (centralH B) fr 2) (j : (centralH B) fr 2 →ₗ[ℤ_[2]] J)
    (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] (centralH B) fr 3)
    (h57d : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧
      Function.Exact δ l ∧ Function.Surjective l)
    {tK hK cE : ℕ} (ht₁ : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1C) = tK)
    (ht₃ : Module.length ℤ_[2] H3C = tK)
    (hh : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2C) = hK)
    (hJ : Module.length ℤ_[2] J ≤ 2 * cE)
    (hr₁ : Module.finrank ℤ_[2] H1C = 1) (hr₂ : Module.finrank ℤ_[2] H2C = 1) :
    B.mTot ≤ dK + 5 ∧ B.hSmith ≤ hK + 2 * cE + 2 * tK := by
  obtain ⟨hi, hij, -, -, hl⟩ := h57d
  constructor
  · have hsum := (sum_finrank_centralRed B) fr hn hpos
    have hle : ∑ k : Fin 4, Module.finrank (ZMod 2) ((centralRed B) fr k) ≤
        ∑ k : Fin 4, (Module.finrank (ZMod 2) (HC k) + Module.finrank (ZMod 2) (HQ k)) :=
      Finset.sum_le_sum fun k _ => finrank_le_of_exact' (fm k) (gm k) (hfg k)
    rw [Finset.sum_add_distrib] at hle
    have hC : ∑ k, Module.finrank (ZMod 2) (HC k) = 2 * dK + 4 := by
      simp only [Fin.sum_univ_four, h57a]; simp; ring
    have hf1 : fr 1 = 1 := by rw [← (finrank_centralH B) fr 1, e.finrank_eq, hr₁]
    have hf2 : 1 ≤ fr 2 := by
      have := LinearMap.finrank_le_finrank_of_injective hi
      rw [hr₂, (finrank_centralH B) fr 2] at this
      exact this
    have hfr : fr 1 + fr 2 ≤ ∑ k : Fin 4, fr k := by
      simp only [Fin.sum_univ_four]; simp; omega
    omega
  · have hS := (sum_length_torsion_centralH B) fr hn
    have h0 : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr 0)) = 0 := by
      rw [length_torsion_H (σ B) (σ_ne B) 0, length_Q_zero]
    have h1 : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr 1)) = tK := by
      rw [length_torsion_eq_of_equiv e, ht₁]
    have h2 : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr 2)) ≤ hK + 2 * cE :=
      (length_torsion_le_of_exact i j hi hij).trans (by rw [hh]; exact add_le_add le_rfl hJ)
    have h3 : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr 3)) ≤ tK :=
      (length_torsion_le_length _).trans ((Module.length_le_of_surjective l hl).trans ht₃.le)
    simp only [Fin.sum_univ_four] at hS
    have : (B.hSmith : ℕ∞) ≤ (hK + 2 * cE + 2 * tK : ℕ) := by
      rw [← hS]
      calc _ ≤ (0 : ℕ∞) + tK + (hK + 2 * cE) + tK := by
              gcongr
              · exact h0.le
              · exact h1.le
              · exact h2
              · exact h3
        _ = ((hK + 2 * cE + 2 * tK : ℕ) : ℕ∞) := by push_cast; ring
    exact_mod_cast this
end SmithData

/-! ## The nodes -/

open SmithCx

/-- **Tex 5357–5359, 5379–5381 (PROVED): total dimension of `H^*(D_c ⊗ 𝔽₂)`.** For RC7's central
Smith data `B` with disks in degrees `< 3` and all central Smith entries in `(2)` (minimal model),
and `f_i` free generators, the cohomology of the reduction modulo two of the central Smith complex
has total dimension `Σ_{k<4} f_k + 2·B.mTot`. With `f = (0,1,1,0)` this is RC7's `hmodel` (with
equality) and `hsmith : rankTotal = 2 + 2 * m` for `m = B.mTot`. -/
def SmithReducedTotalDim : Prop :=
  ∀ (S O : Type) [CommRing S] [CommRing O] [Algebra Lam O] (B : SmithBlocks S O) (fr : ℕ → ℕ),
    B.n ≤ 3 → (∀ i j, 1 ≤ (B.s i j).valuation) →
    ∑ k : Fin 4, Module.finrank (ZMod 2) ((centralRed B) fr k) = ∑ k : Fin 4, fr k + 2 * B.mTot

theorem smithReducedTotalDim_proof : SmithReducedTotalDim :=
  fun _ _ _ _ _ B fr hn hpos => (sum_finrank_centralRed B) fr hn hpos

/-- **Tex 5382–5383, 5539–5541 (PROVED): total torsion length of `H^*(D_c)`.** The torsion
lengths of the cohomology of the central Smith complex add up to `B.hSmith`, the sum of the
valuations of all central Smith entries. This is RC7's `hh₁` (with `h₁ = B.hSmith`). -/
def SmithTorsionLength : Prop :=
  ∀ (S O : Type) [CommRing S] [CommRing O] [Algebra Lam O] (B : SmithBlocks S O) (fr : ℕ → ℕ),
    B.n ≤ 3 →
    ∑ k : Fin 4, Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr k)) =
      (B.hSmith : ℕ∞)

theorem smithTorsionLength_proof : SmithTorsionLength :=
  fun _ _ _ _ _ B fr hn => (sum_length_torsion_centralH B) fr hn

/-- **Tex 5375–5381 (PROVED): free ranks.** `H^i(D_c)` of the central Smith complex has rank
`f_i` (its free cohomology generators). -/
def SmithFreeRank : Prop :=
  ∀ (S O : Type) [CommRing S] [CommRing O] [Algebra Lam O] (B : SmithBlocks S O) (fr : ℕ → ℕ)
    (i : ℕ), Module.finrank ℤ_[2] ((centralH B) fr i) = fr i

theorem smithFreeRank_proof : SmithFreeRank :=
  fun _ _ _ _ _ B fr i => (finrank_centralH B) fr i

/-- **The budget (5.7) in the form consumed by (5.9) (tex 5355–5387; PROVED).** For RC7's
central Smith data `B` (disks in degrees `< 3`, central entries in `(2)`) and `f_i` free
generators, with `HD k = H^k(D_c ⊗ 𝔽₂)` and `H^k D = H^k(D_c)` the cohomology of the central Smith
complex, RC7's (5.7) hypotheses `hfg, h57a, hQ, e, h57d, ht₁, ht₃, hh, hJ` and the free ranks
`hr₁, hr₂` of (5.7b) give exactly RC7's

    (hm : B.mTot ≤ dK + 5) (hh : B.hSmith ≤ hK + 2 * cE + 2 * tK)

of `fixed_field_clearing` (`Determinant/Output.lean`). -/
def FixedFieldBudgetSmith : Prop :=
  ∀ (S O : Type) [CommRing S] [CommRing O] [Algebra Lam O] (B : SmithBlocks S O) (fr : ℕ → ℕ),
    B.n ≤ 3 → (∀ i j, 1 ≤ (B.s i j).valuation) →
    ∀ (HC HQ : Fin 4 → Type) [∀ k, AddCommGroup (HC k)] [∀ k, Module (ZMod 2) (HC k)]
      [∀ k, AddCommGroup (HQ k)] [∀ k, Module (ZMod 2) (HQ k)]
      [∀ k, FiniteDimensional (ZMod 2) (HC k)] [∀ k, FiniteDimensional (ZMod 2) (HQ k)]
      (fm : ∀ k : Fin 4, HC k →ₗ[ZMod 2] (centralRed B) fr k)
      (gm : ∀ k : Fin 4, (centralRed B) fr k →ₗ[ZMod 2] HQ k),
      (∀ k, Function.Exact (fm k) (gm k)) →
    ∀ (dK : ℕ), (∀ k, Module.finrank (ZMod 2) (HC k) = (![2, dK, dK, 2] : Fin 4 → ℕ) k) →
      ∑ k, Module.finrank (ZMod 2) (HQ k) ≤ 8 →
    ∀ (H1C H2C J H3C : Type) [AddCommGroup H1C] [Module ℤ_[2] H1C] [AddCommGroup H2C]
      [Module ℤ_[2] H2C] [AddCommGroup J] [Module ℤ_[2] J] [AddCommGroup H3C] [Module ℤ_[2] H3C]
      (_e : (centralH B) fr 1 ≃ₗ[ℤ_[2]] H1C)
      (i : H2C →ₗ[ℤ_[2]] (centralH B) fr 2) (j : (centralH B) fr 2 →ₗ[ℤ_[2]] J)
      (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] (centralH B) fr 3),
      (Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧
        Function.Exact δ l ∧ Function.Surjective l) →
    ∀ (tK hK cE : ℕ), Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1C) = tK →
      Module.length ℤ_[2] H3C = tK →
      Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2C) = hK →
      Module.length ℤ_[2] J ≤ 2 * cE →
      Module.finrank ℤ_[2] H1C = 1 → Module.finrank ℤ_[2] H2C = 1 →
    B.mTot ≤ dK + 5 ∧ B.hSmith ≤ hK + 2 * cE + 2 * tK

theorem fixedFieldBudgetSmith_proof : FixedFieldBudgetSmith := by
  intro S O _ _ _ B fr hn hpos HC HQ _ _ _ _ _ _ fm gm hfg dK h57a hQ H1C H2C J H3C _ _ _ _ _ _ _ _
    e i j δ l h57d tK hK cE ht₁ ht₃ hh hJ hr₁ hr₂
  exact (budget B) fr hn hpos fm gm hfg h57a hQ e i j δ l h57d ht₁ ht₃ hh hJ hr₁ hr₂

/-! ## The inputs of RC7's `budget_57`

RC7's `budget_57` (`ZInQKernel/Contrib/OneProof/RC/Determinant/Budget.lean`) proves `B.mTot ≤ dK + 5 ∧ B.hSmith ≤ hK + 2 * cE + 2 * tK` from, among others, the
"RankCounts" inputs (their Lean text, with `HD n`, `H0D … H3D` the cohomology of `D_c ⊗ 𝔽₂` and
`D_c`):

    (hmodel : rankTotal ≤ ∑ n, Module.finrank k (HD n))
    (hsmith : rankTotal = 2 + 2 * B.mTot)
    [Subsingleton H0D]
    (htors : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H0D) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1D) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2D) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H3D) =
      ∑ i ∈ range B.n, Module.length ℤ_[2] ((Fin (B.m i) → ℤ_[2]) ⧸
        LinearMap.range (Matrix.diagonal (B.s i)).mulVecLin))

`RC7Budget57Inputs` proves them for the central Smith complex, with `k = 𝔽₂`,
`HD n = (centralRed B) fr n`, `H^n D = (centralH B) fr n`, `rankTotal = 2 + 2 * B.mTot` and the free
generators `fr = (0, 1, 1, 0)` of tex 5379–5380. -/

/-- The cokernel of the central Smith block `diag(s_i)` has length `∑_j v₂(s_ij)`; summed over the
blocks this is `B.hSmith` (tex 5375–5383). PROVED. -/
theorem sum_length_coker {S O : Type*} [CommRing S] [CommRing O] [Algebra Lam O]
    (B : SmithBlocks S O) :
    ∑ i ∈ Finset.range B.n, Module.length ℤ_[2] ((Fin (B.m i) → ℤ_[2]) ⧸
      LinearMap.range (Matrix.diagonal (B.s i)).mulVecLin) = (B.hSmith : ℕ∞) := by
  rw [SmithBlocks.hSmith, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [length_quotient_diagonal, Nat.cast_sum]
  exact Finset.sum_congr rfl fun j _ => ord_eq_valuation (B.s_ne i j)

/-- `H⁰(D_c) = 0` when there is no free generator in degree zero (tex 5285–5287, 5379–5380).
PROVED. -/
theorem subsingleton_centralH_zero {S O : Type*} [CommRing S] [CommRing O]
    [Algebra Lam O] (B : SmithBlocks S O) (fr : ℕ → ℕ) (h0 : fr 0 = 0) :
    Subsingleton ((centralH B) fr 0) := by
  have e := Hequiv (f := fr) (σ B) (σ_ne B) 0
  have : Subsingleton ((Fin (fr 0) → ℤ_[2]) × Q (σ B) 0) := by
    have h1 : Subsingleton (Fin (fr 0) → ℤ_[2]) := by
      rw [h0]; infer_instance
    have h2 : Subsingleton (Q (σ B) 0) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ a
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ b
      congr 1
      funext j; exact (show Fin 0 from j).elim0
    infer_instance
  exact e.toEquiv.subsingleton

/-- **RC7's `budget_57` RankCounts inputs, PROVED for the central Smith complex** (tex 5357–5359,
5375–5383). For RC7's central Smith data `B` (disks in degrees `< 3`, central entries in `(2)`) and
free generators `fr = (0, 1, 1, 0)` (one in each of degrees one and two, tex 5379–5380):
`hmodel` and `hsmith` with `rankTotal = 2 + 2 * B.mTot` and `HD n = H^n(D_c ⊗ 𝔽₂)`;
`[Subsingleton H0D]`; and `htors`, all in RC7's Lean text (`Determinant/Budget.lean`). -/
def RC7Budget57Inputs : Prop :=
  ∀ (S O : Type) [CommRing S] [CommRing O] [Algebra Lam O] (B : SmithBlocks S O) (fr : ℕ → ℕ),
    B.n ≤ 3 → (∀ i j, 1 ≤ (B.s i j).valuation) →
    fr 0 = 0 → fr 1 = 1 → fr 2 = 1 → fr 3 = 0 →
    let rankTotal := 2 + 2 * B.mTot
    (rankTotal ≤ ∑ n : Fin 4, Module.finrank (ZMod 2) ((centralRed B) fr n)) ∧
    (rankTotal = 2 + 2 * B.mTot) ∧
    Subsingleton ((centralH B) fr 0) ∧
    (Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr 0)) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr 1)) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr 2)) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr 3)) =
      ∑ i ∈ Finset.range B.n, Module.length ℤ_[2] ((Fin (B.m i) → ℤ_[2]) ⧸
        LinearMap.range (Matrix.diagonal (B.s i)).mulVecLin))

theorem rc7Budget57Inputs_proof : RC7Budget57Inputs := by
  intro S O _ _ _ B fr hn hpos h0 h1 h2 h3 rankTotal
  refine ⟨?_, rfl, (subsingleton_centralH_zero B) fr h0, ?_⟩
  · rw [(sum_finrank_centralRed B) fr hn hpos]
    simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two,
      show ((3 : Fin 4) : ℕ) = 3 from rfl, h0, h1, h2, h3, rankTotal]
    omega
  · have hS := (sum_length_torsion_centralH B) fr hn
    simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two] at hS
    exact hS.trans (sum_length_coker B).symm

end ZInQ.Contrib.CloudB3RC53.RankCounts

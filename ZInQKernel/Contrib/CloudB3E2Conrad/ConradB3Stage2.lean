import ZInQKernel.Contrib.OneProof.ConradB3Verbatim

/-!
# Conrad's Proposition B.3 at local base `ℚ_p`, from the identity weight

Manuscript `diophantine_zq.tex`, sec:height, L760–764 (step C8); B. Conrad, Appendix B,
pp. 32–33.

`ConradB3Print` asks: if the character `ψ : G_{ℚ_p} → K^×` (`K/ℚ_p` finite Galois) satisfies
Conrad's near-one display with exponent `n`, then the underlying `ℚ_p`-representation is
Hodge–Tate with the single weight `n` (`PureHT p ψ n`). This file derives it from the identity
weight `ConradIdentityWeight` (the near-one display gives the identity coefficient line
`ℂ_p(n)` over `G_K`), using only Tate's theorems on `ℂ_p(i)^{G_K}` (proved in the tree):

* `ysp_eq_bot_of_identityLine` (PROVED): for `m ≠ n`, `Y_m(ψ) = 0` over `G_K` — a vector of
  `Y_m` divided by the identity-line vector is fixed by `G_K` in `ℂ_p(m − n)`, hence zero (Tate);
* `htSpace_finrank_eq_zero_of_identityLine` (PROVED): hence `H_m(ψ) = 0` for `m ≠ n`, through the
  bridge `finrank_htSpace_eq_Ysp`;
* `hasHTWeights_of_identityLine` (PROVED): with `conradHTMult_of_identityLine`
  (`dim_{ℚ_p} H_n(ψ) = [K : ℚ_p]`), `ψ` has the single Hodge–Tate weight `−n` in the tree's
  convention;
* **`conradB3Print_of_identityWeight`** (PROVED): `ConradIdentityWeight → ConradB3Print`, through
  `artinNearOnePrint_iff` and `pureHT_of_hasHTWeights`.

No base change `ℂ_p ⊗ K ≅ ℂ_p^{Gal(K/ℚ_p)}` and no separate descent statement is needed: the
descent from `G_K` to `G_{ℚ_p}` is the tree's bridge `finrank_htSpace_eq_Ysp`.

Kinds: PROVED.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Bridges.CloudB3E2

open Module
open _root_.ZInQ.Contrib.HodgeSplit
namespace G9P
export _root_.ZInQ.Contrib.G9.PkgI4 (cycPow cpAct cpAct_coe)
end G9P
open _root_.ZInQ.Contrib.CloudB3W11 (axSenTate_proof tateTwistInvariants_proof)

variable (p : ℕ) [Fact p.Prime]

/-- `χ(σ)^{a+b} = χ(σ)^a χ(σ)^b` (PROVED). -/
theorem cycPow_add (σ : PkgI4.GQp p) (a b : ℤ) :
    G9P.cycPow p σ (a + b) = G9P.cycPow p σ a * G9P.cycPow p σ b := by
  simp only [G9P.cycPow, zpow_add, Units.val_mul]
  push_cast
  rfl

/-- `χ(σ)^a ≠ 0` (PROVED). -/
theorem cycPow_ne_zero (σ : PkgI4.GQp p) (a : ℤ) : G9P.cycPow p σ a ≠ 0 := by
  have h : G9P.cycPow p σ a * G9P.cycPow p σ (-a) = 1 := by
    rw [← cycPow_add, add_neg_cancel]
    simp [G9P.cycPow]
  exact left_ne_zero_of_mul_eq_one h

section Char

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- `G_K` fixes `K` inside `ℂ_p` (PROVED). -/
theorem cpAct_algebraMap_of_mem (σ : PkgI4.GQp p) (hσ : σ ∈ K.fixingSubgroup) (k : K) :
    G9P.cpAct p σ (algebraMap K ℂ_[p] k) = algebraMap K ℂ_[p] k := by
  rw [IsScalarTower.algebraMap_apply K (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
    G9P.cpAct_coe]
  exact congrArg (fun x : PadicAlgCl p => (x : ℂ_[p])) (hσ k)

/-- The defining relation of `Y_m(ψ)` for a character, on the single coordinate (PROVED). -/
theorem ysp_charRep_iff (ψ : PkgI4.GQp p →* Kˣ) (m : ℤ) (y : Fin 1 → ℂ_[p]) :
    y ∈ Ysp p (charRep ψ) m K ↔ ∀ σ ∈ K.fixingSubgroup,
      algebraMap K ℂ_[p] (ψ σ : K) * y 0 = G9P.cycPow p σ m • G9P.cpAct p σ (y 0) := by
  constructor
  · intro h σ hσ
    have := congrFun (h σ hσ) 0
    simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, matC, vAct,
      charRep, Matrix.algebraMap_matrix_apply] using this
  · intro h σ hσ
    ext j
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, matC, vAct,
      charRep, Matrix.algebraMap_matrix_apply] using h σ hσ

/-- **For `m ≠ n`, `Y_m(ψ) = 0` over `G_K` once the identity line `ℂ_p(n)` exists** (PROVED;
Tate's theorem `ℂ_p(i)^{G_K} = 0` for `i ≠ 0`). -/
theorem ysp_eq_bot_of_identityLine [FiniteDimensional ℚ_[p] K] (ψ : PkgI4.GQp p →* Kˣ)
    {n m : ℤ} (hnm : m ≠ n) (h : IdentityLine p K ψ n) : Ysp p (charRep ψ) m K = ⊥ := by
  obtain ⟨c, hc, he⟩ := h
  rw [eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot]
  have hy' := (ysp_charRep_iff p ψ m y).mp hy
  have hce : ∀ σ ∈ K.fixingSubgroup,
      algebraMap K ℂ_[p] (ψ σ : K) * c = G9P.cycPow p σ n • G9P.cpAct p σ c := by
    intro σ hσ
    have hr : σ ∈ (restrictGalois p K).range := (range_restrictGalois p K).symm ▸ hσ
    obtain ⟨g, rfl⟩ := hr
    exact he g
  have hx : y 0 * c⁻¹ = 0 := by
    apply tateTwistInvariants_proof p K (m - n) (sub_ne_zero.mpr hnm)
    intro σ hσ
    have h1 := hy' σ hσ
    have h2 := hce σ hσ
    have hψ : algebraMap K ℂ_[p] (ψ σ : K) ≠ 0 := by
      rw [ne_eq, map_eq_zero]
      exact Units.ne_zero _
    have hσc : G9P.cpAct p σ c ≠ 0 := by
      intro h0
      rw [h0, smul_zero] at h2
      exact hc ((mul_eq_zero.mp h2).resolve_left hψ)
    have hn0 := cycPow_ne_zero p σ n
    have hm := cycPow_add p σ (m - n) n
    rw [sub_add_cancel] at hm
    rw [map_mul, map_inv₀]
    simp only [Algebra.smul_def] at h1 h2 ⊢
    rw [hm, map_mul] at h1
    set a := algebraMap K ℂ_[p] (ψ σ : K)
    set χk := algebraMap ℚ_[p] ℂ_[p] (G9P.cycPow p σ (m - n))
    set χn := algebraMap ℚ_[p] ℂ_[p] (G9P.cycPow p σ n)
    set sy := G9P.cpAct p σ (y 0)
    set sc := G9P.cpAct p σ c
    have hq : χn ≠ 0 := by
      simp only [χn, ne_eq, map_eq_zero]; exact hn0
    have key0 : a * (χn * (y 0 * sc)) = a * (χn * (χk * sy * c)) := by
      linear_combination (sc * χn) * h1 - (χk * sy * χn) * h2
    have key : y 0 * sc = χk * sy * c :=
      mul_left_cancel₀ hq (mul_left_cancel₀ hψ key0)
    field_simp
    linear_combination -key
  ext j
  have hj : j = 0 := Subsingleton.elim j 0
  subst hj
  simpa [hc] using hx

/-- **For `m ≠ n`, `H_m(ψ) = 0`** (PROVED; the descent from `G_K` is the tree's bridge
`finrank_htSpace_eq_Ysp`). -/
theorem htSpace_finrank_eq_zero_of_identityLine [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : PkgI4.GQp p →* Kˣ) {n m : ℤ} (hnm : m ≠ n) (h : IdentityLine p K ψ n) :
    finrank ℚ_[p] (PkgI4.htSpace p (charRep ψ) m) = 0 := by
  rw [show PkgI4.htSpace p (charRep ψ) m =
      _root_.ZInQ.Contrib.G9.PkgI4.htSpace p (charRep ψ) m from rfl,
    finrank_htSpace_eq_Ysp p K tateTwistInvariants_proof axSenTate_proof,
    ysp_eq_bot_of_identityLine p ψ hnm h]
  exact finrank_bot ℚ_[p] _

/-- **The single Hodge–Tate weight** (PROVED): the identity line `ℂ_p(n)` gives
`HasHTWeights {−n}` in the tree's convention (the cyclotomic character has weight `−1`). -/
theorem hasHTWeights_of_identityLine [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : PkgI4.GQp p →* Kˣ) {n : ℤ} (h : IdentityLine p K ψ n) :
    PkgI4.HasHTWeights p (charRep ψ) {-n} := by
  intro w
  have hd : 0 < finrank ℚ_[p] K := finrank_pos_intermediateField p K
  by_cases hw : w = -n
  · subst hw
    rw [Multiset.count_singleton_self]
    change finrank ℚ_[p] (PkgI4.htSpace p (charRep ψ) (-(-n))) / finrank ℚ_[p] K = 1
    rw [neg_neg]
    have he := conradHTMult_of_identityLine p K ψ n h
    change finrank ℚ_[p] (PkgI4.htSpace p (charRep ψ) n) = _ at he
    rw [he, Nat.div_self hd]
  · rw [Multiset.count_singleton, ite_eq_right_iff.mpr (fun h => absurd h hw)]
    change finrank ℚ_[p] (PkgI4.htSpace p (charRep ψ) (-w)) / finrank ℚ_[p] K = 0
    rw [htSpace_finrank_eq_zero_of_identityLine p ψ (m := -w) (by omega) h, Nat.zero_div]

end Char

/-- **`ConradB3Print` from the identity weight** (PROVED): the near-one display gives the
identity line (`ConradIdentityWeight`, through `artinNearOnePrint_iff`), hence the single weight,
hence the constant-weight splitting `PureHT p ψ n` (`pureHT_of_hasHTWeights`). -/
theorem conradB3Print_of_identityWeight (h : ConradIdentityWeight) : ConradB3Print := by
  intro p _ K _ _ ψ n hc hA
  have hl : IdentityLine p K ψ n := h p K ψ n hc ((artinNearOnePrint_iff p ψ hc n).mp hA)
  simpa only [neg_neg] using pureHT_of_hasHTWeights p ψ (-n) (hasHTWeights_of_identityLine p ψ hl)

end HDec.G0Galois.C8Conrad.Bridges.CloudB3E2

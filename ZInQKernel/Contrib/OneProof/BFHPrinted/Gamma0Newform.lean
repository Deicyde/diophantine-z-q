import TauCeti.NumberTheory.ModularForms.AtkinLehner.Sign
import TauCeti.NumberTheory.ModularForms.Newforms.Basic
import TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Gamma0
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Action

/-!
# Classical newforms on `Γ₀(N)`, and Tau Ceti's `Γ₁(N)`-newforms of trivial nebentypus

Task bfh-gamma0 (report `docs/research/bfh-gamma0.md`). The vendored Tau Ceti library has newforms
on `Γ₁(N)` (`HeckeRing.GL2.Newform N k`: a Hecke eigenform away from the level, in the
`Γ₁(N)`-new subspace `TauCeti.cuspFormsNew N k`, normalised by `a₁ = 1`) and the identification
`S_k(Γ₁(N), 1) ≃ S_k(Γ₀(N))` (`TauCeti.cuspFormCharSpaceOneEquiv`, re-reading the same function),
through which a newform `f` with `f.χ = 1` becomes the cusp form `f.toCuspFormGamma0 hχ` on
`Γ₀(N)`. It has no new subspace of `S_k(Γ₀(N))`. This file defines the classical objects and
proves that `f.toCuspFormGamma0 hχ` is a classical newform on `Γ₀(N)`.

## Definitions (all over Tau Ceti / Mathlib objects)

* `IsGamma0New F`: `F ∈ S_k(Γ₀(N))` is Petersson-orthogonal to `V_d g` for every
  `g ∈ S_k(Γ₀(M))` and every pair `(M, d)` with `d M ∣ N`, `M ≠ N` (Atkin–Lehner's new subspace
  of `S_k(Γ₀(N))`, the Petersson complement of the old subspace spanned by the `V_d S_k(Γ₀(M))`).
  This is Tau Ceti's `cuspFormsNew` (`mem_cuspFormsNew_iff`) with `Γ₁` replaced by `Γ₀` at both
  levels.
* `heckeGamma0 N k`: the action of the `Γ₀(N)` Hecke ring `𝕋(Δ₀(N), Γ₀(N))` on `S_k(Γ₀(N))`, the
  `ℤ`-linear extension of Tau Ceti's untwisted double-coset operators
  `HeckeRing.GL2.heckeSlashGamma0CuspFormEnd`.
* `IsGamma0Newform F`: `F` is an eigenvector of `heckeGamma0 N k (heckeTCompositeGamma0 N n)` (the
  operator `T_n`, Tau Ceti's) for every `n ≥ 1` prime to `N`, lies in the new subspace
  (`IsGamma0New`), and is normalised by `a₁(F) = 1`: the classical newform (primitive form) on
  `Γ₀(N)` (Atkin–Lehner 1970; Miyake, *Modular forms*, §4.6; Diamond–Shurman §5.8; UNVERIFIED
  section numbers). The eigen condition is the one Tau Ceti's `Newform` carries.

## Results

* `isGamma0New_toCuspFormGamma0`: a `Γ₁(N)`-newform of trivial nebentypus is `Γ₀(N)`-new. Proof:
  the restriction `S_k(Γ₀(·)) → S_k(Γ₁(·))` commutes with `V_d` (`restrict_levelRaise_gamma0`),
  restricts `f.toCuspFormGamma0 hχ` to `f` (`Newform.restrict_toCuspFormGamma0`) and multiplies
  the Petersson product by the nonzero index `[Γ₀(N)·{±1} : Γ₁(N)·{±1}]`
  (`CuspForm.peterssonInnerCosets_restrict_restrict`); `f` is orthogonal to `V_d (g|Γ₁(M))`
  (`TauCeti.mem_cuspFormsNew_iff`).
* `coe_heckeGamma0`: on underlying functions, `heckeGamma0 N k T F` is Tau Ceti's nebentypus action
  `heckeRingHomCuspCharSpace k 1 T` on the restriction of `F` to `Γ₁(N)` (at the trivial character
  the twisted slash sum is the untwisted one, `twistedHeckeSlashSum_eq_heckeSlashSum`).
* `isGamma0Newform_toCuspFormGamma0`: `f.toCuspFormGamma0 hχ` is a classical newform on `Γ₀(N)`.
* `coeffGamma0_toCuspFormGamma0`: its Fourier coefficients are those of `f`.
* The converse: `restrict_mem_cuspFormsNew_of_isGamma0New` (a `Γ₀(N)`-new form restricts to a
  `Γ₁(N)`-new form: an old form of trivial nebentypus is the restriction of some `G₀` on `Γ₀(N)`,
  and the trace `Γ₁(N) → Γ₀(N)` carries the `Γ₁(N)`-old subspace into the `Γ₀(N)`-old subspace,
  `cuspFormsOld_le_comap_trace`), whence `IsGamma0Newform.toNewform`, the Tau Ceti newform of
  trivial nebentypus with the same function (`IsGamma0Newform.toCuspFormGamma0_toNewform`).
-/

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 HeckeRing.GLn
open scoped MatrixGroups ModularForm HeckeCosetModule

namespace ZInQ.BFHPrinted

open TauCeti

variable {N : ℕ} {k : ℤ}

/-! ## The new subspace of `S_k(Γ₀(N))` -/

/-- **`F` lies in the new subspace of `S_k(Γ₀(N))`** (Atkin–Lehner): `F` is Petersson-orthogonal
to `V_d g`, `(V_d g)(τ) = g(dτ)`, for every cusp form `g` on `Γ₀(M)` and every pair `(M, d)` with
`d M ∣ N` and `M ≠ N`, i.e. to the old subspace of `S_k(Γ₀(N))`. The Petersson product is Tau
Ceti's `CuspForm.peterssonInnerCosets` at level `Γ₀(N)`. -/
def IsGamma0New [NeZero N] (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) : Prop :=
  ∀ (M d : ℕ) (h : d * M ∣ N), M ≠ N →
    ∀ g : CuspForm ((Gamma0 M).map (mapGL ℝ)) k,
      haveI : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h)
      CuspForm.peterssonInnerCosets
        (TauCeti.CuspForm.levelRaise d (Gamma0_map_le_conjAct_scaleGL_of_dvd h) g) F = 0

/-- Restriction from `Γ₀` to `Γ₁` commutes with the level-raising operator `V_d`. -/
theorem restrict_levelRaise_gamma0 {M d : ℕ} [NeZero d] (h : d * M ∣ N)
    (g : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) :
    CuspForm.restrict (Gamma1_map_le_Gamma0_map N)
        (TauCeti.CuspForm.levelRaise d (Gamma0_map_le_conjAct_scaleGL_of_dvd h) g) =
      TauCeti.CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h)
        (CuspForm.restrict (Gamma1_map_le_Gamma0_map M) g) :=
  CuspForm.ext fun τ ↦ by simp [CuspForm.coe_restrict]

/-- The index `[Γ₀(N)·{±1} : Γ₁(N)·{±1}]` is nonzero. -/
theorem relIndex_gamma1_gamma0_ne_zero [NeZero N] :
    ((Gamma1 N).withCenter.relIndex (Gamma0 N).withCenter : ℂ) ≠ 0 := by
  have : (Gamma1 N).withCenter.FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1 N).le_withCenter
  have h1 : (Gamma1 N).withCenter.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  intro h0
  apply h1
  rw [← Subgroup.relIndex_top_right]
  exact Subgroup.relIndex_eq_zero_of_le_right le_top (by exact_mod_cast h0)

/-- **A `Γ₁(N)`-newform of trivial nebentypus is `Γ₀(N)`-new.** -/
theorem isGamma0New_toCuspFormGamma0 [NeZero N] (f : Newform N k) (hχ : f.χ = 1) :
    IsGamma0New (f.toCuspFormGamma0 hχ) := by
  intro M d h hM g
  have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h)
  have hnew := (mem_cuspFormsNew_iff.mp f.isNew) M d h hM
    (CuspForm.restrict (Gamma1_map_le_Gamma0_map M) g)
  have key := CuspForm.peterssonInnerCosets_restrict_restrict (Γ := Gamma0 N) (Γ' := Gamma1 N)
    (Gamma1_map_le_Gamma0_map N)
    (TauCeti.CuspForm.levelRaise d (Gamma0_map_le_conjAct_scaleGL_of_dvd h) g)
    (f.toCuspFormGamma0 hχ)
  rw [restrict_levelRaise_gamma0 h, Newform.restrict_toCuspFormGamma0, hnew] at key
  exact (mul_eq_zero.mp key.symm).resolve_left relIndex_gamma1_gamma0_ne_zero

/-! ## Hecke operators on `S_k(Γ₀(N))` -/

variable (N k) in
/-- **The Hecke ring of `Γ₀(N)` acting on `S_k(Γ₀(N))`**: the `ℤ`-linear extension of Tau Ceti's
double-coset operators `heckeSlashGamma0CuspFormEnd k D` (no character) to formal
`ℤ`-combinations of double cosets `Γ₀(N) δ Γ₀(N)`, `δ ∈ Δ₀(N)`. -/
noncomputable def heckeGamma0 [NeZero N] :
    𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ →ₗ[ℤ]
      Module.End ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  Finsupp.linearCombination ℤ fun D ↦ heckeSlashGamma0CuspFormEnd k D

/-- The value of `heckeGamma0` on a basis element. -/
theorem heckeGamma0_single [NeZero N]
    (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))) (c : ℤ) :
    heckeGamma0 N k (HeckeCosetModule.single ℤ D c) = c • heckeSlashGamma0CuspFormEnd k D :=
  (Finsupp.linearCombination_apply (R := ℤ)
    (v := fun D ↦ heckeSlashGamma0CuspFormEnd k D) _).trans
    (HeckeCosetModule.sum_single_index ℤ (zero_smul _ _))

/-- **`heckeGamma0` is Tau Ceti's trivial-nebentypus Hecke action, read on `Γ₀(N)`**: on
underlying functions, `heckeGamma0 N k T F = heckeRingHomCuspCharSpace k 1 T (F|Γ₁(N))`. -/
theorem coe_heckeGamma0 [NeZero N] (T : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ)
    (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ⇑(heckeGamma0 N k T F) =
      ⇑((heckeRingHomCuspCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) T
        ⟨CuspForm.restrict (Gamma1_map_le_Gamma0_map N) F,
          restrict_mem_cuspFormCharSpace_one F⟩ :
          cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  induction T using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd S T hS hT =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, FunLike.coe_add, hS, hT]
    rfl
  | hsingle D c =>
    rw [heckeRingHomCuspCharSpace_apply, twistedHeckeSlashCuspFormCharLinearMap_single,
      heckeGamma0_single]
    simp [CuspForm.coe_restrict]

/-! ## Classical newforms on `Γ₀(N)` -/

/-- The `n`-th Fourier coefficient at `∞` of a cusp form on `Γ₀(N)` (Mathlib's `qExpansion`,
width `1`). -/
noncomputable def coeffGamma0 (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (n : ℕ) : ℂ :=
  (qExpansion 1 F).coeff n

/-- **`F` is a newform on `Γ₀(N)`** in the classical sense (Atkin–Lehner; Miyake's primitive
form): an eigenvector of every Hecke operator `T_n`, `n ≥ 1` prime to `N` (Tau Ceti's
`heckeTCompositeGamma0 N n`, acting on `S_k(Γ₀(N))` by `heckeGamma0`), in the new subspace of
`S_k(Γ₀(N))` (`IsGamma0New`), normalised by `a₁(F) = 1`. -/
structure IsGamma0Newform [NeZero N] (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) : Prop where
  /-- `F` is an eigenform of `T_n` for every `n ≥ 1` prime to the level. -/
  isEigen : ∀ n : ℕ, 0 < n → n.Coprime N →
    ∃ c : ℂ, heckeGamma0 N k (heckeTCompositeGamma0 N n) F = c • F
  /-- `F` lies in the new subspace of `S_k(Γ₀(N))`. -/
  isNew : IsGamma0New F
  /-- `F` is normalised: `a₁(F) = 1`. -/
  isNorm : coeffGamma0 F 1 = 1

/-- The Fourier coefficients of `f.toCuspFormGamma0 hχ` are those of `f`. -/
theorem coeffGamma0_toCuspFormGamma0 [NeZero N] (f : Newform N k) (hχ : f.χ = 1) (n : ℕ) :
    coeffGamma0 (f.toCuspFormGamma0 hχ) n = (qExpansion 1 f.toCuspForm).coeff n := by
  rw [coeffGamma0, Newform.coe_toCuspFormGamma0]

/-- The eigenvalue equations of a newform, read at the trivial character. -/
private theorem heckeRingHom_one_eq_smul [NeZero N] (f : Newform N k) (hχ : f.χ = 1)
    (n : ℕ) (hn0 : 0 < n) (hn : Nat.Coprime n N) :
    ((heckeRingHomCuspCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) (heckeTCompositeGamma0 N n)
      ⟨f.toCuspForm, hχ ▸ f.mem_charSpace⟩ : cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = f.eigenvalue ⟨n, hn0⟩ hn • f.toCuspForm := by
  have key : ∀ (χ : (ZMod N)ˣ →* ℂˣ) (hχ : χ = 1) (hm : f.toCuspForm ∈ cuspFormCharSpace k χ)
      (c : ℂ), heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N n) ⟨f.toCuspForm, hm⟩ =
        c • (⟨f.toCuspForm, hm⟩ : cuspFormCharSpace k χ) →
      ((heckeRingHomCuspCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) (heckeTCompositeGamma0 N n)
        ⟨f.toCuspForm, hχ ▸ hm⟩ : cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
          CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = c • f.toCuspForm := by
    intro χ hχ hm c h
    subst hχ
    exact congrArg Subtype.val h
  exact key f.χ hχ f.mem_charSpace _ (f.isEigen ⟨n, hn0⟩ hn)

/-- **A `Γ₁(N)`-newform of trivial nebentypus is a classical newform on `Γ₀(N)`.** -/
theorem isGamma0Newform_toCuspFormGamma0 [NeZero N] (f : Newform N k) (hχ : f.χ = 1) :
    IsGamma0Newform (f.toCuspFormGamma0 hχ) where
  isEigen n hn0 hn := by
    refine ⟨f.eigenvalue (⟨n, hn0⟩ : ℕ+) hn, DFunLike.coe_injective ?_⟩
    rw [coe_heckeGamma0]
    have hres : (⟨CuspForm.restrict (Gamma1_map_le_Gamma0_map N) (f.toCuspFormGamma0 hχ),
        restrict_mem_cuspFormCharSpace_one _⟩ : cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) =
        ⟨f.toCuspForm, hχ ▸ f.mem_charSpace⟩ :=
      Subtype.ext (Newform.restrict_toCuspFormGamma0 f hχ)
    rw [hres, heckeRingHom_one_eq_smul f hχ n hn0 hn, FunLike.coe_smul, FunLike.coe_smul,
      Newform.coe_toCuspFormGamma0]
  isNew := isGamma0New_toCuspFormGamma0 f hχ
  isNorm := by rw [coeffGamma0_toCuspFormGamma0]; exact f.isNorm

/-! ## The converse: a classical newform on `Γ₀(N)` is a Tau Ceti newform of trivial nebentypus -/

variable (N k) in
/-- **The old subspace of `S_k(Γ₀(N))`**: the span of the `V_d S_k(Γ₀(M))`, `d M ∣ N`, `M ≠ N`
(Tau Ceti's `cuspFormsOld` with `Γ₁` replaced by `Γ₀`). -/
noncomputable def cuspFormsOldGamma0 [NeZero N] :
    Submodule ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  ⨆ (M : ℕ) (d : ℕ) (h : d * M ∣ N ∧ M ≠ N),
    have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h.1)
    LinearMap.range
      (TauCeti.CuspForm.levelRaiseₗ (k := k) d (Gamma0_map_le_conjAct_scaleGL_of_dvd h.1))

theorem levelRaise_mem_cuspFormsOldGamma0 [NeZero N] {M d : ℕ} (h : d * M ∣ N) (hM : M ≠ N)
    (g : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) :
    haveI : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h)
    TauCeti.CuspForm.levelRaise d (Gamma0_map_le_conjAct_scaleGL_of_dvd h) g ∈
      cuspFormsOldGamma0 N k :=
  let _ := NeZero.of_dvd (dvd_of_mul_right_dvd h)
  Submodule.mem_iSup_of_mem M (Submodule.mem_iSup_of_mem d
    (Submodule.mem_iSup_of_mem ⟨h, hM⟩ ⟨g, TauCeti.CuspForm.levelRaiseₗ_apply d _ g⟩))

/-- `IsGamma0New F` is membership in the Petersson complement of the old subspace. -/
theorem isGamma0New_iff [NeZero N] {F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k} :
    IsGamma0New F ↔ F ∈ CuspForm.peterssonOrthogonal (cuspFormsOldGamma0 N k) := by
  constructor
  · intro hF
    rw [CuspForm.mem_peterssonOrthogonal_iff_le_ker]
    refine iSup_le fun M ↦ iSup_le fun d ↦ iSup_le fun h ↦ ?_
    have := NeZero.of_dvd (dvd_of_mul_right_dvd h.1)
    rintro _ ⟨g, rfl⟩
    rw [TauCeti.CuspForm.levelRaiseₗ_apply, LinearMap.mem_ker,
      CuspForm.peterssonInnerCosetsₛₗ_apply_apply, ← CuspForm.peterssonInnerCosets_conj_symm,
      hF M d h.1 h.2 g, map_zero]
  · intro hF M d h hM g
    exact CuspForm.mem_peterssonOrthogonal_iff.mp hF _ (levelRaise_mem_cuspFormsOldGamma0 h hM g)

/-- The trace from `Γ₁(N)` to `Γ₀(N)` maps the old subspace of `S_k(Γ₁(N))` into the old
subspace of `S_k(Γ₀(N))`: the trace of `V_d g` is `V_d g₀`, where `g₀ ∈ S_k(Γ₀(M))` restricts to
the diamond sum `∑ᵤ ⟨u mod M⟩ g` (`cuspFormTraceGamma0_levelRaise`), which has trivial
nebentypus (`sum_diamondOpCusp_mem_cuspFormCharSpace_one`). -/
theorem cuspFormsOld_le_comap_trace [NeZero N] :
    cuspFormsOld N k ≤ (cuspFormsOldGamma0 N k).comap (cuspFormTraceGamma0 N k) := by
  refine cuspFormsOld_le fun M d hdvd hM g ↦ ?_
  have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd hdvd)
  have hMN : M ∣ N := dvd_of_mul_left_dvd hdvd
  have : NeZero M := NeZero.of_dvd hMN
  have hS := sum_diamondOpCusp_mem_cuspFormCharSpace_one (N := N) (ZMod.unitsMap_surjective hMN) g
  rw [cuspFormCharSpace_one_eq_range] at hS
  obtain ⟨g₀, hg₀⟩ := hS
  rw [Submodule.mem_comap, cuspFormTraceGamma0_levelRaise hMN hdvd g g₀ hg₀]
  exact levelRaise_mem_cuspFormsOldGamma0 hdvd hM g₀

/-- **A `Γ₀(N)`-new form restricts to a `Γ₁(N)`-new form.** An old form `G` of trivial
nebentypus is the restriction of some `G₀ ∈ S_k(Γ₀(N))`; its trace `#(ℤ/N)ˣ · G₀` is
`Γ₀(N)`-old (`cuspFormsOld_le_comap_trace`), so `G₀` is, and
`⟪G, F|Γ₁⟫ = [Γ₀(N)·{±1} : Γ₁(N)·{±1}] ⟪G₀, F⟫ = 0`. Newness at the trivial nebentypus is tested
against the old forms of trivial nebentypus (`mem_cuspFormsNew_iff_of_mem_cuspFormCharSpace`). -/
theorem restrict_mem_cuspFormsNew_of_isGamma0New [NeZero N]
    {F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k} (hF : IsGamma0New F) :
    CuspForm.restrict (Gamma1_map_le_Gamma0_map N) F ∈ cuspFormsNew N k := by
  rw [mem_cuspFormsNew_iff_of_mem_cuspFormCharSpace (restrict_mem_cuspFormCharSpace_one F),
    CuspForm.mem_peterssonOrthogonal_iff]
  rintro G ⟨hGold, hGchar⟩
  rw [cuspFormCharSpace_one_eq_range] at hGchar
  obtain ⟨G₀, rfl⟩ := hGchar
  have htr := cuspFormsOld_le_comap_trace hGold
  rw [Submodule.mem_comap, CuspForm.restrictₗ_apply, cuspFormTraceGamma0_restrict] at htr
  have hcard : (Fintype.card (ZMod N)ˣ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hG₀ : G₀ ∈ cuspFormsOldGamma0 N k := by
    have := Submodule.smul_mem _ (Fintype.card (ZMod N)ˣ : ℂ)⁻¹ htr
    rwa [smul_smul, inv_mul_cancel₀ hcard, one_smul] at this
  rw [CuspForm.restrictₗ_apply, CuspForm.peterssonInnerCosets_restrict_restrict,
    CuspForm.mem_peterssonOrthogonal_iff.mp (isGamma0New_iff.mp hF) G₀ hG₀, mul_zero]

/-- **A classical newform on `Γ₀(N)`, as a Tau Ceti newform on `Γ₁(N)` of trivial nebentypus**:
its restriction to `Γ₁(N)`. -/
noncomputable def IsGamma0Newform.toNewform [NeZero N] {F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k}
    (hF : IsGamma0Newform F) : Newform N k where
  toCuspForm := CuspForm.restrict (Gamma1_map_le_Gamma0_map N) F
  χ := 1
  mem_charSpace := restrict_mem_cuspFormCharSpace_one F
  eigenvalue n hn := (hF.isEigen n.val n.pos hn).choose
  isEigen n hn := by
    apply Subtype.ext
    apply DFunLike.coe_injective
    have hc := (hF.isEigen n.val n.pos hn).choose_spec
    generalize (hF.isEigen n.val n.pos hn).choose = c at hc ⊢
    rw [← coe_heckeGamma0, hc]
    simp [CuspForm.coe_restrict]
  ne_zero h0 := by
    have hF0 : ⇑F = 0 := by
      simpa [CuspForm.coe_restrict] using congrArg DFunLike.coe h0
    have h1 := hF.isNorm
    rw [coeffGamma0, hF0, qExpansion_zero] at h1
    simp at h1
  isNew := restrict_mem_cuspFormsNew_of_isGamma0New hF.isNew
  isNorm := by simpa [coeffGamma0, CuspForm.coe_restrict] using hF.isNorm

@[simp] theorem IsGamma0Newform.toNewform_χ [NeZero N] {F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k}
    (hF : IsGamma0Newform F) : hF.toNewform.χ = 1 := rfl

/-- Converting back recovers `F`. -/
theorem IsGamma0Newform.toCuspFormGamma0_toNewform [NeZero N]
    {F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k} (hF : IsGamma0Newform F) :
    hF.toNewform.toCuspFormGamma0 hF.toNewform_χ = F :=
  DFunLike.coe_injective (by
    rw [Newform.coe_toCuspFormGamma0]
    exact CuspForm.coe_restrict (Gamma1_map_le_Gamma0_map N) F)

end ZInQ.BFHPrinted

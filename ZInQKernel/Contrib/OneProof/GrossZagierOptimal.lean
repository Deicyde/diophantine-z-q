import ZInQKernel.Contrib.OneProof.GrossZagierModuli
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_isUniformization_toPoint
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_discriminant_ne_zero

/-!
# gz-optimal: the Gross–Zagier leaf for the strong Weil (optimal) parametrization only

Task gz-optimal (2026-11-16). Report: `docs/research/gz-optimal.md`; scratch and log: `scratch/gz-optimal/`.

gz-moduli's leaf `GZModuli.GrossZagierModuliCd` states the Gross–Zagier formula (positive constant
forgotten) for every modular parametrization `φ : X₀(N) → C_d`. Gross–Zagier Ch. V may print it
only for the strong Weil curve with its strong Weil parametrization. This file states the formula
for that case only (`GrossZagierModuliOptAt`: `φ` optimal, i.e. `φ_*` onto `H₁(E(ℂ), ℤ)`, i.e.
`J₀(N) → E` with connected kernel; `IsOptimalParam`), which is printed under either reading, and
proves the consumer `GZHL3.GrossZagierFormulaCd` (every analytic parametrization
`weierPt C_d L (c φ_f)`, `c ∈ ℚ^×`, `c Λ_f ⊆ L`) from it:

* route A (`grossZagierFormulaCd_of_selfOptimal`): with `CdOptimal` (GLUE, a period computation:
  `L(C_d) = c₀ Λ_f`, checked numerically for 13 values of `d`), every admissible `φ` is `[n] ∘ φ_opt`;
* route B (`grossZagierFormulaCd_of_transfer`): with `StrongWeilOptimalCd` (the strong Weil curve
  `E'` with `L(E') = c' Λ_f`) and `AnalyticIsogenyRational` (the isogeny `z ↦ μ z`, `μ ∈ ℚ`, is defined
  over `ℚ`), both textbook and composite, `φ = ψ ∘ φ'`; the formula transfers along `ψ̂ : C_d → E'`
  because `y` and `ψ̂(y)` are torsion together.

Also proved: the new leaf follows from gz-moduli's (`grossZagierModuliOptCd_of_moduli`), so it is
weaker; gz-moduli's all-`φ` leaf follows from it given `ModularParamAnalyticCd` (every modular
parametrization is analytic; composite; not needed by the consumer). Glue proved here: additivity of
`weierPt` for models `y² = x³ + a₄x + a₆` (from the vendored uniformization theorem), torsion of a
`K`-point read off from its complex parameter, rational multipliers of lattices, finite index.

No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane HeckeRing.GL2 WeierstrassCurve ZInQ.GZDecomp Filter Topology
open ZInQ.Contrib.TYZGenus.CM (HeegnerForm)
open scoped WeierstrassCurve.Affine MatrixGroups

namespace ZInQ.GZOptimal

/-! ## §1. Additivity of `weierPt` for curves `y² = x³ + a₄x + a₆` -/

/-- `E` is given by an equation `y² = x³ + a₄x + a₆` (`a₁ = a₂ = a₃ = 0`). -/
def IsShortModel (E : WeierstrassCurve ℚ) : Prop := E.a₁ = 0 ∧ E.a₂ = 0 ∧ E.a₃ = 0

theorem short_cd (d : ℕ) : IsShortModel (shortCurve (-(d : ℚ) ^ 2)) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [shortCurve]

theorem fun_add_of_eq (L : PeriodPair) {W : WeierstrassCurve ℂ} (h : L.weierstrassCurve = W)
    (F : ℂ → W.toAffine.Point) (hF0 : ∀ z ∈ L.lattice, F z = 0)
    (hF1 : ∀ z ∉ L.lattice, ∃ hns, F z = .some (L.weierstrassP z) (L.derivWeierstrassP z / 2) hns)
    (z w : ℂ) : F (z + w) = F z + F w := by
  subst h
  have hD := L.discriminant_ne_zero
  have hF : F = L.toPoint hD := by
    funext u
    by_cases hu : u ∈ L.lattice
    · rw [hF0 u hu, L.toPoint_of_mem hD hu]
    · obtain ⟨hns, e⟩ := hF1 u hu
      rw [e, L.toPoint_of_notMem hD hu]
  rw [hF]
  exact (L.isUniformization_toPoint hD).1 z w

section Short

variable {E : WeierstrassCurve ℚ} (hE : IsShortModel E)
include hE

theorem bc_a₁ : (E⁄ℂ).a₁ = 0 := by simp [hE.1]
theorem bc_a₂ : (E⁄ℂ).a₂ = 0 := by simp [hE.2.1]
theorem bc_a₃ : (E⁄ℂ).a₃ = 0 := by simp [hE.2.2]
theorem bc_b₂ : (E⁄ℂ).b₂ = 0 := by
  rw [WeierstrassCurve.b₂, bc_a₁ hE, bc_a₂ hE]; ring

/-- For a period lattice of a short model `E`, the curve of `L` is `E⁄ℂ`. -/
theorem weierstrassCurve_eq {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice E L) :
    L.weierstrassCurve = E⁄ℂ := by
  obtain ⟨h2, h3⟩ := hL
  have a1 := bc_a₁ hE; have a2 := bc_a₂ hE; have a3 := bc_a₃ hE
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, a1, a2, a3] at h2 h3
  ext
  · rw [PeriodPair.weierstrassCurve_a₁, a1]
  · rw [PeriodPair.weierstrassCurve_a₂, a2]
  · rw [PeriodPair.weierstrassCurve_a₃, a3]
  · rw [PeriodPair.weierstrassCurve_a₄, h2]; ring
  · rw [PeriodPair.weierstrassCurve_a₆, h3]; ring

/-- **`weierPt E L` is additive** for a short model `E` (the uniformization theorem, vendored). -/
theorem weierPt_add' [E.IsElliptic] {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice E L)
    (z w : ℂ) :
    ZInQ.GZHL3.weierPt E L (z + w) = ZInQ.GZHL3.weierPt E L z + ZInQ.GZHL3.weierPt E L w := by
  refine fun_add_of_eq L (weierstrassCurve_eq hE hL) _ (fun u hu => ?_) (fun u hu => ?_) z w
  · exact ZInQ.GZHeegner.weierPt_eq_zero _ L hu
  · rw [ZInQ.GZHeegner.weierPt_eq_some _ hL hu]
    have hns := ZInQ.GZHL3.weierPt_some E hL hu
    simp only [bc_b₂ hE, bc_a₁ hE, bc_a₃ hE, zero_div, sub_zero, zero_mul] at hns ⊢
    exact ⟨hns, trivial⟩

/-- `weierPt E L` as an additive map `ℂ →+ E(ℂ)`. -/
def weierHom [E.IsElliptic] {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice E L) :
    ℂ →+ (E⁄ℂ).toAffine.Point :=
  AddMonoidHom.mk' (ZInQ.GZHL3.weierPt E L) (weierPt_add' hE hL)

theorem weierHom_apply [E.IsElliptic] {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice E L)
    (z : ℂ) : weierHom hE hL z = ZInQ.GZHL3.weierPt E L z := rfl

theorem weierPt_sum [E.IsElliptic] {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice E L)
    {ι : Type*} (s : Finset ι) (g : ι → ℂ) :
    ∑ i ∈ s, ZInQ.GZHL3.weierPt E L (g i) = ZInQ.GZHL3.weierPt E L (∑ i ∈ s, g i) := by
  simp only [← weierHom_apply hE hL, map_sum]

theorem weierPt_zsmul [E.IsElliptic] {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice E L)
    (n : ℤ) (z : ℂ) :
    n • ZInQ.GZHL3.weierPt E L z = ZInQ.GZHL3.weierPt E L ((n : ℂ) * z) := by
  rw [← weierHom_apply hE hL, ← weierHom_apply hE hL, ← map_zsmul, zsmul_eq_mul]

end Short

/-- `weierPt E L z = O` exactly for `z ∈ L`. -/
theorem weierPt_eq_zero_iff (E : WeierstrassCurve ℚ) [E.IsElliptic] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice E L) (z : ℂ) :
    ZInQ.GZHL3.weierPt E L z = 0 ↔ z ∈ L.lattice := by
  refine ⟨fun h => ?_, ZInQ.GZHeegner.weierPt_eq_zero E L⟩
  by_contra hz
  rw [ZInQ.GZHeegner.weierPt_eq_some E hL hz] at h
  exact Affine.Point.some_ne_zero _ h

/-- **Torsion of a `K`-point read off from its complex parameter**: if `ι(P) = weierPt E L w`,
then `P` is torsion iff `k w ∈ L` for some `k ≥ 1`. -/
theorem isOfFinAddOrder_iff {E : WeierstrassCurve ℚ} [E.IsElliptic] (hE : IsShortModel E)
    {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice E L) {K : Type*} [Field K] [Algebra ℚ K]
    [DecidableEq K] (ι : K →ₐ[ℚ] ℂ) (P : (E⁄K).Point) {w : ℂ}
    (hP : Affine.Point.map ι P = ZInQ.GZHL3.weierPt E L w) :
    IsOfFinAddOrder P ↔ ∃ k : ℕ, 0 < k ∧ (k : ℂ) * w ∈ L.lattice := by
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  refine exists_congr fun k => and_congr_right fun _ => ?_
  rw [← (Affine.Point.map_injective (W' := E) (f := ι)).eq_iff, map_nsmul, map_zero, hP,
    ← natCast_zsmul, weierPt_zsmul hE hL, weierPt_eq_zero_iff E hL]
  push_cast; rfl

/-! ## §2. Lattice lemmas -/

/-- Real relations between the periods of a `PeriodPair` are trivial. -/
theorem real_rel {L : PeriodPair} {a b : ℝ} (h : (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ = 0) :
    a = 0 ∧ b = 0 := by
  have h' : a • L.ω₁ + b • L.ω₂ = 0 := by simpa [Complex.real_smul] using h
  exact LinearIndependent.pair_iff.1 L.indep _ _ h'

/-- Integer relations between the periods of a `PeriodPair` are trivial. -/
theorem int_rel {L : PeriodPair} {a b : ℤ} (h : (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ = 0) :
    a = 0 ∧ b = 0 := by
  obtain ⟨ha, hb⟩ := real_rel (L := L) (a := a) (b := b) (by exact_mod_cast h)
  exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩

theorem ω₁_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  intro h
  have := int_rel (L := L) (a := 1) (b := 0) (by simp [h])
  exact one_ne_zero this.1

/-- **A rational multiplier of a lattice is an integer**: `q ω₁ ∈ L` with `q ∈ ℚ` forces `q ∈ ℤ`. -/
theorem rat_mem_int {L : PeriodPair} {q : ℚ} (h : (q : ℂ) * L.ω₁ ∈ L.lattice) :
    ∃ n : ℤ, q = n := by
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 h
  have h1 := (real_rel (L := L) (a := (a : ℝ) - q) (b := b) (by push_cast; linear_combination hab)).1
  exact ⟨a, by exact_mod_cast (sub_eq_zero.1 h1).symm⟩

/-- **Finite index**: if `m L' ⊆ L` (`m ≠ 0`) for lattices `L, L'`, then `M L ⊆ m L'` for some
integer `M ≠ 0` (the determinant of the inclusion). -/
theorem exists_int_mul_mem (L L' : PeriodPair) {m : ℂ} (hm : m ≠ 0)
    (h : ∀ z ∈ L'.lattice, m * z ∈ L.lattice) :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ z ∈ L.lattice, ∃ w ∈ L'.lattice, (M : ℂ) * z = m * w := by
  obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.1 (h _ L'.ω₁_mem_lattice)
  obtain ⟨r, s, hrs⟩ := PeriodPair.mem_lattice.1 (h _ L'.ω₂_mem_lattice)
  refine ⟨p * s - q * r, fun hD => ?_, fun z hz => ?_⟩
  · have hD' : ((p : ℂ) * s - q * r) = 0 := by exact_mod_cast hD
    have e1 : m * ((s : ℂ) * L'.ω₁ + ((-q : ℤ) : ℂ) * L'.ω₂) = 0 := by
      push_cast; linear_combination (s : ℂ) * hpq.symm - (q : ℂ) * hrs.symm + L.ω₁ * hD'
    have e2 : m * (((-r : ℤ) : ℂ) * L'.ω₁ + (p : ℂ) * L'.ω₂) = 0 := by
      push_cast; linear_combination -(r : ℂ) * hpq.symm + (p : ℂ) * hrs.symm + L.ω₂ * hD'
    obtain ⟨hs, hq⟩ := int_rel ((mul_eq_zero.1 e1).resolve_left hm)
    obtain ⟨hr, hp⟩ := int_rel ((mul_eq_zero.1 e2).resolve_left hm)
    have hq' : q = 0 := by simpa using hq
    subst hs hq' hp
    have : m * L'.ω₁ = 0 := by rw [← hpq]; simp
    exact ω₁_ne_zero L' ((mul_eq_zero.1 this).resolve_left hm)
  · obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.1 hz
    refine ⟨(a * s - b * r : ℤ) * L'.ω₁ + (b * p - a * q : ℤ) * L'.ω₂,
      PeriodPair.mem_lattice.2 ⟨_, _, rfl⟩, ?_⟩
    push_cast
    linear_combination ((a : ℂ) * s - b * r) * hpq + ((b : ℂ) * p - a * q) * hrs

/-! ## §3. The optimal parametrization and the statements -/

/-- **`Λ_f`, the period lattice of `2πi f(τ) dτ` on `X₀(N)`**: the subgroup of `ℂ` generated by the
periods `φ_f(γτ) − φ_f(τ) = 2πi ∫_τ^{γτ} f(z) dz`, `γ ∈ Γ₀(N)`, `τ ∈ ℍ` (`φ_f` the Eichler integral).
These are the integrals of `2πi f dτ` over the closed paths of `Y₀(N)` from `τ` to `γτ`; they give
`∫_γ 2πi f dτ` for every class `γ ∈ H₁(X₀(N), ℤ)` (Shimura 1971, §7.5; Diamond–Shurman §6.6;
UNVERIFIED locators). -/
def periodLattice {N : ℕ} [NeZero N] (f : Newform N 2) : Submodule ℤ ℂ :=
  Submodule.span ℤ {w | ∃ γ ∈ CongruenceSubgroup.Gamma0 N, ∃ τ : ℍ,
    w = ZInQ.GZHL3.eichler f (γ • τ) - ZInQ.GZHL3.eichler f τ}

/-- **`φ = (X, Y) : X₀(N) → E` is the strong Weil (optimal) parametrization.** The lift of `φ` to
`ℍ → ℂ ⊃ L` is `c φ_f`, `c ∈ ℚ` (i.e. `φ^*ω = c · 2πi f(τ) dτ` for the invariant differential
`ω = dx/(2y + a₁x + a₃)` of the model, whose period lattice is `L`), and `L = c Λ_f`.

`L = c Λ_f` says that `φ_* : H₁(X₀(N), ℤ) → H₁(E(ℂ), ℤ) = L` (`γ ↦ ∫_γ φ^*ω`) is surjective. For the
homomorphism `J₀(N) → E` induced by `φ` (Albanese), the cokernel of `H₁(J₀(N), ℤ) → H₁(E, ℤ)` is the
group of components of its kernel, so this is equivalent to **`J₀(N) → E` having connected kernel**,
equivalently (dually) to `E → J₀(N)` being injective: the definition of the strong Weil
parametrization (optimal quotient) of the strong Weil curve `E` (Mazur–Swinnerton-Dyer 1974, §1;
Stevens 1989, §1; Cremona 1997, §2.14; Gross–Zagier 1986, Ch. V; all UNVERIFIED). "Minimal degree"
is not stated: Mathlib has no degree of a map of curves, and for a fixed non-optimal `E` the
minimal-degree `φ` is not optimal. -/
def IsOptimalParam (N : ℕ) [NeZero N] (f : Newform N 2) (E : WeierstrassCurve ℚ) (X Y : ℍ → ℂ) :
    Prop :=
  ∃ (L : PeriodPair) (c : ℚ), ZInQ.GZHL3.IsPeriodLattice E L ∧
    L.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c : ℂ)) ∧
    ∀ τ : ℍ, ZInQ.GZModuli.modPt E X Y τ = ZInQ.GZHL3.weierPt E L (c * ZInQ.GZHL3.eichler f τ)

/-- **The Gross–Zagier formula for the strong Weil parametrization (moduli form, positive constant
forgotten; Gross–Zagier 1986, Thm I.6.3 and Ch. V Thm 2.1).** As `GZModuli.GrossZagierModuliAt E`
(gz-moduli), with two changes:

* `φ = (X, Y)` is moreover the **strong Weil (optimal) parametrization** (`IsOptimalParam`), so
  `E` is the strong Weil curve of `f`. Under either reading of Gross–Zagier Ch. V (formula stated for
  every modular parametrization, or only for the strong Weil curve with its strong parametrization)
  this case is printed.
* `y ∈ E(K)` satisfies `ι(y) = n · y_K` for an integer `n ≠ 0`, where `y_K = Σ_x φ(x)` is the sum
  over a complete set of Heegner points `x = (𝒪_K, 𝔫, [𝔞])`, `𝔫 = (N, (−β + √D)/2)`
  (`IsHeegnerPointReps`; for `σ ∈ Gal(H/K)` the `x^σ` run over them, so `y_K = Tr_{H/K} φ(x)`).
  Gross–Zagier state that `y_K ∈ E(K)` and give `L'(E/K, 1)` as a positive multiple of `ĥ(y_K)`;
  `y = n y_K` and `ĥ(n y_K) = n² ĥ(y_K)` give the statement for `y` (`n = 1` is gz-moduli's form).

Then `L'(E/K, 1) = (F G)'(1) = κ · ĥ(y)` for some real `κ > 0`, with `F`, `G` the entire
continuations of `L(f, s) = L(E, s)` and `L(f ⊗ χ_D, s)`.

Source: B. Gross, D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84
(1986), 225–320, Thm I.6.3 and Ch. V Thm 2.1 with `φ^*ω = c · 2πi f(τ) dτ`; locators, the constant
`‖ω‖²/(c² u² √|D|)` and the exact hypotheses on `φ` UNVERIFIED (no copy on this host). Weaker than
the print: the constant is replaced by `∃ κ > 0`; folded in: `L(E/K, s) = L(f, s) L(f ⊗ χ_D, s)`. -/
def GrossZagierModuliOptAt (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ X Y : ℍ → ℂ, ZInQ.GZModuli.IsModularParam N E X Y → IsOptimalParam N f E X Y →
    ∀ D β : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D → (4 * N : ℤ) ∣ D - β ^ 2 →
    ∀ (R : Type) [Fintype R] (τ : R → ℍ), ZInQ.GZModuli.IsHeegnerPointReps N D β τ →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K], Module.finrank ℚ K = 2 →
    ∀ δ : K, δ ^ 2 = (D : K) →
    ∀ ι : K →ₐ[ℚ] ℂ, ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) →
    ∀ n : ℤ, n ≠ 0 →
    ∀ y : (E⁄K).Point, Affine.Point.map ι y = n • ∑ r, ZInQ.GZModuli.modPt E X Y (τ r) →
    ∀ F G : ℂ → ℂ, IsEntireCont (coeff f) 2 F → IsEntireCont (twistCoeff f D) 2 G →
      ∃ κ : ℝ, 0 < κ ∧ deriv (fun s => F s * G s) 1 = κ * y.canonicalHeight

/-- `GrossZagierModuliOptAt` for every elliptic curve over `ℚ`. -/
def GrossZagierModuliOpt : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], GrossZagierModuliOptAt E

/-- **The leaf of the `C_d` route**: `GrossZagierModuliOptAt E'` for every short model `E'` in the
isogeny class of `C_d : y² = x³ − d²x` (`aₙ(E') = aₙ(C_d)`), `d ≡ 5 (mod 8)` squarefree. A
restriction of `GrossZagierModuliOpt`. -/
def GrossZagierModuliOptCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d →
    ∀ (E' : WeierstrassCurve ℚ) [E'.IsElliptic], IsShortModel E' →
      (∀ n : ℕ, n ≠ 0 → E'.LFunction n = (shortCurve (-(d : ℚ) ^ 2)).LFunction n) →
      GrossZagierModuliOptAt E'

theorem grossZagierModuliOptCd_of (h : GrossZagierModuliOpt) : GrossZagierModuliOptCd :=
  fun _ _ _ E' _ _ _ => h E'

/-- **(GLUE, a period computation) `C_d` is the strong Weil curve of its isogeny class**: for the
newform `f` of `C_d` and the period lattice `L` of `C_d`, `L = c₀ Λ_f` for a rational `c₀`.

Not proved. Checked numerically (VERIFIED, computed on a sample of periods): `Λ_f = L` (`c₀ = 1`) for the
18 values `d = 5, 13, …, 165` tested (`scratch/gz-optimal/py/periods_cd.gp`), and PARI's `ellweilcurve`
gives `C_d` as the optimal curve of its class for `d = 5, 13`; for general `d` SPECULATIVE. For `d = 1`
it is false (`y² = x³ − x` is `32a2`, not optimal), so it depends on `d ≡ 5 (mod 8)`. gz-weil proved
`2 Λ_f ⊆ L`; the content is `L = c₀ Λ_f` for one `c₀`. -/
def CdOptimal : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) →
    ∀ L : PeriodPair, ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L →
      ∃ c₀ : ℚ, L.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c₀ : ℂ))

/-- **The strong Weil curve of a rational newform, with its period lattice (textbook; composite).**
For a weight-2 newform `f` of level `N`, trivial character and rational coefficients there is an
elliptic curve `E'/ℚ`, given by an equation `y² = x³ + a₄x + a₆`, with `aₙ(E') = aₙ(f)` for `n ≥ 1`,
whose period lattice is `L' = c Λ_f` for some `c ∈ ℚ`.

Content: the optimal quotient `E_f = J₀(N)/I_f J₀(N)` is an elliptic curve over `ℚ` with
`L(E_f, s) = L(f, s)` (Eichler–Shimura; Shimura 1971, Thm 7.14 and §7.5; Diamond–Shurman §6.6 and
Thm 8.8.1; UNVERIFIED); `φ : X₀(N) → E_f` is the strong Weil parametrization, so
`φ_* : H₁(X₀(N), ℤ) → H₁(E_f, ℤ)` is onto and the period lattice of `ω` is `{∫_γ φ^*ω} = c Λ_f` with
`φ^*ω = c · 2πi f dτ`; `c ∈ ℚ` since `φ` and `ω` are defined over `ℚ` and `f = q + …` (Manin 1972,
rational Manin constant; UNVERIFIED); every elliptic curve over `ℚ` has a model `y² = x³ + a₄x + a₆`
(Silverman, AEC, III.1), and `aₙ` does not depend on the model (Mathlib's `LFunction` uses the
minimal model). Composite: the print states these over `J₀(N)`; the analytic form `L' = c Λ_f` is
the period computation above. Compare gz-hl3's `GZHL3.StrongWeilCurve` (inclusion `c Λ_f ⊆ L'`,
rated composite); this is its sharpening to equality. -/
def StrongWeilOptimal : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → ∃ q : ℚ, coeff f n = q) →
    ∃ E' : WeierstrassCurve ℚ, E'.IsElliptic ∧ IsShortModel E' ∧
      (∀ n : ℕ, n ≠ 0 → coeff f n = (E'.LFunction n : ℂ)) ∧
      ∃ (L' : PeriodPair) (c : ℚ), ZInQ.GZHL3.IsPeriodLattice E' L' ∧
        L'.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c : ℂ))

/-- `StrongWeilOptimal` restricted to the newforms of the curves `C_d`. -/
def StrongWeilOptimalCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) →
    ∃ E' : WeierstrassCurve ℚ, E'.IsElliptic ∧ IsShortModel E' ∧
      (∀ n : ℕ, n ≠ 0 → coeff f n = (E'.LFunction n : ℂ)) ∧
      ∃ (L' : PeriodPair) (c : ℚ), ZInQ.GZHL3.IsPeriodLattice E' L' ∧
        L'.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c : ℂ))

theorem strongWeilOptimalCd_of (h : StrongWeilOptimal) : StrongWeilOptimalCd :=
  fun _ _ _ N _ f hχ hf => h N f hχ fun n hn => ⟨_, by rw [hf n hn]; rfl⟩

/-- **An analytic isogeny with rational multiplier is defined over `ℚ` (textbook; composite).** Let
`E, E'/ℚ` be elliptic curves with period lattices `L, L'`, and `μ ∈ ℚ^×` with `μ L ⊆ L'`. Then the
isogeny `ψ : E → E'`, `z ↦ μ z` on `ℂ/L → ℂ/L'`, maps `E(K)` into `E'(K)` for every number field
`K ⊂ ℂ`: for `P ∈ E(K)` there is `P' ∈ E'(K)` with `ι(P') = ψ(ι(P))`.

Content: `ψ` is an isogeny with `ψ^*ω' = μ ω` (Silverman, AEC, Thm VI.4.1 and Prop. VI.3.6;
UNVERIFIED numbers); for `σ ∈ Aut(ℂ)`, `ψ^σ : E → E'` is an isogeny with `(ψ^σ)^*ω' = σ(μ) ω = μ ω`,
and `ψ ↦ (ψ^*ω'/ω)` is injective on `Hom(E, E')` in characteristic `0` (AEC, Cor. III.5.3 and
Thm III.5.2), so `ψ^σ = ψ`: `ψ` is defined over `ℚ` and maps `E(K)` to `E'(K)` compatibly with `ι`.
Composite only because Mathlib has no isogenies of Weierstrass curves: the isogeny is given by its
analytic multiplier (compare gz-hl3's `GZHL3.IsogenyLattice`). -/
def AnalyticIsogenyRational : Prop :=
  ∀ (E E' : WeierstrassCurve ℚ) [E.IsElliptic] [E'.IsElliptic] (L L' : PeriodPair),
    ZInQ.GZHL3.IsPeriodLattice E L → ZInQ.GZHL3.IsPeriodLattice E' L' →
    ∀ μ : ℚ, μ ≠ 0 → (∀ z ∈ L.lattice, (μ : ℂ) * z ∈ L'.lattice) →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K] (ι : K →ₐ[ℚ] ℂ) (P : (E⁄K).Point),
      ∃ P' : (E'⁄K).Point, ∀ z : ℂ, Affine.Point.map ι P = ZInQ.GZHL3.weierPt E L z →
        Affine.Point.map ι P' = ZInQ.GZHL3.weierPt E' L' (μ * z)

/-! ## §4. Glue lemmas -/

open ZInQ.GZHeegner (ParamSetting zPar xPar yPar)

section Glue

variable {N : ℕ} [NeZero N] {f : Newform N 2}

theorem periodsIn_of_lattice {L : PeriodPair} {c : ℚ}
    (hlat : L.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c : ℂ))) :
    ZInQ.GZHL3.PeriodsIn f c L := by
  intro γ hγ τ
  rw [hlat]
  exact ⟨_, Submodule.subset_span ⟨γ, hγ, τ, rfl⟩, rfl⟩

theorem mul_mem_of_periodsIn {L : PeriodPair} {c : ℂ} (hP : ZInQ.GZHL3.PeriodsIn f c L)
    {w : ℂ} (hw : w ∈ periodLattice f) : c * w ∈ L.lattice := by
  have : periodLattice f ≤ L.lattice.comap (LinearMap.mulLeft ℤ c) := by
    rw [periodLattice, Submodule.span_le]
    rintro _ ⟨γ, hγ, τ, rfl⟩
    exact hP γ hγ τ
  exact this hw

theorem ne_zero_of_lattice {L : PeriodPair} {c : ℚ}
    (hlat : L.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c : ℂ))) : c ≠ 0 := by
  rintro rfl
  have h := L.ω₁_mem_lattice
  rw [hlat] at h
  obtain ⟨w, -, hw⟩ := h
  exact ω₁_ne_zero L (by simpa using hw.symm)

theorem periodsIn_zsmul {L : PeriodPair} {c : ℚ} (hP : ZInQ.GZHL3.PeriodsIn f c L) (n : ℤ) :
    ZInQ.GZHL3.PeriodsIn f (((n : ℚ) * c : ℚ) : ℂ) L := by
  intro γ hγ τ
  have := L.lattice.smul_mem n (hP γ hγ τ)
  rw [zsmul_eq_mul] at this
  push_cast
  rwa [mul_assoc]

end Glue

/-- **From `L'(E/K, 1) = κ' ĥ(P')` to `L'(E/K, 1) = κ ĥ(y)`** when `y` and `P'` are torsion together
(Tau Ceti: `ĥ ≥ 0`, and `ĥ = 0` exactly on torsion over a number field). -/
theorem exists_pos_of_torsion_iff {K : Type} [Field K] [NumberField K] [DecidableEq K]
    {E E' : WeierstrassCurve ℚ} [E.IsElliptic] [E'.IsElliptic] (y : (E⁄K).Point)
    (P' : (E'⁄K).Point) {A : ℂ} {κ' : ℝ} (hκ' : 0 < κ') (hA : A = κ' * P'.canonicalHeight)
    (ht : IsOfFinAddOrder y ↔ IsOfFinAddOrder P') :
    ∃ κ : ℝ, 0 < κ ∧ A = κ * y.canonicalHeight := by
  by_cases h0 : y.canonicalHeight = 0
  · have hP0 : P'.canonicalHeight = 0 :=
      (Affine.Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder P').2
        (ht.1 ((Affine.Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder y).1 h0))
    exact ⟨1, one_pos, by rw [hA, hP0, h0]; simp⟩
  · have hy : 0 < y.canonicalHeight := lt_of_le_of_ne (Affine.Point.canonicalHeight_nonneg y) (Ne.symm h0)
    have hP0 : P'.canonicalHeight ≠ 0 := fun h => h0
      ((Affine.Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder y).2
        (ht.2 ((Affine.Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder P').1 h)))
    have hP : 0 < P'.canonicalHeight :=
      lt_of_le_of_ne (Affine.Point.canonicalHeight_nonneg P') (Ne.symm hP0)
    refine ⟨κ' * P'.canonicalHeight / y.canonicalHeight, by positivity, ?_⟩
    have hy' : (y.canonicalHeight : ℂ) ≠ 0 := by exact_mod_cast h0
    rw [hA]
    push_cast
    rw [div_mul_cancel₀ _ hy']

/-- The analytic Heegner point as one parameter: `Σ_{Q ∈ S} weierPt E L (c φ_f(τ_Q)) =
weierPt E L (c Σ_Q φ_f(τ_Q))`. -/
theorem heegnerC_eq {E : WeierstrassCurve ℚ} [E.IsElliptic] (hE : IsShortModel E) {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice E L) {N : ℕ} [NeZero N] (f : Newform N 2) (c : ℂ) {D : ℤ}
    (S : Finset (HeegnerForm N D)) :
    ZInQ.GZHL3.heegnerC E L f c S =
      ZInQ.GZHL3.weierPt E L (c * ∑ r : S, ZInQ.GZHL3.eichler f r.1.tauH) := by
  rw [ZInQ.GZHL3.heegnerC, weierPt_sum hE hL, Finset.mul_sum, ← Finset.sum_coe_sort S]

/-- `Σ_r φ(τ_r)` for the analytic parametrization with constant `c`, as one parameter. -/
theorem sum_modPt_eq {E : WeierstrassCurve ℚ} [E.IsElliptic] (hE : IsShortModel E) {L : PeriodPair}
    {N : ℕ} [NeZero N] {f : Newform N 2} {c : ℚ} (hs : ParamSetting E f L c) {D : ℤ}
    (S : Finset (HeegnerForm N D)) :
    ∑ r : S, ZInQ.GZModuli.modPt E (xPar E L f c) (yPar E L f c) r.1.tauH =
      ZInQ.GZHL3.weierPt E L (c * ∑ r : S, ZInQ.GZHL3.eichler f r.1.tauH) := by
  rw [Finset.mul_sum, ← weierPt_sum hE hs.2.2.1]
  exact Finset.sum_congr rfl fun r _ => ZInQ.GZModuli.modPt_eq hs r.1.tauH

/-! ## §5. The optimal-parametrization leaf is weaker than gz-moduli's leaf -/

/-- **`GrossZagierModuliOptAt E` follows from gz-moduli's `GrossZagierModuliAt E`** (short `E`): the
`n`-multiple of the optimal Heegner sum is the Heegner sum of the parametrization `[n] ∘ φ`. -/
theorem grossZagierModuliOptAt_of_moduliAt {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (hE : IsShortModel E) (h : ZInQ.GZModuli.GrossZagierModuliAt E) : GrossZagierModuliOptAt E := by
  intro N _ f hχ hcoeff X Y _ hopt D β hD hD4 hH hβ R _ τ hτ K _ _ _ hK δ hδ ι hι n _ y hy F G hF hG
  obtain ⟨L, c, hL, hlat, hmod⟩ := hopt
  have hs : ParamSetting E f L ((n : ℚ) * c) :=
    ⟨hχ, hcoeff, hL, mul_ne_zero (by exact_mod_cast ‹n ≠ 0›) (ne_zero_of_lattice hlat),
      periodsIn_zsmul (periodsIn_of_lattice hlat) n⟩
  refine h N f hχ hcoeff _ _ (ZInQ.GZModuli.isModularParam_of hs) D β hD hD4 hH hβ R τ hτ K hK δ
    hδ ι hι y ?_ F G hF hG
  rw [hy]
  simp only [hmod, fun r => ZInQ.GZModuli.modPt_eq hs (τ r), zPar, weierPt_sum hE hL,
    weierPt_zsmul hE hL, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  push_cast; ring

/-- **`GrossZagierModuliOptCd` follows from gz-moduli's all-`E` leaf `GrossZagierModuli`.** -/
theorem grossZagierModuliOptCd_of_moduli (h : ZInQ.GZModuli.GrossZagierModuli) :
    GrossZagierModuliOptCd :=
  fun _ _ _ E' _ hE' _ => grossZagierModuliOptAt_of_moduliAt hE' (h E')

/-! ## §6. The core: the formula for `weierPt E L (c φ_f)` from the optimal case

Both routes are stated for any complete set `τ : R → ℍ` of Heegner points and any `y ∈ E(K)` with
`ι(y) = Σ_r weierPt E L (c φ_f(τ_r))`, `c ∈ ℚ^×`, `c Λ_f ⊆ L`: that is the Heegner sum of the
parametrization `weierPt E L (c φ_f)` (additivity of `weierPt`). -/

/-- `Σ_r φ(τ_r)` for the analytic parametrization with constant `c`, as one parameter. -/
theorem sum_modPt_eq' {E : WeierstrassCurve ℚ} [E.IsElliptic] (hE : IsShortModel E)
    {L : PeriodPair} {N : ℕ} [NeZero N] {f : Newform N 2} {c : ℚ} (hs : ParamSetting E f L c)
    {R : Type} [Fintype R] (τ : R → ℍ) :
    ∑ r, ZInQ.GZModuli.modPt E (xPar E L f c) (yPar E L f c) (τ r) =
      ZInQ.GZHL3.weierPt E L (c * ∑ r, ZInQ.GZHL3.eichler f (τ r)) := by
  rw [Finset.mul_sum, ← weierPt_sum hE hs.2.2.1]
  exact Finset.sum_congr rfl fun r _ => ZInQ.GZModuli.modPt_eq hs (τ r)

section Core

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] (hE : IsShortModel E) {N : ℕ} [NeZero N]
  {f : Newform N 2} (hχ : f.χ = 1) (hcoeff : ∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ))
  {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice E L) {c : ℚ} (hc : c ≠ 0)
  (hP : ZInQ.GZHL3.PeriodsIn f c L) {D β : ℤ} (hD : IsOddImagFundDisc D) (hD4 : D < -4)
  (hH : HeegnerHyp N D) (hβ : (4 * N : ℤ) ∣ D - β ^ 2) {R : Type} [Fintype R] {τ : R → ℍ}
  (hτ : ZInQ.GZModuli.IsHeegnerPointReps N D β τ) {K : Type} [Field K] [NumberField K]
  [DecidableEq K] (hK : Module.finrank ℚ K = 2) {δ : K} (hδ : δ ^ 2 = (D : K)) {ι : K →ₐ[ℚ] ℂ}
  (hι : ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ)) (y : (E⁄K).Point)
  (hy : Affine.Point.map ι y = ZInQ.GZHL3.weierPt E L (c * ∑ r, ZInQ.GZHL3.eichler f (τ r)))
  {F G : ℂ → ℂ} (hF : IsEntireCont (coeff f) 2 F) (hG : IsEntireCont (twistCoeff f D) 2 G)
include hE hχ hcoeff hL hc hP hD hD4 hH hβ hτ hK hδ hι hy hF hG

/-- **Core of route A**: `E` is its own strong Weil curve, `L = c₀ Λ_f`. Every admissible `c` is
`n c₀`, `n ∈ ℤ ∖ {0}`, and the Heegner sum is `n · y_K(φ_opt)`. -/
theorem core_selfOptimal (hGZ : GrossZagierModuliOptAt E) {c₀ : ℚ}
    (hlat : L.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c₀ : ℂ))) :
    ∃ κ : ℝ, 0 < κ ∧ deriv (fun s => F s * G s) 1 = κ * y.canonicalHeight := by
  have hc₀ := ne_zero_of_lattice hlat
  have hs₀ : ParamSetting E f L c₀ := ⟨hχ, hcoeff, hL, hc₀, periodsIn_of_lattice hlat⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, c / c₀ = n := by
    apply rat_mem_int (L := L)
    have h1 := L.ω₁_mem_lattice
    rw [hlat] at h1
    obtain ⟨w, hw, hw1⟩ := h1
    have : ((c / c₀ : ℚ) : ℂ) * L.ω₁ = c * w := by
      rw [← hw1]; simp only [LinearMap.mulLeft_apply]; push_cast; field_simp
    rw [this]
    exact mul_mem_of_periodsIn hP hw
  have hcn : (c : ℂ) = n * c₀ := by
    have : c = n * c₀ := by rw [← hn]; field_simp
    exact_mod_cast this
  have hn0 : n ≠ 0 := by
    rintro rfl; apply hc; simpa using hcn
  refine hGZ N f hχ hcoeff _ _ (ZInQ.GZModuli.isModularParam_of hs₀) ⟨L, c₀, hL, hlat,
    ZInQ.GZModuli.modPt_eq hs₀⟩ D β hD hD4 hH hβ R τ hτ K hK δ hδ ι hι n hn0 y ?_ F G hF hG
  rw [hy, sum_modPt_eq' hE hs₀, weierPt_zsmul hE hL, hcn, mul_assoc]

omit hcoeff in
/-- **Core of route B**: through the strong Weil curve `E'` of `f`. The parametrization
`weierPt E L (c φ_f)` is `ψ ∘ φ'` with `φ' = weierPt E' L' (c' φ_f)` optimal and `ψ : E' → E`,
`z ↦ (c/c') z`. With `M L ⊆ (c/c') L'` (`M ∈ ℤ ∖ {0}`, finite index), the isogeny `ψ̂ : E → E'`,
`z ↦ μ z`, `μ = M c'/c ∈ ℚ`, maps `y` to `P' ∈ E'(K)` with `ι(P') = M · y_K(φ')`. The optimal leaf at
`E'` gives `L'(E/K, 1) = κ' ĥ(P')`, and `y`, `P'` are torsion together (read off from their complex
parameters), so `L'(E/K, 1) = κ ĥ(y)`. -/
theorem core_transfer (hI : AnalyticIsogenyRational) {E' : WeierstrassCurve ℚ} [E'.IsElliptic]
    (hE's : IsShortModel E') (hGZ : GrossZagierModuliOptAt E')
    (hcoeff' : ∀ n : ℕ, n ≠ 0 → coeff f n = (E'.LFunction n : ℂ)) {L' : PeriodPair} {c' : ℚ}
    (hL' : ZInQ.GZHL3.IsPeriodLattice E' L')
    (hlat' : L'.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c' : ℂ))) :
    ∃ κ : ℝ, 0 < κ ∧ deriv (fun s => F s * G s) 1 = κ * y.canonicalHeight := by
  have hc' := ne_zero_of_lattice hlat'
  have hs' : ParamSetting E' f L' c' := ⟨hχ, hcoeff', hL', hc', periodsIn_of_lattice hlat'⟩
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hc'C : (c' : ℂ) ≠ 0 := by exact_mod_cast hc'
  -- `m L' ⊆ L` for `m = c / c'`
  have hmL : ∀ z ∈ L'.lattice, ((c : ℂ) / c') * z ∈ L.lattice := by
    intro z hz
    rw [hlat'] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have : (c : ℂ) / c' * (LinearMap.mulLeft ℤ (c' : ℂ) w) = c * w := by
      simp only [LinearMap.mulLeft_apply]; field_simp
    rw [this]
    exact mul_mem_of_periodsIn hP hw
  obtain ⟨M, hM0, hM⟩ := exists_int_mul_mem L L' (div_ne_zero hcC hc'C) hmL
  -- `μ L ⊆ L'` for `μ = M c' / c`
  set μ : ℚ := M * c' / c with hμ
  have hμ0 : μ ≠ 0 := div_ne_zero (mul_ne_zero (by exact_mod_cast hM0) hc') hc
  have hμC : (μ : ℂ) = M * c' / c := by rw [hμ]; push_cast; rfl
  have hμL : ∀ z ∈ L.lattice, (μ : ℂ) * z ∈ L'.lattice := by
    intro z hz
    obtain ⟨w, hw, hMw⟩ := hM z hz
    have : (μ : ℂ) * z = w := by
      rw [hμC]
      have e : (M : ℂ) * z * c' = c * w := by rw [hMw]; field_simp
      field_simp
      linear_combination e
    rw [this]; exact hw
  obtain ⟨P', hP'⟩ := hI E E' L L' hL hL' μ hμ0 hμL K ι y
  set u : ℂ := ∑ r, ZInQ.GZHL3.eichler f (τ r) with hu
  have hP'u : Affine.Point.map ι P' = ZInQ.GZHL3.weierPt E' L' (M * (c' * u)) := by
    rw [hP' _ hy, hμC]
    congr 1
    field_simp
  obtain ⟨κ', hκ', hA⟩ := hGZ N f hχ hcoeff' _ _ (ZInQ.GZModuli.isModularParam_of hs')
    ⟨L', c', hL', hlat', ZInQ.GZModuli.modPt_eq hs'⟩ D β hD hD4 hH hβ R τ hτ K hK δ hδ ι hι M hM0
    P' (by rw [hP'u, sum_modPt_eq' hE's hs', weierPt_zsmul hE's hL']) F G hF hG
  refine exists_pos_of_torsion_iff y P' hκ' hA ?_
  rw [isOfFinAddOrder_iff hE hL ι y hy, isOfFinAddOrder_iff hE's hL' ι P' hP'u]
  constructor
  · rintro ⟨k, hk, hmem⟩
    refine ⟨k, hk, ?_⟩
    have := hμL _ hmem
    have e : (μ : ℂ) * (k * (c * u)) = k * (M * (c' * u)) := by rw [hμC]; field_simp
    rwa [e] at this
  · rintro ⟨k, hk, hmem⟩
    have h1 := hmL _ hmem
    have e : (c : ℂ) / c' * (k * (M * (c' * u))) = ((k * M : ℤ) : ℂ) * (c * u) := by
      push_cast; field_simp
    rw [e] at h1
    obtain ⟨j, hj, hjeq⟩ : ∃ j : ℕ, 0 < j ∧ ((k * M : ℤ) = j ∨ (k * M : ℤ) = -j) :=
      ⟨_, Int.natAbs_pos.2 (mul_ne_zero (by exact_mod_cast hk.ne') hM0), Int.natAbs_eq _⟩
    refine ⟨j, hj, ?_⟩
    rcases hjeq with h | h
    · rw [h] at h1; exact_mod_cast h1
    · rw [h] at h1
      have := L.lattice.neg_mem h1
      rw [Int.cast_neg, neg_mul, neg_neg] at this
      exact_mod_cast this

end Core

/-! ## §7. `GZHL3.GrossZagierFormulaCd` (the consumer) from the optimal case -/

/-- **Route A, at `E`**: `GZHL3.GrossZagierFormulaAt E` if `E` is its own strong Weil curve. -/
theorem grossZagierFormulaAt_of_selfOptimal {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (hE : IsShortModel E) (hGZ : GrossZagierModuliOptAt E)
    (hOpt : ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
      (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
      ∀ L : PeriodPair, ZInQ.GZHL3.IsPeriodLattice E L →
        ∃ c₀ : ℚ, L.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c₀ : ℂ))) :
    ZInQ.GZHL3.GrossZagierFormulaAt E := by
  intro N _ f hχ hcoeff D β hD hD4 hH hβ S hS L c hL hc hP K _ _ _ hK δ hδ ι hι y hy F G hF hG
  obtain ⟨c₀, hlat⟩ := hOpt N f hχ hcoeff L hL
  exact core_selfOptimal hE hχ hcoeff hL hc hP hD hD4 hH hβ
    (ZInQ.GZModuli.isHeegnerPointReps_of hD hS) hK hδ hι y (by rw [hy, heegnerC_eq hE hL]) hF hG
    hGZ hlat

/-- **`GZHL3.GrossZagierFormulaCd` from the optimal-parametrization leaf and `CdOptimal`** (route A:
the curves `C_d` are their own strong Weil curves). -/
theorem grossZagierFormulaCd_of_selfOptimal (hGZ : GrossZagierModuliOptCd) (hOpt : CdOptimal) :
    ZInQ.GZHL3.GrossZagierFormulaCd := fun d hd hsq => by
  have := shortCurve_cd_isElliptic (d := d) (by omega)
  exact grossZagierFormulaAt_of_selfOptimal (short_cd d) (hGZ d hd hsq _ (short_cd d) fun _ _ => rfl)
    (hOpt d hd hsq)

/-- **Route B, at `E`**: `GZHL3.GrossZagierFormulaAt E` from the optimal leaf on the short models
isogenous to `E`, the strong Weil curve of each newform of `E` with its period lattice, and the
rationality of analytic isogenies. -/
theorem grossZagierFormulaAt_of_transfer {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (hE : IsShortModel E)
    (hGZ : ∀ (E' : WeierstrassCurve ℚ) [E'.IsElliptic], IsShortModel E' →
      (∀ n : ℕ, n ≠ 0 → E'.LFunction n = E.LFunction n) → GrossZagierModuliOptAt E')
    (hSW : ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
      (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
      ∃ E' : WeierstrassCurve ℚ, E'.IsElliptic ∧ IsShortModel E' ∧
        (∀ n : ℕ, n ≠ 0 → coeff f n = (E'.LFunction n : ℂ)) ∧
        ∃ (L' : PeriodPair) (c : ℚ), ZInQ.GZHL3.IsPeriodLattice E' L' ∧
          L'.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c : ℂ)))
    (hI : AnalyticIsogenyRational) : ZInQ.GZHL3.GrossZagierFormulaAt E := by
  intro N _ f hχ hcoeff D β hD hD4 hH hβ S hS L c hL hc hP K _ _ _ hK δ hδ ι hι y hy F G hF hG
  obtain ⟨E', hE'e, hE's, hcoeff', L', c', hL', hlat'⟩ := hSW N f hχ hcoeff
  have := hE'e
  have hLF : ∀ n : ℕ, n ≠ 0 → E'.LFunction n = E.LFunction n := fun n hn => by
    have := (hcoeff' n hn).symm.trans (hcoeff n hn)
    exact_mod_cast this
  exact core_transfer hE hχ hL hc hP hD hD4 hH hβ
    (ZInQ.GZModuli.isHeegnerPointReps_of hD hS) hK hδ hι y (by rw [hy, heegnerC_eq hE hL]) hF hG
    hI hE's (hGZ E' hE's hLF) hcoeff' hL' hlat'

/-- **`GZHL3.GrossZagierFormulaCd` from the optimal-parametrization leaf, the strong Weil curve with
its period lattice, and the rationality of analytic isogenies** (route B: no assumption on which
curve of the isogeny class of `C_d` is optimal). -/
theorem grossZagierFormulaCd_of_transfer (hGZ : GrossZagierModuliOptCd)
    (hSW : StrongWeilOptimalCd) (hI : AnalyticIsogenyRational) :
    ZInQ.GZHL3.GrossZagierFormulaCd := fun d hd hsq => by
  have := shortCurve_cd_isElliptic (d := d) (by omega)
  exact grossZagierFormulaAt_of_transfer (short_cd d) (hGZ d hd hsq) (hSW d hd hsq) hI

/-! ## §8. The all-`φ` leaf of gz-moduli from the optimal case

gz-moduli's `GrossZagierModuliCd` quantifies over every `φ = (X, Y)` with `IsModularParam`, not only
the analytic ones `weierPt E L (c φ_f)`. That every such `φ` is analytic is the factorization of a
modular parametrization through the `f`-part of `J₀(N)`; the kernel lacks it, so it is isolated here
as `ModularParamAnalyticAt` (composite). The consumer `GZHL3.GrossZagierFormulaCd` does not need it
(§7): its `φ` are analytic by definition. -/

/-- **(Composite; not needed by the consumer) Every modular parametrization is analytic.** For a
nonconstant `φ = (X, Y) : X₀(N) → E` over `ℚ` with `φ(∞) = O` (`IsModularParam`), `E` with the
L-series of the newform `f`: the lift of `φ` to `ℍ → ℂ` is `c φ_f`, `c ∈ ℚ^×`, with `c Λ_f ⊆ L`.

Content: `φ^*ω = 2πi g(τ) dτ` with `g ∈ S₂(Γ₀(N))` of rational `q`-expansion (`φ`, `ω` over `ℚ`);
`φ` factors through `J₀(N) → E`, which by Eichler–Shimura, Faltings' isogeny theorem and
multiplicity one factors through the `f`-isotypic quotient, so `g = c f`; integrating from the cusp
`∞` (`φ(∞) = O`) gives the lift `c φ_f`, whose periods `c Λ_f` lie in `L`. Sources: Shimura 1971,
Thm 7.14; Faltings 1983, Korollar 2; Atkin–Lehner 1970 (multiplicity one); all UNVERIFIED. -/
def ModularParamAnalyticAt (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ X Y : ℍ → ℂ, ZInQ.GZModuli.IsModularParam N E X Y →
    ∃ (L : PeriodPair) (c : ℚ), ZInQ.GZHL3.IsPeriodLattice E L ∧ c ≠ 0 ∧
      ZInQ.GZHL3.PeriodsIn f c L ∧
      ∀ τ : ℍ, ZInQ.GZModuli.modPt E X Y τ = ZInQ.GZHL3.weierPt E L (c * ZInQ.GZHL3.eichler f τ)

/-- `ModularParamAnalyticAt C_d` for the curves of the route. -/
def ModularParamAnalyticCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ModularParamAnalyticAt (shortCurve (-(d : ℚ) ^ 2))

/-- **gz-moduli's `GrossZagierModuliAt E` (every modular parametrization) from the optimal case**
(route B), given that every modular parametrization is analytic. -/
theorem grossZagierModuliAt_of_transfer {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (hE : IsShortModel E)
    (hGZ : ∀ (E' : WeierstrassCurve ℚ) [E'.IsElliptic], IsShortModel E' →
      (∀ n : ℕ, n ≠ 0 → E'.LFunction n = E.LFunction n) → GrossZagierModuliOptAt E')
    (hSW : ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
      (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
      ∃ E' : WeierstrassCurve ℚ, E'.IsElliptic ∧ IsShortModel E' ∧
        (∀ n : ℕ, n ≠ 0 → coeff f n = (E'.LFunction n : ℂ)) ∧
        ∃ (L' : PeriodPair) (c : ℚ), ZInQ.GZHL3.IsPeriodLattice E' L' ∧
          L'.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c : ℂ)))
    (hI : AnalyticIsogenyRational) (hMP : ModularParamAnalyticAt E) :
    ZInQ.GZModuli.GrossZagierModuliAt E := by
  intro N _ f hχ hcoeff X Y hXY D β hD hD4 hH hβ R _ τ hτ K _ _ _ hK δ hδ ι hι y hy F G hF hG
  obtain ⟨L, c, hL, hc, hP, hmod⟩ := hMP N f hχ hcoeff X Y hXY
  obtain ⟨E', hE'e, hE's, hcoeff', L', c', hL', hlat'⟩ := hSW N f hχ hcoeff
  have := hE'e
  have hLF : ∀ n : ℕ, n ≠ 0 → E'.LFunction n = E.LFunction n := fun n hn => by
    have := (hcoeff' n hn).symm.trans (hcoeff n hn)
    exact_mod_cast this
  refine core_transfer hE hχ hL hc hP hD hD4 hH hβ hτ hK hδ hι y ?_ hF hG hI hE's
    (hGZ E' hE's hLF) hcoeff' hL' hlat'
  rw [hy, Finset.mul_sum, ← weierPt_sum hE hL]
  exact Finset.sum_congr rfl fun r _ => hmod (τ r)

/-- **gz-moduli's leaf `GZModuli.GrossZagierModuliCd` from the optimal case** (route B), given
`ModularParamAnalyticCd`. -/
theorem grossZagierModuliCd_of_transfer (hGZ : GrossZagierModuliOptCd)
    (hSW : StrongWeilOptimalCd) (hI : AnalyticIsogenyRational) (hMP : ModularParamAnalyticCd) :
    ZInQ.GZModuli.GrossZagierModuliCd := fun d hd hsq => by
  have := shortCurve_cd_isElliptic (d := d) (by omega)
  exact grossZagierModuliAt_of_transfer (short_cd d) (hGZ d hd hsq) (hSW d hd hsq) hI (hMP d hd hsq)

/-- **gz-moduli's `GrossZagierModuliAt E` from the optimal case, route A** (`E` its own strong Weil
curve), given that every modular parametrization is analytic. -/
theorem grossZagierModuliAt_of_selfOptimal {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (hE : IsShortModel E) (hGZ : GrossZagierModuliOptAt E)
    (hOpt : ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
      (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
      ∀ L : PeriodPair, ZInQ.GZHL3.IsPeriodLattice E L →
        ∃ c₀ : ℚ, L.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c₀ : ℂ)))
    (hMP : ModularParamAnalyticAt E) : ZInQ.GZModuli.GrossZagierModuliAt E := by
  intro N _ f hχ hcoeff X Y hXY D β hD hD4 hH hβ R _ τ hτ K _ _ _ hK δ hδ ι hι y hy F G hF hG
  obtain ⟨L, c, hL, hc, hP, hmod⟩ := hMP N f hχ hcoeff X Y hXY
  obtain ⟨c₀, hlat⟩ := hOpt N f hχ hcoeff L hL
  refine core_selfOptimal hE hχ hcoeff hL hc hP hD hD4 hH hβ hτ hK hδ hι y ?_ hF hG hGZ hlat
  rw [hy, Finset.mul_sum, ← weierPt_sum hE hL]
  exact Finset.sum_congr rfl fun r _ => hmod (τ r)

/-- **gz-moduli's leaf `GZModuli.GrossZagierModuliCd` from the optimal case, route A**, given
`CdOptimal` and `ModularParamAnalyticCd`. -/
theorem grossZagierModuliCd_of_selfOptimal (hGZ : GrossZagierModuliOptCd) (hOpt : CdOptimal)
    (hMP : ModularParamAnalyticCd) : ZInQ.GZModuli.GrossZagierModuliCd := fun d hd hsq => by
  have := shortCurve_cd_isElliptic (d := d) (by omega)
  exact grossZagierModuliAt_of_selfOptimal (short_cd d)
    (hGZ d hd hsq _ (short_cd d) fun _ _ => rfl) (hOpt d hd hsq) (hMP d hd hsq)

end ZInQ.GZOptimal

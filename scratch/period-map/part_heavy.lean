
/-! ## period-map (heavy part): `PeriodMapGlue` from strictly smaller named Props

Task period-map, 2026-11-13. `PeriodMapGlue Y Φ π` (fibre-qm-period, above, unchanged) is proved
from `R1fpProps Y Φ` (its naturality clause only) and five named Props
(`periodMapGlue_of`); at the leaf's own triple the clause list comes from the bundle
(`periodMapGlue_own`). One of the five, `CMFixedHasCM`, is proved from the textbook leaf T11a
(`cmFixedHasCM_of`), so four glue Props remain. The main
theorem `fibreQMPeriod_periodMap` restates fibre-qm-period's `fibreQMPeriod_main` with
`PeriodMapGlue`, `HauptmodulUnique` and `QMDenZeroCM3` replaced by their named pieces. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodMapH

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM

/-- `Q/ℂ` has an `ι`-compatible analytic uniformization with kernel exactly `Λ_τ = ι(𝒪)(τ, 1)ᵀ`
(the hypothesis shape shared by `QMPeriodMap`, `IsR1bFamily` and `PeriodMapGlue`). -/
def HasQMPeriod (Q : QML3 ℂ) (τ : UpperHalfPlane) : Prop :=
  ∃ Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
      IotaCompatible Q Φu

/-- **GLUE (uniqueness of base change up to isomorphism).** Two base changes of `P/ℚ̄` along the
same `ι : ℚ̄ → ℂ` (`IsBaseChangeOf`) have the same class in `M3 ℂ`.

Why true: both squares are pullbacks of `P.A → Spec ℚ̄` along `Spec ι`, so there is a unique
isomorphism `Q.A ≅ Q'.A` over `Spec ℂ` commuting with the maps to `P.A`; uniqueness of maps into a
pullback makes it commute with `ι(a)` and carry `η(a)` to `η'(a)`; it carries the identity section
`η(0)` to `η'(0)`, so it is a homomorphism (rigidity: Mumford, *Abelian Varieties*, §4 Cor. 1,
UNVERIFIED number). Size: medium (pullback bookkeeping; rigidity is not in Mathlib). -/
def BaseChangeClassUnique : Prop :=
  ∀ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q Q' : QML3 ℂ),
    IsBaseChangeOf ιe P Q → IsBaseChangeOf ιe P Q' → M3.mk Q = M3.mk Q'

/-- **GLUE (R2fp's fibre clause on `ℂ`-points).** Two `ℂ`-points of `Y` have the same `π`-value iff
the underlying QM pairs of their objects are `Aut(𝒪)`-twists of each other (as `R2fpProps` states
for `ℚ̄`-points).

Why true for the genuine `Y₃`: `π` is `Y₃ → X₆ → X₆/W ≅ P¹` (R2, Baba–Granath), `X₆(ℂ)` is the set
of isomorphism classes of QM pairs over `ℂ` (coarse moduli space: bijective on points over
algebraically closed fields; Shimura 1967, Deligne 1971; locators UNVERIFIED) and `W ≅ Aut(𝒪)`
acts by twists. For another triple satisfying the repaired clause lists it follows by qm-pin's
comparison (`Y' ≅ Y₃` compatibly with `Φ` and `π`). It does not follow from `R2fpProps` alone,
which speaks of `ℚ̄`-points: one needs that the two relations are algebraic, or the coarse moduli
property over `ℂ`. Size: medium-large. -/
def PiTwistC (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  ∀ (y y' : fieldPt ℂ ⟶ Y) (Q Q' : QML3 ℂ), Φ ℂ y = M3.mk Q → Φ ℂ y' = M3.mk Q' →
    (π.val (K := ℂ) y.left = π.val (K := ℂ) y'.left ↔
      ∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (Q.q.twist α) Q'.q))

/-- **GLUE (Shimura's description of QM tori up to twist).** If `Q, Q'/ℂ` are `ι`-compatibly
`ℂ²/Λ_τ` and `ℂ²/Λ_τ'`, then their QM pairs are `Aut(𝒪)`-twists of each other iff `τ' ∈ Γ*τ`.

Why true (model argument): by GAGA and the `Hom` form of T11a (Mumford §1-2; Birkenhake–Lange
Prop. 1.2.1, UNVERIFIED numbers), an isomorphism `Q.q.twist α ≅ Q'.q` is a linear `T` with
`TΛ_τ = Λ_τ'` and `Tι(α(a)) = ι(a)T`. By Skolem–Noether `α = u⁻¹(·)u` with `u ∈ N_B(𝒪)`, so
`Tι(u)⁻¹` commutes with `ι(B)`, hence is a scalar `c`, and `Λ_τ' = c ι(u)Λ_τ = c ι(𝒪)ι(u)v_τ`. If
`nrd(u) > 0` this says `τ' = ι(u)·τ` (`ι(𝒪)w` determines the line of `w` up to `ι(𝒪^×)`... more
precisely `ι(𝒪)(τ',1)ᵀ = ι(𝒪)(ι(u)τ, 1)ᵀ` iff `τ' ∈ ι(𝒪¹)ι(u)τ`); if `nrd(u) < 0` replace `u` by
`(1+i)u` (`1 + i ∈ 𝒪^×`, reduced norm `−1`, `ι(𝒪)(1+i) = ι(𝒪)`). Conversely `g = ι(u) ∈ Γ*` gives
`T = (cτ + d)⁻¹ ι(u)` and `α = u⁻¹(·)u`. Inputs: the `Hom` version of T11a (the kernel has only the
`End` version) and Skolem–Noether over `ℚ` (the kernel's `TSkolemKW`). Size: medium. -/
def QMTwistLattice : Prop :=
  ∀ (Q Q' : QML3 ℂ) (τ τ' : UpperHalfPlane), HasQMPeriod Q τ → HasQMPeriod Q' τ' →
    ((∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (Q.q.twist α) Q'.q)) ↔
      ∃ g ∈ PkgI1.GammaStar, g • τ = τ')

/-- **GLUE (R2fp's CM clauses on `ℂ`-points).** At a `ℂ`-point whose object has CM by `ℤ[i]`
(resp. `ℤ[ζ₃]`, `ℤ[√−6]`), `π` takes the value `0` (resp. `∞`, `−16/27`).

Why true: a QM abelian surface over `ℂ` with CM is isomorphic (with `ι`) to the base change of one
over `ℚ̄` (CM abelian varieties are defined over `ℚ̄`: Shimura–Taniyama; or: the CM points of `X₆`
are algebraic, Shimura 1967), so with `PiTwistC`, R1fp's naturality and `ToP1.val_comp` the value
is `ι(π(y₀))` for a `ℚ̄`-point `y₀` with CM, which `R2fpProps` gives. Size: medium. -/
def PiCMC (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  ∀ (y : fieldPt ℂ ⟶ Y) (Q : QML3 ℂ), Φ ℂ y = M3.mk Q →
    (HasCM4 Q.q → π.val (K := ℂ) y.left = OnePoint.some 0) ∧
    (HasCM3 Q.q → π.val (K := ℂ) y.left = OnePoint.infty) ∧
    (HasCM24 Q.q → π.val (K := ℂ) y.left = OnePoint.some (-16 / 27))

/-- **GLUE (the CM points of `ℍ`; proved below from T11a, `cmFixedHasCM_of`).** If `Q/ℂ` is
`ι`-compatibly `ℂ²/Λ_τ` and `τ` is fixed by `ι(x)`, `x ∈ 𝒪`, with `x² = −1` (resp.
`x² − x + 1 = 0`, `x² = −6`), then `Q` has CM by `ℤ[i]` (resp. `ℤ[ζ₃]`, `ℤ[√−6]`).

Why true: `ι(x)v_τ = λv_τ` with `λ = cτ + d`, so `z ↦ λz` preserves `Λ_τ`
(`λι(a)v_τ = ι(ax)v_τ`) and commutes with `ι(𝒪)`; by T11a it is an endomorphism `φ` in the
centralizer of `ι(𝒪)` with `φ² = −1` (resp. ...), since `λ` satisfies the equation of `x`. -/
def CMFixedHasCM : Prop :=
  ∀ (Q : QML3 ℂ) (τ : UpperHalfPlane), HasQMPeriod Q τ →
    ∀ (x : PkgI1.B) (g : GL (Fin 2) ℝ), PkgI1.InO x →
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → g • τ = τ →
      (x * x = -1 → HasCM4 Q.q) ∧ (x * x - x + 1 = 0 → HasCM3 Q.q) ∧
        (x * x = -6 → HasCM24 Q.q)

theorem one_mem_gammaStar : (1 : GL (Fin 2) ℝ) ∈ PkgI1.GammaStar :=
  ⟨1, ⟨1, by simp, by simp, fun z hz => ⟨by rwa [_root_.one_mul, _root_.mul_one], by rwa [_root_.one_mul, _root_.mul_one]⟩⟩,
    by simp [PeriodMap.iota_one], by simp⟩

/-! ### `CMFixedHasCM` from T11a (proved) -/

theorem mem_O_of_inO {x : PkgI1.B} (hx : PkgI1.InO x) : (x : LeafQM.B) ∈ LeafQM.O := by
  obtain ⟨n, rfl⟩ := hx
  show LeafQM.InO _
  exact ⟨n, by ext <;> simp [LeafQM.ofInt, PkgI1.oBasis, Fin.sum_univ_four] <;> ring⟩

theorem oBasis_mem (k : Fin 4) : BPAnalytic.QM.oBasis k ∈ LeafQM.O := by
  show LeafQM.InO _
  fin_cases k
  · exact ⟨![1, 0, 0, 0], by ext <;> simp [BPAnalytic.QM.oBasis, LeafQM.ofInt]⟩
  · exact ⟨![0, 1, 0, 0], by ext <;> simp [BPAnalytic.QM.oBasis, LeafQM.ofInt]⟩
  · exact ⟨![0, 0, 1, 0], by ext <;> simp [BPAnalytic.QM.oBasis, LeafQM.ofInt]⟩
  · exact ⟨![0, 0, 0, 1], by ext <;> simp [BPAnalytic.QM.oBasis, LeafQM.ofInt]⟩

/-- N5's basis element `b_k` as an element of `𝒪`. -/
def bO (k : Fin 4) : LeafQM.O := ⟨BPAnalytic.QM.oBasis k, oBasis_mem k⟩

/-- An element with `x² = −1`, `x² − x + 1 = 0` or `x² = −6` has positive reduced norm. -/
theorem det_iota_pos (x : PkgI1.B) (h : x * x = -1 ∨ x * x - x + 1 = 0 ∨ x * x = -6) :
    0 < (PkgI1.iota x).det := by
  rw [PeriodMap.det_iota]
  have key : (0 : ℚ) < x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 := by
    rcases h with h | h | h
    · have e := congrArg QuaternionAlgebra.re h
      simp at e
      nlinarith [sq_nonneg x.re]
    · have e := congrArg QuaternionAlgebra.re h
      simp at e
      nlinarith [sq_nonneg (x.re - 1 / 4)]
    · have e := congrArg QuaternionAlgebra.re h
      simp [QuaternionAlgebra.re_ofNat] at e
      nlinarith [sq_nonneg x.re]
  exact_mod_cast key

/-- **`CMFixedHasCM` from the textbook leaf T11a (proved).** With `ρ` the analytic representation
(`unif_ring_hom`), `ρ(ι(a))` is the matrix `ι(a)` (`IotaCompatible`), `λ = cτ + d` is the eigenvalue
of `ι(x)` on `(τ, 1)ᵀ`, `z ↦ λz` preserves `Λ_τ` and lifts to `φ ∈ End(A)` (T11a), `φ` commutes with
`ι(𝒪)` and satisfies the equation of `x` because `ρ` is injective (T11a's uniqueness). -/
theorem cmFixedHasCM_of (hR : T11aRiemannEnd) : CMFixedHasCM := by
  intro Q τ ⟨Φu, hU, hc⟩ x g hx hg hgτ
  haveI : DiscreteTopology (BPAnalytic.QM.qmLattice τ.im_pos.ne') := by
    unfold BPAnalytic.QM.qmLattice; infer_instance
  obtain ⟨ρ, hρ, hpres⟩ := unif_ring_hom hR Q.A Q.surface (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu hU
  have hρι : ∀ a : LeafQM.O, ρ (Q.q.iota a) = Matrix.toLin' (qmMat a) := fun a =>
    lift_unique hU fun z => by rw [hρ, Matrix.toLin'_apply, hc]
  have hinj : ∀ e e', ρ e = ρ e' → e = e' := by
    intro e e' hee
    obtain ⟨f, -, huniq⟩ := (hR Q.A 2 (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu Q.surface hU).1 (ρ e) (hpres e)
    have h1 := huniq e (hρ e)
    have h2 := huniq e' (fun z => by rw [hee]; exact hρ e' z)
    exact h1.trans h2.symm
  set xO : LeafQM.O := ⟨x, mem_O_of_inO hx⟩ with hxO
  set v : Fin 2 → ℂ := ![(τ : ℂ), 1] with hv
  set lam : ℂ := UpperHalfPlane.denom g τ with hlam
  have hΛ : (BPAnalytic.QM.qmLattice τ.im_pos.ne') = Submodule.span ℤ (Set.range (BPAnalytic.QM.qmVec τ)) :=
    BPAnalytic.QM.qmLattice_eq _
  have hvΛ : v ∈ (BPAnalytic.QM.qmLattice τ.im_pos.ne') := by
    rw [hΛ]
    exact Submodule.subset_span ⟨0, BPAnalytic.QM.latVec0 τ⟩
  -- the CM point: `ι(x)(τ, 1)ᵀ = λ(τ, 1)ᵀ`
  have hcases : ∀ hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det,
      ∃ φ ∈ com Q.q, ρ φ = lam • 1 ∧ ρ (Q.q.iota xO) v = lam • v := by
    intro hdet
    have hfix : UpperHalfPlane.num g τ = (τ : ℂ) * UpperHalfPlane.denom g τ := by
      have := congrArg (fun w : UpperHalfPlane => (w : ℂ)) hgτ
      rw [UpperHalfPlane.coe_smul_of_det_pos (by simpa using hdet),
        div_eq_iff (UpperHalfPlane.denom_ne_zero g τ)] at this
      exact this
    have hxv : ρ (Q.q.iota xO) v = lam • v := by
      rw [hρι, Matrix.toLin'_apply]
      have hqm : qmMat xO = (g : Matrix (Fin 2) (Fin 2) ℝ).map (fun r : ℝ => (r : ℂ)) := by
        rw [hg]; rfl
      rw [hqm]
      ext i; fin_cases i
      · simp only [UpperHalfPlane.num, UpperHalfPlane.denom] at hfix
        simp [hv, hlam, Matrix.mulVec, dotProduct, Fin.sum_univ_two, UpperHalfPlane.denom]
        linear_combination hfix
      · simp [hv, hlam, Matrix.mulVec, dotProduct, Fin.sum_univ_two, UpperHalfPlane.denom]
    have hpresM : ∀ z ∈ (BPAnalytic.QM.qmLattice τ.im_pos.ne'), (lam • (1 : Module.End ℂ (Fin 2 → ℂ))) z ∈ (BPAnalytic.QM.qmLattice τ.im_pos.ne') := by
      have hle : (BPAnalytic.QM.qmLattice τ.im_pos.ne') ≤ (BPAnalytic.QM.qmLattice τ.im_pos.ne').comap ((lam • (1 : Module.End ℂ (Fin 2 → ℂ))).restrictScalars ℤ) := by
        rw [hΛ, Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        rw [← hΛ]
        show (lam • (1 : Module.End ℂ (Fin 2 → ℂ))) (BPAnalytic.QM.qmVec τ k) ∈ (BPAnalytic.QM.qmLattice τ.im_pos.ne')
        have h1 : BPAnalytic.QM.qmVec τ k = ρ (Q.q.iota (bO k)) v := by
          rw [hρι, Matrix.toLin'_apply]; rfl
        have h2 : (lam • (1 : Module.End ℂ (Fin 2 → ℂ))) (BPAnalytic.QM.qmVec τ k) =
            ρ (Q.q.iota (bO k * xO)) v := by
          rw [map_mul, map_mul, Module.End.mul_apply, hxv, map_smul, ← h1]
          rfl
        rw [h2]
        exact hpres _ v hvΛ
      exact fun z hz => hle hz
    obtain ⟨φ, hφ, -⟩ := (hR Q.A 2 (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu Q.surface hU).1 _ hpresM
    have hρφ : ρ φ = lam • 1 := lift_unique hU fun z => by rw [hρ]; exact (hφ z).symm
    refine ⟨φ, ?_, hρφ, hxv⟩
    rw [com, Subring.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    apply hinj
    rw [map_mul, map_mul, hρφ, mul_smul_comm, smul_mul_assoc, _root_.mul_one, _root_.one_mul]
  -- the equation satisfied by `λ`
  have hsq : ρ (Q.q.iota xO) v = lam • v → ρ (Q.q.iota (xO * xO)) v = (lam * lam) • v := by
    intro hxv
    rw [map_mul, map_mul, Module.End.mul_apply, hxv, map_smul, hxv, smul_smul]
  have hcoord : ∀ c c' : ℂ, c • v = c' • v → c = c' := by
    intro c c' h
    have := congrFun h 1
    simpa [hv] using this
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨φ, hφc, hρφ, hxv⟩ := hcases (by rw [hg]; exact det_iota_pos x (Or.inl h))
    have hx2 : xO * xO = -1 := Subtype.ext (by simpa using h)
    have hl : lam * lam = -1 := by
      apply hcoord
      rw [← hsq hxv, hx2, map_neg, map_one, map_neg, map_one]
      simp
    refine ⟨φ, hφc, hinj _ _ ?_⟩
    rw [map_mul, hρφ, map_neg, map_one, smul_mul_smul_comm, _root_.mul_one, hl]
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.smul_apply, LinearMap.neg_apply, Module.End.one_apply]
    ext i; simp
  · obtain ⟨φ, hφc, hρφ, hxv⟩ := hcases (by rw [hg]; exact det_iota_pos x (Or.inr (Or.inl h)))
    have hx2 : xO * xO - xO + 1 = 0 := Subtype.ext (by simpa using h)
    have hl : lam * lam - lam + 1 = 0 := by
      have e : ρ (Q.q.iota (xO * xO - xO + 1)) v = (lam * lam - lam + 1) • v := by
        rw [map_add, map_sub, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
          hsq hxv, hxv, map_one, map_one, Module.End.one_apply, add_smul, sub_smul, one_smul]
      rw [hx2, map_zero, map_zero, LinearMap.zero_apply] at e
      apply hcoord
      rw [← e, zero_smul]
    refine ⟨φ, hφc, hinj _ _ ?_⟩
    rw [map_add, map_sub, map_mul, hρφ, map_one, map_zero, smul_mul_smul_comm, _root_.mul_one]
    rw [show (lam * lam) • (1 : Module.End ℂ (Fin 2 → ℂ)) - lam • 1 + 1 =
      (lam * lam - lam + 1) • 1 by rw [add_smul, sub_smul, one_smul], hl, zero_smul]
  · obtain ⟨φ, hφc, hρφ, hxv⟩ :=
      hcases (by rw [hg]; exact det_iota_pos x (Or.inr (Or.inr h)))
    have hx2 : xO * xO = -6 := Subtype.ext (by push_cast; exact h)
    have e : ρ (Q.q.iota (xO * xO)) v = (-6 : ℂ) • v := by
      rw [hx2, map_neg, map_ofNat, map_neg, map_ofNat, LinearMap.neg_apply, Module.End.ofNat_apply]
      ext i; simp
    have hl : lam * lam = -6 := hcoord _ _ ((hsq hxv).symm.trans e)
    refine ⟨φ, hφc, hinj _ _ ?_⟩
    rw [map_mul, hρφ, smul_mul_smul_comm, _root_.mul_one, hl, map_neg, map_ofNat]
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.smul_apply, LinearMap.neg_apply, Module.End.ofNat_apply, Module.End.one_apply]
    ext i; simp

/-- **`PeriodMapGlue` from strictly smaller named Props (proved).** Only the naturality clause of
`R1fpProps` is used. -/
theorem periodMapGlue_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (h1 : R1fpProps Y Φ) (hBC : BaseChangeClassUnique) (hPT : PiTwistC Y Φ π)
    (hTL : QMTwistLattice) (hCM : PiCMC Y Φ π) (hCF : CMFixedHasCM) :
    PeriodMapGlue Y Φ π := by
  intro yτ hfam
  have hobj : ∀ τ, ∃ P : QML3 ℂ, Φ ℂ (yτ τ) = M3.mk P ∧ HasQMPeriod P τ := fun τ => by
    obtain ⟨P, hP, Φu, hU, hc⟩ := hfam.1 τ
    exact ⟨P, hP, Φu, hU, hc⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro τ τ'
    obtain ⟨P, hP, hPτ⟩ := hobj τ
    obtain ⟨P', hP', hPτ'⟩ := hobj τ'
    exact (hPT _ _ P P' hP hP').trans (hTL P P' τ τ' hPτ hPτ')
  · intro x hx hxx g hg τ hgτ
    obtain ⟨P, hP, hPτ⟩ := hobj τ
    exact (hCM _ P hP).1 ((hCF P τ hPτ x g hx hg hgτ).1 hxx)
  · intro x hx hxx g hg τ hgτ
    obtain ⟨P, hP, hPτ⟩ := hobj τ
    exact (hCM _ P hP).2.1 ((hCF P τ hPτ x g hx hg hgτ).2.1 hxx)
  · intro x hx hxx g hg τ hgτ
    obtain ⟨P, hP, hPτ⟩ := hobj τ
    exact (hCM _ P hP).2.2 ((hCF P τ hPτ x g hx hg hgτ).2.2 hxx)
  · intro y P hP ιe Q hQ τ Φu hΦu hc
    obtain ⟨Pτ, hPτ, hPer⟩ := hobj τ
    obtain ⟨Q', hQ', hBC'⟩ := h1.2.2.2.1 Qbar ℂ ιe.toRatAlgHom y P hP
    have hQQ : M3.mk Q' = M3.mk Q := hBC ιe P Q' Q hBC' hQ
    have hval := ToP1.val_comp π ιe y.left
    have hleft : (fieldMap ιe.toRatAlgHom ≫ y).left =
        Spec.map (CommRingCat.ofHom ιe) ≫ y.left := rfl
    rw [← hval, ← hleft]
    apply (hPT (yτ τ) (fieldMap ιe.toRatAlgHom ≫ y) Pτ Q hPτ (hQ'.trans hQQ)).mpr
    exact (hTL Pτ Q τ τ hPer ⟨Φu, hΦu, hc⟩).mpr ⟨1, one_mem_gammaStar, one_smul _ _⟩


/-! ### `PiCMC` from `PiTwistC`, R1fp, R2fp and the descent of CM objects (proved) -/

/-- **LEAF candidate (QM abelian surfaces with CM are defined over `ℚ̄`).** A level-3 QM surface
`Q/ℂ` with CM by `ℤ[i]` (resp. `ℤ[ζ₃]`, `ℤ[√−6]`) is, as a QM pair, isomorphic to the base change
along some `ι : ℚ̄ → ℂ` of a level-3 QM surface `P/ℚ̄` with the same CM.

Sources: Shimura–Taniyama, *Complex multiplication of abelian varieties* (1961), and Shimura 1967:
abelian varieties with CM are defined over `ℚ̄` (a CM point of `X₆` is algebraic; its fibre has a
model over the field of moduli); the CM descends because endomorphisms of `P_ℂ` come from `P`
(the kernel's textbook leaf T11b, `Hom_ℚ̄ = Hom_ℂ`); the level structure also descends because
`A[3] ⊆ A(ℚ̄)` (locators UNVERIFIED). A consequence of those published statements; size of the glue
around them: small-medium. -/
def CMDescends : Prop :=
  ∀ Q : QML3 ℂ,
    (HasCM4 Q.q → ∃ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ),
      IsBaseChangeOf ιe P Q' ∧ HasCM4 P.q ∧ Nonempty (QMIso Q.q Q'.q)) ∧
    (HasCM3 Q.q → ∃ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ),
      IsBaseChangeOf ιe P Q' ∧ HasCM3 P.q ∧ Nonempty (QMIso Q.q Q'.q)) ∧
    (HasCM24 Q.q → ∃ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ),
      IsBaseChangeOf ιe P Q' ∧ HasCM24 P.q ∧ Nonempty (QMIso Q.q Q'.q))

/-- A QM isomorphism is one for the trivial twist. -/
def qmIsoTwistRefl {A A' : PkgI3.AbVar ℂ} {q : QMStr A} {q' : QMStr A'} (e : QMIso q q') :
    QMIso (q.twist (RingEquiv.refl LeafQM.O)) q' where
  φ := e.φ
  ψ := e.ψ
  left := e.left
  right := e.right
  equivariant a := e.equivariant a

/-- The value of `π` at a `ℂ`-point whose QM pair comes from a `ℚ̄`-point (proved). -/
theorem pi_of_descends (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (h1 : R1fpProps Y Φ) (hBC : BaseChangeClassUnique) (hPT : PiTwistC Y Φ π)
    (y : fieldPt ℂ ⟶ Y) (Q : QML3 ℂ) (hQ : Φ ℂ y = M3.mk Q) (ιe : Qbar →+* ℂ) (P : QML3 Qbar)
    (Q' : QML3 ℂ) (hBCQ : IsBaseChangeOf ιe P Q') (hiso : Nonempty (QMIso Q.q Q'.q)) :
    π.val (K := ℂ) y.left = (π.val (K := Qbar) ((Φ Qbar).symm (M3.mk P)).left).map ιe := by
  set y₀ := (Φ Qbar).symm (M3.mk P) with hy₀
  have hP : Φ Qbar y₀ = M3.mk P := by rw [hy₀, Equiv.apply_symm_apply]
  obtain ⟨Q'', hQ'', hBC''⟩ := h1.2.2.2.1 Qbar ℂ ιe.toRatAlgHom y₀ P hP
  have hQQ : M3.mk Q'' = M3.mk Q' := hBC ιe P Q'' Q' hBC'' hBCQ
  have hval := ToP1.val_comp π ιe y₀.left
  have hleft : (fieldMap ιe.toRatAlgHom ≫ y₀).left =
      Spec.map (CommRingCat.ofHom ιe) ≫ y₀.left := rfl
  rw [← hval, ← hleft]
  obtain ⟨e⟩ := hiso
  exact (hPT y (fieldMap ιe.toRatAlgHom ≫ y₀) Q Q' hQ (hQ''.trans hQQ)).mpr
    ⟨RingEquiv.refl LeafQM.O, ⟨qmIsoTwistRefl e⟩⟩

/-- **`PiCMC` from `PiTwistC`, R1fp naturality, R2fp's CM clauses, `BaseChangeClassUnique` and
`CMDescends` (proved).** -/
theorem piCMC_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) (hBC : BaseChangeClassUnique)
    (hPT : PiTwistC Y Φ π) (hD : CMDescends) : PiCMC Y Φ π := by
  intro y Q hQ
  have hP : ∀ P : QML3 Qbar, Φ Qbar ((Φ Qbar).symm (M3.mk P)) = M3.mk P :=
    fun P => Equiv.apply_symm_apply _ _
  refine ⟨fun hcm => ?_, fun hcm => ?_, fun hcm => ?_⟩
  · obtain ⟨ιe, P, Q', hB, hPcm, hiso⟩ := (hD Q).1 hcm
    rw [pi_of_descends Y Φ π h1 hBC hPT y Q hQ ιe P Q' hB hiso,
      (h2 _ _ P P (hP P) (hP P)).2.1 hPcm]
    simp
  · obtain ⟨ιe, P, Q', hB, hPcm, hiso⟩ := (hD Q).2.1 hcm
    rw [pi_of_descends Y Φ π h1 hBC hPT y Q hQ ιe P Q' hB hiso,
      (h2 _ _ P P (hP P) (hP P)).2.2.1 hPcm]
    rfl
  · obtain ⟨ιe, P, Q', hB, hPcm, hiso⟩ := (hD Q).2.2 hcm
    rw [pi_of_descends Y Φ π h1 hBC hPT y Q hQ ιe P Q' hB hiso,
      (h2 _ _ P P (hP P) (hP P)).2.2.2 hPcm]
    simp [map_ofNat]

/-- **`PeriodMapGlue` at the leaf's own triple (proved).** -/
theorem periodMapGlue_own (h : R1R2fp) (hBC : BaseChangeClassUnique)
    (hPT : PiTwistC (ownY h) (ownΦ h) (ownπ h)) (hTL : QMTwistLattice)
    (hCM : PiCMC (ownY h) (ownΦ h) (ownπ h)) (hCF : CMFixedHasCM) :
    PeriodMapGlue (ownY h) (ownΦ h) (ownπ h) :=
  periodMapGlue_of _ _ _ (own_spec h).1 hBC hPT hTL hCM hCF

/-- **`FibreQMPeriod` with the three targets replaced by their named pieces (proved).** Leaves:
`R1R2fp`, `PkgI1.QMHauptmodul`, T35, T11a, `QMClassNumberOne`, `R1bFamily`,
`ValenceBoundGammaStar`, `CMDescends` (leaf candidate). Glue: `Pin.MobiusGlue` (proved by
mobius-glue), `BaseChangeClassUnique`, `PiTwistC`, `QMTwistLattice`, `S8Nonzero`,
`SphereFactorAffine`, `S8WeightExact`, `CPtsTransport`. -/
theorem fibreQMPeriod_periodMap (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hCN : QMClassNumberOne) (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h))
    (hBC : BaseChangeClassUnique) (hPT : PiTwistC (ownY h) (ownΦ h) (ownπ h))
    (hTL : QMTwistLattice) (hD : CMDescends)
    (hS : PeriodMap.S8Nonzero)
    (hSF : PeriodMap.SphereFactorAffine) (hW : PeriodMap.S8WeightExact)
    (hV : PeriodMap.ValenceBoundGammaStar)
    (hCP : CPtsTransport) : ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_main h hM hH hE hR11 hCN hR
    (periodMapGlue_own h hBC hPT hTL
      (piCMC_of _ _ _ (own_spec h).1 (own_spec h).2.2 hBC hPT hD) (cmFixedHasCM_of hR11))
    (PeriodMap.hauptmodulUnique_of' hS hSF) (PeriodMap.qmDenZeroCM3_of'' hS hW hV) hCP

end HSyn.G0Split.FibreQM.PeriodMapH

end

#print axioms HSyn.G0Split.FibreQM.PeriodMapH.cmFixedHasCM_of
#print axioms HSyn.G0Split.FibreQM.PeriodMapH.periodMapGlue_of
#print axioms HSyn.G0Split.FibreQM.PeriodMapH.piCMC_of
#print axioms HSyn.G0Split.FibreQM.PeriodMapH.periodMapGlue_own
#print axioms HSyn.G0Split.FibreQM.PeriodMapH.fibreQMPeriod_periodMap


/-! ## period-map (heavy part): `PeriodMapGlue` from strictly smaller named Props

Task period-map, 2026-11-13. `PeriodMapGlue Y Φ π` (fibre-qm-period, above, unchanged) is proved
from `R1fpProps Y Φ` (its naturality clause only) and five named Props
(`periodMapGlue_of`); at the leaf's own triple the clause list comes from the bundle
(`periodMapGlue_own`). `CMFixedHasCM` is then proved from T11a (`cmFixedHasCM_of`). The main
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

/-- **`PeriodMapGlue` at the leaf's own triple (proved).** -/
theorem periodMapGlue_own (h : R1R2fp) (hBC : BaseChangeClassUnique)
    (hPT : PiTwistC (ownY h) (ownΦ h) (ownπ h)) (hTL : QMTwistLattice)
    (hCM : PiCMC (ownY h) (ownΦ h) (ownπ h)) (hCF : CMFixedHasCM) :
    PeriodMapGlue (ownY h) (ownΦ h) (ownπ h) :=
  periodMapGlue_of _ _ _ (own_spec h).1 hBC hPT hTL hCM hCF

/-- **`FibreQMPeriod` with the three targets replaced by their named pieces (proved).** Leaves:
`R1R2fp`, `PkgI1.QMHauptmodul`, T35, T11a, `QMClassNumberOne`, `R1bFamily`,
`ValenceBoundGammaStar`. Glue: `Pin.MobiusGlue` (proved by mobius-glue), `BaseChangeClassUnique`,
`PiTwistC`, `QMTwistLattice`, `PiCMC`, `CMFixedHasCM`, `ThetaOmegaAnalytic`, `S8Nonzero`,
`SphereFactorAffine`, `S8Weight8`, `S8OrderCM3`, `CPtsTransport`. -/
theorem fibreQMPeriod_periodMap (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hCN : QMClassNumberOne) (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h))
    (hBC : BaseChangeClassUnique) (hPT : PiTwistC (ownY h) (ownΦ h) (ownπ h))
    (hTL : QMTwistLattice) (hCM : PiCMC (ownY h) (ownΦ h) (ownπ h)) (hCF : CMFixedHasCM)
    (hT : PeriodMap.ThetaOmegaAnalytic) (hS : PeriodMap.S8Nonzero)
    (hSF : PeriodMap.SphereFactorAffine) (hW : PeriodMap.S8Weight8)
    (hO : PeriodMap.S8OrderCM3) (hV : PeriodMap.ValenceBoundGammaStar)
    (hCP : CPtsTransport) : ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_main h hM hH hE hR11 hCN hR (periodMapGlue_own h hBC hPT hTL hCM hCF)
    (PeriodMap.hauptmodulUnique_of hT hS hSF) (PeriodMap.qmDenZeroCM3_of hT hS hW hO hV) hCP

end HSyn.G0Split.FibreQM.PeriodMapH

end

#print axioms HSyn.G0Split.FibreQM.PeriodMapH.periodMapGlue_of
#print axioms HSyn.G0Split.FibreQM.PeriodMapH.periodMapGlue_own
#print axioms HSyn.G0Split.FibreQM.PeriodMapH.fibreQMPeriod_periodMap

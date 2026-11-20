import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveUniformization
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveAbelian
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.GeometricTorsion
import ZInQKernel.Contrib.OneProof.RC.ParamJoin.Cusps
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.AtkinLehner.Sign

/-! The based Abel–Jacobi comparison and the torsion reduction at the
explicitly given rational scale. On the spot (c), tex 1785–1787 and 2937–2943. -/

set_option maxHeartbeats 800000

noncomputable section

open HeckeRing.GL2
open AlgebraicGeometry CategoryTheory Limits Filter MonObj PkgI3 UpperHalfPlane WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
  ZInQ.Contrib.CloudB3RC53.GenusOdd
open scoped Topology

namespace ZInQ.Manuscript.RC.J0Cusps

open PreparedParam

/-- Multiplicativity at complex points is enough to compare the scheme group
with the point law: the underlying coordinate evaluation is already a bijection. -/
def targetPeriodEquiv {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {A : AbVar ℚ} (e : A.X ≅ projectiveTarget E)
    (hAdd : ∀ p q : A.Pt ℂ, projectiveValue (((p * q) ≫ e.hom).left) =
      projectiveValue ((p ≫ e.hom).left) + projectiveValue ((q ≫ e.hom).left))
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) :
    Additive (A.Pt ℂ) ≃+ ℂ ⧸ Lat.lattice.toAddSubgroup := by
  let v (p : Additive (A.Pt ℂ)) := projectiveValue ((p.toMul ≫ e.hom).left)
  have hv : Function.Bijective v := by
    constructor
    · intro p q hpq
      apply Additive.toMul.injective
      apply (cancel_mono e.hom).mp
      exact Over.OverMorphism.ext ((projectiveValue_bijective E ℂ).1 hpq)
    · intro w
      obtain ⟨p, hp⟩ := (projectiveValue_bijective E ℂ).2 w
      let x : AbVar.ptObj (K := ℚ) ℂ ⟶ projectiveTarget E :=
        Over.homMk p (maps_to_rat_unique _ _)
      exact ⟨Additive.ofMul (x ≫ e.inv), by
        change projectiveValue (((x ≫ e.inv) ≫ e.hom).left) = w
        rw [Category.assoc, e.inv_hom_id, Category.comp_id]
        exact hp⟩
  let v' : Additive (A.Pt ℂ) ≃+ (E.baseChange ℂ).toAffine.Point :=
    { Equiv.ofBijective v hv with map_add' := fun p q => hAdd p.toMul q.toMul }
  exact v'.trans (weierstrassPeriodEquiv E Lat hLat).symm

/-- Continuous realization of the point law via the chosen scheme isomorphism. -/
theorem targetPeriodEquiv_lift {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {A : AbVar ℚ} (e : A.X ≅ projectiveTarget E)
    (hAdd : ∀ p q : A.Pt ℂ, projectiveValue (((p * q) ≫ e.hom).left) =
      projectiveValue ((p ≫ e.hom).left) + projectiveValue ((q ≫ e.hom).left))
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (p : A.Pt ℂ) :
    projectiveTorusValue E Lat hLat (Point.map (complexBaseChange.map e.hom) (complexLift p)) =
      targetPeriodEquiv e hAdd Lat hLat (Additive.ofMul p) := by
  rw [← complexLift_comp, projectiveTorusValue_lift]
  rfl

/-- On every finite rational cusp label, the geometric class in the represented
Jacobian maps to its scaled analytic symbol. The at-scale map uses `hr` as an input. -/
theorem algebraicCuspClass_comparison_atScale {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]
    [NeZero (newformLevel (Ecurve ℓ))]
    {f : Newform (newformLevel (Ecurve ℓ)) 2} (hf : PrintsAnalytic.IsNewformOf (Ecurve ℓ) f)
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat)
    {κ : ℂ} (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f.toCuspForm Lat κ)
    (hr : ∃ c : ℚ, (c : ℂ) = κ)
    {A : AbVar ℚ} (e : A.X ≅ projectiveTarget (Ecurve ℓ))
    (hAdd : ∀ p q : A.Pt ℂ, projectiveValue (((p * q) ≫ e.hom).left) =
      projectiveValue ((p ≫ e.hom).left) + projectiveValue ((q ≫ e.hom).left)) :
    ∃ c : ℚ, c ≠ 0 ∧ (c : ℂ) = κ ∧
      ∃ φ : Additive ((J0 (newformLevel (Ecurve ℓ))).Pt Qbar) →+ ℂ ⧸ Lat.lattice.toAddSubgroup,
        ∀ r : ℚ, φ (algebraicCuspClass (newformLevel (Ecurve ℓ)) r) =
          QuotientAddGroup.mk' Lat.lattice.toAddSubgroup
            ((c : ℂ) * ElkikMD.cuspSymbol f.toCuspForm r) := by
  let N := newformLevel (Ecurve ℓ)
  letI : T1Space (ℂ ⧸ Lat.lattice.toAddSubgroup) :=
    QuotientAddGroup.t1Space_iff.mpr Lat.isClosed_lattice
  let f₀ := f.toCuspFormGamma0 hf.1
  have hf₀ : (f₀ : ℍ → ℂ) = (f.toCuspForm : ℍ → ℂ) := f.coe_toCuspFormGamma0 hf.1
  have hcoef : ∀ n : ℕ, 0 < n → (qExpansion 1 f₀).coeff n = ((Ecurve ℓ).LFunction n : ℂ) := by
    intro n hn
    rw [hf₀]
    exact hf.2 n hn
  have hκ₀ : IsParamScale N f₀ Lat κ := hf₀.symm ▸ hκ
  obtain ⟨⟨π, hπ, _, hval⟩, c, hc, hcκ, hzero, hlim⟩ :=
    ParamJoin.algebraicParametrizationAtScale_and_cuspLimits (ℓ := ℓ)
      f₀ hcoef hLat hκ₀ hr
  let π₀ : source N ⟶ projectiveTarget (Ecurve ℓ) := Over.homMk π hπ
  let g : source N ⟶ A.X := π₀ ≫ e.inv
  let v := targetPeriodEquiv e hAdd Lat hLat
  let U := projectiveTorusValue (Ecurve ℓ) Lat hLat ∘ Point.map (complexBaseChange.map e.hom)
  have hU : Continuous U := (continuous_projectiveTorusValue (Ecurve ℓ) Lat hLat).comp (Point.continuous_map _)
  have heval (p : A.Pt ℂ) : U (complexLift p) = v (Additive.ofMul p) :=
    targetPeriodEquiv_lift e hAdd Lat hLat p
  have hchart (τ : ℍ) : U (complexLift (interior N τ ≫ g)) =
      ParamAtScale.torusValue Lat f₀ κ τ := by
    change projectiveTorusValue _ _ _ (Point.map _ (complexLift (interior N τ ≫ g))) = _
    rw [← complexLift_comp, Category.assoc, show g ≫ e.hom = π₀ by simp [g],
      ParamAtScale.torusValue]
    apply projectiveTorusValue_lift_of_eval
    exact hval τ
  have hb : infinity N ≫ g = η[A.X] :=
    Over.OverMorphism.ext
      (cusp_at_infinity_maps_to_unit N g v.toAddMonoidHom v.injective U hU heval
        _ hchart hzero)
  refine ⟨c, hc, hcκ, ?_⟩
  simpa only [hf₀] using cusp_comparison N g hb v.toAddMonoidHom U hU heval _ _ hchart hlim

/-- The Elkik consequence with its geometric inputs supplied by the represented
Jacobian and the at-scale comparison of the fixed target. -/
theorem hElkikMD_atScale_of_geometricTorsion {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {d : ℤ}
    [NeZero (newformLevel (Ecurve ℓ))]
    (hElkik : ElkikPrint.ManinDrinfeldTorsion (newformLevel (Ecurve ℓ))
      (algebraicCuspClass (newformLevel (Ecurve ℓ))))
    {f : Newform (newformLevel (Ecurve ℓ)) 2} (hf : PrintsAnalytic.IsNewformOf (Ecurve ℓ) f)
    (hgp : GenusPartner (Ecurve ℓ) d) {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat)
    {κ : ℂ} (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f.toCuspForm Lat κ)
    (hr : ∃ c : ℚ, (c : ℂ) = κ)
    {A : AbVar ℚ} (e : A.X ≅ projectiveTarget (Ecurve ℓ))
    (hAdd : ∀ p q : A.Pt ℂ, projectiveValue (((p * q) ≫ e.hom).left) =
      projectiveValue ((p ≫ e.hom).left) + projectiveValue ((q ≫ e.hom).left)) :
    ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar (Ecurve ℓ) Lat d := by
  obtain ⟨c, hc, _, φ, hφ⟩ := algebraicCuspClass_comparison_atScale hf hLat hκ hr e hAdd
  exact hElkikMD_of_geometricTorsion hElkik hf hgp Lat hc φ (fun a _ _ => hφ _)

/-- On the indicated Proj, a scheme group law inducing the Weierstrass
point law supplies the last target input to the Elkik comparison. -/
theorem hElkikMD_atScale_of_projectiveGroup {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {d : ℤ}
    [NeZero (newformLevel (Ecurve ℓ))]
    [GrpObj (projectiveTarget (Ecurve ℓ))]
    (hAdd : ∀ p q : AbVar.ptObj (K := ℚ) ℂ ⟶ projectiveTarget (Ecurve ℓ),
      projectiveValue (p * q).left = projectiveValue p.left + projectiveValue q.left)
    (hElkik : ElkikPrint.ManinDrinfeldTorsion (newformLevel (Ecurve ℓ))
      (algebraicCuspClass (newformLevel (Ecurve ℓ))))
    {f : Newform (newformLevel (Ecurve ℓ)) 2} (hf : PrintsAnalytic.IsNewformOf (Ecurve ℓ) f)
    (hgp : GenusPartner (Ecurve ℓ) d) {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat)
    {κ : ℂ} (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f.toCuspForm Lat κ)
    (hr : ∃ c : ℚ, (c : ℂ) = κ) :
    ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar (Ecurve ℓ) Lat d := by
  apply hElkikMD_atScale_of_geometricTorsion hElkik hf hgp hLat hκ hr
    (A := projectiveAbVar (Ecurve ℓ)) (Iso.refl _)
  intro p q
  simp only [Iso.refl_hom]
  exact hAdd p q


end ZInQ.Manuscript.RC.J0Cusps

import ZInQKernel.Contrib.OneProof.RC.PMWire.Operators
import ZInQKernel.Contrib.OneProof.RC.PMWire.MovingCusp
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.WeightedComparison

/-! Tex 2937–2942, 8282–8297, and 8487–8489. Apply the existing Elkik
print to the represented geometric classes. The factorization and the
comparison with the reduction of the rational section are glue (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory CartesianMonoidalCategory Limits PkgI3 WeierstrassCurve
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 350000

namespace ZInQ.Manuscript.RC.PMWire

open GoodReduction (generic)
open PMQuotient (residueUnit)
open PreparedParam

namespace GoodRow

variable {R : Type} [CommRing R] [Algebra R ℚ]
  {ell N : ℕ} [Fact ell.Prime] [NeZero N] {K : Type} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
  {Ebar : WeierstrassCurve (ZMod ell)} {X : PMAdelic.CoarseFibre}
  {E₀ : WeierstrassCurve ℚ} [E₀.IsElliptic] {π : rationalSource N ⟶ ellipticTarget E₀}
  (G : GoodRow R ell N K Ebar X π)

/-- The basedness needed by the Albanese factor is entirely rational.
Witnesses to the reduced zero section on the modular source are unnecessary. -/
theorem based
    (hzero : projectiveValue ((AtkinPin.infinityPoint N).val ≫ π.left) = 0) :
    J0Cusps.infinity N ≫ G.φ = η[G.genericE] := by
  let k : complexBase ⟶ 𝟙_ (Over (Spec (.of ℚ))) := toUnit _
  have hk : k.left = Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)) := Over.w k
  have hdom : IsDominant k.left := ⟨by
    intro y
    let z := IsLocalRing.closedPoint ℂ
    rw [Subsingleton.elim y (k.left z)]
    exact subset_closure (Set.mem_range_self z)⟩
  have hv : (G.readComplex (k ≫ (J0Cusps.infinity N ≫ G.φ))).toAdd = 0 := by
    rw [G.readComplex_eq]
    have hφ : G.φ ≫ G.jE.hom = π := by simp [φ]
    have hj : (J0Cusps.infinity N ≫ G.φ).left ≫ G.jE.hom.left =
        (J0Cusps.infinity N ≫ π).left :=
      congrArg CommaMorphism.left ((Category.assoc _ _ _).trans
        (congrArg (fun t => J0Cusps.infinity N ≫ t) hφ))
    change projectiveValue (k.left ≫ (J0Cusps.infinity N ≫ G.φ).left ≫ G.jE.hom.left) = 0
    rw [hj, hk]
    change projectiveValue
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)) ≫
        ((AtkinPin.infinityPoint N).val ≫ π.left)) = 0
    exact (projectiveValue_map (E := E₀) (Algebra.ofId ℚ ℂ) _).symm.trans
      (by rw [hzero, map_zero])
  have hh : k ≫ (J0Cusps.infinity N ≫ G.φ) = k ≫ η[G.genericE] := by
    apply Over.OverMorphism.ext
    apply (cancel_mono G.jE.hom.left).mp
    apply AtkinRational.projectiveValue_injective_of_origin E₀
      ((AtkinPin.infinityPoint N).val ≫ π.left) hzero
    have hkone : k ≫ η[G.genericE] = 1 := rfl
    rw [← G.readComplex_eq, ← G.readComplex_eq, hv, hkone, map_one]
    rfl
  have : IsReduced (𝟙_ (Over (Spec (.of ℚ)))).left :=
    inferInstanceAs (IsReduced (Spec (.of ℚ)))
  ext1
  exact ext_of_isDominant_of_isSeparated G.genericE.hom ((Over.w _).trans (Over.w _).symm)
    k.left (congrArg CommaMorphism.left hh)

/-- The represented Abel–Jacobi factor of the same map on geometric points. -/
def cuspPhi (hb : J0Cusps.infinity N ≫ G.φ = η[G.genericE]) :
    Additive ((J0Cusps.J0 N).Pt J0Cusps.Qbar) →+ Additive (G.abVar.Pt J0Cusps.Qbar) :=
  let g := J0Cusps.factor (A := G.abVar) (J0Cusps.isJacobian_aj0 N) G.φ hb
  letI : IsMonHom g := J0Cusps.factor_isMonHom (A := G.abVar) (J0Cusps.isJacobian_aj0 N) G.φ hb
  J0Cusps.torusHom g (AddMonoidHom.id _)

/-- Base extension on the rational sections of the elliptic model. -/
def geometricValue : Additive ((𝟙_ (Over (Spec (.of ℚ)))) ⟶ G.genericE) →+
    Additive (G.abVar.Pt J0Cusps.Qbar) :=
  ({ toFun := fun t => toUnit (AbVar.ptObj (K := ℚ) J0Cusps.Qbar) ≫ t
     map_one' := MonObj.comp_one _
     map_mul' := fun t u => MonObj.comp_mul _ t u } :
    ((𝟙_ (Over (Spec (.of ℚ)))) ⟶ G.genericE) →* G.abVar.Pt J0Cusps.Qbar).toAdditive

theorem geometricValue_injective : Function.Injective G.geometricValue := by
  intro t u h
  let k := toUnit (AbVar.ptObj (K := ℚ) J0Cusps.Qbar)
  have : IsDominant k.left := ⟨by
    intro y
    let z := IsLocalRing.closedPoint J0Cusps.Qbar
    rw [Subsingleton.elim y (k.left z)]
    exact subset_closure (Set.mem_range_self z)⟩
  have : IsReduced (𝟙_ (Over (Spec (.of ℚ)))).left :=
    inferInstanceAs (IsReduced (Spec (.of ℚ)))
  apply Additive.toMul.injective
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated G.genericE.hom ((Over.w t.toMul).trans (Over.w u.toMul).symm)
    k.left (congrArg (fun v => v.toMul.left) h)

/-- Define the map out of the represented Jacobian by the universal
property and apply Elkik's existing print to the actual cusp class. -/
theorem translation_torsion (hb : J0Cusps.infinity N ≫ G.φ = η[G.genericE])
    (pin : MovingCusps N) (elkik : ElkikPrint.ManinDrinfeldTorsion N (J0Cusps.algebraicCuspClass N))
    (q : ℕ) (hq : q.Prime) (he : 0 < N.factorization q) :
    IsOfFinAddOrder (Additive.ofMul (G.translationQ q)) := by
  obtain ⟨r, hr⟩ := pin q hq he
  obtain ⟨n, hn, ht⟩ := elkik r
  have hφ : G.cuspPhi hb (J0Cusps.algebraicCuspClass N r) =
      G.geometricValue (Additive.ofMul (G.translationQ q)) := by
    let g := J0Cusps.factor (A := G.abVar) (J0Cusps.isJacobian_aj0 N) G.φ hb
    let : IsMonHom g := J0Cusps.factor_isMonHom (A := G.abVar) (J0Cusps.isJacobian_aj0 N) G.φ hb
    have hg := J0Cusps.abelJacobi_comp_factor (A := G.abVar) (J0Cusps.isJacobian_aj0 N) G.φ hb
    change J0Cusps.torusHom g (AddMonoidHom.id _)
      (J0Cusps.pointClass (J0Cusps.aj0 N) (J0Cusps.algebraicCusp N (ElkikPrint.cuspOrbit N r))) = _
    rw [J0Cusps.torusHom_pointClass g hg, hr]
    apply congrArg Additive.ofMul
    apply Over.OverMorphism.ext
    let a := Spec.map (CommRingCat.ofHom (algebraMap ℚ J0Cusps.Qbar))
    let b := (J0Cusps.infinity N).left
    let c := (rationalW N q).left
    let d := G.φ.left
    change (a ≫ (b ≫ c)) ≫ d = a ≫ b ≫ c ≫ d
    exact (Category.assoc a (b ≫ c) d).trans (congrArg (fun t => a ≫ t) (Category.assoc b c d))
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, G.geometricValue_injective ?_⟩
  rw [map_nsmul, ← hφ, ← map_nsmul, ht, map_zero, map_zero]

/-- The part of the multiplier choice at tex 8295–8297 needed by this row. -/
def KillsTranslation (L : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → 0 < N.factorization q →
    IsOfFinAddOrder (Additive.ofMul (G.translationQ q)) →
    L • Additive.ofMul (G.translationQ q) = 0

/-- The fixed multiplier kills the same translation used in the affine
specialization. The Néron extension and reduction preserve the group law. -/
theorem translation_killed {L : ℕ} (kills : G.KillsTranslation L)
    (hb : J0Cusps.infinity N ≫ G.φ = η[G.genericE])
    (pin : MovingCusps N) (elkik : ElkikPrint.ManinDrinfeldTorsion N (J0Cusps.algebraicCuspClass N))
    (q : ℕ) (hq : q.Prime) (he : 0 < N.factorization q) :
    L • G.translation q = 0 := by
  have ht := kills q hq he (G.translation_torsion hb pin elkik q hq he)
  let : Smooth (𝟙_ (Over (Spec (.of R)))).hom := by
    change Smooth (𝟙 (Spec (.of R)))
    infer_instance
  have hi : G.translationInt q ^ L = 1 := by
    apply (G.neron.2.2.2.2 _).injective
    let gen := (generic R ℚ).homMonoidHom (X := 𝟙_ (Over (Spec (.of R)))) (M := G.E)
    change gen (G.translationInt q ^ L) = gen 1
    rw [map_pow, map_one]
    change ((generic R ℚ).map (G.translationInt q)) ^ L = 1
    let k : (generic R ℚ).obj (𝟙_ (Over (Spec (.of R)))) ⟶ 𝟙_ (Over (Spec (.of ℚ))) := toUnit _
    let premul : ((𝟙_ (Over (Spec (.of ℚ)))) ⟶ G.genericE) →*
        ((generic R ℚ).obj (𝟙_ (Over (Spec (.of R)))) ⟶ G.genericE) :=
      { toFun := fun t => k ≫ t
        map_one' := MonObj.comp_one _
        map_mul' := fun t u => MonObj.comp_mul _ t u }
    rw [G.translationInt_generic]
    change premul (G.translationQ q) ^ L = 1
    rw [← map_pow, show G.translationQ q ^ L = 1 from ht, map_one]
  apply Subtype.ext
  let red := G.readAt (residueUnit G.closed)
  change ((red (G.translationInt q)) ^ L).toAdd = (1 : Multiplicative _).toAdd
  rw [← map_pow, hi, map_one]


end GoodRow
end ZInQ.Manuscript.RC.PMWire

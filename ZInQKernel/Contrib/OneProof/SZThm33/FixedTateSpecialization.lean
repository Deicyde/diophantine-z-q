import ZInQKernel.Contrib.OneProof.SZThm33.ModelTateEmbedding
import ZInQKernel.Contrib.OneProof.SZThm33.FixedTorsionDescent
import ZInQKernel.Contrib.OneProof.SZThm33.NeronSections
import ZInQKernel.Contrib.OneProof.NeronBaseChangeStrictHenselization

/-!
# Geometric residue Tate towers exhaust absolute inertia invariants

This holds for the given Néron model and the specified prolongation of the
valuation over arbitrary residue fields.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit ReductGlue
open ZInQ.Contrib.AbVarBC
open ZInQ.FaltingsRestate (isCommMonObj_groupModelO)

namespace SZRaynaud.Ambient

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {O : ValuationSubring K} [IsDiscreteValuationRing O] {w : ValuationSubring Ω}
  (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K) (M : GroupModelO A O)

private def sectionToPoint :
    (Over.mk (base hw) ⟶ M.G) →* A.Pt Ω :=
  (genPtHom hw A M).comp (SmoothGroup.restrictPoint (gen (w := w)))

omit [IsAlgClosure K Ω] [IsDiscreteValuationRing O] in
private theorem sectionToPoint_injective : Function.Injective (sectionToPoint hw A M) := by
  intro s t h
  have hh := genPtHom_injective hw A M h
  apply Over.OverMorphism.ext
  have := isDominant_gen (w := w)
  have : IsReduced (Over.mk (base hw)).left := inferInstanceAs (IsReduced (Spec (.of w)))
  exact ext_of_isDominant_of_isSeparated M.G.hom (s.w.trans t.w.symm) (gen (w := w))
    (congrArg Over.Hom.left hh)

/-- A rational point over the strict henselization field extends to a
section over the given prolongation in the algebraic closure. -/
theorem exists_section_of_inertiaField_point (hN : M.IsNeronModel)
    (y : A.Pt (GapSHPair.inertiaField (K := K) w)) :
    ∃ s : Over.mk (base hw) ⟶ M.G,
      sectionToPoint hw A M s = extPt A (GapSHPair.inertiaField (K := K) w).val y := by
  let E := GapSHPair.inertiaField (K := K) w
  let v := GapSHPair.wE (K := K) w
  let hv := GapSHPair.hE_eq w hw
  let ks := Spec.map (CommRingCat.ofHom (algebraMap E Ω))
  let vs := Spec.map (CommRingCat.ofHom (GapSHPair.ιw (K := K) w))
  let B := gD hv
  have hB : B = base hv := rfl
  have hb : vs ≫ B = base hw := by
    rw [← Spec.map_comp]
    rfl
  have hg : gen (w := w) ≫ vs = ks ≫ jO v := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have he : ks ≫ (gen (w := v) ≫ base hv) = gen (w := w) ≫ base hw := by
    rw [← Category.assoc, show gen (w := v) = jO v from rfl, ← hg, Category.assoc, ← hB, hb]
  obtain ⟨z, hzy⟩ := genPtHom_surjective hv A M y
  let M' := bcDVR hv M
  have hM' : M'.IsNeronModel :=
    NeronSH.neronBaseChangeStrictHenselization_proof K O E v hv
      (GapSHPair.isSHSep_inertia w hw) A M hN
  have hz : z.left ≫ M.G.hom = jO v ≫ B := z.w
  let z' : Spec (.of E) ⟶ M'.G.left := pullback.lift z.left (jO v) hz
  have hz' : z' ≫ M'.G.hom = jO v := pullback.lift_snd _ _ _
  obtain ⟨s', hs'B, hs'⟩ := exists_section_of_neron M' hM' z' hz'
  let π : M'.G.left ⟶ M.G.left := pullback.fst M.G.hom B
  have hπ : π ≫ M.G.hom = M'.G.hom ≫ B := pullback.condition
  have hs'π : jO v ≫ s' ≫ π = z.left := by
    rw [← Category.assoc, hs']
    exact pullback.lift_fst _ _ _
  let s : Over.mk (base hw) ⟶ M.G := Over.homMk (vs ≫ s' ≫ π) (by
    rw [Category.assoc, Category.assoc, hπ, ← Category.assoc s', hs'B,
      Category.id_comp, hb]
    rfl)
  have hres : SmoothGroup.restrictPoint (gen (w := w)) s =
      (Over.homMk _ he : Over.mk (gen (w := w) ≫ base hw) ⟶
        Over.mk (gen (w := v) ≫ base hv)) ≫ z := by
    apply Over.OverMorphism.ext
    change gen (w := w) ≫ vs ≫ s' ≫ π = ks ≫ z.left
    rw [← Category.assoc (gen (w := w)), hg, Category.assoc, hs'π]
  refine ⟨s, ?_⟩
  change genPtHom hw A M (SmoothGroup.restrictPoint (gen (w := w)) s) = _
  rw [hres]
  exact (genPtHom_extPt hw A M hv E.val z he).trans (congrArg (extPt A E.val) hzy)

variable [IsAlgClosed Ω] {ℓ : ℕ} [Fact ℓ.Prime] (hu : IsUnit (ℓ : O))

local instance : IsCommMonObj M.G := isCommMonObj_groupModelO M

/-- The Tate module of the geometric special fibre maps onto the
absolute inertia invariants of the geometric generic Tate module. -/
theorem exists_modelEmbedTate_of_inertia_fixed (hN : M.IsNeronModel)
    (t : TΩ A Ω ℓ)
    (ht : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → galTΩ A ℓ σ t = t) :
    ∃ y : PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hw) ⟶ M.G)),
      modelEmbedTate hw A M hu y = t := by
  have hℓK : (ℓ : K) ≠ 0 := by
    exact (show IsUnit (O.subtype (ℓ : O)) from hu.map O.subtype).ne_zero
  let x (n : ℕ) : A.Pt Ω := Additive.toMul (t.1 n)
  have hx (n : ℕ) : x n ^ (ℓ ^ n) = 1 := pow_smul_tate t n
  have hxfix (n : ℕ) (σ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ) :
      A.galAct σ (x n) = x n :=
    congrArg (fun t : TΩ A Ω ℓ => Additive.toMul (t.1 n)) (ht σ hσ)
  choose y hy using fun n => exists_torsion_point_over_inertiaField w A (ℓ ^ n)
    (by simpa only [Nat.cast_pow] using pow_ne_zero n hℓK) (x n) (hx n) (hxfix n)
  choose s hs using fun n => exists_section_of_inertiaField_point hw A M hN (y n)
  let r := sectionToPoint hw A M
  have hsr (n : ℕ) : r (s n) = x n := (hs n).trans (hy n).2
  have hs0 : s 0 = 1 := by
    apply sectionToPoint_injective hw A M
    change r (s 0) = r 1
    rw [hsr, map_one]
    exact t.2.1
  have hsc (n : ℕ) : s (n + 1) ^ ℓ = s n := by
    apply sectionToPoint_injective hw A M
    change r (s (n + 1) ^ ℓ) = r (s n)
    rw [map_pow, hsr, hsr]
    exact t.2.2 n
  let z : PkgI3.Tate.T ℓ (Additive (Over.mk (base hw) ⟶ M.G)) :=
    ⟨fun n => Additive.ofMul (s n), hs0, hsc⟩
  refine ⟨SmoothGroup.restrictTate res z, ?_⟩
  have := henselianLocalRing_of_valuationSubring w
  let e := LinearEquiv.ofBijective _ (SmoothGroup.restrictTate_bijective_of_residue
    (X := M.G) (ℓ := ℓ) (base hw) hu)
  change PkgI3.Tate.map (genPtHom hw A M).toAdditive
    (SmoothGroup.restrictTate (gen (w := w)) (e.symm (e z))) = t
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  funext n
  exact congrArg Additive.ofMul (hsr n)

#print axioms exists_section_of_inertiaField_point
#print axioms exists_modelEmbedTate_of_inertia_fixed

end SZRaynaud.Ambient

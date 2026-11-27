import ZInQKernel.Contrib.OneProof.ShimuraGoodReductionNoGuard
import ZInQKernel.Contrib.OneProof.ShimuraY3PrintedLeaves
import ZInQKernel.Contrib.OneProof.Y3FullThreeZ30
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.OverPullbackMonoid
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.BuzzardLeaves
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open PkgI3
open scoped CategoryTheory.Obj

/-!
# Points of a level-three family: the geometric-point dictionary

For a geometric point `s : Spec k ⟶ S` and a monoid object `M` over `S` we identify
`Over.mk s ⟶ M` multiplicatively with `ptObj k ⟶ (Over.pullback s).obj M`, compute the image
of a section, and deduce that the printed level condition is the generator condition at
every geometric point, for the point `s ≫ eta 1`.

Helper lemmas take the monoid structure as an ordinary implicit argument `{inst : MonObj M}`,
so that it is read off the goal by unification and no instance search is needed for the
group structure of a family.
-/

/- Same local instances as in the pullback-monoid file: convolution monoid on hom-sets,
monoid object structure on the image under a monoidal functor, cartesian and braided
structure on over categories. -/
attribute [local instance] CategoryTheory.Hom.monoid CategoryTheory.Functor.monObjObj
  CategoryTheory.Over.cartesianMonoidalCategory CategoryTheory.Over.braidedCategory

namespace Y3Fix.G0Dictionary

variable {S : Scheme.{0}}

/-! ## 1. The dictionary -/

/-- `Over.map s` sends the point object over `Spec k` to `Over.mk s`, with identity
underlying map, because the point object has identity structure map. -/
def mapPtIso {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ S) :
    (Over.map s).obj (AbVar.ptObj (K := k) k) ≅ Over.mk s :=
  Over.isoMk (Iso.refl _) (by simp [Over.map_obj_hom, SGRSplit.ptObj_hom_self])

/-- Points `Over.mk s ⟶ M` correspond multiplicatively to morphisms from the point object
into the pullback of `M` along `s`. -/
def pointDict {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ S) (M : Over S) [MonObj M] :
    (Over.mk s ⟶ M) ≃* (AbVar.ptObj (K := k) k ⟶ (Over.pullback s).obj M) :=
  (Y3OverPullbackMonoid.precompMulEquiv (mapPtIso s)).trans
    (Y3OverPullbackMonoid.homMulEquiv s (AbVar.ptObj (K := k) k) M)

theorem pointDict_apply {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ S) (M : Over S)
    [MonObj M] (u : Over.mk s ⟶ M) :
    pointDict s M u =
      (Over.mapPullbackAdj s).homEquiv (AbVar.ptObj (K := k) k) M ((mapPtIso s).hom ≫ u) :=
  rfl

/-! ## 2. The image of a section -/

/-- The unit of `Over.map f ⊣ Over.pullback f`, followed by the first projection, is the
identity. -/
theorem unit_left_fst {X Y : Scheme.{0}} (f : X ⟶ Y) (A : Over X) {Z : Scheme.{0}}
    (h : A.left ⟶ Z) :
    ((Over.mapPullbackAdj f).unit.app A).left ≫ pullback.fst ((Over.map f).obj A).hom f ≫ h =
      h := by
  first
  | simp
  | simp [Over.mapPullbackAdj]

theorem homMk_w {W : Scheme.{0}} (s : W ⟶ S) {M : Over S} (e : S ⟶ M.left)
    (he : e ≫ M.hom = 𝟙 S) : (s ≫ e) ≫ M.hom = (Over.mk s).hom := by
  show (s ≫ e) ≫ M.hom = s
  rw [Category.assoc, he, Category.comp_id]

theorem pointDict_homMk {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ S) (M : Over S)
    {inst : MonObj M} (e : S ⟶ M.left) (he : e ≫ M.hom = 𝟙 S) :
    pointDict s M (Over.homMk (U := Over.mk s) (s ≫ e) (homMk_w s e he)) =
      SGRSplit.cpt s ≫ (Over.pullback s).map (Over.homMk (U := 𝟙_ (Over S)) e he) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hR : (SGRSplit.cpt s ≫ (Over.pullback s).map
        (Over.homMk (U := 𝟙_ (Over S)) e he)).left ≫ pullback.fst M.hom s = s ≫ e := by
      rw [Over.comp_left, Category.assoc, SGRSplit.map_left_fst, ← Category.assoc,
        SGRSplit.cpt_fst]
      all_goals rfl
    have hL : (pointDict s M (Over.homMk (U := Over.mk s) (s ≫ e) (homMk_w s e he))).left ≫
        pullback.fst M.hom s = s ≫ e := by
      rw [pointDict_apply, Y3OverPullbackMonoid.homEquiv_eq, Over.comp_left, Category.assoc,
        SGRSplit.map_left_fst, unit_left_fst]
      exact Category.id_comp (s ≫ e)
    rw [hL, hR]
  · exact (Over.w (pointDict s M (Over.homMk (U := Over.mk s) (s ≫ e) (homMk_w s e he)))).trans
      (Over.w (SGRSplit.cpt s ≫ (Over.pullback s).map
        (Over.homMk (U := 𝟙_ (Over S)) e he))).symm

/-! ## 3. Unit, powers, and the level condition -/

/-- The unit of `Over.mk s ⟶ M` has underlying map `s ≫ η.left`. -/
theorem one_left {W : Scheme.{0}} (s : W ⟶ S) {M : Over S} {inst : MonObj M} :
    (1 : Over.mk s ⟶ M).left = s ≫ η[M].left := by
  have h : (toUnit (Over.mk s)).left = s := by
    have h0 := Over.w (toUnit (Over.mk s))
    rw [Over.tensorUnit_hom] at h0
    exact (Category.comp_id _).symm.trans h0
  exact congrArg (fun z => z ≫ η[M].left) h

theorem homMk_eq_one_iff {W : Scheme.{0}} (s : W ⟶ S) {M : Over S} {inst : MonObj M}
    (e : S ⟶ M.left) (he : e ≫ M.hom = 𝟙 S) :
    (Over.homMk (U := Over.mk s) (s ≫ e) (homMk_w s e he) : Over.mk s ⟶ M) = 1 ↔
      s ≫ e = s ≫ η[M].left := by
  rw [← one_left s]
  constructor
  · intro h
    exact congrArg (fun z : Over.mk s ⟶ M => z.left) h
  · intro h
    exact Over.OverMorphism.ext h

/-- Torsion points transport along the dictionary. -/
theorem torsion_transport {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ S) {M : Over S}
    {inst : MonObj M} (g : O → (Over.mk s ⟶ M)) :
    (∀ x : AbVar.ptObj (K := k) k ⟶ (Over.pullback s).obj M, x ^ 3 = 1 →
        ∃ a : O, x = pointDict s M (g a)) ↔
      ∀ x : Over.mk s ⟶ M, x ^ 3 = 1 → ∃ a : O, x = g a := by
  constructor
  · intro h x hx
    obtain ⟨a, ha⟩ := h (pointDict s M x) (by rw [← map_pow, hx, map_one])
    exact ⟨a, (pointDict s M).injective ha⟩
  · intro h y hy
    obtain ⟨a, ha⟩ := h ((pointDict s M).symm y) (by rw [← map_pow, hy, map_one])
    exact ⟨a, by rw [← ha, MulEquiv.apply_symm_apply]⟩

/-- The point `s ≫ eta a` of a family. -/
theorem etaPt_w (𝒜 : QMAbSchemeNL S) {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ S)
    (a : O) : (s ≫ 𝒜.eta a) ≫ 𝒜.F.hom = (Over.mk s).hom :=
  homMk_w s (𝒜.eta a) (𝒜.eta_sec a)

def etaPt (𝒜 : QMAbSchemeNL S) {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ S)
    (a : O) : Over.mk s ⟶ 𝒜.F :=
  Over.homMk (U := Over.mk s) (s ≫ 𝒜.eta a) (etaPt_w 𝒜 s a)

/-- `O`-linearity of `eta` at `b = 1`. -/
theorem etaPt_comp_iota (𝒜 : QMAbSchemeNL S) {k : Type} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ S) (a : O) :
    etaPt 𝒜 s 1 ≫ (Over.homMk (𝒜.iota a) (𝒜.iota_over a) : 𝒜.F ⟶ 𝒜.F) = etaPt 𝒜 s a := by
  apply Over.OverMorphism.ext
  show (s ≫ 𝒜.eta 1) ≫ 𝒜.iota a = s ≫ 𝒜.eta a
  rw [Category.assoc, ← 𝒜.eta_linear, _root_.mul_one]

theorem etaPt_iota_eq_one_iff (𝒜 : QMAbSchemeNL S) {k : Type} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ S) (a : O) :
    letI := 𝒜.grp
    etaPt 𝒜 s 1 ≫ (Over.homMk (𝒜.iota a) (𝒜.iota_over a) : 𝒜.F ⟶ 𝒜.F) = 1 ↔
      s ≫ 𝒜.eta a = s ≫ 𝒜.eta 0 := by
  rw [etaPt_comp_iota]
  exact (homMk_eq_one_iff s (𝒜.eta a) (𝒜.eta_sec a)).trans (by rw [𝒜.one_eq])

theorem cpt_secF_eq (𝒜 : QMAbSchemeNL S) {k : Type} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ S) (a : O) :
    letI := 𝒜.grp
    SGRSplit.cpt s ≫ (Over.pullback s).map (secF 𝒜.toQMFamily a) =
      pointDict s 𝒜.F (etaPt 𝒜 s 1 ≫ (Over.homMk (𝒜.iota a) (𝒜.iota_over a) : 𝒜.F ⟶ 𝒜.F)) := by
  rw [etaPt_comp_iota]
  exact (pointDict_homMk s 𝒜.F (𝒜.eta a) (𝒜.eta_sec a)).symm

/-- The generator condition, restated for the family itself. -/
theorem isGenAt_toFEC_iff (𝒜 : QMAbSchemeNL S) {k : Type} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ S) (P : Over.mk s ⟶ 𝒜.F) :
    Y3Buzzard.IsGenAt 3 𝒜.toFEC s P ↔
      letI := 𝒜.grp
      (∀ a : O, P ≫ (Over.homMk (𝒜.iota a) (𝒜.iota_over a) : 𝒜.F ⟶ 𝒜.F) = 1 ↔
          ∃ b : O, a = ((3 : ℕ) : O) * b) ∧
        ∀ x : Over.mk s ⟶ 𝒜.F, x ^ 3 = 1 →
          ∃ a : O, x = P ≫ (Over.homMk (𝒜.iota a) (𝒜.iota_over a) : 𝒜.F ⟶ 𝒜.F) :=
  Iff.rfl

theorem levelPrint_iff_isGenAt (𝒜 : QMAbSchemeNL S) :
    LevelPrint 𝒜 ↔ ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S),
      Y3Buzzard.IsGenAt 3 𝒜.toFEC s (Over.homMk (s ≫ 𝒜.eta 1) (etaPt_w 𝒜 s 1)) := by
  unfold Y3Fix.LevelPrint
  refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun s => ?_
  refine Iff.trans ?_ (isGenAt_toFEC_iff 𝒜 s (etaPt 𝒜 s 1)).symm
  refine and_congr (forall_congr' fun a => ?_) ?_
  · rw [etaPt_iota_eq_one_iff, Nat.cast_ofNat]
    all_goals exact Iff.rfl
  · simp only [cpt_secF_eq]
    exact torsion_transport s _

end Y3Fix.G0Dictionary

import ZInQKernel.OneProof.H.TailW
import ZInQKernel.OneProof.H.TailZ16

noncomputable section

namespace SGRG1

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid PkgI3
open scoped CategoryTheory.Obj

def QMAbFieldFibre : Prop :=
  ∀ (S : Scheme.{0}) (𝒜 : QMAbScheme S) (K : Type) [Field K] [Algebra ℚ K]
    (y : Spec (CommRingCat.of K) ⟶ S), ∃ P : QML3 K, IsFibreOf 𝒜.toQMFamily y P

/-- L1. -/
def SmoothGeomConnIntegral : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)), Smooth f →
    GeometricallyConnected f → GeometricallyIntegral f

/-- L2. -/
def AbVarEndTorsionFree : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ) (f : AbVar.End A), 0 < n → n • f = 0 → f = 0

theorem ptObj_hom_self (K : Type) [Field K] : (AbVar.ptObj (K := K) K).hom = 𝟙 _ := by
  simp [AbVar.ptObj, Algebra.algebraMap_self]

section
variable {S : Scheme.{0}} (𝒜 : QMAbScheme S) {K : Type} [Field K] (y : Spec (CommRingCat.of K) ⟶ S)

/-- The family as an object of `Over S` with its group law. -/
abbrev FF : Over S := 𝒜.F

/-- The sections `η(a)` as maps from the unit. -/
def sec (a : O) : 𝟙_ (Over S) ⟶ 𝒜.F := Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta a) (𝒜.eta_sec a)

/-- `ι(a)` as an `Over` endomorphism. -/
def fa (a : O) : 𝒜.F ⟶ 𝒜.F := Over.homMk (𝒜.iota a) (𝒜.iota_over a)

/-- The comparison `Spec K → y^*𝟙`. -/
def cpt : AbVar.ptObj (K := K) K ⟶ (Over.pullback y).obj (𝟙_ (Over S)) :=
  Over.homMk (pullback.lift y (AbVar.ptObj (K := K) K).hom (by
    rw [ptObj_hom_self]; simp only [Over.tensorUnit_hom]
    exact (Category.id_comp y).symm)) (pullback.lift_snd _ _ _)

theorem cpt_fst : (cpt y).left ≫ pullback.fst (𝟙_ (Over S)).hom y = y := pullback.lift_fst _ _ _

theorem map_left_fst {X Z : Over S} (u : X ⟶ Z) :
    ((Over.pullback y).map u).left ≫ pullback.fst Z.hom y = pullback.fst X.hom y ≫ u.left := by
  simp [Over.pullback_map_left]

end

theorem int_eq_zero_of_forall_dvd (z : ℤ) (h : ∀ k : ℕ, (3 : ℤ) ^ k ∣ z) : z = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h z.natAbs)
  rw [Int.natAbs_pow]
  exact Nat.lt_pow_self (by norm_num)

theorem pow_three_mul_ofInt (k : ℕ) (m : Fin 4 → ℤ) :
    (3 : B) ^ k * ofInt m = ofInt (fun i => 3 ^ k * m i) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', _root_.mul_assoc, ih, three_mul_ofInt]
    congr 1; funext i; ring

theorem O_eq_zero_of_forall_dvd (c : O) (h : ∀ k : ℕ, ∃ d : O, c = 3 ^ k * d) : c = 0 := by
  obtain ⟨n, hn⟩ := c.2
  have hn0 : n = 0 := by
    funext i
    apply int_eq_zero_of_forall_dvd
    intro k
    obtain ⟨d, hd⟩ := h k
    obtain ⟨m, hm⟩ := d.2
    have : ofInt n = ofInt (fun i => 3 ^ k * m i) := by
      rw [← hn, ← pow_three_mul_ofInt, ← hm, hd]
      push_cast; rfl
    exact ⟨m i, congrFun (ofInt_injective this) i⟩
  apply Subtype.ext
  rw [hn, hn0]
  exact ofInt_zero


/-- The fibre of a QM abelian scheme at a field point, as an abelian variety (given `SmoothGeomConnIntegral`). -/
def fibreAbVar (hI : SmoothGeomConnIntegral) {S : Scheme.{0}} (𝒜 : QMAbScheme S) {K : Type} [Field K]
    (y : Spec (CommRingCat.of K) ⟶ S) : AbVar K :=
  letI := 𝒜.grp
  have := 𝒜.proper
  have := 𝒜.smooth
  have := 𝒜.geomConn
  have : IsProper ((Over.pullback y).obj 𝒜.F).hom := by dsimp; infer_instance
  have : SmoothOfRelativeDimension 2 ((Over.pullback y).obj 𝒜.F).hom := by dsimp; infer_instance
  have : Smooth ((Over.pullback y).obj 𝒜.F).hom := SmoothOfRelativeDimension.smooth 2 _
  have : GeometricallyConnected ((Over.pullback y).obj 𝒜.F).hom := by dsimp; infer_instance
  have : GeometricallyIntegral ((Over.pullback y).obj 𝒜.F).hom :=
    hI K _ _ inferInstance inferInstance
  ⟨(Over.pullback y).obj 𝒜.F⟩

/-- **G1 from the two textbook leaves** (compiled). -/
theorem qmAbFieldFibre_of (hI : SmoothGeomConnIntegral) (hT : AbVarEndTorsionFree) :
    QMAbFieldFibre := by
  intro S 𝒜 K _ _ y
  letI := 𝒜.grp
  have := 𝒜.proper
  have := 𝒜.smooth
  have := 𝒜.geomConn
  let Fs : Over (Spec (CommRingCat.of K)) := (Over.pullback y).obj 𝒜.F
  have hsm2 : SmoothOfRelativeDimension 2 Fs.hom := by dsimp [Fs]; infer_instance
  have : Smooth Fs.hom := SmoothOfRelativeDimension.smooth 2 _
  set AF : AbVar K := fibreAbVar hI 𝒜 y with hAF
  -- the level points
  let pt : O → AF.Pt K := fun a => cpt y ≫ (Over.pullback y).map (sec 𝒜 a)
  have hpt : ∀ a, (pt a).left ≫ pullback.fst 𝒜.F.hom y = y ≫ 𝒜.eta a := fun a => by
    change ((cpt y).left ≫ ((Over.pullback y).map (sec 𝒜 a)).left) ≫ _ = _
    rw [Category.assoc, map_left_fst, ← Category.assoc, cpt_fst]
    rfl
  have hpt_eq : ∀ a b, pt a = pt b ↔ y ≫ 𝒜.eta a = y ≫ 𝒜.eta b := fun a b => by
    constructor
    · intro h; rw [← hpt, ← hpt, h]
    · intro h
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · exact (hpt a).trans (h.trans (hpt b).symm)
      · exact (Over.w (pt a)).trans (Over.w (pt b)).symm
  -- dimension
  have hdim : AF.dim = 2 := by
    have : GeometricallyIntegral Fs.hom := (fibreAbVar hI 𝒜 y).geomInt
    have : IrreducibleSpace Fs.left := GeometricallyIrreducible.irreducibleSpace_of_subsingleton Fs.hom
    have : JacobsonSpace Fs.left := LocallyOfFiniteType.jacobsonSpace Fs.hom
    obtain ⟨z, -, hzc⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set Fs.left))
      ⟨(pt 0).left.base (IsLocalRing.closedPoint K), trivial⟩ isClosed_univ.isLocallyClosed
    have h1 := (ZInQ.Contrib.Dim.ringKrullDim_stalk_of_smoothOfRelativeDimension Fs.hom 2 z hzc).1
    have h2 := (ZInQ.Contrib.Dim.topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth Fs.hom z hzc).1
    change topologicalKrullDim Fs.left = 2
    rw [h2, h1]; rfl
  -- `ι` on the fibre
  have hmon : ∀ a, IsMonHom ((Over.pullback y).map (fa 𝒜 a)) := fun a => by
    have : IsMonHom (fa 𝒜 a) := 𝒜.iota_hom a
    infer_instance
  let jf : O → AbVar.End AF := fun a => @AbVar.Hom.mk' K _ AF AF ((Over.pullback y).map (fa 𝒜 a)) (hmon a)
  have hjf : ∀ a, (jf a).hom = (Over.pullback y).map (fa 𝒜 a) := fun a => rfl
  have hfa1 : fa 𝒜 1 = 𝟙 _ := Over.OverMorphism.ext 𝒜.iota_one
  have hfamul : ∀ a b, fa 𝒜 (a * b) = fa 𝒜 b ≫ fa 𝒜 a := fun a b =>
    Over.OverMorphism.ext (𝒜.iota_mul a b)
  have hfaadd : ∀ a b, fa 𝒜 (a + b) = fa 𝒜 a * fa 𝒜 b := fun a b => 𝒜.iota_add a b
  have hfa0 : fa 𝒜 0 = 1 := by
    have h := hfaadd 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  let jq : O →+* AbVar.End AF :=
    { toFun := jf
      map_one' := AbVar.Hom.ext' (by rw [hjf, hfa1]; exact CategoryTheory.Functor.map_id _ _)
      map_mul' := fun a b => AbVar.Hom.ext' (by
        rw [hjf, hfamul]; exact CategoryTheory.Functor.map_comp _ _ _)
      map_zero' := AbVar.Hom.ext' (by
        rw [hjf, hfa0]; exact CategoryTheory.Functor.map_one _)
      map_add' := fun a b => AbVar.Hom.ext' (by
        rw [hjf, hfaadd]; exact CategoryTheory.Functor.map_mul _ _ _) }
  have hsec_lin : ∀ a b, sec 𝒜 (a * b) = sec 𝒜 b ≫ fa 𝒜 a := fun a b =>
    Over.OverMorphism.ext (𝒜.eta_linear a b)
  have hpt_lin : ∀ a b, pt (a * b) = pt b ≫ (jq a).hom := fun a b => by
    change cpt y ≫ (Over.pullback y).map (sec 𝒜 (a * b)) = (cpt y ≫ (Over.pullback y).map (sec 𝒜 b)) ≫
      (Over.pullback y).map (fa 𝒜 a)
    rw [hsec_lin, CategoryTheory.Functor.map_comp, Category.assoc]
  -- `jq(d) = 0 ⇒ d ∈ 3𝒪`
  have hker1 : ∀ d : O, jq d = 0 → ∃ e : O, d = 3 * e := fun d hd => by
    rw [← 𝒜.eta_ker K y d, ← hpt_eq]
    have h1 := hpt_lin d 1
    rw [_root_.mul_one, hd, AbVar.Hom.hom_zero, MonObj.comp_one] at h1
    have h0 := hpt_lin 0 1
    rw [_root_.mul_one, map_zero, AbVar.Hom.hom_zero, MonObj.comp_one] at h0
    rw [h1, h0]
  have hinj : Function.Injective jq := by
    have hz : ∀ c, jq c = 0 → c = 0 := fun c hc => by
      apply O_eq_zero_of_forall_dvd
      intro k
      induction k with
      | zero => exact ⟨c, by simp⟩
      | succ k ih =>
        obtain ⟨d, hd⟩ := ih
        have hd0 : jq d = 0 := by
          apply hT K AF (3 ^ k) (jq d) (by positivity)
          rw [nsmul_eq_mul, ← map_natCast jq, ← map_mul]
          push_cast
          rw [← hd, hc]
        obtain ⟨e, he⟩ := hker1 d hd0
        exact ⟨e, by rw [hd, he, pow_succ, _root_.mul_assoc]⟩
    intro a b hab
    have := hz (a - b) (by rw [map_sub, hab, sub_self])
    exact sub_eq_zero.mp this
  let q : QMStr AF := ⟨jq, hinj⟩
  -- the level structure
  have hsec0 : sec 𝒜 0 = 1 := by
    apply Over.OverMorphism.ext
    change 𝒜.eta 0 = (toUnit (𝟙_ (Over S)) ≫ η[𝒜.F]).left
    rw [toUnit_unique (toUnit (𝟙_ (Over S))) (𝟙 _), Category.id_comp, 𝒜.one_eq]
  have hpt0 : pt 0 = 1 := by
    change cpt y ≫ (Over.pullback y).map (sec 𝒜 0) = 1
    rw [hsec0, CategoryTheory.Functor.map_one, MonObj.comp_one]
  have hptadd : ∀ a b, pt (a + b) = pt a * pt b := fun a b => by
    change cpt y ≫ (Over.pullback y).map (sec 𝒜 (a + b)) = _
    rw [show sec 𝒜 (a + b) = sec 𝒜 a * sec 𝒜 b from 𝒜.eta_add a b,
      CategoryTheory.Functor.map_mul, MonObj.comp_mul]
    rfl
  let e0 : O →+ Additive (AF.Pt K) :=
    { toFun := fun a => Additive.ofMul (pt a)
      map_zero' := by rw [hpt0]; rfl
      map_add' := fun a b => by rw [hptadd]; rfl }
  let e : Level3 q :=
    { eta := e0
      linear := fun a b => by
        change Additive.ofMul (pt (a * b)) = Additive.ofMul (pt b ≫ (jq a).hom)
        rw [hpt_lin]
      ker := fun a => by
        change Additive.ofMul (pt a) = Additive.ofMul (1 : AF.Pt K) ↔ _
        rw [EmbeddingLike.apply_eq_iff_eq, ← hpt0, hpt_eq, 𝒜.eta_ker] }
  refine ⟨⟨AF, hdim, q, e⟩, pullback.fst 𝒜.F.hom y, IsPullback.of_hasPullback _ _, fun a => ?_,
    fun a => hpt a⟩
  exact map_left_fst y (fa 𝒜 a)

end SGRG1
#print axioms SGRG1.qmAbFieldFibre_of

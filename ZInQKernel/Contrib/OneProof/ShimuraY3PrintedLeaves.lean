import ZInQKernel.Contrib.OneProof.ShimuraY3Print
import ZInQKernel.Contrib.OneProof.ShimuraGoodReductionNoGuard
import ZInQKernel.Contrib.OneProof.UniformizationLeafAll

/-! # y3-fix: `shimuraMainThmIDeligneY3AbU` from two printed-form leaves

Task y3-fix (2026-11-17). Report: `docs/research/y3-fix.md`; log: `scratch/y3-fix/log.md`.

y3abu-print (`ShimuraY3Print.lean`) proved the research field `RayClassCFT.ShimuraMainThmIDeligneY3AbU` from two
leaves, `Y3FineModuliAb` and `DeligneCanonicalModelY3Every`, which the review rated GLUE for three reasons:
(1) `Y3FineModuliAb` asserts `Nonempty (fieldPt Qbar ⟶ Y)`, which no representability theorem states;
(2) its level structure is the kernel's pointwise form (`η : 𝒪 → A(S)` with kernel `3𝒪` on field fibres), not the
printed one; (3) the moduli clause of `DeligneCanonicalModelY3Every` is in lattice form (`IsUniformization` of
`Λ_τ = ι(𝒪)(τ,1)ᵀ`), while the print describes `[τ, g]` by `(H₁(A, ℤ), h_A) ≅ (L_g, h_τ)`.

This file replaces both leaves:

1. `Y3FineModuliAbP := ∃ Y Φ, R1fpPropsAbP Y Φ`: representability with the **printed level structure**
   (`LevelPrint`, Mumford *GIT* Def. 7.1 in `𝒪`-linear form: at every geometric point `s`,
   `η_s : 𝒪/3𝒪 → A_s(k)[3]` is bijective, `A_s` the pulled-back fibre with its group law) and **without** the
   `ℚ̄`-point clause.
2. `DeligneCanonicalModelY3EveryH`: the canonical-model leaf on every witness, with the moduli clause in the
   **`H₁`/Hodge form** `IsHodgeH1` (an analytic uniformization `A(ℂ) = Lie A / H₁(A, ℤ)` and an `𝒪`-linear
   `β : B_ℝ ≅ H₁(A, ℝ)` carrying `𝒪` onto `H₁(A, ℤ)` and `h_τ(i)` to the complex structure of `Lie A`).

Proved here (standard axioms, no `sorry`):
* `nonempty_qbar_of_cpt`: a proper `ℚ`-scheme with a `ℂ`-point has a `ℚ̄`-point. The `ℚ̄`-point of the field's
  `R1fpPropsAb` is obtained from `Ψ(i, 1)`, given by the canonical-model leaf.
* `toKer`, `ofKer`: the printed level structure and the kernel's are equivalent over `ℚ`-schemes (`ofKer`
  uses `TorsionStructure`, i.e. the textbook field `mumfordTorsionAlgClosed`, through `Level3.onto` on the
  fibre object of SGRSplit).
* `lattice_of_hodge`: **the uniformization dictionary**, `IsHodgeH1 P τ →` the lattice-form clause
  (`Φ = φ ∘ proj ∘ β ∘ ℓ_τ⁻¹`, `ℓ_τ(M) = M (τ,1)ᵀ`, `ℂ`-linear because `ℓ_τ(M J_τ) = i ℓ_τ(M)`).
* `shimuraMainThmIDeligneY3AbU_of_print : MumfordTorsionAlgClosed → Y3FineModuliAbP →
  DeligneCanonicalModelY3EveryH → ShimuraMainThmIDeligneY3AbU` (the discharge).
* `hodge_of_lattice`, `hodge_iff_lattice`: the converse dictionary (lattice form ⇒ `H₁` form, through
  `uniformizationLeafAll_proof` and the `ℂ`-linear lift of `φ⁻¹ ∘ Φu`), so the two forms are equivalent.
* `print_iff_field : MumfordTorsionAlgClosed → ((Y3FineModuliAbP ∧ DeligneCanonicalModelY3EveryH) ↔
  ShimuraMainThmIDeligneY3AbU)`: neither new leaf is stronger than the field.
-/

set_option linter.all false

noncomputable section

namespace Y3Fix

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid
open ShimuraCFT RayClassCFT

/-! ## 1. A `ℚ̄`-point from a `ℂ`-point -/

/-- **A proper `ℚ`-scheme with a `ℂ`-point has a `ℚ̄`-point**: it is nonempty and quasi-compact, so it has a
closed point, whose residue field is finite over `ℚ` (Jacobson; `HDec.ModelGlue.exists_qbarPt`). -/
theorem nonempty_qbar_of_cpt (Y : Over (Spec (CommRingCat.of ℚ))) (hP : IsProper Y.hom)
    (y : fieldPt ℂ ⟶ Y) : Nonempty (fieldPt Qbar ⟶ Y) := by
  haveI := hP
  haveI : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := Y.left) isClosed_univ
    ⟨y.left.base (IsLocalRing.closedPoint ℂ), trivial⟩
  obtain ⟨-, y0, -⟩ := HDec.ModelGlue.exists_qbarPt Y x hx
  exact ⟨y0⟩

/-! ## 2. The level structure in its printed form -/

section Level

open MonoidalCategory CartesianMonoidalCategory MonObj PkgI3
open scoped CategoryTheory.Obj
open SGRSplit

/-- `QMAbScheme` without its level clause `eta_ker` (the data and the group, ring and linearity clauses,
verbatim). -/
structure QMAbSchemeNL (S : Scheme.{0}) extends QMFamily S where
  [grp : GrpObj F]
  geomConn : GeometricallyConnected F.hom
  one_eq : η[F].left = eta 0
  iota_hom : ∀ a : O, IsMonHom (Over.homMk (iota a) (iota_over a) : F ⟶ F)
  iota_one : iota 1 = 𝟙 _
  iota_mul : ∀ a b : O, iota (a * b) = iota b ≫ iota a
  iota_add : ∀ a b : O, (Over.homMk (iota (a + b)) (iota_over _) : F ⟶ F) =
    Over.homMk (iota a) (iota_over a) * Over.homMk (iota b) (iota_over b)
  eta_add : ∀ a b : O, (Over.homMk (U := 𝟙_ (Over S)) (eta (a + b)) (eta_sec _) : 𝟙_ (Over S) ⟶ F) =
    Over.homMk (U := 𝟙_ (Over S)) (eta a) (eta_sec a) *
      Over.homMk (U := 𝟙_ (Over S)) (eta b) (eta_sec b)
  eta_linear : ∀ a b : O, eta (a * b) = eta b ≫ iota a
  eta_three : ∀ b : O, eta (3 * b) = eta 0

/-- The section `η(a)` as a map from the unit of `Over S`. -/
def secF {S : Scheme.{0}} (𝒜 : QMFamily S) (a : O) : 𝟙_ (Over S) ⟶ 𝒜.F :=
  Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta a) (𝒜.eta_sec a)

/-- **The printed level condition** (Mumford, *GIT*, Def. 7.1, in its `𝒪`-linear form): at every geometric
point `s : Spec k → S` (`k` algebraically closed), the homomorphism `η_s : 𝒪/3𝒪 → A_s(k)[3]`,
`a ↦ η(a)(s)`, is bijective; here `A_s = s^*A` is the geometric fibre (Mathlib's pullback, with the group law
of the pulled-back group object) and `A_s(k)[3]` its group of `k`-points `x` with `x³ = 1`. -/
def LevelPrint {S : Scheme.{0}} (𝒜 : QMAbSchemeNL S) : Prop :=
  letI := 𝒜.grp
  ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S),
    (∀ a : O, s ≫ 𝒜.eta a = s ≫ 𝒜.eta 0 ↔ ∃ b : O, a = 3 * b) ∧
    ∀ x : AbVar.ptObj (K := k) k ⟶ (Over.pullback s).obj 𝒜.F, x ^ 3 = 1 →
      ∃ a : O, x = cpt s ≫ (Over.pullback s).map (secF 𝒜.toQMFamily a)

/-- **An abelian surface scheme with QM by `𝒪` and a full level-3 structure, in the printed form**: the
level clause is `LevelPrint`. -/
structure QMAbSchemeP (S : Scheme.{0}) extends QMAbSchemeNL S where
  level : LevelPrint toQMAbSchemeNL

/-- The kernel's form forgets to `QMAbSchemeNL`. -/
def toNL {S : Scheme.{0}} (𝒜 : QMAbScheme S) : QMAbSchemeNL S :=
  letI := 𝒜.grp
  { toQMFamily := 𝒜.toQMFamily, grp := 𝒜.grp, geomConn := 𝒜.geomConn, one_eq := 𝒜.one_eq,
    iota_hom := 𝒜.iota_hom, iota_one := 𝒜.iota_one, iota_mul := 𝒜.iota_mul, iota_add := 𝒜.iota_add,
    eta_add := 𝒜.eta_add, eta_linear := 𝒜.eta_linear, eta_three := 𝒜.eta_three }

/-- **Printed form ⇒ the kernel's form**: injectivity at a field point follows from injectivity at the
geometric point over it (`Spec K̄ → Spec K` is an epimorphism). -/
def toKer {S : Scheme.{0}} (𝒜 : QMAbSchemeP S) : QMAbScheme S :=
  letI := 𝒜.grp
  { toQMFamily := 𝒜.toQMFamily, grp := 𝒜.grp, geomConn := 𝒜.geomConn, one_eq := 𝒜.one_eq,
    iota_hom := 𝒜.iota_hom, iota_one := 𝒜.iota_one, iota_mul := 𝒜.iota_mul, iota_add := 𝒜.iota_add,
    eta_add := 𝒜.eta_add, eta_linear := 𝒜.eta_linear, eta_three := 𝒜.eta_three
    eta_ker := fun K _ s a => by
      constructor
      · intro h
        have hp : Epi (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) :=
          Flat.epi_of_flat_of_surjective _
        refine ((𝒜.level (AlgebraicClosure K)
          (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫ s)).1 a).1 ?_
        rw [Category.assoc, h, Category.assoc]
      · rintro ⟨b, rfl⟩
        rw [𝒜.eta_three] }

theorem toKer_toQMFamily {S : Scheme.{0}} (𝒜 : QMAbSchemeP S) : (toKer 𝒜).toQMFamily = 𝒜.toQMFamily := rfl

/-- **The fibre of a kernel-form QM abelian scheme at a field point of characteristic 0 is an object, with
level points the pulled-back sections** (SGRSplit's `qmAbFieldFibre_of`, verbatim, with the object exhibited). -/
theorem fibre_level (hI : SmoothGeomConnIntegral) (hT : AbVarEndTorsionFree) {S : Scheme.{0}}
    (𝒜 : QMAbScheme S) {K : Type} [Field K] [CharZero K] (y : Spec (CommRingCat.of K) ⟶ S) :
    ∃ (hdim : (fibreAbVar hI 𝒜 y).dim = 2) (q : QMStr (fibreAbVar hI 𝒜 y)) (e : Level3 q),
      ∀ a : O, Additive.toMul (e.eta a) = cpt y ≫ (Over.pullback y).map (sec 𝒜 a) := by
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
  exact ⟨hdim, q, e, fun a => rfl⟩

/-- `CharZero` of a field with a point of a `ℚ`-scheme. -/
theorem charZero_of_pt {S : Over (Spec (CommRingCat.of ℚ))} {k : Type} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ S.left) : CharZero k := by
  let f : ℚ →+* k := (Spec.preimage (s ≫ S.hom)).hom
  letI := f.toAlgebra
  exact charZero_of_injective_algebraMap f.injective

/-- **The kernel's form ⇒ printed form, over a `ℚ`-scheme** (given `TorsionStructure`): injectivity at
geometric points is `eta_ker`; ontoness onto `A_s(k)[3]` is `Level3.onto` on the fibre object. -/
theorem levelPrint_of_ker (hT : ObjBridge.TorsionStructure) {S : Over (Spec (CommRingCat.of ℚ))}
    (𝒜 : QMAbScheme S.left) : LevelPrint (toNL 𝒜) := by
  intro k _ _ s
  haveI := charZero_of_pt s
  refine ⟨fun a => 𝒜.eta_ker k s a, fun x hx => ?_⟩
  obtain ⟨hdim, q, e, he⟩ := fibre_level smoothGeomConnIntegral abVarEndTorsionFree 𝒜 s
  let P : QML3 k := ⟨fibreAbVar smoothGeomConnIntegral 𝒜 s, hdim, q, e⟩
  let x' : P.A.Pt k := x
  have hx' : x' ^ 3 = 1 := hx
  obtain ⟨a, ha⟩ := Level3.onto hT P (bcPt P.A x') (by
    rw [bcPt, ← MonObj.comp_pow, hx']
    exact MonObj.comp_one _)
  refine ⟨a, ?_⟩
  have := bcPt_injective P.A ha
  exact (this.symm.trans (he a))

/-- The kernel's form gives the printed form (over a `ℚ`-scheme, given `TorsionStructure`). -/
def ofKer (hT : ObjBridge.TorsionStructure) {S : Over (Spec (CommRingCat.of ℚ))} (𝒜 : QMAbScheme S.left) :
    QMAbSchemeP S.left :=
  { toNL 𝒜 with level := levelPrint_of_ker hT 𝒜 }

theorem ofKer_toQMFamily (hT : ObjBridge.TorsionStructure) {S : Over (Spec (CommRingCat.of ℚ))}
    (𝒜 : QMAbScheme S.left) : (ofKer hT 𝒜).toQMFamily = 𝒜.toQMFamily := rfl

end Level

/-! ## 3. The clause lists in printed form -/

/-- **R1univ, printed form**: `R1univAbProps` with the printed level structure (`QMAbSchemeP`). -/
def R1univAbPropsP (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ 𝒜' : QMAbSchemeP S.left,
      (∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S), ∃ P : QML3 K,
        IsFibreOf 𝒜'.toQMFamily s.left P) →
      ∃ g : S ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S) (P : QML3 K),
        IsFibreOf 𝒜'.toQMFamily s.left P → Φ K (s ≫ g) = M3.mk P

/-- **R1fam, printed form**: the universal object has the printed level structure. -/
def R1famAbPropsP (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∃ 𝒜 : QMAbSchemeP Y.left, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K),
    Φ K y = M3.mk P → IsFibreOf 𝒜.toQMFamily y.left P

/-- **The fine-moduli clause list in printed form**: `R1fpPropsAb` with the printed level structure and
**without** the clause `Nonempty (fieldPt Qbar ⟶ Y)` (which no representability theorem states). -/
def R1fpPropsAbP (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧
  (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q) ∧
  R1famAbPropsP Y Φ ∧ R1univAbPropsP Y Φ

/-- The kernel's clause list without the `ℚ̄`-point. -/
def R1fpPropsAbNP (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧
  (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q) ∧
  R1famAbProps Y Φ ∧ R1univAbProps Y Φ

/-- **Printed list ⇒ the kernel's list without the point** (given `TorsionStructure`). -/
theorem np_of_P (hT : ObjBridge.TorsionStructure) {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpPropsAbP Y Φ) : R1fpPropsAbNP Y Φ := by
  obtain ⟨hp, hs, hn, ⟨𝒜, h𝒜⟩, hU⟩ := h
  exact ⟨hp, hs, hn, ⟨toKer 𝒜, h𝒜⟩, fun S hpS hsS 𝒜' hall => hU S hpS hsS (ofKer hT 𝒜') hall⟩

/-- **The kernel's list ⇒ printed list** (given `TorsionStructure`). -/
theorem P_of_np (hT : ObjBridge.TorsionStructure) {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpPropsAbNP Y Φ) : R1fpPropsAbP Y Φ := by
  obtain ⟨hp, hs, hn, ⟨𝒜, h𝒜⟩, hU⟩ := h
  exact ⟨hp, hs, hn, ⟨ofKer hT (S := Y) 𝒜, h𝒜⟩, fun S hpS hsS 𝒜' hall => hU S hpS hsS (toKer 𝒜') hall⟩

theorem np_of_ab {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (h : R1fpPropsAb Y Φ) :
    R1fpPropsAbNP Y Φ :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem ab_of_np {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (h : R1fpPropsAbNP Y Φ)
    (hpt : Nonempty (fieldPt Qbar ⟶ Y)) : R1fpPropsAb Y Φ :=
  ⟨h.1, h.2.1, hpt, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-! ## 4. Pinning without the point (elkies-print's `compare_iso_ab`, the point clause unused) -/

theorem phi_part_np {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (hU : R1univAbProps Y Φ) (h1' : R1fpPropsAbNP Y' Φ') :
    ∃ g : Y' ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g) := by
  obtain ⟨hp', hs', -, ⟨𝒜', h𝒜'⟩, -⟩ := h1'
  have hall : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y'), ∃ P : QML3 K,
      IsFibreOf 𝒜'.toQMFamily s.left P :=
    fun K _ _ s => ⟨Quotient.out (Φ' K s), h𝒜' K s _ (Quotient.out_eq _).symm⟩
  obtain ⟨g, hg⟩ := hU Y' hp' hs' 𝒜' hall
  refine ⟨g, fun K _ _ y => ?_⟩
  rw [hg K y _ (h𝒜' K y _ (Quotient.out_eq _).symm)]
  exact (Quotient.out_eq _).symm

theorem compare_iso_np {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (h : R1fpPropsAbNP Y Φ) (h' : R1fpPropsAbNP Y' Φ') :
    ∃ g : Y' ≅ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g.hom) := by
  obtain ⟨g, hg⟩ := phi_part_np h.2.2.2.2 h'
  obtain ⟨g', hg'⟩ := phi_part_np h'.2.2.2.2 h
  have e1 : g' ≫ g = 𝟙 Y := HDec.QMSplit.Moduli.eq_id_of_fieldPts h.1 h.2.1 _ fun K _ _ y =>
    (Φ K).injective (by rw [← Category.assoc, ← hg K (y ≫ g'), ← hg' K y])
  have e2 : g ≫ g' = 𝟙 Y' := HDec.QMSplit.Moduli.eq_id_of_fieldPts h'.1 h'.2.1 _ fun K _ _ y =>
    (Φ' K).injective (by rw [← Category.assoc, ← hg' K (y ≫ g), ← hg K y])
  exact ⟨⟨g, g', e2, e1⟩, hg⟩

/-! ## 6. The moduli clause in the print's `H₁` / Hodge form, and the uniformization dictionary -/

section Hodge

open Complex
open HDec.HSyn.G0Split.FibreQM (qmMat IotaCompatible)
open MonoidalCategory CartesianMonoidalCategory MonObj PkgI3
open scoped CategoryTheory.Obj

/-- `h_τ(i)`: the complex structure `J_τ ∈ M₂(ℝ)` with `J_τ (τ, 1)ᵀ = i (τ, 1)ᵀ`, i.e.
`J_τ = (1/y) [[x, -(x² + y²)], [1, -x]]` for `τ = x + iy`. -/
def Jmat (τ : UpperHalfPlane) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(τ : ℂ).re / (τ : ℂ).im, -((τ : ℂ).re ^ 2 + (τ : ℂ).im ^ 2) / (τ : ℂ).im;
     1 / (τ : ℂ).im, -(τ : ℂ).re / (τ : ℂ).im]

/-- **The moduli clause in the print's `H₁` (Hodge) form**: `A(ℂ) ≅ Lie(A)/H₁(A, ℤ)` (`(Λ, φ)` an analytic
uniformization in bp-analytic's sense: `Lie A = ℂ^g`, `H₁(A, ℤ) = Λ`), and an `ℝ`-linear isomorphism
`β : B_ℝ = M₂(ℝ) ≅ H₁(A, ℝ) = ℂ^g` (`B` embedded by N5's `ι`) carrying `𝒪` onto `H₁(A, ℤ)`, left
multiplication by `a ∈ 𝒪` to the action of `ι_A(a)`, and right multiplication by `h_τ(i) = J_τ` to the complex
structure of `Lie A`: the pair `(H₁(A, ℤ), h_A)` is `(𝒪, h_τ)` as an `𝒪`-module with Hodge structure. -/
def IsHodgeH1 (P : QML3 ℂ) (τ : UpperHalfPlane) : Prop :=
  ∃ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (_ : DiscreteTopology Λ)
    (φ : BPAnalytic.Torus Λ ≃+ Additive (P.A.Pt ℂ)),
    BPAnalytic.Uniformization.IsUniformization P.A Λ φ ∧
    ∃ β : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Fin g → ℂ),
      (∀ v, v ∈ Λ ↔ ∃ b : B, b ∈ O ∧ v = β (BPAnalytic.QM.iota b)) ∧
      (∀ M, β (M * Jmat τ) = Complex.I • β M) ∧
      (∀ (a : O) (M : Matrix (Fin 2) (Fin 2) ℝ),
        Additive.toMul (φ (BPAnalytic.proj Λ (β (BPAnalytic.QM.iota (a : B) * M)))) =
          Additive.toMul (φ (BPAnalytic.proj Λ (β M))) ≫ (P.q.iota a).hom)

/-- `M ↦ M (τ, 1)ᵀ`. -/
def ellF (τ : UpperHalfPlane) (M : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → ℂ :=
  fun i => (M i 0 : ℂ) * (τ : ℂ) + (M i 1 : ℂ)

def ellL (τ : UpperHalfPlane) : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] (Fin 2 → ℂ) where
  toFun := ellF τ
  map_add' M N := by funext i; simp [ellF]; ring
  map_smul' c M := by funext i; simp [ellF, Complex.real_smul]; ring

theorem ellL_injective (τ : UpperHalfPlane) : Function.Injective (ellL τ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro M hM
  have hy : (τ : ℂ).im ≠ 0 := τ.im_pos.ne'
  funext i j
  have h := congrFun hM i
  change (M i 0 : ℂ) * (τ : ℂ) + (M i 1 : ℂ) = 0 at h
  have hi := congrArg Complex.im h
  have hr := congrArg Complex.re h
  simp at hi hr
  have h0 : M i 0 = 0 := hi.resolve_right τ.im_pos.ne'
  have h1 : M i 1 = 0 := by rw [h0] at hr; simpa using hr
  fin_cases j
  · exact h0
  · exact h1

theorem finrank_mat : Module.finrank ℝ (Matrix (Fin 2) (Fin 2) ℝ) = Module.finrank ℝ (Fin 2 → ℂ) := by
  rw [Module.finrank_matrix, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex]

/-- `ℓ_τ : M₂(ℝ) ≅ ℂ²`, `M ↦ M (τ, 1)ᵀ`. -/
def ellE (τ : UpperHalfPlane) : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Fin 2 → ℂ) :=
  LinearEquiv.ofBijective (ellL τ) ⟨ellL_injective τ,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank finrank_mat).1 (ellL_injective τ)⟩

theorem ellE_apply (τ : UpperHalfPlane) (M : Matrix (Fin 2) (Fin 2) ℝ) : ellE τ M = ellF τ M := rfl

theorem latVec_eq (τ : UpperHalfPlane) (b : B) :
    BPAnalytic.QM.latVec b (τ : ℂ) = ellE τ (BPAnalytic.QM.iota b) := by
  funext i
  rw [ellE_apply]
  fin_cases i <;> simp [BPAnalytic.QM.latVec, ellF, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem ellE_J (τ : UpperHalfPlane) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    ellE τ (M * Jmat τ) = Complex.I • ellE τ M := by
  have hy : (τ : ℂ).im ≠ 0 := τ.im_pos.ne'
  have hyc : (((τ : ℂ).im : ℝ) : ℂ) * (((τ : ℂ).im : ℝ) : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (by exact_mod_cast hy)
  have hτ : (τ : ℂ) = (((τ : ℂ).re : ℝ) : ℂ) + (((τ : ℂ).im : ℝ) : ℂ) * Complex.I :=
    (Complex.re_add_im _).symm
  funext i
  simp only [ellE_apply, ellF, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two, Jmat,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  generalize (τ : ℂ).re = x at hτ ⊢
  generalize (τ : ℂ).im = y at hτ hyc ⊢
  rw [hτ]
  push_cast
  linear_combination ((M i 0 : ℂ) * (x : ℂ) * Complex.I + (M i 1 : ℂ) * Complex.I - (M i 0 : ℂ) * (y : ℂ)) * hyc
    + (-(M i 0 : ℂ) * (y : ℂ)) * Complex.I_sq

theorem ellE_iota (τ : UpperHalfPlane) (a : O) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    ellE τ (BPAnalytic.QM.iota (a : B) * M) = (qmMat a).mulVec (ellE τ M) := by
  funext i
  simp only [ellE_apply, ellF, qmMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct,
    Matrix.map_apply]
  push_cast
  ring

/-- `T = β ∘ ℓ_τ⁻¹ : ℂ² → ℂ^g` is `ℂ`-linear. -/
def Tlin {g : ℕ} (τ : UpperHalfPlane) (β : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Fin g → ℂ))
    (hJ : ∀ M, β (M * Jmat τ) = Complex.I • β M) : (Fin 2 → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun v := β ((ellE τ).symm v)
  map_add' v w := by simp
  map_smul' c v := by
    have hI : ∀ w, β ((ellE τ).symm (Complex.I • w)) = Complex.I • β ((ellE τ).symm w) := fun w => by
      obtain ⟨M, rfl⟩ := (ellE τ).surjective w
      rw [← ellE_J, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hJ]
    have hc : c • v = (c.re : ℝ) • v + (c.im : ℝ) • (Complex.I • v) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul]
      congr 1
      exact (Complex.re_add_im c).symm
    have hc' : c • β ((ellE τ).symm v) = (c.re : ℝ) • β ((ellE τ).symm v) +
        (c.im : ℝ) • (Complex.I • β ((ellE τ).symm v)) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul]
      congr 1
      exact (Complex.re_add_im c).symm
    rw [RingHom.id_apply, hc', hc, map_add, map_add, map_smul, map_smul, map_smul, map_smul, hI]

theorem Tlin_ellE {g : ℕ} (τ : UpperHalfPlane) (β : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Fin g → ℂ))
    (hJ : ∀ M, β (M * Jmat τ) = Complex.I • β M) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    Tlin τ β hJ (ellE τ M) = β M := by
  change β ((ellE τ).symm (ellE τ M)) = β M
  rw [LinearEquiv.symm_apply_apply]

/-- **The uniformization dictionary** (compiled): the print's `H₁`/Hodge form of the moduli clause gives the
lattice form `IsUniformization (Λ_τ)` with `ι`-compatibility (the kernel's clause in `IsShimuraHolFamily` and
`ModuliAtUnits`): `Φ = φ ∘ proj ∘ β ∘ ℓ_τ⁻¹`. -/
theorem lattice_of_hodge {P : QML3 ℂ} {τ : UpperHalfPlane} (h : IsHodgeH1 P τ) :
    ∃ Φu : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts P.A (RingHom.id ℂ),
      ZInQ.LeafPush2.IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
      IotaCompatible P Φu := by
  obtain ⟨g, Λ, hD, φ, hφ, β, hΛ, hJ, hio⟩ := h
  obtain ⟨h1, h2, h3, h4, h5⟩ := ZInQ.LeafPush2.isUniformization_of_bp P.A hφ
  set Φ0 : (Fin g → ℂ) → ZInQ.LeafPush2.CPts P.A (RingHom.id ℂ) :=
    fun z => Additive.toMul (φ (BPAnalytic.proj Λ z)) with hΦ0
  let T := Tlin τ β hJ
  have hTc : Continuous T := LinearMap.continuous_of_finiteDimensional T
  have hTd : Differentiable ℂ T := (LinearMap.toContinuousLinearMap T).differentiable
  have hTs : Function.Surjective T := fun w => ⟨ellE τ (β.symm w), by
    rw [Tlin_ellE, LinearEquiv.apply_symm_apply]⟩
  refine ⟨fun z => Φ0 (T z), ⟨fun z w => ?_, fun z => ?_, fun p => ?_, fun U => ?_, fun U s => ?_⟩,
    fun a z => ?_⟩
  · change Φ0 (T (z + w)) = Φ0 (T z) * Φ0 (T w)
    rw [map_add]; exact h1 _ _
  · change Φ0 (T z) = 1 ↔ _
    rw [h2, hΛ]
    refine Iff.trans ?_ (HDec.HSyn.G0Split.FibreQM.PeriodGlue.mem_qmLattice_iff _ z).symm
    obtain ⟨M, rfl⟩ := (ellE τ).surjective z
    rw [Tlin_ellE]
    constructor
    · rintro ⟨b, hb, he⟩
      exact ⟨b, hb, by rw [latVec_eq, β.injective he]⟩
    · rintro ⟨b, hb, he⟩
      refine ⟨b, hb, ?_⟩
      rw [latVec_eq] at he
      rw [(ellE τ).injective he]
  · obtain ⟨w, hw⟩ := h3 p
    obtain ⟨z, rfl⟩ := hTs w
    exact ⟨z, hw⟩
  · exact (h4 U).preimage hTc
  · exact (h5 U s).comp hTd.differentiableOn (fun z hz => hz)
  · obtain ⟨M, rfl⟩ := (ellE τ).surjective z
    change Φ0 (T ((qmMat a).mulVec (ellE τ M))) = Φ0 (T (ellE τ M)) ≫ (P.q.iota a).hom
    rw [← ellE_iota, Tlin_ellE, Tlin_ellE]
    exact hio a M

end Hodge

/-! ## 8. The converse dictionary: the lattice form gives the `H₁` form -/

section Converse

open Complex Filter Topology
open HDec.HSyn.G0Split.FibreQM (qmMat IotaCompatible)
open MonoidalCategory CartesianMonoidalCategory MonObj PkgI3
open scoped CategoryTheory.Obj

theorem countable_of_zlattice {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] : (Λ : Set (Fin g → ℂ)).Countable := by
  haveI : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ Λ
  have : (Λ : Set (Fin g → ℂ)) = Set.range (fun c => ((f c : Λ) : Fin g → ℂ)) := by
    ext v
    constructor
    · intro hv
      obtain ⟨c, hc⟩ := hf ⟨v, hv⟩
      exact ⟨c, by simp only [hc]⟩
    · rintro ⟨c, rfl⟩
      exact (f c).2
  rw [this]
  exact Set.countable_range _

/-- A real subspace `W` with `W + Λ` everything, `Λ` countable, is everything. -/
theorem eq_top_of_add_countable {g : ℕ} (W : Submodule ℝ (Fin g → ℂ)) (Λ : Set (Fin g → ℂ))
    (hΛ : Λ.Countable) (h : ∀ w, ∃ x ∈ W, w - x ∈ Λ) : W = ⊤ := by
  by_contra hW
  obtain ⟨ψ, hψ0, hψW⟩ := W.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hW)
  obtain ⟨v, hv⟩ : ∃ v, ψ v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hψ0 (LinearMap.ext hc)
  apply Cardinal.not_countable_real
  refine (hΛ.image ψ).mono fun r _ => ?_
  obtain ⟨x, hx, hwx⟩ := h ((r / ψ v) • v)
  refine ⟨_, hwx, ?_⟩
  rw [map_sub, LinearMap.mem_ker.mp (hψW hx), sub_zero, map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]

/-- **The converse dictionary** (compiled): the kernel's lattice-form clause gives the `H₁`/Hodge form, with
`(Λ, φ)` the uniformization of `uniformizationLeafAll_proof` and `β = T ∘ ℓ_τ`, `T` the `ℂ`-linear lift of
`φ⁻¹ ∘ Φu`. So `IsHodgeH1 P τ` is equivalent to the lattice form. -/
theorem hodge_of_lattice {P : QML3 ℂ} {τ : UpperHalfPlane}
    {Φu : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts P.A (RingHom.id ℂ)}
    (hU : ZInQ.LeafPush2.IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu)
    (hio : IotaCompatible P Φu) : IsHodgeH1 P τ := by
  obtain ⟨g, Λ, hDisc, hZ, φ, hφ⟩ := uniformizationLeafAll_proof P.A
  obtain ⟨u1, u2, u3, u4, u5⟩ := hU
  set Lτ := BPAnalytic.QM.qmLattice τ.im_pos.ne' with hLτ
  haveI : DiscreteTopology Lτ := by
    rw [hLτ]; unfold BPAnalytic.QM.qmLattice; infer_instance
  let f : (Fin 2 → ℂ) → BPAnalytic.Torus Λ := fun z => φ.symm (Additive.ofMul (Φu z))
  have hf : ∀ z, φ (f z) = Additive.ofMul (Φu z) := fun z => φ.apply_symm_apply _
  have hfadd : ∀ z w, f (z + w) = f z + f w := by
    intro z w
    simp only [f, u1]
    exact map_add φ.symm _ _
  have hf0 : f 0 = 0 := by
    have h := hfadd 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  have hfker : ∀ z, f z = 0 ↔ z ∈ Lτ := by
    intro z
    rw [← u2 z]
    constructor
    · intro h
      have h2 := hf z
      rw [h, map_zero] at h2
      exact Additive.ofMul.injective (by rw [← h2]; rfl)
    · intro h
      apply φ.injective
      rw [hf, h, map_zero]
      rfl
  -- continuity of `f = φ⁻¹ ∘ Φu`
  have hev : ∀ (U : P.A.X.left.Opens) (s : Γ(P.A.X.left, U)),
      (fun z => BPAnalytic.Uniformization.evalAt P.A U s (Φu z)) =
        fun z => ZInQ.LeafPush2.cEvalAt (Φu z) U s := fun U s =>
    funext fun z => (ZInQ.LeafPush2.cEvalAt_eq_evalAt P.A (Φu z) U s).symm
  have hfc : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro z0 N hN
    obtain ⟨v0, hv0⟩ := QuotientAddGroup.mk_surjective (f z0)
    have hv0' : BPAnalytic.proj Λ v0 = f z0 := hv0
    rw [← hv0'] at hN
    obtain ⟨U, k, fs, ε, hε, hin, hcl⟩ := hφ.open_map v0 N hN
    have hpt : Additive.toMul (φ (BPAnalytic.proj Λ v0)) = Φu z0 := by
      rw [hv0', hf]; rfl
    rw [hpt] at hin hcl
    have hz0 : z0 ∈ ZInQ.LeafPush2.cDom Φu U := hin
    have hcont : ∀ i, ContinuousAt (fun z => BPAnalytic.Uniformization.evalAt P.A U (fs i) (Φu z)) z0 :=
      fun i => by
        rw [hev]
        exact ((u5 U (fs i)).differentiableAt ((u4 U).mem_nhds hz0)).continuousAt
    have hball : ∀ᶠ z in 𝓝 z0, z ∈ ZInQ.LeafPush2.cDom Φu U ∧ ∀ i,
        ‖BPAnalytic.Uniformization.evalAt P.A U (fs i) (Φu z) -
          BPAnalytic.Uniformization.evalAt P.A U (fs i) (Φu z0)‖ < ε := by
      refine Filter.Eventually.and
        (show ∀ᶠ z in 𝓝 z0, z ∈ ZInQ.LeafPush2.cDom Φu U from (u4 U).mem_nhds hz0) ?_
      rw [Filter.eventually_all]
      intro i
      exact ((hcont i).eventually (Metric.ball_mem_nhds _ hε)).mono fun z hz => by
        simpa [dist_eq_norm] using hz
    refine Filter.mem_map.mpr (hball.mono fun z hz => ?_)
    obtain ⟨q, hq, hqe⟩ := hcl (Φu z) hz.1 hz.2
    have : q = f z := φ.injective (by rw [hf, ← hqe]; rfl)
    rw [← this]
    exact hq
  -- the `ℝ`-linear lift
  let fA : (Fin 2 → ℂ) →+ BPAnalytic.Torus Λ := { toFun := f, map_zero' := hf0, map_add' := hfadd }
  let fb : BPAnalytic.Torus Lτ →+ BPAnalytic.Torus Λ :=
    QuotientAddGroup.lift Lτ.toAddSubgroup fA (fun z hz => (AddMonoidHom.mem_ker).mpr ((hfker z).2 hz))
  have hfbc : Continuous fb := (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr hfc
  obtain ⟨T, -, hTf⟩ := BPAnalytic.exists_realLinear_lift Lτ Λ fb hfbc
  have hTf' : ∀ v, BPAnalytic.proj Λ (T v) = f v := fun v => (hTf v).symm
  -- `T` is `ℂ`-linear (the argument of `IsUniformization.exists_complexLinear`)
  obtain ⟨U, fs, e, hU0, hF⟩ := hφ.coords (T 0)
  set F : (Fin g → ℂ) → (Fin g → ℂ) := fun v i =>
    BPAnalytic.Uniformization.evalAt P.A U (fs i) (Additive.toMul (φ (BPAnalytic.proj Λ v))) with hFdef
  set G : (Fin 2 → ℂ) → (Fin g → ℂ) := fun v i =>
    BPAnalytic.Uniformization.evalAt P.A U (fs i) (Φu v) with hGdef
  have hFT : ∀ v, F (T v) = G v := by
    intro v
    funext i
    simp only [hFdef, hGdef, hTf', hf]
    rfl
  have hFan : AnalyticAt ℂ F (T 0) :=
    AnalyticAt.pi fun i => (hφ.holo U (fs i)).2 (T 0) hU0
  have hz0 : (0 : Fin 2 → ℂ) ∈ ZInQ.LeafPush2.cDom Φu U := by
    have h : BPAnalytic.Uniformization.PtIn P.A (Additive.toMul (φ (BPAnalytic.proj Λ (T 0)))) U := hU0
    rw [hTf', hf] at h
    exact h
  have hGd : DifferentiableAt ℂ G 0 := by
    rw [differentiableAt_pi]
    intro i
    have h := (u5 U (fs i)).differentiableAt ((u4 U).mem_nhds hz0)
    rw [← hev] at h
    exact h
  have hstrict : HasStrictFDerivAt F (e : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) (T 0) := by
    have h := hFan.hasStrictFDerivAt
    rwa [hF.fderiv] at h
  have hevT : ∀ᶠ v in 𝓝 (0 : Fin 2 → ℂ), hstrict.localInverse F e (T 0) (G v) = T v := by
    have hcont : Filter.Tendsto (T : (Fin 2 → ℂ) → (Fin g → ℂ)) (𝓝 0) (𝓝 (T 0)) :=
      T.continuous.tendsto 0
    filter_upwards [hcont.eventually hstrict.eventually_left_inverse] with v hv
    rw [← hFT v]; exact hv
  have hdiffL : DifferentiableAt ℂ (hstrict.localInverse F e (T 0)) (G 0) := by
    have h := hstrict.to_localInverse.differentiableAt
    rwa [hFT 0] at h
  have hTdiff : DifferentiableAt ℂ (T : (Fin 2 → ℂ) → (Fin g → ℂ)) 0 :=
    (hdiffL.comp 0 hGd).congr_of_eventuallyEq (hevT.mono fun v hv => hv.symm)
  set D := fderiv ℂ (T : (Fin 2 → ℂ) → (Fin g → ℂ)) 0
  have hD : (D.restrictScalars ℝ : (Fin 2 → ℂ) →L[ℝ] (Fin g → ℂ)) = T :=
    (hTdiff.hasFDerivAt.restrictScalars ℝ).unique T.hasFDerivAt
  have hDT : ∀ v, D v = T v := fun v => congrArg (fun L : (Fin 2 → ℂ) →L[ℝ] _ => L v) hD
  have hDf : ∀ v, BPAnalytic.proj Λ (D v) = f v := fun v => by rw [hDT, hTf']
  have hkey : ∀ z, D z ∈ Λ ↔ z ∈ Lτ := fun z => by
    rw [← hfker, ← hDf, show (0 : BPAnalytic.Torus Λ) = BPAnalytic.proj Λ 0 from rfl,
      BPAnalytic.proj_eq_iff, sub_zero]
  -- `D` is bijective
  have hDinj : Function.Injective D := by
    have h0 : ∀ y, D y = 0 → y = 0 := by
      intro y hy
      have hmem : ∀ t : ℝ, t • y ∈ Lτ := fun t => by
        rw [← hkey, D.map_smul_of_tower, hy, smul_zero]
        exact Λ.zero_mem
      have hconst := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℝ)
        (f := fun t => (⟨t • y, hmem t⟩ : Lτ)) ((continuous_id.smul continuous_const).subtype_mk _)
        (x := 1) (y := 0)
      have := congrArg Subtype.val hconst
      simpa using this
    intro z w h
    exact sub_eq_zero.mp (h0 _ (by rw [map_sub, h, sub_self]))
  have hDsurj : Function.Surjective D := by
    have hW := eq_top_of_add_countable
      (LinearMap.range (D.restrictScalars ℝ : (Fin 2 → ℂ) →L[ℝ] (Fin g → ℂ)).toLinearMap)
      (Λ : Set (Fin g → ℂ)) (countable_of_zlattice Λ) (fun w => by
        obtain ⟨z, hz⟩ := u3 (Additive.toMul (φ (BPAnalytic.proj Λ w)))
        refine ⟨D z, ⟨z, rfl⟩, ?_⟩
        have : BPAnalytic.proj Λ w = BPAnalytic.proj Λ (D z) := by
          rw [hDf]
          apply φ.injective
          rw [hf, hz]
          rfl
        exact (BPAnalytic.proj_eq_iff Λ).mp this)
    intro w
    have hw : w ∈ LinearMap.range (D.restrictScalars ℝ : (Fin 2 → ℂ) →L[ℝ] (Fin g → ℂ)).toLinearMap := by
      rw [hW]; exact Submodule.mem_top
    obtain ⟨z, hz⟩ := hw
    exact ⟨z, hz⟩
  let Tl : (Fin 2 → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) :=
    LinearEquiv.ofBijective (D.restrictScalars ℝ : (Fin 2 → ℂ) →L[ℝ] (Fin g → ℂ)).toLinearMap
      ⟨hDinj, hDsurj⟩
  have hTl : ∀ M, ((ellE τ).trans Tl) M = D (ellE τ M) := fun M => rfl
  refine ⟨g, Λ, hDisc, φ, hφ, (ellE τ).trans Tl, fun v => ?_, fun M => ?_, fun a M => ?_⟩
  · obtain ⟨z, rfl⟩ := hDsurj v
    rw [hkey]
    refine Iff.trans (HDec.HSyn.G0Split.FibreQM.PeriodGlue.mem_qmLattice_iff _ z) ?_
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, by rw [hTl, latVec_eq]⟩
    · rintro ⟨b, hb, h⟩
      exact ⟨b, hb, by rw [latVec_eq]; exact hDinj (by rw [h, hTl])⟩
  · rw [hTl, hTl, ellE_J, D.map_smul]
  · rw [hTl, hTl, ellE_iota, hDf, hDf, hf, hf]
    exact hio a (ellE τ M)

/-- **`IsHodgeH1` is equivalent to the kernel's lattice-form clause** (both directions compiled). -/
theorem hodge_iff_lattice (P : QML3 ℂ) (τ : UpperHalfPlane) :
    IsHodgeH1 P τ ↔ ∃ Φu : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts P.A (RingHom.id ℂ),
      ZInQ.LeafPush2.IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
      IotaCompatible P Φu :=
  ⟨lattice_of_hodge, fun ⟨_, hU, hio⟩ => hodge_of_lattice hU hio⟩

end Converse

/-! ## 5. The leaves (lattice form) and the discharge -/

/-- **LEAF `Y3FineModuliAbP`: the fine moduli scheme `Y₃` of QM abelian surfaces with full level-3 structure
over `ℚ`, in printed form** (one object: `Y₃` with its universal family).

*Published statement* (locators recalled, UNVERIFIED; no network): the moduli functor of abelian schemes `A/S`
of relative dimension 2 with an action `ι : 𝒪 → End_S(A)` of the maximal order `𝒪` of `B = (2, −3 | ℚ)`
(discriminant 6) and an `𝒪`-linear full level-3 structure, on `ℤ[1/6]`-schemes, is represented by a scheme
projective and smooth of relative dimension 1 over `ℤ[1/6]` (proper because `B` is a division algebra):
K. Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997), §1; J.-F. Boutot,
H. Carayol, Astérisque 196-197 (1991), Ch. III; J. S. Milne, Proc. Sympos. Pure Math. 33 (1979), Part 2;
D. Mumford, *GIT*, Def. 7.1 (level-`n` structure: sections forming a basis of `A_s[n]` at every geometric
point `s`, `n` invertible) and Thm. 7.9.

*Lean form*: some `(Y, Φ)` satisfies `R1fpPropsAbP`: `Y` proper and smooth of relative dimension 1 over `ℚ`;
`Φ` the moduli bijections on field points, natural in the field; the universal object `QMAbSchemeP` over `Y`;
the classifying map of every `QMAbSchemeP` over a proper smooth curve `S/ℚ` whose field fibres are objects.
The level structure is `LevelPrint` (Mumford's Def. 7.1, `𝒪`-linear: `η(a)`, `a ∈ 𝒪/3𝒪`, are sections with
`η(3b) = 0`, and at each geometric point they are exactly the 81 points of `A_s(k)[3]`). No `ℚ̄`-point clause.

*Form*: a consequence of representability (universal property only on proper smooth curves over `ℚ`, read on
field points; base `ℚ`). Reading risk: no polarization in the moduli problem (Lemma P), as for every
`R1fpPropsAb` in the chain; Milne 1979 and Boutot–Carayol state the polarized problem. -/
def Y3FineModuliAbP : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpPropsAbP Y Φ

/-- The canonical-model leaf over the printed clause list (lattice form of the moduli clause). -/
def DeligneCanonicalModelY3EveryP : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpPropsAbP Y Φ →
    ∃ Ψ, DeligneBodyAt Y Φ Ψ ∧ ModuliAtUnits Y Φ Ψ

/-- **The discharge (lattice form)**: the point comes from `Ψ(i, 1)`. -/
theorem field_of_printP (hT : ObjBridge.TorsionStructure) (h1 : Y3FineModuliAbP)
    (h2 : DeligneCanonicalModelY3EveryP) : ShimuraMainThmIDeligneY3AbU := by
  obtain ⟨Y, Φ, h⟩ := h1
  obtain ⟨Ψ, hb, hU⟩ := h2 Y Φ h
  exact ⟨Y, Φ, ab_of_np (np_of_P hT h) (nonempty_qbar_of_cpt Y h.1 (Ψ UpperHalfPlane.I 1)), Ψ, hb, hU⟩

theorem y3FineModuliAbP_of_field (hT : ObjBridge.TorsionStructure) (h : ShimuraMainThmIDeligneY3AbU) :
    Y3FineModuliAbP := by
  obtain ⟨Y, Φ, h1, -⟩ := h
  exact ⟨Y, Φ, P_of_np hT (np_of_ab h1)⟩

theorem deligneP_of_field (hT : ObjBridge.TorsionStructure) (h : ShimuraMainThmIDeligneY3AbU) :
    DeligneCanonicalModelY3EveryP := by
  obtain ⟨Y, Φ, h1, Ψ, hb, hU⟩ := h
  intro Y' Φ' h'
  obtain ⟨k, hk⟩ := compare_iso_np (np_of_ab h1) (np_of_P hT h')
  exact ⟨_, Y3ABUPrint.body_transport k hk hb hU⟩

/-! ## 7. The canonical-model leaf in the print's form, and the final discharge -/

section Final

open NumberField IsDedekindDomain TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields

/-- `IsShimuraHolFamily` with its moduli clause in the `H₁`/Hodge form (`IsHodgeH1`) instead of the lattice form. -/
def IsShimuraHolFamilyH (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y)) : Prop :=
  (∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, Φ ℂ (yτ τ) = M3.mk P ∧ IsHodgeH1 P τ) ∧
  ShimuraSplit.IsHolFamily (X := Y.left) (fun τ => (yτ τ).left)

/-- `DeligneBodyAt` with the moduli clause at `g = 1` in the `H₁`/Hodge form (all other clauses verbatim). -/
def DeligneBodyAtH (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)) : Prop :=
    (∀ y : fieldPt ℂ ⟶ Y, ∃ τ g, Ψ τ g = y) ∧
    (∀ τ g τ' g', Ψ τ g = Ψ τ' g' ↔ DCRel τ g τ' g') ∧
    (∀ g, ShimuraSplit.IsHolFamily (X := Y.left) (fun τ => (Ψ τ g).left)) ∧
    IsShimuraHolFamilyH Y Φ (fun τ => Ψ τ 1) ∧
    ∃ (ε : ℤˣ) (δ : Bool),
      ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
      ∀ (κ : K →+* ℂ) (q : K →ₐ[ℚ] LeafQM.B) (z : UpperHalfPlane),
        IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) z →
      ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K), ArtinCondC κ σ s →
      ∀ g : BAQˣ, galPt σ (Ψ z g) = Ψ z (qHatU q s ^ (ε : ℤ) * g)

/-- `ModuliAtUnits` in the `H₁`/Hodge form: at `Ψ(τ, u)`, `u ∈ 𝒪̂^×`, `(H₁(A, ℤ), h_A) ≅ (𝒪, h_τ)`. -/
def ModuliAtUnitsH (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)) : Prop :=
  ∀ u ∈ OhatU, ∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, Φ ℂ (Ψ τ u) = M3.mk P ∧ IsHodgeH1 P τ

/-- **LEAF `DeligneCanonicalModelY3EveryH`: the fine moduli scheme `Y₃`, with its complex moduli interpretation
in the `H₁`/Hodge form, is the canonical model of `Sh_{K₃}(B^×, ℍ^±)`**, for every witness `(Y, Φ)` of the
printed clause list (one object: `Y₃ = Sh_{K₃}`; no existence claim).

*Published statement* (locators recalled, UNVERIFIED; no network): P. Deligne, *Travaux de Shimura*,
Sém. Bourbaki 389 (1971), §4 (the moduli interpretation: `[h, g]` is the abelian variety `A` with
`(H₁(A, ℚ), h_A) ≅ (B, h)` and `H₁(A, ℤ) ↦ L_g = B ∩ 𝒪̂g⁻¹`, with level structure from `g`) and §5
(Cor. 5.7 / Ex. 5.8: the PEL moduli scheme is the canonical model over the reflex field, with Shimura's
reciprocity law at CM points); J. S. Milne, *Introduction to Shimura varieties*, §§8, 14. Here `G = B^×`,
`E(G, X) = ℚ`, `K = K₃`.

*Lean form*: `DeligneBodyAt` and `ModuliAtUnits` verbatim except that the moduli clause (at `g = 1` and at every
`u ∈ 𝒪̂^×`, where `L_u = 𝒪`) is `IsHodgeH1 P τ`: `H₁(A, ℤ) = Λ` and `Lie A = ℂ^g` for an analytic uniformization
`φ : ℂ^g/Λ ≅ A(ℂ)` (bp-analytic's `IsUniformization`; Mumford, *Abelian varieties*, §1: `H₁(V/Λ, ℤ) = Λ`), and
an `𝒪`-linear `β : B_ℝ ≅ H₁(A, ℝ)` with `β(𝒪) = H₁(A, ℤ)` and `β(M J_τ) = i β(M)`, `J_τ = h_τ(i)`.

*Form*: a consequence of the print (as for y3abu-print's leaf: the biholomorphism weakened to "bijective,
holomorphic in `τ`"; the moduli clause kept only at `𝒪̂^×` and only for the QM pair; conventions `ε, δ`
existential; `ℍ` with `B^×_+` for `ℍ^±` with `B^×`). Its moduli clause is the print's description of
`[τ, u]`; the passage to the kernel's lattice form is proved (`lattice_of_hodge`). Reading risks: the polarized
PEL problem (locators.md R1); the sign convention `h_τ(i) = J_τ` versus `−J_τ` (Deligne's normalization of
`h`, UNVERIFIED). -/
def DeligneCanonicalModelY3EveryH : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpPropsAbP Y Φ →
    ∃ Ψ, DeligneBodyAtH Y Φ Ψ ∧ ModuliAtUnitsH Y Φ Ψ

theorem body_of_H {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)} (h : DeligneBodyAtH Y Φ Ψ) : DeligneBodyAt Y Φ Ψ := by
  obtain ⟨h1, h2, h3, ⟨hm, hh⟩, h5⟩ := h
  refine ⟨h1, h2, h3, ⟨fun τ => ?_, hh⟩, h5⟩
  obtain ⟨P, hP, hH⟩ := hm τ
  exact ⟨P, hP, lattice_of_hodge hH⟩

theorem units_of_H {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)} (h : ModuliAtUnitsH Y Φ Ψ) : ModuliAtUnits Y Φ Ψ := by
  intro u hu τ
  obtain ⟨P, hP, hH⟩ := h u hu τ
  exact ⟨P, hP, lattice_of_hodge hH⟩

/-- The `H₁`-form leaf gives the lattice-form leaf (the uniformization dictionary, clause by clause). -/
theorem deligneP_of_H (h : DeligneCanonicalModelY3EveryH) : DeligneCanonicalModelY3EveryP := by
  intro Y Φ hY
  obtain ⟨Ψ, hb, hU⟩ := h Y Φ hY
  exact ⟨Ψ, body_of_H hb, units_of_H hU⟩

/-- **The discharge**: `ShimuraMainThmIDeligneY3AbU` from the two printed-form leaves and the textbook leaf
`mumfordTorsionAlgClosed` (Mumford, *Abelian varieties*, §4, Application 2 (iv), already a field of the
textbook bundle). -/
theorem shimuraMainThmIDeligneY3AbU_of_print (hM : AvSplit.MumfordTorsionAlgClosed)
    (h1 : Y3FineModuliAbP) (h2 : DeligneCanonicalModelY3EveryH) : ShimuraMainThmIDeligneY3AbU :=
  field_of_printP (AvSplit.torsionStructure_of_mumford hM) h1 (deligneP_of_H h2)

theorem body_H_of {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)} (h : DeligneBodyAt Y Φ Ψ) : DeligneBodyAtH Y Φ Ψ := by
  obtain ⟨h1, h2, h3, ⟨hm, hh⟩, h5⟩ := h
  refine ⟨h1, h2, h3, ⟨fun τ => ?_, hh⟩, h5⟩
  obtain ⟨P, hP, Φu, hU, hio⟩ := hm τ
  exact ⟨P, hP, hodge_of_lattice hU hio⟩

theorem units_H_of {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)} (h : ModuliAtUnits Y Φ Ψ) : ModuliAtUnitsH Y Φ Ψ := by
  intro u hu τ
  obtain ⟨P, hP, Φu, hU, hio⟩ := h u hu τ
  exact ⟨P, hP, hodge_of_lattice hU hio⟩

/-- The `H₁`-form leaf and the lattice-form leaf (over the printed clause list) are equivalent. -/
theorem deligneH_iff_P : DeligneCanonicalModelY3EveryH ↔ DeligneCanonicalModelY3EveryP := by
  refine ⟨deligneP_of_H, fun h Y Φ hY => ?_⟩
  obtain ⟨Ψ, hb, hU⟩ := h Y Φ hY
  exact ⟨Ψ, body_H_of hb, units_H_of hU⟩

/-- **Neither new leaf is stronger than the field** (given the textbook field `mumfordTorsionAlgClosed`):
together they are equivalent to `ShimuraMainThmIDeligneY3AbU`. -/
theorem print_iff_field (hM : AvSplit.MumfordTorsionAlgClosed) :
    (Y3FineModuliAbP ∧ DeligneCanonicalModelY3EveryH) ↔ ShimuraMainThmIDeligneY3AbU :=
  ⟨fun h => shimuraMainThmIDeligneY3AbU_of_print hM h.1 h.2, fun h =>
    ⟨y3FineModuliAbP_of_field (AvSplit.torsionStructure_of_mumford hM) h,
     deligneH_iff_P.2 (deligneP_of_field (AvSplit.torsionStructure_of_mumford hM) h)⟩⟩

end Final

end Y3Fix


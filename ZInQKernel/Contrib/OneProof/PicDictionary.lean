import ZInQKernel.OneProof.H.TailZ24
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FreeGeneratorPullback
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Descent
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.PullbackMonoidal
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.Image
import ZInQKernel.Contrib.SmoothFibre.Basic
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.StructureSheaf

/-! # pic-dict: the Pic dictionary at `K̄`, and the rows `weilPairingMumford` and `phiAmpleIsogeny` from printed leaves

Task pic-dict (report `docs/research/pic-dict.md`).

* §1 proves L5, `T09Pic.PicPointsAlgClosed`: at `T = Spec K̄` every fppf covering sieve is maximal, by the
  Nullstellensatz, so `toPicardFunctor` is bijective there.
* §2–§3 prove the dictionary between the kernel's `B(K̄)` (`IsPicZero`) and Mumford's objects on `A_K̄`:
  `picClass` is an injective homomorphism, and `φ_L`, `f^∨` and `σ ∈ G_K` act on points.
* §4 defines Mumford's formula `weilFormula`, the right side of `T09Pic.weilScalar_spec`.
* The transport section proves that the formula is carried along any automorphism commuting with `n_A` and
  intertwining translations (`Transport.wf_transport`). This gives the Galois clause (`weilFormulaGaloisEx`) and
  the adjoint clause (`mumfordWeilDual_of_pairing`).
* §5 states the leaves: Mumford's displays for the abelian variety `A_K̄` over `K̄`.
* §6 assembles `T09Pic.WeilPairingMumford` (`weilPairingMumford_of_printed`).
* §7 assembles `T09Pic.PhiAmpleIsogeny` (`phiAmpleIsogeny_of_printed`), with `finiteOfFiniteKerPts` proved.
* The last part restates the leaves over an algebraically closed field `k` for `X : AbVar k` (namespace `PicDict.AC`;
  leaves `Mumford*AC`). It proves the bridge to `A_K̄ := Over.pullback (Spec K̄ → Spec K)` of `A` (`tr_pts`,
  `mul_AKbar`, `pts`, `formula_bridge`), and gives the main results `weilPairingMumford_of_ac` and
  `phiAmpleIsogeny_of_ac`.
* The adjoint and compatibility properties of `ē_n` are proved from bilinearity by transport
  (`mumfordWeilDual_of_pairing`, `mumfordWeilCompat_of_pairing`).
* The final part proves that the `K̄`-points of `Pic⁰` are translation-invariant (`picZeroPtsTranslInv_of_leaves`):
  vendored Kleiman 9.2.5 and rigidity on `A × Pic⁰`. This gives `phiAmpleIsogeny_of_leaves` from printed leaves
  only.
* The last part reduces `PicZeroAbVar` to four statements (`picZeroAbVar_of_leaves`): the Picard scheme is locally
  of finite type, the identity component of a group scheme is an open geometrically irreducible subgroup, and
  `Pic⁰` is smooth and proper. The open-subgroup glue is proved. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

namespace PicDict

universe u

/-! ## §1. L5: sheafification is the identity at `Spec K̄` -/

/-- A nonempty scheme locally of finite type over an algebraically closed field `k` has a `k`-point
(Mathlib's `pointOfClosedPoint`, Nullstellensatz). -/
theorem exists_section_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (hf : LocallyOfFiniteType f) (x0 : X) :
    ∃ s : Spec (CommRingCat.of k) ⟶ X, s ≫ f = 𝟙 _ := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set X)) ⟨x0, trivial⟩
    isClosed_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx⟩

/-- **Every fppf covering sieve contains every point with values in an algebraically closed field.** -/
theorem fppf_arrows_of_isAlgClosed {X : Scheme.{u}} {S : Sieve X} (hS : S ∈ Scheme.fppfTopology X)
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ X) : S.arrows s := by
  rw [Precoverage.mem_toGrothendieck_iff] at hS
  induction hS with
  | of X R hR =>
    obtain ⟨I, Y, f, rfl⟩ := R.exists_eq_ofArrows
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hR
    obtain ⟨hsurj, hP⟩ := hR
    obtain ⟨i, y, hy⟩ := hsurj (s (IsLocalRing.closedPoint k))
    haveI : Flat (f i) := (hP i).1
    haveI : LocallyOfFinitePresentation (f i) := (hP i).2
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f i) (g := s) y
      (IsLocalRing.closedPoint k) hy
    obtain ⟨σ, hσ⟩ := exists_section_of_isAlgClosed (pullback.snd (f i) s) inferInstance z
    refine ⟨Y i, σ ≫ pullback.fst (f i) s, f i, ⟨i⟩, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  | top X => trivial
  | pullback X S hS Y f ih => exact ih (s ≫ f)
  | transitive X S R hS hR ihS ihR =>
    have h1 := ihR (ihS s) (𝟙 _)
    simpa using h1

/-- `Spec K̄` in `Over (Spec K)`: every fppf covering sieve is the maximal sieve. -/
theorem over_fppf_id_mem {K : Type} [Field K] {S : Sieve (T09Pic.ptK K)}
    (hS : S ∈ (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) (T09Pic.ptK K)) :
    S.arrows (𝟙 _) := by
  rw [GrothendieckTopology.mem_over_iff] at hS
  have h := fppf_arrows_of_isAlgClosed hS (k := AlgebraicClosure K) (𝟙 _)
  replace h := (Sieve.overEquiv_iff S _).1 h
  have h2 := S.downward_closed h
    (Over.homMk (𝟙 (T09Pic.ptK K).left) (by simp) :
      T09Pic.ptK K ⟶ Over.mk (𝟙 _ ≫ (T09Pic.ptK K).hom))
  convert h2 using 1
  ext
  exact (Category.id_comp _).symm

/-- **L5 is a theorem** (`T09Pic.PicPointsAlgClosed`; Kleiman 9.2.5 at `T = Spec K̄`). -/
theorem picPointsAlgClosed : T09Pic.PicPointsAlgClosed := by
  intro K _ A
  constructor
  · intro c c' h
    haveI : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (toPicardFunctor A.X.hom) := Presheaf.isLocallyInjective_toSheafify' _ (picardPresheaf A.X.hom)
    have hm := Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (toPicardFunctor A.X.hom) c c' h
    have := over_fppf_id_mem hm
    simpa [Presheaf.equalizerSieve] using this
  · intro s
    haveI : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (toPicardFunctor A.X.hom) := Presheaf.isLocallySurjective_toSheafify' _ (picardPresheaf A.X.hom)
    have hm := Presheaf.imageSieve_mem (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (toPicardFunctor A.X.hom) s
    obtain ⟨t, ht⟩ := over_fppf_id_mem hm
    exact ⟨t, by simpa using ht⟩

open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing

variable {K : Type} [Field K]

/-- `A_K̄ = A ×_K K̄` as a scheme (the scheme of `weilScalar`). -/
abbrev AK (A : AbVar K) : Scheme.{0} := pullback A.X.hom (ptK K).hom

/-! ## §2. The dictionary `B(K̄) → Pic(A_K̄)`, `y ↦ M_y = picClass y` (glue, proved) -/

section Dictionary

variable {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
  (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} (j : B.X ⟶ P)

theorem toPicardFunctor_picClass (y : B.Pt (AlgebraicClosure K)) :
    (toPicardFunctor A.X.hom).app (op (ptK K)) (picClass rep j y) = rep.homEquiv (y ≫ j) := by
  have h : ∃ c, (toPicardFunctor A.X.hom).app (op (ptK K)) c = rep.homEquiv (y ≫ j) :=
    (picPointsAlgClosed K A).2 _
  have e : picClass rep j y = h.choose := by
    unfold picClass
    exact dif_pos h
  rw [e]
  exact h.choose_spec

theorem picClass_eq_iff (y : B.Pt (AlgebraicClosure K)) (c : (AK A).Pic) :
    picClass rep j y = c ↔
      (toPicardFunctor A.X.hom).app (op (ptK K)) c = rep.homEquiv (y ≫ j) :=
  ⟨fun h => h ▸ toPicardFunctor_picClass rep j y,
   fun h => (picPointsAlgClosed K A).1 ((toPicardFunctor_picClass rep j y).trans h.symm)⟩

theorem picClass_mul {j : B.X ⟶ P} (hj : IsPicZero rep B j) (y y' : B.Pt (AlgebraicClosure K)) :
    picClass rep j (y * y') = picClass rep j y * picClass rep j y' := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  haveI : IsMonHom j := hj.2.2
  rw [picClass_eq_iff, ← Equiv.symm_apply_eq, homEquiv_symm_toPicardFunctor_mul,
    toPicardFunctor_picClass, toPicardFunctor_picClass, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, MonObj.mul_comp]

theorem picClass_injective {j : B.X ⟶ P} (hj : IsPicZero rep B j) :
    Function.Injective (picClass rep j) := by
  intro y y' h
  have h1 := (toPicardFunctor_picClass rep j y).symm.trans
    (h ▸ toPicardFunctor_picClass rep j y')
  have h2 : y ≫ j = y' ≫ j := rep.homEquiv.injective h1
  haveI : IsOpenImmersion j.left := hj.1
  apply Over.OverMorphism.ext
  exact (cancel_mono j.left).1 (by rw [← Over.comp_left, h2, Over.comp_left])

/-- `y ↦ M_y` as a group homomorphism `B(K̄) → Pic(A_K̄)`. -/
def picHom {j : B.X ⟶ P} (hj : IsPicZero rep B j) : B.Pt (AlgebraicClosure K) →* (AK A).Pic :=
  MonoidHom.mk' (picClass rep j) (picClass_mul rep hj)

@[simp] lemma picHom_apply {j : B.X ⟶ P} (hj : IsPicZero rep B j) (y) :
    picHom rep hj y = picClass rep j y := rfl

/-- The Galois action on `B(K̄)` corresponds to pull-back along `1 × Spec σ` on `A_K̄`. -/
theorem picClass_gal (σ : Gal K) (y : B.Pt (AlgebraicClosure K)) :
    picClass rep j (galHom σ ≫ y) =
      Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom (galHom σ)) (picClass rep j y) := by
  rw [picClass_eq_iff]
  have hn := (toPicardFunctor A.X.hom).naturality_apply (galHom σ).op (picClass rep j y)
  refine hn.trans ?_
  rw [toPicardFunctor_picClass, ← rep.homEquiv_comp, Category.assoc]

/-- The dual morphism `f^∨` acts on `K̄`-points of `Pic⁰` by pull-back along `f × 1`. -/
theorem picClass_dual (f : A.X ⟶ A.X) (fv : B.X ⟶ B.X) (hfv : fv ≫ j = j ≫ dualP rep f)
    (y : B.Pt (AlgebraicClosure K)) :
    picClass rep j (y ≫ fv) = Scheme.Pic.map (famMap f (ptK K)) (picClass rep j y) := by
  rw [picClass_eq_iff, Category.assoc, hfv, ← Category.assoc, comp_dualP, Equiv.apply_symm_apply,
    ← toPicardFunctor_picClass]
  have := congrArg (fun τ => τ.app (op (ptK K)) (picClass rep j y))
    (toPicardFunctor_comp_dualSheafMap f)
  exact this.symm

end Dictionary

/-! ## §3. Translations, `φ_L` on points -/

/-- `t_x` on the scheme `A_K̄`. -/
abbrev trl {A : AbVar K} (x : A.Pt (AlgebraicClosure K)) : AK A ⟶ AK A := (transl x).left

/-- `n_A` on the scheme `A_K̄`. -/
abbrev mlN (A : AbVar K) (n : ℕ) : AK A ⟶ AK A := (mulN A n).left

/-- `L_K̄ = p₁^*L`. -/
def bcPic (A : AbVar K) (L : A.X.left.Pic) : (AK A).Pic :=
  Scheme.Pic.map (pullback.fst A.X.hom (ptK K).hom) L

/-- Mumford's `φ_L(x) = t_x^*L ⊗ L⁻¹` (§8). -/
def phiPt {A : AbVar K} (c : (AK A).Pic) (x : A.Pt (AlgebraicClosure K)) : (AK A).Pic :=
  Scheme.Pic.map (trl x) c * c⁻¹

/-- Mumford's `Pic⁰(A_K̄)`: classes invariant under every translation `t_x`, `x ∈ A(K̄)` (§8). -/
def IsTranslInv {A : AbVar K} (c : (AK A).Pic) : Prop :=
  ∀ x : A.Pt (AlgebraicClosure K), Scheme.Pic.map (trl x) c = c

/-- Mumford's `Â_n = Pic⁰(A_K̄)[n]`. -/
def IsDualTors {A : AbVar K} (n : ℕ) (c : (AK A).Pic) : Prop := IsTranslInv c ∧ c ^ n = 1

theorem transl_comp_transl {A : AbVar K} (z x : A.Pt (AlgebraicClosure K)) :
    transl z ≫ transl x = transl (z * x) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [transl, Category.assoc, CartesianMonoidalCategory.lift_fst]
    rw [← CategoryTheory.Hom.mul_def, ← CategoryTheory.Hom.mul_def, ← CategoryTheory.Hom.mul_def,
      MonObj.comp_mul, CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd_assoc,
      mul_assoc, ← MonObj.comp_mul]
  · simp [transl]

/-- **Glue (proved): `φ_L(x)` lies in Mumford's `Pic⁰`**, from the theorem of the square. -/
theorem phiPt_translInv {A : AbVar K}
    (hsq : ∀ (c : (AK A).Pic) (x y : A.Pt (AlgebraicClosure K)),
      Scheme.Pic.map (trl (x * y)) c * c =
        Scheme.Pic.map (trl x) c * Scheme.Pic.map (trl y) c)
    (c : (AK A).Pic) (x : A.Pt (AlgebraicClosure K)) : IsTranslInv (phiPt c x) := by
  intro z
  have h1 : Scheme.Pic.map (trl z) (Scheme.Pic.map (trl x) c) =
      Scheme.Pic.map (trl (z * x)) c := by
    rw [← Scheme.Pic.map_comp, ← Over.comp_left, transl_comp_transl]
  have h2 := hsq c z x
  simp only [phiPt, ← Scheme.Pic.mapHom_apply, map_mul, map_inv] at h2 ⊢
  simp only [Scheme.Pic.mapHom_apply] at h2 ⊢
  rw [h1]
  have : Scheme.Pic.map (trl (z * x)) c =
      Scheme.Pic.map (trl z) c * Scheme.Pic.map (trl x) c * c⁻¹ := by
    rw [← h2]; group
  rw [this, mul_comm (_ * _ * _) _]
  simp [mul_assoc]

/-- `A_K̄ → A × A`, `(a, s) ↦ (a, x(s))` is `(A ◁ x).left`. -/
lemma baseChangeMap_pt {A : AbVar K} (x : A.Pt (AlgebraicClosure K)) :
    JacobianChallenge.baseChangeMap A.X.hom x = (A.X ◁ x).left := by
  apply pullback.hom_ext <;> simp [JacobianChallenge.baseChangeMap]

/-- **`Λ(L)` restricted along `x`** is `φ_{L_K̄}(x)` (glue, proved). -/
theorem map_mumfordBundle_pt {A : AbVar K} (L : A.X.left.Pic) (x : A.Pt (AlgebraicClosure K)) :
    Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom x) (mumfordBundle A L) =
      phiPt (bcPic A L) x := by
  have hμ : JacobianChallenge.baseChangeMap A.X.hom x ≫ (μ[A.X]).left =
      (transl x).left ≫ pullback.fst A.X.hom (ptK K).hom := by
    rw [baseChangeMap_pt, ← Over.comp_left]
    have : (transl x).left ≫ pullback.fst A.X.hom (ptK K).hom =
        (transl x ≫ CartesianMonoidalCategory.fst A.X (ptK K)).left := by simp
    rw [this]
    congr 1
    simp only [transl, CartesianMonoidalCategory.lift_fst]
    congr 1
  have hfst : JacobianChallenge.baseChangeMap A.X.hom x ≫ pullback.fst A.X.hom A.X.hom =
      pullback.fst A.X.hom (ptK K).hom := pullback.lift_fst _ _ _
  have hsnd : JacobianChallenge.baseChangeMap A.X.hom x ≫ pullback.snd A.X.hom A.X.hom =
      pullback.snd _ _ ≫ x.left := pullback.lift_snd _ _ _
  have hS : Scheme.Pic.map x.left L = 1 :=
    Subsingleton.elim (α := (Spec (CommRingCat.of (AlgebraicClosure K))).Pic) _ _
  rw [mumfordBundle, ← Scheme.Pic.mapHom_apply]
  simp only [map_mul, map_inv, Scheme.Pic.mapHom_apply, ← Scheme.Pic.map_comp, hμ, hsnd, hfst]
  rw [Scheme.Pic.map_comp (pullback.snd _ _) x.left, hS, Scheme.Pic.map_one, Scheme.Pic.map_comp]
  simp [phiPt, bcPic]

/-- **`M_{λ_L(x)} = φ_{L_K̄}(x)`** (glue, proved). -/
theorem picClass_phiL {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} {j : B.X ⟶ P}
    (L : A.X.left.Pic) (lam : A.X ⟶ B.X) (hlam : lam ≫ j = phiL rep L)
    (x : A.Pt (AlgebraicClosure K)) :
    picClass rep j (x ≫ lam) = phiPt (bcPic A L) x := by
  rw [picClass_eq_iff, Category.assoc, hlam, phiL, comp_classify, Equiv.apply_symm_apply,
    map_mumfordBundle_pt]

/-- **Lifting `K̄`-points along a surjective morphism locally of finite type** (Nullstellensatz). -/
theorem exists_lift_pt {A B : AbVar K} (lam : A.X ⟶ B.X) [LocallyOfFiniteType lam.left]
    (hs : Surjective lam.left) (y : B.Pt (AlgebraicClosure K)) :
    ∃ x : A.Pt (AlgebraicClosure K), x ≫ lam = y := by
  obtain ⟨a, ha⟩ := hs.surj (y.left (IsLocalRing.closedPoint (AlgebraicClosure K)))
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := lam.left) (g := y.left) a
    (IsLocalRing.closedPoint (AlgebraicClosure K)) ha
  have hlft : LocallyOfFiniteType (pullback.snd lam.left y.left) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback _ _)
      inferInstance
  obtain ⟨σ, hσ⟩ := exists_section_of_isAlgClosed (pullback.snd lam.left y.left) hlft z
  have hc : σ ≫ pullback.fst lam.left y.left ≫ lam.left = y.left := by
    rw [pullback.condition]
    have := congrArg (· ≫ y.left) hσ
    exact (Category.assoc _ _ _).symm.trans (this.trans (Category.id_comp _))
  refine ⟨Over.homMk (σ ≫ pullback.fst lam.left y.left) ?_, ?_⟩
  · change (σ ≫ pullback.fst lam.left y.left) ≫ A.X.hom = (ptK K).hom
    rw [← Over.w lam, Category.assoc, reassoc_of% hc]
    exact Over.w y
  · apply Over.OverMorphism.ext
    show (σ ≫ pullback.fst lam.left y.left) ≫ lam.left = y.left
    rw [Category.assoc]
    exact hc

/-! ## §4. Mumford's `ē_n` by its formula, on any class -/

/-- The module of a class. -/
abbrev mod {A : AbVar K} (c : (AK A).Pic) : (AK A).Modules :=
  (fromSkeleton (AK A).Modules).obj c.val

/-- Trivializations `ψ : 𝒪 ≅ n_A^*M` of `n_A^*M` on `A_K̄`. -/
abbrev Triv (A : AbVar K) (n : ℕ) (c : (AK A).Pic) :=
  Scheme.Modules.unit (AK A) ≅ (Scheme.Modules.pullback (mulN A n).left).obj (mod c)

/-- **Mumford's formula** `ē_n(x, M) = t_x^*ψ ∘ ψ⁻¹ ∈ Γ(A_K̄, 𝒪)` for `x ∈ A[n](K̄)` and a trivialization
`ψ : 𝒪 ≅ n_A^*M` (Mumford §20; the right side of `weilScalar_spec`). -/
def weilFormula {A : AbVar K} {n : ℕ} (x : tors A n) (c : (AK A).Pic) (ψ : Triv A n c) :
    Γ(AK A, ⊤) :=
  Scheme.Modules.unitHomAddEquiv (Scheme.Modules.unit _)
    ((Scheme.Modules.pullbackObjUnitIso (transl (Additive.toMul (x : P A))).left).inv ≫
      (Scheme.Modules.pullback (transl (Additive.toMul (x : P A))).left).map ψ.hom ≫
      (Scheme.Modules.pullbackComp _ _).hom.app _ ≫
      (Scheme.Modules.pullbackCongr (transl_left_comp_mulN_left x)).hom.app _ ≫ ψ.inv)

end PicDict

section TransportSection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

namespace PicDict.Transport

open Scheme.Modules

universe u

variable {X Y Z : Scheme.{u}}

/-- `𝒪 → (f ≫ h)_* 𝒪` is the composite of `𝒪 → h_* 𝒪 → h_* f_* 𝒪`. -/
lemma unitToPushforward_comp (f : X ⟶ Y) (h : Y ⟶ Z) :
    SheafOfModules.unitToPushforwardObjUnit (f ≫ h).toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom ≫
        (pushforward h).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          (pushforwardComp f h).hom.app (unit X) := by
  ext U x
  rfl

/-- **`pullbackObjUnitIso` is compatible with `pullbackComp`.** -/
lemma pullbackObjUnitIso_comp (f : X ⟶ Y) (h : Y ⟶ Z) :
    (pullbackComp f h).inv.app _ ≫ (Scheme.Modules.pullback f).map (pullbackObjUnitIso h).hom ≫
      (pullbackObjUnitIso f).hom = (pullbackObjUnitIso (f ≫ h)).hom := by
  haveI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  haveI : (SheafOfModules.pushforward h.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction h).isRightAdjoint
  haveI : (SheafOfModules.pushforward (f ≫ h).toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction (f ≫ h)).isRightAdjoint
  apply ((pullbackPushforwardAdjunction (f ≫ h)).homEquiv _ _).injective
  have hR : (pullbackPushforwardAdjunction (f ≫ h)).homEquiv _ _ (pullbackObjUnitIso (f ≫ h)).hom =
      SheafOfModules.unitToPushforwardObjUnit (f ≫ h).toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hf : (pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackObjUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hh : (pullbackPushforwardAdjunction h).homEquiv _ _ (pullbackObjUnitIso h).hom =
      SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [hR, unitToPushforward_comp]
  set adj₁ := (pullbackPushforwardAdjunction h).comp (pullbackPushforwardAdjunction f)
  set adj₂ := pullbackPushforwardAdjunction (f ≫ h)
  set Yf := (Scheme.Modules.pullback f).map (pullbackObjUnitIso h).hom ≫ (pullbackObjUnitIso f).hom
  have hc := conjugateEquiv_pullbackComp_inv f h
  have hu := unit_conjugateEquiv adj₁ adj₂ (pullbackComp f h).inv (unit Z)
  rw [hc] at hu
  have key : adj₂.homEquiv _ _ ((pullbackComp f h).inv.app _ ≫ Yf) =
      adj₁.homEquiv _ _ Yf ≫ (pushforwardComp f h).hom.app (unit X) := by
    rw [adj₂.homEquiv_unit, adj₁.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hu,
      Category.assoc, Category.assoc]
    congr 1
  rw [key, ← Category.assoc]
  refine congrArg (fun φ => φ ≫ (pushforwardComp f h).hom.app (unit X)) ?_
  rw [Adjunction.comp_homEquiv]
  show (pullbackPushforwardAdjunction h).homEquiv _ _ ((pullbackPushforwardAdjunction f).homEquiv _ _
    ((Scheme.Modules.pullback f).map (pullbackObjUnitIso h).hom ≫ (pullbackObjUnitIso f).hom)) = _
  rw [Adjunction.homEquiv_naturality_left, hf, Adjunction.homEquiv_naturality_right, hh]

end PicDict.Transport

namespace PicDict.Transport

open Scheme.Modules

universe v

variable {X Y Z W : Scheme.{v}}

lemma pullbackCongr_hom_app {f f' : X ⟶ Y} (e : f = f') (M : Y.Modules) :
    (pullbackCongr e).hom.app M = eqToHom (by rw [e]) := by
  subst e; rfl

/-- naturality of `pullbackComp` in the first variable -/
lemma eqToHom_comp_pullbackComp {f f' : X ⟶ Y} (e : f = f') (h : Y ⟶ Z) (M : Z.Modules)
    (p : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback h).obj M) =
      (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback h).obj M)) :
    eqToHom p ≫ (pullbackComp f' h).hom.app M =
      (pullbackComp f h).hom.app M ≫ eqToHom (by rw [e]) := by
  subst e; simp

/-- naturality of `pullbackComp` in the second variable -/
lemma map_eqToHom_comp_pullbackComp (f : X ⟶ Y) {h h' : Y ⟶ Z} (e : h = h') (M : Z.Modules)
    (p : (Scheme.Modules.pullback h).obj M = (Scheme.Modules.pullback h').obj M) :
    (Scheme.Modules.pullback f).map (eqToHom p) ≫ (pullbackComp f h').hom.app M =
      (pullbackComp f h).hom.app M ≫ eqToHom (by rw [e]) := by
  subst e; simp

/-- associativity of `pullbackComp`, on objects -/
lemma pullbackComp_assoc_app (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫
        (pullbackComp f (g ≫ h)).hom.app M =
      (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (pullbackComp (f ≫ g) h).hom.app M ≫ eqToHom (by rw [Category.assoc]) := by
  have H := congrArg (fun τ => τ.app M) (pseudofunctor_associativity f g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at H
  have H1 := (Iso.inv_comp_eq ((pullbackComp f (g ≫ h)).app M)).mp H
  have H2 := (Iso.inv_comp_eq ((Scheme.Modules.pullback f).mapIso ((pullbackComp g h).app M))).mp H1
  simp only [Functor.mapIso_hom, Iso.app_hom] at H2
  rw [← Category.assoc ((pullbackComp f g).hom.app _), H2]
  simp

lemma pullbackCongr_inv_app {f f' : X ⟶ Y} (e : f = f') (M : Y.Modules) :
    (pullbackCongr e).inv.app M = eqToHom (by rw [e]) := by
  subst e; rfl

lemma pullbackComp_assoc_inv₁ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).inv.app M) ≫
        (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
          (pullbackComp (f ≫ g) h).hom.app M =
      (pullbackComp f (g ≫ h)).hom.app M ≫ eqToHom (by rw [Category.assoc]) := by
  rw [← cancel_epi ((Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M)),
    ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    reassoc_of% (pullbackComp_assoc_app f g h M)]
  simp

lemma pullbackComp_assoc_inv₂ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫
          (pullbackComp f (g ≫ h)).hom.app M =
      (pullbackComp (f ≫ g) h).hom.app M ≫ eqToHom (by rw [Category.assoc]) := by
  rw [pullbackComp_assoc_app, Iso.inv_hom_id_app_assoc]

/-- `g^* m^* M ≅ m^* g^* M` for `g ≫ m = m ≫ g`. -/
def Qiso (g m : X ⟶ X) (hb : g ≫ m = m ≫ g) (M : X.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback m).obj M) ≅
      (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback g).obj M) :=
  (pullbackComp g m).app M ≪≫ (pullbackCongr hb).app M ≪≫ ((pullbackComp m g).app M).symm

/-- `t'^* g^* ≅ g^* t^*` for `t' ≫ g = g ≫ t`. -/
def Niso (t' g t : X ⟶ X) (ha : t' ≫ g = g ≫ t) :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback t' ≅
      Scheme.Modules.pullback t ⋙ Scheme.Modules.pullback g :=
  pullbackComp t' g ≪≫ pullbackCongr ha ≪≫ (pullbackComp g t).symm

/-- **Coherence (II).** -/
lemma coherence_II (t' g m t : X ⟶ X) (ha : t' ≫ g = g ≫ t) (hb : g ≫ m = m ≫ g)
    (h : t ≫ m = m) (h' : t' ≫ m = m) (M : X.Modules) :
    (Niso t' g t ha).inv.app ((Scheme.Modules.pullback m).obj M) ≫
        (Scheme.Modules.pullback t').map (Qiso g m hb M).hom ≫
          (pullbackComp t' m).hom.app ((Scheme.Modules.pullback g).obj M) ≫
            (pullbackCongr h').hom.app ((Scheme.Modules.pullback g).obj M) ≫ (Qiso g m hb M).inv =
      (Scheme.Modules.pullback g).map
        ((pullbackComp t m).hom.app M ≫ (pullbackCongr h).hom.app M) := by
  rw [← cancel_mono ((pullbackComp g m).hom.app M)]
  simp only [Niso, Qiso, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, pullbackCongr_hom_app, pullbackCongr_inv_app]
  -- RHS
  rw [map_eqToHom_comp_pullbackComp g h M, reassoc_of% (pullbackComp_assoc_app g t m M)]
  -- LHS
  rw [reassoc_of% (eqToHom_comp_pullbackComp h' g M)]
  rw [reassoc_of% (pullbackComp_assoc_inv₁ t' m g M)]
  rw [reassoc_of% (map_eqToHom_comp_pullbackComp t' hb M)]
  rw [reassoc_of% (pullbackComp_assoc_inv₂ t' g m M)]
  rw [reassoc_of% (eqToHom_comp_pullbackComp ha.symm m M)]
  simp

/-- `pullbackObjUnitIso` with its type stated through `Scheme.Modules.unit`. -/
def pOU (f : X ⟶ Y) : (Scheme.Modules.pullback f).obj (unit Y) ≅ unit X := pullbackObjUnitIso f

lemma pOU_comp (f : X ⟶ Y) (h : Y ⟶ Z) :
    (pullbackComp f h).inv.app (unit Z) ≫ (Scheme.Modules.pullback f).map (pOU h).hom ≫
      (pOU f).hom = (pOU (f ≫ h)).hom :=
  pullbackObjUnitIso_comp f h

lemma pOU_conj (h : Y ⟶ X) (f : unit X ⟶ unit X) :
    ((pOU h).inv ≫ (Scheme.Modules.pullback h).map f ≫ (pOU h).hom).app ⊤ (1 : Γ(Y, ⊤)) =
      h.appTop (f.app ⊤ (1 : Γ(X, ⊤))) :=
  pullbackObjUnitIso_conj_app_top h f

lemma pOU_inv_comp (f : X ⟶ Y) (h : Y ⟶ Z) :
    (pOU (f ≫ h)).inv = (pOU f).inv ≫
      (Scheme.Modules.pullback f).map (pOU h).inv ≫ (pullbackComp f h).hom.app (unit _) := by
  refine Iso.inv_ext ?_
  rw [← pOU_comp f h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact Iso.inv_hom_id_app _ _

lemma pOU_inv_congr {f f' : X ⟶ Y} (e : f = f') :
    (pOU f).inv ≫ (pullbackCongr e).hom.app (unit _) = (pOU f').inv := by
  subst e; simp [pullbackCongr]

/-- **Coherence (I).** -/
lemma coherence_I (t' g t : X ⟶ X) (ha : t' ≫ g = g ≫ t) :
    (pOU t').inv ≫ (Scheme.Modules.pullback t').map (pOU g).inv ≫
        (Niso t' g t ha).hom.app (unit _) =
      (pOU g).inv ≫ (Scheme.Modules.pullback g).map (pOU t).inv := by
  simp only [Niso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← reassoc_of% (pOU_inv_comp t' g), reassoc_of% (pOU_inv_congr ha), pOU_inv_comp g t]
  simp

/-- The generic Weil formula. -/
def wf (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) : Γ(X, ⊤) :=
  unitHomAddEquiv (unit X) ((pOU t).inv ≫ (Scheme.Modules.pullback t).map ψ.hom ≫
    (pullbackComp t m).hom.app M ≫ (pullbackCongr h).hom.app M ≫ ψ.inv)

/-- The transported trivialization. -/
def transTriv (g m : X ⟶ X) (hb : g ≫ m = m ≫ g) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    unit X ≅ (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback g).obj M) :=
  (pOU g).symm ≪≫ (Scheme.Modules.pullback g).mapIso ψ ≪≫ Qiso g m hb M

/-- **Transport of Mumford's formula along `g`.** -/
theorem wf_transport (t' g m t : X ⟶ X) (ha : t' ≫ g = g ≫ t) (hb : g ≫ m = m ≫ g)
    (h : t ≫ m = m) (h' : t' ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    wf t' m h' ((Scheme.Modules.pullback g).obj M) (transTriv g m hb M ψ) =
      g.appTop (wf t m h M ψ) := by
  simp only [wf, unitHomAddEquiv_apply]
  rw [← pOU_conj g]
  congr 2
  have nat := (Niso t' g t ha).hom.naturality ψ.hom
  have e1 : (Scheme.Modules.pullback t').map ((Scheme.Modules.pullback g).map ψ.hom) =
      (Niso t' g t ha).hom.app _ ≫ (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback t).map ψ.hom) ≫
        (Niso t' g t ha).inv.app _ := by
    simp only [Functor.comp_map] at nat
    rw [← Category.assoc, ← nat]; simp
  simp only [transTriv, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  rw [e1]
  simp only [Category.assoc]
  rw [reassoc_of% (coherence_I t' g t ha)]
  have h2 := coherence_II t' g m t ha hb h h' M
  simp only [Functor.map_comp] at h2
  rw [reassoc_of% h2]

/-- Invariance under isomorphisms of the module. -/
theorem wf_iso (t m : X ⟶ X) (h : t ≫ m = m) {M₁ M₂ : X.Modules} (e : M₁ ≅ M₂)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M₁) :
    wf t m h M₂ (ψ ≪≫ (Scheme.Modules.pullback m).mapIso e) = wf t m h M₁ ψ := by
  have n1 := (pullbackComp t m).hom.naturality e.hom
  have n2 := (pullbackCongr h).hom.naturality e.hom
  simp only [Functor.comp_map] at n1
  simp only [wf, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% n1, reassoc_of% n2]
  simp

end PicDict.Transport

namespace PicDict.Transport
open Scheme.Modules

section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v
variable {X : Scheme.{v}}

/-- **Coherence (III).** -/
lemma coherence_III (t g m t' : X ⟶ X) (ha : t ≫ g = g ≫ t') (h : t' ≫ m = m)
    (h₂ : t ≫ (g ≫ m) = g ≫ m) (M : X.Modules) :
    (Niso t g t' ha).inv.app ((Scheme.Modules.pullback m).obj M) ≫
        (Scheme.Modules.pullback t).map ((pullbackComp g m).hom.app M) ≫
          (pullbackComp t (g ≫ m)).hom.app M ≫ (pullbackCongr h₂).hom.app M ≫
            (pullbackComp g m).inv.app M =
      (Scheme.Modules.pullback g).map
        ((pullbackComp t' m).hom.app M ≫ (pullbackCongr h).hom.app M) := by
  rw [← cancel_mono ((pullbackComp g m).hom.app M)]
  simp only [Niso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, pullbackCongr_hom_app, pullbackCongr_inv_app]
  rw [map_eqToHom_comp_pullbackComp g h M, reassoc_of% (pullbackComp_assoc_app g t' m M)]
  rw [reassoc_of% (pullbackComp_assoc_inv₂ t g m M)]
  rw [reassoc_of% (eqToHom_comp_pullbackComp ha.symm m M)]
  simp

/-- **Transport, second form**: pulling a trivialization back along `g` computes the formula for `g ≫ m`. -/
theorem wf_transport₂ (t g m t' : X ⟶ X) (ha : t ≫ g = g ≫ t') (h : t' ≫ m = m)
    (h₂ : t ≫ (g ≫ m) = g ≫ m) (M : X.Modules) (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    wf t (g ≫ m) h₂ M ((pOU g).symm ≪≫ (Scheme.Modules.pullback g).mapIso ψ ≪≫ (pullbackComp g m).app M) =
      g.appTop (wf t' m h M ψ) := by
  simp only [wf, unitHomAddEquiv_apply]
  rw [← pOU_conj g]
  congr 2
  have nat := (Niso t g t' ha).hom.naturality ψ.hom
  have e1 : (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback g).map ψ.hom) =
      (Niso t g t' ha).hom.app _ ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback t').map ψ.hom) ≫
        (Niso t g t' ha).inv.app _ := by
    simp only [Functor.comp_map] at nat
    rw [← Category.assoc, ← nat]; simp
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc, Iso.app_hom, Iso.app_inv]
  rw [e1]
  simp only [Category.assoc]
  rw [reassoc_of% (coherence_I t g t' ha)]
  have h3 := coherence_III t g m t' ha h h₂ M
  simp only [Functor.map_comp] at h3
  rw [reassoc_of% h3]

lemma wf_congr_m (t : X ⟶ X) {m m' : X ⟶ X} (e : m = m') (h : t ≫ m = m) (h' : t ≫ m' = m')
    (M : X.Modules) (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    wf t m' h' M (ψ ≪≫ (pullbackCongr e).app M) = wf t m h M ψ := by
  subst e
  simp [wf, pullbackCongr]

end

end PicDict.Transport

end TransportSection

namespace PicDict

open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {K : Type} [Field K]

/-- `1 × Spec σ` on `A_K̄`. -/
abbrev gal (A : AbVar K) (σ : Gal K) : AK A ⟶ AK A :=
  JacobianChallenge.baseChangeMap A.X.hom (galHom σ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma gal_eq (A : AbVar K) (σ : Gal K) : gal A σ = (A.X ◁ galHom σ).left := by
  apply Limits.pullback.hom_ext <;> simp [JacobianChallenge.baseChangeMap]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma transl_gal (A : AbVar K) (σ : Gal K) (x : A.Pt (AlgebraicClosure K)) :
    transl (galHom σ ≫ x) ≫ (A.X ◁ galHom σ) = (A.X ◁ galHom σ) ≫ transl x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [transl, CartesianMonoidalCategory.comp_lift_assoc]
  · simp [transl]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma gal_transl (A : AbVar K) (σ : Gal K) (x : A.Pt (AlgebraicClosure K)) :
    trl (galHom σ ≫ x) ≫ gal A σ = gal A σ ≫ trl x := by
  rw [gal_eq, ← Over.comp_left, ← Over.comp_left, transl_gal]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma gal_mulN (A : AbVar K) (σ : Gal K) (n : ℕ) : gal A σ ≫ mlN A n = mlN A n ≫ gal A σ := by
  rw [gal_eq, ← Over.comp_left, ← Over.comp_left]
  congr 1
  unfold mulN
  exact whisker_exchange _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma gal_constK (A : AbVar K) (σ : Gal K) (u : AlgebraicClosure K) :
    (gal A σ).appTop (constK A u) = constK A (σ u) := by
  have hs : gal A σ ≫ Limits.pullback.snd A.X.hom (ptK K).hom =
      Limits.pullback.snd A.X.hom (ptK K).hom ≫ (galHom σ).left := Limits.pullback.lift_snd _ _ _
  simp only [constK, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]
  congr 1
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K))
  exact (congrArg (fun φ => φ.hom u) this).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma weilFormula_eq_wf {A : AbVar K} {n : ℕ} (x : tors A n) (c : (AK A).Pic) (ψ : Triv A n c) :
    weilFormula x c ψ = Transport.wf (trl (Additive.toMul (x : P A))) (mlN A n)
      (transl_left_comp_mulN_left x) (mod c) ψ := rfl

/-- **GLUE, proved form**: transport along `σ ∈ G_K`. -/
def WeilFormulaGaloisEx : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ) (σ : Gal K) (x : tors A n) (c c' : (AK A).Pic),
      c' = Scheme.Pic.map (gal A σ) c →
      ∀ (ψ : Triv A n c) (u : AlgebraicClosure K),
        weilFormula x c ψ = constK A u →
          ∃ ψ' : Triv A n c', weilFormula (galTors A n σ x) c' ψ' = constK A (σ u)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem weilFormulaGaloisEx : WeilFormulaGaloisEx := by
  intro K _ A n σ x c c' hc ψ u hu
  subst hc
  let e : (Scheme.Modules.pullback (gal A σ)).obj (mod c) ≅ mod (Scheme.Pic.map (gal A σ) c) :=
    (Scheme.Pic.mkIso _).symm
  refine ⟨Transport.transTriv (gal A σ) (mlN A n) (gal_mulN A σ n) (mod c) ψ ≪≫
    (Scheme.Modules.pullback (mlN A n)).mapIso e, ?_⟩
  have ha : (transl (Additive.toMul ((galTors A n σ x : tors A n) : P A))).left ≫ gal A σ =
      gal A σ ≫ trl (Additive.toMul (x : P A)) := gal_transl A σ _
  have h1 := Transport.wf_iso (transl (Additive.toMul ((galTors A n σ x : tors A n) : P A))).left (mlN A n)
    (transl_left_comp_mulN_left (galTors A n σ x)) e
    (Transport.transTriv (gal A σ) (mlN A n) (gal_mulN A σ n) (mod c) ψ)
  have h2 := Transport.wf_transport (transl (Additive.toMul ((galTors A n σ x : tors A n) : P A))).left
    (gal A σ) (mlN A n) (trl (Additive.toMul (x : P A))) ha (gal_mulN A σ n)
    (transl_left_comp_mulN_left x) (transl_left_comp_mulN_left (galTors A n σ x)) (mod c) ψ
  have h3 : weilFormula x c ψ = Transport.wf (trl (Additive.toMul (x : P A))) (mlN A n)
    (transl_left_comp_mulN_left x) (mod c) ψ := rfl
  have h4 := weilFormula_eq_wf (galTors A n σ x) (Scheme.Pic.map (gal A σ) c)
      (Transport.transTriv (gal A σ) (mlN A n) (gal_mulN A σ n) (mod c) ψ ≪≫
        (Scheme.Modules.pullback (mlN A n)).mapIso e)
  rw [h4, h1, h2, ← h3, hu]
  exact gal_constK A σ u


/-! ## §5. Leaves: Mumford's printed statements for the abelian variety `X = A_K̄` over `k = K̄` -/

/-- **LEAF (theorem of the square).** For an abelian variety `X` over an algebraically closed field `k`,
`L ∈ Pic(X)` and `x, y ∈ X(k)`: `t_{x+y}^*L ⊗ L ≅ t_x^*L ⊗ t_y^*L`. Mumford, *Abelian varieties*, §6,
Cor. 4 (UNVERIFIED numbering). Instance `X = A_K̄`, `X(K̄) = A(K̄)`. -/
def MumfordSquare : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (c : (AK A).Pic) (x y : A.Pt (AlgebraicClosure K)),
    Scheme.Pic.map (trl (x * y)) c * c =
      Scheme.Pic.map (trl x) c * Scheme.Pic.map (trl y) c

/-- **LEAF (`n_X^*L ≅ Lⁿ` on `Pic⁰`).** For `L ∈ Pic⁰(X)` (`t_x^*L ≅ L` for all `x ∈ X(k)`), `n_X^*L ≅ Lⁿ`.
Mumford §8 (iv) (UNVERIFIED numbering). Instance `X = A_K̄`. -/
def MumfordMulNPicZero : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (c : (AK A).Pic), IsTranslInv c →
    ∀ n : ℕ, Scheme.Pic.map (mlN A n) c = c ^ n

/-- **LEAF (`φ_L` maps onto `Pic⁰`).** For `L` ample and `M ∈ Pic⁰(X)` there is `x ∈ X(k)` with
`M ≅ t_x^*L ⊗ L⁻¹`. Mumford §8, Thm 1 (UNVERIFIED numbering). Instance `X = A_K̄`. -/
def MumfordPhiSurjective : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (c₀ : (AK A).Pic), IsAmple (AK A) c₀ →
    ∀ c : (AK A).Pic, IsTranslInv c → ∃ x : A.Pt (AlgebraicClosure K), c = phiPt c₀ x

/-- **LEAF (ampleness and field extension).** If `L` is ample on `X` over `K` then `L_{K'}` is ample on
`X_{K'}` for a field extension `K'/K` (EGA II 4.6.13 (iii); Stacks, Tag 0D2M? UNVERIFIED numbering).
Instance `K' = K̄`. -/
def AmpleBaseChangeAlgClosure : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : A.X.left.Pic), IsAmple A.X.left L →
    IsAmple (AK A) (bcPic A L)

/-- **LEAF (`ē_n` well defined, `μ_n`-valued, bilinear).** For `x, x' ∈ X_n` and `M, M' ∈ X̂_n`, Mumford's
`ē_n(x, M) = t_x^*ψ ∘ ψ⁻¹` does not depend on the trivialization `ψ : 𝒪 ≅ n^*M`, is a constant in `μ_n(k)`,
and is bimultiplicative. Mumford §20 (definition of `ē_n` and its bilinearity; UNVERIFIED numbering).
Instance `X = A_K̄`, stated for `n ≥ 1` prime to the characteristic. -/
def MumfordWeilPairing : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), 0 < n → (n : K) ≠ 0 →
    ∀ (x x' : tors A n) (c c' : (AK A).Pic), IsDualTors n c → IsDualTors n c' →
      (∀ ψ ψ' : Triv A n c, weilFormula x c ψ = weilFormula x c ψ') ∧
      (∀ ψ : Triv A n c, ∃ u : (AlgebraicClosure K)ˣ, u ^ n = 1 ∧
        constK A (u : AlgebraicClosure K) = weilFormula x c ψ) ∧
      (∀ ψ : Triv A n c, weilFormula (x + x') c ψ = weilFormula x c ψ * weilFormula x' c ψ) ∧
      (∀ (ψ : Triv A n c) (ψ' : Triv A n c') (ψ'' : Triv A n (c * c')),
        weilFormula x (c * c') ψ'' = weilFormula x c ψ * weilFormula x c' ψ')

/-- **LEAF (`ē_n` nondegenerate).** For `n` prime to the characteristic, `ē_n : X_n × X̂_n → μ_n` has trivial
kernels. Mumford §20 (UNVERIFIED numbering). Instance `X = A_K̄`. -/
def MumfordWeilNondeg : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), 0 < n → (n : K) ≠ 0 →
    (∀ x : tors A n, (∀ c : (AK A).Pic, IsDualTors n c → ∀ ψ : Triv A n c, weilFormula x c ψ = 1) →
      x = 0) ∧
    (∀ c : (AK A).Pic, IsDualTors n c → (∀ (x : tors A n) (ψ : Triv A n c), weilFormula x c ψ = 1) →
      c = 1)

/-- **`ē_{mn}(x, M) = ē_n(mx, M)` for `M ∈ X̂_n` (proved below from `MumfordWeilPairing`, `mumfordWeilCompat_of_pairing`).** Mumford §20 (UNVERIFIED numbering). Instance
`X = A_K̄`. -/
def MumfordWeilCompat : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (m n : ℕ), 0 < m → 0 < n → ((m * n : ℕ) : K) ≠ 0 →
    ∀ (x : tors A (m * n)) (c : (AK A).Pic), IsDualTors n c →
      ∀ (ψ : Triv A (m * n) c) (ψ' : Triv A n c),
        weilFormula x c ψ = weilFormula (torsSmul A m n x) c ψ'

/-- **`ē_n(x, f^*M) = ē_n(f x, M)` (proved below from `MumfordWeilPairing`, `mumfordWeilDual_of_pairing`).** For a homomorphism `f : X → X`, Mumford §20 (5) (stated there for
isogenies) and Milne 1986, Lemma 16.2(c) (every homomorphism); UNVERIFIED numbering. Instance `X = A_K̄`,
`f = g_K̄` for `g ∈ End_K(A)`. -/
def MumfordWeilDual : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), 0 < n → (n : K) ≠ 0 →
    ∀ (f : End A) (x : tors A n) (c : (AK A).Pic), IsDualTors n c →
      ∀ (ψ : Triv A n (Scheme.Pic.map (famMap f.hom (ptK K)) c)) (ψ' : Triv A n c),
        weilFormula x (Scheme.Pic.map (famMap f.hom (ptK K)) c) ψ = weilFormula (torsMap f n x) c ψ'

/-- **LEAF (`e^L_n(x, x) = 1`).** For `L ∈ Pic(X)` and `x ∈ X_n`, `ē_n(x, φ_L(x)) = 1`. Mumford §23
(`e^L_n(x, y) = ē_n(x, φ_L(y))` and `e^L_n(x, x) = 1`; UNVERIFIED numbering). Instance `X = A_K̄`. -/
def MumfordWeilAlt : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), 0 < n → (n : K) ≠ 0 →
    ∀ (c₀ : (AK A).Pic) (x : tors A n) (ψ : Triv A n (phiPt c₀ (Additive.toMul (x : P A)))),
      weilFormula x (phiPt c₀ (Additive.toMul (x : P A))) ψ = 1

/-! ## §5b. `MumfordWeilDual` is a consequence of `MumfordWeilPairing` (transport along `f × 1`) -/

lemma famMap_eq (A : AbVar K) (f : A.X ⟶ A.X) : famMap f (ptK K) = (f ▷ ptK K).left := by
  apply Limits.pullback.hom_ext <;> simp

lemma transl_famMap (A : AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] (x : A.Pt (AlgebraicClosure K)) :
    transl x ≫ (f ▷ ptK K) = (f ▷ ptK K) ≫ transl (x ≫ f) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [transl, Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
      CartesianMonoidalCategory.lift_fst_assoc, CartesianMonoidalCategory.lift_fst]
    rw [← Category.assoc, ← CategoryTheory.Hom.mul_def, MonObj.mul_comp, ← CategoryTheory.Hom.mul_def,
      MonObj.comp_mul]
    simp
  · simp [transl]

lemma famMap_mulN (A : AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] (n : ℕ) :
    (f ▷ ptK K) ≫ mulN A n = mulN A n ≫ (f ▷ ptK K) := by
  unfold mulN
  rw [← comp_whiskerRight, ← comp_whiskerRight]
  congr 1
  rw [MonObj.comp_pow, Category.comp_id, MonObj.pow_comp, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma famMap_constK (A : AbVar K) (f : A.X ⟶ A.X) (u : AlgebraicClosure K) :
    (famMap f (ptK K)).appTop (constK A u) = constK A u := by
  have hs : famMap f (ptK K) ≫ Limits.pullback.snd A.X.hom (ptK K).hom =
      Limits.pullback.snd A.X.hom (ptK K).hom := by simp
  simp only [constK, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs]

lemma famMap_dualTors {A : AbVar K} (f : End A) {n : ℕ} {c : (AK A).Pic} (hc : IsDualTors n c) :
    IsDualTors n (Scheme.Pic.map (famMap f.hom (ptK K)) c) := by
  refine ⟨fun z => ?_, ?_⟩
  · have h1 : trl z ≫ famMap f.hom (ptK K) = famMap f.hom (ptK K) ≫ trl (z ≫ f.hom) := by
      rw [famMap_eq, ← Over.comp_left, ← Over.comp_left, transl_famMap]
    rw [← Scheme.Pic.map_comp, h1, Scheme.Pic.map_comp, hc.1]
  · rw [← Scheme.Pic.mapHom_apply, ← map_pow, hc.2, map_one]

/-- **`MumfordWeilDual` from `MumfordWeilPairing`** (transport along `f × 1`). -/
theorem mumfordWeilDual_of_pairing (h20a : MumfordWeilPairing) : MumfordWeilDual := by
  intro K _ A n hn hnK f x c hc ψ ψ'
  have hb : famMap f.hom (ptK K) ≫ mlN A n = mlN A n  ≫ famMap f.hom (ptK K) := by
    rw [famMap_eq, ← Over.comp_left, ← Over.comp_left, famMap_mulN]
  have ha : trl (Additive.toMul (x : P A))  ≫ famMap f.hom (ptK K) = famMap f.hom (ptK K) ≫ trl (Additive.toMul ((torsMap f n x : tors A n) : P A)) := by
    rw [famMap_eq, ← Over.comp_left, ← Over.comp_left, transl_famMap]
    rfl
  let e : (Scheme.Modules.pullback (famMap f.hom (ptK K))).obj (mod c) ≅ mod (Scheme.Pic.map (famMap f.hom (ptK K)) c) := (Scheme.Pic.mkIso _).symm
  let ψ'' : Triv A n (Scheme.Pic.map (famMap f.hom (ptK K)) c) :=
    Transport.transTriv (famMap f.hom (ptK K)) (mlN A n) hb (mod c) ψ' ≪≫ (Scheme.Modules.pullback (mlN A n)).mapIso e
  have hc' := famMap_dualTors f hc
  rw [(h20a K A n hn hnK x x _ _ hc' hc').1 ψ ψ'']
  obtain ⟨u, -, hu⟩ := (h20a K A n hn hnK (torsMap f n x) (torsMap f n x) c c hc hc).2.1 ψ'
  have h1 := Transport.wf_iso (trl (Additive.toMul (x : P A))) (mlN A n) (transl_left_comp_mulN_left x) e
    (Transport.transTriv (famMap f.hom (ptK K)) (mlN A n) hb (mod c) ψ')
  have h2 := Transport.wf_transport (trl (Additive.toMul (x : P A))) (famMap f.hom (ptK K)) (mlN A n)
    (trl (Additive.toMul ((torsMap f n x : tors A n) : P A))) ha hb
    (transl_left_comp_mulN_left (torsMap f n x)) (transl_left_comp_mulN_left x) (mod c) ψ'
  rw [weilFormula_eq_wf, h1, h2, ← weilFormula_eq_wf, ← hu]
  exact famMap_constK A f.hom u


/-! ## §5c. `MumfordWeilCompat` is a consequence of `MumfordWeilPairing` (transport along `m_A`) -/

lemma mulN_mul (A : AbVar K) (m n : ℕ) : mlN A (m * n) = mlN A m ≫ mlN A n := by
  show (mulN A (m * n)).left = (mulN A m ≫ mulN A n).left
  congr 1
  unfold mulN
  rw [← comp_whiskerRight, MonObj.comp_pow, Category.comp_id, ← pow_mul]

lemma transl_mulN (A : AbVar K) (m : ℕ) (x : A.Pt (AlgebraicClosure K)) :
    transl x ≫ mulN A m = mulN A m ≫ transl (x ^ m) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [transl, mulN, Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
      CartesianMonoidalCategory.lift_fst_assoc, CartesianMonoidalCategory.lift_fst]
    rw [← Category.assoc, ← CategoryTheory.Hom.mul_def, MonObj.comp_pow, Category.comp_id, mul_pow,
      ← CategoryTheory.Hom.mul_def, MonObj.comp_mul]
    simp [MonObj.comp_pow]
  · simp [transl, mulN]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma mulN_constK (A : AbVar K) (m : ℕ) (u : AlgebraicClosure K) :
    (mlN A m).appTop (constK A u) = constK A u := by
  have hs : mlN A m ≫ Limits.pullback.snd A.X.hom (ptK K).hom = Limits.pullback.snd A.X.hom (ptK K).hom := by
    show (mulN A m).left ≫ (CartesianMonoidalCategory.snd A.X (ptK K)).left =
      (CartesianMonoidalCategory.snd A.X (ptK K)).left
    rw [← Over.comp_left]
    unfold mulN
    rw [CartesianMonoidalCategory.whiskerRight_snd]
  simp only [constK, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs]

/-- **`MumfordWeilCompat` from `MumfordWeilPairing`** (transport along `m_A`). -/
theorem mumfordWeilCompat_of_pairing (h20a : MumfordWeilPairing) : MumfordWeilCompat := by
  intro K _ A m n hm hn hmnK x c hc ψ ψ'
  have hnK : (n : K) ≠ 0 := by intro h; apply hmnK; rw [Nat.cast_mul, h, mul_zero]
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  have hc' : IsDualTors (m * n) c := ⟨hc.1, by rw [mul_comm, pow_mul, hc.2, one_pow]⟩
  have ha : trl (Additive.toMul (x : P A)) ≫ mlN A m =
      mlN A m ≫ trl (Additive.toMul ((torsSmul A m n x : tors A n) : P A)) := by
    rw [← Over.comp_left, ← Over.comp_left, transl_mulN]
    rfl
  have h₂ : trl (Additive.toMul (x : P A)) ≫ (mlN A m ≫ mlN A n) = mlN A m ≫ mlN A n := by
    rw [← mulN_mul]; exact transl_left_comp_mulN_left x
  let ψ₂ := (Transport.pOU (mlN A m)).symm ≪≫ (Scheme.Modules.pullback (mlN A m)).mapIso ψ' ≪≫
    (Scheme.Modules.pullbackComp (mlN A m) (mlN A n)).app (mod c)
  let ψ₃ : Triv A (m * n) c := ψ₂ ≪≫ (Scheme.Modules.pullbackCongr (mulN_mul A m n).symm).app (mod c)
  rw [(h20a K A (m * n) hmn hmnK x x c c hc' hc').1 ψ ψ₃]
  obtain ⟨u, -, hu⟩ := (h20a K A n hn hnK (torsSmul A m n x) (torsSmul A m n x) c c hc hc).2.1 ψ'
  have h1 := Transport.wf_congr_m (trl (Additive.toMul (x : P A))) (mulN_mul A m n).symm h₂
    (transl_left_comp_mulN_left x) (mod c) ψ₂
  have h2 := Transport.wf_transport₂ (trl (Additive.toMul (x : P A))) (mlN A m) (mlN A n)
    (trl (Additive.toMul ((torsSmul A m n x : tors A n) : P A))) ha
    (transl_left_comp_mulN_left (torsSmul A m n x)) h₂ (mod c) ψ'
  rw [weilFormula_eq_wf, h1, h2, ← weilFormula_eq_wf, ← hu]
  exact mulN_constK A m u


/-! ## §6. Assembly: `WeilPairingMumford` from the leaves (glue, proved) -/

theorem constK_injective (A : AbVar K) : Function.Injective (constK A) := by
  have : Nonempty (𝟙_ (Over (Spec (CommRingCat.of K)))).left :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of K)))
  have : Nonempty A.X.left := ⟨η[A.X].left (Nonempty.some inferInstance)⟩
  have : Nonempty (ptK K).left :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of (AlgebraicClosure K))))
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hX : Nonempty ↥(pullback A.X.hom (ptK K).hom : Scheme.{0}) := inferInstance
  have : Nonempty (⊤ : (pullback A.X.hom (ptK K).hom : Scheme.{0}).Opens) :=
    ⟨⟨hX.some, trivial⟩⟩
  exact (constK A).injective

theorem nonempty_triv {A : AbVar K} {n : ℕ} {c : (AK A).Pic}
    (h : Scheme.Pic.map (mlN A n) c = 1) : Nonempty (Triv A n c) := by
  obtain ⟨e⟩ := Scheme.Pic.eq_iff_nonempty_iso.1 h
  exact ⟨(Scheme.Pic.oneIso).symm ≪≫ e.symm ≪≫ Scheme.Pic.mkIso _⟩

theorem weilFormula_congr {A : AbVar K} {n : ℕ} (x : tors A n) {c c' : (AK A).Pic} (h : c = c')
    (ψ : Triv A n c) : weilFormula x c' (h ▸ ψ) = weilFormula x c ψ := by
  subst h; rfl

/-- The pairing with values `u x y`, as a `Pairing`. -/
def mkPairing {A B : AbVar K} {n : ℕ} (u : tors A n → tors B n → (AlgebraicClosure K)ˣ)
    (hu : ∀ x y, u x y ^ n = 1) (hx : ∀ x x' y, u (x + x') y = u x y * u x' y)
    (hy : ∀ x y y', u x (y + y') = u x y * u x y') : Pairing A B n :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
      (fun y => Additive.ofMul (⟨u x y, (mem_rootsOfUnity n _).2 (hu x y)⟩ :
        rootsOfUnity n (AlgebraicClosure K)))
      (fun y y' => by
        apply Additive.toMul.injective
        apply Subtype.ext
        simp [hy]))
    (fun x x' => by
      refine AddMonoidHom.ext fun y => ?_
      apply Additive.toMul.injective
      apply Subtype.ext
      simp [hx])

@[simp] lemma mkPairing_val {A B : AbVar K} {n : ℕ} (u : tors A n → tors B n → (AlgebraicClosure K)ˣ)
    (hu hx hy) (x y) : (mkPairing (n := n) u hu hx hy x y).val = u x y := rfl

/-- **Main result (`WeilPairingMumford`).** From Mumford's statements at `A_K̄` (theorem of the square,
§8 (iv), §8 Thm 1, §20, §23), ampleness under field extension and the row `PhiAmpleIsogeny`; L5
(`picPointsAlgClosed`), the dictionary and the Galois transport (`weilFormulaGaloisEx`) are proved. -/
theorem weilPairingMumford_of_printed (hsq : MumfordSquare) (h8iv : MumfordMulNPicZero)
    (h8 : MumfordPhiSurjective) (hamp : AmpleBaseChangeAlgClosure) (h20a : MumfordWeilPairing)
    (h20b : MumfordWeilNondeg)
    (h23 : MumfordWeilAlt) (h3 : PhiAmpleIsogeny) :
    WeilPairingMumford := by
  classical
  have h20d := mumfordWeilDual_of_pairing h20a
  have h20c := mumfordWeilCompat_of_pairing h20a
  intro K _ A P rep B j hj
  obtain ⟨L, hL⟩ := exists_isVeryAmple A
  have hLa := veryAmpleIsAmple K A L hL
  obtain ⟨lam, hlam⟩ := exists_hom_comp_eq_phiL rep hj L
  obtain ⟨hfin, hsurj⟩ := h3 K A P rep B j hj L hLa lam.hom hlam
  -- `B(K̄) ⊆ Pic⁰(A_K̄)`
  have hsub : ∀ y, IsTranslInv (picClass rep j y) := fun y => by
    obtain ⟨x, rfl⟩ := exists_lift_pt lam.hom hsurj y
    rw [picClass_phiL rep L lam.hom hlam x]
    exact phiPt_translInv (hsq K A) _ x
  -- `Pic⁰(A_K̄) ⊆ B(K̄)`
  have hsup : ∀ c, IsTranslInv c → ∃ y, picClass rep j y = c := fun c hc => by
    obtain ⟨x, rfl⟩ := h8 K A _ (hamp K A L hLa) c hc
    exact ⟨x ≫ lam.hom, picClass_phiL rep L lam.hom hlam x⟩
  have hone : picClass rep j 1 = 1 := map_one (picHom rep hj)
  have htors : ∀ (n : ℕ) (y : tors B n),
      IsDualTors n (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B))) := fun n y => by
    refine ⟨hsub _, ?_⟩
    rw [← picHom_apply rep hj, ← map_pow, ← toMul_nsmul, nsmul_tors y]
    exact hone
  have htriv : ∀ (n : ℕ) (y : tors B n),
      Nonempty (Triv A n (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B)))) :=
    fun n y => nonempty_triv (by rw [h8iv K A _ (hsub _) n, (htors n y).2])
  have hspec : ∀ (n : ℕ) (x : tors A n) (y : tors B n),
      weilScalar rep j n (Additive.toMul (x : HDec.WeilPairing.P A))
          (Additive.toMul (y : HDec.WeilPairing.P B)) =
        weilFormula x (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B))) (htriv n y).some := by
    intro n x y
    unfold weilScalar
    rw [dite_eq_left (transl_left_comp_mulN_left x)]
    exact dite_eq_left (htriv n y)
  have hval : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (y : tors B n),
      ∃ u : (AlgebraicClosure K)ˣ, u ^ n = 1 ∧ constK A (u : AlgebraicClosure K) =
        weilScalar rep j n (Additive.toMul (x : HDec.WeilPairing.P A))
          (Additive.toMul (y : HDec.WeilPairing.P B)) := by
    intro n hn hnK x y
    rw [hspec]
    exact (h20a K A n hn hnK x x _ _ (htors n y) (htors n y)).2.1 _
  choose u hu1 hu2 using hval
  -- the values are pinned by `weilScalar`
  have hpin : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (y : tors B n)
      (v : (AlgebraicClosure K)ˣ), constK A (v : AlgebraicClosure K) =
        weilScalar rep j n (Additive.toMul (x : HDec.WeilPairing.P A))
          (Additive.toMul (y : HDec.WeilPairing.P B)) → u n hn hnK x y = v := by
    intro n hn hnK x y v hv
    exact Units.ext (constK_injective A ((hu2 n hn hnK x y).trans hv.symm))
  have hux : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x x' : tors A n) (y : tors B n),
      u n hn hnK (x + x') y = u n hn hnK x y * u n hn hnK x' y := by
    intro n hn hnK x x' y
    apply hpin
    rw [Units.val_mul, map_mul, hu2, hu2, hspec, hspec, hspec]
    exact ((h20a K A n hn hnK x x' _ _ (htors n y) (htors n y)).2.2.1 _).symm
  have huy : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (y y' : tors B n),
      u n hn hnK x (y + y') = u n hn hnK x y * u n hn hnK x y' := by
    intro n hn hnK x y y'
    apply hpin
    rw [Units.val_mul, map_mul, hu2, hu2, hspec, hspec, hspec]
    have hc : picClass rep j (Additive.toMul ((y + y' : tors B n) : HDec.WeilPairing.P B)) =
        picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B)) *
          picClass rep j (Additive.toMul (y' : HDec.WeilPairing.P B)) :=
      picClass_mul rep hj _ _
    rw [← weilFormula_congr x hc]
    exact ((h20a K A n hn hnK x x _ _ (htors n y) (htors n y')).2.2.2 _ _ _).symm
  let e : ∀ n : ℕ, Pairing A B n := fun n =>
    if h : 0 < n ∧ (n : K) ≠ 0 then
      mkPairing (u n h.1 h.2) (hu1 n h.1 h.2) (hux n h.1 h.2) (huy n h.1 h.2)
    else 0
  have he : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (y : tors B n),
      (e n x y).val = u n hn hnK x y := by
    intro n hn hnK x y
    simp only [e, dif_pos (And.intro hn hnK), mkPairing_val]
  have he0 : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (y : tors B n),
      e n x y = 0 ↔ weilFormula x (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B)))
        (htriv n y).some = 1 := by
    intro n hn hnK x y
    constructor
    · intro h
      have h1 := he n hn hnK x y
      rw [h, Mu.val_zero] at h1
      rw [← hspec, ← hu2 n hn hnK x y, ← h1]
      simp
    · intro h
      apply Mu.val_injective
      rw [he n hn hnK x y, Mu.val_zero]
      apply hpin
      rw [hspec, h]
      simp
  -- independence of the trivialization
  have hind : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (c : (AK A).Pic),
      IsDualTors n c → ∀ ψ ψ' : Triv A n c, weilFormula x c ψ = weilFormula x c ψ' :=
    fun n hn hnK x c hc ψ ψ' => (h20a K A n hn hnK x x c c hc hc).1 ψ ψ'
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- perfect
    intro n hn hnK
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · apply (h20b K A n hn hnK).1 x
      intro c hc ψ
      obtain ⟨y0, hy0⟩ := hsup c hc.1
      have hy0t : Additive.ofMul y0 ∈ tors B n := by
        rw [mem_tors]
        apply Additive.toMul.injective
        apply picClass_injective rep hj
        rw [toMul_nsmul, toMul_ofMul, toMul_zero, ← picHom_apply rep hj, map_pow, picHom_apply, hy0,
          hc.2, hone]
      have h1 := (he0 n hn hnK x ⟨_, hy0t⟩).1 (hx _)
      have hy0' : picClass rep j (Additive.toMul ((⟨_, hy0t⟩ : tors B n) : HDec.WeilPairing.P B)) =
          c := hy0
      rw [← weilFormula_congr x hy0'] at h1
      rw [hind n hn hnK x c hc ψ _]
      exact h1
    · have hc := (h20b K A n hn hnK).2 _ (htors n y) (fun x ψ => by
        rw [hind n hn hnK x _ (htors n y) ψ (htriv n y).some]
        exact (he0 n hn hnK x y).1 (hy x))
      exact Subtype.ext (Additive.toMul.injective (picClass_injective rep hj (hc.trans hone.symm)))
  · -- Galois
    intro n hn hnK σ x y
    apply Mu.val_injective
    apply Units.ext
    rw [he n hn hnK, galMu_val, he n hn hnK]
    apply constK_injective A
    rw [hu2, hspec]
    have hg : picClass rep j (Additive.toMul ((galTors B n σ y : tors B n) : HDec.WeilPairing.P B)) =
        Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom (galHom σ))
          (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B))) :=
      picClass_gal rep j σ _
    obtain ⟨ψ', hψ'⟩ := weilFormulaGaloisEx K A n σ x _ _ hg (htriv n y).some _
      ((hspec n x y).symm.trans (hu2 n hn hnK x y).symm)
    rw [hind n hn hnK _ _ (htors n (galTors B n σ y)) _ ψ']
    exact hψ'
  · -- compatibility
    intro m n hm hn hmnK x y
    have hnK : (n : K) ≠ 0 := by
      intro h; apply hmnK; rw [Nat.cast_mul, h, mul_zero]
    have hmn : 0 < m * n := Nat.mul_pos hm hn
    rw [he (m * n) hmn hmnK, he n hn hnK]
    apply hpin
    rw [hu2, hspec, hspec]
    exact (h20c K A m n hm hn hmnK x _ (htors n y) _ _).symm
  · -- adjoint
    intro f fv hfv n hn hnK x y
    apply Mu.val_injective
    rw [he n hn hnK, he n hn hnK]
    apply hpin
    rw [hu2, hspec, hspec]
    have hd : picClass rep j (Additive.toMul ((torsMap fv n y : tors B n) : HDec.WeilPairing.P B)) =
        Scheme.Pic.map (famMap f.hom (ptK K))
          (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B))) :=
      picClass_dual rep j f.hom fv.hom hfv _
    rw [← weilFormula_congr x hd]
    exact (h20d K A n hn hnK f x _ (htors n y) _ _).symm
  · -- `e_n(x, λ_L x) = 1`
    intro L' hL' lam' hlam' n hn hnK x
    rw [he0 n hn hnK]
    have hp : picClass rep j (Additive.toMul ((torsMap lam' n x : tors B n) : HDec.WeilPairing.P B)) =
        phiPt (bcPic A L') (Additive.toMul (x : HDec.WeilPairing.P A)) :=
      picClass_phiL rep L' lam'.hom hlam' _
    rw [← weilFormula_congr x hp]
    exact h23 K A n hn hnK _ x _
  · -- the pin
    intro n hn hnK x y
    rw [he n hn hnK]
    exact hu2 n hn hnK x y

/-! ## §7. `PhiAmpleIsogeny`: surjectivity from `K̄`-points (glue, proved), finiteness (named glue) -/

/-- Every closed point of a scheme locally of finite type over `K` is the image of a `K̄`-point. -/
theorem exists_pt_of_isClosed {B : AbVar K} (b : B.X.left) (hb : IsClosed {b}) :
    ∃ y : B.Pt (AlgebraicClosure K), y.left (IsLocalRing.closedPoint (AlgebraicClosure K)) = b := by
  haveI : IsFinite (B.X.left.fromSpecResidueField b ≫ B.X.hom) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hb
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  let φ := Spec.preimage (B.X.left.fromSpecResidueField b ≫ B.X.hom)
  have hφ : Spec.map φ = B.X.left.fromSpecResidueField b ≫ B.X.hom := Spec.map_preimage _
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  letI : Algebra K (B.X.left.residueField b) := φ.hom.toAlgebra
  haveI : Module.Finite K (B.X.left.residueField b) := hfin
  haveI : Algebra.IsIntegral K (B.X.left.residueField b) := Algebra.IsIntegral.of_finite _ _
  let ψ : B.X.left.residueField b →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom (ψ : B.X.left.residueField b →+* AlgebraicClosure K)) ≫
    B.X.left.fromSpecResidueField b) ?_, ?_⟩
  · change (_ ≫ _) ≫ B.X.hom = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    congr 1
    ext a
    exact ψ.commutes a
  · show (Spec.map _ ≫ B.X.left.fromSpecResidueField b) _ = b
    exact Scheme.fromSpecResidueField_apply b _

/-- **Surjectivity from surjectivity on `K̄`-points** (glue, proved): the image of `lam` is closed (`lam`
is proper) and contains every closed point of the Jacobson scheme `B`. -/
theorem surjective_of_forall_pt {A B : AbVar K} (lam : A.X ⟶ B.X)
    (h : ∀ y : B.Pt (AlgebraicClosure K), ∃ x : A.Pt (AlgebraicClosure K), x ≫ lam = y) :
    Surjective lam.left := by
  haveI : IsProper (lam.left ≫ B.X.hom) := by rw [Over.w lam]; infer_instance
  haveI : IsProper lam.left := IsProper.of_comp lam.left B.X.hom
  have hcl : IsClosed (Set.range lam.left) := lam.left.isClosedMap.isClosed_range
  haveI : JacobsonSpace B.X.left := LocallyOfFiniteType.jacobsonSpace B.X.hom
  have hcp : closedPoints B.X.left ⊆ Set.range lam.left := by
    intro b hb
    obtain ⟨y, rfl⟩ := exists_pt_of_isClosed b hb
    obtain ⟨x, rfl⟩ := h y
    exact ⟨x.left (IsLocalRing.closedPoint _), rfl⟩
  constructor
  intro b
  have : b ∈ closure (closedPoints B.X.left) := by rw [closure_closedPoints]; trivial
  exact (closure_minimal hcp hcl) this

/-- **LEAF (`K(L)` is finite for ample `L`).** For `L` ample on an abelian variety `X` over an algebraically
closed field, `K(L) = {x ∈ X(k) : t_x^*L ≅ L}` is finite. Mumford §6, Application 1 (printed for `L = 𝒪(D)`,
`D` effective; for general ample `L`, `L^m` is effective and `K(L) ⊆ K(L^m)`); UNVERIFIED numbering. Instance
`X = A_K̄`. -/
def MumfordKLFinite : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (c₀ : (AK A).Pic), IsAmple (AK A) c₀ →
    {x : A.Pt (AlgebraicClosure K) | phiPt c₀ x = 1}.Finite

/-- **LEAF? (`K̄`-points of `Pic⁰_{A/K}` are translation-invariant).** For `y ∈ B(K̄)`, `B` the identity
component of `Pic_{A/K}`, the class `M_y` lies in Mumford's `Pic⁰(A_K̄)`. Composite: Kleiman, *The Picard
scheme*, Prop. 9.5.10 (the `K̄`-points of `Pic⁰` are the classes algebraically equivalent to `0`) with Mumford
§8 (classes algebraically equivalent to `0` are translation-invariant); UNVERIFIED numbering. -/
def PicZeroPtsTranslInv : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j → ∀ y : B.Pt (AlgebraicClosure K), IsTranslInv (picClass rep j y)

/-- **Finite kernel on `K̄`-points ⇒ finite** (proved below, `finiteOfFiniteKerPts`). A homomorphism of abelian varieties over `K` whose kernel
has finitely many `K̄`-points is a finite morphism (proper and quasi-finite). -/
def FiniteOfFiniteKerPts : Prop :=
  ∀ (K : Type) [Field K] (A B : AbVar K) (f : Hom A B),
    {x : A.Pt (AlgebraicClosure K) | x ≫ f.hom = 1}.Finite → IsFinite f.hom.left

/-- Over a closed point `b`, there are finitely many `K̄`-points (they are the `K`-embeddings of the finite
extension `κ(b)` into `K̄`). -/
theorem finite_pts_over {B : AbVar K} (b : B.X.left) (hb : IsClosed {b}) :
    {y : B.Pt (AlgebraicClosure K) |
      y.left (IsLocalRing.closedPoint (AlgebraicClosure K)) = b}.Finite := by
  haveI : IsFinite (B.X.left.fromSpecResidueField b ≫ B.X.hom) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hb
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  let φ := Spec.preimage (B.X.left.fromSpecResidueField b ≫ B.X.hom)
  have hφ : Spec.map φ = B.X.left.fromSpecResidueField b ≫ B.X.hom := Spec.map_preimage _
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  letI : Algebra K (B.X.left.residueField b) := φ.hom.toAlgebra
  haveI : Module.Finite K (B.X.left.residueField b) := hfin
  let mk : (B.X.left.residueField b →ₐ[K] AlgebraicClosure K) → (Spec (CommRingCat.of (AlgebraicClosure K)) ⟶
      B.X.left) := fun ψ =>
    Spec.map (CommRingCat.ofHom (ψ : B.X.left.residueField b →+* AlgebraicClosure K)) ≫
      B.X.left.fromSpecResidueField b
  have key : ∀ y : B.Pt (AlgebraicClosure K),
      y.left (IsLocalRing.closedPoint (AlgebraicClosure K)) = b → ∃ ψ, y.left = mk ψ := by
    intro y hy
    have e1 : ∀ (x : B.X.left) (hx : x = b) (ψ : B.X.left.residueField x ⟶
        CommRingCat.of (AlgebraicClosure K)), ∃ ψ' : B.X.left.residueField b ⟶
          CommRingCat.of (AlgebraicClosure K),
        Spec.map ψ ≫ B.X.left.fromSpecResidueField x = Spec.map ψ' ≫ B.X.left.fromSpecResidueField b := by
      intro x hx ψ; subst hx; exact ⟨ψ, rfl⟩
    have hy' : (Scheme.SpecToEquivOfField (AlgebraicClosure K) B.X.left y.left).1 = b := hy
    obtain ⟨ψ', hψ'⟩ := e1 _ hy' (Scheme.SpecToEquivOfField (AlgebraicClosure K) B.X.left y.left).2
    have hyl : y.left = Spec.map ψ' ≫ B.X.left.fromSpecResidueField b := by
      rw [← hψ']
      exact ((Scheme.SpecToEquivOfField (AlgebraicClosure K) B.X.left).symm_apply_apply y.left).symm
    have hw : φ ≫ ψ' = CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ, ← Category.assoc, ← hyl]
      exact Over.w y
    refine ⟨{ toRingHom := ψ'.hom, commutes' := fun a => ?_ }, hyl⟩
    exact congrArg (fun χ => χ.hom a) hw
  apply Set.Finite.of_finite_image (f := fun y : B.Pt (AlgebraicClosure K) => y.left)
  · refine (Set.finite_range mk).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨ψ, h⟩ := key y hy
    exact ⟨ψ, h.symm⟩
  · intro y _ y' _ h
    exact Over.OverMorphism.ext h

/-- A fibre of a homomorphism on `K̄`-points is empty or a translate of the kernel. -/
theorem finite_fiber_pts {A B : AbVar K} (f : Hom A B)
    (hS : {x : A.Pt (AlgebraicClosure K) | x ≫ f.hom = 1}.Finite) (y : B.Pt (AlgebraicClosure K)) :
    {x : A.Pt (AlgebraicClosure K) | x ≫ f.hom = y}.Finite := by
  by_cases h : ∃ x₀, x₀ ≫ f.hom = y
  · obtain ⟨x₀, hx₀⟩ := h
    refine (hS.image (· * x₀)).subset ?_
    intro x hx
    refine ⟨x * x₀⁻¹, ?_, by simp⟩
    change (x * x₀⁻¹) ≫ f.hom = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, hx, hx₀, mul_inv_cancel]
  · convert Set.finite_empty
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hx => h ⟨x, hx⟩

/-- Over a closed point there are finitely many closed points. -/
theorem finite_closed_over {A B : AbVar K} (f : Hom A B)
    (hS : {x : A.Pt (AlgebraicClosure K) | x ≫ f.hom = 1}.Finite) (b : B.X.left) (hb : IsClosed {b}) :
    {a : A.X.left | IsClosed {a} ∧ f.hom.left a = b}.Finite := by
  have hU : {x : A.Pt (AlgebraicClosure K) |
      (x ≫ f.hom).left (IsLocalRing.closedPoint (AlgebraicClosure K)) = b}.Finite := by
    refine ((finite_pts_over b hb).biUnion fun y _ => finite_fiber_pts f hS y).subset ?_
    intro x hx
    exact Set.mem_biUnion (x := x ≫ f.hom) hx rfl
  refine (hU.image fun x => x.left (IsLocalRing.closedPoint (AlgebraicClosure K))).subset ?_
  rintro a ⟨ha, hab⟩
  obtain ⟨x, hx⟩ := exists_pt_of_isClosed (B := A) a ha
  refine ⟨x, ?_, hx⟩
  change f.hom.left (x.left _) = b
  rw [hx, hab]

/-- `f` is quasi-finite at every closed point. -/
theorem quasiFiniteAt_of_isClosed {A B : AbVar K} (f : Hom A B)
    (hS : {x : A.Pt (AlgebraicClosure K) | x ≫ f.hom = 1}.Finite) (a : A.X.left) (ha : IsClosed {a}) :
    f.hom.left.QuasiFiniteAt a := by
  haveI : IsProper (f.hom.left ≫ B.X.hom) := by rw [Over.w f.hom]; infer_instance
  haveI : IsProper f.hom.left := IsProper.of_comp f.hom.left B.X.hom
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have hb : IsClosed {f.hom.left a} := by
    rw [← Set.image_singleton]; exact f.hom.left.isClosedMap _ ha
  have hpre : IsClosed (f.hom.left ⁻¹' {f.hom.left a}) := hb.preimage f.hom.left.continuous
  have hcp : (closedPoints (f.hom.left.fiber (f.hom.left a))).Finite := by
    refine Set.Finite.of_finite_image (f := f.hom.left.fiberι (f.hom.left a)) ?_
      (f.hom.left.fiberι _).isEmbedding.injective.injOn
    refine (finite_closed_over f hS _ hb).subset ?_
    rintro _ ⟨p, hp, rfl⟩
    have e : f.hom.left.fiberι (f.hom.left a) p =
        ((f.hom.left.fiberHomeo (f.hom.left a)) p : A.X.left) := by
      rw [Scheme.Hom.fiberHomeo_apply]
    refine ⟨?_, ?_⟩
    · rw [e]
      have h1 := (f.hom.left.fiberHomeo (f.hom.left a)).isClosedMap _ hp
      rw [Set.image_singleton] at h1
      have h2 := hpre.isClosedMap_subtype_val _ h1
      rwa [Set.image_singleton] at h2
    · rw [e]
      exact ((f.hom.left.fiberHomeo (f.hom.left a)) p).2
  haveI := JacobsonSpace.discreteTopology hcp
  exact isOpen_discrete _

/-- **`FiniteOfFiniteKerPts` is a theorem.** -/
theorem finiteOfFiniteKerPts : FiniteOfFiniteKerPts := by
  intro K _ A B f hS
  haveI : IsProper (f.hom.left ≫ B.X.hom) := by rw [Over.w f.hom]; infer_instance
  haveI : IsProper f.hom.left := IsProper.of_comp f.hom.left B.X.hom
  haveI : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
  haveI : LocallyQuasiFinite f.hom.left := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    by_contra hne
    have hc : (f.hom.left.quasiFiniteLocus : Set A.X.left)ᶜ.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
      exact hne (SetLike.coe_injective (h.trans TopologicalSpace.Opens.coe_top.symm))
    obtain ⟨a, ha, hca⟩ := nonempty_inter_closedPoints hc
      (f.hom.left.quasiFiniteLocus.isOpen.isClosed_compl.isLocallyClosed)
    exact ha (quasiFiniteAt_of_isClosed f hS a hca)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f.hom.left


/-- **`PhiAmpleIsogeny` from the leaves** (glue, proved): the kernel of `λ_L` on `K̄`-points is `K(L_K̄)`
(dictionary), and `λ_L` is onto on `K̄`-points (Mumford §8 Thm 1 and `PicZeroPtsTranslInv`). -/
theorem phiAmpleIsogeny_of_printed (hKL : MumfordKLFinite) (h8 : MumfordPhiSurjective)
    (hamp : AmpleBaseChangeAlgClosure) (hsub : PicZeroPtsTranslInv) :
    PhiAmpleIsogeny := by
  have hfin := finiteOfFiniteKerPts
  intro K _ A P rep B j hj L hL lam hlam
  obtain ⟨lam', hlam'⟩ := exists_hom_comp_eq_phiL rep hj L
  have hjm : Mono j := by
    haveI : IsOpenImmersion j.left := hj.1
    exact (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  have he : lam = lam'.hom := by rw [← cancel_mono j, hlam, hlam']
  subst he
  have hone : picClass rep j 1 = 1 := map_one (picHom rep hj)
  refine ⟨hfin K A B lam' ((hKL K A _ (hamp K A L hL)).subset fun x hx => ?_), ?_⟩
  · change x ≫ lam'.hom = 1 at hx
    change phiPt (bcPic A L) x = 1
    rw [← picClass_phiL rep L lam'.hom hlam x, hx, hone]
  · apply surjective_of_forall_pt
    intro y
    obtain ⟨x, hx⟩ := h8 K A _ (hamp K A L hL) _ (hsub K A P rep B j hj y)
    exact ⟨x, picClass_injective rep hj (by rw [picClass_phiL rep L lam'.hom hlam x, hx])⟩

end PicDict

namespace PicDict.AC

open PkgI3 PkgI3.AbVar

variable {k : Type} [Field k]

/-- `X(k)`: sections of `X → Spec k`. -/
abbrev Kpt (X : AbVar k) : Type := 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X.X

/-- Mumford's translation `t_x : X → X`. -/
def tr {X : AbVar k} (x : Kpt X) : X.X ⟶ X.X :=
  CartesianMonoidalCategory.lift (𝟙 _) (CartesianMonoidalCategory.toUnit _ ≫ x) ≫ μ[X.X]

/-- `n_X`. -/
def mul (X : AbVar k) (n : ℕ) : X.X ⟶ X.X := (𝟙 X.X) ^ n

lemma tr_comp_tr {X : AbVar k} (z x : Kpt X) : tr z ≫ tr x = tr (z * x) := by
  simp only [tr, ← CategoryTheory.Hom.mul_def]
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    CartesianMonoidalCategory.toUnit_unique (_ ≫ CartesianMonoidalCategory.toUnit X.X)
      (CartesianMonoidalCategory.toUnit X.X), mul_assoc, ← MonObj.comp_mul]

lemma tr_comp_mul {X : AbVar k} {n : ℕ} (x : Kpt X) (hx : x ^ n = 1) : tr x ≫ mul X n = mul X n := by
  simp only [tr, mul, ← CategoryTheory.Hom.mul_def]
  rw [MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, mul_one]

/-- Mumford's `Pic⁰(X)`: classes invariant under every `t_x`, `x ∈ X(k)`. -/
def IsTI {X : AbVar k} (c : X.X.left.Pic) : Prop := ∀ x : Kpt X, Scheme.Pic.map (tr x).left c = c

/-- `X̂_n`. -/
def IsDT {X : AbVar k} (n : ℕ) (c : X.X.left.Pic) : Prop := IsTI c ∧ c ^ n = 1

/-- `φ_L(x) = t_x^*L ⊗ L⁻¹`. -/
def phi {X : AbVar k} (c : X.X.left.Pic) (x : Kpt X) : X.X.left.Pic :=
  Scheme.Pic.map (tr x).left c * c⁻¹

/-- The module of a class. -/
abbrev modX {X : AbVar k} (c : X.X.left.Pic) : X.X.left.Modules :=
  (fromSkeleton X.X.left.Modules).obj c.val

/-- Trivializations of `n_X^*M`. -/
abbrev Triv (X : AbVar k) (n : ℕ) (c : X.X.left.Pic) :=
  Scheme.Modules.unit X.X.left ≅ (Scheme.Modules.pullback (mul X n).left).obj (modX c)

/-- **Mumford's formula** `ē_n(x, M) = t_x^*ψ ∘ ψ⁻¹` (§20). -/
def formula {X : AbVar k} {n : ℕ} (x : Kpt X) (hx : x ^ n = 1) (c : X.X.left.Pic) (ψ : Triv X n c) :
    Γ(X.X.left, ⊤) :=
  Transport.wf (tr x).left (mul X n).left (by rw [← Over.comp_left, tr_comp_mul x hx]) (modX c) ψ

/-- Constants `k → Γ(X, 𝒪)`. -/
def const (X : AbVar k) (u : k) : Γ(X.X.left, ⊤) :=
  X.X.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom u)

end PicDict.AC

namespace PicDict

open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing

variable {K : Type} [Field K]

/-- `A_K̄ = A ×_K K̄` over `K̄` (Mathlib's `Over.pullback`; group law transported by the monoidal functor). -/
abbrev bcX (A : AbVar K) : Over (Spec (CommRingCat.of (AlgebraicClosure K))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).obj A.X

instance (A : AbVar K) : GrpObj (bcX A) := Functor.grpObjObj

instance (A : AbVar K) : IsProper (bcX A).hom := by dsimp; infer_instance
instance (A : AbVar K) : Smooth (bcX A).hom := by dsimp; infer_instance
instance (A : AbVar K) : GeometricallyIntegral (bcX A).hom := by dsimp; infer_instance

/-- `A_K̄` as an abelian variety over `K̄`. -/
abbrev AKbar (A : AbVar K) : AbVar (AlgebraicClosure K) := AbVar.mk (bcX A)

example (A : AbVar K) : (AKbar A).X.left = AK A := rfl

/-- `A(K̄) → A_K̄(K̄)`. -/
def pts {A : AbVar K} (x : A.Pt (AlgebraicClosure K)) : AC.Kpt (AKbar A) :=
  Over.homMk (pullback.lift x.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w x))
    (pullback.lift_snd _ _ _)

lemma pts_left_fst {A : AbVar K} (x : A.Pt (AlgebraicClosure K)) :
    (pts x).left ≫ pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) =
      x.left := pullback.lift_fst _ _ _

lemma mu_AKbar (A : AbVar K) : μ[(AKbar A).X] =
    Functor.LaxMonoidal.μ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))
        A.X A.X ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).map μ[A.X] :=
  rfl

lemma tr_pts {A : AbVar K} (x : A.Pt (AlgebraicClosure K)) :
    (AC.tr (pts x)).left = (transl x).left := by
  apply pullback.hom_ext
  · rw [AC.tr, mu_AKbar]
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    have key : (CartesianMonoidalCategory.lift (𝟙 (bcX A))
          (CartesianMonoidalCategory.toUnit (bcX A) ≫ pts x)).left ≫
        (Functor.LaxMonoidal.μ (Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap K (AlgebraicClosure K))))) A.X A.X).left ≫
        pullback.fst (A.X ⊗ A.X).hom (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) =
        (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst A.X (ptK K))
          (CartesianMonoidalCategory.snd A.X (ptK K) ≫ x)).left := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_fst]
        simp
        exact (pullback.lift_fst _ _ _).symm
      · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_snd]
        simp
        exact (congrArg (_ ≫ ·) (pts_left_fst x)).trans (pullback.lift_snd _ _ _).symm
    rw [reassoc_of% key]
    simp [transl]
    exact (pullback.lift_fst _ _ _).symm
  · have h1 := Over.w (AC.tr (pts x))
    have h2 : (transl x).left ≫ pullback.snd A.X.hom (ptK K).hom = pullback.snd A.X.hom (ptK K).hom := by
      have := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd
        (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst A.X (ptK K))
          (CartesianMonoidalCategory.snd A.X (ptK K) ≫ x) ≫ μ[A.X]) (CartesianMonoidalCategory.snd A.X (ptK K)))
      simpa [transl] using this
    exact h1.trans h2.symm

lemma mul_AKbar (A : AbVar K) (n : ℕ) : (AC.mul (AKbar A) n).left = (mulN A n).left := by
  have h1 : AC.mul (AKbar A) n =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).map
        ((𝟙 A.X) ^ n) := by
    rw [AC.mul]
    have := map_pow (Functor.homMonoidHom (Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap K (AlgebraicClosure K)))))) (𝟙 A.X) n
    simp only [Functor.homMonoidHom_apply, CategoryTheory.Functor.map_id] at this
    exact this.symm
  rw [h1, mulN]
  apply pullback.hom_ext
  · simp
    exact (congrArg Over.Hom.left (CartesianMonoidalCategory.whiskerRight_fst ((𝟙 A.X) ^ n) (ptK K))).symm
  · simp
    exact (congrArg Over.Hom.left (CartesianMonoidalCategory.whiskerRight_snd ((𝟙 A.X) ^ n) (ptK K))).symm

lemma pts_mul {A : AbVar K} (x y : A.Pt (AlgebraicClosure K)) : pts (x * y) = pts x * pts y := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [pts_left_fst]
    change _ = (CartesianMonoidalCategory.lift (pts x) (pts y) ≫ μ[bcX A]).left ≫ _
    rw [mu_AKbar]
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    have key : (CartesianMonoidalCategory.lift (pts x) (pts y)).left ≫
        (Functor.LaxMonoidal.μ (Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap K (AlgebraicClosure K))))) A.X A.X).left ≫
        pullback.fst (A.X ⊗ A.X).hom (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) =
        (CartesianMonoidalCategory.lift x y).left := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_fst]
        simp
        exact (pts_left_fst x).trans (pullback.lift_fst _ _ _).symm
      · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_snd]
        simp
        exact (pts_left_fst y).trans (pullback.lift_snd _ _ _).symm
    rw [reassoc_of% key]
    rfl
  · exact (Over.w (pts (x * y))).trans (Over.w (pts x * pts y)).symm

/-- `A_K̄(K̄) → A(K̄)`, inverse of `pts`. -/
def unpts {A : AbVar K} (σ : AC.Kpt (AKbar A)) : A.Pt (AlgebraicClosure K) :=
  Over.homMk (σ.left ≫ pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))
    (by
      change (σ.left ≫ pullback.fst _ _) ≫ A.X.hom = _
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      have := Over.w σ
      simp only [Functor.id_obj, Functor.const_obj_obj] at this
      exact (congrArg (· ≫ _) this).trans (Category.id_comp _))

lemma pts_unpts {A : AbVar K} (σ : AC.Kpt (AKbar A)) : pts (unpts σ) = σ := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact pts_left_fst _
  · exact (Over.w (pts (unpts σ))).trans (Over.w σ).symm

lemma pts_injective {A : AbVar K} : Function.Injective (pts (A := A)) := by
  intro x y h
  apply Over.OverMorphism.ext
  rw [← pts_left_fst x, ← pts_left_fst y, h]

lemma pts_surjective {A : AbVar K} : Function.Surjective (pts (A := A)) :=
  fun σ => ⟨unpts σ, pts_unpts σ⟩

/-- `pts` as a group isomorphism. -/
def ptsHom (A : AbVar K) : A.Pt (AlgebraicClosure K) →* AC.Kpt (AKbar A) :=
  MonoidHom.mk' pts pts_mul

/-! ## Mumford's statements over an algebraically closed field (leaves) -/

/-- **LEAF (theorem of the square).** Mumford, *Abelian varieties*, §6, Cor. 4: for `X` an abelian variety
over an algebraically closed field `k`, `L ∈ Pic(X)` and `x, y ∈ X(k)`, `t_{x+y}^*L ⊗ L ≅ t_x^*L ⊗ t_y^*L`
(UNVERIFIED numbering). -/
def MumfordSquareAC : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : AbVar k) (c : X.X.left.Pic) (x y : AC.Kpt X),
    Scheme.Pic.map (AC.tr (x * y)).left c * c =
      Scheme.Pic.map (AC.tr x).left c * Scheme.Pic.map (AC.tr y).left c

/-- **LEAF (`n_X^*L ≅ Lⁿ` for `L ∈ Pic⁰`).** Mumford §8 (iv) (UNVERIFIED numbering). -/
def MumfordMulNPicZeroAC : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : AbVar k) (c : X.X.left.Pic), AC.IsTI c →
    ∀ n : ℕ, Scheme.Pic.map (AC.mul X n).left c = c ^ n

/-- **LEAF (`φ_L` maps onto `Pic⁰` for `L` ample).** Mumford §8, Thm 1 (UNVERIFIED numbering). -/
def MumfordPhiSurjectiveAC : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : AbVar k) (c₀ : X.X.left.Pic), IsAmple X.X.left c₀ →
    ∀ c : X.X.left.Pic, AC.IsTI c → ∃ x : AC.Kpt X, c = AC.phi c₀ x

/-- **LEAF (`ē_n` well defined, `μ_n`-valued, bilinear).** Mumford §20 (definition of `ē_n` by
`t_x^*ψ ∘ ψ⁻¹` and its bilinearity), for `n` prime to the characteristic (UNVERIFIED numbering). -/
def MumfordWeilPairingAC : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : AbVar k) (n : ℕ), 0 < n → (n : k) ≠ 0 →
    ∀ (x x' : AC.Kpt X) (hx : x ^ n = 1) (hx' : x' ^ n = 1) (c c' : X.X.left.Pic),
      AC.IsDT n c → AC.IsDT n c' →
      (∀ ψ ψ' : AC.Triv X n c, AC.formula x hx c ψ = AC.formula x hx c ψ') ∧
      (∀ ψ : AC.Triv X n c, ∃ u : kˣ, u ^ n = 1 ∧ AC.const X (u : k) = AC.formula x hx c ψ) ∧
      (∀ ψ : AC.Triv X n c, AC.formula (x * x') (by rw [mul_pow, hx, hx', mul_one]) c ψ =
        AC.formula x hx c ψ * AC.formula x' hx' c ψ) ∧
      (∀ (ψ : AC.Triv X n c) (ψ' : AC.Triv X n c') (ψ'' : AC.Triv X n (c * c')),
        AC.formula x hx (c * c') ψ'' = AC.formula x hx c ψ * AC.formula x hx c' ψ')

/-- **LEAF (`ē_n` nondegenerate).** Mumford §20, `n` prime to the characteristic (UNVERIFIED numbering). -/
def MumfordWeilNondegAC : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : AbVar k) (n : ℕ), 0 < n → (n : k) ≠ 0 →
    (∀ (x : AC.Kpt X) (hx : x ^ n = 1),
      (∀ c : X.X.left.Pic, AC.IsDT n c → ∀ ψ : AC.Triv X n c, AC.formula x hx c ψ = 1) → x = 1) ∧
    (∀ c : X.X.left.Pic, AC.IsDT n c →
      (∀ (x : AC.Kpt X) (hx : x ^ n = 1) (ψ : AC.Triv X n c), AC.formula x hx c ψ = 1) → c = 1)

/-- **LEAF (`e^L_n(x, x) = 1`).** Mumford §23 (UNVERIFIED numbering). -/
def MumfordWeilAltAC : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : AbVar k) (n : ℕ), 0 < n → (n : k) ≠ 0 →
    ∀ (c₀ : X.X.left.Pic) (x : AC.Kpt X) (hx : x ^ n = 1) (ψ : AC.Triv X n (AC.phi c₀ x)),
      AC.formula x hx (AC.phi c₀ x) ψ = 1

/-- **LEAF (`K(L)` finite for `L` ample).** Mumford §6, Application 1 (printed for `L = 𝒪(D)`, `D` effective;
UNVERIFIED numbering). -/
def MumfordKLFiniteAC : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : AbVar k) (c₀ : X.X.left.Pic), IsAmple X.X.left c₀ →
    {x : AC.Kpt X | AC.phi c₀ x = 1}.Finite

/-! ## The bridge: each leaf at `A_K̄` from the leaf over `K̄` -/

lemma isTI_iff {A : AbVar K} (c : (AK A).Pic) : AC.IsTI (X := AKbar A) c ↔ IsTranslInv c := by
  constructor
  · intro h x
    have := h (pts x)
    rwa [tr_pts] at this
  · intro h σ
    obtain ⟨x, rfl⟩ := pts_surjective σ
    rw [tr_pts]
    exact h x

lemma phi_pts {A : AbVar K} (c₀ : (AK A).Pic) (x : A.Pt (AlgebraicClosure K)) :
    AC.phi (X := AKbar A) c₀ (pts x) = phiPt c₀ x := by
  show (Scheme.Pic.map (AC.tr (pts x)).left c₀ : (AK A).Pic) * c₀⁻¹ = _
  rw [tr_pts]; rfl

theorem mumfordSquare_of_ac (h : MumfordSquareAC) : MumfordSquare := by
  intro K _ A c x y
  have := h (AlgebraicClosure K) (AKbar A) c (pts x) (pts y)
  rw [← pts_mul, tr_pts, tr_pts, tr_pts] at this
  exact this

theorem mumfordMulNPicZero_of_ac (h : MumfordMulNPicZeroAC) : MumfordMulNPicZero := by
  intro K _ A c hc n
  have := h (AlgebraicClosure K) (AKbar A) c ((isTI_iff c).2 hc) n
  rwa [mul_AKbar] at this

theorem mumfordPhiSurjective_of_ac (h : MumfordPhiSurjectiveAC) : MumfordPhiSurjective := by
  intro K _ A c₀ hc₀ c hc
  obtain ⟨σ, hσ⟩ := h (AlgebraicClosure K) (AKbar A) c₀ hc₀ c ((isTI_iff c).2 hc)
  obtain ⟨x, rfl⟩ := pts_surjective σ
  exact ⟨x, hσ.trans (phi_pts c₀ x)⟩

theorem mumfordKLFinite_of_ac (h : MumfordKLFiniteAC) : MumfordKLFinite := by
  intro K _ A c₀ hc₀
  refine ((h (AlgebraicClosure K) (AKbar A) c₀ hc₀).preimage pts_injective.injOn).subset ?_
  intro x hx
  change AC.phi c₀ (pts x) = 1
  rw [phi_pts]; exact hx

lemma wf_congr2 {X : Scheme.{0}} {t t' m m' : X ⟶ X} (et : t = t') (em : m = m') (h : t ≫ m = m)
    (h' : t' ≫ m' = m') (M : X.Modules) (ψ : Scheme.Modules.unit X ≅ (Scheme.Modules.pullback m).obj M) :
    Transport.wf t' m' h' M (ψ ≪≫ (Scheme.Modules.pullbackCongr em).app M) = Transport.wf t m h M ψ := by
  subst et em
  have : ψ ≪≫ (Scheme.Modules.pullbackCongr (rfl : m = m)).app M = ψ := by
    ext1
    simp [Scheme.Modules.pullbackCongr]
  rw [this]

lemma formula_congr_pt {k : Type} [Field k] {X : AbVar k} {n : ℕ} {x y : AC.Kpt X} (e : x = y)
    (hx : x ^ n = 1) (hy : y ^ n = 1) (c : X.X.left.Pic) (ψ : AC.Triv X n c) :
    AC.formula x hx c ψ = AC.formula y hy c ψ := by
  subst e; rfl

lemma formula_congr_c {k : Type} [Field k] {X : AbVar k} {n : ℕ} (x : AC.Kpt X) (hx : x ^ n = 1)
    {c c' : X.X.left.Pic} (e : c = c') (ψ : AC.Triv X n c) :
    AC.formula x hx c' (e ▸ ψ) = AC.formula x hx c ψ := by
  subst e; rfl

lemma pts_pow {A : AbVar K} (x : A.Pt (AlgebraicClosure K)) (n : ℕ) : pts (x ^ n) = pts x ^ n :=
  map_pow (ptsHom A) x n

lemma pts_tors {A : AbVar K} {n : ℕ} (x : tors A n) : pts (Additive.toMul (x : P A)) ^ n = 1 := by
  rw [← pts_pow, ← toMul_nsmul, nsmul_tors x]
  exact map_one (ptsHom A)

/-- Change of trivialization type along `n_{A_K̄} = n_A`. -/
abbrev trivAC {A : AbVar K} {n : ℕ} {c : (AK A).Pic} (ψ : Triv A n c) : AC.Triv (AKbar A) n c :=
  ψ ≪≫ (Scheme.Modules.pullbackCongr (mul_AKbar A n).symm).app (mod c)

lemma congr_trans_symm {X : Scheme.{0}} {m m' : X ⟶ X} (e : m = m') (M : X.Modules)
    (ψ : Scheme.Modules.unit X ≅ (Scheme.Modules.pullback m').obj M) :
    ψ = (ψ ≪≫ (Scheme.Modules.pullbackCongr e.symm).app M) ≪≫ (Scheme.Modules.pullbackCongr e).app M := by
  subst e
  ext1
  simp [Scheme.Modules.pullbackCongr]

lemma triv_surj {A : AbVar K} {n : ℕ} {c : (AK A).Pic} (ψ' : AC.Triv (AKbar A) n c) :
    ∃ ψ : Triv A n c, ψ' = trivAC ψ := by
  exact ⟨ψ' ≪≫ (Scheme.Modules.pullbackCongr (mul_AKbar A n)).app (mod c),
    congr_trans_symm (mul_AKbar A n).symm (mod c) ψ'⟩

lemma formula_bridge {A : AbVar K} {n : ℕ} (x : tors A n) (c : (AK A).Pic) (ψ : Triv A n c) :
    AC.formula (X := AKbar A) (pts (Additive.toMul (x : P A))) (pts_tors x) c (trivAC ψ) =
      weilFormula x c ψ := by
  rw [weilFormula_eq_wf]
  exact wf_congr2 (tr_pts _).symm (mul_AKbar A n).symm _ _ (mod c) ψ

lemma isDT_iff {A : AbVar K} (n : ℕ) (c : (AK A).Pic) : AC.IsDT (X := AKbar A) n c ↔ IsDualTors n c := by
  show AC.IsTI (X := AKbar A) c ∧ c ^ n = 1 ↔ IsTranslInv c ∧ c ^ n = 1
  rw [isTI_iff]

lemma natCast_ne_zero_bar {n : ℕ} (h : (n : K) ≠ 0) : (n : AlgebraicClosure K) ≠ 0 := by
  rw [← map_natCast (algebraMap K (AlgebraicClosure K))]
  exact (map_ne_zero_iff _ (algebraMap K (AlgebraicClosure K)).injective).2 h

theorem mumfordWeilPairing_of_ac (h : MumfordWeilPairingAC) : MumfordWeilPairing := by
  intro K _ A n hn hnK x x' c c' hc hc'
  have H := h (AlgebraicClosure K) (AKbar A) n hn (natCast_ne_zero_bar hnK) _ _ (pts_tors x) (pts_tors x')
    c c' ((isDT_iff n c).2 hc) ((isDT_iff n c').2 hc')
  refine ⟨fun ψ ψ' => ?_, fun ψ => ?_, fun ψ => ?_, fun ψ ψ' ψ'' => ?_⟩
  · exact (formula_bridge x c ψ).symm.trans ((H.1 _ _).trans (formula_bridge x c ψ'))
  · obtain ⟨u, hu1, hu2⟩ := H.2.1 (trivAC ψ)
    exact ⟨u, hu1, hu2.trans (formula_bridge x c ψ)⟩
  · exact (formula_bridge (x + x') c ψ).symm.trans ((formula_congr_pt (pts_mul _ _) _ _ c _).trans
      ((H.2.2.1 (trivAC ψ)).trans (congrArg₂ (· * ·) (formula_bridge x c ψ) (formula_bridge x' c ψ))))
  · exact (formula_bridge x (c * c') ψ'').symm.trans ((H.2.2.2 (trivAC ψ) (trivAC ψ') (trivAC ψ'')).trans
      (congrArg₂ (· * ·) (formula_bridge x c ψ) (formula_bridge x c' ψ')))

theorem mumfordWeilNondeg_of_ac (h : MumfordWeilNondegAC) : MumfordWeilNondeg := by
  intro K _ A n hn hnK
  have H := h (AlgebraicClosure K) (AKbar A) n hn (natCast_ne_zero_bar hnK)
  refine ⟨fun x hx => ?_, fun c hc hx => ?_⟩
  · have h1 := H.1 (pts (Additive.toMul (x : P A))) (pts_tors x) (fun c hc ψ' => by
      obtain ⟨ψ, rfl⟩ := triv_surj ψ'
      exact (formula_bridge x c ψ).trans (hx c ((isDT_iff n c).1 hc) ψ))
    apply Subtype.ext
    apply Additive.toMul.injective
    apply pts_injective
    rw [h1]
    exact (map_one (ptsHom A)).symm
  · refine H.2 c ((isDT_iff n c).2 hc) (fun σ hσ ψ' => ?_)
    obtain ⟨y, rfl⟩ := pts_surjective σ
    obtain ⟨ψ, rfl⟩ := triv_surj ψ'
    have hy : Additive.ofMul y ∈ tors A n := by
      rw [mem_tors]
      apply Additive.toMul.injective
      apply pts_injective
      rw [toMul_nsmul, toMul_ofMul, pts_pow, hσ, toMul_zero]
      exact (map_one (ptsHom A)).symm
    exact (formula_congr_pt rfl _ _ _ _).trans ((formula_bridge ⟨_, hy⟩ c ψ).trans (hx ⟨_, hy⟩ ψ))

theorem mumfordWeilAlt_of_ac (h : MumfordWeilAltAC) : MumfordWeilAlt := by
  intro K _ A n hn hnK c₀ x ψ
  have key : ∀ (c' : (AKbar A).X.left.Pic) (hc' : c' = AC.phi c₀ (pts (Additive.toMul (x : P A))))
      (ψ' : AC.Triv (AKbar A) n c'), AC.formula (pts (Additive.toMul (x : P A))) (pts_tors x) c' ψ' = 1 := by
    intro c' hc' ψ'
    subst hc'
    exact h (AlgebraicClosure K) (AKbar A) n hn (natCast_ne_zero_bar hnK) c₀ _ (pts_tors x) ψ'
  exact (formula_bridge x _ ψ).symm.trans (key _ (phi_pts c₀ _).symm (trivAC ψ))


/-! ## Main results over the algebraically-closed-field leaves -/

/-- **Main result (`WeilPairingMumford`), leaves over an algebraically closed field.** -/
theorem weilPairingMumford_of_ac (hsq : MumfordSquareAC) (h8iv : MumfordMulNPicZeroAC)
    (h8 : MumfordPhiSurjectiveAC) (hamp : AmpleBaseChangeAlgClosure) (h20a : MumfordWeilPairingAC)
    (h20b : MumfordWeilNondegAC) (h23 : MumfordWeilAltAC) (h3 : PhiAmpleIsogeny) :
    WeilPairingMumford :=
  weilPairingMumford_of_printed (mumfordSquare_of_ac hsq) (mumfordMulNPicZero_of_ac h8iv)
    (mumfordPhiSurjective_of_ac h8) hamp (mumfordWeilPairing_of_ac h20a) (mumfordWeilNondeg_of_ac h20b)
    (mumfordWeilAlt_of_ac h23) h3

/-- **`PhiAmpleIsogeny`, leaves over an algebraically closed field** (one composite leaf). -/
theorem phiAmpleIsogeny_of_ac (hKL : MumfordKLFiniteAC) (h8 : MumfordPhiSurjectiveAC)
    (hamp : AmpleBaseChangeAlgClosure) (hsub : PicZeroPtsTranslInv) : PhiAmpleIsogeny :=
  phiAmpleIsogeny_of_printed (mumfordKLFinite_of_ac hKL) (mumfordPhiSurjective_of_ac h8) hamp hsub

end PicDict

namespace PicDict

open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing

variable {K : Type} [Field K]

/-- **LEAF (`𝒪_T = f_{T*}𝒪_{A_T}` universally).** For an abelian variety `A` over `K` (proper, flat, with
geometrically integral fibre) and every `K`-scheme `T`, the unit `𝒪_T → (A_T → T)_* 𝒪_{A_T}` is an isomorphism.
EGA III 7.8.6 (cohomology and base change in degree 0); Kleiman, *The Picard scheme*, Ex. 9.3.11 (`𝒪_S = f_*𝒪_X`
holds universally for `f` proper flat with geometrically integral fibres); over a field also flat base change
(Stacks 02KH) with `Γ(A, 𝒪) = K`. Locators UNVERIFIED. -/
def PushforwardUnitUniversal : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (T : Over (Spec (CommRingCat.of K))),
    IsIso (pushforwardUnitMap (pullback.snd A.X.hom T.hom))

/-- **LEAF (products of geometrically integral schemes).** If `X` and `Y` are geometrically integral over a field
`K`, so is `X ×_K Y`. EGA IV 4.6.5 / Stacks, *Varieties*, products of geometrically irreducible and geometrically
reduced schemes (locators UNVERIFIED). Instance for two abelian varieties. -/
def GeomIntegralProd : Prop :=
  ∀ (K : Type) [Field K] (A B : AbVar K), GeometricallyIntegral (A.X ⊗ B.X).hom

section Setup

variable (A : AbVar K)

/-- The zero section `Spec K → A`. -/
abbrev zs : Spec (CommRingCat.of K) ⟶ A.X.left := η[A.X].left

lemma zs_comp : zs A ≫ A.X.hom = 𝟙 _ := Over.w η[A.X]

/-- Translation by a `T`-point `a` on `A ×_K T`. -/
def translT {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) : A.X ⊗ T ⟶ A.X ⊗ T :=
  CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst _ _)
      (CartesianMonoidalCategory.snd _ _ ≫ a) ≫ μ[A.X])
    (CartesianMonoidalCategory.snd _ _)

/-- `t_a` on the scheme `A ×_K T`. -/
abbrev trT {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) :
    pullback A.X.hom T.hom ⟶ pullback A.X.hom T.hom := (translT A a).left

/-- The normalized subfunctor (classes trivial along the zero section). -/
abbrev Nrm : Subfunctor (picardPresheaf A.X.hom) := picardFunctorNormalized A.X.hom (zs A) (zs_comp A)

/-- Kleiman 9.2.5, proved in the vendored library: normalized classes ≅ the Picard sheaf. -/
def Θ (hU : PushforwardUnitUniversal) : (Nrm A).toFunctor ≅ (picardFunctor A.X.hom).obj :=
  picardFunctorNormalizedIso A.X.hom (zs A) (zs_comp A) (hU K A)

lemma Θ_hom_app (hU : PushforwardUnitUniversal) (T) (x) :
    (Θ A hU).hom.app T x = (toPicardFunctor A.X.hom).app T x.1 := rfl

/-- The `T`-section of `A_T` along `0`. -/
abbrev zT (T : Over (Spec (CommRingCat.of K))) : T.left ⟶ pullback A.X.hom T.hom :=
  sectionBaseChange A.X.hom (zs A) (zs_comp A) T

/-- `t_a^*c ⊗ (pr^* 0^* t_a^* c)⁻¹ ⊗ c⁻¹`, the renormalized `φ_c(a)`. -/
def dT {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) (c : (pullback A.X.hom T.hom).Pic) :
    (pullback A.X.hom T.hom).Pic :=
  Scheme.Pic.map (trT A a) c *
    (Scheme.Pic.map (pullback.snd A.X.hom T.hom) (Scheme.Pic.map (zT A T)
      (Scheme.Pic.map (trT A a) c)))⁻¹ * c⁻¹

lemma dT_mem {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) (c : (pullback A.X.hom T.hom).Pic)
    (hc : Scheme.Pic.map (zT A T) c = 1) : Scheme.Pic.map (zT A T) (dT A a c) = 1 := by
  have h1 : Scheme.Pic.map (zT A T) (Scheme.Pic.map (pullback.snd A.X.hom T.hom)
      (Scheme.Pic.map (zT A T) (Scheme.Pic.map (trT A a) c))) =
      Scheme.Pic.map (zT A T) (Scheme.Pic.map (trT A a) c) := by
    rw [← Scheme.Pic.map_comp, sectionBaseChange_snd, Scheme.Pic.map_id]
  rw [dT, ← Scheme.Pic.mapHom_apply, map_mul, map_mul, map_inv, map_inv]
  simp only [Scheme.Pic.mapHom_apply]
  rw [h1, hc]
  group

lemma bcm_eq {T T' : Over (Spec (CommRingCat.of K))} (g : T' ⟶ T) :
    JacobianChallenge.baseChangeMap A.X.hom g = (A.X ◁ g).left := by
  apply pullback.hom_ext <;> simp [JacobianChallenge.baseChangeMap]

lemma translT_whisker {T T' : Over (Spec (CommRingCat.of K))} (g : T' ⟶ T) (a : T ⟶ A.X) :
    (A.X ◁ g) ≫ translT A a = translT A (g ≫ a) ≫ (A.X ◁ g) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT, CartesianMonoidalCategory.comp_lift_assoc]
  · simp [translT]

lemma dT_natural {T T' : Over (Spec (CommRingCat.of K))} (g : T' ⟶ T) (a : T ⟶ A.X)
    (c : (pullback A.X.hom T.hom).Pic) :
    Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom g) (dT A a c) =
      dT A (g ≫ a) (Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom g) c) := by
  have n1 : JacobianChallenge.baseChangeMap A.X.hom g ≫ trT A a =
      trT A (g ≫ a) ≫ JacobianChallenge.baseChangeMap A.X.hom g := by
    rw [bcm_eq, ← Over.comp_left, ← Over.comp_left, translT_whisker]
  have n2 : JacobianChallenge.baseChangeMap A.X.hom g ≫ pullback.snd A.X.hom T.hom =
      pullback.snd A.X.hom T'.hom ≫ g.left := pullback.lift_snd _ _ _
  have n3 : zT A T' ≫ JacobianChallenge.baseChangeMap A.X.hom g = g.left ≫ zT A T :=
    sectionBaseChange_comp_baseChangeMap _ _ _ g
  rw [dT, dT, ← Scheme.Pic.mapHom_apply, map_mul, map_mul, map_inv, map_inv]
  simp only [Scheme.Pic.mapHom_apply]
  rw [← Scheme.Pic.map_comp, n1, Scheme.Pic.map_comp, ← Scheme.Pic.map_comp _ (pullback.snd _ _), n2,
    Scheme.Pic.map_comp, ← Scheme.Pic.map_comp g.left, ← n3, Scheme.Pic.map_comp,
    ← Scheme.Pic.map_comp _ (trT A a), n1, Scheme.Pic.map_comp]

end Setup

section Psi

variable {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
  (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (hU : PushforwardUnitUniversal)

/-- The morphism classifying the renormalized `φ_c(a)`. -/
def PsiT {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) (c : (Nrm A).toFunctor.obj (op T)) :
    T ⟶ P :=
  rep.homEquiv.symm ((Θ A hU).hom.app (op T) ⟨dT A a c.1, dT_mem A a c.1 c.2⟩)

lemma PsiT_natural {T T' : Over (Spec (CommRingCat.of K))} (g : T' ⟶ T) (a : T ⟶ A.X)
    (c : (Nrm A).toFunctor.obj (op T)) :
    g ≫ PsiT rep hU a c = PsiT rep hU (g ≫ a) ((Nrm A).toFunctor.map g.op c) := by
  rw [PsiT, PsiT, rep.comp_homEquiv_symm]
  congr 1
  rw [← NatTrans.naturality_apply]
  congr 1
  apply Subtype.ext
  exact dT_natural A g a c.1

/-- `η ≫ (classifying map of 1)`: the class `1` classifies the unit. -/
lemma homEquiv_symm_one {T : Over (Spec (CommRingCat.of K))} :
    letI := picardFunctorCommGrpObj A.X.hom rep
    rep.homEquiv.symm ((toPicardFunctor A.X.hom).app (op T) (1 : (pullback A.X.hom T.hom).Pic)) =
      CartesianMonoidalCategory.toUnit T ≫ η[P] := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  have h := (picardClassifyingHom A.X.hom rep T).map_one
  rw [picardClassifyingHom_apply] at h
  exact h

lemma dT_one {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) : dT A a 1 = 1 := by
  simp [dT, Scheme.Pic.map_one]

lemma translT_zero {T : Over (Spec (CommRingCat.of K))} :
    translT A (CartesianMonoidalCategory.toUnit T ≫ η[A.X]) = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [translT, CartesianMonoidalCategory.lift_fst, Category.id_comp]
    rw [← Category.assoc, CartesianMonoidalCategory.toUnit_unique (CartesianMonoidalCategory.snd A.X T ≫
        CartesianMonoidalCategory.toUnit T) (CartesianMonoidalCategory.toUnit _),
      ← CategoryTheory.Hom.one_def, ← CategoryTheory.Hom.mul_def, mul_one]
  · simp [translT]

lemma Θ_inj {T : Over (Spec (CommRingCat.of K))} {x y : (Nrm A).toFunctor.obj (op T)}
    (h : (Θ A hU).hom.app (op T) x = (Θ A hU).hom.app (op T) y) : x = y := by
  have := congrArg ((Θ A hU).inv.app (op T)) h
  simpa using this

/-- `PsiT a c = 1` when `dT a c = 1`. -/
lemma PsiT_eq_one {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) (c : (Nrm A).toFunctor.obj (op T))
    (h : dT A a c.1 = 1) :
    letI := picardFunctorCommGrpObj A.X.hom rep
    PsiT rep hU a c = CartesianMonoidalCategory.toUnit T ≫ η[P] := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  rw [PsiT, ← homEquiv_symm_one rep]
  congr 1
  rw [Θ_hom_app]
  exact congrArg _ h

/-- Conversely, `PsiT a c = 1` forces `dT a c = 1`. -/
lemma dT_eq_one_of_PsiT {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X)
    (c : (Nrm A).toFunctor.obj (op T))
    (h : letI := picardFunctorCommGrpObj A.X.hom rep
      PsiT rep hU a c = CartesianMonoidalCategory.toUnit T ≫ η[P]) : dT A a c.1 = 1 := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  rw [PsiT, ← homEquiv_symm_one rep] at h
  have h2 := rep.homEquiv.symm.injective h
  have h3 : (1 : (pullback A.X.hom T.hom).Pic) ∈ (Nrm A).obj (op T) := by
    change Scheme.Pic.map _ 1 = 1; exact Scheme.Pic.map_one _
  have h4 := Θ_inj hU (x := ⟨dT A a c.1, dT_mem A a c.1 c.2⟩) (y := ⟨(1 : (pullback A.X.hom T.hom).Pic), h3⟩) (by rw [h2]; rfl)
  exact congrArg Subtype.val h4

end Psi

lemma dT_zero {A : AbVar K} {T : Over (Spec (CommRingCat.of K))} (c : (pullback A.X.hom T.hom).Pic)
    (hc : Scheme.Pic.map (zT A T) c = 1) : dT A (CartesianMonoidalCategory.toUnit T ≫ η[A.X]) c = 1 := by
  have e : trT A (CartesianMonoidalCategory.toUnit T ≫ η[A.X]) = 𝟙 _ := by
    rw [trT, translT_zero]; rfl
  rw [dT, e, Scheme.Pic.map_id, hc, Scheme.Pic.map_one, inv_one, mul_one, mul_inv_cancel]

lemma lift_mul_lift {G H T : Over (Spec (CommRingCat.of K))} [GrpObj G] [GrpObj H] (f f' : T ⟶ G)
    (g g' : T ⟶ H) :
    CartesianMonoidalCategory.lift f g * CartesianMonoidalCategory.lift f' g' =
      CartesianMonoidalCategory.lift (f * f') (g * g') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.mul_comp]; simp
  · rw [MonObj.mul_comp]; simp

/-- **`PicZeroPtsTranslInv` from two printed leaves** (rigidity on `A × Pic⁰`). -/
theorem picZeroPtsTranslInv_of_leaves (hU : PushforwardUnitUniversal) (hGI : GeomIntegralProd) :
    PicZeroPtsTranslInv := by
  intro K _ A P rep B j hj y x
  letI := picardFunctorCommGrpObj A.X.hom rep
  obtain ⟨hopen, hrange, hmon⟩ := hj
  haveI : IsOpenImmersion j.left := hopen
  haveI : IsMonHom j := hmon
  haveI : GeometricallyIntegral (A.X ⊗ B.X).hom := hGI K A B
  haveI : IsProper (A.X ⊗ B.X).hom := by dsimp; infer_instance
  let c₀ : (Nrm A).toFunctor.obj (op (A.X ⊗ B.X)) :=
    (Θ A hU).inv.app (op (A.X ⊗ B.X)) (rep.homEquiv (CartesianMonoidalCategory.snd A.X B.X ≫ j))
  let Ψ := PsiT rep hU (CartesianMonoidalCategory.fst A.X B.X) c₀
  -- the class of `g ≫ snd ≫ j` along any `g`
  have hΘc : ∀ {T : Over (Spec (CommRingCat.of K))} (g : T ⟶ A.X ⊗ B.X),
      (Θ A hU).hom.app (op T) ((Nrm A).toFunctor.map g.op c₀) =
        rep.homEquiv (g ≫ CartesianMonoidalCategory.snd A.X B.X ≫ j) := by
    intro T g
    rw [NatTrans.naturality_apply, Iso.inv_hom_id_app_apply]
    exact (rep.homEquiv_comp g _).symm
  have hjη : η[B.X] ≫ j = η[P] := IsMonHom.one_hom j
  -- axis `A × {0}`
  have haxA : CartesianMonoidalCategory.lift (𝟙 A.X) (CartesianMonoidalCategory.toUnit A.X ≫ η[B.X]) ≫ Ψ =
      CartesianMonoidalCategory.toUnit A.X ≫ η[P] := by
    rw [PsiT_natural]
    apply PsiT_eq_one
    have h1 : ((Nrm A).toFunctor.map (CartesianMonoidalCategory.lift (𝟙 A.X)
        (CartesianMonoidalCategory.toUnit A.X ≫ η[B.X])).op c₀).1 =
        (1 : (pullback A.X.hom A.X.hom).Pic) := by
      have h3 : Scheme.Pic.map (zT A A.X) (1 : (pullback A.X.hom A.X.hom).Pic) = 1 :=
        Scheme.Pic.map_one _
      have := Θ_inj hU (x := (Nrm A).toFunctor.map (CartesianMonoidalCategory.lift (𝟙 A.X)
        (CartesianMonoidalCategory.toUnit A.X ≫ η[B.X])).op c₀)
        (y := ⟨(1 : (pullback A.X.hom A.X.hom).Pic), h3⟩) (by
          rw [hΘc, Θ_hom_app]
          simp only [CartesianMonoidalCategory.lift_snd_assoc, Category.assoc, hjη]
          rw [← homEquiv_symm_one rep, Equiv.apply_symm_apply])
      exact congrArg Subtype.val this
    rw [h1]; exact dT_one _
  -- axis `{0} × B`
  have haxB : CartesianMonoidalCategory.lift (CartesianMonoidalCategory.toUnit B.X ≫ η[A.X]) (𝟙 B.X) ≫ Ψ =
      CartesianMonoidalCategory.toUnit B.X ≫ η[P] := by
    rw [PsiT_natural]
    apply PsiT_eq_one
    set c := (Nrm A).toFunctor.map (CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.toUnit B.X ≫ η[A.X]) (𝟙 B.X)).op c₀
    have hc : Scheme.Pic.map (zT A B.X) c.1 = 1 := c.2
    rw [CartesianMonoidalCategory.lift_fst]
    exact dT_zero c.1 hc
  -- `Ψ(0) = 0`
  have hηAB : η[A.X ⊗ B.X] = η[A.X] ≫ CartesianMonoidalCategory.lift (𝟙 A.X)
      (CartesianMonoidalCategory.toUnit A.X ≫ η[B.X]) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [IsMonHom.one_hom (CartesianMonoidalCategory.fst A.X B.X)]; simp
    · rw [IsMonHom.one_hom (CartesianMonoidalCategory.snd A.X B.X)]
      simp only [Category.assoc, CartesianMonoidalCategory.lift_snd]
      rw [← Category.assoc, CartesianMonoidalCategory.toUnit_unique (η[A.X] ≫ _) (𝟙 _),
        Category.id_comp]
  have hη : η[A.X ⊗ B.X] ≫ Ψ = η[P] := by
    rw [hηAB, Category.assoc, haxA, ← Category.assoc,
      CartesianMonoidalCategory.toUnit_unique (η[A.X] ≫ _) (𝟙 _), Category.id_comp]
  -- `Ψ` factors through `Pic⁰ = B`
  haveI : IsIntegral (A.X ⊗ B.X).left := GeometricallyIntegral.isIntegral_of_subsingleton (A.X ⊗ B.X).hom
  have hsub : Set.range Ψ.left ⊆ Set.range j.left := by
    rw [hrange]
    rintro _ ⟨a, rfl⟩
    refine ⟨(A.X ⊗ B.X).hom a, ?_⟩
    have he : η[P].left ((A.X ⊗ B.X).hom a) = Ψ.left (η[A.X ⊗ B.X].left ((A.X ⊗ B.X).hom a)) := by
      rw [← hη]; rfl
    rw [he]
    exact (isPreconnected_range Ψ.left.continuous).subset_connectedComponent ⟨_, rfl⟩ ⟨a, rfl⟩
  let l : (A.X ⊗ B.X).left ⟶ B.X.left := IsOpenImmersion.lift j.left Ψ.left hsub
  have hl : l ≫ j.left = Ψ.left := IsOpenImmersion.lift_fac _ _ _
  have hw : l ≫ B.X.hom = (A.X ⊗ B.X).hom := by
    rw [← Over.w j, ← Category.assoc, hl, Over.w]
  let Ψ' : A.X ⊗ B.X ⟶ B.X := Over.homMk l hw
  have hΨ' : Ψ' ≫ j = Ψ := Over.OverMorphism.ext hl
  have hjm : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  have hη' : η[A.X ⊗ B.X] ≫ Ψ' = η[B.X] := by
    rw [← cancel_mono j, Category.assoc, hΨ', hη, hjη]
  haveI : IsMonHom Ψ' := MulRigidity.isMonHom_of_geometricallyIntegral (A.X ⊗ B.X) B.X Ψ' hη'
  have hA' : CartesianMonoidalCategory.lift (𝟙 A.X) (CartesianMonoidalCategory.toUnit A.X ≫ η[B.X]) ≫ Ψ' =
      CartesianMonoidalCategory.toUnit A.X ≫ η[B.X] := by
    rw [← cancel_mono j, Category.assoc, hΨ', haxA, Category.assoc, hjη]
  have hB' : CartesianMonoidalCategory.lift (CartesianMonoidalCategory.toUnit B.X ≫ η[A.X]) (𝟙 B.X) ≫ Ψ' =
      CartesianMonoidalCategory.toUnit B.X ≫ η[B.X] := by
    rw [← cancel_mono j, Category.assoc, hΨ', haxB, Category.assoc, hjη]
  -- at `K̄`-points
  have hpt : CartesianMonoidalCategory.lift x y ≫ Ψ = CartesianMonoidalCategory.toUnit _ ≫ η[P] := by
    have hxy : CartesianMonoidalCategory.lift x y =
        (x ≫ CartesianMonoidalCategory.lift (𝟙 A.X) (CartesianMonoidalCategory.toUnit A.X ≫ η[B.X])) *
        (y ≫ CartesianMonoidalCategory.lift (CartesianMonoidalCategory.toUnit B.X ≫ η[A.X]) (𝟙 B.X)) := by
      simp only [CartesianMonoidalCategory.comp_lift, Category.comp_id, lift_mul_lift]
      congr 1
      · rw [← Category.assoc, CartesianMonoidalCategory.toUnit_unique (y ≫ _) (CartesianMonoidalCategory.toUnit _),
          ← CategoryTheory.Hom.one_def, mul_one]
      · rw [← Category.assoc, CartesianMonoidalCategory.toUnit_unique (x ≫ _) (CartesianMonoidalCategory.toUnit _),
          ← CategoryTheory.Hom.one_def, one_mul]
    rw [← hΨ', ← Category.assoc, hxy, MonObj.mul_comp, Category.assoc, Category.assoc, hA', hB',
      ← Category.assoc, ← Category.assoc,
      CartesianMonoidalCategory.toUnit_unique (x ≫ _) (CartesianMonoidalCategory.toUnit _),
      CartesianMonoidalCategory.toUnit_unique (y ≫ _) (CartesianMonoidalCategory.toUnit _),
      ← CategoryTheory.Hom.one_def, mul_one, MonObj.one_comp, CategoryTheory.Hom.one_def]
  rw [PsiT_natural, CartesianMonoidalCategory.lift_fst] at hpt
  have hd := dT_eq_one_of_PsiT rep hU x _ hpt
  have hcy : ((Nrm A).toFunctor.map (CartesianMonoidalCategory.lift x y).op c₀).1 = picClass rep j y := by
    have h0 := (Θ_hom_app A hU _ ((Nrm A).toFunctor.map (CartesianMonoidalCategory.lift x y).op c₀)).symm.trans
      ((hΘc (CartesianMonoidalCategory.lift x y)).trans
        (by rw [CartesianMonoidalCategory.lift_snd_assoc]))
    exact ((picClass_eq_iff rep j y _).2 h0).symm
  rw [hcy] at hd
  have hS : Scheme.Pic.map (zT A (ptK K)) (Scheme.Pic.map (trT A x) (picClass rep j y)) = 1 :=
    Subsingleton.elim (α := (Spec (CommRingCat.of (AlgebraicClosure K))).Pic) _ _
  rw [dT, hS, Scheme.Pic.map_one, inv_one, mul_one, mul_inv_eq_one] at hd
  exact hd


/-- **`PhiAmpleIsogeny` from printed leaves only** (Mumford §6 App. 1, §8 Thm 1 over `k̄`; EGA II 4.6.13;
`𝒪_T = f_{T*}𝒪` universally; products of geometrically integral schemes). -/
theorem phiAmpleIsogeny_of_leaves (hKL : MumfordKLFiniteAC) (h8 : MumfordPhiSurjectiveAC)
    (hamp : AmpleBaseChangeAlgClosure) (hU : PushforwardUnitUniversal) (hGI : GeomIntegralProd) :
    PhiAmpleIsogeny :=
  phiAmpleIsogeny_of_ac hKL h8 hamp (picZeroPtsTranslInv_of_leaves hU hGI)

end PicDict

namespace PicDict

open T09Pic PkgI3 PkgI3.AbVar


/-- Pull-back of a tensor power. -/
def pullbackTensorPowIso {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules) :
    ∀ n : ℕ, (Scheme.Modules.pullback f).obj (M.tensorPow n) ≅
      ((Scheme.Modules.pullback f).obj M).tensorPow n
  | 0 => (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).symm
  | n + 1 => Scheme.Modules.pullbackTensorObjIso f M (M.tensorPow n) ≪≫
      (Iso.refl _ ⊗ᵢ pullbackTensorPowIso f M n)

/-- Tensor powers of an isomorphism. -/
def tensorPowIso {X : Scheme.{0}} {M N : X.Modules} (e : M ≅ N) : ∀ n : ℕ, M.tensorPow n ≅ N.tensorPow n
  | 0 => Iso.refl _
  | n + 1 => e ⊗ᵢ tensorPowIso e n

/-- **Ampleness pulls back along an affine morphism** (for the EGA/Stacks notion `IsAmple`). -/
theorem isAmple_pullback {X Y : Scheme.{0}} (f : X ⟶ Y) [IsAffineHom f] [CompactSpace X]
    (L : Y.Pic) (hL : IsAmple Y L) : IsAmple X (Scheme.Pic.map f L) := by
  refine ⟨inferInstance, fun x => ?_⟩
  obtain ⟨n, hn, s, hx, haff⟩ := hL.2 (f x)
  let M := (fromSkeleton Y.Modules).obj L.val
  let e1 : (fromSkeleton X.Modules).obj (Scheme.Pic.map f L).val ≅ (Scheme.Modules.pullback f).obj M :=
    Scheme.Pic.mkIso _
  let eT : (Scheme.Modules.pullback f).obj (M.tensorPow n) ≅
      ((fromSkeleton X.Modules).obj (Scheme.Pic.map f L).val).tensorPow n :=
    pullbackTensorPowIso f M n ≪≫ tensorPowIso e1.symm n
  let s' : 𝟙_ X.Modules ⟶ ((fromSkeleton X.Modules).obj (Scheme.Pic.map f L).val).tensorPow n :=
    (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).hom ≫ (Scheme.Modules.pullback f).map s ≫ eT.hom
  have hz : Scheme.Modules.Hom.zeroLocus s' = Scheme.Modules.Hom.zeroLocus ((Scheme.Modules.pullback f).map s) :=
    Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso _ _
      (Arrow.isoMk (Functor.Monoidal.εIso (Scheme.Modules.pullback f)) eT.symm (by simp only [s', Arrow.mk_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]))
  have hU : (Scheme.Modules.Hom.zeroLocus s').support.compl = f ⁻¹ᵁ (Scheme.Modules.Hom.zeroLocus s).support.compl := by
    rw [hz, ← Scheme.Modules.Hom.comap_zeroLocus]
    ext y
    simp only [TopologicalSpace.Closeds.compl, TopologicalSpace.Opens.map_coe]
    have h := Scheme.IdealSheafData.coe_support_comap (Scheme.Modules.Hom.zeroLocus s) f
    change y ∈ (((Scheme.Modules.Hom.zeroLocus s).comap f).support : Set X)ᶜ ↔
      f y ∈ ((Scheme.Modules.Hom.zeroLocus s).support : Set Y)ᶜ
    rw [h]
    rfl
  refine ⟨n, hn, s', ?_, ?_⟩
  · rw [hU]; exact hx
  · rw [hU]; exact haff.preimage f

end PicDict

namespace PicDict

open T09Pic PkgI3 PkgI3.AbVar

/-- **`AmpleBaseChangeAlgClosure` is a theorem.** -/
theorem ampleBaseChangeAlgClosure : AmpleBaseChangeAlgClosure := by
  intro K _ A L hL
  haveI : CompactSpace (ptK K).left :=
    inferInstanceAs (CompactSpace (Spec (CommRingCat.of (AlgebraicClosure K))))
  haveI : IsAffineHom (ptK K).hom :=
    inferInstanceAs (IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))
  haveI : IsAffineHom (pullback.fst A.X.hom (ptK K).hom) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
  haveI : CompactSpace (AK A) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd A.X.hom (ptK K).hom)
  exact isAmple_pullback (pullback.fst A.X.hom (ptK K).hom) L hL


/-! ## Final results: printed leaves only -/

/-- **`WeilPairingMumford` from Mumford's statements over an algebraically closed field** (§6 Cor. 4, §8 (iv),
§8 Thm 1, §20 twice, §23) and the row `PhiAmpleIsogeny`. -/
theorem weilPairingMumford_of_mumford (hsq : MumfordSquareAC) (h8iv : MumfordMulNPicZeroAC)
    (h8 : MumfordPhiSurjectiveAC) (h20a : MumfordWeilPairingAC) (h20b : MumfordWeilNondegAC)
    (h23 : MumfordWeilAltAC) (h3 : PhiAmpleIsogeny) : WeilPairingMumford :=
  weilPairingMumford_of_ac hsq h8iv h8 ampleBaseChangeAlgClosure h20a h20b h23 h3

/-- **`PhiAmpleIsogeny` from printed leaves** (Mumford §6 App. 1 and §8 Thm 1 over `k̄`; `𝒪 = f_*𝒪` universally;
products of geometrically integral schemes). -/
theorem phiAmpleIsogeny_of_mumford (hKL : MumfordKLFiniteAC) (h8 : MumfordPhiSurjectiveAC)
    (hU : PushforwardUnitUniversal) (hGI : GeomIntegralProd) : PhiAmpleIsogeny :=
  phiAmpleIsogeny_of_leaves hKL h8 ampleBaseChangeAlgClosure hU hGI

end PicDict

/-! ## `PicZeroAbVar` from four statements -/

namespace PicDict

open T09Pic PkgI3 PkgI3.AbVar

/-- A scheme smooth over a field is reduced. -/
theorem isReduced_of_smooth_field {X : Scheme.{0}} {L : Type} [Field L]
    (f : X ⟶ Spec (CommRingCat.of L)) [Smooth f] : IsReduced X := by
  haveI : ∀ i, IsReduced (X.affineCover.X i) := fun i => by
    let g := X.affineCover.f i ≫ f
    haveI : Smooth g := inferInstance
    have hs := g.smooth_appLE (isAffineOpen_top (Spec (CommRingCat.of L)))
      (isAffineOpen_top (X.affineCover.X i)) le_top
    let φ : L →+* Γ(X.affineCover.X i, ⊤) :=
      (g.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom
    have hφ : φ.Smooth := by
      refine RingHom.Smooth.comp ?_ hs
      exact RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
    letI := φ.toAlgebra
    haveI : Algebra.Smooth L Γ(X.affineCover.X i, ⊤) := hφ
    haveI : _root_.IsReduced Γ(X.affineCover.X i, ⊤) :=
      ZInQ.SmoothFibre.isReduced_of_smooth_of_field L _
    exact isReduced_of_isAffine_isReduced _
  exact IsReduced.of_openCover (X := X) X.affineCover

/-- Smooth morphisms are geometrically reduced. -/
theorem geometricallyReduced_of_smooth {X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] :
    GeometricallyReduced f := by
  rw [GeometricallyReduced.eq_geometrically]
  intro K _ y Z fst snd h
  haveI : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h inferInstance
  exact isReduced_of_smooth_field snd

/-! ## Leaves -/

/-- **LEAF (Z1, the Picard scheme is locally of finite type).** For an abelian variety `A` over a field `K`, a
scheme representing `Pic_{A/K}` is locally of finite type over `K`. Kleiman, *The Picard scheme*, Thm 9.4.8
(`Pic_{X/S}` exists, separated and locally of finite presentation, for `X/S` projective flat with geometrically
integral fibres); representing objects are unique up to isomorphism. Locator UNVERIFIED. -/
def PicLocFinType : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (_ : (picardFunctor A.X.hom).obj.RepresentableBy P), LocallyOfFiniteType P.hom

/-- **LEAF (Z2, the identity component of a group scheme locally of finite type over a field).** It is open, a
subgroup, and geometrically irreducible. SGA 3, VI_A 2.4; Stacks, Tag 0B7R; Kleiman 9.5.1 (locators
UNVERIFIED). -/
def IdentityComponentLFT : Prop :=
  ∀ (K : Type) [Field K] (G : Over (Spec (CommRingCat.of K))) [GrpObj G], LocallyOfFiniteType G.hom →
    ∃ V : G.left.Opens, (V : Set G.left) = identityComponent G ∧
      (∀ z : (G ⊗ G).left, (CartesianMonoidalCategory.fst G G).left z ∈ V →
        (CartesianMonoidalCategory.snd G G).left z ∈ V → μ[G].left z ∈ V) ∧
      (∀ g : G.left, g ∈ V → ((𝟙 G)⁻¹ : G ⟶ G).left g ∈ V) ∧
      GeometricallyIrreducible (V.ι ≫ G.hom)

/-- **LEAF? (Z3a, `Pic⁰_{A/K}` is smooth).** The identity component of the Picard scheme of an abelian variety is
smooth over `K`. Mumford §13 (over `k̄`: `Â = Pic⁰`, `dim Â = h¹(𝒪) = g`); over `K`: Kleiman 9.5.1 and descent;
BLR 8.4 / Milne 1986 §10 may print it in one statement (pending reading; locators UNVERIFIED). -/
def PicZeroSmooth : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (V : P.left.Opens),
    letI := picardFunctorCommGrpObj A.X.hom rep
    (V : Set P.left) = identityComponent P → Smooth (V.ι ≫ P.hom)

/-- **LEAF (Z3b, `Pic⁰_{X/K}` is proper).** For `X` proper and geometrically normal over `K`, the identity
component of `Pic_{X/K}` is proper. Kleiman, *The Picard scheme*, Thm 9.5.4 (locator UNVERIFIED). Instance for
an abelian variety. -/
def PicZeroProper : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (V : P.left.Opens),
    letI := picardFunctorCommGrpObj A.X.hom rep
    (V : Set P.left) = identityComponent P → IsProper (V.ι ≫ P.hom)

/-! ## Glue -/

section OpenSub

variable {K : Type} [Field K] {P : Over (Spec (CommRingCat.of K))} (V : P.left.Opens)

/-- The open subscheme on `V` as a `K`-scheme. -/
abbrev subX : Over (Spec (CommRingCat.of K)) := Over.mk (V.ι ≫ P.hom)

/-- Its inclusion. -/
abbrev subι : subX V ⟶ P := Over.homMk V.ι rfl

instance : Mono (subι V) := by
  constructor
  intro T g h e
  apply Over.OverMorphism.ext
  exact (cancel_mono V.ι).1 (congrArg Over.Hom.left e)

/-- Lift through the open subscheme. -/
lemma range_sub {T : Over (Spec (CommRingCat.of K))} (f : T ⟶ P) (h : ∀ t, f.left t ∈ V) :
    Set.range f.left ⊆ Set.range V.ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨t, rfl⟩
  exact h t

def liftV {T : Over (Spec (CommRingCat.of K))} (f : T ⟶ P) (h : ∀ t, f.left t ∈ V) : T ⟶ subX V :=
  Over.homMk (IsOpenImmersion.lift V.ι f.left (range_sub V f h))
    (by
      change IsOpenImmersion.lift V.ι f.left _ ≫ V.ι ≫ P.hom = T.hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.w])

lemma liftV_comp {T : Over (Spec (CommRingCat.of K))} (f : T ⟶ P) (h : ∀ t, f.left t ∈ V) :
    liftV V f h ≫ subι V = f :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

end OpenSub

/-- **`PicZeroAbVar` from four statements**: the Picard scheme is locally of finite type (Kleiman 9.4.8), the
identity component of a group scheme locally of finite type is an open geometrically irreducible subgroup (SGA 3
VI_A 2.4), and `Pic⁰` is smooth and proper. -/
theorem picZeroAbVar_of_leaves (h1 : PicLocFinType) (h2 : IdentityComponentLFT) (h3a : PicZeroSmooth)
    (h3b : PicZeroProper) : PicZeroAbVar := by
  intro K _ A P rep
  letI := picardFunctorCommGrpObj A.X.hom rep
  obtain ⟨V, hV, hmulV, hinvV, hirr⟩ := h2 K P (h1 K A P rep)
  let j := subι V
  have hmem : ∀ x : P.left, x ∈ identityComponent P → x ∈ V := fun x hx => by
    rw [← SetLike.mem_coe, hV]; exact hx
  have hιV : ∀ y, V.ι y ∈ V := fun y => by
    rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι V]; exact ⟨y, rfl⟩
  -- multiplication
  let pj : subX V ⊗ subX V ⟶ P ⊗ P := CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.fst (subX V) (subX V) ≫ j) (CartesianMonoidalCategory.snd (subX V) (subX V) ≫ j)
  have hm : ∀ t, (pj ≫ μ[P]).left t ∈ V := fun t => by
    rw [Over.comp_left]
    apply hmulV
    · change (pj ≫ CartesianMonoidalCategory.fst P P).left t ∈ V
      rw [CartesianMonoidalCategory.lift_fst, Over.comp_left, Scheme.Hom.comp_apply]
      exact hιV _
    · change (pj ≫ CartesianMonoidalCategory.snd P P).left t ∈ V
      rw [CartesianMonoidalCategory.lift_snd, Over.comp_left, Scheme.Hom.comp_apply]
      exact hιV _
  let mulY := liftV V (pj ≫ μ[P]) hm
  have hmul : mulY ≫ j = CartesianMonoidalCategory.fst (subX V) (subX V) ≫ j *
      CartesianMonoidalCategory.snd (subX V) (subX V) ≫ j := by
    rw [liftV_comp, CategoryTheory.Hom.mul_def]
  -- unit
  have ho : ∀ t, (η[P]).left t ∈ V := fun t => hmem _ ⟨t, mem_connectedComponent⟩
  let oneY := liftV V η[P] ho
  have hone : oneY ≫ j = η[P] := liftV_comp V _ _
  -- inverse
  have hi : ∀ t, (j ≫ (𝟙 P)⁻¹).left t ∈ V := fun t => by
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hinvV _ (hιV t)
  let invY := liftV V (j ≫ (𝟙 P)⁻¹) hi
  have hinv : invY ≫ j = j⁻¹ := by
    rw [liftV_comp, GrpObj.comp_inv, Category.comp_id]
  letI : GrpObj (subX V) := AVGlue.grpObjOfMono j mulY hmul oneY hone invY hinv
  have hjmon : IsMonHom j := AVGlue.isMonHom_grpObjOfMono j mulY hmul oneY hone invY hinv
  haveI : IsProper (subX V).hom := h3b K A P rep V hV
  haveI : Smooth (subX V).hom := h3a K A P rep V hV
  haveI : GeometricallyReduced (subX V).hom := geometricallyReduced_of_smooth _
  haveI : GeometricallyIrreducible (subX V).hom := hirr
  haveI : GeometricallyIntegral (subX V).hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _
  refine ⟨AbVar.mk (subX V), j, ?_, ?_, hjmon⟩
  · exact inferInstanceAs (IsOpenImmersion V.ι)
  · change Set.range V.ι = _
    rw [Scheme.Opens.range_ι, hV]

end PicDict

/-! ## The two remaining general statements are theorems; final results -/

namespace PicDict

open T09Pic PkgI3 PkgI3.AbVar

/-- **`PushforwardUnitUniversal` is a theorem** (vendored
`isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral`: proper geometrically integral over a field). -/
theorem pushforwardUnitUniversal : PushforwardUnitUniversal := by
  intro K _ A T
  letI : A.X.left.Over (Spec (CommRingCat.of K)) := ⟨A.X.hom⟩
  haveI : IsProper (A.X.left ↘ Spec (CommRingCat.of K)) := inferInstanceAs (IsProper A.X.hom)
  haveI : GeometricallyIntegral (A.X.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (GeometricallyIntegral A.X.hom)
  exact isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral T

/-- **`GeomIntegralProd` is a theorem** for abelian varieties: `A × B` is smooth (so geometrically reduced) and
geometrically irreducible (Mathlib's `GeometricallyIrreducible.comp`). -/
theorem geomIntegralProd : GeomIntegralProd := by
  intro K _ A B
  have e : (A.X ⊗ B.X).hom = pullback.fst A.X.hom B.X.hom ≫ A.X.hom := rfl
  haveI : Smooth (A.X ⊗ B.X).hom := by rw [e]; infer_instance
  haveI := geometricallyReduced_of_smooth (A.X ⊗ B.X).hom
  haveI : GeometricallyIrreducible (A.X ⊗ B.X).hom := by
    rw [e]; exact GeometricallyIrreducible.comp _ _
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

/-- **Main result (`PhiAmpleIsogeny`)** from two of Mumford's statements over an algebraically closed field:
§6 Application 1 (`K(L)` finite for `L` ample) and §8 Thm 1 (`φ_L` onto `Pic⁰`). -/
theorem phiAmpleIsogeny_final (hKL : MumfordKLFiniteAC) (h8 : MumfordPhiSurjectiveAC) : PhiAmpleIsogeny :=
  phiAmpleIsogeny_of_mumford hKL h8 pushforwardUnitUniversal geomIntegralProd

/-- **Main result (`WeilPairingMumford`)** from seven of Mumford's statements over an algebraically closed field:
§6 Cor. 4, §6 App. 1, §8 (iv), §8 Thm 1, §20 (`ē_n` well defined and bilinear; nondegenerate), §23. -/
theorem weilPairingMumford_final (hsq : MumfordSquareAC) (h8iv : MumfordMulNPicZeroAC)
    (h8 : MumfordPhiSurjectiveAC) (h20a : MumfordWeilPairingAC) (h20b : MumfordWeilNondegAC)
    (h23 : MumfordWeilAltAC) (hKL : MumfordKLFiniteAC) : WeilPairingMumford :=
  weilPairingMumford_of_mumford hsq h8iv h8 h20a h20b h23 (phiAmpleIsogeny_final hKL h8)

end PicDict

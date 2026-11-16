import ZInQKernel.OneProof.H.TailZ24

/-! # pic-dict core: the Pic dictionary at `K̄` (glue), Mumford's statements at `A_K̄` (leaves) -/

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

/-- **LEAF (`ē_{mn}(x, M) = ē_n(mx, M)` for `M ∈ X̂_n`).** Mumford §20 (UNVERIFIED numbering). Instance
`X = A_K̄`. -/
def MumfordWeilCompat : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (m n : ℕ), 0 < m → 0 < n → ((m * n : ℕ) : K) ≠ 0 →
    ∀ (x : tors A (m * n)) (c : (AK A).Pic), IsDualTors n c →
      ∀ (ψ : Triv A (m * n) c) (ψ' : Triv A n c),
        weilFormula x c ψ = weilFormula (torsSmul A m n x) c ψ'

/-- **LEAF (`ē_n(x, f^*M) = ē_n(f x, M)`).** For a homomorphism `f : X → X`, Mumford §20 (5) (stated there for
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

/-- **GLUE (transport of structure along `σ ∈ G_K`).** `1 × Spec σ` on `A_K̄` carries Mumford's formula for
`(x, M)` to the formula for `(σx, σ^*M)`, and acts on constants by `σ`. -/
def WeilFormulaGalois : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), 0 < n → (n : K) ≠ 0 →
    ∀ (σ : Gal K) (x : tors A n) (c c' : (AK A).Pic), IsDualTors n c →
      c' = Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom (galHom σ)) c →
      ∀ (ψ : Triv A n c) (ψ' : Triv A n c') (u : AlgebraicClosure K),
        weilFormula x c ψ = constK A u → weilFormula (galTors A n σ x) c' ψ' = constK A (σ u)

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
§8 (iv), §8 Thm 1, §20, §23), ampleness under field extension, the Galois transport glue and the row
`PhiAmpleIsogeny`; L5 (`picPointsAlgClosed`) and the dictionary are proved. -/
theorem weilPairingMumford_of_printed (hsq : MumfordSquare) (h8iv : MumfordMulNPicZero)
    (h8 : MumfordPhiSurjective) (hamp : AmpleBaseChangeAlgClosure) (h20a : MumfordWeilPairing)
    (h20b : MumfordWeilNondeg) (h20c : MumfordWeilCompat) (h20d : MumfordWeilDual)
    (h23 : MumfordWeilAlt) (hgal : WeilFormulaGalois) (h3 : PhiAmpleIsogeny) :
    WeilPairingMumford := by
  classical
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
    exact hgal K A n hn hnK σ x _ _ (htors n y) hg (htriv n y).some _ _
      ((hspec n x y).symm.trans (hu2 n hn hnK x y).symm)
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

/-- **GLUE (finite kernel on `K̄`-points ⇒ finite).** A homomorphism of abelian varieties over `K` whose kernel
has finitely many `K̄`-points is a finite morphism (proper and quasi-finite). -/
def FiniteOfFiniteKerPts : Prop :=
  ∀ (K : Type) [Field K] (A B : AbVar K) (f : Hom A B),
    {x : A.Pt (AlgebraicClosure K) | x ≫ f.hom = 1}.Finite → IsFinite f.hom.left

/-- **`PhiAmpleIsogeny` from the leaves** (glue, proved): the kernel of `λ_L` on `K̄`-points is `K(L_K̄)`
(dictionary), and `λ_L` is onto on `K̄`-points (Mumford §8 Thm 1 and `PicZeroPtsTranslInv`). -/
theorem phiAmpleIsogeny_of_printed (hKL : MumfordKLFinite) (h8 : MumfordPhiSurjective)
    (hamp : AmpleBaseChangeAlgClosure) (hsub : PicZeroPtsTranslInv) (hfin : FiniteOfFiniteKerPts) :
    PhiAmpleIsogeny := by
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
#print axioms PicDict.weilPairingMumford_of_printed
#print axioms PicDict.phiAmpleIsogeny_of_printed
#print axioms PicDict.picPointsAlgClosed

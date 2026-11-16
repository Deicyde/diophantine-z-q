import ZInQKernel.Contrib.OneProof.PicDictionary

/-! # pic-dict: Mumford's statements over an algebraically closed field, and the bridge to `A_K̄` -/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory Limits
open scoped CategoryTheory.MonObj

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

end PicDict

#print axioms PicDict.mumfordWeilPairing_of_ac
#print axioms PicDict.mumfordWeilNondeg_of_ac
#print axioms PicDict.mumfordWeilAlt_of_ac
#print axioms PicDict.mumfordSquare_of_ac

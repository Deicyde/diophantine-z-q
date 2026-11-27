import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FrameModuli
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.OrderMod
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FibreTransfer
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.BuzzardLeaves2
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# The action of `G 5` on the level-(5,3) moduli scheme (draft)

Assumptions on the sibling structure `Moduli35` (only the adapters `rep'` and `huniq'`
below touch `rep` and `huniq`; adjust them if the shape differs):
* `sec5 : P5 ≫ A.F.hom = 𝟙 X.left`, `sec3 : P3 ≫ A.F.hom = 𝟙 X.left`;
* `rep S A' P5' P3' s5 s3 g5 g3 : ∃! g : S ⟶ X, ∃ h, (cartesian ∧ ι-compatible ∧
  P5' ≫ h = g.left ≫ P5 ∧ P3' ≫ h = g.left ≫ P3)`, with the conjuncts in that order;
* `huniq S A' P5' P3' g h h' hh hh' : h = h'`.

The extra imports `Y3FibreTransfer` and `Y3BuzzardLeaves2` are harmless if already
transitive.

Freeness needs, besides `SerreRigidityLevel3'`, the existence of geometric fibres of a false
elliptic curve as false elliptic curves (`FECGeomFibre` below): `SerreRigidityLevel3'` is stated
for an automorphism over the identity of the base, and the comparison map `h_δ` lies over
`g_δ`, so it has to be restricted to a fibre that is itself an object of `FEC`.
-/

attribute [local instance] FEC.grp

/-- Geometric fibres of false elliptic curves exist as false elliptic curves. -/
def FECGeomFibre : Prop :=
  ∀ (S : Scheme.{0}) (A : FEC S) (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ S), ∃ A' : FEC (Spec (CommRingCat.of k)), FECFibre A s A'

/-! ## 0. Generic helpers -/

/-- A group anti-hom into endomorphisms, read as a hom into `Aut`. -/
def autOfAntiHom {C : Type*} [Category C] {Y : C} {Γ : Type*} [Group Γ] (f : Γ → (Y ⟶ Y))
    (h1 : f 1 = 𝟙 Y) (hmul : ∀ a b, f (a * b) = f b ≫ f a) : Γ →* Aut Y where
  toFun δ := ⟨{ hom := f δ, inv := f δ⁻¹
                hom_inv_id := by rw [← hmul, inv_mul_cancel, h1]
                inv_hom_id := by rw [← hmul, mul_inv_cancel, h1] }⟩
  map_one' := by
    apply Aut.ext; apply Iso.ext
    first
      | (rw [Aut.one_asIso]; exact h1)
      | (simp only [Aut.one_asIso, Iso.refl_hom]; exact h1)
  map_mul' a b := by
    apply Aut.ext; apply Iso.ext
    first
      | (simp only [Aut.mul_asIso, Iso.trans_hom]; exact hmul a b)
      | (rw [Aut.Aut_mul_def]; exact hmul a b)
      | (simp only [Aut.Aut_mul_def, Iso.trans_hom]; exact hmul a b)

theorem autOfAntiHom_hom {C : Type*} [Category C] {Y : C} {Γ : Type*} [Group Γ]
    (f : Γ → (Y ⟶ Y)) (h1 : f 1 = 𝟙 Y) (hmul : ∀ a b, f (a * b) = f b ≫ f a) (δ : Γ) :
    (autOfAntiHom f h1 hmul δ).asIso.hom = f δ := rfl

/-- An automorphism in `Over S` from mutually inverse maps over `S`. -/
def isoOfInv {C : Type*} [Category C] {S : C} {F : Over S} (E E' : F.left ⟶ F.left)
    (h1 : E ≫ F.hom = F.hom) (h2 : E' ≫ F.hom = F.hom) (h3 : E ≫ E' = 𝟙 _)
    (h4 : E' ≫ E = 𝟙 _) : F ≅ F where
  hom := Over.homMk E h1
  inv := Over.homMk E' h2
  hom_inv_id := Over.OverMorphism.ext (by first | exact h3 | simp [h3])
  inv_hom_id := Over.OverMorphism.ext (by first | exact h4 | simp [h4])

theorem isoOfInv_hom_left {C : Type*} [Category C] {S : C} {F : Over S} (E E' : F.left ⟶ F.left)
    (h1 h2 h3 h4) : (isoOfInv (F := F) E E' h1 h2 h3 h4).hom.left = E := rfl

/-- Reverse transfer of `IsGenAt` along an `O`-compatible cartesian square. -/
theorem isGenAt_of_fibre_rev {S S' : Scheme.{0}} {A : FEC S} {A' : FEC S'} {g : S' ⟶ S}
    {h : A'.F.left ⟶ A.F.left} (hpb : IsPullback h A'.F.hom A.F.hom g)
    (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a) {n : ℕ} {k : Type} [Field k]
    {t' : Spec (CommRingCat.of k) ⟶ S'} {t : Spec (CommRingCat.of k) ⟶ S} (ht : t' ≫ g = t)
    {P' : Over.mk t' ⟶ A'.F} (hP : IsGenAt n A t (fibreMap hpb ht P')) :
    IsGenAt n A' t' P' := by
  dsimp only [IsGenAt] at hP ⊢
  obtain ⟨h1, h2⟩ := hP
  refine ⟨fun a => ?_, fun x hx => ?_⟩
  · rw [← fibreMap_eq_one_iff hpb hι ht, ← fibreMap_iota hpb hι ht]
    exact h1 a
  · have hx' : (fibreMap hpb ht x) ^ n = 1 := by
      rw [← fibreMap_pow hpb hι ht, hx, fibreMap_one hpb hι ht]
    obtain ⟨a, ha⟩ := h2 _ hx'
    refine ⟨a, fibreMap_injective hpb ht ?_⟩
    rw [ha, fibreMap_iota hpb hι ht]

/-- A ring map out of the base ring from a map of spectra. -/
def ringHomOfSpec {R S : CommRingCat.{0}} (f : Spec S ⟶ Spec R) : R ⟶ S := by
  first
    | exact Spec.preimage f
    | exact Spec.fullyFaithful.preimage f
    | exact (Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ (Scheme.ΓSpecIso S).hom

theorem isUnit_thirty : IsUnit (30 : Y3RouteA.Z30) := by
  first
    | simpa using IsLocalization.Away.algebraMap_isUnit (S := Y3RouteA.Z30) (30 : ℤ)
    | simpa using IsLocalization.Away.algebraMap_isUnit (S := Y3RouteA.Z30) (30 : ℕ)
    | exact Y3RouteA.isUnit_thirty

theorem ringChar_ne_of_Z30 {k : Type} [Field k] (φ : Y3RouteA.Z30 →+* k) {p : ℕ}
    (hp : p ∣ 30) : ringChar k ≠ p := by
  intro hc
  have h30 : ((30 : ℕ) : k) = 0 := (ringChar.spec k 30).2 (by rw [hc]; exact hp)
  have h30' : (30 : k) = 0 := by exact_mod_cast h30
  have hu : IsUnit (φ 30) := isUnit_thirty.map φ
  rw [map_ofNat, h30'] at hu
  exact not_isUnit_zero hu

/-! ## 1. Frame squares and the classifying maps -/

section Frame

variable (M : Moduli35)

/-- The comparison data required by `rep`. -/
def FrameSq {S : Over Z30Base} (A' : FEC S.left) (P5' P3' : S.left ⟶ A'.F.left)
    (g : S ⟶ M.X) (h : A'.F.left ⟶ M.A.F.left) : Prop :=
  IsPullback h A'.F.hom M.A.F.hom g.left ∧ (∀ a : O, A'.iota a ≫ h = h ≫ M.A.iota a) ∧
    P5' ≫ h = g.left ≫ M.P5 ∧ P3' ≫ h = g.left ≫ M.P3

theorem rep' {S : Over Z30Base} (A' : FEC S.left) (P5' P3' : S.left ⟶ A'.F.left)
    (s5 : P5' ≫ A'.F.hom = 𝟙 S.left) (s3 : P3' ≫ A'.F.hom = 𝟙 S.left)
    (g5 : IsGen 5 A' P5') (g3 : IsGen 3 A' P3') :
    ∃! g : S ⟶ M.X, ∃ h, FrameSq M A' P5' P3' g h := by
  first
    | exact M.rep S A' P5' P3' s5 s3 g5 g3
    | exact M.rep S A' P5' P3' g5 g3 s5 s3
    | exact M.rep S A' P5' P3' s5 g5 s3 g3

theorem huniq' {S : Over Z30Base} (A' : FEC S.left) (P5' P3' : S.left ⟶ A'.F.left)
    (s5 : P5' ≫ A'.F.hom = 𝟙 S.left) (s3 : P3' ≫ A'.F.hom = 𝟙 S.left)
    (g5 : IsGen 5 A' P5') (g3 : IsGen 3 A' P3') {g : S ⟶ M.X} {h h' : A'.F.left ⟶ M.A.F.left}
    (hh : FrameSq M A' P5' P3' g h) (hh' : FrameSq M A' P5' P3' g h') : h = h' := by
  first
    | exact M.huniq S A' P5' P3' g h h' hh hh'
    | exact M.huniq S A' P5' P3' s5 s3 g5 g3 g h h' hh hh'
    | exact M.huniq hh hh'

/-- Frame squares of `M.A` over itself for the twisted frame `(P5 ≫ ι u, P3)`. -/
def FrameSqU (u : O) (g : M.X ⟶ M.X) (h : M.A.F.left ⟶ M.A.F.left) : Prop :=
  FrameSq M M.A (M.P5 ≫ M.A.iota u) M.P3 g h

theorem P5_iota_congr {u v : O} (huv : ∃ c : O, u - v = ((5 : ℕ) : O) * c) :
    M.P5 ≫ M.A.iota u = M.P5 ≫ M.A.iota v := by
  obtain ⟨c, hc⟩ := huv
  have hu : u = v + ((5 : ℕ) : O) * c := by rw [← hc]; abel
  set x : Over.mk (M.P5 ≫ M.A.F.hom) ⟶ M.A.F :=
    Over.homMk (U := Over.mk (M.P5 ≫ M.A.F.hom)) M.P5 rfl with hx
  have h5 : x ≫ (Over.homMk (M.A.iota ((5 : ℕ) : O)) (M.A.iota_over _) : M.A.F ⟶ M.A.F) = 1 := by
    rw [comp_iotaHom_natCast]; exact M.gen5.1
  have key : x ≫ (Over.homMk (M.A.iota u) (M.A.iota_over u) : M.A.F ⟶ M.A.F) =
      x ≫ (Over.homMk (M.A.iota v) (M.A.iota_over v) : M.A.F ⟶ M.A.F) := by
    subst hu
    rw [comp_iota_add, comp_iota_natCast_mul_eq_one M.A 5 x h5, _root_.mul_one]
  exact congrArg (fun f : Over.mk (M.P5 ≫ M.A.F.hom) ⟶ M.A.F => f.left) key

theorem frameSqU_congr {u v : O} (huv : ∃ c : O, u - v = ((5 : ℕ) : O) * c)
    {g : M.X ⟶ M.X} {h : M.A.F.left ⟶ M.A.F.left} (hs : FrameSqU M u g h) :
    FrameSqU M v g h := by
  unfold FrameSqU at hs ⊢
  rw [← P5_iota_congr M huv]
  exact hs

theorem frameSqU_id : FrameSqU M 1 (𝟙 M.X) (𝟙 M.A.F.left) := by
  unfold FrameSqU FrameSq
  refine ⟨?_, fun a => ?_, ?_, ?_⟩
  · first
      | exact IsPullback.id_horiz M.A.F.hom
      | simpa only [Over.id_left] using IsPullback.id_horiz M.A.F.hom
  · rw [Category.comp_id, Category.id_comp]
  · first
      | (simp only [M.A.iota_one, Category.comp_id, Over.id_left, Category.id_comp])
      | (rw [M.A.iota_one]; simp)
  · first
      | (simp only [Category.comp_id, Over.id_left, Category.id_comp])
      | simp

theorem frameSqU_comp {u v : O} {g g' : M.X ⟶ M.X} {h h' : M.A.F.left ⟶ M.A.F.left}
    (s : FrameSqU M u g h) (t : FrameSqU M v g' h') :
    FrameSqU M (v * u) (g ≫ g') (h ≫ h') := by
  unfold FrameSqU FrameSq at s t ⊢
  obtain ⟨s1, s2, s3, s4⟩ := s
  obtain ⟨t1, t2, t3, t4⟩ := t
  refine ⟨?_, fun a => ?_, ?_, ?_⟩
  · rw [Over.comp_left]
    first
      | exact s1.paste_horiz t1
      | exact IsPullback.paste_horiz s1 t1
  · calc M.A.iota a ≫ h ≫ h' = (M.A.iota a ≫ h) ≫ h' := (Category.assoc _ _ _).symm
      _ = (h ≫ M.A.iota a) ≫ h' := by rw [s2 a]
      _ = h ≫ M.A.iota a ≫ h' := Category.assoc _ _ _
      _ = h ≫ h' ≫ M.A.iota a := by rw [t2 a]
      _ = (h ≫ h') ≫ M.A.iota a := (Category.assoc _ _ _).symm
  · rw [Over.comp_left, M.A.iota_mul]
    have e1 : M.A.iota v ≫ h ≫ h' = h ≫ M.A.iota v ≫ h' := by
      rw [← Category.assoc, s2 v, Category.assoc]
    calc (M.P5 ≫ (M.A.iota u ≫ M.A.iota v)) ≫ h ≫ h'
        = ((M.P5 ≫ M.A.iota u) ≫ h) ≫ M.A.iota v ≫ h' := by simp only [Category.assoc, e1]
      _ = g.left ≫ ((M.P5 ≫ M.A.iota v) ≫ h') := by rw [s3]; simp only [Category.assoc]
      _ = g.left ≫ g'.left ≫ M.P5 := by rw [t3]
  · calc M.P3 ≫ h ≫ h' = (M.P3 ≫ h) ≫ h' := (Category.assoc _ _ _).symm
      _ = (g.left ≫ M.P3) ≫ h' := by rw [s4]
      _ = g.left ≫ M.P3 ≫ h' := Category.assoc _ _ _
      _ = g.left ≫ g'.left ≫ M.P3 := by rw [t4]
      _ = (g ≫ g').left ≫ M.P3 := by rw [Over.comp_left, Category.assoc]

theorem P5u_sec (u : O) : (M.P5 ≫ M.A.iota u) ≫ M.A.F.hom = 𝟙 M.X.left := by
  rw [Category.assoc, M.A.iota_over, M.sec5]

theorem P5σ_gen (δ : Y3OrderMod.G 5) : IsGen 5 M.A (M.P5 ≫ M.A.iota (Y3OrderMod.σ δ)) := by
  obtain ⟨d, hd⟩ := Y3OrderMod.σ_inv_mul δ
  obtain ⟨d', hd'⟩ := Y3OrderMod.σ_mul_inv δ
  exact isGen_mul_unit M.gen5 hd hd'

theorem actionData (δ : Y3OrderMod.G 5) :
    ∃! g : M.X ⟶ M.X, ∃ h, FrameSqU M (Y3OrderMod.σ δ) g h :=
  rep' M M.A _ M.P3 (P5u_sec M _) M.sec3 (P5σ_gen M δ) M.gen3

/-- The classifying map of `(A, P5 ≫ ι(σ δ), P3)`. -/
def actionMap (δ : Y3OrderMod.G 5) : M.X ⟶ M.X := Classical.choose (actionData M δ).exists

/-- The comparison map `h_δ` over `actionMap δ`. -/
def actionTot (δ : Y3OrderMod.G 5) : M.A.F.left ⟶ M.A.F.left :=
  Classical.choose (Classical.choose_spec (actionData M δ).exists)

theorem actionSq (δ : Y3OrderMod.G 5) :
    FrameSqU M (Y3OrderMod.σ δ) (actionMap M δ) (actionTot M δ) :=
  Classical.choose_spec (Classical.choose_spec (actionData M δ).exists)

theorem actionSq_pb (δ : Y3OrderMod.G 5) :
    IsPullback (actionTot M δ) M.A.F.hom M.A.F.hom (actionMap M δ).left := by
  have h := actionSq M δ; unfold FrameSqU FrameSq at h; exact h.1

theorem actionTot_iota (δ : Y3OrderMod.G 5) (a : O) :
    M.A.iota a ≫ actionTot M δ = actionTot M δ ≫ M.A.iota a := by
  have h := actionSq M δ; unfold FrameSqU FrameSq at h; exact h.2.1 a

theorem actionTot_P5 (δ : Y3OrderMod.G 5) :
    (M.P5 ≫ M.A.iota (Y3OrderMod.σ δ)) ≫ actionTot M δ = (actionMap M δ).left ≫ M.P5 := by
  have h := actionSq M δ; unfold FrameSqU FrameSq at h; exact h.2.2.1

theorem actionTot_P3 (δ : Y3OrderMod.G 5) :
    M.P3 ≫ actionTot M δ = (actionMap M δ).left ≫ M.P3 := by
  have h := actionSq M δ; unfold FrameSqU FrameSq at h; exact h.2.2.2

theorem actionTot_w (δ : Y3OrderMod.G 5) :
    actionTot M δ ≫ M.A.F.hom = M.A.F.hom ≫ (actionMap M δ).left :=
  (actionSq_pb M δ).w

theorem actionMap_eq_of {δ : Y3OrderMod.G 5} {u : O}
    (hu : ∃ c : O, u - Y3OrderMod.σ δ = ((5 : ℕ) : O) * c) {g : M.X ⟶ M.X}
    {h : M.A.F.left ⟶ M.A.F.left} (s : FrameSqU M u g h) : g = actionMap M δ :=
  (actionData M δ).unique ⟨h, frameSqU_congr M hu s⟩ ⟨actionTot M δ, actionSq M δ⟩

theorem actionTot_eq_of {δ : Y3OrderMod.G 5} {u : O}
    (hu : ∃ c : O, u - Y3OrderMod.σ δ = ((5 : ℕ) : O) * c) {h : M.A.F.left ⟶ M.A.F.left}
    (s : FrameSqU M u (actionMap M δ) h) : h = actionTot M δ :=
  huniq' M M.A _ M.P3 (P5u_sec M _) M.sec3 (P5σ_gen M δ) M.gen3
    (frameSqU_congr M hu s) (actionSq M δ)

theorem one_sub_σ_one : ∃ c : O, 1 - Y3OrderMod.σ (1 : Y3OrderMod.G 5) = ((5 : ℕ) : O) * c := by
  obtain ⟨c, hc⟩ := Y3OrderMod.σ_one (M := 5)
  exact ⟨-c, by rw [mul_neg, ← hc, neg_sub]⟩

theorem actionMap_one : actionMap M 1 = 𝟙 M.X :=
  (actionMap_eq_of M one_sub_σ_one (frameSqU_id M)).symm

/-- Composition order of `Aut`: `actionMap (a * b) = actionMap b ≫ actionMap a`. -/
theorem actionMap_mul (a b : Y3OrderMod.G 5) :
    actionMap M (a * b) = actionMap M b ≫ actionMap M a :=
  (actionMap_eq_of M (Y3OrderMod.σ_mul a b) (frameSqU_comp M (actionSq M b) (actionSq M a))).symm

theorem actionTot_one : actionTot M 1 = 𝟙 M.A.F.left := by
  have s := frameSqU_id M
  rw [← actionMap_one M] at s
  exact (actionTot_eq_of M one_sub_σ_one s).symm

theorem actionTot_mul (a b : Y3OrderMod.G 5) :
    actionTot M (a * b) = actionTot M b ≫ actionTot M a := by
  have s := frameSqU_comp M (actionSq M b) (actionSq M a)
  rw [← actionMap_mul M a b] at s
  exact (actionTot_eq_of M (Y3OrderMod.σ_mul a b) s).symm

/-- The action on the base. -/
def ρ : Y3OrderMod.G 5 →* Aut M.X.left :=
  autOfAntiHom (fun δ => (actionMap M δ).left)
    (by simp only [actionMap_one M, Over.id_left])
    (fun a b => by
      show (actionMap M (a * b)).left = (actionMap M b).left ≫ (actionMap M a).left
      rw [actionMap_mul, Over.comp_left])

theorem ρ_hom (δ : Y3OrderMod.G 5) : (ρ M δ).asIso.hom = (actionMap M δ).left := rfl

theorem ρ_mul_hom (a b : Y3OrderMod.G 5) :
    (ρ M (a * b)).asIso.hom = (ρ M b).asIso.hom ≫ (ρ M a).asIso.hom := by
  rw [ρ_hom, ρ_hom, ρ_hom, actionMap_mul, Over.comp_left]

/-- The action on the total space. -/
def ρA : Y3OrderMod.G 5 →* Aut M.A.F.left :=
  autOfAntiHom (actionTot M) (actionTot_one M) (actionTot_mul M)

theorem ρA_hom (δ : Y3OrderMod.G 5) : (ρA M δ).asIso.hom = actionTot M δ := rfl

theorem ρA_equivariant (δ : Y3OrderMod.G 5) :
    (ρA M δ).asIso.hom ≫ M.A.F.hom = M.A.F.hom ≫ (ρ M δ).asIso.hom :=
  actionTot_w M δ

theorem ρA_iota (δ : Y3OrderMod.G 5) (a : O) :
    M.A.iota a ≫ (ρA M δ).asIso.hom = (ρA M δ).asIso.hom ≫ M.A.iota a :=
  actionTot_iota M δ a

theorem fix_inv {δ : Y3OrderMod.G 5} {W : Scheme.{0}} {s : W ⟶ M.X.left}
    (hzs : s ≫ (actionMap M δ).left = s) : s ≫ (actionMap M δ⁻¹).left = s := by
  calc s ≫ (actionMap M δ⁻¹).left = (s ≫ (actionMap M δ).left) ≫ (actionMap M δ⁻¹).left := by
        rw [hzs]
    _ = s ≫ (actionMap M δ ≫ actionMap M δ⁻¹).left := by rw [Over.comp_left, Category.assoc]
    _ = s := by rw [← actionMap_mul, inv_mul_cancel, actionMap_one, Over.id_left, Category.comp_id]

end Frame

/-! ## 2. Restriction to a fibre -/

section Fibre

variable {B : Scheme.{0}} {A : FEC B} {k : Type} [Field k]
  {s : Spec (CommRingCat.of k) ⟶ B} {As : FEC (Spec (CommRingCat.of k))}
  {hs : As.F.left ⟶ A.F.left}

theorem exists_fibreEndo (hpb : IsPullback hs As.F.hom A.F.hom s) (φ : A.F.left ⟶ A.F.left)
    (gB : B ⟶ B) (hφ : φ ≫ A.F.hom = A.F.hom ≫ gB) (hgB : s ≫ gB = s) :
    ∃ E : As.F.left ⟶ As.F.left, E ≫ hs = hs ≫ φ ∧ E ≫ As.F.hom = As.F.hom :=
  ⟨hpb.lift (hs ≫ φ) As.F.hom (by
      rw [Category.assoc, hφ, ← Category.assoc, hpb.w, Category.assoc, hgB]),
    hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩

theorem fibreEndo_comp_eq_id (hpb : IsPullback hs As.F.hom A.F.hom s)
    {φ ψ : A.F.left ⟶ A.F.left} (hφψ : φ ≫ ψ = 𝟙 _) {E E' : As.F.left ⟶ As.F.left}
    (hE1 : E ≫ hs = hs ≫ φ) (hE2 : E ≫ As.F.hom = As.F.hom)
    (hE1' : E' ≫ hs = hs ≫ ψ) (hE2' : E' ≫ As.F.hom = As.F.hom) : E ≫ E' = 𝟙 _ := by
  apply hpb.hom_ext
  · calc (E ≫ E') ≫ hs = E ≫ (E' ≫ hs) := Category.assoc _ _ _
      _ = (E ≫ hs) ≫ ψ := by rw [hE1', Category.assoc]
      _ = hs ≫ (φ ≫ ψ) := by rw [hE1, Category.assoc]
      _ = 𝟙 _ ≫ hs := by rw [hφψ, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, hE2', hE2, Category.id_comp]

theorem fibreEndo_iota (hpb : IsPullback hs As.F.hom A.F.hom s)
    (hι : ∀ a, As.iota a ≫ hs = hs ≫ A.iota a) {φ : A.F.left ⟶ A.F.left}
    (hφι : ∀ a, A.iota a ≫ φ = φ ≫ A.iota a) {E : As.F.left ⟶ As.F.left}
    (hE1 : E ≫ hs = hs ≫ φ) (hE2 : E ≫ As.F.hom = As.F.hom) (a : O) :
    As.iota a ≫ E = E ≫ As.iota a := by
  apply hpb.hom_ext
  · calc (As.iota a ≫ E) ≫ hs = As.iota a ≫ (E ≫ hs) := Category.assoc _ _ _
      _ = As.iota a ≫ (hs ≫ φ) := by rw [hE1]
      _ = (As.iota a ≫ hs) ≫ φ := (Category.assoc _ _ _).symm
      _ = (hs ≫ A.iota a) ≫ φ := by rw [hι a]
      _ = hs ≫ (A.iota a ≫ φ) := Category.assoc _ _ _
      _ = hs ≫ (φ ≫ A.iota a) := by rw [hφι a]
      _ = (hs ≫ φ) ≫ A.iota a := (Category.assoc _ _ _).symm
      _ = (E ≫ hs) ≫ A.iota a := by rw [hE1]
      _ = E ≫ (hs ≫ A.iota a) := Category.assoc _ _ _
      _ = E ≫ (As.iota a ≫ hs) := by rw [hι a]
      _ = (E ≫ As.iota a) ≫ hs := (Category.assoc _ _ _).symm
  · simp only [Category.assoc, hE2, As.iota_over]

/-- A fibre point over a point fixed by `φ` is fixed by the restriction `E`. -/
theorem fibre_point_fixed (hpb : IsPullback hs As.F.hom A.F.hom s) {φ : A.F.left ⟶ A.F.left}
    {E : As.F.left ⟶ As.F.left} (hE1 : E ≫ hs = hs ≫ φ) (hE2 : E ≫ As.F.hom = As.F.hom)
    {y : Spec (CommRingCat.of k) ⟶ A.F.left} (hyφ : y ≫ φ = y)
    {ys : Spec (CommRingCat.of k) ⟶ As.F.left} (h1 : ys ≫ hs = y) : ys ≫ E = ys := by
  apply hpb.hom_ext
  · calc (ys ≫ E) ≫ hs = ys ≫ (E ≫ hs) := Category.assoc _ _ _
      _ = (ys ≫ hs) ≫ φ := by rw [hE1, Category.assoc]
      _ = ys ≫ hs := by rw [h1, hyφ]
  · rw [Category.assoc, hE2]

/-- If `E` fixes every fibre section, `φ` fixes every point over `s`. -/
theorem point_fixed_of_fibre (hpb : IsPullback hs As.F.hom A.F.hom s) {φ : A.F.left ⟶ A.F.left}
    {E : As.F.left ⟶ As.F.left} (hE1 : E ≫ hs = hs ≫ φ)
    (hall : ∀ x : Spec (CommRingCat.of k) ⟶ As.F.left, x ≫ As.F.hom = 𝟙 _ → x ≫ E = x)
    (y : Spec (CommRingCat.of k) ⟶ A.F.left) (hy : y ≫ A.F.hom = s) : y ≫ φ = y := by
  obtain ⟨ys, hys1, hys2⟩ : ∃ ys, ys ≫ hs = y ∧ ys ≫ As.F.hom = 𝟙 _ :=
    ⟨hpb.lift y (𝟙 _) (by rw [hy, Category.id_comp]), hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  calc y ≫ φ = (ys ≫ hs) ≫ φ := by rw [hys1]
    _ = ys ≫ (E ≫ hs) := by rw [hE1, Category.assoc]
    _ = (ys ≫ E) ≫ hs := (Category.assoc _ _ _).symm
    _ = y := by rw [hall ys hys2, hys1]

end Fibre

/-! ## 3. Freeness -/

section Free

variable (M : Moduli35)

/-- Rigidity on a fibre: `h_δ` fixes every point over a geometric point fixed by `g_δ`. -/
theorem actionTot_fixes_fibre (hB3 : SerreRigidityLevel3') (δ : Y3OrderMod.G 5) {k : Type}
    [Field k] [IsAlgClosed k] (hc2 : ringChar k ≠ 2) (hc3 : ringChar k ≠ 3)
    (s : Spec (CommRingCat.of k) ⟶ M.X.left) (hzs : s ≫ (actionMap M δ).left = s)
    (As : FEC (Spec (CommRingCat.of k))) (hs : As.F.left ⟶ M.A.F.left)
    (hpb : IsPullback hs As.F.hom M.A.F.hom s) (hι : ∀ a, As.iota a ≫ hs = hs ≫ M.A.iota a)
    (y : Spec (CommRingCat.of k) ⟶ M.A.F.left) (hy : y ≫ M.A.F.hom = s) :
    y ≫ actionTot M δ = y := by
  have hzs' := fix_inv M hzs
  obtain ⟨E, hE1, hE2⟩ := exists_fibreEndo hpb (actionTot M δ) _ (actionTot_w M δ) hzs
  obtain ⟨E', hE1', hE2'⟩ := exists_fibreEndo hpb (actionTot M δ⁻¹) _ (actionTot_w M δ⁻¹) hzs'
  have hEE' : E ≫ E' = 𝟙 _ := fibreEndo_comp_eq_id hpb
    (by rw [← actionTot_mul, inv_mul_cancel, actionTot_one]) hE1 hE2 hE1' hE2'
  have hE'E : E' ≫ E = 𝟙 _ := fibreEndo_comp_eq_id hpb
    (by rw [← actionTot_mul, mul_inv_cancel, actionTot_one]) hE1' hE2' hE1 hE2
  -- the restriction of `P3`
  have e3 : s ≫ M.P3 ≫ M.A.F.hom = s := by rw [M.sec3, Category.comp_id]
  have h3 : (s ≫ M.P3) ≫ M.A.F.hom = s := by rw [Category.assoc, e3]
  obtain ⟨P3s, hP1, hP2⟩ : ∃ P3s, P3s ≫ hs = s ≫ M.P3 ∧ P3s ≫ As.F.hom = 𝟙 _ :=
    ⟨hpb.lift (s ≫ M.P3) (𝟙 _) (by rw [h3, Category.id_comp]),
      hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  let P3pt : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ As.F :=
    Over.homMk (U := Over.mk (𝟙 (Spec (CommRingCat.of k)))) P3s hP2
  have hG : IsGenAt 3 M.A s (Over.homMk (U := Over.mk s) (s ≫ M.P3) h3) :=
    (isGenAt_congr M.A e3 (s ≫ M.P3) (Category.assoc _ _ _) h3).1 (M.gen3.2 k s)
  have hPQ : (Over.homMk (U := Over.mk s) (s ≫ M.P3) h3 : Over.mk s ⟶ M.A.F) =
      fibreMap hpb (Category.id_comp s) P3pt :=
    Over.OverMorphism.ext hP1.symm
  have hgen3 : IsGenAt 3 As (𝟙 _) P3pt :=
    isGenAt_of_fibre_rev hpb hι (Category.id_comp s) (IsGenAt.of_eq hPQ hG)
  have hP3fix : (s ≫ M.P3) ≫ actionTot M δ = s ≫ M.P3 := by
    rw [Category.assoc, actionTot_P3, ← Category.assoc, hzs]
  have hP3s : P3s ≫ E = P3s := fibre_point_fixed hpb hE1 hE2 hP3fix hP1
  -- Serre rigidity on the fibre
  let θ : As.F ≅ As.F := isoOfInv E E' hE2 hE2' hEE' hE'E
  have hθι : ∀ a : O, As.iota a ≫ θ.hom.left = θ.hom.left ≫ As.iota a := fun a =>
    fibreEndo_iota hpb hι (actionTot_iota M δ) hE1 hE2 a
  have hfix3 : P3pt ≫ θ.hom = P3pt := Over.OverMorphism.ext (by
    first
      | exact hP3s
      | simpa only [Over.comp_left, Over.homMk_left, θ, isoOfInv_hom_left, P3pt] using hP3s)
  have hθ := hB3 (Spec (CommRingCat.of k)) As θ hθι k hc2 hc3 (𝟙 _) P3pt hgen3 hfix3
  have hall : ∀ x : Spec (CommRingCat.of k) ⟶ As.F.left, x ≫ As.F.hom = 𝟙 _ → x ≫ E = x := by
    intro x hx
    have hl := congrArg (fun f => f.left)
      (hθ (Over.homMk (U := Over.mk (𝟙 (Spec (CommRingCat.of k)))) x hx))
    first
      | exact hl
      | simpa only [Over.comp_left, Over.homMk_left, θ, isoOfInv_hom_left] using hl
  exact point_fixed_of_fibre hpb hE1 hall y hy

/-- A geometric point at which `ι(u) P5 = P5` forces `u ≡ 1 mod 5`. -/
theorem rel_of_fixed_P5 {k : Type} [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ M.X.left) (u : O)
    (hfix : s ≫ M.P5 ≫ M.A.iota u = s ≫ M.P5) : ∃ b : O, u - 1 = ((5 : ℕ) : O) * b := by
  have e : s ≫ M.P5 ≫ M.A.F.hom = s := by rw [M.sec5, Category.comp_id]
  have h₂ : (s ≫ M.P5) ≫ M.A.F.hom = s := by rw [Category.assoc, e]
  have hg := (isGenAt_congr M.A e (s ≫ M.P5) (Category.assoc _ _ _) h₂).1 (M.gen5.2 k s)
  dsimp only [IsGenAt] at hg
  set P : Over.mk s ⟶ M.A.F := Over.homMk (U := Over.mk s) (s ≫ M.P5) h₂ with hP
  have hPu : P ≫ (Over.homMk (M.A.iota u) (M.A.iota_over u) : M.A.F ⟶ M.A.F) = P := by
    exact Over.OverMorphism.ext (by
      show (s ≫ M.P5) ≫ M.A.iota u = s ≫ M.P5
      rw [Category.assoc]
      exact hfix)
  have ha := comp_iota_add M.A P u (-1)
  have hb := comp_iota_add M.A P 1 (-1)
  rw [hPu] at ha
  rw [iotaHom_one, Category.comp_id] at hb
  have hc := ha.trans hb.symm
  have e0 : (1 : O) + -1 = 0 := by simp
  have e1 : u + -1 = u - 1 := (sub_eq_add_neg u 1).symm
  rw [e0, iotaHom_zero, MonObj.comp_one, e1] at hc
  exact (hg.1 (u - 1)).1 hc

theorem eq_one_of_rel {δ : Y3OrderMod.G 5}
    (h : ∃ b : O, Y3OrderMod.σ δ - 1 = ((5 : ℕ) : O) * b) : δ = 1 := by
  apply Units.ext
  rw [Units.val_one, ← Y3OrderMod.σ_spec δ]
  have h' := (Y3OrderMod.coe_eq_coe_iff (M := 5) (x := Y3OrderMod.σ δ) (y := 1)).2 h
  rw [h']
  first | exact RingCon.coe_one _ | rfl | simp

/-- No geometric point is fixed by `ρ δ` for `δ ≠ 1`. -/
theorem fixedPointFree_geom (hB3 : SerreRigidityLevel3') (hBC : FECGeomFibre)
    {δ : Y3OrderMod.G 5} (hδ : δ ≠ 1) {T : Scheme.{0}} (z : T ⟶ M.X.left)
    (hz : z ≫ (ρ M δ).asIso.hom = z) (k : Type) [Field k] [IsAlgClosed k]
    (t : Spec (CommRingCat.of k) ⟶ T) : False := by
  apply hδ
  have hz' : z ≫ (actionMap M δ).left = z := hz
  have hzs : (t ≫ z) ≫ (actionMap M δ).left = t ≫ z := by rw [Category.assoc, hz']
  let φ := (ringHomOfSpec (t ≫ z ≫ M.X.hom)).hom
  have hc2 : ringChar k ≠ 2 := ringChar_ne_of_Z30 φ (by norm_num)
  have hc3 : ringChar k ≠ 3 := ringChar_ne_of_Z30 φ (by norm_num)
  obtain ⟨As, hAs⟩ := hBC M.X.left M.A k (t ≫ z)
  have hAs' : ∃ h, IsPullback h As.F.hom M.A.F.hom (t ≫ z) ∧
      ∀ a : O, As.iota a ≫ h = h ≫ M.A.iota a := hAs
  obtain ⟨hs, hpb, hι⟩ := hAs'
  have hy : ((t ≫ z) ≫ M.P5 ≫ M.A.iota (Y3OrderMod.σ δ)) ≫ M.A.F.hom = t ≫ z := by
    simp only [Category.assoc, M.A.iota_over, M.sec5, Category.comp_id]
  have hfixy := actionTot_fixes_fibre M hB3 δ hc2 hc3 (t ≫ z) hzs As hs hpb hι _ hy
  have hP5 : (t ≫ z) ≫ M.P5 ≫ M.A.iota (Y3OrderMod.σ δ) = (t ≫ z) ≫ M.P5 := by
    calc (t ≫ z) ≫ M.P5 ≫ M.A.iota (Y3OrderMod.σ δ)
        = ((t ≫ z) ≫ M.P5 ≫ M.A.iota (Y3OrderMod.σ δ)) ≫ actionTot M δ := hfixy.symm
      _ = (t ≫ z) ≫ ((M.P5 ≫ M.A.iota (Y3OrderMod.σ δ)) ≫ actionTot M δ) :=
          Category.assoc _ _ _
      _ = (t ≫ z) ≫ ((actionMap M δ).left ≫ M.P5) := by rw [actionTot_P5]
      _ = ((t ≫ z) ≫ (actionMap M δ).left) ≫ M.P5 := (Category.assoc _ _ _).symm
      _ = (t ≫ z) ≫ M.P5 := by rw [hzs]
  exact eq_one_of_rel (rel_of_fixed_P5 M (t ≫ z) _ hP5)

theorem fixedPointFree (hB3 : SerreRigidityLevel3') (hBC : FECGeomFibre)
    {δ : Y3OrderMod.G 5} (hδ : δ ≠ 1) (T : Scheme.{0}) (z : T ⟶ M.X.left)
    (hz : z ≫ (ρ M δ).asIso.hom = z) : IsEmpty T := by
  by_contra hne
  obtain ⟨x⟩ := not_isEmpty_iff.mp hne
  exact fixedPointFree_geom M hB3 hBC hδ z hz (AlgebraicClosure (T.residueField x))
    (Spec.map (CommRingCat.ofHom
        (algebraMap (T.residueField x) (AlgebraicClosure (T.residueField x)))) ≫
      T.fromSpecResidueField x)

/-- The hypothesis in the shape used by the quotient step. -/
theorem hfix (hB3 : SerreRigidityLevel3') (hBC : FECGeomFibre) :
    ∀ δ : Y3OrderMod.G 5, δ ≠ 1 → ∀ (T : Scheme.{0}) (z : T ⟶ M.X.left),
      z ≫ (ρ M δ).asIso.hom = z → IsEmpty T :=
  fun _ hδ T z hz => fixedPointFree M hB3 hBC hδ T z hz

end Free

end Y3Buzzard

import ZInQKernel.Contrib.OneProof.RC.HCMV21.LevelIdealPrincipal
import ZInQKernel.Contrib.OneProof.RC.HCMV21.LevelOrderClasses

/-! The map from isomorphism classes of supersingular enhanced elliptic curves
of level `N` to `ClassSet (levelOrder q h N hN)` (tex 8465–8468), for a fixed
reference pair `(E₀, ⟨P₀⟩)` with frame `j : End(E₀) ≃+* S.ring`.

For an enhanced curve `(E, C)`, a placement of `Hom(E, E₀)` (the invertibility
clause of the Theorem 42.3.2 candidate) puts the lattice of maps sending `C`
into `C₀ = ⟨P₀⟩` in `B = ℍ[ℚ,-1,0,-q]` as a locally principal left ideal of the
enhanced reference order `End(E₀, C₀)`. Its class does not depend on the
placement and is constant on isomorphism classes. The mirror carries it to
the right-ideal class set, and the reference coordinate `z` to the explicit
`levelOrder`. The reference pair goes to the class of `fromAdelic z`. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry Eichler Adelic PkgI3.AbVar
open scoped CategoryTheory.MonObj

section Placement

variable {k : Type} [Field k] {a b : ℚ} {E₀ E : PkgI3.AbVar k}
  {S : Order a b} {j : E₀.End ≃+* S.ring}

theorem LeftIdeal.self_locallyPrincipal (R : Order a b) : (LeftIdeal.self R).LocallyPrincipal := by
  intro p _
  refine ⟨1, ?_⟩
  change (localLattice p R.lattice : Set (Bp p a b)) =
    (fun x : Bp p a b => x * ((1 : (Bp p a b)ˣ) : Bp p a b)) '' (R.completion p : Set (Bp p a b))
  rw [← R.completion_toSubmodule]
  simp
  rfl

/-- The canonical placement of `End(E₀)` through the frame. -/
def selfPlacement (S : Order a b) (j : E₀.End ≃+* S.ring) : HomPlacement S j E₀ where
  emb := (S.ring.subtype.comp j.toRingHom).toAddMonoidHom
  injective := Subtype.val_injective.comp j.injective
  map_postcomp o α := by
    change ((j (postcomp o α) : S.ring) : B a b) = (j o : B a b) * (j α : B a b)
    have h : postcomp o α = o * α := rfl
    rw [h, map_mul]
    rfl
  ideal := ⟨LeftIdeal.self S, LeftIdeal.self_locallyPrincipal S⟩
  range_eq := by
    ext x
    constructor
    · intro hx
      exact ⟨j.symm ⟨x, hx⟩, congrArg Subtype.val (j.apply_symm_apply ⟨x, hx⟩)⟩
    · rintro ⟨y, rfl⟩
      exact (j y).property

theorem levelLattice_of_mul (P P' : HomPlacement S j E) (u : (B a b)ˣ)
    (h : ∀ α, P'.emb α = P.emb α * u) (C : Subgroup (E.Pt k)) (C₀ : Subgroup (E₀.Pt k)) :
    levelLattice P' C C₀ = (levelLattice P C C₀).map ((mulRightEquiv u).restrictScalars ℤ).toLinearMap := by
  ext x
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨P.emb α, ⟨α, hα, rfl⟩, (h α).symm⟩
  · rintro ⟨_, ⟨α, hα, rfl⟩, rfl⟩
    exact ⟨α, hα, h α⟩

/-- The placed level lattice of the reference is the enhanced reference order. -/
theorem levelLattice_selfPlacement (C₀ : Subgroup (E₀.Pt k)) (N : ℕ) (hN : N ≠ 0)
    (hC₀ : ∀ x ∈ C₀, x ^ N = 1) :
    levelLattice (selfPlacement S j) C₀ C₀ = (levelOrderOfEndOrder S j C₀ N hN hC₀).lattice := by
  ext x
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨α, hα, rfl⟩
  · rintro ⟨α, hα, rfl⟩
    exact ⟨α, hα, rfl⟩

end Placement

theorem SupersingularEnhanced.pow_level_eq_one {q : ℕ} [Fact q.Prime] {k : Type} [Field k]
    [Algebra (ZMod q) k] [IsAlgClosure (ZMod q) k] {N : ℕ} (X : SupersingularEnhanced q k N) :
    ∀ x ∈ X.level, x ^ N = 1 := by
  intro x hx
  have h1 : (⟨x, hx⟩ : X.level) ^ Nat.card X.level = 1 := pow_card_eq_one'
  rw [X.card_level] at h1
  exact congrArg Subtype.val h1

theorem zpowers_pow_eq_one {G : Type*} [Group G] (N : ℕ) (P₀ : G) (hP₀ : orderOf P₀ = N) :
    ∀ x ∈ Subgroup.zpowers P₀, x ^ N = 1 := by
  intro x hx
  obtain ⟨m, rfl⟩ := hx
  change (P₀ ^ m) ^ N = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hP₀, pow_orderOf_eq_one,
    one_zpow]

/-- The enhanced reference order `End(E₀, ⟨P₀⟩)` in the frame. -/
abbrev enhancedReferenceOrder (q : ℕ) {k : Type} [Field k] (N : ℕ) (hN : 0 < N)
    {E₀ : PkgI3.AbVar k} (P₀ : E₀.Pt k) (hP₀ : orderOf P₀ = N)
    (S : Order (-1) (-(q : ℚ))) (j : E₀.End ≃+* S.ring) : Order (-1) (-(q : ℚ)) :=
  levelOrderOfEndOrder S j (Subgroup.zpowers P₀) N hN.ne' (zpowers_pow_eq_one N P₀ hP₀)

section Map

variable {q : ℕ} [Fact q.Prime] {k : Type} [Field k] [Algebra (ZMod q) k]
  [IsAlgClosure (ZMod q) k] {N : ℕ} (hN : 0 < N) (hcop : N.Coprime q)
  {E₀ : PkgI3.AbVar k} {P₀ : E₀.Pt k} (hP₀ : orderOf P₀ = N)
  {S : Order (-1) (-(q : ℚ))} {j : E₀.End ≃+* S.ring}

/-- The placed level ideal of an enhanced curve, for a given placement. -/
def placedLevelIdeal (X : SupersingularEnhanced q k N) (P : HomPlacement S j X.curve) :
    LeftIdeal (enhancedReferenceOrder q N hN P₀ hP₀ S j) :=
  levelIdeal P (Subgroup.zpowers P₀) hN.ne' (zpowers_pow_eq_one N P₀ hP₀) X.level
    X.pow_level_eq_one

include hcop in
set_option maxHeartbeats 400000 in
theorem placedLevelIdeal_locallyPrincipal (h₀ : IsSupersingular E₀)
    (X : SupersingularEnhanced q k N) (P : HomPlacement S j X.curve) :
    (placedLevelIdeal hN hP₀ X P).LocallyPrincipal := by
  haveI := charP_of_isAlgClosure q k
  haveI := isAlgClosed_of_isAlgClosure q k
  intro p _
  obtain ⟨Pt, hX, hPt⟩ := X.exists_generator
  by_cases hpN : p ∣ N
  · have hpq : p ≠ q := by
      rintro rfl
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop.symm hpN
    have hp : (p : k) ≠ 0 := by
      intro hz
      have hd := (CharP.cast_eq_zero_iff k q p).mp hz
      exact hpq ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp hd).symm
    have hC : ∀ x ∈ Subgroup.zpowers Pt, x ^ N = 1 := hX ▸ X.pow_level_eq_one
    obtain ⟨u, hu⟩ := levelIdeal_locallyPrincipal_tate P X.supersingular.1 h₀.1 N hN.ne' Pt hPt
      P₀ hP₀ (zpowers_pow_eq_one N P₀ hP₀) hC p hp hpN
    refine ⟨u, ?_⟩
    have he : (placedLevelIdeal hN hP₀ X P).lattice =
        (levelIdeal P (Subgroup.zpowers P₀) hN.ne' (zpowers_pow_eq_one N P₀ hP₀)
          (Subgroup.zpowers Pt) hC).lattice := by
      change levelLattice P X.level _ = levelLattice P (Subgroup.zpowers Pt) _
      rw [hX]
    rw [he]
    exact hu
  · have hpN' : IsUnit (N : ℤ_[p]) :=
      PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
        ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpN))
    exact levelIdeal_locallyPrincipal_away P (Subgroup.zpowers P₀) hN.ne'
      (zpowers_pow_eq_one N P₀ hP₀) X.pow_level_eq_one p hpN'

/-- The left ideal class of the placed level ideal. -/
def placedLevelClass (h₀ : IsSupersingular E₀) (X : SupersingularEnhanced q k N)
    (P : HomPlacement S j X.curve) : LeftClassSet (enhancedReferenceOrder q N hN P₀ hP₀ S j) :=
  Quotient.mk _ ⟨placedLevelIdeal hN hP₀ X P, placedLevelIdeal_locallyPrincipal hN hcop hP₀ h₀ X P⟩

theorem placedLevelIdeal_of_mul (X : SupersingularEnhanced q k N) (P P' : HomPlacement S j X.curve)
    (u : (Eichler.B (-1) (-(q : ℚ)))ˣ) (hu : ∀ α, P'.emb α = P.emb α * u) :
    placedLevelIdeal hN hP₀ X P' = (placedLevelIdeal hN hP₀ X P).translate u := by
  apply LeftIdeal.ext
  exact levelLattice_of_mul P P' u hu _ _

theorem neg_q_lt_zero : (-(q : ℚ)) < 0 := by
  have : (0 : ℚ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  linarith

/-- The class does not depend on the placement. -/
theorem placedLevelClass_eq (h₀ : IsSupersingular E₀) (X : SupersingularEnhanced q k N)
    (P P' : HomPlacement S j X.curve) :
    placedLevelClass hN hcop hP₀ h₀ X P = placedLevelClass hN hcop hP₀ h₀ X P' := by
  obtain ⟨u, hu⟩ := P.exists_unit (by norm_num) (neg_q_lt_zero (q := q)) P'
  apply Quotient.sound
  exact ⟨u, (placedLevelIdeal_of_mul hN hP₀ X P P' u hu).symm⟩

/-- The class is constant on isomorphism classes of enhanced curves. -/
theorem placedLevelClass_iso (h₀ : IsSupersingular E₀) {X Y : SupersingularEnhanced q k N}
    (e : EnhancedIso X Y) (P : HomPlacement S j X.curve) (P' : HomPlacement S j Y.curve) :
    placedLevelClass hN hcop hP₀ h₀ X P = placedLevelClass hN hcop hP₀ h₀ Y P' := by
  let P'' := P'.transport e.hom e.inv e.hom_inv e.inv_hom
  rw [placedLevelClass_eq hN hcop hP₀ h₀ X P P'']
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  apply LeftIdeal.ext
  exact levelLattice_transport P' e.hom e.inv e.hom_inv e.inv_hom X.level Y.level e.map_level

variable (hInv : VoightThm4232Invertible)

/-- The left ideal class of an enhanced curve, through the placement given
by the invertibility clause of the Theorem 42.3.2 candidate. -/
def levelLeftClass (h₀ : IsSupersingular E₀) (X : SupersingularEnhanced q k N) :
    LeftClassSet (enhancedReferenceOrder q N hN P₀ hP₀ S j) :=
  placedLevelClass hN hcop hP₀ h₀ X (hInv q k E₀ h₀ _ _ S j X.curve X.supersingular).some

/-- The left ideal class on isomorphism classes of enhanced curves. -/
def enhancedLeftClass (h₀ : IsSupersingular E₀) :
    EnhancedClasses q k N → LeftClassSet (enhancedReferenceOrder q N hN P₀ hP₀ S j) :=
  Quotient.lift (levelLeftClass hN hcop hP₀ hInv h₀) (by
    rintro X Y ⟨e⟩
    exact placedLevelClass_iso hN hcop hP₀ h₀ e _ _)

/-- The reference enhanced curve has the unit left ideal class. -/
theorem enhancedLeftClass_reference (h₀ : IsSupersingular E₀) :
    enhancedLeftClass hN hcop hP₀ hInv h₀ (S := S) (j := j) (Quotient.mk _ (referenceEnhanced E₀ h₀ P₀ hP₀)) =
      Quotient.mk _ ⟨LeftIdeal.self _, LeftIdeal.self_locallyPrincipal _⟩ := by
  change placedLevelClass hN hcop hP₀ h₀ (referenceEnhanced E₀ h₀ P₀ hP₀) _ = _
  rw [placedLevelClass_eq hN hcop hP₀ h₀ (referenceEnhanced E₀ h₀ P₀ hP₀) _ (selfPlacement S j)]
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  apply LeftIdeal.ext
  exact levelLattice_selfPlacement (Subgroup.zpowers P₀) N hN.ne' (zpowers_pow_eq_one N P₀ hP₀)

end Map

section Classes

variable {q : ℕ} [Fact q.Prime] (h : q % 4 = 3) {k : Type} [Field k] [Algebra (ZMod q) k]
  [IsAlgClosure (ZMod q) k] {N : ℕ} (hN : 0 < N) (hcop : N.Coprime q)
  {E₀ : PkgI3.AbVar k} (h₀ : IsSupersingular E₀) {P₀ : E₀.Pt k} (hP₀ : orderOf P₀ = N)
  {S : Order (-1) (-(q : ℚ))} (j : E₀.End ≃+* S.ring)
  (hmax : ∀ T : Order (-1) (-(q : ℚ)), S.ring ≤ T.ring → T.ring ≤ S.ring)

include hcop h₀ hmax in
theorem exists_enhancedReferenceCoordinates :
    ∃ z : Adelic.FiniteUnits (levelOrder q h N hN),
      ReferenceOrderCoordinates (levelOrder q h N hN) (enhancedReferenceOrder q N hN P₀ hP₀ S j) z := by
  haveI := charP_of_isAlgClosure q k
  haveI := isAlgClosed_of_isAlgClosure q k
  exact exists_levelReferenceCoordinates HDec.CMSerreTate.P1.originalTateModuleFree_proved
    q h N hN hcop S j hmax h₀.1 P₀ hP₀ (zpowers_pow_eq_one N P₀ hP₀)

/-- The chosen reference coordinate of the enhanced reference order in `levelOrder`. -/
def enhancedReferenceCoordinate : Adelic.FiniteUnits (levelOrder q h N hN) :=
  Classical.choose (exists_enhancedReferenceCoordinates h hN hcop h₀ hP₀ j hmax)

theorem enhancedReferenceCoordinate_spec :
    ReferenceOrderCoordinates (levelOrder q h N hN) (enhancedReferenceOrder q N hN P₀ hP₀ S j)
      (enhancedReferenceCoordinate h hN hcop h₀ hP₀ j hmax) :=
  Classical.choose_spec (exists_enhancedReferenceCoordinates h hN hcop h₀ hP₀ j hmax)

variable (hInv : VoightThm4232Invertible)

/-- **The level-`N` Deuring class map.** Isomorphism classes of supersingular
enhanced elliptic curves of level `N` to the class set of the explicit
`levelOrder`: the placed level ideal, its mirror, and right multiplication by
the reference coordinate. -/
def levelDeuringClass : EnhancedClasses q k N → ClassSet (levelOrder q h N hN) :=
  fun x => classSetEquivOfReference (enhancedReferenceCoordinate_spec h hN hcop h₀ hP₀ j hmax)
    (leftClassSetEquiv _ (enhancedLeftClass hN hcop hP₀ hInv h₀ (S := S) (j := j) x))

/-- **Reference lemma.** The reference pair goes to the class of `fromAdelic z`. -/
theorem levelDeuringClass_reference :
    levelDeuringClass h hN hcop h₀ hP₀ j hmax hInv (Quotient.mk _ (referenceEnhanced E₀ h₀ P₀ hP₀)) =
      Quotient.mk _ (fromAdelic (enhancedReferenceCoordinate h hN hcop h₀ hP₀ j hmax)) := by
  unfold levelDeuringClass
  rw [enhancedLeftClass_reference, leftClassSetEquiv_mk]
  have hm : LPLeftIdeal.mirror (⟨LeftIdeal.self (enhancedReferenceOrder q N hN P₀ hP₀ S j),
      LeftIdeal.self_locallyPrincipal _⟩ : LPLeftIdeal (enhancedReferenceOrder q N hN P₀ hP₀ S j)) =
      (⟨RightIdeal.self _, RightIdeal.self_locallyPrincipal _⟩ :
        LPIdeal (enhancedReferenceOrder q N hN P₀ hP₀ S j)) :=
    Subtype.ext (LeftIdeal.mirror_self _)
  rw [hm, classSetEquivOfReference_self]

end Classes

end ZInQ.Manuscript.RC.HCMV21

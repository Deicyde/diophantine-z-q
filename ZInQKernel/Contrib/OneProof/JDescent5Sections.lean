import ZInQKernel.Contrib.OneProof.JDescent5Cubic
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq

/-! Regular sections on the complement of the identity. -/

namespace HDec.CMBranch.CMjBridges

open CategoryTheory AlgebraicGeometry TauCeti TopologicalSpace
noncomputable section

attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra

/-- The open obtained by removing the image of the unit section. -/
def abVarPunctured {L : Type} [Field L] (A : PkgI3.AbVar L) : A.X.left.Opens :=
  ⟨{abVarIdentity A}ᶜ, (abVarIdentity_isClosed A).isOpen_compl⟩

theorem germToFunctionField_restrict {X : Scheme} [IsIntegral X]
    {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V) (s : Γ(X, V)) :
    X.germToFunctionField U (X.presheaf.map i.op s) = X.germToFunctionField V s :=
  X.presheaf.germ_res_apply i _ _ s

private theorem exists_section_of_mem_stalks_at_closedPoints {X : Scheme} [IsIntegral X]
    [JacobsonSpace X] (U : X.Opens) [Nonempty U] (f : X.functionField)
    (hf : ∀ x ∈ U, IsClosed ({x} : Set X) →
      f ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ s : Γ(X, U), X.germToFunctionField U s = f := by
  classical
  have loc (x : U) : ∃ (V : X.Opens), V ≤ U ∧ ∃ (hx : x.1 ∈ V) (s : Γ(X, V)),
      ∀ (_ : Nonempty V), X.germToFunctionField V s = f := by
    obtain ⟨y, ⟨hycl, hyU⟩, hy⟩ := nonempty_inter_closedPoints
      (Z := closure ({x.1} : Set X) ∩ U)
      ⟨x.1, subset_closure (Set.mem_singleton _), x.2⟩
      (isClosed_closure.isLocallyClosed.inter U.isOpen.isLocallyClosed)
    obtain ⟨g, hg⟩ := hf y hyU hy
    obtain ⟨V, hVU, hyV, s, hs⟩ := X.presheaf.exists_le_germ_eq g hyU
    refine ⟨V, hVU, (specializes_iff_mem_closure.mpr hycl).mem_open V.isOpen hyV, s, ?_⟩
    intro inst
    rw [← X.algebraMap_germ_eq_germToFunctionField hyV, hs, hg]
  choose V hVU hxV s hs using loc
  have hV (x : U) : Nonempty (V x) := ⟨⟨x.1, hxV x⟩⟩
  have hcover : U ≤ ⨆ x, V x := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  have compat : X.presheaf.IsCompatible V s := by
    intro i j
    let η := genericPoint X
    have hη (i : U) : η ∈ V i :=
      (genericPoint_spec X).specializes (Set.mem_univ i.1) |>.mem_open (V i).isOpen (hxV i)
    have := hV i
    have := hV j
    have : Nonempty (V i ⊓ V j : X.Opens) := ⟨⟨η, hη i, hη j⟩⟩
    apply X.germToFunctionField_injective (V i ⊓ V j)
    rw [germToFunctionField_restrict, germToFunctionField_restrict, hs, hs]
  obtain ⟨t₀, ht, _⟩ := X.sheaf.existsUnique_gluing' V U (fun i => homOfLE (hVU i)) hcover s compat
  obtain ⟨i⟩ := ‹Nonempty U›
  let t : Γ(X, U) := t₀
  have hi := hV i
  have ht' : X.presheaf.map (homOfLE (hVU i)).op t = s i := ht i
  refine ⟨t, ?_⟩
  calc
    X.germToFunctionField U t =
        X.germToFunctionField (V i) (X.presheaf.map (homOfLE (hVU i)).op t) :=
      (germToFunctionField_restrict (homOfLE (hVU i)) t).symm
    _ = X.germToFunctionField (V i) (s i) := congrArg (X.germToFunctionField (V i)) ht'
    _ = f := hs i hi

theorem abVarPunctured_nonempty {L : Type} [Field L] (A : PkgI3.AbVar L)
    (P : Place L (AbVarFunctionField A))
    (hp : (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).range =
      P.integers.toSubring) : Nonempty (abVarPunctured A) := by
  let X := A.X.left
  have hη : genericPoint X ≠ abVarIdentity A := by
    intro h
    let R (p : X) : Subring X.functionField :=
      (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ p))).hom.range
    have he : R (abVarIdentity A) = P.integers.toSubring := hp
    have hir : R (genericPoint X) = ⊤ := by
      dsimp [R]
      rw [X.presheaf.stalkSpecializes_refl]
      exact RingHom.range_eq_top.mpr (fun x => ⟨x, rfl⟩)
    rw [← h, hir] at he
    exact P.integers_ne_top (ValuationSubring.toSubring_injective he.symm)
  exact ⟨⟨genericPoint X, hη⟩⟩

/-- A function with nonnegative order away from the identity place is a section on the
complement of the identity. -/
private theorem abVar_section_of_nonnegative_orders {L : Type} [Field L] [CharZero L]
    (A : PkgI3.AbVar L) (hdim : A.dim = 1) (P : Place L (AbVarFunctionField A))
    (hP : (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).range =
      P.integers.toSubring) (f : AbVarFunctionField A)
    (hf : ∀ Q, Q ≠ P → 0 ≤ Q.ord f) :
    letI := abVarPunctured_nonempty A P hP
    ∃ s : Γ(A.X.left, abVarPunctured A), A.X.left.germToFunctionField (abVarPunctured A) s = f := by
  have := abVarPunctured_nonempty A P hP
  let X := A.X.left
  have := abVar_smoothRelDimOne A hdim
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace A.X.hom
  apply exists_section_of_mem_stalks_at_closedPoints
  intro x hx hxcl
  obtain ⟨v, hv⟩ := AlgebraicCurve.exists_place_range_stalk_eq A.X.hom x hxcl
  let Q := Place.ofValuationSubring (A := v.toValuationSubring)
    (abVar_isFunctionField A hdim) v.algebraMap_mem' v.ne_top'
  have hQ : (algebraMap (X.presheaf.stalk x) X.functionField).range = Q.integers.toSubring := by
    simpa [Q, Place.integers_ofValuationSubring] using hv
  have hn : Q ≠ P := by
    intro h
    have hEq := AlgebraicCurve.eq_of_range_stalk_eq A.X.hom x (abVarIdentity A)
      (hQ.trans (h ▸ hP).symm)
    exact hx hEq
  rw [hQ]
  exact Q.mem_integers_iff_ord_nonneg.mpr (hf Q hn)

noncomputable def abVarSectionConst {L : Type} [Field L] (A : PkgI3.AbVar L)
    (U : A.X.left.Opens) (a : L) : Γ(A.X.left, U) :=
  A.X.hom.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (CommRingCat.of L)).inv a)

theorem germToFunctionField_abVarSectionConst {L : Type} [Field L] (A : PkgI3.AbVar L)
    (U : A.X.left.Opens) [Nonempty U] (a : L) :
    A.X.left.germToFunctionField U (abVarSectionConst A U a) =
      algebraMap L (AbVarFunctionField A) a := by
  obtain ⟨z, hz⟩ := ‹Nonempty U›
  rw [← A.X.left.algebraMap_germ_eq_germToFunctionField hz]
  symm
  change (AlgebraicCurve.baseToFunctionField A.X.hom) a = _
  open P2MW.S_AlgebraicCurve_exists_place_range_stalk_eq in
  rw [AlgebraicCurve.baseToFunctionField_apply_eq_algebraMap_stalk A.X.hom z a]
  congr 1
  let X := A.X.left
  let c : Γ(X, ⊤) := A.X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of L)).inv a)
  change X.presheaf.germ ⊤ z trivial c =
    X.presheaf.germ U z hz (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op c)
  exact (X.presheaf.germ_res_apply (homOfLE le_top) z hz c).symm

/-- The algebraic coordinates are regular sections off the identity and satisfy the same
nonsingular cubic as in the generic stalk. -/
theorem abVar_shortSections_of_genusOne {L : Type} [Field L] [NumberField L]
    (hgenus : AbVarFunctionFieldGenusOne) (A : PkgI3.AbVar L) (hdim : A.dim = 1) :
    ∃ (P : Place L (AbVarFunctionField A))
      (hp : (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).range =
        P.integers.toSubring) (x y : Γ(A.X.left, abVarPunctured A)) (a b : L),
      have := abVarPunctured_nonempty A P hp
      P.ord (A.X.left.germToFunctionField (abVarPunctured A) x) = -2 ∧
      P.ord (A.X.left.germToFunctionField (abVarPunctured A) y) = -3 ∧
      (∀ Q, Q ≠ P → 0 ≤ Q.ord (A.X.left.germToFunctionField (abVarPunctured A) x) ∧
        0 ≤ Q.ord (A.X.left.germToFunctionField (abVarPunctured A) y)) ∧
      y ^ 2 = x ^ 3 + abVarSectionConst A _ a * x + abVarSectionConst A _ b ∧
      (⟨0, 0, 0, a, b⟩ : WeierstrassCurve L).Δ ≠ 0 := by
  obtain ⟨P, X, Y, a, b, hp, _, _, hxo, hyo, hreg, heq, hΔ⟩ :=
    abVar_shortCubic_of_genusOne hgenus A hdim
  have := abVarPunctured_nonempty A P hp
  obtain ⟨x, hx⟩ := abVar_section_of_nonnegative_orders A hdim P hp X (fun Q hQ => (hreg Q hQ).1)
  obtain ⟨y, hy⟩ := abVar_section_of_nonnegative_orders A hdim P hp Y (fun Q hQ => (hreg Q hQ).2)
  refine ⟨P, hp, x, y, a, b, hx ▸ hxo, hy ▸ hyo, fun Q hQ => hx ▸ hy ▸ hreg Q hQ, ?_, hΔ⟩
  apply A.X.left.germToFunctionField_injective (abVarPunctured A)
  change (A.X.left.germToFunctionField (abVarPunctured A)).hom _ =
    (A.X.left.germToFunctionField (abVarPunctured A)).hom _
  rw [map_pow, map_add, map_add, map_pow, map_mul]
  change A.X.left.germToFunctionField _ y ^ 2 = A.X.left.germToFunctionField _ x ^ 3 +
    A.X.left.germToFunctionField _ (abVarSectionConst A _ a) * A.X.left.germToFunctionField _ x +
    A.X.left.germToFunctionField _ (abVarSectionConst A _ b)
  rwa [germToFunctionField_abVarSectionConst, germToFunctionField_abVarSectionConst, hx, hy]

#print axioms germToFunctionField_restrict
#print axioms exists_section_of_mem_stalks_at_closedPoints
#print axioms abVarPunctured_nonempty
#print axioms abVar_section_of_nonnegative_orders
#print axioms germToFunctionField_abVarSectionConst
#print axioms abVar_shortSections_of_genusOne

end

end HDec.CMBranch.CMjBridges

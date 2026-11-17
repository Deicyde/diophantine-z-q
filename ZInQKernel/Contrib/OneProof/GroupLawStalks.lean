import ZInQKernel.Contrib.OneProof.GroupLawSpread

/-!
# group-law, III: from group laws over the local rings of the base to a group law over the base

* `grpObj_of_stalkLaws`: over a base `S` with `F`, `F ×_S F`, `(F ×_S F) ×_S F` reduced, a group law on every
  `F ×_S Spec Γ(S, V)_𝔭` (`V` affine open, `𝔭` prime) with identity the base change of `e` gives a group law on
  `F` with identity `e` (spreading, `localLaw_of_stalk`, and gluing, `exists_grpObj_of_localLaws`).
* `stalkData`: the hypotheses of `MumfordGroupLaw` pass to `F ×_S Spec Γ(S, V)_𝔭`.
* `grpObj_of_isField`: over a field the group law exists outright (the fibre hypothesis at the identity point
  identifies `F` with an abelian variety).
* `field_or_dvr_localization`: for `S` smooth of relative dimension one over a field, every `Γ(S, V)_𝔭` is a field
  or a discrete valuation ring (from the fork's dimension theory of smooth schemes, `ZInQ.Contrib.Dim`, and
  `isDomain_of_maximalIdeal_eq_span`).

Mathlib and the fork's proved lemmas only.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing

namespace ZInQ.Contrib.GroupLaw

open LeafQM.AV.R1UnivRigid PkgI3

/-! ## §1 The hypotheses at a local ring, and the gluing -/

section Stalks

variable {S : Scheme.{0}} {F : Over S} {e : S ⟶ F.left} {V : S.Opens} (hV : IsAffineOpen V)
  (𝔭 : Ideal Γ(S, V)) [𝔭.IsPrime]

/-- The base change of `e` to `F ×_S Spec Γ(S, V)_𝔭`. -/
def eLoc (he : e ≫ F.hom = 𝟙 S) :
    Spec (CommRingCat.of (Localization.AtPrime 𝔭)) ⟶ ((Over.pullback (locMap hV 𝔭)).obj F).left :=
  pullback.lift (locMap hV 𝔭 ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])

theorem eLoc_sec (he : e ≫ F.hom = 𝟙 S) :
    eLoc hV 𝔭 he ≫ ((Over.pullback (locMap hV 𝔭)).obj F).hom = 𝟙 _ := pullback.lift_snd _ _ _

theorem eLoc_fst (he : e ≫ F.hom = 𝟙 S) :
    eLoc hV 𝔭 he ≫ pullback.fst F.hom (locMap hV 𝔭) = locMap hV 𝔭 ≫ e := pullback.lift_fst _ _ _

/-- **The hypotheses of `MumfordGroupLaw` at `F ×_S Spec Γ(S, V)_𝔭`.** -/
theorem stalkData [IsProper F.hom] [Smooth F.hom] [GeometricallyConnected F.hom] (he : e ≫ F.hom = 𝟙 S)
    (hfib : FibreHyp F e) :
    IsProper ((Over.pullback (locMap hV 𝔭)).obj F).hom ∧ Smooth ((Over.pullback (locMap hV 𝔭)).obj F).hom ∧
      GeometricallyConnected ((Over.pullback (locMap hV 𝔭)).obj F).hom ∧
      FibreHyp ((Over.pullback (locMap hV 𝔭)).obj F) (eLoc hV 𝔭 he) :=
  ⟨by change IsProper (pullback.snd F.hom (locMap hV 𝔭)); infer_instance,
    by change Smooth (pullback.snd F.hom (locMap hV 𝔭)); infer_instance,
    by change GeometricallyConnected (pullback.snd F.hom (locMap hV 𝔭)); infer_instance,
    fibreHyp_of_isPullback (IsPullback.of_hasPullback F.hom _) (eLoc_sec hV 𝔭 he) (eLoc_fst hV 𝔭 he) hfib⟩

variable (F e) in
/-- **The gluing.** Group laws over all `Spec Γ(S, V)_𝔭` give a group law over `S` (reduced `F`, `F ×_S F`,
`(F ×_S F) ×_S F`). -/
theorem grpObj_of_stalkLaws [IsProper F.hom] [Smooth F.hom] [IsReduced F.left] [IsReduced (F ⊗ F).left]
    [IsReduced ((F ⊗ F) ⊗ F).left] (he : e ≫ F.hom = 𝟙 S) (hfib : FibreHyp F e)
    (hst : ∀ (V : S.Opens) (hV : IsAffineOpen V) (𝔭 : Ideal Γ(S, V)) [𝔭.IsPrime],
      ∃ _G : GrpObj ((Over.pullback (locMap hV 𝔭)).obj F),
        η[(Over.pullback (locMap hV 𝔭)).obj F].left = eLoc hV 𝔭 he) :
    ∃ _G : GrpObj F, η[F].left = e := by
  have hloc : ∀ s : S, ∃ L : LocalLaw F e, s ∈ Set.range L.j := by
    intro s
    obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := s) trivial
    let x : V := ⟨s, hsV⟩
    obtain ⟨G, hη⟩ := hst V hV (hV.primeIdealOf x).asIdeal
    obtain ⟨L, hL⟩ := localLaw_of_stalk hV (hV.primeIdealOf x).asIdeal he G
      (by rw [hη]; exact eLoc_fst hV _ he)
    refine ⟨L, ?_⟩
    have : hV.fromSpec (⟨(hV.primeIdealOf x).asIdeal, inferInstance⟩ : PrimeSpectrum Γ(S, V)) = s :=
      hV.fromSpec_primeIdealOf x
    rw [← this]
    exact hL
  choose L hL using hloc
  exact exists_grpObj_of_localLaws L hL he hfib

end Stalks

/-! ## §2 Over a field -/

/-- **Over a field the group law exists outright**: the fibre at the identity point of `Spec R` is `F` itself. -/
theorem grpObj_of_isField (R : Type) [CommRing R] (hR : IsField R) (F : Over (Spec (CommRingCat.of R)))
    (e : Spec (CommRingCat.of R) ⟶ F.left) (hfib : FibreHyp F e) : ∃ _G : GrpObj F, η[F].left = e := by
  letI : Field R := hR.toField
  obtain ⟨A, g, hpb, h1⟩ := hfib R (𝟙 _)
  haveI : IsIso g := hpb.isIso_fst_of_isIso
  let φ : A.X ≅ F := Over.isoMk (asIso g) (by simpa using hpb.w)
  refine ⟨GrpObj.ofIso φ, ?_⟩
  have h2 := one_pt0_comp g _ h1
  change (toUnit (pt0 R) ≫ η[A.X]).left ≫ g = _ at h2
  rw [Over.comp_left, Over.toUnit_left] at h2
  simp only [Over.mk_hom, Category.id_comp] at h2
  change (η[A.X] ≫ φ.hom).left = e
  rw [Over.comp_left]
  exact h2

/-! ## §3 Local rings of a smooth curve -/

/-- A reduced noetherian local ring that is not a field and whose maximal ideal is principal is a domain. -/
theorem isDomain_of_maximalIdeal_eq_span {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [_root_.IsReduced R] (hR : ¬ IsField R) (π : R) (hπ : maximalIdeal R = Ideal.span {π}) : IsDomain R := by
  have hπn : ∀ n : ℕ, π ^ n ≠ 0 := by
    intro n hn
    have h0 : π = 0 := IsNilpotent.eq_zero ⟨n, hn⟩
    apply hR
    rw [isField_iff_maximalIdeal_eq, hπ, h0, Ideal.span_singleton_eq_bot]
  have hpow : ∀ n : ℕ, maximalIdeal R ^ n = Ideal.span {π ^ n} := fun n => by
    rw [hπ, Ideal.span_singleton_pow]
  have key : ∀ x : R, x ≠ 0 → ∃ (u : R) (n : ℕ), IsUnit u ∧ x = u * π ^ n := by
    intro x hx
    have hinf := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
    have hex : ∃ n : ℕ, x ∉ maximalIdeal R ^ n := by
      by_contra h
      push Not at h
      apply hx
      have : x ∈ ⨅ n : ℕ, maximalIdeal R ^ n := by rw [Submodule.mem_iInf]; exact h
      rwa [hinf, Submodule.mem_bot] at this
    classical
    let n := Nat.find hex
    have hn : x ∉ maximalIdeal R ^ n := Nat.find_spec hex
    have hn0 : n ≠ 0 := by
      intro h0
      apply hn
      rw [h0, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hxm : x ∈ maximalIdeal R ^ m := by
      by_contra h
      have := Nat.find_min' hex h
      omega
    rw [hpow, Ideal.mem_span_singleton'] at hxm
    obtain ⟨a, ha⟩ := hxm
    refine ⟨a, m, ?_, ha.symm⟩
    by_contra hau
    have ham : a ∈ maximalIdeal R := (mem_maximalIdeal a).mpr hau
    rw [hπ, Ideal.mem_span_singleton'] at ham
    obtain ⟨b, hb⟩ := ham
    apply hn
    rw [hm, hpow, Ideal.mem_span_singleton']
    exact ⟨b, by rw [← ha, ← hb, pow_succ]; ring⟩
  haveI : Nontrivial R := inferInstance
  haveI : NoZeroDivisors R := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_contra h
    push Not at h
    obtain ⟨u, n, hu, rfl⟩ := key x h.1
    obtain ⟨v, m, hv, rfl⟩ := key y h.2
    have : (u * v) * π ^ (n + m) = 0 := by rw [← hxy]; ring
    exact hπn (n + m) ((hu.mul hv).mul_right_eq_zero.mp this)
  exact NoZeroDivisors.to_isDomain R

/-- **The local rings of a smooth curve over a field are fields or discrete valuation rings.** -/
theorem stalk_field_or_dvr {k : Type} [Field k] {S : Scheme.{0}} (p : S ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 1 p] [IsLocallyNoetherian S] (s : S) :
    IsField (S.presheaf.stalk s) ∨
      ∃ _ : IsDomain (S.presheaf.stalk s), IsDiscreteValuationRing (S.presheaf.stalk s) := by
  haveI : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  haveI : IsReduced S := isReduced_of_smooth p
  by_cases hs : IsClosed ({s} : Set S)
  · obtain ⟨hdim, hspan⟩ := ZInQ.Contrib.Dim.ringKrullDim_stalk_of_smoothOfRelativeDimension p 1 s hs
    right
    have hnf : ¬ IsField (S.presheaf.stalk s) := by
      intro hF
      have := ringKrullDim_eq_zero_of_isField hF
      rw [this] at hdim
      norm_num at hdim
    obtain ⟨⟨⟨π, hπ⟩⟩, -⟩ := (Submodule.spanFinrank_eq_one_iff _).mp hspan
    haveI := isDomain_of_maximalIdeal_eq_span hnf π hπ
    have hP : (maximalIdeal (S.presheaf.stalk s)).IsPrincipal := ⟨⟨π, hπ⟩⟩
    exact ⟨inferInstance, ((IsDiscreteValuationRing.TFAE _ hnf).out 5 1).mp hP⟩
  · left
    haveI : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace p
    obtain ⟨t, ht, htc⟩ := nonempty_inter_closedPoints (Z := closure {s}) ⟨s, subset_closure rfl⟩
      isClosed_closure.isLocallyClosed
    have htc' : IsClosed ({t} : Set S) := htc
    have hts : t ≠ s := fun h => hs (h ▸ htc')
    have hlt : t < s := by
      refine ⟨specializes_iff_mem_closure.mpr ht, fun h => hts ?_⟩
      have := specializes_iff_mem_closure.mp h
      rw [htc'.closure_eq] at this
      exact (Set.mem_singleton_iff.mp this).symm
    have h1 := (ZInQ.Contrib.Dim.ringKrullDim_stalk_of_smoothOfRelativeDimension p 1 t htc').1
    rw [ringKrullDim_stalk_eq_coheight] at h1
    have h1' : Order.coheight t = 1 := by exact_mod_cast h1
    have h2 := Order.coheight_add_one_le hlt
    rw [h1'] at h2
    have h3 : Order.coheight s ≤ 0 := by
      have : Order.coheight s + 1 ≤ 0 + 1 := by simpa using h2
      exact (ENat.add_le_add_iff_right (by simp)).mp this
    haveI : Ring.KrullDimLE 0 (S.presheaf.stalk s) := krullDimLE_of_coheight_le (by exact_mod_cast h3)
    exact Ring.KrullDimLE.isField_of_isReduced

/-- **`Γ(S, V)_𝔭` is a field or a discrete valuation ring** for `S` smooth of relative dimension one over a
field (transport from the stalk, a localization of `Γ(S, V)` at `𝔭`). -/
theorem field_or_dvr_localization {k : Type} [Field k] {S : Scheme.{0}} (p : S ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 1 p] [IsLocallyNoetherian S] {V : S.Opens} (hV : IsAffineOpen V)
    (𝔭 : Ideal Γ(S, V)) [𝔭.IsPrime] :
    IsField (Localization.AtPrime 𝔭) ∨
      ∃ _ : IsDomain (Localization.AtPrime 𝔭), IsDiscreteValuationRing (Localization.AtPrime 𝔭) := by
  let y : PrimeSpectrum Γ(S, V) := ⟨𝔭, inferInstance⟩
  have hy : hV.fromSpec y ∈ V := by
    have h := hV.range_fromSpec
    have : hV.fromSpec y ∈ Set.range hV.fromSpec := Set.mem_range_self _
    rw [h] at this
    exact this
  letI : Algebra Γ(S, V) (S.presheaf.stalk (hV.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨hV.fromSpec y, hy⟩
  haveI : IsLocalization.AtPrime (S.presheaf.stalk (hV.fromSpec y)) 𝔭 := hV.isLocalization_stalk' y hy
  let φ : Localization.AtPrime 𝔭 ≃+* S.presheaf.stalk (hV.fromSpec y) :=
    (IsLocalization.algEquiv 𝔭.primeCompl (Localization.AtPrime 𝔭) _).toRingEquiv
  rcases stalk_field_or_dvr p (hV.fromSpec y) with hF | ⟨hD, hDVR⟩
  · exact Or.inl (MulEquiv.isField hF φ.toMulEquiv)
  · right
    haveI := hD
    haveI : IsDomain (Localization.AtPrime 𝔭) := φ.toMulEquiv.isDomain _
    exact ⟨inferInstance, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing φ.symm⟩

end ZInQ.Contrib.GroupLaw

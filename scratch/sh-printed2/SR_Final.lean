/-! ## Final: the three strict-henselization leaves from the single Néron leaf -/

namespace ShRoute

open ReductSplit ReductGlue

/-- **`StrictHenselizationNeron` (char 0, perfect residue field) from `NeronBaseChangeSH`.** -/
theorem strictHenselizationNeron0_final (hN : NeronBaseChangeSH) : StrictHenselizationNeron0 :=
  strictHenselizationNeron0_of hN shExists0

/-- **`StrictHenselizationPair` (char 0, perfect residue field) from `NeronBaseChangeSH`.** -/
theorem strictHenselizationPair0_final (hN : NeronBaseChangeSH) : StrictHenselizationPair0 :=
  strictHenselizationPair0_of hN shPair0

/-- **`StrictHenselizationInside` (char 0, perfect residue field) from `NeronBaseChangeSH`.** -/
theorem strictHenselizationInside0_final (hN : NeronBaseChangeSH) : StrictHenselizationInside0 :=
  strictHenselizationInside0_of hN shInside0

/-- **The route**: the general-DVR SGA 7 IX leaves 4.7, 3.3 (first assertion) and 3.5, for `K` of
characteristic 0 with perfect residue field, from their strictly henselian forms, the bundle leaf
`MulEtaleAbelianScheme` and the one Néron leaf `NeronBaseChangeSH`. -/
theorem route_final (hR : RaynaudSemistableSH) (hP : SemistablePersistsSH)
    (hU : SemistableUnipotentSH) (hE : AvSplit.T4.MulEtaleAbelianScheme)
    (hN : NeronBaseChangeSH) :
    RaynaudSemistable0 ∧ SemistablePersistsDVR0 ∧ SemistableUnipotent0 :=
  ⟨raynaudSemistable0_of hR (strictHenselizationNeron0_final hN) hE,
   semistablePersistsDVR0_of hP (strictHenselizationPair0_final hN),
   semistableUnipotent0_of hU (strictHenselizationInside0_final hN)⟩

/-! ### Sanity checks: the new statements are no stronger than the old ones -/

/-- The Néron leaf is a specialization of reduct-glue's `NeronBaseChangeUnramifiedDVR` (the general
BLR §7.2 Thm. 1 form: ramification index 1, separable residue extension). -/
theorem neronBaseChangeSH_of_unramified (h : NeronBaseChangeUnramifiedDVR) : NeronBaseChangeSH := by
  intro K _ _ O _ K₁ _ _ O₁ hO hU A 𝒩 h𝒩
  obtain ⟨hSH, halg, hunr, hsep⟩ := hU
  haveI : IsDiscreteValuationRing O₁ := hSH.1
  haveI := halg
  haveI : Algebra.IsSeparable K K₁ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact h K O K₁ O₁ hO inferInstance hunr hsep A 𝒩 h𝒩

/-- Each char-0 leaf is a specialization of reduct-glue's leaf (same statement, two added
hypotheses). -/
theorem char0_of_general :
    (StrictHenselizationNeron → StrictHenselizationNeron0) ∧
    (StrictHenselizationPair → StrictHenselizationPair0) ∧
    (StrictHenselizationInside → StrictHenselizationInside0) ∧
    (RaynaudSemistable → RaynaudSemistable0) ∧
    (SemistablePersistsDVR → SemistablePersistsDVR0) ∧
    (SemistableUnipotent → SemistableUnipotent0) :=
  ⟨fun h K _ _ O _ _ => h K O, fun h K _ _ O _ _ => h K O, fun h K _ _ O _ _ => h K O,
   fun h K _ _ O _ _ => h K O, fun h K _ _ O _ _ => h K O, fun h K _ _ O _ _ => h K O⟩

end ShRoute

#print axioms ShRoute.key_finite
#print axioms ShRoute.henselian_wE
#print axioms ShRoute.isSepClosed_wE
#print axioms ShRoute.isDVR_wE
#print axioms ShRoute.res_isAlgebraic
#print axioms ShRoute.shExists0
#print axioms ShRoute.shInside0
#print axioms ShRoute.shPair0
#print axioms ShRoute.strictHenselizationNeron0_final
#print axioms ShRoute.strictHenselizationPair0_final
#print axioms ShRoute.strictHenselizationInside0_final
#print axioms ShRoute.route_final
#print axioms ShRoute.neronBaseChangeSH_of_unramified
#print axioms ShRoute.char0_of_general

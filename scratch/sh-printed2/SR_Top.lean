/-!
# sh-route, top level: the three strict-henselization leaves of reduct-glue from one Néron leaf
# and commutative algebra

Task sh-route (2026-11-14). Namespace `ShRoute`. Appended after `ReductGlue.lean` (a verbatim copy of
`scratch/reduct-glue/ReductGlue.lean` = `Base.lean` + `Body.lean`), so the reduct-glue statements are
used, never restated.

* `IsSHUnram O O₁ hO`: `O₁ ⊇ O` is a strictly henselian DVR, `K₁/K` algebraic, a uniformizer of `O`
  stays a uniformizer of `O₁` (ramification index 1), and `κ(O₁)/κ(O)` is separable.
* LEAF `NeronBaseChangeSH` (BLR, *Néron models*, §7.2 Thm. 1 / §1.2 Prop. 2; UNVERIFIED): Néron models
  base change along such `O → O₁`. In characteristic 0 these hypotheses force `O₁ ≅ O^sh` (see the
  report), so the leaf is the print's "Néron models commute with strict henselization".
* commutative algebra (GLUE, proved in `CA.lean` or named here): `SHExists0`, `SHInside0`, `SHPair0`.
* the three reduct-glue leaves in characteristic 0 with perfect residue field
  (`StrictHenselizationNeron0`, `StrictHenselizationPair0`, `StrictHenselizationInside0`: the
  verbatim statements with the two hypotheses `[CharZero K]`, `[PerfectField κ(O)]` added) are
  theorems from these;
* the resulting char-0 forms of reduct-glue's general-DVR leaves: `RaynaudSemistable0`,
  `SemistablePersistsDVR0`, `SemistableUnipotent0`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety Pts torsion galAct IsInertia UnipSq HasGoodReduction)
open ReductSplit ReductGlue
set_option linter.style.haveILetI false

namespace ShRoute

/-- `O₁ ⊇ O` is an unramified strictly henselian extension: `O₁` is a strictly henselian DVR,
`K₁/K` is algebraic, a uniformizer of `O` is a uniformizer of `O₁`, and the residue extension is
separable. (In characteristic 0 this characterizes the strict henselization of `O`; see the report.) -/
def IsSHUnram {K K₁ : Type} [Field K] [Field K₁] [Algebra K K₁] (O : ValuationSubring K)
    (O₁ : ValuationSubring K₁) (hO : O₁.comap (algebraMap K K₁) = O) : Prop :=
  IsStrictlyHenselianDVR O₁ ∧ Algebra.IsAlgebraic K K₁ ∧
    (∀ ϖ : O, Irreducible ϖ → Irreducible (comapHom hO ϖ)) ∧
    (letI := (resMap hO).toAlgebra
     Algebra.IsSeparable (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O₁))

/-- **LEAF `NeronBaseChangeSH`** (Néron models commute with strict henselization:
Bosch–Lütkebohmert–Raynaud, *Néron models*, §7.2 Thm. 1 and §1.2 Prop. 2; numbers UNVERIFIED). `K` of
characteristic 0, `O ⊆ K` a DVR, `O₁ ⊇ O` an unramified strictly henselian extension with `K₁/K`
algebraic (`IsSHUnram`); then the base change of a Néron model of `A` over `O` is a Néron model of
`A_{K₁}` over `O₁`. In characteristic 0 the hypotheses force `O → O₁` to be (isomorphic over `O` to)
the strict henselization `O → O^sh` (report §3), so this is the printed statement for `O^sh`. -/
def NeronBaseChangeSH : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K₁ : Type) [Field K₁] [Algebra K K₁] (O₁ : ValuationSubring K₁)
    (hO : O₁.comap (algebraMap K K₁) = O), IsSHUnram O O₁ hO →
    ∀ (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O), 𝒩.IsNeronModel → (bcDVR hO 𝒩).IsNeronModel

theorem isSHNeronExt_of (hN : NeronBaseChangeSH) {K K₁ : Type} [Field K] [CharZero K] [Field K₁]
    [Algebra K K₁] {O : ValuationSubring K} [IsDiscreteValuationRing O] {O₁ : ValuationSubring K₁}
    {hO : O₁.comap (algebraMap K K₁) = O} (h : IsSHUnram O O₁ hO) : IsSHNeronExt O O₁ hO := by
  refine ⟨h.1, ?_, hN K O K₁ O₁ hO h⟩
  letI := (resMap hO).toAlgebra
  have := h.2.2.2
  exact Algebra.IsSeparable.isAlgebraic _ _

/-! ## The commutative algebra (GLUE; proved in `CA.lean`, see the report) -/

/-- **GLUE `SHExists0`** (existence of the strict henselization of a DVR as an unramified strictly
henselian extension: EGA IV₄ 18.8.8/18.8.13; here built as the valuation ring of the inertia field in
an algebraic closure). -/
def SHExists0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)],
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (O' : ValuationSubring K')
      (hO : O'.comap (algebraMap K K') = O), IsSHUnram O O' hO

/-- **GLUE `SHInside0`** (the valuation ring of the inertia field of `w` in an algebraic closure is
an unramified strictly henselian extension of `O`, and the inertia group of `w` fixes the inertia
field). -/
def SHInside0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O →
    ∃ (E : IntermediateField K Ω) (hE : (w.comap (algebraMap E Ω)).comap (algebraMap K E) = O),
      IsSHUnram O (w.comap (algebraMap E Ω)) hE ∧
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → ∀ x ∈ E, σ x = x

/-- **GLUE `SHPair0`** (strict henselizations nest along a finite extension: for `O' ⊆ K'` over
`O ⊆ K` with `K'/K` finite, unramified strictly henselian extensions `P ⊇ O`, `P' ⊇ O'` with
`E'/E` finite and `P'` over `P`; here the inertia fields of one valuation ring `w` of an algebraic
closure of `K'`, over `K` and over `K'`). -/
def SHPair0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'] (hO : O'.comap (algebraMap K K') = O),
    ∃ (E E' : Type) (_ : Field E) (_ : Field E') (_ : Algebra K E) (_ : Algebra K' E')
      (_ : Algebra E E') (_ : Algebra K E') (_ : IsScalarTower K E E') (_ : IsScalarTower K K' E')
      (_ : FiniteDimensional E E') (P : ValuationSubring E) (P' : ValuationSubring E')
      (hP : P.comap (algebraMap K E) = O) (hP' : P'.comap (algebraMap K' E') = O'),
      IsSHUnram O P hP ∧ IsSHUnram O' P' hP' ∧ P'.comap (algebraMap E E') = P

/-! ## The three reduct-glue leaves in characteristic 0 (verbatim plus `[CharZero K]`,
`[PerfectField κ(O)]`) -/

/-- `StrictHenselizationNeron` (reduct-glue) for `K` of characteristic 0 with perfect residue field. -/
def StrictHenselizationNeron0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)],
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (O' : ValuationSubring K')
      (hO : O'.comap (algebraMap K K') = O),
      IsStrictlyHenselianDVR O' ∧
      (letI := (resMap hO).toAlgebra
       Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')) ∧
      ∀ (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O), 𝒩.IsNeronModel → (bcDVR hO 𝒩).IsNeronModel

/-- `StrictHenselizationPair` (reduct-glue) for `K` of characteristic 0 with perfect residue
field. -/
def StrictHenselizationPair0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'] (hO : O'.comap (algebraMap K K') = O),
    ∃ (E E' : Type) (_ : Field E) (_ : Field E') (_ : Algebra K E) (_ : Algebra K' E')
      (_ : Algebra E E') (_ : Algebra K E') (_ : IsScalarTower K E E') (_ : IsScalarTower K K' E')
      (_ : FiniteDimensional E E') (P : ValuationSubring E) (P' : ValuationSubring E')
      (hP : P.comap (algebraMap K E) = O) (hP' : P'.comap (algebraMap K' E') = O'),
      IsSHNeronExt O P hP ∧ IsSHNeronExt O' P' hP' ∧ P'.comap (algebraMap E E') = P

/-- `StrictHenselizationInside` (reduct-glue) for `K` of characteristic 0 with perfect residue
field. -/
def StrictHenselizationInside0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O →
    ∃ (E : IntermediateField K Ω) (hE : (w.comap (algebraMap E Ω)).comap (algebraMap K E) = O),
      IsSHNeronExt O (w.comap (algebraMap E Ω)) hE ∧
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → ∀ x ∈ E, σ x = x

theorem strictHenselizationNeron0_of (hN : NeronBaseChangeSH) (hC : SHExists0) :
    StrictHenselizationNeron0 := by
  intro K _ _ O _ _
  obtain ⟨K', _, _, O', hO, h⟩ := hC K O
  exact ⟨K', inferInstance, inferInstance, O', hO, isSHNeronExt_of hN h⟩

theorem strictHenselizationPair0_of (hN : NeronBaseChangeSH) (hC : SHPair0) :
    StrictHenselizationPair0 := by
  intro K _ _ O _ _ K' _ _ _ O' _ hO
  obtain ⟨E, E', _, _, _, _, _, _, _, _, _, P, P', hP, hP', h1, h2, h3⟩ := hC K O K' O' hO
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  exact ⟨E, E', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, P, P', hP, hP',
    isSHNeronExt_of hN h1, isSHNeronExt_of hN h2, h3⟩

theorem strictHenselizationInside0_of (hN : NeronBaseChangeSH) (hC : SHInside0) :
    StrictHenselizationInside0 := by
  intro K _ _ O _ _ Ω _ _ _ w hw
  obtain ⟨E, hE, h, hfix⟩ := hC K O Ω w hw
  exact ⟨E, hE, isSHNeronExt_of hN h, hfix⟩

/-! ## The general-DVR leaves of reduct-glue in characteristic 0 -/

/-- `RaynaudSemistable` (reduct-split; SGA 7 IX 4.7) for `K` of characteristic 0 with perfect
residue field. -/
def RaynaudSemistable0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)] (A : PkgI3.AbVar K)
    (m : ℕ), 3 ≤ m → IsUnit (m : O) →
    (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
    SemistableNeronModels A O

/-- `SemistablePersistsDVR` (reduct-split; SGA 7 IX 3.3, first assertion) for `K` of
characteristic 0 with perfect residue field. -/
def SemistablePersistsDVR0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'], O'.comap (algebraMap K K') = O →
    ∀ A : PkgI3.AbVar K, HasSemistableReduction A O → SemistableNeronModels (A.baseChange K') O'

/-- `SemistableUnipotent` (reduct-split; SGA 7 IX 3.5) for `K` of characteristic 0 with perfect
residue field. -/
def SemistableUnipotent0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0

open ZInQ.Contrib.AbVarBC in
/-- **SGA 7 IX 4.7 over a DVR of a characteristic-0 field from its strictly henselian form**: the
proof of reduct-glue's `raynaudSemistable_of_SH'`, with `StrictHenselizationNeron0`. -/
theorem raynaudSemistable0_of (hR : RaynaudSemistableSH) (hSN : StrictHenselizationNeron0)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : RaynaudSemistable0 := by
  intro K _ _ O _ _ A m hm3 hmu htors 𝒩 h𝒩
  obtain ⟨K', _, _, O', hO, hSH, halg, hbc⟩ := hSN K O
  haveI : IsDiscreteValuationRing O' := hSH.1
  have hmu' : IsUnit (m : O') := by
    have := hmu.map (comapHom hO)
    rwa [map_natCast] at this
  rw [isSemistable_bcDVR_iff hO halg]
  refine hR K' O' hSH (A.baseChange K') m hm3 hmu' ?_ _ (hbc A 𝒩 h𝒩)
  intro x hx
  have hmK : (m : K) ≠ 0 := natCast_ne_zero_of_isUnit O hmu
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K' := IsAlgClosed.lift
  obtain ⟨p, hp, hpx⟩ := torsion_descends_etale hE A κ m hmK x hx
  obtain ⟨z, hz⟩ := htors p hp
  refine ⟨(bcPt A K').symm (extPt A (Algebra.ofId K K') z), ?_⟩
  rw [← hpx, ← hz]
  apply (bcPt A (AlgebraicClosure K')).injective
  rw [MulEquiv.apply_symm_apply, bcPt_extPt, MulEquiv.apply_symm_apply, extPt_extPt, extPt_extPt]
  congr 1
  ext a
  simp

/-- **SGA 7 IX 3.3 (first assertion) over a DVR of a characteristic-0 field from the strictly
henselian form**: the proof of reduct-glue's `persistsFromSH_of`, with `StrictHenselizationPair0`. -/
theorem semistablePersistsDVR0_of (hSH : SemistablePersistsSH) (hPair : StrictHenselizationPair0) :
    SemistablePersistsDVR0 := by
  intro K _ _ O _ _ K' _ _ _ O' _ hO A hA 𝒩' h𝒩'
  obtain ⟨E, E', _, _, _, _, _, _, _, _, _, P, P', hP, hP', ⟨hSHP, halgP, hbcP⟩,
    ⟨hSHP', halgP', hbcP'⟩, hPP'⟩ := hPair K O K' O' hO
  haveI : IsDiscreteValuationRing P := hSHP.1
  haveI : IsDiscreteValuationRing P' := hSHP'.1
  have hAE : HasSemistableReduction (A.baseChange E) P := by
    obtain ⟨𝒩, h𝒩, hs⟩ := hA
    exact ⟨bcDVR hP 𝒩, hbcP A 𝒩 h𝒩, (isSemistable_bcDVR_iff hP halgP 𝒩).mp hs⟩
  have h1 : SemistableNeronModels ((A.baseChange E).baseChange E') P' :=
    hSH E P hSHP E' P' hPP' (A.baseChange E) hAE
  have he : IsMonHom (bcbcIso A E E' ≪≫ (bcbcIso A K' E').symm).hom := by
    haveI := bcbcIso_isMonHom A E E'
    have : IsMonHom (bcbcIso A K' E').inv := by
      haveI := bcbcIso_isMonHom A K' E'
      infer_instance
    exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ (bcbcIso_isMonHom A E E') this
  have h2 : SemistableNeronModels ((A.baseChange K').baseChange E') P' :=
    semistableNeronModels_transport (bcbcIso A E E' ≪≫ (bcbcIso A K' E').symm) he h1
  rw [isSemistable_bcDVR_iff hP' halgP']
  exact h2 _ (hbcP' (A.baseChange K') 𝒩' h𝒩')

/-- **SGA 7 IX 3.5 over a DVR of a characteristic-0 field from the strictly henselian form**:
reduct-glue's `unipotentFromSH_of` applied through `StrictHenselizationInside0`. -/
theorem semistableUnipotent0_of (hSH : SemistableUnipotentSH) (hIn : StrictHenselizationInside0) :
    SemistableUnipotent0 := by
  intro K _ _ O _ _ Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t
  obtain ⟨E, hE, ⟨hSHP, halg, hbc⟩, hfix⟩ := hIn K O Ω w hw
  haveI : IsDiscreteValuationRing (w.comap (algebraMap E Ω)) := hSHP.1
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) E⟩
  have hAE : HasSemistableReduction (A.baseChange E) (w.comap (algebraMap E Ω)) := by
    obtain ⟨𝒩, h𝒩, hs⟩ := hA
    exact ⟨bcDVR hE 𝒩, hbc A 𝒩 h𝒩, (isSemistable_bcDVR_iff hE halg 𝒩).mp hs⟩
  have hℓP : IsUnit (ℓ : w.comap (algebraMap E Ω)) := by
    have := hℓ.map (comapHom hE)
    rwa [map_natCast] at this
  let σ₁ := toE E σ (hfix σ hσ)
  have hσ₁ : IsInertia w σ₁ := isInertia_toE E w σ (hfix σ hσ) hσ
  let φ : TΩ (A.baseChange E) Ω ℓ →ₗ[ℤ_[ℓ]] TΩ A Ω ℓ :=
    PkgI3.Tate.map (MonoidHom.toAdditive (ZInQ.Contrib.AbVarBC.bcPt A Ω).toMonoidHom)
  let ψ : TΩ A Ω ℓ →ₗ[ℤ_[ℓ]] TΩ (A.baseChange E) Ω ℓ :=
    PkgI3.Tate.map (MonoidHom.toAdditive (ZInQ.Contrib.AbVarBC.bcPt A Ω).symm.toMonoidHom)
  have hφψ : φ (ψ t) = t := by
    apply Subtype.ext
    funext n
    change Additive.ofMul (ZInQ.Contrib.AbVarBC.bcPt A Ω ((ZInQ.Contrib.AbVarBC.bcPt A Ω).symm
      (Additive.toMul (t.1 n)))) = t.1 n
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hcomm : ∀ s, φ (galTΩ (A.baseChange E) ℓ σ₁ s) = galTΩ A ℓ σ (φ s) := by
    intro s
    apply Subtype.ext
    funext n
    change Additive.ofMul (ZInQ.Contrib.AbVarBC.bcPt A Ω ((A.baseChange E).galAct σ₁
      (Additive.toMul (s.1 n)))) =
      Additive.ofMul (A.galAct σ (ZInQ.Contrib.AbVarBC.bcPt A Ω (Additive.toMul (s.1 n))))
    rw [ZInQ.Contrib.AbVarBC.bcPt_galAct, toE_restrictScalars]
  have key := hSH E (w.comap (algebraMap E Ω)) hSHP Ω w rfl (A.baseChange E) hAE ℓ hℓP σ₁ hσ₁
    (ψ t)
  have := congrArg φ key
  simp only [map_add, map_sub, map_nsmul, map_zero, hcomm, hφψ] at this
  exact this

/-- **The route, assembled**: the char-0 general-DVR leaves 4.7, 3.3a, 3.5 from the printed
(strictly henselian) SGA 7 leaves, the bundle leaf `MulEtaleAbelianScheme`, the Néron leaf
`NeronBaseChangeSH` and the commutative algebra. -/
theorem route (hR : RaynaudSemistableSH) (hP : SemistablePersistsSH)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) (hN : NeronBaseChangeSH) (hC : SHExists0)
    (hC2 : SHPair0) : RaynaudSemistable0 ∧ SemistablePersistsDVR0 :=
  ⟨raynaudSemistable0_of hR (strictHenselizationNeron0_of hN hC) hE,
   semistablePersistsDVR0_of hP (strictHenselizationPair0_of hN hC2)⟩

end ShRoute

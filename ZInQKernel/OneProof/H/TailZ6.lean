import ZInQKernel.OneProof.H.TailZ5

/-! # OneProof H, leaf-fold9 (bundles): `sixContactMin_of_open9`

First, modular-split's `scratch/modular-split/R15.lean` verbatim after its two import lines (`#print` dropped):
`ModularSplit.deligneSerreConseq_of_ds : DSThm966 → HDec.HSyn.DeligneSerreConseq` (row r15 from Deligne–Serre's
printed theorem, already the field `dsThm966`). Then the bundles `OpenResearchLeaves9`, `OpenTextbookLeaves9`, the
maps to leaf-fold8's bundles and `sixContactMin_of_open9`. -/

/-! # modular-split, row r15: `DeligneSerreConseq` from Deligne–Serre's printed theorem

The row (bundle field `r15 : DeligneSerreConseq`, `ZInQKernel/OneProof/H/LPrefix.lean`, namespace
`HSyn`) is imported, not copied. It is proved from `DSThm966` alone (Deligne–Serre 1974 Thm 4.1 in
Diamond–Shurman's form, `ZInQKernel/OneProof/H/TailS.lean`, already a published-form LEAF of the
bundle, field `dsThm966`), the kernel's proved T18 (Chebotarev density) and T19 (Brauer–Nesbitt)
through hodge-split's proved `attachedConj_proof`, and the specialization argument of
hodge-split's `artinTransport_proof` (copied below, keeping the finiteness of the image that the
original drops). This is Deligne–Serre's Lemma 3.2 route, read by the locator audit (row R15). -/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

namespace ModularSplit

open ZInQ.Contrib.HodgeSplit ZInQ.Contrib.G9.PkgI4

/-- **GLUE, proved: an Artin representation as an `ℓ`-adic one, keeping the finite image.**
hodge-split's `artinTransport_proof` (`TailT.lean` §17), verbatim up to the last step, which here
returns the finiteness of the image. -/
theorem artinTransport_finite (hDS : DSThm966) (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) (N : ℕ) (χ : DirichletCharacter ℂ N) (g : CF N 1)
    (hN : 0 < N) (hg : IsNormalizedEigenform g χ) :
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g ∧ (Set.range ρ.toHom).Finite := by
  classical
  obtain ⟨ρc, hcont, hfin, hloc⟩ := hDS N χ g hN hg
  let E : Set ℂ := ⋃ M ∈ Set.range ρc,
    Set.range fun ij : Fin 2 × Fin 2 => (M : Matrix (Fin 2) (Fin 2) ℂ) ij.1 ij.2
  haveI : Finite E := (hfin.biUnion fun M _ => Set.finite_range _).to_subtype
  have hmem : ∀ σ i j, (ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j ∈ genRing ιC E := fun σ i j =>
    mem_genRing_of_mem ιC (Set.mem_biUnion (Set.mem_range_self σ) ⟨(i, j), rfl⟩)
  obtain ⟨φ, hφ⟩ := exists_specialization ιC E
  let ρA := liftGLSub (genRing ιC E) ρc hmem
  let g' : genRing ιC E →+* PadicAlgCl ℓ := ιL.toRingHom.comp φ
  let ρh : GQ →* GL (Fin 2) (PadicAlgCl ℓ) := (Matrix.GeneralLinearGroup.map g').comp ρA
  have hentry : ∀ σ i j, (ρh σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) i j =
      g' ⟨(ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j, hmem σ i j⟩ := fun _ _ _ => rfl
  have hker : ∀ σ, ρc σ = 1 → ρh σ = 1 := by
    intro σ h
    apply Units.ext
    ext i j
    rw [hentry]
    have hval : (ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j = if i = j then 1 else 0 := by
      rw [h, Units.val_one, Matrix.one_apply]
    by_cases hij : i = j
    · have : (⟨(ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j, hmem σ i j⟩ : genRing ιC E) = 1 :=
        Subtype.ext (by change (ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j = 1; rw [hval, if_pos hij])
      rw [this, map_one, Units.val_one, Matrix.one_apply, if_pos hij]
    · have : (⟨(ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j, hmem σ i j⟩ : genRing ιC E) = 0 :=
        Subtype.ext (by change (ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j = 0; rw [hval, if_neg hij])
      rw [this, map_zero, Units.val_one, Matrix.one_apply, if_neg hij]
  have hopen : IsOpen (ρc.ker : Set GQ) := by
    have hcl : IsClosed (ρc.ker : Set GQ) := by
      have : (ρc.ker : Set GQ) = ρc ⁻¹' {1} := by ext; simp
      rw [this]; exact isClosed_singleton.preimage hcont
    haveI : Finite ρc.range := by
      have : (ρc.range : Set (GL (Fin 2) ℂ)) = Set.range ρc := MonoidHom.coe_range ρc
      exact Set.Finite.to_subtype (this ▸ hfin)
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl
  have hρhc : Continuous ρh := by
    refine continuous_of_continuousAt_one _ ?_
    rw [ContinuousAt, map_one]
    exact tendsto_nhds_of_eventually_eq
      (Filter.mem_of_superset (hopen.mem_nhds ρc.ker.one_mem) fun σ hσ => hker σ hσ)
  have hdep : ∀ σ σ', ρc σ = ρc σ' → ρh σ = ρh σ' := by
    intro σ σ' h
    have h1 : ρc (σ⁻¹ * σ') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := hker _ h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have hρfin : (Set.range ρh).Finite := by
    refine (hfin.image fun M => ρh (Function.invFun ρc M)).subset ?_
    rintro _ ⟨σ, rfl⟩
    refine ⟨ρc σ, ⟨σ, rfl⟩, hdep _ _ ?_⟩
    exact Function.invFun_eq ⟨σ, rfl⟩
  let ρ : GaloisRep ℓ 2 := ⟨ρh, hρhc⟩
  refine ⟨ρ, isSemisimple_of_finite_range ρ hρfin, ?_, hρfin⟩
  intro p hp hpNl
  have hpN : ¬ p ∣ N := fun h => hpNl (Dvd.dvd.mul_right h ℓ)
  obtain ⟨hun, hfr⟩ := hloc p hp hpN
  refine ⟨fun v hv σ hσ => hker _ (hun v hv σ hσ), ?_⟩
  obtain ⟨v₀, τ₀, hv₀, hτ₀⟩ := exists_arithFrob p hp
  have htr₀ := (hfr v₀ τ₀ hv₀ hτ₀).1
  -- `ρc τ₀` has finite order
  haveI : Finite ρc.range := by
    have : (ρc.range : Set (GL (Fin 2) ℂ)) = Set.range ρc := MonoidHom.coe_range ρc
    exact Set.Finite.to_subtype (this ▸ hfin)
  let x : ρc.range := ⟨ρc τ₀, τ₀, rfl⟩
  have hx : IsOfFinOrder x := isOfFinOrder_of_finite x
  have hn : orderOf x ≠ 0 := hx.orderOf_pos.ne'
  have hpow : (ρc τ₀ : Matrix (Fin 2) (Fin 2) ℂ) ^ orderOf x = 1 := by
    have h1 := congrArg Subtype.val (pow_orderOf_eq_one x)
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
    rw [← Units.val_pow_eq_pow_val]
    change ((x : GL (Fin 2) ℂ) ^ orderOf x : GL (Fin 2) ℂ).val = 1
    rw [h1, Units.val_one]
  obtain ⟨α, hα'⟩ := trace_mem_range_of_pow_eq_one ιC _ hn hpow
  have hα : ιC α = (ρc τ₀ : Matrix (Fin 2) (Fin 2) ℂ).trace := hα'
  refine ⟨α, by rw [hα, htr₀], fun v σ hv hσ => ?_⟩
  have htr := (hfr v σ hv hσ).1
  have hsum : (∑ i, (⟨(ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i i, hmem σ i i⟩ : genRing ιC E)) =
      ⟨ιC α, iotaC_mem_genRing ιC E α⟩ := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    change (ρc σ : Matrix (Fin 2) (Fin 2) ℂ).trace = ιC α
    rw [htr, ← htr₀, hα]
  change (Matrix.trace fun i j => (ρh σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) i j) = ιL α
  simp only [Matrix.trace, Matrix.diag, hentry, ← map_sum, hsum, g', RingHom.comp_apply, hφ]
  rfl

/-- **Row r15 (`HSyn.DeligneSerreConseq`), proved from the published-form leaf `DSThm966`
(Deligne–Serre 1974 Thm 4.1; Diamond–Shurman Thm 9.6.6).** A semisimple `ρ` attached to a weight-one
normalized eigenform `g` agrees at Frobenius, outside the primes dividing `Nℓ`, with the
`ℓ`-adic realization `ρ₀` of Deligne–Serre's representation (`artinTransport_finite`); both are
semisimple, so they are conjugate (`attachedConj_proof`: T18 + T19), and `ρ` has finite image. -/
theorem deligneSerreConseq_of_ds (hDS : DSThm966) : HDec.HSyn.DeligneSerreConseq := by
  intro ℓ _ ιC ιL ρ N χ g hN hg hss hatt
  obtain ⟨ρ0, hss0, hatt0, hfin0⟩ := artinTransport_finite hDS ℓ ιC ιL N χ g hN hg
  let ρ' : GaloisRep ℓ 2 := ⟨ρ.toHom, ρ.continuous_toHom⟩
  have hatt' : ρ'.AttachedTo ιC ιL g := hatt
  have hconj : IsConj ρ0 ρ' := by
    refine attachedConj_proof ℓ ρ0 ρ' (N * ℓ).primeFactors hss0 hss fun p hp hpS => ?_
    have hpN : ¬ p ∣ N * ℓ := by
      intro h
      exact hpS (Nat.mem_primeFactors.mpr ⟨hp, h, Nat.mul_ne_zero (by omega)
        (Fact.out : ℓ.Prime).ne_zero⟩)
    obtain ⟨hu0, α0, hα0, htr0⟩ := hatt0 p hp hpN
    obtain ⟨hu, α, hα, htr⟩ := hatt' p hp hpN
    have heq : α0 = α := by
      apply ιC.toRingHom.injective
      change ιC α0 = ιC α
      rw [hα0, hα]
    refine ⟨hu0, hu, fun v σ hv hσ => ?_⟩
    rw [htr0 v σ hv hσ, htr v σ hv hσ, heq]
  obtain ⟨P, hP⟩ := hconj
  refine (hfin0.image fun M => P⁻¹ * M * P).subset ?_
  rintro _ ⟨σ, rfl⟩
  refine ⟨ρ0.toHom σ, ⟨σ, rfl⟩, ?_⟩
  change P⁻¹ * ρ0.toHom σ * P = ρ'.toHom σ
  rw [hP σ]
  group

end ModularSplit

namespace HDec

namespace HSyn

open CategoryTheory AlgebraicGeometry Limits

/-! ## The bundles -/

/-- **The research leaves still open** (leaf-fold9): leaf-fold8's `OpenResearchLeaves8` without `r1rec`, `r5`
(proved from `r1r2`, `r1rec_of_rep`, `r5fp_of_rep`) and `r15` (proved from `dsThm966`, modular-split's
`deligneSerreConseq_of_ds`). 28 fields. -/
structure OpenResearchLeaves9 : Prop where
  r1r2 : LeafAdopt.R1R2fpRep
  shimuraFamily : QMSplit.Moduli.ShimuraFamily
  r3 : _root_.ZInQ.LeafPush2.R03_LinYang
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r5count : LeafQM.AV.R5fpCount
  r6 : _root_.PkgI2.RaynaudCriterion.{0}
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r7b : _root_.PkgI2.SerreTatePotentialGood.{0}
  r8 : _root_.PkgI2.GrothendieckMonodromy.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, SS1: Grothendieck's semistable reduction theorem, global form (SGA 7 IX 3.6). -/
  semistableReductionThm : _root_.ZInQ.HeightSplit.SemistableReductionThm
  /-- height-split, SS2: base change of the identity component in the semistable case (SGA 7 IX 3.3). -/
  semistableNeronBaseChange : _root_.ZInQ.HeightSplit.SemistableNeronBaseChange
  /-- height-split, SS3: semistability persists under finite extension (SGA 7 IX 3.3). -/
  semistablePersists : _root_.ZInQ.HeightSplit.SemistablePersists
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.BostLowerBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-16: Faltings 1983 Lemma 5 (semistable form) over every number field `L ⊇ K`, replaces
  `r20`. -/
  faltingsLemma5BC : _root_.ZInQ.HeightSplit.FaltingsLemma5BC
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14

/-- **The textbook leaves still open** (leaf-fold9): leaf-fold8's `OpenTextbookLeaves8` without `t33` and
`normalModelOfFunctionFieldQ` (proved by cloud PR #11, `ZInQKernel/Contrib/CloudW07JacobiansCurves/`). 18 fields. -/
structure OpenTextbookLeaves9 : Prop where
  mulEtaleAbelianScheme : _root_.AvSplit.T4.MulEtaleAbelianScheme
  mumfordTorsionAlgClosed : _root_.AvSplit.MumfordTorsionAlgClosed
  homFreeFiniteAlgClosed : _root_.ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed
  charPolyIndepOfEllAlgClosed : _root_.ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed
  poincareComplement : _root_.ZInQ.Contrib.AVB1.PoincareComplement
  cartierSmooth : _root_.AVGlue.CartierSmooth
  geomConnOfRationalPoint : _root_.AVGlue.GeomConnOfRationalPoint
  groupSchemeEquidim : _root_.AVGlue.GroupSchemeEquidim
  t10 : _root_.T10Etale.T10_TateDuality
  uniformizationLeafAll : _root_.BPAnalytic.Uniformization.UniformizationLeafAll
  gagaMorphism : _root_.ZInQ.HomLattice.GAGAMorphism
  bdRInvariants : ∀ (p : ℕ) [Fact p.Prime], _root_.ZInQ.Contrib.HodgeSplit.BdRInvariants p
  yuThm11 : QMSplit.Yu.YuThm11
  dimJacobianEqGenus : _root_.ZInQ.Contrib.CurvesG.DimJacobianEqGenus
  genusX1Field : _root_.ZInQ.Contrib.CurvesG.GenusX1Field
  regularSmoothPerfect : _root_.CurveSplit.RegularSmoothPerfect
  igusaGL2 : _root_.ZInQ.RLeaf.IgusaGL2
  neronSchemeExtensionExists : _root_.ZInQ.Contrib.NeronC.NeronSchemeExtensionExists

/-! ## From the new bundles to leaf-fold8's -/

/-- leaf-fold8's research bundle from leaf-fold9's. -/
theorem researchLeaves8_of_open9 (r : OpenResearchLeaves9) : OpenResearchLeaves8 where
  r1r2 := r.r1r2
  shimuraFamily := r.shimuraFamily
  r1rec := r1rec_of_rep r.r1r2
  r3 := r.r3
  igusaPsi4 := r.igusaPsi4
  igusaChi10 := r.igusaChi10
  r5 := r5fp_of_rep r.r1r2
  r5count := r.r5count
  r6 := r.r6
  r7a := r.r7a
  r7b := r.r7b
  r8 := r.r8
  r9a := r.r9a
  r9b := r.r9b
  hodgeTateDecompAbVar := r.hodgeTateDecompAbVar
  deRhamH1AbVarT := r.deRhamH1AbVarT
  r11r12 := r.r11r12
  eigenformHTNew := r.eigenformHTNew
  dsThm965 := r.dsThm965
  dsThm966 := r.dsThm966
  r15 := _root_.ModularSplit.deligneSerreConseq_of_ds r.dsThm966
  r16 := r.r16
  r17 := r.r17
  semistableReductionThm := r.semistableReductionThm
  semistableNeronBaseChange := r.semistableNeronBaseChange
  semistablePersists := r.semistablePersists
  bostLowerBound := r.bostLowerBound
  javanpeykarBound := r.javanpeykarBound
  faltingsLemma5BC := r.faltingsLemma5BC
  pazukiCor13Upper := r.pazukiCor13Upper
  gaudronRemondThm14 := r.gaudronRemondThm14

/-- leaf-fold8's textbook bundle from leaf-fold9's. -/
theorem textbookLeaves8_of_open9 (t : OpenTextbookLeaves9) : OpenTextbookLeaves8 where
  mulEtaleAbelianScheme := t.mulEtaleAbelianScheme
  mumfordTorsionAlgClosed := t.mumfordTorsionAlgClosed
  homFreeFiniteAlgClosed := t.homFreeFiniteAlgClosed
  charPolyIndepOfEllAlgClosed := t.charPolyIndepOfEllAlgClosed
  poincareComplement := t.poincareComplement
  cartierSmooth := t.cartierSmooth
  geomConnOfRationalPoint := t.geomConnOfRationalPoint
  groupSchemeEquidim := t.groupSchemeEquidim
  t10 := t.t10
  uniformizationLeafAll := t.uniformizationLeafAll
  gagaMorphism := t.gagaMorphism
  bdRInvariants := t.bdRInvariants
  yuThm11 := t.yuThm11
  t33 := _root_.ZInQ.Contrib.CloudW07JacobiansCurves.JacobianExists_proof
  dimJacobianEqGenus := t.dimJacobianEqGenus
  genusX1Field := t.genusX1Field
  normalModelOfFunctionFieldQ := _root_.ZInQ.Contrib.CloudW07JacobiansCurves.NormalModelOfFunctionFieldQ_proof
  regularSmoothPerfect := t.regularSmoothPerfect
  igusaGL2 := t.igusaGL2
  neronSchemeExtensionExists := t.neronSchemeExtensionExists

/-- **G0 with only the open leaves and the open glue** (leaf-fold9; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from `OpenResearchLeaves9` (28), `OpenTextbookLeaves9` (18), leaf-fold8's
`OpenAddedLeaves8` (14) and leaf-fold7's `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every field is
`docs/research/leaf-fold9.md` §2. -/
theorem sixContactMin_of_open9 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves9) (l : OpenAddedLeaves8)
    (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open8 (researchLeaves8_of_open9 r) (textbookLeaves8_of_open9 t) l g

end HSyn

end HDec

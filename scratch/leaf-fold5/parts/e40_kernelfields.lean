/-! ## leaf-fold5 (c): fields restated over the kernel's own Props

The chain's Props below are verbatim copies (inside `namespace HDec`) of kernel declarations
(`ZInQKernel/HDecomp/Objects.lean`, `ZInQKernel/HDecomp/LeafPush2/`, `ZInQKernel/HDecomp/ModCurves/`). They are
not definitionally equal to the kernel's, because the structures and classes they quantify over (`PkgI3.AbVar`,
`PkgI2.IsAbelianVariety`, `PkgI2.IsAbelianScheme`, `LeafModCurves.IsCurve`, `IsJacobian`) are copies too. Each
theorem derives the chain's Prop from the kernel's, so that leaf-fold5's bundles can take the kernel's Prop as the
field: the instances are rebuilt field by field and abelian varieties are passed with `toAbVarK4`/`ofAbVarK4`
(same scheme). -/

noncomputable section

namespace HSyn

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-! ### Group B / C: the PkgI2 leaves (over Mathlib's `Grp` and the class `IsAbelianVariety`) -/

/-- T5 (`TorsionStructure`, Mumford §4) from the kernel's statement. -/
theorem torsionStructure_ofK5 (h : _root_.PkgI2.TorsionStructure.{0}) : PkgI2.TorsionStructure.{0} := by
  intro K _ A hA g n hg hn hnK
  haveI : _root_.PkgI2.IsAbelianVariety A := ⟨hA.proper, hA.smooth, hA.geomIntegral⟩
  exact h K A g n hg hn hnK

/-- T4 (`ReductionTorsionBijective`) from the kernel's statement. -/
theorem reductionTorsionBijective_ofK5 (h : _root_.PkgI2.ReductionTorsionBijective.{0}) :
    PkgI2.ReductionTorsionBijective.{0} := by
  intro K _ O _ w hw A hA 𝒜 h𝒜 e m hm hmO
  haveI : _root_.PkgI2.IsAbelianVariety A := ⟨hA.proper, hA.smooth, hA.geomIntegral⟩
  haveI : _root_.PkgI2.IsAbelianScheme 𝒜 := ⟨h𝒜.proper, h𝒜.smooth, h𝒜.geomConnected⟩
  exact h K O w hw A 𝒜 e m hm hmO

/-- R6 (`RaynaudCriterion`, SGA 7 IX 4.7) from the kernel's statement. -/
theorem raynaudCriterion_ofK5 (h : _root_.PkgI2.RaynaudCriterion.{0}) : PkgI2.RaynaudCriterion.{0} := by
  intro K _ O _ w hw A hA
  haveI : _root_.PkgI2.IsAbelianVariety A := ⟨hA.proper, hA.smooth, hA.geomIntegral⟩
  exact h K O w hw A

/-- The kernel's `HasGoodReduction` is the chain's (the class `IsAbelianScheme` inside it is a copy). -/
theorem hasGoodReduction_iffK5 {K : Type} [Field K] (A : Grp (Over (Spec (.of K)))) (O : ValuationSubring K) :
    _root_.PkgI2.HasGoodReduction A O ↔ PkgI2.HasGoodReduction A O :=
  ⟨fun ⟨𝒜, h, e⟩ => ⟨𝒜, ⟨h.proper, h.smooth, h.geomConnected⟩, e⟩,
   fun ⟨𝒜, h, e⟩ => ⟨𝒜, ⟨h.proper, h.smooth, h.geomConnected⟩, e⟩⟩

/-- R7(a) (`NeronOggShafarevich`, Serre–Tate 1968 Thm 1) from the kernel's statement. -/
theorem neronOggShafarevich_ofK5 (h : _root_.PkgI2.NeronOggShafarevich.{0}) :
    PkgI2.NeronOggShafarevich.{0} := by
  intro K _ O _ w hw A hA
  haveI : _root_.PkgI2.IsAbelianVariety A := ⟨hA.proper, hA.smooth, hA.geomIntegral⟩
  have h' := h K O w hw A
  rw [hasGoodReduction_iffK5] at h'
  exact h'

/-- R7(b) (`SerreTatePotentialGood`) from the kernel's statement. -/
theorem serreTatePotentialGood_ofK5 (h : _root_.PkgI2.SerreTatePotentialGood.{0}) :
    PkgI2.SerreTatePotentialGood.{0} := by
  intro K _ O _ w hw A hA
  haveI : _root_.PkgI2.IsAbelianVariety A := ⟨hA.proper, hA.smooth, hA.geomIntegral⟩
  have h' := h K O w hw A
  simp only [hasGoodReduction_iffK5] at h'
  exact h'

/-- R8 (`GrothendieckMonodromy`, SGA 7 IX) from the kernel's statement. -/
theorem grothendieckMonodromy_ofK5 (h : _root_.PkgI2.GrothendieckMonodromy.{0}) :
    PkgI2.GrothendieckMonodromy.{0} := by
  intro K _ O _ w hw A hA
  haveI : _root_.PkgI2.IsAbelianVariety A := ⟨hA.proper, hA.smooth, hA.geomIntegral⟩
  exact h K O w hw A

/-! ### Group B / D: the PkgI3 leaves (over `PkgI3.AbVar`) -/

set_option maxHeartbeats 8000000 in
/-- R9(a) (`FaltingsSemisimple`, Faltings 1983 Satz 3) from the kernel's statement. -/
theorem faltingsSemisimple_ofK5 (h : _root_.PkgI3.FaltingsSemisimple) : PkgI3.FaltingsSemisimple :=
  fun K _ _ A ℓ _ => h K (toAbVarK4 A) ℓ

/-- R9(b) (`FaltingsTate`, Faltings 1983 Satz 4, Kor. 1) from the kernel's statement. -/
theorem faltingsTate_ofK5 (h : _root_.PkgI3.FaltingsTate) : PkgI3.FaltingsTate :=
  fun K _ _ A B ℓ _ => h K (toAbVarK4 A) (toAbVarK4 B) ℓ

/-- T27 (`QMDichotomyYu`, Yu 2013 Thm 1.1) from the kernel's statement. -/
theorem qmDichotomyYu_ofK5 (h : _root_.PkgI3.QMDichotomyYu) : PkgI3.QMDichotomyYu :=
  fun k _ _ _ A hA a b hab hdiv hemb => h k (toAbVarK4 A) hA a b hab hdiv hemb

/-- T35 (`UniformizationExists`, `A(ℂ) ≅ ℂ^g/Λ`) from the kernel's statement. -/
theorem uniformizationExists_ofK5 (h : _root_.ZInQ.LeafPush2.UniformizationExists) :
    ZInQ.LeafPush2.UniformizationExists :=
  fun K _ A σ g hg => h K (toAbVarK4 A) σ g hg

/-! ### Group G: Jacobians -/

/-- T33 (`JacobianExists ℚ`, Weil; Milne 1986 Thm 1.1, Prop. 6.1) from the kernel's statement. -/
theorem jacobianExists_ofK5 (h : _root_.LeafModCurves.JacobianExists ℚ) : LeafModCurves.JacobianExists ℚ := by
  intro X hX P₀
  obtain ⟨J, aj, hJ⟩ := h X ⟨hX.proper, hX.smooth, hX.geomConnected⟩ P₀
  exact ⟨ofAbVarK4 J, aj, ⟨hJ.base, fun A f hf => hJ.univ (toAbVarK4 A) f hf⟩⟩

/-! ### Groups F, G: R16 (Eichler–Shimura on `J₁(N)`) and R17 (Carayol) -/

/-- R17 (`CarayolR17'`, Carayol 1986 Thm (A)) from the kernel's statement (the chain's `GaloisRep` is a copy of the
kernel's structure, rebuilt from its two fields). -/
theorem carayolR17_ofK5 (h : _root_.LadicCond.CarayolR17') : LadicCond.CarayolR17' := by
  intro ℓ _ ιC ιL N χ f ρ p _ hN hf hs ha hp
  exact h ℓ ιC ιL N χ f ⟨ρ.toHom, ρ.continuous_toHom⟩ p hN hf hs ha hp

set_option maxHeartbeats 8000000 in
/-- R16 (`R16_EichlerShimuraJ1'`) from the kernel's statement (`IsJ1` transported as for T34; the quotient `A` is
the kernel's abelian variety, read back with `ofAbVarK4`). Lean needs about 6 minutes of unfolding here. -/
theorem eichlerShimuraJ1_ofK5 (h : _root_.LeafModCurves.R16_EichlerShimuraJ1') :
    LeafModCurves.R16_EichlerShimuraJ1' := by
  rintro N χ f J hN hf ⟨X, P₀, aj, hX, hJ⟩
  obtain ⟨h1, A, π, θ, h2⟩ := h N χ f (toAbVarK4 J) hN hf
    ⟨X, P₀, aj, ⟨⟨hX.1.proper, hX.1.smooth, hX.1.geomConnected⟩, hX.2⟩, isJacobianK_of5 hJ⟩
  exact ⟨h1, ofAbVarK4 A, π, θ, h2⟩

end HSyn

end

#print axioms HSyn.torsionStructure_ofK5
#print axioms HSyn.reductionTorsionBijective_ofK5
#print axioms HSyn.raynaudCriterion_ofK5
#print axioms HSyn.hasGoodReduction_iffK5
#print axioms HSyn.neronOggShafarevich_ofK5
#print axioms HSyn.serreTatePotentialGood_ofK5
#print axioms HSyn.grothendieckMonodromy_ofK5
#print axioms HSyn.faltingsSemisimple_ofK5
#print axioms HSyn.faltingsTate_ofK5
#print axioms HSyn.qmDichotomyYu_ofK5
#print axioms HSyn.uniformizationExists_ofK5
#print axioms HSyn.jacobianExists_ofK5
#print axioms HSyn.carayolR17_ofK5
#print axioms HSyn.eichlerShimuraJ1_ofK5

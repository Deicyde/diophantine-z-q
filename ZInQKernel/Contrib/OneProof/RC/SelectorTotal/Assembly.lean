import ZInQKernel.Contrib.OneProof.RC.ParamJoin.Assembly
import ZInQKernel.Contrib.OneProof.RC.O7Residual.Family

/-! The conductor-one selector covers the full odd filter (tex 8209–8217,
9439–9443). Install the two parametrization selectors before constructing
the stage setup. The interface assembly is on-the-spot, provenance (c). -/

noncomputable section

open scoped NumberField WeierstrassCurve Classical
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Visibility

namespace ZInQ.Manuscript.RC.SelectorTotal

open Gz34Instance PreparedParam

/-- The existing inputs of the genus assembly that do not depend on either
index function, together with the inputs of the fixed-scale parametrization.
The CM field proof is shared with the Heegner anchor. -/
structure ParamInputs {ℓ : ℕ} (W₀ : WData ℓ) where
  P : Prints
  hℓ : 0 < ℓ
  f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
    Subgroup (GL (Fin 2) ℝ)) 2
  hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ)
  Lat : PeriodPair
  hLat : IsLatticeOf (Ecurve ℓ) Lat
  hNC : IsNonCMLattice Lat
  κ : ℂ
  hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ
  hr : ∃ c : ℚ, (c : ℂ) = κ
  hCMField : letI : NeZero (newformLevel (Ecurve ℓ)) := ⟨(curve_form P hℓ).1.ne'⟩
    CMFieldOfDefinition (X0Branch.model (newformLevel (Ecurve ℓ)))
  N : Even.CentralNormalization (Ecurve ℓ)
  hN : N.Lstar = W₀.Lstar
  hElkikMD : ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar (Ecurve ℓ) Lat W₀.hstar
  hpartner : IsGenusPartner ℓ W₀.hstar
  hlevel0 : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ S0 ℓ
  hS : SupportSpec W₀
  hprepared : PreparedSpec W₀
  hstarS : ∀ p ∈ W₀.hstar.natAbs.primeFactors, p ∈ W₀.S
  hpreparedLoc : ∀ h, W₀.prepared h →
    ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → SquareAt p h
  hk0 : W₀.kfin < 0
  hksq : Squarefree W₀.kfin
  hk4 : W₀.kfin % 4 = 1
  hk2N : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → UnitSquareAt p W₀.kfin
  hkcop : IsCoprime W₀.kfin W₀.hstar

abbrev genusValues {ℓ : ℕ} {W₀ : WData ℓ} (a : ParamInputs W₀) :=
  ParamJoin.genus_values (W := W₀) a.P a.hℓ a.hf a.hLat a.hκ a.hr a.hCMField a.hpartner a.hlevel0

abbrev ringValues {ℓ : ℕ} {W₀ : WData ℓ} (a : ParamInputs W₀) :=
  ParamJoin.ring_values (s := W₀.hstar) a.P a.hℓ a.hf a.hLat a.hκ a.hr a.hCMField

/-- Keep the interface data and define its two index functions from the
separate conductor-one and companion selectors. -/
def withParamIndices {ℓ : ℕ} {W₀ : WData ℓ} (a : ParamInputs W₀) : WData ℓ :=
  { W₀ with
    jgen := jgenOf (Ecurve ℓ) a.f a.Lat a.κ W₀.hstar
      (selectGenus (curve_form a.P a.hℓ).1 (genusPartner_of_support a.hpartner a.hlevel0)
        (genusValues a))
    jrc := jrcOf (Ecurve ℓ) a.f a.Lat a.κ (selectRing (curve_form a.P a.hℓ).1 (ringValues a)) }

/-- Build the genus instance with its two algebraic value families supplied
by ParamJoin and both index equations by reflexivity. -/
def genusInstance {ℓ : ℕ} {W₀ : WData ℓ} (a : ParamInputs W₀) :
    GenusOddInstance (withParamIndices a) :=
  instanceOfParamValues a.P a.hℓ a.hf a.hLat a.hNC a.hκ a.N a.hN a.hElkikMD
    a.hpartner a.hlevel0 a.hS a.hprepared a.hstarS a.hpreparedLoc
    (genusValues a) (ringValues a) rfl rfl a.hk0 a.hksq a.hk4 a.hk2N a.hkcop

/-- The selector has a value on every admissible row, irrespective of rank. -/
theorem selG_isSome_of_admissible {ℓ : ℕ} {W₀ : WData ℓ} (a : ParamInputs W₀)
    (hglue : PreparedGlue (withParamIndices a)) (i : ℕ) (D : ℤ)
    (hD : (withParamIndices a).admissible i D) :
    ((genusInstance a).selG D).isSome :=
  selectGenus_isSome _ _ (genusValues a) ((genusInstance a).hprep D (hglue i D hD))

/-- The exact selection equation consumed by the actual point interface. -/
theorem exists_selected_of_admissible {ℓ : ℕ} {W₀ : WData ℓ} (a : ParamInputs W₀)
    (hglue : PreparedGlue (withParamIndices a)) (i : ℕ) (D : ℤ)
    (hD : (withParamIndices a).admissible i D) :
    ∃ t, (genusInstance a).selG D = some t :=
  Option.isSome_iff_exists.mp (selG_isSome_of_admissible a hglue i D hD)


/-- Read the selected datum and equation at the natural index used by the
actual comparison. Positivity of admissible indices makes this the same row. -/
def selectedDatum {ℓ : ℕ} {W₀ : WData ℓ} (a : ParamInputs W₀)
    {L : ℕ} (s : StageKummer.Setup (genusInstance a) L)
    (i : ℕ) (D : ℤ) (hD : (withParamIndices a).admissible i D) :
    {t : HeegnerDatum (Ecurve ℓ) a.f a.Lat a.κ ((D.toNat : ℤ) * W₀.hstar) 1 W₀.hstar //
      (genusInstance a).selG (D.toNat : ℤ) = some t} := by
  have hglue := StageSelector.preparedGlue_of_withStages s.hstages.withStages_eq
  have hp := (genusInstance a).hprep D (hglue i D hD)
  have hD' : (withParamIndices a).admissible i (D.toNat : ℤ) := by
    rwa [Int.toNat_of_nonneg hp.1.le]
  have ht := exists_selected_of_admissible a hglue i (D.toNat : ℤ) hD'
  exact ⟨ht.choose, ht.choose_spec⟩

open O7Residual O7Assemble O7Actual O7Orbits PicardFibers Eichler Adelic ThetaJoin ThetaClose PMGeometry

section Point

variable {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W} {L : ℕ} (s : StageKummer.Setup I L)
  (i : ℕ) [Fact (s.q.stage i).p.Prime]
  [(ReducedEquation (EcurveZ ℓ) (s.q.stage i).p).IsElliptic]

variable {m : ℕ} (hN : 0 < StageKummer.level ℓ)
  (hcop : (StageKummer.level ℓ).Coprime (s.q.stage i).p)
  (H : DiscriminantData m (StageKummer.level ℓ) (s.q.stage i).p) (w : ℕ → ℤˣ)
  (hm : (m : ℤ) = -W.hstar) {ap : ℕ → ℤ} {X : PMAdelic.CoarseFibre}
  (J : PMAdelic.JetchevKane (s.q.stage i).p (StageKummer.stage_mod_four s i)
    (StageKummer.level ℓ) hN hcop X)
  (G : PMAdelic.SpecialFibre (s.q.stage i).p (StageKummer.level ℓ)
    (ResidueAt (StageKummer.place s i)) (ReducedEquation (EcurveZ ℓ) (s.q.stage i).p) ap X)

variable {n : ℕ}
  (A : AdmissibleD (actualStage s i hN hcop H w hm J G) (n : ℤ))
  (t : HeegnerDatum (Ecurve ℓ) I.f I.Lat I.κ ((n : ℤ) * W.hstar) 1 W.hstar)

/-- The reference data and pointwise hypotheses at a datum supplied by
the selector. -/
structure PointComparisons where
  embedding : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
    (StageKummer.chosenDatum t).K →ₐ[ℚ] B (-1) (-((s.q.stage i).p : ℚ))
  ref : Orientations (StageKummer.level ℓ).primeFactors.card
  r : (supportAt s i hN hcop H w hm J G A t).classGroup → X.Point
  hCM : ∀ c, r c =
    (J.idealClasses (Visibility.ThetaStage.zc
      (orbitsAt s i hN hcop H w hm J G A t embedding
        (chartAt s i hN hcop H w hm J G A t embedding)
        (realizationsAt s i hN hcop H w hm J G A t embedding)).param (ref, c))).val
  hπ : ∀ c, (PMAdelic.geometricInput J G).specialize (r c) =
    StageKummer.reduceDatum s i t (show stageTest s.q i (n : ℤ) from A.detecting)
      (conjugate (StageKummer.chosenDatum t) (artinLabelAt s i hN hcop H w hm J G A t c))

end Point

section Leaf

attribute [local irreducible] StageKummer.datumOnModel ringClassArtinEquiv

variable {ℓ : ℕ} {W₀ : WData ℓ} (a : ParamInputs W₀) {L : ℕ}
  (s : StageKummer.Setup (genusInstance a) L)

variable {m : ℕ} (hN : 0 < StageKummer.level ℓ)
  (hcop : ∀ i, (StageKummer.level ℓ).Coprime (s.q.stage i).p)
  (H : ∀ i, DiscriminantData m (StageKummer.level ℓ) (s.q.stage i).p) (w : ℕ → ℤˣ)
  (hm : (m : ℤ) = -(withParamIndices a).hstar) {ap : ℕ → ℤ} {X : ℕ → PMAdelic.CoarseFibre}
  (J : ∀ i, PMAdelic.JetchevKane (s.q.stage i).p (StageKummer.stage_mod_four s i)
    (StageKummer.level ℓ) hN (hcop i) (X i))
  (G : ∀ i, PMAdelic.SpecialFibre (s.q.stage i).p (StageKummer.level ℓ)
    (ResidueAt (StageKummer.place s i)) (ReducedEquation (EcurveZ ℓ) (s.q.stage i).p) ap (X i))

variable (comparisons : ∀ i D (hD : (withParamIndices a).admissible i D),
  PointComparisons s i hN (hcop i) (H i) w hm (J i) (G i)
    (admissibleNatAt s hN hcop H w hm J G i D hD) (selectedDatum a s i D hD).val)

/-- Supply `PointInputs.ht` for the selected datum and keep the given
reference data and pointwise equalities. -/
def pointInputs (i : ℕ) (D : ℤ) (hD : (withParamIndices a).admissible i D) :
    PointInputs s i hN (hcop i) (H i) w hm (J i) (G i)
      (admissibleNatAt s hN hcop H w hm J G i D hD) :=
  let p := comparisons i D hD
  { t := (selectedDatum a s i D hD).val
    embedding := p.embedding
    ref := p.ref
    r := p.r
    ht := (selectedDatum a s i D hD).property
    hCM := p.hCM
    hπ := p.hπ }

variable
  (hSign : ∀ i (j : Fin (StageKummer.level ℓ).primeFactors.card),
    (w (levelPrime (StageKummer.level ℓ) j).val : ℤ) =
      (G i).atkinSign (levelPrime (StageKummer.level ℓ) j).val)
  (hCusp : ∀ i (j : Fin (StageKummer.level ℓ).primeFactors.card),
    L • (PMAdelic.geometry (J i) (G i)).cusp (levelPrime (StageKummer.level ℓ) j).val = 0)

set_option maxHeartbeats 1400000 in
set_option maxRecDepth 1600 in
/-- Instantiate `PreLeaves.odd_staged` over `withParamIndices a`. Inputs
(by kind and owner):

* `ℓ`, `W₀`: base curve parameter and interface data, RC0 integrator.
* `a.P : Prints`: existing shared GLUE prints, shared print layer.
* `a.hℓ`, `a.f`, `a.hf`: positive curve parameter and normalized newform
  data, actual-curve lane (`Gz34Instance`).
* `a.Lat`, `a.hLat`, `a.hNC`, `a.κ`, `a.hκ`: lattice, non-CM proof and
  fixed parametrization scale data, uniformization and parametrization lanes.
* `a.hr`: rationality of that same `κ`, parametrization lane. Tex
  1785–1787 fixes the based map via the chosen rational isogeny and
  1825–1828 keeps its period normalization.
* `a.hCMField`: `CMFieldOfDefinition` at
  `X0Branch.model (newformLevel (Ecurve ℓ))`, the shared source CM descent
  input owned by the Heegner anchor residual. The same proof serves both lanes.
* `a.N`, `a.hN`: central normalization data and its identification with
  the interface, RC11. `a.hElkikMD`: nonzero rational partner value in the
  chosen lattice normalization, Elkik–Manin–Drinfeld lane.
* `a.hpartner`, `a.hlevel0`, `a.hS`, `a.hprepared`, `a.hstarS`,
  `a.hpreparedLoc`: partner and support/filter proofs, RC13, actual curve
  and stage support lanes.
* `a.hk0`, `a.hksq`, `a.hk4`, `a.hk2N`, `a.hkcop`: final companion local
  and coprimality proofs, final companion lane.
* `L`, `s`: fixed multiplier and actual witness, detector, places,
  stage sequence and precision data, RC23 and Stage Kummer.
* `m`, `hN`, `hcop`, `H`, `w`, `hm`: discriminant, level, prime,
  sign and partner data, ThetaClose and the stage arithmetic lane.
* `ap`, `X`, `J`, `G`: eigenvalue and coarse fibre data with supersingular
  identification and specialization, PM adelic geometry lane.
* `comparisons`: reference embedding, orientation and coarse points
  (O7Orbits and PM adelic geometry), with the per-row point identities
  `hCM` and `hπ` (X0 model and Stage Kummer).
* `hSign`, `hCusp`: fixed Atkin signs and annihilation of cusp
  translations, O.7 normalizers and PM adelic geometry.
* `ha`: fixed integer `aθ` reads the actual theta coefficient with its
  phase and precision, theta coefficient interface and integrator.
* `hL`, `hsign`: native torsion is killed by `L`, and admissible twists
  have odd sign, RC23 and the root-number lane.

The selector equation is supplied for each row by `selectedDatum`. -/
theorem oddStagedOfParamValues
    (ha : ∀ i D (hD : (withParamIndices a).admissible i D),
      let row := actualRows s hN hcop H w hm J G
        (actualRowFamily s hN hcop H w hm J G hSign hCusp
          (pointInputs a s hN hcop H w hm J G comparisons)) i D hD
      (2 : Coefficients hN (H 0) w) ^ (withParamIndices a).Mθ i ∣
        row.weights.phase row.reference * ((withParamIndices a).aθ i D : Coefficients hN (H 0) w) -
          Visibility.thetaCoeff (actualFamily s hN hcop H w hm J G i).visibility
            ((m : ℤ) * D : ℤ))
    (hL : MultiplierKillsNativeTorsion (Ecurve ℓ) a.f a.Lat a.κ (withParamIndices a).hstar L)
    (hsign : AdmissibleOddSign (withParamIndices a).toRCData) :
    Nonempty (OddStagedInstance (withParamIndices a)) :=
  oddStagedActual s hN hcop H w hm J G hSign hCusp
    (pointInputs a s hN hcop H w hm J G comparisons) ha hL hsign

end Leaf

end ZInQ.Manuscript.RC.SelectorTotal

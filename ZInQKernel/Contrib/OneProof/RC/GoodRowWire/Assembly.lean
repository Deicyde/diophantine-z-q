import ZInQKernel.Contrib.OneProof.RC.GoodRowWire.Row
import ZInQKernel.Contrib.OneProof.RC.PMWire.Assembly

/-! **The odd staged instance from the same-place data** (tex 9101–9113, 8366–8368, 8476–8492).

`oddStagedOfSamePlace` is `PMWire.oddStagedOfGoodRows` (`RC/PMWire/Assembly.lean:220`) with its
hypotheses `G` and `hcop` replaced by

* `hB : (N φ(N)).primeFactors ⊆ s.B` (`N := StageKummer.level ℓ`), and
* `sp : ∀ i, StageSamePlace s hN hB (X i) i` (the same-place data at every stage),

under the substitution `R i := LocalIntegers (s.q.stage i).p`, `G := stageRows a s π hQ hN hB sp`
(`G i = stageRow s hN hB π hQ i (sp i)`) and `hcop := stage_coprime s hN hB`. The hypotheses
`J`, `relations`, `cusps`, `refs` and `ha` mention `G`, `hcop` or `R` and are restated with
exactly the same content after this substitution. `htame` and `hcop` are derived from `hB`
(`ModelGeneric5.stagePrime_not_dvd_tame`, `stage_coprime`), `h₂` from `ModelGeneric5.two_le_level
hN` and `h₅` from `ModelGeneric5.stagePrime_five_le`. Provenance: wiring only, on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve
open scoped NumberField WeierstrassCurve Classical
  MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Visibility
open WeierstrassCurve.ModelTorsion

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 2600
set_option maxHeartbeats 1900000
set_option synthInstance.maxHeartbeats 350000

namespace ZInQ.Manuscript.RC.GoodRowWire

open PMWire PreparedParam O7Actual O7Assemble O7Orbits O7Residual PMGeometry ThetaClose
  SelectorTotal AtkinPin PicardFibers Eichler Adelic ThetaJoin

variable {ℓ : ℕ} {W₀ : WData ℓ} (a : ParamInputs W₀) {L : ℕ}
  (s : StageKummer.Setup (genusInstance a) L)
  [NeZero (CST.newformLevel (Ecurve ℓ))] (F : ConsumerNewform (genusInstance a))
  [NeZero (StageKummer.level ℓ)] [((EcurveZ ℓ)⁄ℚ).IsElliptic]
  (π : (X0Model3.model (StageKummer.level ℓ)).X ⟶ Proj ((EcurveZ ℓ)⁄ℚ).toProjective.grading)
  (hQ : π ≫ projectiveOverQ ((EcurveZ ℓ)⁄ℚ) = (X0Model3.model (StageKummer.level ℓ)).overQ)
  (han : ∀ τ : UpperHalfPlane, projectiveValue
    (((X0Model3.model (StageKummer.level ℓ)).complexPoint τ).comp π hQ).val =
      phiAn ((EcurveZ ℓ)⁄ℚ) (StageKummer.formOnModel (f := a.f) (EcurveZ_baseChange ℓ)) a.Lat a.κ τ)
  {m : ℕ} (hN : 0 < StageKummer.level ℓ) {ap : ℕ → ℤ} {X : ℕ → PMAdelic.CoarseFibre}

/-- The family of assembled rows: `stageRow` at every stage, from the same-place data `sp`. -/
abbrev stageRows
    (hB : (StageKummer.level ℓ * (StageKummer.level ℓ).totient).primeFactors ⊆ s.B)
    (sp : ∀ i, StageSamePlace s hN hB (X i) i) (i : ℕ) :
    GoodRow (LocalIntegers (s.q.stage i).p) (s.q.stage i).p (StageKummer.level ℓ)
      (ResidueAt (StageKummer.place s i)) (ReducedEquation (EcurveZ ℓ) (s.q.stage i).p)
      (X i) (fixedMap (C := EcurveZ ℓ) π hQ) :=
  stageRow s hN hB π hQ i (sp i)

/-- **The odd staged instance for (O.7) from the same-place data.** This is
`PMWire.oddStagedOfGoodRows` with `G` and `hcop` replaced by `hB` and `sp`.

Remaining hypotheses and their owners:
* `hB` (the stage lane's exclusion set; tex 8366–8368, the place for `l₀` is chosen to
  "exclude two, all bad primes, the support of D_w h_* and any other finite set"):
  `(N φ(N)).primeFactors ⊆ s.B` with `N := StageKummer.level ℓ`. It is satisfiable: for a
  setup from `Stages.exists_detector_stages`, `s.B = stageExclusions ℓ Dw hstar B'`
  (`RC/Stages/DetectorStages.lean:48–49`, `RC/Stages/Actual.lean:99`), and
  `ModelGeneric5.subset_stageExclusions` gives `B' ⊆ s.B`, so `B' ⊇ (N φ(N)).primeFactors`
  suffices. `hcop` and `htame` are derived from it (`stage_coprime`,
  `ModelGeneric5.stagePrime_not_dvd_tame`).
* `sp` (the same-place lane in the hCM lane; tex 8479–8492): `point`, `point_W`, `point_frob`,
  `frobenius_sq` at every stage.
* `J` (the hCM lane: Jetchev–Kane class correspondence GLUE and its three compatibilities;
  tex 8468–8474), `relations` (the detector-specialization lane: `Relations` of
  `RC/PMWire/Operators.lean`), `cusps` (Manin–Drinfeld torsion and `KillsTranslation`; the
  J0Cusps lane), `H`, `hm` (discriminant data of the stage, the stage lane), `refs` (the CM
  points and the selected-row reference comparisons; the hCM lane), `ha` (the aθ definition
  pin, tex 2081–2082), `hL` (multiplier torsion), `hsign` (the admissible odd sign): unchanged
  in content from `oddStagedOfGoodRows`.
* `hN`, `π`, `hQ`, `han`, `F`: the fixed parametrization and newform, as in `oddStagedOfGoodRows`. -/
theorem oddStagedOfSamePlace
    (hB : (StageKummer.level ℓ * (StageKummer.level ℓ).totient).primeFactors ⊆ s.B)
    (sp : ∀ i, StageSamePlace s hN hB (X i) i)
    (J : ∀ i, PMAdelic.JetchevKane (s.q.stage i).p (StageKummer.stage_mod_four s i)
      (StageKummer.level ℓ) hN (stage_coprime s hN hB i) (X i))
    (relations : ∀ i, (stageRows a s π hQ hN hB sp i).Relations ap)
    (cusps : ElkikPrint.ManinDrinfeldTorsion (StageKummer.level ℓ)
        (J0Cusps.algebraicCuspClass (StageKummer.level ℓ)) ∧
      ∀ i, (stageRows a s π hQ hN hB sp i).KillsTranslation L)
    (H : ∀ i, DiscriminantData m (StageKummer.level ℓ) (s.q.stage i).p)
    (hm : (m : ℤ) = -(withParamIndices a).hstar)
    (refs : ∀ i D (hD : (withParamIndices a).admissible i D),
      Reference a s F π hQ han hN (stage_coprime s hN hB) H hm J (stageRows a s π hQ hN hB sp)
        relations i D hD)
    (ha : ∀ i D (hD : (withParamIndices a).admissible i D),
      let row := actualRows s hN (stage_coprime s hN hB) H F.signs hm
        (fun i => adaptComparison (J i))
        (fibreFamily a s F π hQ han (stageRows a s π hQ hN hB sp) relations)
        (AtkinSign.actualRowFamily s hN (stage_coprime s hN hB) H F.signs hm
          (fun i => adaptComparison (J i))
          (signedFamily a s F π hQ han (stageRows a s π hQ hN hB sp) relations)
          (hCuspAt (a := a) (s := s) (F := F) (π := π) (hQ := hQ) (han := han) (hN := hN)
            (hcop := stage_coprime s hN hB) (J := J) (G := stageRows a s π hQ hN hB sp)
            (relations := relations) (cusps := cusps))
          (pointInputs a s hN (stage_coprime s hN hB) H F.signs hm
            (fun i => adaptComparison (J i))
            (fibreFamily a s F π hQ han (stageRows a s π hQ hN hB sp) relations)
            (fun i D hD => referenceComparisons a s F π hQ han hN (stage_coprime s hN hB) H hm J
              (stageRows a s π hQ hN hB sp) relations i D hD (refs i D hD)))) i D hD
      (2 : Coefficients hN (H 0) F.signs) ^ (withParamIndices a).Mθ i ∣
        row.weights.phase row.reference * ((withParamIndices a).aθ i D : Coefficients hN (H 0) F.signs) -
          Visibility.thetaCoeff
            (actualFamily s hN (stage_coprime s hN hB) H F.signs hm (fun i => adaptComparison (J i))
              (fibreFamily a s F π hQ han (stageRows a s π hQ hN hB sp) relations) i).visibility
            ((m : ℤ) * D : ℤ))
    (hL : MultiplierKillsNativeTorsion (Ecurve ℓ) a.f a.Lat a.κ (withParamIndices a).hstar L)
    (hsign : AdmissibleOddSign (withParamIndices a).toRCData) :
    Nonempty (OddStagedInstance (withParamIndices a)) :=
  oddStagedOfGoodRows (a := a) (s := s) (F := F) (π := π) (hQ := hQ) (han := han) (hN := hN)
    (hcop := stage_coprime s hN hB) (H := H) (hm := hm) (J := J)
    (G := stageRows a s π hQ hN hB sp) (relations := relations) (cusps := cusps) (refs := refs)
    ha hL hsign

#print axioms stageRows
#print axioms oddStagedOfSamePlace

end ZInQ.Manuscript.RC.GoodRowWire

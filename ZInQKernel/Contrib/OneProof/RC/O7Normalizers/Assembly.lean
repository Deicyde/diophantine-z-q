import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Weights

/-! Appendix F on the actual level weights and PMAdelic geometry. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O7Normalizers

open Adelic Eichler ThetaJoin ThetaClose O7Actual O7Orbits Visibility

section Fiber

variable {I X T Cl : Type*} [DecidableEq I] {β : I → Type*}

theorem flip_involutive (i : I) : Function.Involutive (O7Actual.flip i : (I → Bool) → I → Bool) := by
  intro t
  funext j
  by_cases hj : j = i
  · subst j
    simp [O7Actual.flip]
  · simp [O7Actual.flip, Function.update_of_ne hj]

variable {o : X → I → Bool} (fiber : ∀ t, Cl ≃ {P : X // o P = t})
    (i : I) (w : Equiv.Perm X) (hw : ∀ P, o (w P) = O7Actual.flip i (o P))

/-- Fiber inverse, after the actual orbit move, after the original fiber map. -/
def fiberPerm (t : I → Bool) : Cl ≃ Cl :=
  (fiber t).trans ((w.subtypeEquiv (fun P => by
    change o P = t ↔ o (w P) = O7Actual.flip i t
    rw [hw]
    exact (flip_involutive i).injective.eq_iff.symm)).trans (fiber (O7Actual.flip i t)).symm)

theorem fiberPerm_apply (t : I → Bool) (c : Cl) :
    (fiber (O7Actual.flip i t) (fiberPerm fiber i w hw t c)).val = w (fiber t c).val := by
  simp [fiberPerm, Equiv.subtypeEquiv]

end Fiber

section Actual

variable {ell N M m : ℕ} [Fact ell.Prime]
variable (h : ell % 4 = 3) (hN : 0 < N) (hcop : N.Coprime ell)
variable (H : DiscriminantData m N ell) (w : ℕ → ℤˣ)
variable {K : Type} [Field K] [Algebra (ZMod ell) K] [DecidableEq K] [IsSepClosed K]
variable {Ebar : WeierstrassCurve (ZMod ell)} [Ebar.IsElliptic] {ap : ℕ → ℤ}
variable {X : PMAdelic.CoarseFibre}
variable (J : PMAdelic.JetchevKane ell h N hN hcop X) (G₀ : PMAdelic.SpecialFibre ell N K Ebar ap X)
variable (d : PM.Evaluation K Ebar M) (L : ℕ)

/-- The geometry's signs as integer units, for choosing the very same
signs in the fixed level characters. -/
def geometrySigns (p : ℕ) : ℤˣ :=
  if hp : p.Prime ∧ 0 < N.factorization p then
    (Int.isUnit_iff.mpr (G₀.atkinSign_eq p hp.1 hp.2)).unit
  else 1

include hN in
theorem geometrySigns_spec (i : Fin N.primeFactors.card) :
    (geometrySigns G₀ (levelPrime N i).val : ℤ) = G₀.atkinSign (levelPrime N i).val := by
  rw [geometrySigns, dite_eq_left ⟨(levelPrime N i).prop, levelPrime_exp hN i⟩, IsUnit.unit_spec]

/-- The fixed multiple of the cusp annihilator kills the actual translation
supplied by PMAdelic. -/
theorem cusp_of_multiple {Cπ : ℕ} (hmul : Cπ ∣ L)
    (hc : ∀ i : Fin N.primeFactors.card, Cπ • (PMAdelic.geometry J G₀).cusp (levelPrime N i).val = 0)
    (i : Fin N.primeFactors.card) :
    L • (PMAdelic.geometry J G₀).cusp (levelPrime N i).val = 0 := by
  obtain ⟨k, rfl⟩ := hmul
  calc
    _ = k • (Cπ • (PMAdelic.geometry J G₀).cusp (levelPrime N i).val) := by
      rw [← mul_nsmul]
    _ = 0 := by rw [hc i, nsmul_zero]

/-- The actual normalizer stage takes its class operations from PMAdelic
and its weights from the aligned theta constructor. -/
def stageAt (u : ClassSet (levelRing h hN) → ℤ)
    (hu : PM.IsLift (PMAdelic.geometry J G₀) d L u) :
    StageAt (Coefficients hN H w) N M hN (m : ℤ) where
  ell := ell
  mod_four := h
  K := K
  Ebar := Ebar
  ap := ap
  G := PMAdelic.geometry J G₀
  d := d
  L := L
  weights := actualPmLocal h hN hcop H w
  m_eq := rfl
  u := u
  hu := hu

variable {u : ClassSet (levelRing h hN) → ℤ}
variable (hu : PM.IsLift (PMAdelic.geometry J G₀) d L u)
variable {D : ℕ} {k : ℤ}

abbrev actualStageAt := stageAt h hN hcop H w J G₀ d L u hu

theorem actualBridge (hD : RequestedIndices (ell := ell) (m := m) D k)
    (hF : LevelFilter (N := N) (m := m) D) :
    SupportBridge (actualStageAt h hN hcop H w J G₀ d L hu) (D : ℤ) := by
  intro z x hx hn
  exact actualFilteredSupport h hN H w z D k hD hF x hx (by exact_mod_cast hn)

abbrev levelDivisor (i : Fin N.primeFactors.card) : (levelPrime N i).val ∣ N :=
  Nat.dvd_of_mem_primeFactors ((N.primeFactors.orderIsoOfFin rfl) i).prop

theorem actual_disc_neg (hD : RequestedIndices (ell := ell) (m := m) D k) :
    disc (actualStageAt h hN hcop H w J G₀ d L hu) (D : ℤ) < 0 := by
  change (D : ℤ) * -(m : ℤ) < 0
  exact mul_neg_of_pos_of_neg (by exact_mod_cast hD.1) (neg_lt_zero.mpr (by
    have := H.odd
    omega))

theorem actual_disc_split (hD : RequestedIndices (ell := ell) (m := m) D k)
    (hF : LevelFilter (N := N) (m := m) D) (i : Fin N.primeFactors.card) :
    Nonvanishing.SplitsIn (disc (actualStageAt h hN hcop H w J G₀ d L hu) (D : ℤ))
      (levelPrime N i).val := by
  let q := levelPrime N i
  change Nonvanishing.SplitsIn ((D : ℤ) * -(m : ℤ)) q.val
  refine ⟨fun _ => hD.2.2.2.2.2, fun ht => ?_⟩
  have hs := hF.2 q.val q.prop ht (levelDivisor i)
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hs
  have hn : (((D : ℤ) * -(m : ℤ) : ℤ) : ZMod q.val) ≠ 0 := by
    intro hz
    have hz' := (legendreSym.eq_zero_iff q.val _).mpr hz
    omega
  exact ⟨fun hd => hn ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd),
    (legendreSym.eq_one_iff q.val hn).mp hs⟩

theorem actual_disc_detecting (hD : RequestedIndices (ell := ell) (m := m) D k) :
    ((disc (actualStageAt h hN hcop H w J G₀ d L hu) (D : ℤ) : ℤ) : ZMod ell) ≠ 0 := by
  change (((D : ℤ) * -(m : ℤ) : ℤ) : ZMod ell) ≠ 0
  have hs : jacobiSym ((D : ℤ) * -(m : ℤ)) ell = -1 := by
    rw [jacobiSym.mul_left, hD.2.2.2.1, H.inert, one_mul]
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hs
  intro hz
  change quadraticChar (ZMod ell) _ = -1 at hs
  rw [hz, quadraticChar_zero] at hs
  omega

variable (hD : RequestedIndices (ell := ell) (m := m) D k) (hF : LevelFilter (N := N) (m := m) D)

abbrev actualOrientationBridge := actualBridge h hN hcop H w J G₀ d L hu hD hF

end Actual

section OrbitWeight

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m D : ℤ}
variable (s : StageAt O N M hN m)

def supportOrbitWeight (P : OrbitSet s.visibility (index s D)) : O :=
  s.visibility.χN P.1 * s.visibility.f P.1 (Quotient.out P.2).val

theorem supportOrbitWeight_mk (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) :
    supportOrbitWeight s ⟨z, Quotient.mk _ x⟩ =
      s.visibility.χN z * s.visibility.f z x.val := by
  unfold supportOrbitWeight
  congr 1
  apply s.visibility.f_eq_of_mem_orbit
  let S := @MulAction.orbitRel (s.visibility.G z) (ActualSupport s D z) _
    (Visibility.ThetaStage.conjAction s.visibility z (index s D))
  exact Quotient.exact (Quotient.out_eq (Quotient.mk S x))

theorem orbitWeight_eq_supportOrbitWeight {Cl : Type}
    (A : OrbitFibers s.visibility (index s D) N.primeFactors.card Cl) (t c) :
    orbitWeight _ A t c = supportOrbitWeight s (A.param (t,c)) := rfl

end OrbitWeight

section ActualMoves

variable {ell N M m : ℕ} [Fact ell.Prime]
variable (h : ell % 4 = 3) (hN : 0 < N) (hcop : N.Coprime ell)
variable (H : DiscriminantData m N ell) (w : ℕ → ℤˣ)
variable {K : Type} [Field K] [Algebra (ZMod ell) K] [DecidableEq K] [IsSepClosed K]
variable {Ebar : WeierstrassCurve (ZMod ell)} [Ebar.IsElliptic] {ap : ℕ → ℤ}
variable {X : PMAdelic.CoarseFibre}
variable (J : PMAdelic.JetchevKane ell h N hN hcop X) (G₀ : PMAdelic.SpecialFibre ell N K Ebar ap X)
variable (d : PM.Evaluation K Ebar M) (L : ℕ)
variable {u : ClassSet (levelRing h hN) → ℤ}
variable (hu : PM.IsLift (PMAdelic.geometry J G₀) d L u)
variable {D : ℕ} {k : ℤ}
variable (hD : RequestedIndices (ell := ell) (m := m) D k) (hF : LevelFilter (N := N) (m := m) D)

abbrev actualOrbits (s : StageAt (Coefficients hN H w) N M hN (m : ℤ)) (D : ℕ) :=
  OrbitSet s.visibility (index s (D : ℤ))

section Moves

variable (s : StageAt (Coefficients hN H w) N M hN (m : ℤ)) (B : SupportBridge s (D : ℤ))

abbrev atkinMove (i : Fin N.primeFactors.card) : Equiv.Perm (actualOrbits hN H w s D) :=
  orbitMove s B _ (splitAdele_order s i)

abbrev uniformizerMove : Equiv.Perm (actualOrbits hN H w s D) :=
  orbitMove s B _ (divisionAdele_order s)

end Moves

theorem atkinMove_class (B : SupportBridge (actualStageAt h hN hcop H w J G₀ d L hu) (D : ℤ))
    (i : Fin N.primeFactors.card) (P : actualOrbits hN H w (actualStageAt h hN hcop H w J G₀ d L hu) D) :
    (atkinMove hN H w _ B i P).1 =
      (PMAdelic.geometry J G₀).atkin (levelPrime N i).val (levelPrime N i).prop (levelPrime_exp hN i) P.1 := by
  let s := actualStageAt h hN hcop H w J G₀ d L hu
  have he := orbitMove_class s B (splitAdele s i) (splitAdele_order s i) P
  exact he.trans (congrArg (fun e : Equiv.Perm (ClassSet (levelRing h hN)) => e P.1)
    (split_class h hN hcop _ (levelPrime_ne_detecting s i) (levelPrime_exp hN i)))

theorem uniformizerMove_class (B : SupportBridge (actualStageAt h hN hcop H w J G₀ d L hu) (D : ℤ))
    (P : actualOrbits hN H w (actualStageAt h hN hcop H w J G₀ d L hu) D) :
    (uniformizerMove hN H w _ B P).1 = (PMAdelic.geometry J G₀).uniformizer P.1 := by
  change (orbitMove _ _ _ _ P).1 = _
  rw [orbitMove_class, division_class]
  rfl

abbrev actualPhase := phaseFor (levelRoots hN H w) (exceptionalProduct_ne_zero hN H)
abbrev actualNorm := levelNormCharacter h hN (levelRoots hN H w) (exceptionalProduct_ne_zero hN H)
abbrev actualFactors := localFactor h (levelRoots hN H w) m

theorem actual_weight_mk (B : SupportBridge (actualStageAt h hN hcop H w J G₀ d L hu) (D : ℤ))
    (z : ClassSet (levelRing h hN))
    (x : ActualSupport (actualStageAt h hN hcop H w J G₀ d L hu) (D : ℤ) z) :
    supportOrbitWeight (actualStageAt h hN hcop H w J G₀ d L hu) ⟨z, Quotient.mk _ x⟩ =
      pointWeight (actualPhase hN H w) (actualFactors h hN H w) (actualNorm h hN H w)
        (pointOfSupport (actualStageAt h hN hcop H w J G₀ d L hu) B z x) := by
  let s := actualStageAt h hN hcop H w J G₀ d L hu
  refine (supportOrbitWeight_mk s z x).trans ?_
  exact congrArg
    (fun r => (actualNorm h hN H w (classRepresentative z) : Coefficients hN H w) *
      weightAt (actualPhase hN H w) (actualFactors h hN H w) (classRepresentative z) r)
    (pointOfSupport_root s B z x).symm

include H in
theorem level_symbol (i : Fin N.primeFactors.card) :
    jacobiSym (-(m : ℤ)) (levelPrime N i).val = 1 := by
  let q := levelPrime N i
  by_cases hq : q.val = 2
  · rw [show (levelPrime N i).val = 2 from hq]
    apply (jacobiSym.mod_left' (b := 2) (a₂ := 1) ?_).trans (jacobiSym.one_left 2)
    have hh := H.twoSplit
    change (-(m : ℤ)) % 8 = 1 % 8 at hh
    omega
  · exact H.levelSplit q hq (levelDivisor i)

theorem actual_atkin_weight
    (hSign : ∀ i : Fin N.primeFactors.card, (w (levelPrime N i).val : ℤ) = G₀.atkinSign (levelPrime N i).val)
    (i : Fin N.primeFactors.card) (P : actualOrbits hN H w (actualStageAt h hN hcop H w J G₀ d L hu) D) :
    supportOrbitWeight (actualStageAt h hN hcop H w J G₀ d L hu)
        (atkinMove hN H w _ (actualOrientationBridge h hN hcop H w J G₀ d L hu hD hF) i P) =
      (G₀.atkinSign (levelPrime N i).val : Coefficients hN H w) *
        supportOrbitWeight (actualStageAt h hN hcop H w J G₀ d L hu) P := by
  let s := actualStageAt h hN hcop H w J G₀ d L hu
  let B := actualOrientationBridge h hN hcop H w J G₀ d L hu hD hF
  let q := levelPrime N i
  let hn := exceptionalProduct_ne_zero hN H
  let C := levelRoots hN H w
  let A := actualPhase hN H w
  let f := actualFactors h hN H w
  let χ := actualNorm h hN H w
  let v := splitUnit (N := N) h q (levelPrime_ne_detecting s i)
  let cov := levelNormCovariance h hN C hn (discriminantDisjoint H)
  obtain ⟨z,x⟩ := P
  induction x using Quotient.inductionOn with
  | _ x =>
    generalize he : atkinMove hN H w s B i ⟨z, Quotient.mk _ x⟩ = Q
    obtain ⟨z',x'⟩ := Q
    induction x' using Quotient.inductionOn with
    | _ x' =>
      rw [actual_weight_mk h hN hcop H w J G₀ d L hu B z' x',
        actual_weight_mk h hN hcop H w J G₀ d L hu B z x]
      rw [pointWeight_rel A f χ cov (orbitMove_rel s B _ _ z x z' x' he)]
      have hmem : q ∈ A.places := (mem_exceptionalPlaces m N ell hn q).mpr
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (levelDivisor i) _) _)
      have htr := (split_generator_trace_det s B (c := -k)
        (by change (D : ℤ) * -(m : ℤ) = 1 - 4 * -k; have := hD.2.2.2.2.1; omega)
        (actual_disc_neg h hN hcop H w J G₀ d L hu hD).ne q
        (levelPrime_ne_detecting s i) z x).1
      let P := pointOfSupport s B z x
      let sign : Coefficients hN H w := C.alpha q (levelDivisor i) (-1)
      have hl : f q (rightConj v (atRep P.z q (root P.y))) =
          sign * f q (atRep P.z q (root P.y)) :=
        split_schwartz (m₀ := m) s C i (levelDivisor i) P htr
      change pointWeight A f χ (stepPoint _ (splitAdele_order s i) P) =
        (G₀.atkinSign q.val : Coefficients hN H w) * pointWeight A f χ P
      refine (stepPoint_weight A f χ q v hmem (splitAdele_order s i) P sign hl).trans ?_
      apply congrArg (fun a : Coefficients hN H w => a * pointWeight A f χ P)
      have hnorm := norm_single h hN H C hn q
        (fun hm => (discriminantDisjoint H q hm).2.1 (levelDivisor i))
        v _ (splitUnit_valuation (N := N) h q (levelPrime_ne_detecting s i))
      change (χ (single _ q v) : Coefficients hN H w) = _ at hnorm
      have hpar := levelRoots_parity hN H w q (levelDivisor i)
      change sign = ((w q.val : ℤ) : Coefficients hN H w) *
        (jacobiSym (-(m : ℤ)) q.val : Coefficients hN H w) ^ N.factorization q.val at hpar
      have hq : jacobiSym (-(m : ℤ)) q.val = 1 := level_symbol H i
      have hsign : (w q.val : ℤ) = G₀.atkinSign q.val := hSign i
      rw [hnorm, hpar, hq]
      simp [hsign]

theorem actual_uniformizer_weight
    (B : SupportBridge (actualStageAt h hN hcop H w J G₀ d L hu) (D : ℤ))
    (P : actualOrbits hN H w (actualStageAt h hN hcop H w J G₀ d L hu) D) :
    supportOrbitWeight (actualStageAt h hN hcop H w J G₀ d L hu) (uniformizerMove hN H w _ B P) =
      supportOrbitWeight (actualStageAt h hN hcop H w J G₀ d L hu) P := by
  let s := actualStageAt h hN hcop H w J G₀ d L hu
  let q := detectingPrime ell
  let hn := exceptionalProduct_ne_zero hN H
  let C := levelRoots hN H w
  let A := actualPhase hN H w
  let f := actualFactors h hN H w
  let χ := actualNorm h hN H w
  let v := divisionUnit h
  let cov := levelNormCovariance h hN C hn (discriminantDisjoint H)
  obtain ⟨z,x⟩ := P
  induction x using Quotient.inductionOn with
  | _ x =>
    generalize he : uniformizerMove hN H w s B ⟨z, Quotient.mk _ x⟩ = Q
    obtain ⟨z',x'⟩ := Q
    induction x' using Quotient.inductionOn with
    | _ x' =>
      rw [actual_weight_mk h hN hcop H w J G₀ d L hu B z' x',
        actual_weight_mk h hN hcop H w J G₀ d L hu B z x]
      rw [pointWeight_rel A f χ cov (orbitMove_rel s B _ _ z x z' x' he)]
      have hmem : q ∈ A.places := (mem_exceptionalPlaces m N ell hn q).mpr (dvd_mul_left _ _)
      let P := pointOfSupport s B z x
      have hl : f q (rightConj v (atRep P.z q (root P.y))) =
          (-1 : Coefficients hN H w) * f q (atRep P.z q (root P.y)) :=
        division_local_schwartz (m₀ := m) s C P
      change pointWeight A f χ (stepPoint _ (divisionAdele_order s) P) = pointWeight A f χ P
      refine (stepPoint_weight A f χ q v hmem (divisionAdele_order s) P (-1) hl).trans ?_
      have hnorm := norm_single h hN H C hn q
        (fun hm => (discriminantDisjoint H q hm).1 rfl) v 1 (divisionUnit_valuation h)
      change (χ (single _ q v) : Coefficients hN H w) = (jacobiSym (-(m : ℤ)) ell : Coefficients hN H w) ^ 1 at hnorm
      rw [hnorm, H.inert]
      simp

variable {Cl : Type}
variable (A : OrbitFibers (actualStageAt h hN hcop H w J G₀ d L hu).visibility
  (index (actualStageAt h hN hcop H w J G₀ d L hu) (D : ℤ)) N.primeFactors.card Cl)
variable (hA : A.orientation =
  orientation (actualStageAt h hN hcop H w J G₀ d L hu)
    (actualOrientationBridge h hN hcop H w J G₀ d L hu hD hF))

/-- The per-orbit input of DatumAt on the actual stage. -/
def normalizers
    (hSign : ∀ i : Fin N.primeFactors.card, (w (levelPrime N i).val : ℤ) = G₀.atkinSign (levelPrime N i).val)
    (hL : ∀ i : Fin N.primeFactors.card, L • (PMAdelic.geometry J G₀).cusp (levelPrime N i).val = 0) :
    Normalizers (actualStageAt h hN hcop H w J G₀ d L hu).G d L
      (actualStageAt h hN hcop H w J G₀ d L hu).weights u hu A := by
  let s := actualStageAt h hN hcop H w J G₀ d L hu
  let B := actualOrientationBridge h hN hcop H w J G₀ d L hu hD hF
  let ω := N.primeFactors.card
  let moves : Fin (ω + 1) → Equiv.Perm (actualOrbits hN H w s D) :=
    Fin.lastCases (uniformizerMove hN H w s B) (atkinMove hN H w s B)
  have hflip (i : Fin (ω+1)) (P : actualOrbits hN H w s D) :
      A.orientation (moves i P) = O7Actual.flip i (A.orientation P) := by
    rw [hA]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [moves, Fin.lastCases_last] using
        division_orientation s B (actual_disc_detecting h hN hcop H w J G₀ d L hu hD) P
    · simpa only [moves, Fin.lastCases_castSucc] using
        split_orientation s B j (actual_disc_neg h hN hcop H w J G₀ d L hu hD).ne hD.2.2.2.2.2
          (actual_disc_split h hN hcop H w J G₀ d L hu hD hF j) P
  let perm (i : Fin (ω + 1)) := fiberPerm A.fiber i (moves i) (hflip i)
  have hperm (i : Fin (ω + 1)) (t : Orientations ω) (c : Cl) :
      A.param (O7Actual.flip i t, perm i t c) = moves i (A.param (t,c)) :=
    fiberPerm_apply A.fiber i (moves i) (hflip i) t c
  refine ⟨perm, (fun i => (levelPrime N i).val), (fun i => (levelPrime N i).prop),
    levelPrime_exp hN, hL, ?_, ?_, ?_, ?_⟩
  · intro i t c
    change (A.param (O7Actual.flip i.castSucc t, perm i.castSucc t c)).1 =
      (PMAdelic.geometry J G₀).atkin (levelPrime N i).val (levelPrime N i).prop
        (levelPrime_exp hN i) (A.param (t,c)).1
    have hm : moves i.castSucc = atkinMove hN H w s B i := by
      simp only [moves, Fin.lastCases_castSucc]
    rw [hperm, hm]
    exact atkinMove_class h hN hcop H w J G₀ d L hu B i (A.param (t,c))
  · intro i t c
    change supportOrbitWeight s (A.param (O7Actual.flip i.castSucc t, perm i.castSucc t c)) =
      (G₀.atkinSign (levelPrime N i).val : Coefficients hN H w) * supportOrbitWeight s (A.param (t,c))
    have hm : moves i.castSucc = atkinMove hN H w s B i := by
      simp only [moves, Fin.lastCases_castSucc]
    rw [hperm, hm]
    exact actual_atkin_weight h hN hcop H w J G₀ d L hu hD hF hSign i (A.param (t,c))
  · intro t c
    change (A.param (O7Actual.flip (Fin.last ω) t, perm (Fin.last ω) t c)).1 =
      (PMAdelic.geometry J G₀).uniformizer (A.param (t,c)).1
    have hm : moves (Fin.last ω) = uniformizerMove hN H w s B := by
      simp only [moves, Fin.lastCases_last]
    rw [hperm, hm]
    exact uniformizerMove_class h hN hcop H w J G₀ d L hu B (A.param (t,c))
  · intro t c
    change supportOrbitWeight s (A.param (O7Actual.flip (Fin.last ω) t, perm (Fin.last ω) t c)) =
      supportOrbitWeight s (A.param (t,c))
    have hm : moves (Fin.last ω) = uniformizerMove hN H w s B := by
      simp only [moves, Fin.lastCases_last]
    rw [hperm, hm]
    exact actual_uniformizer_weight h hN hcop H w J G₀ d L hu B (A.param (t,c))

/-- Direct entry point for any independently constructed Picard fibers. -/
def ofPicardFibers
    (F : PicardFibers (actualStageAt h hN hcop H w J G₀ d L hu)
      (actualOrientationBridge h hN hcop H w J G₀ d L hu hD hF) Cl)
    (hSign : ∀ i : Fin N.primeFactors.card, (w (levelPrime N i).val : ℤ) = G₀.atkinSign (levelPrime N i).val)
    (hL : ∀ i : Fin N.primeFactors.card, L • (PMAdelic.geometry J G₀).cusp (levelPrime N i).val = 0) :
    Normalizers (actualStageAt h hN hcop H w J G₀ d L hu).G d L
      (actualStageAt h hN hcop H w J G₀ d L hu).weights u hu
      (⟨orientation (actualStageAt h hN hcop H w J G₀ d L hu)
        (actualOrientationBridge h hN hcop H w J G₀ d L hu hD hF), F⟩) :=
  normalizers h hN hcop H w J G₀ d L hu hD hF _ rfl hSign hL

end ActualMoves

end ZInQ.Manuscript.RC.O7Normalizers

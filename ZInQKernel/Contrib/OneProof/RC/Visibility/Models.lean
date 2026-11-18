import ZInQKernel.Contrib.OneProof.RC.Visibility.Inputs
import ZInQKernel.Contrib.OneProof.RC.Visibility.Witness
import ZInQKernel.Contrib.OneProof.RC.Visibility.Theta

/-!
# Lane RC23: (O.7) for the genuine `λ`, and `VisibilityInputs D` from the theta side

Manuscript (11/5), Appendix F, proof of Proposition `ex:app-theta-comparison` (tex 9265–9296):

"Writing `χ_F([a]) = χ_{h_*}(N_{F/ℚ} a)`, `z_a = [a z₀]`, equivariance gives the exact finite-sum identity
`∑_{[a]} χ_F([a]) P_M(z_a) = λ_M(\overline{L ∑_{[a]} χ_F([a]) π(x_D^{[a]})}) = λ_M(\overline{L P_D})` in
`ℤ/2^M`. […] Additivity, specialization, and multiplication by the fixed integer `L` commute with this
finite sum."

This file joins the two halves of the lane:
* the theta side (`Visibility/Theta.lean`): the finite theta coefficient (O.4) at one stage, and
  (O.7) from the comparison argument (orbit parametrization, torsor weights, the reference-tuple
  reduction identity, orientation signs, stabilizers) and phase removal;
* the point side (`Visibility/Genus.lean`): `λ_θ(D) = lamOf …`, the stage map applied to `L` times the
  genuine genus point `P_D = ∑_σ χ(σ) σ(y)`.

Results:
* `kummer_heegnerSum` — **PROVED** (tex 9283–9291, "additivity … commute with this finite sum"): the stage
  map of `L P_D` is `∑_σ χ(σ) · (stage map of L σ(y))`.
* `kummerLift_reduction`, `lamOf_reduction` — **PROVED**: the reduction identity (the field
  `reduction` of `ComparisonCore` and `ComparisonInputs`, for `λ = lamOf`) follows from its
  **pointwise** form: a bijection `e` of the
  class-group torsor with `Gal(H₁/K)` carrying the genus character to `χ`, such that the integer lift
  `P_M(z_{t₀,c})` is congruent mod `2^M` to the stage map of `L σ_c(y)` — i.e. the supersingular point
  `z_{t₀,c}` is the reduction at `ℓ₀` of the Heegner conjugate `σ_c(y)` and `P_M = λ_M ∘ L π_{ℓ₀}`
  (PRINT: C. Cornut, D. Jetchev, *Liftings of reduction maps for quaternion algebras*, preprint (2010),
  §3.5 Theorem 3.1 and Corollary 3.2 (p. 9), §4.9 and §4.10 (p. 15), read in the preprint's text;
  tex 9195–9272; definition of `P_M`, tex 8476).
* `ThetaSide` — the **named input for the theta-form construction** (tex 8409–8621, 8418, 2081–2084):
  per stage a finite model of (O.4), and `a_θ(D)` an integer representative of the phase-removed
  coefficient `ζ⁻¹ H_M(mD)`. The theta side is not formalized here (it belongs to the construction of
  `ex:app-theta-form`); this is exactly what it must deliver to the comparison.
* `ComparisonCore`, `ComparisonCore.O7`, `thetaComparison_of_core` — the comparison argument of (O.7)
  (tex 9120–9370) at each admissible `(θ, D)`, and **PROVED** (O.7) in `𝒪` and after phase removal;
  `ComparisonInputs.toCore` and `nonvacuous_comparisonCore` (**PROVED**): the comparison argument holds
  in the concrete instance of `Visibility/Theta.lean`, with a non-trivial conclusion.
* `visibilityInputs_of_models` — **PROVED**: `VisibilityInputs D` from the genuine data of
  `visibilityInputs_of_genuine`, the theta side and the comparison argument (for `λ = lamOf`).
* `witnessLeaf_of_models` — **PROVED**: the wiring's `WitnessLeaf` from the same inputs, (O.2) at the
  witness read on `lamOf`, and the advancing stages.
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory

namespace ZInQ.Manuscript.RC.Visibility

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring ZInQ.Contrib.CloudB3RC53
  ZInQ.Contrib.CloudB3RC53.GenusOdd ZInQ.Contrib.CloudB3RC53.CST

/-! ## Field level -/

section FieldLevel

variable (E : WeierstrassCurve ℚ) {K : Type} [Field K] [NumberField K] {c : ℕ} [NeZero c]

/-- **PROVED (tex 9283–9291): additivity of the stage map over the unaveraged sum.** For an additive
`κ : E(H_c) → ℤ/2^M`, `κ(L P_χ) = ∑_{σ ∈ Gal(H_c/K)} χ(σ) κ(L σ(y))`. -/
theorem kummer_heegnerSum {M : ℕ} (L : ℕ) (χ : Pic (conductorOrder K c) →* ℂˣ)
    (y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point)
    (ev : letI := Classical.decEq (ringClassField (conductorOrder K c))
      (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point →+ ZMod (2 ^ M)) :
    letI := Classical.decEq (ringClassField (conductorOrder K c))
    ev (L • heegnerSum E χ y) =
      ∑ σ : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c),
        ((chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) : ZMod (2 ^ M)) *
          ev (L • galPt E σ y) := by
  let _ := Classical.decEq (ringClassField (conductorOrder K c))
  simp only [heegnerSum, Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [smul_comm, map_zsmul, zsmul_eq_mul]

/-- **PROVED (tex 9265–9291): the reduction identity from its pointwise form, field level.** Let
`e : Cl ≃ Gal(H_c/K)` carry the genus character `χ_F` to `χ` (`χ_F(c) = χ(e c)`), and let the integer
lifts `P(c)` satisfy `P(c) ≡ val κ(L e(c)(y)) (mod 2^M)`. Then in any commutative ring `O`,
`∑_c χ_F(c) P(c) ≡ val κ(L P_χ) (mod 2^M O)`. -/
theorem kummerLift_reduction {M L : ℕ} (χ : Pic (conductorOrder K c) →* ℂˣ)
    (y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point)
    (ev : letI := Classical.decEq (ringClassField (conductorOrder K c))
      (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point →+ ZMod (2 ^ M))
    {O : Type*} [CommRing O] {Cl : Type*} [Fintype Cl]
    (e : Cl ≃ (ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c)))
    (χF : Cl → O)
    (hχF : ∀ c', χF c' = ((chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm (e c')) : ℤ) : O))
    (Pz : Cl → ℤ)
    (hP : ∀ c', (2 : ℤ) ^ M ∣ Pz c' -
      (letI := Classical.decEq (ringClassField (conductorOrder K c))
       ((ev (L • galPt E (e c') y)).val : ℤ))) :
    (2 : O) ^ M ∣ ∑ c', χF c' * (Pz c' : O) - (kummerLift E M L χ y ev : O) := by
  let _ := Classical.decEq (ringClassField (conductorOrder K c))
  set s : (ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c)) → ℤ :=
    fun σ => chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) with hs
  set v : (ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c)) → ℤ :=
    fun σ => ((ev (L • galPt E σ y)).val : ℤ) with hv
  -- the integer identity modulo `2^M`
  have hA : (2 : ℤ) ^ M ∣ ∑ σ, s σ * v σ - kummerLift E M L χ y ev := by
    have h2 : ((2 : ℤ) ^ M) = ((2 ^ M : ℕ) : ℤ) := by push_cast; ring
    rw [h2, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have : NeZero (2 ^ M) := ⟨by positivity⟩
    have hval : ∀ z : ZMod (2 ^ M), (((z.val : ℤ)) : ZMod (2 ^ M)) = z := fun z => by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    simp only [hs, hv, kummerLift, Int.cast_sub, Int.cast_sum, Int.cast_mul, hval]
    rw [kummer_heegnerSum E L χ y ev, sub_self]
  have hB : (2 : ℤ) ^ M ∣ ∑ c', s (e c') * Pz c' - ∑ c', s (e c') * v (e c') := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun c' _ => ?_
    rw [← mul_sub]
    exact dvd_mul_of_dvd_right (hP c') _
  have hre : ∑ c', s (e c') * v (e c') = ∑ σ, s σ * v σ :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hC : (2 : ℤ) ^ M ∣ ∑ c', s (e c') * Pz c' - kummerLift E M L χ y ev := by
    have := dvd_add hB hA
    rwa [hre, sub_add_sub_cancel] at this
  have hcast := map_dvd (Int.castRingHom O) hC
  simp only [map_sub, map_sum, map_mul, map_pow, eq_intCast, Int.cast_ofNat] at hcast
  convert hcast using 3 with c'
  rw [hχF c']

end FieldLevel

/-! ## Data level: the selected genus data -/

section Data

variable {E : WeierstrassCurve ℚ}
  {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {hstar : ℤ}

/-- **PROVED (tex 9265–9291): the reduction identity for `λ = lamOf`, from its pointwise form.** If the
genus datum `dat` of `D` is the selected one, `e : Cl ≃ Gal(H₁/K_D)` carries the genus character
`χ_F` to `dat.χ`, and the integer lifts `P(c)` of `P_M(z_{t₀,c})` are congruent mod `2^{M_θ}` to the
stage map of `L σ_c(y)` (the supersingular point `z_{t₀,c}` is the reduction of the Heegner conjugate
`σ_c(y)`: PRINT Cornut–Jetchev, preprint (2010), §3.5 Theorem 3.1, Corollary 3.2 (p. 9), §§4.9–4.10
(p. 15); `P_M = λ_M ∘ L π_{ℓ₀}`, tex 8476), then
`∑_c χ_F(c) P(c) ≡ λ_θ(D) (mod 2^{M_θ} 𝒪)` — the field `reduction` of `ComparisonCore` (and of
`ComparisonInputs`). -/
theorem lamOf_reduction (Mθ : ℕ → ℕ) (L : ℕ)
    (selG : (h : ℤ) → Option (HeegnerDatum E f Lat κ (h * hstar) 1 hstar))
    (ev : StageKummer E f Lat κ hstar Mθ) (θ : ℕ) {Dd : ℤ}
    (dat : HeegnerDatum E f Lat κ (Dd * hstar) 1 hstar) (hsel : selG Dd = some dat)
    {O : Type*} [CommRing O] {Cl : Type*} [Fintype Cl]
    (e : letI := dat.field
      letI := dat.nf
      letI := dat.nz
      Cl ≃ (ringClassField (conductorOrder dat.K 1) ≃ₐ[dat.K]
        ringClassField (conductorOrder dat.K 1)))
    (χF : Cl → O)
    (hχF : letI := dat.field
      letI := dat.nf
      letI := dat.nz
      ∀ c', χF c' =
        ((chiSign dat.χ ((ringClassArtinEquiv (conductorOrder dat.K 1)).symm (e c')) : ℤ) : O))
    (Pz : Cl → ℤ)
    (hP : letI := dat.field
      letI := dat.nf
      letI := dat.nz
      letI := Classical.decEq (ringClassField (conductorOrder dat.K 1))
      ∀ c', (2 : ℤ) ^ Mθ θ ∣ Pz c' - ((ev θ Dd dat (L • galPt E (e c') dat.y)).val : ℤ)) :
    (2 : O) ^ Mθ θ ∣ ∑ c', χF c' * (Pz c' : O) - (lamOf Mθ L selG ev θ Dd : O) := by
  unfold lamOf
  rw [hsel]
  exact (letI := dat.field; letI := dat.nf; letI := dat.nz
    kummerLift_reduction E dat.χ dat.y (ev θ Dd dat) e χF hχF Pz hP)

end Data

/-! ## The split of (O.7): the theta side (a named input) and the comparison argument -/

/-- **Named input: the theta side** — what the theta-form construction (Proposition
`ex:app-theta-form`, tex 8409–8621, and the phase removal of tex 2081–2084, 2538) must deliver, in the
form the comparison consumes. A coefficient ring `𝒪` (the valuation ring of the fixed character field,
tex 8567–8570) in which `2^{M}𝒪 ∩ ℤ = 2^{M}ℤ` at every stage precision; at every stage `θ` a finite
model `S θ` of (O.4) over the definite quaternion algebra `ℍ[ℚ, a_θ, 0, b_θ]` (`ThetaStage`: the
supersingular classes, the unit groups `R_z^×` with `|R_z^×| ∣ c₀`, the weights `f(z⁻¹xz)` invariant under
`R_z^×`, the norm-character values `χ_{h_*}(Nrd z)`, integer lifts of `P_M(z)`, finite supports); and for
every admissible `(θ, D)` a unit phase `ζ_θ(D)` such that the integer `a_θ(D)` represents the
phase-removed coefficient: `ζ_θ(D) a_θ(D) ≡ H_M(mD) (mod 2^{M_θ} 𝒪)`, `m = |h_*| = −h_*`
(`a_M(D) = H_M(mD)`, tex 8418). Kind: ELLIOT (the construction) — to be discharged by the theta-form
construction; the comparison below only reads `thetaCoeff (S θ)` at `mD`. -/
structure ThetaSide {ℓ : ℕ} (D : RCData ℓ) (O : Type*) [CommRing O] where
  /-- the first parameter of the quaternion algebra at stage `θ` -/
  aq : ℕ → ℚ
  /-- the second parameter of the quaternion algebra at stage `θ` -/
  bq : ℕ → ℚ
  /-- the finite model of (O.4) at stage `θ` -/
  S : ∀ θ, ThetaStage O (aq θ) (bq θ)
  /-- the unit phase `ζ_θ(D)` -/
  ζ : ℕ → ℤ → O
  phase_unit : ∀ θ Dd, D.admissible θ Dd → IsUnit (ζ θ Dd)
  /-- `a_θ(D)` is an integer representative of the phase-removed coefficient `ζ⁻¹ H_M(mD)` -/
  coeff : ∀ θ Dd, D.admissible θ Dd →
    (2 : O) ^ D.Mθ θ ∣ ζ θ Dd * (D.aθ θ Dd : O) - thetaCoeff (S θ) ((-D.hstar * Dd : ℤ) : ℚ)
  /-- `2^{M_θ} 𝒪 ∩ ℤ = 2^{M_θ} ℤ` (GLUE: `𝒪` is a 2-adically separated ring containing `ℤ` with
  `2^M 𝒪 ∩ ℤ = 2^M ℤ`, e.g. the valuation ring of a finite extension of `ℚ₂`, or `ℤ`) -/
  ring_two : ∀ θ (z : ℤ), (2 : O) ^ D.Mθ θ ∣ (z : O) → (2 : ℤ) ^ D.Mθ θ ∣ z

open ThetaStage in
/-- **The comparison argument of (O.7)** at one stage and one `D` (Proposition
`ex:app-theta-comparison`, proof, tex 9120–9370), for a finite model `S` of (O.4), the norm `n = mD`,
a phase `ζ` and an integer `λ`: the orbit parametrization by orientation tuples × class-group torsor
(ELLIOT, tex 9136–9170), the weights along the torsor (ELLIOT, tex 9171–9194, 9297–9305), the
reduction identity at the reference tuple (PRINT Cornut–Jetchev + ELLIOT, tex 9195–9296; for
`λ = lamOf` it follows from its pointwise form, `lamOf_reduction`), the orientation changes (ELLIOT,
tex 9329–9364), the stabilizers `𝒪_F^× = {±1}` (ELLIOT/GLUE, tex 9308–9309), and the phase of the
reference tuple equal to `ζ` (tex 9318–9327). Same fields as `ComparisonInputs` without its theta-side
fields `representative` and `ring_two`, and with `ζ₀ t₀ = ζ` in place of `phase_unit`. -/
structure ComparisonCore {O : Type*} [CommRing O] {a b : ℚ} (S : ThetaStage O a b) (M : ℕ)
    (m D : ℤ) (ω : ℕ) (lam : ℤ) (ζ : O) where
  /-- the local orientation tuples (`2^{ω(N)+1}` of them) -/
  Tup : Type
  /-- the class-group torsor `Pic(𝒪_F)` -/
  Cl : Type
  [fintypeTup : Fintype Tup]
  [fintypeCl : Fintype Cl]
  card_Tup : Fintype.card Tup = 2 ^ (ω + 1)
  param : Tup × Cl ≃
    Σ z : S.X, MulAction.orbitRel.Quotient (S.G z) (S.supp z ((m * D : ℤ) : ℚ))
  ζ₀ : Tup → O
  χF : Cl → O
  weight : ∀ t c,
    S.χN (zc param (t, c)) * S.f (zc param (t, c)) (rep param (t, c)) = ζ₀ t * χF c
  t₀ : Tup
  reduction : (2 : O) ^ M ∣ ∑ c, χF c * (S.P (zc param (t₀, c)) : O) - (lam : O)
  orientation : ∀ t, (2 : O) ^ M ∣ ζ₀ t * ∑ c, χF c * (S.P (zc param (t, c)) : O) -
    ζ₀ t₀ * ∑ c, χF c * (S.P (zc param (t₀, c)) : O)
  stab : ∀ z (x : S.supp z ((m * D : ℤ) : ℚ)), Nat.card (MulAction.stabilizer (S.G z) x) = 2
  phase : ζ₀ t₀ = ζ

attribute [instance] ComparisonCore.fintypeTup ComparisonCore.fintypeCl

/-- **PROVED: (O.7) in `𝒪`** (tex 9112–9113): `H_M(mD) ≡ c₀ 2^{ω(N)} ζ λ (mod 2^M 𝒪)`, from the
comparison argument (lane helper `O7_of_inputs`). -/
theorem ComparisonCore.O7 {O : Type*} [CommRing O] {a b : ℚ} {S : ThetaStage O a b} {M : ℕ}
    {m D : ℤ} {ω : ℕ} {lam : ℤ} {ζ : O} (I : ComparisonCore S M m D ω lam ζ) :
    (2 : O) ^ M ∣ thetaCoeff S ((m * D : ℤ) : ℚ) - (Odd.c0 : O) * 2 ^ ω * ζ * (lam : O) := by
  have h := O7_of_inputs S M m D ω I.card_Tup I.param I.ζ₀ I.χF I.weight I.t₀ lam I.reduction
    I.orientation I.stab
  rwa [I.phase] at h

/-- The comparison argument of a full set of `ComparisonInputs` (forgetting its theta-side fields
`representative`, `ring_two`; the phase is that of the reference tuple). Definition. -/
def ComparisonInputs.toCore {O : Type*} [CommRing O] {a b : ℚ} {S : ThetaStage O a b} {M : ℕ}
    {m D : ℤ} {ω : ℕ} {lam aθ : ℤ} (I : ComparisonInputs S M m D ω lam aθ) :
    ComparisonCore S M m D ω lam (I.ζ₀ I.t₀) where
  Tup := I.Tup
  Cl := I.Cl
  card_Tup := I.card_Tup
  param := I.param
  ζ₀ := I.ζ₀
  χF := I.χF
  weight := I.weight
  t₀ := I.t₀
  reduction := I.reduction
  orientation := I.orientation
  stab := I.stab
  phase := rfl

/-- **PROVED (non-vacuity of `ComparisonCore`).** The comparison argument holds in the concrete
instance of `Visibility/Theta.lean` (`ℍ[ℚ, −1, 0, −3]`, `x₀ = 2i + j`, `x₀² = −7`, `m = 7`, `D = 1`,
two orientation tuples, trivial class group, `λ = 1`), and its conclusion (O.7) is not trivial there:
`H(7) = c₀`, which `2^{10}` does not divide. -/
theorem nonvacuous_comparisonCore (M : ℕ) :
    (2 : ℤ) ^ M ∣ thetaCoeff ThetaExample.stage ((7 * 1 : ℤ) : ℚ) -
        (Odd.c0 : ℤ) * 2 ^ 0 * ((ThetaExample.inputs M).ζ₀ (ThetaExample.inputs M).t₀) * 1 ∧
      ¬ (2 : ℤ) ^ 10 ∣ thetaCoeff ThetaExample.stage ((7 * 1 : ℤ) : ℚ) := by
  refine ⟨?_, ThetaExample.nonvacuous_O7.2.2⟩
  have h := (ThetaExample.inputs M).toCore.O7
  simpa using h

/-- **PROVED: (O.7) after phase removal, as the wiring consumes it** (`Odd.ThetaComparison`), from the
theta side (`ThetaSide`, named input) and the comparison argument at every admissible `(θ, D)` with
the theta side's phase. -/
theorem thetaComparison_of_core {ℓ : ℕ} {D : RCData ℓ} {O : Type*} [CommRing O]
    (T : ThetaSide D O) (lam : ℕ → ℤ → ℤ) (ω : ℕ)
    (hcore : ∀ θ Dd, D.admissible θ Dd →
      ComparisonCore (T.S θ) (D.Mθ θ) (-D.hstar) Dd ω (lam θ Dd) (T.ζ θ Dd)) :
    Odd.ThetaComparison D.Mθ D.aθ lam D.admissible ω := fun θ Dd hD =>
  ⟨1, odd_one, phase_removal (T.phase_unit θ Dd hD) (hcore θ Dd hD).O7 (T.coeff θ Dd hD)
    (T.ring_two θ)⟩

/-! ## `VisibilityInputs D` from the theta side and the comparison argument -/

/-- **`VisibilityInputs D` (PROVED)** from the inputs of `visibilityInputs_of_genuine`, with (O.7)
replaced by the theta side (`ThetaSide`, the named input for the theta-form construction) and the
comparison argument at every admissible `(θ, D)` for `λ = lamOf` (`ComparisonCore`; its field
`reduction` can be supplied by `lamOf_reduction` from the pointwise Cornut–Jetchev identity). -/
theorem visibilityInputs_of_models {ℓ : ℕ} (D : RCData ℓ) [(Ecurve ℓ).IsElliptic]
    (P : Prints) (hArtin : ArtinFactorization)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat) (hNC : IsNonCMLattice Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ)
    (hgp : GenusPartner (Ecurve ℓ) D.hstar)
    (selG : (h : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ (h * D.hstar) 1 D.hstar))
    (hjgen : ∀ θ : ℕ, ∀ Dd : ℤ, D.admissible θ Dd →
      D.jgen Dd = jgenOf (Ecurve ℓ) f Lat κ D.hstar selG Dd)
    {L : ℕ} (hL : MultiplierKillsNativeTorsion (Ecurve ℓ) f Lat κ D.hstar L)
    (ev : StageKummer (Ecurve ℓ) f Lat κ D.hstar D.Mθ)
    (hprep : AdmissiblePrepared D) (hsign : AdmissibleOddSign D) (ω : ℕ)
    {O : Type*} [CommRing O] (T : ThetaSide D O)
    (hcore : ∀ θ Dd, D.admissible θ Dd →
      ComparisonCore (T.S θ) (D.Mθ θ) (-D.hstar) Dd ω (lamOf D.Mθ L selG ev θ Dd) (T.ζ θ Dd)) :
    VisibilityInputs D :=
  visibilityInputs_of_genuine D P hArtin hf hLat hNC hκ hgp selG hjgen hL ev hprep hsign ω
    (thetaComparison_of_core T _ ω hcore)

/-- **`RCSteps.visibility` ((O.8)) from the theta side and the comparison argument (PROVED).** -/
theorem visibilityTarget_of_models {ℓ : ℕ} (D : RCData ℓ) [(Ecurve ℓ).IsElliptic]
    (P : Prints) (hArtin : ArtinFactorization)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat) (hNC : IsNonCMLattice Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ)
    (hgp : GenusPartner (Ecurve ℓ) D.hstar)
    (selG : (h : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ (h * D.hstar) 1 D.hstar))
    (hjgen : ∀ θ : ℕ, ∀ Dd : ℤ, D.admissible θ Dd →
      D.jgen Dd = jgenOf (Ecurve ℓ) f Lat κ D.hstar selG Dd)
    {L : ℕ} (hL : MultiplierKillsNativeTorsion (Ecurve ℓ) f Lat κ D.hstar L)
    (ev : StageKummer (Ecurve ℓ) f Lat κ D.hstar D.Mθ)
    (hprep : AdmissiblePrepared D) (hsign : AdmissibleOddSign D) (ω : ℕ)
    {O : Type*} [CommRing O] (T : ThetaSide D O)
    (hcore : ∀ θ Dd, D.admissible θ Dd →
      ComparisonCore (T.S θ) (D.Mθ θ) (-D.hstar) Dd ω (lamOf D.Mθ L selG ev θ Dd) (T.ζ θ Dd)) :
    VisibilityTarget D :=
  visibilityTarget_of_inputs D (visibilityInputs_of_models D P hArtin hf hLat hNC hκ hgp selG hjgen hL
    ev hprep hsign ω T hcore)

/-- **The fixed visible witness from the theta side and the comparison argument (PROVED):** the
wiring's `WitnessLeaf` from (O.7) so obtained, (O.2) at the witness read on `lamOf`, and the advancing
stages. -/
theorem witnessLeaf_of_models {ℓ : ℕ} (W : WData ℓ)
    {E : WeierstrassCurve ℚ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} {hstar : ℤ} {L : ℕ}
    (selG : (h : ℤ) → Option (HeegnerDatum E f Lat κ (h * hstar) 1 hstar))
    (ev : StageKummer E f Lat κ hstar W.Mθ) (ω : ℕ)
    {O : Type*} [CommRing O] (T : ThetaSide W.toRCData O)
    (hcore : ∀ θ Dd, W.admissible θ Dd →
      ComparisonCore (T.S θ) (W.Mθ θ) (-W.hstar) Dd ω (lamOf W.Mθ L selG ev θ Dd) (T.ζ θ Dd))
    {Dw : ℤ} {cw : ℕ} (hO2 : WitnessValuation W (lamOf W.Mθ L selG ev) Dw cw)
    (hadv : Filter.Tendsto W.Mθ (W.stages : Filter ℕ) Filter.atTop) :
    WitnessLeaf W :=
  witnessLeaf_of_genuine W selG ev ω (thetaComparison_of_core T _ ω hcore) hO2 hadv

end ZInQ.Manuscript.RC.Visibility

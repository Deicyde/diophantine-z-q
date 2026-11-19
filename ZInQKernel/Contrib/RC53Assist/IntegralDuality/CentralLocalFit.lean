import ZInQKernel.Contrib.OneProof.RC.KummerMaps.ActualComplements
import ZInQKernel.Contrib.RC53Assist.CalibrationShape.CalibrationDischarge

/-!
# The actual central local conditions in the finite orthogonality interface

The finite orthogonality interface of the actual Selmer data pairs the coefficient module
`M_i(α)` with `M_i(α⁻¹)` and has three kinds of places: Kummer on `P`, full/zero on `S₀ - P`,
unramified on `S - S₀`.  The genuine central data use `S₀ = S`, `P = S` and the central
character.  This file records the exact fit:

* `charInv_centralChar`: the central character is its own inverse, so the orthogonal side of
  the interface is the same coefficient module and the same Kummer condition;
* `centralActLCondA_eq`, `centralActLCondB_eq`: at every place of the support both sides of the
  interface are the actual Kummer condition (no full, zero or unramified place occurs);
* `centralActLSelDataA_eq`, `centralActLSelDataB_eq`: the Selmer data of both sides are the
  genuine finite central Selmer data `simpleCentralSelData`;
* `centralActualCondition_eq_actLCondA`: the condition reduced from the compact Kummer condition
  is the interface condition;
* `centralLocalPerf`: at every place of the support, for every precision `i ≥ 1`, every local
  trace inducing an isomorphism on degree-two cohomology, and every truncated isotropy homotopy,
  the finite local orthogonal-complement map is a quasi-isomorphism.  The hypotheses are the
  local Milne print, the cochain local duality print, total complexity and the support
  condition at the places above two.  The unramified print is not needed.

No integral pairing, integral trace or integral orthogonality statement is asserted here.
-/

noncomputable section

set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.DerivedKummer.CentralLocalFit

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Duality (MilneLocalTateDualityKummerCharZero LocalTruncIsotropy)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral

section Character

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- The central coefficient character is its own inverse. -/
theorem charInv_centralChar (i : ℕ) (s : KS K S) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) :
    charInv (centralChar i s hs hs0) = centralChar i s hs hs0 := by
  refine MonoidHom.ext fun g => ?_
  rw [charInv_apply]
  have hΨ : movingCharS i 1 g = 1 := by simp [movingCharS, ZInQ.Manuscript.RC.HeegnerAlgebra.movingChar]
  change (intUnitsTo (Acoef i) (quadChar s hs hs0 g) * movingCharS i 1 g)⁻¹ =
    intUnitsTo (Acoef i) (quadChar s hs hs0 g) * movingCharS i 1 g
  rw [hΨ, mul_one, ← map_inv, Int.units_inv_eq_self]

end Character

section Central

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (D : GenuineKummerData K E₀ hZ) (i : ℕ) [NeZero i]

attribute [local instance] acoefTop acoefTop_discrete

omit [NeZero i] in
/-- The roots of unity of the central precision, from full two-power torsion. -/
theorem centralRoots : HasRootsOfUnity K D.S (2 ^ i) :=
  hasRootsOfUnity_of_fullTorsion K D.S D.W (2 ^ i) (D.hFull i)

omit [NeZero i] in
/-- The central character is the quadratic character at every place. -/
theorem centralQuad : ∀ v ∈ D.S,
    IsLocallyQuadAt (S := D.S) i (centralChar i D.s D.hs D.hs0) (quadChar D.s D.hs D.hs0) v :=
  fun v _ => isLocallyQuadAt_centralChar i D.s D.hs D.hs0 v

/-- At every place of the support the interface condition is the actual Kummer condition. -/
theorem centralActLCondA_eq (v : Places K D.S) :
    actLCondA (subset_refl D.S) D.W i D.s D.hs D.hs0 (D.hFull i) D.S
        (centralChar i D.s D.hs D.hs0) (centralQuad D i) v =
      actualKummerAtS (subset_refl D.S) D.W i D.s D.hs D.hs0 (centralChar i D.s D.hs D.hs0)
        (D.hFull i) v (isLocallyQuadAt_centralChar i D.s D.hs D.hs0 v.1) :=
  actLCondA_of_P (subset_refl D.S) D.W i D.s D.hs D.hs0 (D.hFull i) D.S
    (centralChar i D.s D.hs D.hs0) (centralQuad D i) v.2 v.2

/-- At every place of the support the orthogonal interface condition is the actual Kummer
condition of the inverse character. -/
theorem centralActLCondB_eq (v : Places K D.S) :
    actLCondB (subset_refl D.S) D.W i D.s D.hs D.hs0 (D.hFull i) D.S
        (centralChar i D.s D.hs D.hs0) (centralQuad D i) v =
      actualKummerAtS (subset_refl D.S) D.W i D.s D.hs D.hs0
        (charInv (centralChar i D.s D.hs D.hs0)) (D.hFull i) v
        (isLocallyQuadAt_charInv (isLocallyQuadAt_centralChar i D.s D.hs D.hs0 v.1)) :=
  actLCondB_of_P (subset_refl D.S) D.W i D.s D.hs D.hs0 (D.hFull i) D.S
    (centralChar i D.s D.hs D.hs0) (centralQuad D i) v.2 v.2

/-- The condition reduced from the compact Kummer condition is the interface condition. -/
theorem centralActualCondition_eq_actLCondA (v : Places K D.S) :
    ZInQ.Contrib.RC53Assist.CalibrationShape.centralActualCondition D i v =
      (actLCondA (subset_refl D.S) D.W i D.s D.hs D.hs0 (D.hFull i) D.S
        (centralChar i D.s D.hs D.hs0) (centralQuad D i) v).U := by
  rw [centralActLCondA_eq]

/-- The Selmer data of the primitive side of the interface are the genuine central data. -/
theorem centralActLSelDataA_eq :
    galoisSelData K D.S (Acoef i) (finiteCentralModule D i)
        (actLDeltaA (subset_refl D.S) D.W i D.s D.hs D.hs0 (D.hFull i) D.S
          (centralChar i D.s D.hs D.hs0) (centralQuad D i)) =
      simpleCentralSelData D i := by
  simp only [simpleCentralSelData, actLDeltaA]
  congr 1
  apply congrArg (ofCondAt K D.S (Acoef i) (finiteCentralModule D i))
  funext v
  exact centralActLCondA_eq D i v

omit [NeZero i] in
/-- Changing the character along an equality does not change the Kummer Selmer data. -/
theorem kummerSelData_char_congr (α β : GKS K D.S →* (Acoef i)ˣ) [IsOpenKer α] [IsOpenKer β]
    (hβ : β = α)
    (qα : ∀ v : Places K D.S, IsLocallyQuadAt (S := D.S) i α (quadChar D.s D.hs D.hs0) v.1)
    (qβ : ∀ v : Places K D.S, IsLocallyQuadAt (S := D.S) i β (quadChar D.s D.hs D.hs0) v.1) :
    galoisSelData K D.S (Acoef i) (MinS (subset_refl D.S) D.W i β)
        (ofCondAt K D.S (Acoef i) (MinS (subset_refl D.S) D.W i β) fun v =>
          actualKummerAtS (subset_refl D.S) D.W i D.s D.hs D.hs0 β (D.hFull i) v (qβ v)) =
      galoisSelData K D.S (Acoef i) (MinS (subset_refl D.S) D.W i α)
        (ofCondAt K D.S (Acoef i) (MinS (subset_refl D.S) D.W i α) fun v =>
          actualKummerAtS (subset_refl D.S) D.W i D.s D.hs D.hs0 α (D.hFull i) v (qα v)) := by
  subst hβ
  rfl

/-- The Selmer data of the orthogonal side of the interface are again the genuine central
data: the self-duality fit of the central character. -/
theorem centralActLSelDataB_eq :
    galoisSelData K D.S (Acoef i)
        (MinS (subset_refl D.S) D.W i (charInv (centralChar i D.s D.hs D.hs0)))
        (actLDeltaB (subset_refl D.S) D.W i D.s D.hs D.hs0 (D.hFull i) D.S
          (centralChar i D.s D.hs D.hs0) (centralQuad D i)) =
      simpleCentralSelData D i := by
  have hB : actLDeltaB (subset_refl D.S) D.W i D.s D.hs D.hs0 (D.hFull i) D.S
      (centralChar i D.s D.hs D.hs0) (centralQuad D i) =
      ofCondAt K D.S (Acoef i)
        (MinS (subset_refl D.S) D.W i (charInv (centralChar i D.s D.hs D.hs0))) fun v =>
          actualKummerAtS (subset_refl D.S) D.W i D.s D.hs D.hs0
            (charInv (centralChar i D.s D.hs D.hs0)) (D.hFull i) v
            (isLocallyQuadAt_charInv (isLocallyQuadAt_centralChar i D.s D.hs D.hs0 v.1)) := by
    simp only [actLDeltaB]
    apply congrArg (ofCondAt K D.S (Acoef i) _)
    funext v
    exact centralActLCondB_eq D i v
  rw [hB, kummerSelData_char_congr D i (centralChar i D.s D.hs D.hs0) _
    (charInv_centralChar i D.s D.hs D.hs0)
    (fun v => isLocallyQuadAt_centralChar i D.s D.hs D.hs0 v.1)]
  rfl

open scoped Classical in
/-- At every place of the support and every precision `i ≥ 1`, the finite local
orthogonal-complement map of the actual central Kummer condition and its orthogonal condition
is a quasi-isomorphism, for every admissible local trace and every truncated isotropy
homotopy.  Places above two are included. -/
theorem centralLocalPerf (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    (v : Places K D.S)
    (trv : (localCx (Acoef i) (GKS K D.S) (fun v : Places K D.S => Gloc K v.1)
      (fun v => locMap K D.S v.1)
        (InflMod (subset_refl D.S) (Tate1 (Acoef i) (centralRoots D i))) v).X 2 →ₗ[Acoef i]
          Acoef i)
    (htrv : ∀ z, trv ((localCx (Acoef i) (GKS K D.S) (fun v : Places K D.S => Gloc K v.1)
      (fun v => locMap K D.S v.1)
        (InflMod (subset_refl D.S) (Tate1 (Acoef i) (centralRoots D i))) v).d 1 2 rfl z) = 0)
    (htrv2 : InducesIsoH2 trv)
    (J : LocalTruncIsotropy
      (actualKummerAtS (subset_refl D.S) D.W i D.s D.hs D.hs0 (centralChar i D.s D.hs D.hs0)
        (D.hFull i) v (isLocallyQuadAt_centralChar i D.s D.hs D.hs0 v.1)).i
      (actualKummerAtS (subset_refl D.S) D.W i D.s D.hs D.hs0
        (charInv (centralChar i D.s D.hs D.hs0)) (D.hFull i) v
        (isLocallyQuadAt_charInv (isLocallyQuadAt_centralChar i D.s D.hs D.hs0 v.1))).i
      (orthUrPair (subset_refl D.S) (Acoef i)
        (weilPairingM (S := D.S) D.W (centralRoots D i) (Acoef i) (centralChar i D.s D.hs D.hs0))
        (weilPairingM_smul (S := D.S) D.W (centralRoots D i) (Acoef i)
          (centralChar i D.s D.hs D.hs0)) v)) :
    QuasiIso (GHom.toCC (orthLocalMap
      (actualKummerAtS (subset_refl D.S) D.W i D.s D.hs D.hs0 (centralChar i D.s D.hs D.hs0)
        (D.hFull i) v (isLocallyQuadAt_centralChar i D.s D.hs D.hs0 v.1)).i
      (actualKummerAtS (subset_refl D.S) D.W i D.s D.hs D.hs0
        (charInv (centralChar i D.s D.hs D.hs0)) (D.hFull i) v
        (isLocallyQuadAt_charInv (isLocallyQuadAt_centralChar i D.s D.hs D.hs0 v.1))).i
      (orthUrPair (subset_refl D.S) (Acoef i)
        (weilPairingM (S := D.S) D.W (centralRoots D i) (Acoef i) (centralChar i D.s D.hs D.hs0))
        (weilPairingM_smul (S := D.S) D.W (centralRoots D i) (Acoef i)
          (centralChar i D.s D.hs D.hs0)) v) J trv htrv)) :=
  kummerPerPlace_perf_of_milne (subset_refl D.S) D.W i D.s D.hs D.hs0 (D.hFull i) v
    (centralRoots D i) (centralChar i D.s D.hs D.hs0) hM h524 hK D.hSfin h2
    (cycloInfl_isCyclotomicTwist_tate1 (subset_refl D.S) i (centralRoots D i))
    (isLocallyQuadAt_centralChar i D.s D.hs D.hs0 v.1) trv htrv htrv2 J

end Central

section IntegralConcentration

open ZInQ.Manuscript.RC53Assist.CentralKummer ZInQ.Manuscript.RC.LambdaCoef

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))
  (v : HeightOneSpectrum (𝓞 K)) [DecidableEq (v.adicCompletion K)]

attribute [local instance] levTop

/-- The integral compact Kummer condition at a finite place is concentrated in degrees zero
and one; this is the concentration input of the zero truncated isotropy homotopy. -/
theorem tateKummerCondition_vanishesOutside :
    ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.VanishesOutside (tateKummerCondition W hFull v)
      (fun n => n = 0 ∨ n = 1) := by
  intro n hn
  cases n with
  | ofNat j =>
    rcases j with _ | _ | j
    · exact absurd (Or.inl rfl) hn
    · exact absurd (Or.inr rfl) hn
    · change Subsingleton ↥(⊥ : Submodule ℤ_[2] (contCochain ℤ_[2] (Gloc K v)
        (ResMod (locMap K S v) (TateS K S W)) (j + 2)))
      infer_instance
  | negSucc j =>
    change Subsingleton PUnit.{1}
    infer_instance

end IntegralConcentration

end ZInQ.Contrib.RC53Assist.DerivedKummer.CentralLocalFit

import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.Adapter

/-!
# A trace-one cycle from compatible finite local invariant classes

At level a take the class of invariant 1 modulo 2^a. Its reduction is the
prescribed class one level down. Lift the boundary between representatives
and subtract it before passing to the inverse limit of continuous cochains.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.PlaceAboveTwo

open CategoryTheory NumberField IsDedekindDomain
open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.Duality
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralTrace

section Tower

variable (F : Type) [Field F]

private abbrev finiteCx (a : ℕ) :=
  finiteIntegralComplex (AbsoluteGaloisGroup F) (UnitsCoeff F) a

private abbrev cycles (a : ℕ) := LinearMap.ker ((finiteCx F a).d 2 3).hom

private abbrev lower (a : ℕ) := transitionCycle (AbsoluteGaloisGroup F) (UnitsCoeff F) a 2

/-- On cocycles the Tate transition is the roots-of-unity power map on the same values. -/
private theorem class_transition (a : ℕ) (c : cycles F (a + 1)) :
    actualMuH2Equiv F a (kerToH2 (lower F a c)) =
      finiteMuH2Transition F a (actualMuH2Equiv F (a + 1) (kerToH2 c)) := by
  simp only [actualMuH2Equiv, finiteMuH2Transition, kerToH2_apply,
    explicitCoeff2Equiv_apply, explicitCoeff2_mk]
  apply congrArg (H2pi (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a)))
  apply Subtype.ext
  funext p
  exact actualMuLevelEquiv_transition F a (cfun c.val ![p.1, p.2])

variable [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private def coordinate (a : ℕ) :=
  (actualMuH2Equiv F a).trans (FiniteTrace.finiteInvariant F (2 ^ a) (twoPower_isUnit F a))

private def oneClass (a : ℕ) := (coordinate F a).symm 1

private theorem coordinate_lower (a : ℕ) (c : cycles F (a + 1)) :
    coordinate F a (kerToH2 (lower F a c)) =
      (ZMod.castHom (pow_dvd_pow 2 a.le_succ) (ZMod (2 ^ a)))
        (coordinate F (a + 1) (kerToH2 c)) := by
  exact (congrArg (fun z => FiniteTrace.finiteInvariant F (2 ^ a) (twoPower_isUnit F a) z)
    (class_transition F a c)).trans
    (finiteInvariant_transition F a (actualMuH2Equiv F (a + 1) (kerToH2 c))).symm

private theorem lower_class (a : ℕ) (c : cycles F (a + 1))
    (hc : kerToH2 c = oneClass F (a + 1)) :
    kerToH2 (lower F a c) = oneClass F a := by
  apply (coordinate F a).injective
  let castDown := ZMod.castHom (pow_dvd_pow 2 a.le_succ) (ZMod (2 ^ a))
  calc
    coordinate F a (kerToH2 (lower F a c)) = castDown (coordinate F (a + 1) (kerToH2 c)) :=
      coordinate_lower F a c
    _ = castDown (coordinate F (a + 1) (oneClass F (a + 1))) :=
      congrArg (fun x => castDown (coordinate F (a + 1) x)) hc
    _ = castDown 1 := congrArg (fun t => castDown t) ((coordinate F (a + 1)).apply_symm_apply 1)
    _ = 1 := map_one castDown
    _ = coordinate F a (oneClass F a) := ((coordinate F a).apply_symm_apply 1).symm

private abbrev reps (a : ℕ) := {c : cycles F a // kerToH2 c = oneClass F a}

private theorem lift_rep (a : ℕ) (c : reps F a) :
    ∃ c' : reps F (a + 1), lower F a c'.val = c.val := by
  let G := AbsoluteGaloisGroup F
  let A := UnitsCoeff F
  obtain ⟨y, hy⟩ := kerToH2_surjective (k := ℤ_[2]) (G := G)
    (M := FiniteTateCoeff G A (a + 1)) (oneClass F (a + 1))
  have hd : kerToH2 (lower F a y - c.val) = 0 := by
    rw [map_sub, lower_class F a y hy, c.property, sub_self]
  obtain ⟨b, hb⟩ := (kerToH2_eq_zero_iff _).mp hd
  obtain ⟨t, ht⟩ := transitionCochains_surjective G A a 1 (actualMuTransition_surjective F a) b
  let boundary : cycles F (a + 1) := ⟨((finiteCx F (a + 1)).d 1 2).hom t, by
    have h := congrArg (fun f => f.hom t) ((finiteCx F (a + 1)).d_comp_d 1 2 3)
    change ((finiteCx F (a + 1)).d 2 3).hom (((finiteCx F (a + 1)).d 1 2).hom t) = 0
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h⟩
  have hbclass : kerToH2 boundary = 0 := (kerToH2_eq_zero_iff _).mpr ⟨t, rfl⟩
  refine ⟨⟨y - boundary, by rw [map_sub, hbclass, sub_zero, hy]⟩, Subtype.ext ?_⟩
  change ((transitionCochains G A a).f 2).hom
    (y.val - ((finiteCx F (a + 1)).d 1 2).hom t) = c.val.val
  rw [map_sub, transitionCochains_d, ht, hb]
  change (lower F a y).val - ((lower F a y).val - c.val.val) = c.val.val
  abel

/-- A single integral cycle realizes all normalized finite classes, including level zero. -/
theorem exists_normalized_cycle :
    ∃ z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom,
      ∀ a, actualMuH2Reduction F a z =
        (FiniteTrace.finiteInvariant F (2 ^ a) (twoPower_isUnit F a)).symm 1 := by
  classical
  let G := AbsoluteGaloisGroup F
  let A := UnitsCoeff F
  obtain ⟨c₀, h₀⟩ := kerToH2_surjective (k := ℤ_[2]) (G := G)
    (M := FiniteTateCoeff G A 0) (oneClass F 0)
  let c : ∀ a, reps F a := fun a =>
    Nat.rec (motive := reps F) ⟨c₀, h₀⟩ (fun i r => (lift_rep F i r).choose) a
  let u := fun a => (c a).val.val
  have compat (a : ℕ) : ((transitionCochains G A a).f 2).hom (u (a + 1)) = u a :=
    congrArg Subtype.val ((lift_rep F a (c a)).choose_spec)
  let t := liftCompatibleCochains G A 2 u compat
  have closed : ((actualTraceComplex F).d 2 3).hom t = 0 := by
    apply integralCochain_ext G A 3
    intro a
    rw [reduceCochains_d, map_zero]
    change ((finiteCx F a).d 2 3).hom
      (((reduceCochains G A a).f 2).hom (liftCompatibleCochains G A 2 u compat)) = 0
    rw [liftCompatibleCochains_projection]
    exact (c a).val.property
  let z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom := ⟨t, closed⟩
  refine ⟨z, fun a => ?_⟩
  have hp : reduceTwoCycle G A a z = (c a).val :=
    Subtype.ext (liftCompatibleCochains_projection G A 2 u compat a)
  change actualMuH2Equiv F a (kerToH2 (reduceTwoCycle G A a z)) = _
  rw [hp, (c a).property]
  exact (actualMuH2Equiv F a).apply_symm_apply _

/-- The actual integral local trace has a closed cochain of trace exactly one. -/
theorem exists_trace_one :
    ∃ z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom,
      AllCochainTrace.trv F z.val = 1 := by
  obtain ⟨z, hz⟩ := exists_normalized_cycle F
  refine ⟨z, ?_⟩
  apply PadicInt.ext_of_toZModPow.mp
  intro a
  rw [AllCochainTrace.trv_finite_normalization, hz a, AddEquiv.apply_symm_apply, map_one]

end Tower

open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.RC53Assist.DKLocalAdapter
open ZInQ.Contrib.RC53Assist.IntegralDuality
open ZInQ.Manuscript.RC.KummerMaps ZInQ.Manuscript.RC.FibreDuality

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- Trace one at any finite place, with the project's global orientation. -/
theorem orientedTraceOne (w : HeightOneSpectrum (𝓞 K))
    [DecidableEq (w.adicCompletion K)] :
    ∃ z : (restrictedLineComplex (S := S) w).X 2,
      ((restrictedLineComplex (S := S) w).d 2 3).hom z = 0 ∧
        orientedLocalTrace (S := S) W w z = 1 := by
  obtain ⟨z, hz⟩ := exists_trace_one (w.adicCompletion K)
  let y := ((localLineCochainInv (S := S) W w).f 2).hom z.val
  have hc : ((restrictedLineComplex (S := S) w).d 2 3).hom y = 0 := by
    have h := congrArg (fun f => f.hom z.val) ((localLineCochainInv (S := S) W w).comm 2 3)
    have hdz : ((actualTraceComplex (w.adicCompletion K)).d 2 3).hom z.val = 0 := z.property
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hdz, map_zero] using h
  refine ⟨y, hc, ?_⟩
  have hb := congrArg (fun f => (f.f 2).hom z.val)
    (localLineCochainInv_map (S := S) W w)
  have he : ((localLineCochainMap (S := S) W w).f 2).hom y = z.val := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using hb
  change AllCochainTrace.trv (w.adicCompletion K)
    (((localLineCochainMap (S := S) W w).f 2).hom y) = 1
  rw [he]
  exact hz

/-- The existing integral local trace induces the degree-two isomorphism at every finite place. -/
theorem orientedTrace_inducesIsoH2
    (w : HeightOneSpectrum (𝓞 K))
    [DecidableEq (w.adicCompletion K)] :
    InducesIsoH2 (C := natCx (restrictedLineComplex (S := S) w))
      (orientedLocalTrace (S := S) W w) :=
  ⟨orientedLocalTrace_kernel W w, orientedTraceOne W w⟩

end ZInQ.Contrib.RC53Assist.PlaceAboveTwo

end

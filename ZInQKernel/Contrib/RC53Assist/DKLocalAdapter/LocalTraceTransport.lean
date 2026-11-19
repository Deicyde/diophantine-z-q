import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.LocalDuality
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.TraceUnitNormalization

/-!
# Local scalar trace transport on the fixed ordinary cone

The degree-two comparison uses the fixed cup product and the fixed local
condition. Trace differences factor through the coefficient differential.
The signed adjoint homotopy is lifted to the ordinary cone by projection
onto its first component. The extra cone term in this homotopy has total
local-condition degree three and vanishes by the zero-and-one support.
The degree-two cup of two local-condition elements is not asserted to be
zero as a cochain: only its scalar trace is zero.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.DKLocalAdapter.LocalTraceTransport

open CategoryTheory HomologicalComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Duality
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology (VanishesOutside)
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.SelfDualCore
open ZInQ.Contrib.RC53Assist.IntegralDuality

variable {R : Type} [CommRing R] {U L T : GCx R}

/-- The degree-three homotopy term vanishes on the local condition by support. -/
theorem traceHomotopyFun_iota_zero (ι : GHom U L) (P : GPair L L T)
    (hU : VanishesOutside U (fun n => n = 0 ∨ n = 1))
    (h : T.X 3 →ₗ[R] R) (i j : ℤ) (hij : j + 1 = i) (u : U.X i) :
    traceHomotopyFun (pullPair P (idGHom L) ι) 2 h i j hij (ι.f i i rfl u) = 0 := by
  apply dualCx_ext
  intro v
  change h (P.P i (2 - j) 3 (by omega) (ι.f i i rfl u)
      (ι.f (2 - j) (2 - j) rfl v)) = 0
  by_cases hi : i = 0 ∨ i = 1
  · haveI : Subsingleton (U.X (2 - j)) := hU (2 - j) (by omega)
    have hv : v = 0 := Subsingleton.elim _ _
    rw [hv, map_zero, map_zero, map_zero]
  · haveI : Subsingleton (U.X i) := hU i hi
    have hu : u = 0 := Subsingleton.elim _ _
    rw [hu, map_zero, LinearMap.map_zero₂, map_zero]

/-- The explicit homotopy component on the actual ordinary cone. -/
def coneTraceHomotopyFun (ι : GHom U L) (P : GPair L L T)
    (h : T.X 3 →ₗ[R] R) (i j : ℤ) (hij : j + 1 = i) :
    (ordinaryCone ι).X i →ₗ[R] (dualCx U 2).X j :=
  (traceHomotopyFun (pullPair P (idGHom L) ι) 2 h i j hij).comp
    (LinearMap.fst R (L.X i) (U.X (i + 1)))

/-- The homotopy evaluates the same cup on the first cone component. -/
theorem coneTraceHomotopyFun_apply (ι : GHom U L) (P : GPair L L T)
    (h : T.X 3 →ₗ[R] R) (i j : ℤ) (hij : j + 1 = i)
    (x : (ordinaryCone ι).X i) (v : U.X (2 - j)) :
    asDual (coneTraceHomotopyFun ι P h i j hij x) v =
      h (P.P i (2 - j) 3 (by omega) x.1 (ι.f (2 - j) (2 - j) rfl v)) := rfl

/-- The ordinary-cone homotopy identity, including its fixed dual shift and signs. -/
theorem coneTraceHomotopy_identity (ι : GHom U L) (P : GPair L L T)
    (hU : VanishesOutside U (fun n => n = 0 ∨ n = 1))
    (tr₁ tr₂ : T.X 2 →ₗ[R] R) (h : T.X 3 →ₗ[R] R)
    (hh : ∀ z : T.X 2, tr₁ z - tr₂ z = h (T.d 2 3 rfl z))
    (i : ℤ) (x : (ordinaryCone ι).X i) :
    adjFun (pullPair P (idGHom L) ι) 2 tr₁ i i rfl x.1 -
      adjFun (pullPair P (idGHom L) ι) 2 tr₂ i i rfl x.1 =
      (dualCx U 2).d (i - 1) i (by omega)
        (coneTraceHomotopyFun ι P h i (i - 1) (by omega) x) +
      coneTraceHomotopyFun ι P h (i + 1) i rfl
        ((ordinaryCone ι).d i (i + 1) rfl x) := by
  have key := adjFun_sub_eq (pullPair P (idGHom L) ι) 2 tr₁ tr₂ h hh
    i (i - 1) (i + 1) (by omega) rfl x.1
  change adjFun (pullPair P (idGHom L) ι) 2 tr₁ i i rfl x.1 -
      adjFun (pullPair P (idGHom L) ι) 2 tr₂ i i rfl x.1 =
      (dualCx U 2).d (i - 1) i (by omega)
        (traceHomotopyFun (pullPair P (idGHom L) ι) 2 h i (i - 1) (by omega) x.1) +
      traceHomotopyFun (pullPair P (idGHom L) ι) 2 h (i + 1) i rfl
        (L.d i (i + 1) rfl x.1 + ι.f (i + 1) (i + 1) rfl x.2)
  rw [map_add, traceHomotopyFun_iota_zero ι P hU, add_zero]
  exact key

/-- The ordinary-cone homotopy maps, zero off the cochain relation. -/
def coneTraceHomotopyHom (ι : GHom U L) (P : GPair L L T) (h : T.X 3 →ₗ[R] R)
    (i j : ℤ) : (ordinaryCone ι).toCC.X i ⟶ (dualCx U 2).toCC.X j :=
  if hij : j + 1 = i then ModuleCat.ofHom (coneTraceHomotopyFun ι P h i j hij) else 0

/-- Factoring a trace difference gives a homotopy of the SAME local comparisons. -/
def selfDualConeComparisonHomotopy (ι : GHom U L) (P : GPair L L T)
    (tr₁ tr₂ : T.X 2 →ₗ[R] R)
    (htr₁ : ∀ z, tr₁ (T.d 1 2 rfl z) = 0) (htr₂ : ∀ z, tr₂ (T.d 1 2 rfl z) = 0)
    (hU : VanishesOutside U (fun n => n = 0 ∨ n = 1))
    (h11₁ : ∀ u v : U.X 1, tr₁ (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι.f 1 1 rfl v)) = 0)
    (h11₂ : ∀ u v : U.X 1, tr₂ (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι.f 1 1 rfl v)) = 0)
    (h : T.X 3 →ₗ[R] R)
    (hh : ∀ z : T.X 2, tr₁ z - tr₂ z = h (T.d 2 3 rfl z)) :
    Homotopy (GHom.toCC (selfDualConeComparison ι P tr₁ htr₁ hU h11₁))
      (GHom.toCC (selfDualConeComparison ι P tr₂ htr₂ hU h11₂)) where
  hom := coneTraceHomotopyHom ι P h
  zero i j hij := by
    have hn : ¬ j + 1 = i := hij
    simp only [coneTraceHomotopyHom, hn, ↓reduceDIte]
  comm i := by
    have hd1 : coneTraceHomotopyHom ι P h (i + 1) i =
        ModuleCat.ofHom (coneTraceHomotopyFun ι P h (i + 1) i rfl) := dite_eq_left rfl
    have hd0 : coneTraceHomotopyHom ι P h i (i - 1) =
        ModuleCat.ofHom (coneTraceHomotopyFun ι P h i (i - 1) (by omega)) :=
      dite_eq_left (show i - 1 + 1 = i by omega)
    rw [dNext_eq (coneTraceHomotopyHom ι P h)
        (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq (coneTraceHomotopyHom ι P h)
        (show (ComplexShape.up ℤ).Rel (i - 1) i by simp), hd1, hd0]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have key := coneTraceHomotopy_identity ι P hU tr₁ tr₂ h hh i x
    rw [sub_eq_iff_eq_add] at key
    rw [ModuleCat.hom_add, ModuleCat.hom_add, LinearMap.add_apply, LinearMap.add_apply]
    change adjFun (pullPair P (idGHom L) ι) 2 tr₁ i i rfl x.1 =
      coneTraceHomotopyFun ι P h (i + 1) i rfl
        (((ordinaryCone ι).toCC.d i (i + 1)).hom x) +
      (show (dualCx U 2).X i from
        ((dualCx U 2).toCC.d (i - 1) i).hom
          (coneTraceHomotopyFun ι P h i (i - 1) (by omega) x)) +
      adjFun (pullPair P (idGHom L) ι) 2 tr₂ i i rfl x.1
    erw [GCx.toCC_d_hom (ordinaryCone ι) i (i + 1) rfl x,
      GCx.toCC_d_hom (dualCx U 2) (i - 1) i (by omega)]
    rw [key]
    abel

/-- Quasi-isomorphy is unchanged under a factored trace difference. -/
theorem selfDualConeComparison_quasiIso_iff_of_factor (ι : GHom U L) (P : GPair L L T)
    (tr₁ tr₂ : T.X 2 →ₗ[R] R)
    (htr₁ : ∀ z, tr₁ (T.d 1 2 rfl z) = 0) (htr₂ : ∀ z, tr₂ (T.d 1 2 rfl z) = 0)
    (hU : VanishesOutside U (fun n => n = 0 ∨ n = 1))
    (h11₁ : ∀ u v : U.X 1, tr₁ (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι.f 1 1 rfl v)) = 0)
    (h11₂ : ∀ u v : U.X 1, tr₂ (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι.f 1 1 rfl v)) = 0)
    (h : T.X 3 →ₗ[R] R) (hh : ∀ z : T.X 2, tr₁ z - tr₂ z = h (T.d 2 3 rfl z)) :
    QuasiIso (GHom.toCC (selfDualConeComparison ι P tr₁ htr₁ hU h11₁)) ↔
      QuasiIso (GHom.toCC (selfDualConeComparison ι P tr₂ htr₂ hU h11₂)) := by
  have H := selfDualConeComparisonHomotopy ι P tr₁ tr₂ htr₁ htr₂ hU h11₁ h11₂ h hh
  simp only [quasiIso_iff, quasiIsoAt_iff_isIso_homologyMap, H.homologyMap_eq]

section Support

/-- A supported degree-one local-condition element maps to a genuine one-cycle. -/
theorem iota_one_cycle (ι : GHom U L)
    (hU : VanishesOutside U (fun n => n = 0 ∨ n = 1)) (u : U.X 1) :
    L.d 1 2 rfl (ι.f 1 1 rfl u) = 0 := by
  haveI : Subsingleton (U.X 2) := hU 2 (by omega)
  have h0 : U.d 1 2 rfl u = 0 := Subsingleton.elim _ _
  have h := ι.comm 1 2 1 2 rfl rfl rfl rfl u
  rw [h0, map_zero] at h
  exact h.symm

/-- The cup of two supported local-condition one-elements is a two-cycle,
not necessarily a zero cochain. -/
theorem iota_pair11_cycle (ι : GHom U L) (P : GPair L L T)
    (hU : VanishesOutside U (fun n => n = 0 ∨ n = 1)) (u v : U.X 1) :
    T.d 2 3 rfl (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι.f 1 1 rfl v)) = 0 := by
  rw [P.leib 1 2 1 2 2 3 rfl rfl rfl rfl,
    iota_one_cycle ι hU, iota_one_cycle ι hU,
    LinearMap.map_zero₂, map_zero, smul_zero, add_zero]

/-- Scalar isotropy for any top trace follows from canonical scalar isotropy;
the normalization unit is derived from the two trace isomorphisms. -/
theorem isotropy_of_topTraceIso (ι : GHom U L) (P : GPair L L T)
    (tr₁ tr₂ : T.X 2 →ₗ[R] R)
    (h₁ : IsTopTraceIso (T.d 1 2 rfl) (T.d 2 3 rfl) tr₁)
    (h₂ : IsTopTraceIso (T.d 1 2 rfl) (T.d 2 3 rfl) tr₂)
    (hU : VanishesOutside U (fun n => n = 0 ∨ n = 1))
    (h11₂ : ∀ u v : U.X 1, tr₂ (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι.f 1 1 rfl v)) = 0) :
    ∀ u v : U.X 1, tr₁ (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι.f 1 1 rfl v)) = 0 := by
  obtain ⟨a, ha⟩ := topTraceUnit_on_cycles h₁ h₂
  intro u v
  rw [ha _ (iota_pair11_cycle ι P hU u v), h11₂, mul_zero]

end Support

section CompactScalar

variable [IsDomain R] [IsPrincipalIdealRing R]
  [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]

/-- The compact-scalar extension theorem factors the trace difference on the
raw coefficient complex, without assuming self-injectivity. -/
theorem selfDualConeComparison_quasiIso_iff_of_eq_on_cycles
    (ι : GHom U L) (P : GPair L L T) (tr₁ tr₂ : T.X 2 →ₗ[R] R)
    (htr₁ : ∀ z, tr₁ (T.d 1 2 rfl z) = 0) (htr₂ : ∀ z, tr₂ (T.d 1 2 rfl z) = 0)
    (hU : VanishesOutside U (fun n => n = 0 ∨ n = 1))
    (h11₁ : ∀ u v : U.X 1, tr₁ (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι.f 1 1 rfl v)) = 0)
    (h11₂ : ∀ u v : U.X 1, tr₂ (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι.f 1 1 rfl v)) = 0)
    [Module.IsTorsionFree R (T.X 4)]
    (hnext : ∀ z : T.X 3, T.d 3 4 rfl z = 0 → ∃ y : T.X 2, T.d 2 3 rfl y = z)
    (hcyc : ∀ z : T.X 2, T.d 2 3 rfl z = 0 → tr₁ z = tr₂ z) :
    QuasiIso (GHom.toCC (selfDualConeComparison ι P tr₁ htr₁ hU h11₁)) ↔
      QuasiIso (GHom.toCC (selfDualConeComparison ι P tr₂ htr₂ hU h11₂)) := by
  letI : Module.IsTorsionFree R (T.X (2 + 2)) :=
    inferInstanceAs (Module.IsTorsionFree R (T.X 4))
  obtain ⟨h, hh⟩ := exists_trace_sub_eq_comp_d_compact (T := T) 2 tr₁ tr₂ hnext hcyc
  exact selfDualConeComparison_quasiIso_iff_of_factor ι P tr₁ tr₂
    htr₁ htr₂ hU h11₁ h11₂ h hh

/-- Scalar isotropy is preserved by unit scaling. -/
theorem unitTrace_isotropy (ι : GHom U L) (P : GPair L L T)
    (tr : T.X 2 →ₗ[R] R) (a : Rˣ)
    (h11 : ∀ u v : U.X 1, tr (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι.f 1 1 rfl v)) = 0) :
    ∀ u v : U.X 1, ((a : R) • tr)
      (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι.f 1 1 rfl v)) = 0 := by
  intro u v
  rw [LinearMap.smul_apply, h11, smul_zero]

/-- The unit-scaled trace gives the SAME comparison followed by unit multiplication. -/
theorem selfDualConeComparison_unit_trace_eq (ι : GHom U L) (P : GPair L L T)
    (tr : T.X 2 →ₗ[R] R) (htr : ∀ z, tr (T.d 1 2 rfl z) = 0)
    (hU : VanishesOutside U (fun n => n = 0 ∨ n = 1))
    (h11 : ∀ u v : U.X 1, tr (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι.f 1 1 rfl v)) = 0)
    (a : Rˣ) :
    GHom.toCC (selfDualConeComparison ι P ((a : R) • tr)
      (unitScaledTrace_boundary 2 tr htr a) hU (unitTrace_isotropy ι P tr a h11)) =
      GHom.toCC (selfDualConeComparison ι P tr htr hU h11) ≫
        (unitScalarCochainIso (dualCx U 2) a).hom := by
  ext n x
  apply dualCx_ext
  intro v
  rfl

/-- Unit scaling preserves quasi-isomorphy of the fixed comparison. -/
theorem selfDualConeComparison_quasiIso_iff_unit_trace (ι : GHom U L) (P : GPair L L T)
    (tr : T.X 2 →ₗ[R] R) (htr : ∀ z, tr (T.d 1 2 rfl z) = 0)
    (hU : VanishesOutside U (fun n => n = 0 ∨ n = 1))
    (h11 : ∀ u v : U.X 1, tr (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι.f 1 1 rfl v)) = 0)
    (a : Rˣ) :
    QuasiIso (GHom.toCC (selfDualConeComparison ι P ((a : R) • tr)
      (unitScaledTrace_boundary 2 tr htr a) hU (unitTrace_isotropy ι P tr a h11))) ↔
      QuasiIso (GHom.toCC (selfDualConeComparison ι P tr htr hU h11)) := by
  rw [selfDualConeComparison_unit_trace_eq]
  exact quasiIso_iff_comp_right
    (GHom.toCC (selfDualConeComparison ι P tr htr hU h11))
    (unitScalarCochainIso (dualCx U 2) a).hom

/-- Any top degree-two scalar trace has the same quasi-isomorphy verdict as
the canonical trace on the SAME ordinary-cone comparison. Its scalar isotropy
is derived, not supplied as an independent normalization hypothesis. -/
theorem selfDualConeComparison_quasiIso_iff_topTrace (ι : GHom U L) (P : GPair L L T)
    (tr₁ tr₂ : T.X 2 →ₗ[R] R)
    (h₁ : IsTopTraceIso (T.d 1 2 rfl) (T.d 2 3 rfl) tr₁)
    (h₂ : IsTopTraceIso (T.d 1 2 rfl) (T.d 2 3 rfl) tr₂)
    (hU : VanishesOutside U (fun n => n = 0 ∨ n = 1))
    (h11₂ : ∀ u v : U.X 1, tr₂ (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι.f 1 1 rfl v)) = 0)
    [Module.IsTorsionFree R (T.X 4)]
    (hnext : ∀ z : T.X 3, T.d 3 4 rfl z = 0 → ∃ y : T.X 2, T.d 2 3 rfl y = z) :
    QuasiIso (GHom.toCC (selfDualConeComparison ι P tr₁ h₁.1 hU
      (isotropy_of_topTraceIso ι P tr₁ tr₂ h₁ h₂ hU h11₂))) ↔
      QuasiIso (GHom.toCC (selfDualConeComparison ι P tr₂ h₂.1 hU h11₂)) := by
  obtain ⟨a, ha⟩ := topTraceUnit_on_cycles h₁ h₂
  have hcyc : ∀ z : T.X 2, T.d 2 3 rfl z = 0 → tr₁ z = ((a : R) • tr₂) z := by
    intro z hz
    exact ha z hz
  have h := selfDualConeComparison_quasiIso_iff_of_eq_on_cycles ι P tr₁ ((a : R) • tr₂)
    h₁.1 (unitScaledTrace_boundary 2 tr₂ h₂.1 a) hU
    (isotropy_of_topTraceIso ι P tr₁ tr₂ h₁ h₂ hU h11₂)
    (unitTrace_isotropy ι P tr₂ a h11₂) hnext hcyc
  exact h.trans (selfDualConeComparison_quasiIso_iff_unit_trace ι P tr₂ h₂.1 hU h11₂ a)

end CompactScalar

section ActualLocal

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.RC53Assist.CalibrationModel
open ZInQ.Contrib.RC53Assist.DerivedKummerActual
open ZInQ.Contrib.RC53Assist.DerivedKummer

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

omit [W.IsElliptic] [HasFullTwoTorsion K S W] [DecidableEq (w.adicCompletion K)] in
/-- Every raw restricted coefficient term is torsion-free; neither degree zero
nor the infinite cochain modules are discarded. -/
theorem localCoefficient_term_torsionFree (n : ℤ) :
    Module.IsTorsionFree ℤ_[2] ((natCx (restrictedLineComplex (S := S) w)).X n) := by
  letI : Module.IsTorsionFree ℤ_[2] (IntegralTate1 K S) := integralTate1_torsionFree K S
  letI : Module.IsTorsionFree ℤ_[2] (ResMod (locMap K S w) (IntegralTate1 K S)) :=
    resMod_torsionFree (locMap K S w)
  exact natCx_torsionFree _ (fun m => contCochain_torsionFree m) n

/-- The canonical invariant is a top trace on this SAME coefficient complex. -/
theorem canonicalLocalTrace_top
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint) :
    IsTopTraceIso ((natCx (restrictedLineComplex (S := S) w)).d 1 2 rfl)
      ((natCx (restrictedLineComplex (S := S) w)).d 2 3 rfl)
      (orientedLocalTrace (S := S) W w) :=
  ⟨orientedLocalTrace_boundary W w, orientedLocalTrace_inducesIsoH2 W w hH⟩

include W in
/-- Next-degree exactness is transported through the existing actual line
cochain isomorphism, using the finite cyclotomic degree bound. -/
theorem localCoefficient_degree_three_exact
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint)
    (z : (natCx (restrictedLineComplex (S := S) w)).X 3)
    (hz : (natCx (restrictedLineComplex (S := S) w)).d 3 4 rfl z = 0) :
    ∃ y : (natCx (restrictedLineComplex (S := S) w)).X 2,
      (natCx (restrictedLineComplex (S := S) w)).d 2 3 rfl y = z := by
  have hzN : ((restrictedLineComplex (S := S) w).d 3 4).hom z = 0 := hz
  have h := congrArg (fun f => f.hom z) ((localLineCochainMap (S := S) W w).comm 3 4)
  have hc : ((IntegralReduction.actualTraceComplex (w.adicCompletion K)).d 3 4).hom
      (((localLineCochainMap (S := S) W w).f 3).hom z) = 0 := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hzN, map_zero] using h
  obtain ⟨b, hb⟩ := FiniteLocalDegreeBound.actualThirdDegreeExact_of_print hH
    (w.adicCompletion K) (((localLineCochainMap (S := S) W w).f 3).hom z) hc
  refine ⟨((localLineCochainInv (S := S) W w).f 2).hom b, ?_⟩
  change ((restrictedLineComplex (S := S) w).d 2 3).hom
    (((localLineCochainInv (S := S) W w).f 2).hom b) = z
  have hi := congrArg (fun f => f.hom b) ((localLineCochainInv (S := S) W w).comm 2 3)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hi
  rw [hi, hb]
  have hback := congrArg (fun f => (f.f 3).hom z) (localLineCochainMap_inv (S := S) W w)
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using hback

/-- Scalar isotropy of the original canonical comparison, reused unchanged. -/
theorem canonicalLocalTrace_isotropy (hM : MilneLocalDualityPrint) :
    ∀ u v : (integralCondition (S := S) W w).X 1,
      orientedLocalTrace (S := S) W w
        ((natPair (restrictedIntegralCup W w)).P 1 1 2 rfl
          ((integralConditionMap (S := S) W w).f 1 1 rfl u)
          ((integralConditionMap (S := S) W w).f 1 1 rfl v)) = 0 := by
  intro u v
  change orientedLocalTrace (S := S) W w
    ((restrictedIntegralCup W w).P 1 1 2 rfl u.val v.val) = 0
  rw [orientedLocalTrace_cup_one]
  exact kummerTracePair_condition W w hM u v

/-- The original ordinary-cone comparison with the GIVEN scalar trace. Its
scalar isotropy is derived from the two trace isomorphisms, not re-chosen. -/
def literalLocalComparisonWithTrace (hM : MilneLocalDualityPrint)
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint)
    (tr : (natCx (restrictedLineComplex (S := S) w)).X 2 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : IsTopTraceIso ((natCx (restrictedLineComplex (S := S) w)).d 1 2 rfl)
      ((natCx (restrictedLineComplex (S := S) w)).d 2 3 rfl) tr) :
    GHom (literalLocalQuotientCone (S := S) W w) (dualCx (integralCondition (S := S) W w) 2) :=
  selfDualConeComparison (integralConditionMap (S := S) W w)
    (natPair (restrictedIntegralCup W w)) tr htr.1 (integralKummerCondition_support W w)
    (isotropy_of_topTraceIso (integralConditionMap (S := S) W w)
      (natPair (restrictedIntegralCup W w)) tr (orientedLocalTrace (S := S) W w)
      htr (canonicalLocalTrace_top W w hH) (integralKummerCondition_support W w)
      (canonicalLocalTrace_isotropy W w hM))

/-- Every component has the literal given-trace cup formula with shift `2 - n`. -/
theorem literalLocalComparisonWithTrace_apply (hM : MilneLocalDualityPrint)
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint)
    (tr : (natCx (restrictedLineComplex (S := S) w)).X 2 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : IsTopTraceIso ((natCx (restrictedLineComplex (S := S) w)).d 1 2 rfl)
      ((natCx (restrictedLineComplex (S := S) w)).d 2 3 rfl) tr)
    (n : ℤ) (x : (literalLocalQuotientCone (S := S) W w).X n)
    (u : (integralCondition (S := S) W w).X (2 - n)) :
    asDual ((literalLocalComparisonWithTrace W w hM hH tr htr).f n n rfl x) u =
      tr ((natPair (restrictedIntegralCup W w)).P n (2 - n) 2 (by omega) x.1
        ((integralConditionMap (S := S) W w).f (2 - n) (2 - n) rfl u)) := rfl

/-- The canonical-versus-arbitrary LOCAL scalar trace transfer is an iff for
the SAME specified comparison. No canonical or arbitrary local quasi-isomorphism,
derived isomorphism, residue assumption or new arithmetic print is supplied. -/
theorem literalLocalComparisonWithTrace_quasiIso_iff (hM : MilneLocalDualityPrint)
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint)
    (tr : (natCx (restrictedLineComplex (S := S) w)).X 2 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : IsTopTraceIso ((natCx (restrictedLineComplex (S := S) w)).d 1 2 rfl)
      ((natCx (restrictedLineComplex (S := S) w)).d 2 3 rfl) tr) :
    QuasiIso (GHom.toCC (literalLocalComparisonWithTrace W w hM hH tr htr)) ↔
      QuasiIso (GHom.toCC (literalLocalSelfDualComparison (S := S) W w hM)) := by
  letI : Module.IsTorsionFree ℤ_[2] ((natCx (restrictedLineComplex (S := S) w)).X 4) :=
    localCoefficient_term_torsionFree (S := S) w 4
  have h := selfDualConeComparison_quasiIso_iff_topTrace
    (integralConditionMap (S := S) W w) (natPair (restrictedIntegralCup W w))
    tr (orientedLocalTrace (S := S) W w) htr (canonicalLocalTrace_top W w hH)
    (integralKummerCondition_support W w) (canonicalLocalTrace_isotropy W w hM)
    (localCoefficient_degree_three_exact W w hH)
  simpa only [literalLocalComparisonWithTrace, literalLocalSelfDualComparison] using h

end ActualLocal

end ZInQ.Contrib.RC53Assist.DKLocalAdapter.LocalTraceTransport

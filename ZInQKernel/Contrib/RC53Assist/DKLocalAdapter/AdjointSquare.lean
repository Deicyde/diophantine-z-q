import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.LocalDuality

/-!
# The fixed local adjoint commuting square

The ordinary-cone dictionary and the condition dictionary transport the same
raw trace-cup adjoint. Cup compatibility and the inverse cochain identities
are used in every integer degree. No quasi-isomorphism, replacement adjoint,
or equality with an unrelated trace is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.DKLocalAdapter

open CategoryTheory HomologicalComplex NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness)
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.LambdaCoef

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- The fixed inverse point-cochain dictionary is inverse in every integer degree. -/
theorem adjointSquare_point_inverse (n : ℤ)
    (x : (ActualSelfDual.localCochains K w (W.baseChange (w.adicCompletion K))).X n) :
    (natHom (localPointCochainMap (S := S) W w)).f n n rfl
      ((natHom (localPointCochainInv (S := S) W w)).f n n rfl x) = x := by
  cases n with
  | ofNat n =>
    change ((localPointCochainMap (S := S) W w).f n).hom
      (((localPointCochainInv (S := S) W w).f n).hom x) = x
    have h := congrArg (fun f => (f.f n).hom x) (localPointCochainInv_map (S := S) W w)
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h
  | negSucc n =>
    change (0 : PUnit) = x
    exact Subsingleton.elim _ _

/-- Canonical cup-trace transport, including the zero-extension degrees. -/
theorem adjointSquare_cup_transport (i j : ℤ) (hij : i + j = 2)
    (x : (natCx (restrictedPointComplex (S := S) W w)).X i)
    (y : (natCx (restrictedPointComplex (S := S) W w)).X j) :
    orientedLocalTrace (S := S) W w
        ((natPair (restrictedIntegralCup (S := S) W w)).P i j 2 hij x y) =
      AllCochainTrace.trv (w.adicCompletion K)
        ((ActualSelfDual.localCup K w (W.baseChange (w.adicCompletion K))).P i j 2 hij
          ((natHom (localPointCochainMap (S := S) W w)).f i i rfl x)
          ((natHom (localPointCochainMap (S := S) W w)).f j j rfl y)) := by
  cases i with
  | negSucc i =>
    change orientedLocalTrace (S := S) W w (0 : (restrictedLineComplex (S := S) w).X 2) =
      AllCochainTrace.trv (w.adicCompletion K) (0 : (actualTraceComplex (w.adicCompletion K)).X 2)
    simp only [map_zero]
  | ofNat p =>
    cases j with
    | negSucc j =>
      change orientedLocalTrace (S := S) W w (0 : (restrictedLineComplex (S := S) w).X 2) =
        AllCochainTrace.trv (w.adicCompletion K) (0 : (actualTraceComplex (w.adicCompletion K)).X 2)
      simp only [map_zero]
    | ofNat q =>
      have hpq : p + q = 2 := by
        simp only [Int.ofNat_eq_natCast] at hij
        omega
      change AllCochainTrace.trv (w.adicCompletion K)
          (((localLineCochainMap (S := S) W w).f 2).hom
            ((restrictedIntegralCup (S := S) W w).P p q 2 hpq x y)) =
        AllCochainTrace.trv (w.adicCompletion K)
          ((integralCupPair (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).P p q 2 hpq
            (((localPointCochainMap (S := S) W w).f p).hom x)
            (((localPointCochainMap (S := S) W w).f q).hom y))
      rw [localLineCochainMap_cup]

/-- Both routes evaluate the same raw local adjoint on the reflected degree `2-n`. -/
theorem adjointSquare_apply (hloc : MilneLocalFiniteness) (hM : MilneLocalDualityPrint)
    (n : ℤ)
    (x : (ActualSelfDual.localQuotientCone K w (W.baseChange (w.adicCompletion K))).X n)
    (u : (ActualSelfDual.localCondition K w (W.baseChange (w.adicCompletion K))).X (2 - n)) :
    asDual ((ActualSelfDual.localSelfDualComparison K w (W.baseChange (w.adicCompletion K)) hM).f
        n n rfl x) u =
      asDual ((literalLocalSelfDualComparison (S := S) W w hM).f n n rfl
        ((actualConeToLiteral (S := S) W w hloc).f n n rfl x))
        ((actualConditionToLiteral (S := S) W w hloc).f (2 - n) (2 - n) rfl u) := by
  rw [ActualSelfDual.localSelfDualComparison_formula, literalLocalSelfDualComparison_apply]
  change AllCochainTrace.trv (w.adicCompletion K)
      ((ActualSelfDual.localCup K w (W.baseChange (w.adicCompletion K))).P n (2 - n) 2 (by omega)
        x.1 ((ActualSelfDual.localConditionMap K w (W.baseChange (w.adicCompletion K))).f
          (2 - n) (2 - n) rfl u)) =
    orientedLocalTrace (S := S) W w
      ((natPair (restrictedIntegralCup (S := S) W w)).P n (2 - n) 2 (by omega)
        ((natHom (localPointCochainInv (S := S) W w)).f n n rfl x.1)
        ((integralConditionMap (S := S) W w).f (2 - n) (2 - n) rfl
          ((actualConditionToLiteral (S := S) W w hloc).f (2 - n) (2 - n) rfl u)))
  rw [adjointSquare_cup_transport]
  rw [adjointSquare_point_inverse, actualConditionToLiteral_over_point]

/-- The exact commuting square for the fixed actual and literal local adjoints. -/
theorem localSelfDualComparison_commutingSquare (hloc : MilneLocalFiniteness)
    (hM : MilneLocalDualityPrint) :
    GHom.toCC (ActualSelfDual.localSelfDualComparison K w (W.baseChange (w.adicCompletion K)) hM) =
      GHom.toCC (actualConeToLiteral (S := S) W w hloc) ≫
        GHom.toCC (literalLocalSelfDualComparison (S := S) W w hM) ≫
          GHom.toCC (dualHom (actualConditionToLiteral (S := S) W w hloc) 2) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply dualCx_ext
  intro u
  exact adjointSquare_apply (S := S) W w hloc hM n x u

end ZInQ.Contrib.RC53Assist.DKLocalAdapter

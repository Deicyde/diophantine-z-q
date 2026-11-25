import ZInQKernel.Contrib.RC53Assist.G0Prints.Assembly
import ZInQKernel.Contrib.RC53Assist.TateCurve.TwoPrints
import ZInQKernel.Contrib.RC53Assist.DecompositionGlue.Glue

/-! # One semistability criterion for both bad-reduction cases

The two cases in the Euler-factor comparison use the same criterion on the
same representation. Local integral unipotence is obtained from global
rational unipotence, not taken as a second independent assumption. -/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.G0Prints

open ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open ZInQ.Contrib.RC53Assist.DecompositionGlue
open ZInQ.Contrib.RC53Assist.GlobalTrace
open ZInQ.Contrib.RC53Assist.TateCurve
open scoped Classical WithZero

/-- Faithful scalar extension detects nilpotence on the given finite free module. -/
private theorem isNilpotent_of_baseChange {R K V : Type*}
    [CommRing R] [CommRing K] [Algebra R K] [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin 2) R V) (hi : Function.Injective (algebraMap R K))
    (f : Module.End R V) (h : IsNilpotent (f.baseChange K)) : IsNilpotent f := by
  obtain ⟨n, hn⟩ := h
  have hM := LinearMap.toMatrix_baseChange K (f ^ n) b b
  rw [LinearMap.baseChange_pow, hn, map_zero] at hM
  refine ⟨n, (LinearMap.toMatrix b b).injective ?_⟩
  rw [map_zero]
  apply Matrix.map_injective hi
  change ((LinearMap.toMatrix b b) (f ^ n)).map (algebraMap R K) =
    (0 : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K)
  simpa only [Matrix.map_zero _ (map_zero _)] using hM.symm

/-- Compare unipotence on the global rational and local integral Tate
representations along the actual equivariant embedding. -/
private theorem nilpotent_global_iff_local (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : p.Prime) (ℓ : ℕ) [Fact ℓ.Prime]
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))
    (r : LocalGaloisQ p hp →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hres : ∀ (σ : LocalGaloisQ p hp) (x : AlgebraicClosure ℚ), ι (r σ x) = σ (ι x))
    (σ : LocalGaloisQ p hp) :
    IsNilpotent (rationalTateRep E ℓ (r σ) - 1) ↔
      IsNilpotent (WeierstrassCurve.tateModuleGaloisRepresentation
        (E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)) ℓ σ - 1) := by
  let f := integralTateRep E ℓ (r σ)
  have hBase : (f - 1).baseChange ℚ_[ℓ] = rationalTateRep E ℓ (r σ) - 1 := by
    simp only [f, LinearMap.baseChange_sub, LinearMap.baseChange_one, rationalTateRep,
      Representation.baseChange_apply]
  let e := tateToLocal E p hp ι ℓ
  let c := e.conjAlgEquiv ℤ_[ℓ]
  have hc : c f =
      (E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).tateModuleGaloisRepresentation ℓ σ := by
    apply LinearMap.ext
    intro y
    change e (f (e.symm y)) = _
    rw [show f = integralTateRep E ℓ (r σ) from rfl]
    have hh := tateToLocal_equivariant E p hp ι r hres ℓ σ (e.symm y)
    change e (integralTateRep E ℓ (r σ) (e.symm y)) = _ at hh
    rw [hh, e.apply_symm_apply]
  have hLocal : c (f - 1) =
      (E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).tateModuleGaloisRepresentation ℓ σ - 1 :=
    by rw [map_sub, map_one, hc]
  constructor
  · intro h
    have hi : IsNilpotent (f - 1) :=
      isNilpotent_of_baseChange (integralTateBasis E ℓ)
        (fun {_ _} hij => PadicInt.coe_inj.mp hij) (f - 1) (hBase.symm ▸ h)
    simpa only [hLocal] using hi.map c
  · intro h
    have h' : IsNilpotent (c (f - 1)) := hLocal.symm ▸ h
    have hi : IsNilpotent (f - 1) := by simpa only [AlgEquiv.symm_apply_apply] using h'.map c.symm
    obtain ⟨n, hn⟩ := hi
    exact ⟨n, by rw [← hBase, ← LinearMap.baseChange_pow, hn, LinearMap.baseChange_zero]⟩

/-- The local integral statement used in Tate descent follows from the one
semistability criterion on the actual rational Tate representation. The
restriction is for the same place; uniqueness of the extending valuation
identifies its inertia with that of the valuation in the input. -/
theorem localSemistableTatePrint_of_global (hS : GrothendieckSemistableReductionPrint) :
    LocalSemistableTatePrint := by
  classical
  intro E _ p hp ℓ _ hℓp hm Γ _ w hw σ hσ
  obtain ⟨D⟩ := localArithmeticFrobenius_nonempty p hp
  obtain ⟨Γ', hg, v, ι, r, hv, hres, hrI, -⟩ := decompositionGroupLocalGlobalGlue p hp D
  letI : LinearOrderedCommGroupWithZero Γ' := hg
  letI := padicNontriviallyNormedField p hp
  have hvw : v.IsEquiv w :=
    (local_valuation_isEquiv_spectral p hp Γ' v hv).trans
      (local_valuation_isEquiv_spectral p hp Γ w hw).symm
  have hI : localInertia v = localInertia w := by
    unfold localInertia
    rw [(Valuation.isEquiv_iff_valuationSubring v w).mp hvw]
  have hri : r σ ∈ inertiaAt D := by
    rw [← hrI, hI]
    exact ⟨σ, hσ, rfl⟩
  exact (nilpotent_global_iff_local E p hp ℓ ι r hres σ).mp
    ((hS E ℓ p hp hℓp.symm D).mp (Or.inr hm) (r σ) hri)

/-- **GLUE.** Grothendieck, SGA 7 I, Exposé IX, Corollary 3.8, condition (vi) equivalent to (i)
of Proposition 3.5, joined with Silverman VII.5.1 and a Néron-model dictionary that is not cited.
Sources: the read copy is Silverberg–Zarhin, *Reduction of Abelian Varieties*,
arXiv:alg-geom/9602014v2, Theorem 4.1(i)-(ii) (text body read), the provenance of main's
`GrothendieckSemistableReductionPrint` (`RC53Assist/TateCurve/AdditiveReading.lean`), whose
proof cites SGA 7 IX 3.5 and 3.8. The SGA 7 IX original is UNVERIFIED: no reading of it is on
record (pp. 350, 353 are as cited; it is row 2 of the reading list, Th. 3.6 at p. 351). Use the
actual integral Tate module at the complete local field. In the elliptic-curve specialization,
semistability is good or multiplicative reduction of the local minimal
Weierstrass equation (Silverman, AEC, 2nd ed., VII.5.1, p. 196). -/
def SGA7IX38LocalEllipticCriterion : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) (hp : p.Prime) (ℓ : ℕ) [Fact ℓ.Prime],
    p ≠ ℓ → ∀ (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
      (w : Valuation (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) Γ),
      (w.comap (algebraMap ((primeIdealQ p hp).adicCompletion ℚ)
        (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)))).IsEquiv
        (Valued.v : Valuation ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰) →
      ((GoodReductionAt E (primeIdealQ p hp) ∨
        ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
          ((primeIdealQ p hp).adicCompletionIntegers ℚ)).HasMultiplicativeReduction
          ((primeIdealQ p hp).adicCompletionIntegers ℚ)) ↔
        ∀ σ ∈ localInertia w, IsNilpotent
          (WeierstrassCurve.tateModuleGaloisRepresentation
            (E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)) ℓ σ - 1))

/-- The local criterion (GLUE, above) supplies the old global reading using
both directions of the actual inertia comparison. -/
theorem grothendieckSemistableReductionPrint_of_sga7 (hS : SGA7IX38LocalEllipticCriterion) :
    GrothendieckSemistableReductionPrint := by
  intro E _ ℓ _ p hp hℓ D
  obtain ⟨Γ, hΓ, w, ι, r, hw, hres, hrI, -⟩ := decompositionGroupLocalGlobalGlue p hp D
  letI : LinearOrderedCommGroupWithZero Γ := hΓ
  have h := hS E p hp ℓ hℓ Γ w hw
  constructor
  · intro hgood i hi
    rw [← hrI] at hi
    obtain ⟨σ, hσ, rfl⟩ := hi
    exact (nilpotent_global_iff_local E p hp ℓ ι r hres σ).mpr (h.mp hgood σ hσ)
  · intro hg
    apply h.mpr
    intro σ hσ
    apply (nilpotent_global_iff_local E p hp ℓ ι r hres σ).mp
    apply hg
    rw [← hrI]
    exact ⟨σ, hσ, rfl⟩

/-- The unchanged Faltings interface now follows from the printed local Euler
factor implication, Tate uniformization and one semistability criterion.
No decomposition, additive-vanishing or separate local-unipotence premise
is passed to the receiver. -/
theorem faltingsRigidity_of_classical (hF : Faltings1983Korollar2iiiivPrint)
    (hT : SilvermanC141TateUniformizationLiteral) (hS : GrothendieckSemistableReductionPrint) :
    Faltings1983EulerFactorRigidityQ :=
  Faltings1983EulerFactorRigidityQ_of_print
    (tateCurveTateModulePrint_of_two_prints hT (localSemistableTatePrint_of_global hS))
    decompositionGroupLocalGlobalGlue (additiveReductionCoinvariantsVanish_of_semistability hS) hF

/-- Both existing full-coefficient fields share the same bad-reduction proof.
The separate geometric reading of Shimura's quotient remains explicit. -/
theorem g0_fields_of_classical (hGeom : Shimura1973RationalGeometricReading)
    (hC : Carayol1986CorollaireRational) (hF : Faltings1983Korollar2iiiivPrint)
    (hT : SilvermanC141TateUniformizationLiteral) (hS : GrothendieckSemistableReductionPrint) :
    Carayol1986RationalNewformEulerFactors ∧ Faltings1983EulerFactorRigidityQ :=
  g0_local_factor_fields_of_prints_of_geometricReading hGeom hC hF
    (tateCurveTateModulePrint_of_two_prints hT (localSemistableTatePrint_of_global hS))
    decompositionGroupLocalGlobalGlue (additiveReductionCoinvariantsVanish_of_semistability hS)

end ZInQ.Contrib.RC53Assist.G0Prints

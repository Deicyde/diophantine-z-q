/-
tc-survey statement comparison (scratch, not a deliverable proof).

Question: does Tau Ceti's degree-two cochain comparison
`TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete` (vendored from oct16 by tc-port)
apply to the project's `PkgI6.Z2 K` (trivial `ℤ/2`), and are Tau Ceti's explicit cocycles /
coboundaries `ContCohomology.Z2`, `ContCohomology.B2` the project's `PkgI6.IsCocycle2`,
`PkgI6.IsCoboundary2`?  If yes, the cochain leaves `BrauerHasse2C`, `LocalH2CardC`, ... are
equivalent to their `continuousCohomology` forms, on which Tau Ceti's Brauer theorems land.
-/
import ZInQKernel.HDecomp.Conductor.I6Base
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison

open TauCeti.ContCohomology

namespace TCSurvey

variable (K : Type) [Field K] [CharZero K]

noncomputable instance instDMA : DistribMulAction (Field.absoluteGaloisGroup K) (PkgI6.Z2 K).V :=
  (PkgI6.Z2 K).distribMulAction

instance compactGK : CompactSpace (Field.absoluteGaloisGroup K) := by
  have : IsGalois K (AlgebraicClosure K) := {}
  exact (inferInstance : CompactSpace Gal(AlgebraicClosure K/K))

instance : LocallyCompactSpace (Field.absoluteGaloisGroup K) := inferInstance

/-- The action of `G_K` on the carrier of `Z2 K` is trivial. -/
theorem smul_triv (g : Field.absoluteGaloisGroup K) (m : (PkgI6.Z2 K).V) : g • m = m := by
  rfl

instance : ContinuousSMul (Field.absoluteGaloisGroup K) (PkgI6.Z2 K).V :=
  ⟨continuous_snd.congr fun p => (smul_triv K p.1 p.2).symm⟩

/-- The comparison instantiates on the project's `Z2 K`. -/
noncomputable def h2Equiv :
    H2 (Field.absoluteGaloisGroup K) (PkgI6.Z2 K).V ≃+ continuousCohomology 2 (PkgI6.Z2 K) :=
  (PkgI6.Z2 K).explicitH2AddEquivContinuousCohomologyOfDiscrete

/-- Tau Ceti's explicit 2-cocycles are the project's continuous inhomogeneous cocycles. -/
theorem mem_Z2_iff (ε : Field.absoluteGaloisGroup K → Field.absoluteGaloisGroup K → ZMod 2) :
    ((fun q => ε q.1 q.2 : _ → (PkgI6.Z2 K).V) ∈ Z2 (Field.absoluteGaloisGroup K) (PkgI6.Z2 K).V)
      ↔ PkgI6.IsCocycle2 ε := by
  simp only [Z2, AddSubgroup.mem_inf, AddMonoidHom.mem_ker, PkgI6.IsCocycle2, C2, mem_C1_iff,
    funext_iff, Prod.forall]
  constructor
  · rintro ⟨hc, hd⟩
    refine ⟨hc, fun a b c => ?_⟩
    have := hd a b c
    simp only [d2, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply] at this
    rwa [smul_triv K a (ε b c)] at this
  · rintro ⟨hc, hd⟩
    refine ⟨hc, fun a b c => ?_⟩
    simp only [d2, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply]
    rw [smul_triv K a (ε b c)]
    exact hd a b c

/-- Tau Ceti's explicit 2-coboundaries are the project's coboundaries. -/
theorem mem_B2_iff (ε : Field.absoluteGaloisGroup K → Field.absoluteGaloisGroup K → ZMod 2) :
    ((fun q => ε q.1 q.2 : _ → (PkgI6.Z2 K).V) ∈ B2 (Field.absoluteGaloisGroup K) (PkgI6.Z2 K).V)
      ↔ PkgI6.IsCoboundary2 ε := by
  simp only [B2, AddSubgroup.mem_map, mem_C1_iff, PkgI6.IsCoboundary2, funext_iff, Prod.forall]
  constructor
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, fun a b => by
      rw [← h a b]; simp only [d1, AddMonoidHom.coe_mk, ZeroHom.coe_mk]; rw [smul_triv K a (f b)]⟩
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, fun a b => by
      rw [h a b]; simp only [d1, AddMonoidHom.coe_mk, ZeroHom.coe_mk]; rw [smul_triv K a (f b)]⟩

end TCSurvey

#print axioms TCSurvey.h2Equiv
#print axioms TCSurvey.mem_Z2_iff
#print axioms TCSurvey.mem_B2_iff

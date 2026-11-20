import ZInQKernel.Contrib.OneProof.T10Proetale.Tower

/-!
# Discrete coefficients on the pro-étale site

The finite continuous-function sheaves in the reduction tower are genuine constant
sheaves. The map from the constant presheaf is locally bijective: use the open
fibres of a continuous function into a discrete space.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped PadicInt

namespace ZInQ.Manuscript.T10Proetale

noncomputable section

universe u

variable {X : Scheme.{u}}

/-- An open of a weakly étale object is still weakly étale over the base. -/
def proOpen {U : X.ProEt} (V : U.left.Opens) : X.ProEt :=
  .mk (V.ι ≫ U.hom)

/-- The arrow of the pro-étale site underlying the open immersion. -/
def proOpenInclusion {U : X.ProEt} (V : U.left.Opens) : proOpen V ⟶ U :=
  MorphismProperty.Over.homMk V.ι rfl

set_option backward.isDefEq.respectTransparency false in
/-- A jointly surjective family of opens of a weakly étale object covers it in the
small pro-étale site. -/
theorem proOpenCover {U : X.ProEt} {I : Type*} (V : I → U.left.Opens)
    (hV : ∀ x : U.left, ∃ i, x ∈ V i) :
    Sieve.generate (Presieve.ofArrows (fun i => proOpen (V i))
      (fun i => proOpenInclusion (V i))) ∈ Scheme.ProEt.topology X U := by
  apply Precoverage.generate_mem_toGrothendieck
  rw [Scheme.ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  change Presieve.ofArrows (fun i => (V i : Scheme)) (fun i => (V i).ι) ∈
    Scheme.proetalePrecoverage U.left
  apply Scheme.zariskiPrecoverage_le_propQCPrecoverage (P := @WeaklyEtale)
  rw [Scheme.ofArrows_mem_precoverage_iff]
  exact ⟨fun x => by
    obtain ⟨i, hi⟩ := hV x
    exact ⟨i, ⟨⟨x, hi⟩, rfl⟩⟩, fun _ => inferInstance⟩

variable (X) (B : Type) [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B]

/-- Map the constant presheaf to the presheaf of continuous functions. -/
def constantToContinuous :
    (Functor.const (X.ProEt)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u+1} B)) ⟶
      (continuousCoefficients X B).obj where
  app U := AddCommGrpCat.ofHom
    { toFun b := ULift.up (ContinuousMap.const U.unop.left b.down)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality U V f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    rfl

/-- Two constant sections that become equal agree locally, including over the empty scheme. -/
theorem constantToContinuous_locallyInjective :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) (constantToContinuous X B) := by
  constructor
  intro U a b h
  by_cases hU : Nonempty U.unop.left
  · obtain ⟨x⟩ := hU
    have hab : a = b := ULift.ext (congrArg (fun f : ULift C(U.unop.left, B) => f.down x) h)
    subst b
    rw [Presheaf.equalizerSieve_self_eq_top]
    exact (Scheme.ProEt.topology X).top_mem _
  · let : IsEmpty U.unop.left := not_nonempty_iff.mp hU
    exact (Scheme.ProEt.topology X).superset_covering bot_le (Scheme.ProEt.bot_mem_topology U.unop)

variable [DiscreteTopology B]

set_option backward.isDefEq.respectTransparency false in
/-- A section with discrete values is constant on each of its open fibres. -/
theorem constantToContinuous_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (constantToContinuous X B) := by
  constructor
  intro U s
  let f : C(U.left, B) := s.down
  let V (b : B) : U.left.Opens :=
    ⟨f ⁻¹' {b}, (isOpen_discrete _).preimage f.continuous⟩
  have hV : ∀ x : U.left, ∃ b, x ∈ V b := fun x => ⟨f x, rfl⟩
  refine (Scheme.ProEt.topology X).superset_covering
    ((Sieve.generate_le_iff _ _).mpr ?_) (proOpenCover V hV)
  rintro _ _ ⟨b⟩
  refine ⟨ULift.up b, ULift.ext (ContinuousMap.ext fun x => ?_)⟩
  change b = f ((V b).ι x)
  exact x.2.symm

/-- Continuous functions to a discrete abelian group are the associated constant
abelian sheaf on the small pro-étale site. -/
def discreteCoefficientsIso :
    (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u+1}).obj
        (AddCommGrpCat.of (ULift.{u+1} B)) ≅ continuousCoefficients X B := by
  let J := Scheme.ProEt.topology X
  let F := continuousCoefficients X B
  letI := constantToContinuous_locallyInjective X B
  letI := constantToContinuous_locallySurjective X B
  have h : IsIso ((presheafToSheaf J AddCommGrpCat.{u+1}).map (constantToContinuous X B)) :=
    (J.W_iff _).mp (J.W_of_isLocallyBijective _)
  exact (@asIso _ _ _ _ _ h) ≪≫
    asIso ((sheafificationAdjunction J _).counit.app F)

end
end ZInQ.Manuscript.T10Proetale

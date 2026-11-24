import ZInQKernel.Contrib.CMSerreTateSupport.ActualTameQuotientV003

/-!
# A topological generator of the actual tame-inertia quotient, from its two exact inputs

`ProcyclicStatement` is the exact statement of the generic compact procyclicity lemma (a compact
topological group whose open normal subgroups form a basis at `1` and whose quotients by them
are cyclic has a dense cyclic subgroup). `FiniteLayerTameCyclic` is the finite-layer statement
supplied by the finite tame-character theorem. Everything else is proved for the actual groups:
`tame_hbasis`, `tame_hcyc`, compactness and the topological-group structure of the actual tame
quotient, and the finite-layer reading `layer_agreement_of_dense`.
-/

noncomputable section
set_option autoImplicit false

universe u v

namespace ActualTameInertia

open Topology

/-- The exact statement of the generic compact procyclicity lemma, in universe `u`. -/
def ProcyclicStatement : Prop :=
  ∀ (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H],
    (∀ U ∈ 𝓝 (1 : H), ∃ N : Subgroup H, N.Normal ∧ IsOpen (N : Set H) ∧ (N : Set H) ⊆ U) →
    (∀ (N : Subgroup H) [N.Normal], IsOpen (N : Set H) → IsCyclic (H ⧸ N)) →
    ∃ g : H, Dense (Subgroup.zpowers g : Set H)

variable {K : Type v} {Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- **A topological generator of the actual tame quotient.** -/
theorem exists_tame_generator_of (hproc : ProcyclicStatement.{u}) (O : ValuationSubring K)
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (hfin : FiniteLayerTameCyclic K Ω O) :
    ∃ τ : inertiaGroup (K := K) w,
      Dense ((Subgroup.zpowers (QuotientGroup.mk τ : TameQuotient (K := K) w)) :
        Set (TameQuotient (K := K) w)) := by
  obtain ⟨g, hg⟩ := hproc (TameQuotient (K := K) w) (tame_hbasis w) (tame_hcyc O w hw hfin)
  obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective g
  exact ⟨τ, hg⟩

/-- **The generator read on finite Galois layers**: some actual inertia element `τ` is such
that on every finite Galois layer `L`, every actual inertia element agrees with `τ ^ k π` for
an actual strict-displacement element `π`. -/
theorem exists_tame_generator_layers_of (hproc : ProcyclicStatement.{u})
    (O : ValuationSubring K) (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (hfin : FiniteLayerTameCyclic K Ω O) :
    ∃ τ : inertiaGroup (K := K) w, ∀ (σ : inertiaGroup (K := K) w)
      (L : FiniteGaloisIntermediateField K Ω), ∃ k : ℤ, ∃ π ∈ wildGroup (K := K) w,
        layerRestrict w L (τ ^ k) * AlgEquiv.restrictNormalHom L.toIntermediateField π =
          layerRestrict w L σ := by
  obtain ⟨τ, hτ⟩ := exists_tame_generator_of hproc O w hw hfin
  exact ⟨τ, fun σ L => layer_agreement_of_dense w τ hτ σ L⟩

end ActualTameInertia

#print axioms ActualTameInertia.exists_tame_generator_of
#print axioms ActualTameInertia.exists_tame_generator_layers_of

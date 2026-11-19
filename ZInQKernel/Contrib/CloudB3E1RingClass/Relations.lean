import ZInQKernel.Contrib.CloudB3E1RingClass.CSTBridge

/-!
# The relation lattice of the chosen classes is finitely generated (the interface's `m_span`)

Manuscript `diophantine_zq.tex`, tex 3532–3540: `𝓡 = ker(ℤ^s → Cl(K))` with spanning vectors
`m^{(a)}`. For any classes `cls : Fin s → G` in an additive commutative group, the relation
lattice `𝓡 ⊆ ℤ^s` is finitely generated, being a subgroup of the Noetherian `ℤ`-module `ℤ^s`.
`exists_relation_basis` chooses a finite spanning family `m : Fin t → Fin s → ℤ` of relations: each
`m a` is a relation, and every relation is a `ℤ`-combination of the `m a` (the interface's
`m_span`). Kind: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

/-- **A finite spanning family of the relation lattice** (tex 3532–3540; the interface's
`m_span`). Kind: PROVED. -/
theorem exists_relation_basis {G : Type*} [AddCommGroup G] {s : ℕ} (cls : Fin s → G) :
    ∃ (t : ℕ) (m : Fin t → Fin s → ℤ), (∀ a, ∑ j, m a j • cls j = 0) ∧
      ∀ v : Fin s → ℤ, ∑ j, v j • cls j = 0 → ∃ b : Fin t → ℤ, v = ∑ a, b a • m a := by
  classical
  let φ : (Fin s → ℤ) →ₗ[ℤ] G :=
    { toFun := fun v => ∑ j, v j • cls j
      map_add' := fun v w => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c v => by simp [Finset.smul_sum, mul_smul] }
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian (LinearMap.ker φ) : (LinearMap.ker φ).FG)
  let m : Fin T.card → Fin s → ℤ := fun a => (T.equivFin.symm a : Fin s → ℤ)
  refine ⟨T.card, m, fun a => ?_, fun v hv => ?_⟩
  · have hmem : (T.equivFin.symm a : Fin s → ℤ) ∈ LinearMap.ker φ :=
      hT ▸ Submodule.subset_span (T.equivFin.symm a).2
    exact hmem
  · have hv' : v ∈ Submodule.span ℤ (T : Set (Fin s → ℤ)) := hT ▸ hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_finset'.mp hv'
    refine ⟨fun a => c (T.equivFin.symm a), ?_⟩
    rw [← hc]
    exact (Fintype.sum_equiv T.equivFin.symm _ _ (fun x => rfl)).symm

end ZInQ.Contrib.CloudB3E1RingClass

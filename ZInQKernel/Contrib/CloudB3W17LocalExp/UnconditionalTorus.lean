import ZInQKernel.Contrib.CloudB3W17LocalExp.GlobalHom
import ZInQKernel.Contrib.CloudB3W17LocalExp.ManifoldIFT
import ZInQKernel.Contrib.CloudB3W17Realify.ComplexExp

/-!
# A compact connected commutative complex Lie group is a complex torus

**Unconditional** (no hypothesis beyond the group itself): combining

* the global analytic exponential of `CloudB3W17Realify.exists_complexExp` (built from fixed real
  flows complexified through Cauchy–Riemann, with `exp 0 = 1`, `exp (x + y) = exp x * exp y`,
  `ContMDiff ω` and derivative the identity at `0`; no compactness or connectedness used),
* the analytic inverse function theorem with vector-space source and manifold target
  (`CloudB3W17LocalExp.isLocalDiffeomorphAt_of_hasMFDerivAt`),
* the globalization/surjectivity/lattice assembly (`CloudB3W17LocalExp.torus_diffeo_of_globalHom`,
  resting on `CloudB3W17Lattice.isZLattice_of_exp`),

gives: a compact connected commutative complex Lie group `G` charted on a finite-dimensional complex
normed space `E` is analytically isomorphic, as a group, to a complex torus `E ⧸ Λ` with `Λ` a discrete
full lattice.

`mumfordComplexTorus_comm` is the same statement for `E = Fin g → ℂ`: it is the conclusion of
`UnifPrinted.MumfordComplexTorus` (the H103 printed leaf) in the commutative case, with `T2Space`
dropped. Commutativity of a general compact connected complex Lie group is **not** proved here and is
not needed for abelian varieties, whose points form a commutative group.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology

noncomputable section

namespace CloudB3W17LocalExp

open BPAnalytic CloudB3W17Lattice

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [CommGroup G] [LieGroup 𝓘(ℂ, E) ω G]

/-- **The exponential of a commutative complex Lie group is a local biholomorphism at `0`.**
`CloudB3W17Realify.exists_complexExp` builds it; the inverse function theorem makes it a local
diffeomorphism. -/
theorem exists_globalExp_isLocalDiffeomorphAt :
    ∃ exp : E → G, exp 0 = 1 ∧ (∀ x y, exp (x + y) = exp x * exp y) ∧
      ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω exp ∧ IsLocalDiffeomorphAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω exp 0 := by
  have hcomplete : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨exp, h0, hadd, hsm, hd⟩ := CloudB3W17Realify.exists_complexExp (E := E) (G := G)
  have hd' : HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, E) exp 0
      ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) := hd
  exact ⟨exp, h0, hadd, hsm, isLocalDiffeomorphAt_of_hasMFDerivAt (hsm 0) hd'⟩

variable [CompactSpace G] [ConnectedSpace G]

/-- **A compact connected commutative complex Lie group is a complex torus (unconditional).**
Full form: the exponential is surjective, its kernel is a discrete full lattice `Λ`, and the induced
map `E ⧸ Λ → G` is an analytic group isomorphism. -/
theorem exists_exp_torus_diffeo :
    ∃ (exp : E → G) (Λ : Submodule ℤ E) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
      (e : Torus Λ ≃ₘ^ω⟮𝓘(ℂ, E), 𝓘(ℂ, E)⟯ G),
      Function.Surjective exp ∧ (∀ v : E, v ∈ Λ ↔ exp v = 1) ∧
        (∀ a b, e (a + b) = e a * e b) ∧ ∀ v : E, e (proj Λ v) = exp v := by
  obtain ⟨exp, h0, hadd, hsm, hloc⟩ := exists_globalExp_isLocalDiffeomorphAt (E := E) (G := G)
  obtain ⟨hsurj, Λ, hdisc, hZ, hker, e, hhom, hproj⟩ :=
    torus_diffeo_of_globalHom hadd h0 hsm (localInverseData_of_isLocalDiffeomorphAt h0 hloc)
  exact ⟨exp, Λ, hdisc, hZ, e, hsurj, hker, hhom, hproj⟩

/-- **Mumford's theorem, commutative case (unconditional).** A compact connected commutative complex
Lie group is `E ⧸ Λ` for a discrete full lattice `Λ`, analytically and as a group. -/
theorem exists_torus_diffeo :
    ∃ (Λ : Submodule ℤ E) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
      (e : Torus Λ ≃ₘ^ω⟮𝓘(ℂ, E), 𝓘(ℂ, E)⟯ G), ∀ a b, e (a + b) = e a * e b := by
  obtain ⟨-, Λ, hdisc, hZ, e, -, -, hhom, -⟩ := exists_exp_torus_diffeo (E := E) (G := G)
  exact ⟨Λ, hdisc, hZ, e, hhom⟩

end Main

/-- **The commutative case of the H103 printed leaf `UnifPrinted.MumfordComplexTorus`, proved.**
Verbatim its conclusion for a compact connected complex Lie group of dimension `g`, with `Group`
strengthened to `CommGroup` and `T2Space` dropped (it is not needed). -/
theorem mumfordComplexTorus_comm (g : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (Fin g → ℂ) X] [CommGroup X]
    (hman : IsManifold 𝓘(ℂ, Fin g → ℂ) ω X) (hlie : LieGroup 𝓘(ℂ, Fin g → ℂ) ω X)
    (hcpt : CompactSpace X) (hconn : ConnectedSpace X) :
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
      (e : Torus Λ ≃ₘ^ω⟮𝓘(ℂ, Fin g → ℂ), 𝓘(ℂ, Fin g → ℂ)⟯ X), ∀ a b, e (a + b) = e a * e b := by
  have := hman
  have := hlie
  have := hcpt
  have := hconn
  exact exists_torus_diffeo (E := Fin g → ℂ) (G := X)

end CloudB3W17LocalExp

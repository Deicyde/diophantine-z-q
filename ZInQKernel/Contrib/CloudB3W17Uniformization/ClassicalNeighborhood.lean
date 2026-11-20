import ZInQKernel.Contrib.CloudB3W17Hodge.Bridge

/-!
# Finite regular-function neighbourhoods for the actual classical topology

Attribution: adapted from host `unif-printed`, Stage 2a,
`UniformizationPrinted.lean` lines 272–341 at
`dbf043a4eb8d977b1d4bf0b03010f915b70bcfb8`. The host module is not on main.
Here the carrier, evaluation and classical topology are the genuine compiled
W17 Hodge bridge; the restriction identity is obtained through that bridge
from native `Point.evaluate_res`. The generated-topology induction proves a
neighbourhood basis, rather than assuming an analytic dictionary leaf.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter
open scoped Topology

namespace CloudB3W17Uniformization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CloudB3W17Hodge

variable {X : Over (Spec ↧ℂ)}

private noncomputable def res {U V : X.left.Opens} (h : V ≤ U) (f : Γ(X.left, U)) : Γ(X.left, V) :=
  X.left.presheaf.map (homOfLE h).op f

private theorem ptIn_mono {U V : X.left.Opens} (h : V ≤ U) {P : CPt X}
    (hP : XPtIn X P V) : XPtIn X P U :=
  hP.trans (fun _ hx => h hx)

private theorem evaluate_res {U V : X.left.Opens} (h : V ≤ U) (f : Γ(X.left, U))
    {P : CPt X} (hP : XPtIn X P V) : XevalAt X V (res h f) P = XevalAt X U f P := by
  rw [xevalAt_eq_evaluate, xevalAt_eq_evaluate]
  exact (AlgebraicGeometry.Point.evaluate_res h f (cptEquiv X P) ((ptIn_iff X P V).mp hP)).symm

private theorem finite_regular_control_of_isOpen {S : Set (CPt X)}
    (hS : IsOpen[classicalTopology X] S) :
    ∀ P₀ ∈ S, ∃ (U : X.left.Opens) (k : ℕ) (f : Fin k → Γ(X.left, U)) (ε : ℝ),
      0 < ε ∧ XPtIn X P₀ U ∧ ∀ P, XPtIn X P U →
        (∀ i, ‖XevalAt X U (f i) P - XevalAt X U (f i) P₀‖ < ε) → P ∈ S := by
  induction hS with
  | basic s hs =>
    obtain ⟨U, f, z, ε, rfl⟩ := hs
    rintro P₀ ⟨hP₀, hlt⟩
    refine ⟨U, 1, fun _ => f, ε - ‖XevalAt X U f P₀ - z‖, by linarith, hP₀,
      fun P hP hi => ?_⟩
    refine ⟨hP, ?_⟩
    have h1 := hi 0
    calc ‖XevalAt X U f P - z‖
        ≤ ‖XevalAt X U f P - XevalAt X U f P₀‖ + ‖XevalAt X U f P₀ - z‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε := by linarith
  | univ =>
    intro P₀ _
    exact ⟨⊤, 0, Fin.elim0, 1, one_pos, fun _ _ => trivial, fun _ _ _ => trivial⟩
  | inter s t _ _ hs ht =>
    rintro P₀ ⟨h₁, h₂⟩
    obtain ⟨U, k, f, ε, hε, hU, hsep⟩ := hs P₀ h₁
    obtain ⟨U', k', f', ε', hε', hU', hsep'⟩ := ht P₀ h₂
    refine ⟨U ⊓ U', k + k', Fin.append (fun i => res inf_le_left (f i))
      (fun i => res inf_le_right (f' i)), min ε ε', lt_min hε hε', ?_, fun P hP hi => ?_⟩
    · intro x hx
      exact ⟨hU hx, hU' hx⟩
    · have hPU : XPtIn X P U := ptIn_mono inf_le_left hP
      have hPU' : XPtIn X P U' := ptIn_mono inf_le_right hP
      have hP₀ : XPtIn X P₀ (U ⊓ U') := fun _ hx => ⟨hU hx, hU' hx⟩
      refine ⟨hsep P hPU fun i => ?_, hsep' P hPU' fun i => ?_⟩
      · have h := hi (Fin.castAdd k' i)
        rw [Fin.append_left, evaluate_res _ _ hP, evaluate_res _ _ hP₀] at h
        exact lt_of_lt_of_le h (min_le_left _ _)
      · have h := hi (Fin.natAdd k i)
        rw [Fin.append_right, evaluate_res _ _ hP, evaluate_res _ _ hP₀] at h
        exact lt_of_lt_of_le h (min_le_right _ _)
  | sUnion S _ hS =>
    rintro P₀ ⟨s, hs, hP₀⟩
    obtain ⟨U, k, f, ε, hε, hU, hsep⟩ := hS s hs P₀ hP₀
    exact ⟨U, k, f, ε, hε, hU, fun P hP hi => ⟨s, hs, hsep P hP hi⟩⟩

/-- Every actual classical neighbourhood contains a finite Γ-evaluation neighbourhood. -/
theorem regular_neighborhood_basis (P₀ : CPt X) (N : Set (CPt X))
    (hN : N ∈ @nhds _ (classicalTopology X) P₀) :
    ∃ (U : X.left.Opens) (k : ℕ) (f : Fin k → Γ(X.left, U)) (ε : ℝ),
      0 < ε ∧ XPtIn X P₀ U ∧ ∀ P, XPtIn X P U →
        (∀ i, ‖XevalAt X U (f i) P - XevalAt X U (f i) P₀‖ < ε) → P ∈ N := by
  let : TopologicalSpace (CPt X) := classicalTopology X
  obtain ⟨S, hSN, hS, hP₀⟩ := mem_nhds_iff.mp hN
  obtain ⟨U, k, f, ε, hε, hU, hsep⟩ := finite_regular_control_of_isOpen hS P₀ hP₀
  exact ⟨U, k, f, ε, hε, hU, fun P hP hi => hSN (hsep P hP hi)⟩

end CloudB3W17Uniformization

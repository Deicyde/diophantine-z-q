import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.SelmerLink
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.DualQuasiIso

/-!
# A degreewise injective chain map with acyclic cokernel is a quasi-isomorphism

For complexes `A, B, Q` (lane PairedFunctional's `GCx`) and chain maps `f : A → B`, `π : B → Q`
which are degreewise a short exact sequence `0 → A → B → Q → 0`, if `Q` is acyclic then `f` is a
quasi-isomorphism (PROVED, from lane SelmerDuality's `quasiIso_τ₁` applied to the morphism of short
exact sequences `(f, id, 0) : (A → B → Q) → (B → B → 0)`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (GAcyclic acyclic_toCC_iff quasiIso_of_acyclic
  quasiIso_τ₁ idGHom toCC_idGHom)

variable {S : Type} [CommRing S] {A B Q : GCx S} (f : GHom A B) (π : GHom B Q)

theorem quasiIso_of_ses (hπf : ∀ i x, π.f i i rfl (f.f i i rfl x) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl))
    (hsurj : ∀ i, Function.Surjective (π.f i i rfl))
    (hex : ∀ i y, π.f i i rfl y = 0 → ∃ x, f.f i i rfl x = y) (hQ : GAcyclic Q) :
    QuasiIso (SelmerDuality.GHom.toCC f) := by
  let S₁ : ShortComplex (CochainComplex (ModuleCat.{0} S) ℤ) :=
    ShortComplex.mk (SelmerDuality.GHom.toCC f) (SelmerDuality.GHom.toCC π) (by
      ext i x
      exact hπf i x)
  have h₁ : S₁.ShortExact := by
    refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.moduleCat_exact_iff]
      intro y hy
      exact hex i y hy
    · rw [ModuleCat.mono_iff_injective]
      exact hinj i
    · rw [ModuleCat.epi_iff_surjective]
      exact hsurj i
  let S₂ : ShortComplex (CochainComplex (ModuleCat.{0} S) ℤ) :=
    ShortComplex.mk (SelmerDuality.GHom.toCC (idGHom B))
      (SelmerDuality.GHom.toCC (ClearingComplex.zeroGHom B (zeroGCx S))) (by ext i x; rfl)
  have h₂ : S₂.ShortExact := by
    refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.moduleCat_exact_iff]
      intro c _
      exact ⟨c, rfl⟩
    · rw [ModuleCat.mono_iff_injective]
      intro a b h
      exact h
    · rw [ModuleCat.epi_iff_surjective]
      intro y
      exact ⟨0, rfl⟩
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := SelmerDuality.GHom.toCC f
      τ₂ := SelmerDuality.GHom.toCC (idGHom B)
      τ₃ := SelmerDuality.GHom.toCC (ClearingComplex.zeroGHom Q (zeroGCx S))
      comm₁₂ := by ext i x; rfl
      comm₂₃ := by ext i x; rfl }
  have hτ₂ : QuasiIso φ.τ₂ := by
    change QuasiIso (SelmerDuality.GHom.toCC (idGHom B))
    rw [toCC_idGHom]
    infer_instance
  have hz : GAcyclic (zeroGCx S) := fun _ _ _ _ _ _ _ => ⟨0, rfl⟩
  have hτ₃ : QuasiIso φ.τ₃ :=
    quasiIso_of_acyclic _ ((acyclic_toCC_iff _).2 hQ) ((acyclic_toCC_iff _).2 hz)
  exact quasiIso_τ₁ φ h₁ h₂ hτ₂ hτ₃

end ZInQ.Contrib.CloudB3RC53.ClearingComplex

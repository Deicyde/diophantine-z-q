import ZInQKernel.Contrib.OneProof.RC.CMField2.Results

/-! The pointwise CM descent input at tex 2839–2844 and 2915–2916. -/

open NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory
  ZInQ.Contrib.CloudB3RC53.CST ZInQ.Manuscript.RC.PreparedParam

namespace ZInQ.Manuscript.RC.CMScope

/-- **GLUE (unread)**: field of definition on the split modular curve.
Candidate: Gross, *Heegner points on X₀(N)* (1984), §1, UNVERIFIED.

* Tex 2839: one imaginary quadratic field, split at the primes of `2N`.
* Tex 2840: discard the two fields of discriminants `-4` and `-3`.
* Tex 2841–2844: use the order `ℤ + c 𝓞_K` for a positive conductor
  prime to `2N D_K`, with ring class field attached to that order.
* Tex 2915–2916: the primitive Heegner form gives the proper lattice
  pair of that order (level prime to the form discriminant). A fixed
  orientation is encoded by a root `β` of `D_K` modulo `4N`; the
  middle coefficient at conductor `c` reads `c * β` modulo `2N`.

The conclusion is pointwise over the abstract ring class field, as in
`CMFieldOfDefinition`. Compatibility of Galois actions, embeddings in
a tower, and norm relations are separate from this input. -/
def CMFieldOfDefinitionScoped {N : ℕ} [NeZero N] (X : X0Model N) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    Module.finrank ℚ K = 2 → IsTotallyComplex K →
    (∀ p : ℕ, p.Prime → p ∣ 2 * N → SplitsIn K p) →
    discr K ≠ -4 → discr K ≠ -3 →
    ∀ (β : ℤ), Int.ModEq (4 * (N : ℤ)) (β ^ 2) (discr K) →
    ∀ (c : ℕ) [NeZero c], Nat.Coprime c (2 * N * (discr K).natAbs) →
    ∀ (d A B C : ℤ), (conductorOrder K c).discr = d → d < 0 →
      IsCoprime d (N : ℤ) → IsHeegnerForm N d A B C →
      Int.ModEq (2 * (N : ℤ)) B ((c : ℤ) * β) →
      let H := ringClassField (conductorOrder K c)
      ∃ (ι : H →ₐ[ℚ] ℂ) (x : FieldPoint X.overQ H),
        x.map ι = X.complexPoint (cmPoint A B d)

/-- Restrict the broad pointwise assertion to the manuscript data (c). -/
theorem cmFieldOfDefinitionScoped_of_broad {N : ℕ} [NeZero N] {X : X0Model N}
    (h : CMFieldOfDefinition X) : CMFieldOfDefinitionScoped X :=
  fun K _ _ hK hc _ _ _ _ _ c _ _ d A B C hO hd hn hf _ =>
    h K hK hc (conductorOrder K c) d A B C hO hd hn hf

/-- The scoped input holds for the model of level one. -/
theorem cmFieldOfDefinitionScoped_modelOne : CMFieldOfDefinitionScoped X0Model2.modelOne :=
  cmFieldOfDefinitionScoped_of_broad CMField2.cmFieldOfDefinition_modelOne

/-- The scoped input holds for the normalized branch model at level one. -/
theorem cmFieldOfDefinitionScoped_one : CMFieldOfDefinitionScoped (X0Branch.model 1) :=
  cmFieldOfDefinitionScoped_of_broad CMField2.cmFieldOfDefinition_one

end ZInQ.Manuscript.RC.CMScope

# smooth-fibre: `SmoothFibreReduced` proved from Mathlib

## Main result (VERIFIED: compiled, `lake build ZInQKernel.Contrib.SmoothFibre.Basic`)

```lean
-- ZInQKernel/Contrib/SmoothFibre/Statement.lean (verbatim body of VertWitness.SmoothFibreReduced,
-- scratch/vert-witness/VertWitness.lean:1840)
def ZInQ.SmoothFibre.SmoothFibreReduced : Prop :=
  ∀ (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A), φ.Smooth →
    ∀ m : Ideal R, m.IsMaximal → (m.map φ).IsRadical

-- ZInQKernel/Contrib/SmoothFibre/Basic.lean
theorem ZInQ.SmoothFibre.smoothFibreReduced : SmoothFibreReduced
theorem ZInQ.SmoothFibre.isReduced_of_smooth_of_field (k A : Type*) [Field k] [CommRing A]
    [Algebra k A] [Algebra.Smooth k A] : IsReduced A
theorem ZInQ.SmoothFibre.isReduced_of_etale_of_isDomain (P S : Type*) [CommRing P] [IsDomain P]
    [CommRing S] [Algebra P S] [Algebra.Etale P S] : IsReduced S
```

`#print axioms` (scratch/smooth-fibre/Axioms.lean), for each of the three theorems:
`depends on axioms: [propext, Classical.choice, Quot.sound]`.

The statement is exactly the vert-witness one. The only difference is the namespace
(`ZInQ.SmoothFibre` rather than `VertWitness`), chosen so that the two do not clash once
vert-witness's file moves under `Contrib/`. The two bodies are identical, so
`VertWitness.specialFibreMaxIdeal_of ZInQ.SmoothFibre.smoothFibreReduced` typechecks by defeq.
That use is not compiled here, because the vert-witness file is scratch. Inside the Contrib file
`rfl` checks that the definition equals the expanded body.

## Proof (Mathlib 4.35 only)

1. **Étale over a domain ⇒ reduced.** `S` is flat over `P` (`Algebra.Smooth.flat`), so
   `S → Frac(P) ⊗_P S` is injective. `Frac(P) ⊗_P S` is étale over a field (`Algebra.Etale.baseChange`),
   hence reduced (`Algebra.FormallyUnramified.isReduced_of_field`).
2. **Smooth over a field ⇒ reduced.** Let `x ≠ 0` be nilpotent and `m ⊇ Ann(x)` a maximal ideal.
   `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial` gives `f ∉ m` such that `A_f` is
   standard étale over `k[X_1..X_n]`, a domain, so `A_f` is reduced by step 1. So `x ↦ 0` in `A_f`,
   `f^j x = 0`, and `f^j ∈ Ann(x) ⊆ m`. This contradicts `f ∉ m`.
3. **Main.** Put `φ.toAlgebra`. `RingHom.smooth_algebraMap` gives `Algebra.Smooth R A`. Base change
   gives `Algebra.Smooth (R/m) ((R/m) ⊗_R A)`, which is reduced by step 2. Then
   `A/mA ≃ A ⊗_R R/m ≃ (R/m) ⊗_R A` (`Algebra.TensorProduct.quotIdealMapEquivTensorQuot`, `comm`)
   and `Ideal.isRadical_iff_quotient_reduced` finish.

## Remaining

Nothing for this target. Consequence for vert-witness: in its finest composite
`heckeVertWitness_of_leaves (hL) (hRR) (hSR : SmoothFibreReduced) (hD) (hB)`, the argument `hSR`
can be discharged by `ZInQ.SmoothFibre.smoothFibreReduced`.

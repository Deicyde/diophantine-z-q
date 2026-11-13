import ZInQKernel.Contrib.UnramifiedCocycle.CyclotomicQuotient

/-!
# The exact local embedding and a genuine finite local container

The embedding is the `IsAlgClosed.lift` selected by the actual baseline `resp`,
with the same scalar-algebra construction as `Field.absoluteGaloisGroup.map`.
It is not identified with another separately chosen embedding.  The local
container is constructed by scalar extension and normal closure, not assumed
as a local-field model.
-/

namespace ZInQ.Contrib.UnramifiedCocycle

open GlueDescent.B2Q
open ZInQ.Contrib.LocalSquareRoot
open IntermediateField

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- Exactly the ring embedding used by `resp`. -/
noncomputable def localClosureEmbedding (p : Nat.Primes) :
    AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[p] :=
  let _ : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  let e : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p] := IsAlgClosed.lift
  e.toRingHom

/-- Regard that same ring map as a rational algebra map, without making a new
choice of an algebraic-closure embedding. -/
noncomputable def localClosureAlgEmbedding (p : Nat.Primes) :
    AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p] :=
  (localClosureEmbedding p).toRatAlgHom

noncomputable def localAct (p : Nat.Primes) (g : GQp p) :
    Gal(AlgebraicClosure ℚ_[p]/ℚ_[p]) := g

/-- The actual local/global action compatibility, at every algebraic element. -/
theorem localClosureEmbedding_intertwines (p : Nat.Primes) (g : GQp p)
    (x : AlgebraicClosure ℚ) :
    localAct p g (localClosureEmbedding p x) =
      localClosureEmbedding p (act (resp p g) x) :=
  absoluteGalois_map_intertwines (algebraMap ℚ ℚ_[p]) (localAct p g) x

/-- Images of an actual finite rational basis of the original field. -/
noncomputable def localBasisSet (p : Nat.Primes)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] :
    Set (AlgebraicClosure ℚ_[p]) :=
  Set.range (fun i : Fin (Module.finrank ℚ L) =>
    localClosureEmbedding p ((Module.finBasis ℚ L i : L) : AlgebraicClosure ℚ))

/-- The finite scalar-extended image, constructed from a finite basis. -/
noncomputable def localImageAdjoin (p : Nat.Primes)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] :
    IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]) :=
  adjoin ℚ_[p] (localBasisSet p L)

theorem localImageAdjoin_finite (p : Nat.Primes)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] :
    FiniteDimensional ℚ_[p] (localImageAdjoin p L) := by
  let : Finite (localBasisSet p L) := (Set.finite_range _).to_subtype
  exact IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral x)

/-- The basis construction covers EVERY element of the original global field. -/
theorem localClosureEmbedding_mem_adjoin (p : Nat.Primes)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] (x : L) :
    localClosureEmbedding p (x : AlgebraicClosure ℚ) ∈ localImageAdjoin p L := by
  let b := Module.finBasis ℚ L
  let f : L →ₐ[ℚ] AlgebraicClosure ℚ_[p] := (localClosureAlgEmbedding p).comp L.val
  have he : f x = ∑ i : Fin (Module.finrank ℚ L),
      (algebraMap ℚ ℚ_[p] (b.repr x i)) • f (b i) := by
    have h := congrArg f (b.sum_repr x)
    rw [map_sum] at h
    calc
      f x = ∑ i : Fin (Module.finrank ℚ L), f ((b.repr x i) • b i) := h.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Algebra.smul_def, map_mul, f.commutes]
        exact congrArg (fun a => a * f (b i))
          (((algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).toRatAlgHom).commutes (b.repr x i)).symm
  change f x ∈ (localImageAdjoin p L).toSubalgebra.toSubmodule
  rw [he]
  apply (localImageAdjoin p L).toSubalgebra.toSubmodule.sum_mem
  intro i _
  apply (localImageAdjoin p L).toSubalgebra.toSubmodule.smul_mem
  exact IntermediateField.subset_adjoin ℚ_[p] (localBasisSet p L) ⟨i, rfl⟩

/-- A constructed finite Galois local field containing the original image and
all roots at the required positive prime-to-p cyclotomic level. -/
noncomputable def localContainer (p : Nat.Primes)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    (n : ℕ) [NeZero n] : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]) :=
  normalClosure ℚ_[p] (localImageAdjoin p L) (AlgebraicClosure ℚ_[p]) ⊔
    GlueSqrtDisj.muField (p : ℕ) (unramifiedLevel p n)

instance localContainer_finite (p : Nat.Primes)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    (n : ℕ) [NeZero n] : FiniteDimensional ℚ_[p] (localContainer p L n) := by
  let : FiniteDimensional ℚ_[p] (localImageAdjoin p L) := localImageAdjoin_finite p L
  let : FiniteDimensional ℚ_[p]
    (normalClosure ℚ_[p] (localImageAdjoin p L) (AlgebraicClosure ℚ_[p])) :=
    normalClosure.is_finiteDimensional ℚ_[p] (localImageAdjoin p L) (AlgebraicClosure ℚ_[p])
  change FiniteDimensional ℚ_[p]
    (normalClosure ℚ_[p] (localImageAdjoin p L) (AlgebraicClosure ℚ_[p]) ⊔
      GlueSqrtDisj.muField (p : ℕ) (unramifiedLevel p n) :
        IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
  exact IntermediateField.finiteDimensional_sup _ _

instance localContainer_galois (p : Nat.Primes)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    (n : ℕ) [NeZero n] : IsGalois ℚ_[p] (localContainer p L n) := by
  let : IsGalois ℚ_[p]
    (normalClosure ℚ_[p] (localImageAdjoin p L) (AlgebraicClosure ℚ_[p])) :=
    IsGalois.normalClosure ℚ_[p] (localImageAdjoin p L) (AlgebraicClosure ℚ_[p])
  change IsGalois ℚ_[p]
    (normalClosure ℚ_[p] (localImageAdjoin p L) (AlgebraicClosure ℚ_[p]) ⊔
      GlueSqrtDisj.muField (p : ℕ) (unramifiedLevel p n) :
        IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
  infer_instance

theorem localClosureEmbedding_mem_container (p : Nat.Primes)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    (n : ℕ) [NeZero n] (x : AlgebraicClosure ℚ) (hx : x ∈ L) :
    localClosureEmbedding p x ∈ localContainer p L n := by
  exact (show normalClosure ℚ_[p] (localImageAdjoin p L) (AlgebraicClosure ℚ_[p]) ≤
      localContainer p L n from le_sup_left)
    ((IntermediateField.le_normalClosure (localImageAdjoin p L))
      (localClosureEmbedding_mem_adjoin p L ⟨x, hx⟩))

theorem root_mem_container (p : Nat.Primes)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    (n : ℕ) [NeZero n] (ζ : AlgebraicClosure ℚ_[p])
    (hζ : ζ ^ unramifiedLevel p n = 1) : ζ ∈ localContainer p L n := by
  exact (show GlueSqrtDisj.muField (p : ℕ) (unramifiedLevel p n) ≤ localContainer p L n
      from le_sup_right) (IntermediateField.subset_adjoin ℚ_[p] _ hζ)

end ZInQ.Contrib.UnramifiedCocycle

import Mathlib

/-!
# Lane RC6: the local printed theorems behind the table of `ex:limits-residual-bound`

The proof of Lemma `ex:limits-residual-bound` (manuscript tex 4544–4550) cites
"Local duality and the local Euler characteristic [Milne, I.2.3 and I.2.8]" to get, for the
trivial module `W = E[2] = 𝔽₂²` over a completion `K_w`,
`(h⁰, h¹, h²)(K_w, W) = (2, 4 + 2d_w, 2)`.

Both printed theorems concern genuine objects that exist in Mathlib: finite extensions `F` of
`ℚ_p`, their absolute Galois groups `Field.absoluteGaloisGroup F` with the Krull topology, and the
continuous cohomology `continuousCohomology n M` of a topological representation `M`.  They are
stated below as `PRINT` propositions (definitions of type `Prop`, not axioms), with locators checked
against the print:

* J. S. Milne, *Arithmetic Duality Theorems*, second edition (BookSurge, 2006; electronic version
  2006), Chapter I: Corollary 2.3 (p. 28), the sentence preceding Theorem 2.8 and Theorem 2.8
  (p. 31).

The consequence used by Elliot is then `PROVED` from them (`local_cohomology_dims`).

Conventions.  Mathlib's `continuousCohomology` is the cohomology of homogeneous continuous cochains
`C(G, C(G, …, C(G, M)))`; for a profinite group and a discrete module this is the usual continuous
cochain cohomology (GLUE: the standard comparison, listed as a TODO in Mathlib).  Mathlib's
`ContRepresentation` does not require the action to be continuous in the group variable, so the
statements carry the hypothesis that the action map `G × M → M` is continuous (a discrete Galois
module in Milne's sense).
-/

namespace ZInQ.Manuscript.RC.Limits

open CategoryTheory

/-- The trivial representation of the absolute Galois group of `F` on a discrete `𝔽₂`-vector
space `V`, as an object of `TopRep (ZMod 2) G_F`. -/
noncomputable abbrev trivialGaloisRep (F : Type) [Field F] (V : Type) [AddCommGroup V]
    [Module (ZMod 2) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul (ZMod 2) V] : TopRep (ZMod 2) (Field.absoluteGaloisGroup F) :=
  TopRep.of (ContRepresentation.trivial (ZMod 2) (Field.absoluteGaloisGroup F) V)

/-- **PRINT — Milne, *Arithmetic Duality Theorems*, 2nd ed. (2006), Ch. I, p. 31: the sentence
preceding Theorem 2.8, and Theorem 2.8 (the local Euler–Poincaré characteristic)**, for finite
discrete `𝔽₂`-representations.  Used at tex 4546–4550.

Milne: for a nonarchimedean local field `K` with ring of integers `R` and a finite `G_K`-module `M`
of order `m` prime to `char K`, the groups `H^r(G, M)` are finite, zero for `r > 2`, and
`χ(G, M) = [H⁰(G,M)][H²(G,M)]/[H¹(G,M)] = (R : mR)⁻¹`.  For `K = F` a finite extension of `ℚ_p`
and `M` an `𝔽₂`-vector space of dimension `n`, `m = 2ⁿ` and `(R : mR) = 2^{n[F:ℚ₂]}` if `p = 2`,
`= 1` if `p` is odd; in dimensions this is
`h⁰ − h¹ + h² = −[F : ℚ₂]·n` if `p = 2`, and `0` otherwise. -/
def MilneADT_I_2_8 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (M : TopRep.{0} (ZMod 2) (Field.absoluteGaloisGroup F)),
    Finite M → DiscreteTopology M →
    Continuous (fun x : Field.absoluteGaloisGroup F × M => M.ρ x.1 x.2) →
    (∀ n, Module.Finite (ZMod 2) (continuousCohomology n M)) ∧
    (∀ n, 2 < n → Subsingleton (continuousCohomology n M)) ∧
    ((Module.finrank (ZMod 2) (continuousCohomology 0 M) : ℤ) -
        Module.finrank (ZMod 2) (continuousCohomology 1 M) +
        Module.finrank (ZMod 2) (continuousCohomology 2 M) =
      -(if p = 2 then (Module.finrank ℚ_[p] F : ℤ) * Module.finrank (ZMod 2) M else 0))

/-- **PRINT — Milne, *Arithmetic Duality Theorems*, 2nd ed. (2006), Ch. I, Corollary 2.3 (p. 28)
(local duality), specialized to finite trivial `𝔽₂`-modules.**  Used at tex 4546–4550.

Milne: for a finitely generated `G_K`-module `M` with torsion of order prime to `char K`, cup
product gives `H^r(G, M^D) ≅ H^{2−r}(G, M)^*` for `r ≥ 1` and `H⁰(G, M^D)^∧ ≅ H²(G, M)^*`, where
`M^D = Hom(M, K_s^×)`.  For `K = F` of characteristic zero and `M = V` a finite trivial
`𝔽₂`-module, `M^D = Hom(V, μ₂)` with `μ₂ = {±1} ⊂ F`, again a trivial module of dimension `dim V`;
so `H²(G_F, V)` has dimension `dim V`.  (The specialization uses only `μ₂ ⊂ F`.) -/
def MilneADT_I_2_3_trivial : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul (ZMod 2) V], Finite V → DiscreteTopology V →
    Module.finrank (ZMod 2) (continuousCohomology 2 (trivialGaloisRep F V)) =
      Module.finrank (ZMod 2) V

/-- `H⁰` of a trivial representation is the whole module.  PROVED, from Mathlib's identification
`ContinuousCohomology.zeroIso : H⁰(G, A) ≅ A^G`. -/
theorem finrank_H0_trivialGaloisRep (F : Type) [Field F] (V : Type) [AddCommGroup V]
    [Module (ZMod 2) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul (ZMod 2) V] :
    Module.finrank (ZMod 2) (continuousCohomology 0 (trivialGaloisRep F V)) =
      Module.finrank (ZMod 2) V := by
  have e := (ContinuousCohomology.zeroIso (trivialGaloisRep F V)).toContinuousLinearEquiv
  rw [e.toLinearEquiv.finrank_eq]
  have htop : (trivialGaloisRep F V).ρ.invariants = ⊤ := by
    ext v
    simp only [Submodule.mem_top, iff_true]
    rw [ContRepresentation.mem_invariants]
    intro g
    rfl
  change Module.finrank (ZMod 2) ((trivialGaloisRep F V).ρ.invariants) = _
  rw [htop, finrank_top]

/-- The trivial representation is a discrete Galois module: its action map is continuous. -/
theorem continuous_trivialGaloisRep_action (F : Type) [Field F] (V : Type) [AddCommGroup V]
    [Module (ZMod 2) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul (ZMod 2) V] :
    Continuous (fun x : Field.absoluteGaloisGroup F × trivialGaloisRep F V =>
      (trivialGaloisRep F V).ρ x.1 x.2) :=
  continuous_snd

/-- **The local cohomology of `W = 𝔽₂²`** (tex 4545–4550):
`(h⁰, h¹, h²)(K_w, W) = (2, 4 + 2d_w, 2)` with `d_w = [K_w : ℚ₂]` if `w ∣ 2` and `d_w = 0`
otherwise.  PROVED from the two PRINT propositions above (and `finrank_H0_trivialGaloisRep`). -/
theorem local_cohomology_dims (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] :
    let W := trivialGaloisRep F (Fin 2 → ZMod 2)
    let d : ℕ := if p = 2 then Module.finrank ℚ_[p] F else 0
    Module.finrank (ZMod 2) (continuousCohomology 0 W) = 2 ∧
      Module.finrank (ZMod 2) (continuousCohomology 1 W) = 4 + 2 * d ∧
      Module.finrank (ZMod 2) (continuousCohomology 2 W) = 2 := by
  intro W d
  have hV : Module.finrank (ZMod 2) (Fin 2 → ZMod 2) = 2 := by simp
  have h0 : Module.finrank (ZMod 2) (continuousCohomology 0 W) = 2 := by
    rw [finrank_H0_trivialGaloisRep]; exact hV
  have h2 : Module.finrank (ZMod 2) (continuousCohomology 2 W) = 2 := by
    rw [h23 p F (Fin 2 → ZMod 2) inferInstance inferInstance]; exact hV
  obtain ⟨-, -, hχ⟩ := h28 p F W (inferInstanceAs (Finite (Fin 2 → ZMod 2)))
    (inferInstanceAs (DiscreteTopology (Fin 2 → ZMod 2)))
    (continuous_trivialGaloisRep_action F (Fin 2 → ZMod 2))
  have hW : Module.finrank (ZMod 2) W = 2 := hV
  rw [h0, h2, hW] at hχ
  refine ⟨h0, ?_, h2⟩
  by_cases hp : p = 2
  · simp only [hp, ite_true] at hχ
    have : d = Module.finrank ℚ_[p] F := by simp [d, hp]
    rw [this]
    omega
  · simp only [hp, ite_false] at hχ
    have : d = 0 := by simp [d, hp]
    rw [this]
    omega

end ZInQ.Manuscript.RC.Limits

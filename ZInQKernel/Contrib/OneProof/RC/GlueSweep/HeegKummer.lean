import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.Kummer
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Interfaces

/-!
# Lane RC22 (glue sweep), share Heeg: (H7) with the genuine Kummer sequence

Manuscript `diophantine_zq.tex` (11/5), Proposition `ex:arith-finite-heegner`, (H7), tex 2992–3002:
the derivative class `c_{I,a} = δ_a(C_π D_I y_{f n_I})` is `Gal(M_I/H_f)`-invariant.

Lane RC10 proves (H7) as `ZInQ.Manuscript.RC.HeegnerAlgebra.H7_assembled` from an abstract Kummer
sequence `KummerSequence Γ P HV HE a` (a `GLUE` interface: the Kummer map is equivariant, kills
`2^a P`, and is exact into `H¹(F, E)`).  The interface is constructed over genuine continuous
cohomology in `ZInQ.Contrib.CloudB3RC53.HeegnerCohomology`: `kummerSequenceGenuine` (any short
exact sequence `0 → A → B → B → 0` of discrete modules with second map `2^a`) and
`kummerSequenceTorsion` (the sequence `0 → E[2^a] → E → E → 0` of an elliptic curve, `2`
invertible).  Here the hypothesis is removed: (H7) is restated with the genuine Kummer map (the
connecting map
`δ⁰` of the restricted sequence) and the genuine conjugation action `explicitConj1` of `G` on
`H¹(N, A)`; the remaining inputs are exactly those of the constructions plus RC10's
`DerivativeInput` (the norm relations of Cai–Chen–Liu, unweighted, so the print once the unit
index `u_1 = [𝒪_K^× : ℤ^×]` is one, `D_K < -4`, and the generators of (H5), `PRINT`/`GLUE`)
and the precision hypothesis (H12) (gap B1-a).
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Heeg

open TauCeti.ContCohomology
open ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

section Genuine

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]

/-- **(H7) with the genuine Kummer sequence**, tex 2992–3002 (and 3089–3096 for gap B1-a).
Kind: `PROVED`, from the remaining hypotheses: a short exact sequence `S : 0 → A → B → B → 0` of
discrete `G`-modules whose second map is multiplication by `2^a` (for `0 → E[2^a] → E → E → 0`,
`G = G_{H_f}`), a normal subgroup `N` (for `G_{M_I}`), RC10's `DerivativeInput` over
`Γ = G ⧸ N` acting on `P = H⁰(N, B)` (for `E(M_I)`), and (H12) at every prime of `I`.  Conclusion:
for every `g ∈ G`, the conjugation `explicitConj1 N g` fixes the genuine Kummer class
`δ⁰(C_π D_I y_{f n_I}) ∈ H¹(N, A)`.

Consumer: `ZInQ.Manuscript.RC.HeegnerAlgebra.H7_assembled` (lane RC10, its `KummerSequence`
hypothesis).  Discharger: `ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.kummerSequenceGenuine`. -/
theorem H7_assembled_genuine (N : Subgroup G) [N.Normal] (a : ℕ) (S : DiscreteShortExact G A B B)
    (hproj : ∀ b, S.proj b = ((2 : ℤ) ^ a) • b)
    {ι 𝒜 : Type*} [DecidableEq ι] [CommRing 𝒜] [Module 𝒜 (H0 N B)]
    (I : Finset ι) (Din : DerivativeInput ι 𝒜 (G ⧸ N) (H0 N B) I) (Cπ : ℤ)
    (hH12 : ∀ i ∈ I, (2 : ℤ) ^ (a + 1) ∣ Din.aℓ i ∧ (2 : ℤ) ^ (a + 1) ∣ Din.ℓnum i + 1) (g : G) :
    explicitConj1 N g
        ((S.restrict N).explicitDelta0 (((Cπ : 𝒜) * ∏ j ∈ I, Din.D j) • Din.y I)) =
      (S.restrict N).explicitDelta0 (((Cπ : 𝒜) * ∏ j ∈ I, Din.D j) • Din.y I) :=
  H7_assembled I a (kummerSequenceGenuine N a S hproj) Din Cπ hH12 (g : G ⧸ N)

end Genuine

section Elliptic

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **(H7) for the Kummer sequence of an elliptic curve**, tex 2992–3002 (and 3089–3096).
Kind: `PROVED`, from the remaining hypotheses: an elliptic curve `E/K` (for `K = H_f`) given by a
Weierstrass model, `2^a` invertible in `K`, a normal subgroup `N` of the absolute Galois group
`G_K` (for `G_{M_I}`), RC10's `DerivativeInput` over `Γ = G_K ⧸ N` acting on `E(K^sep)^N` (for
`E(M_I)`), and (H12) at every prime of `I`.  Conclusion: for every `g ∈ G_K`, the conjugation
`explicitConj1 N g` fixes the genuine Kummer class `δ_a(C_π D_I y_{f n_I}) ∈ H¹(N, E[2^a])`, the
connecting map of `0 → E[2^a] → E → E → 0` restricted to `N`.

Consumer: `ZInQ.Manuscript.RC.HeegnerAlgebra.H7_assembled` (lane RC10).  Discharger:
`ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.kummerSequenceTorsion`. -/
theorem H7_assembled_torsion (a : ℕ) (h2 : IsUnit ((2 ^ a : ℕ) : K))
    (N : Subgroup (TauCeti.AbsoluteGaloisGroup K)) [N.Normal]
    {ι 𝒜 : Type*} [DecidableEq ι] [CommRing 𝒜] [Module 𝒜 (H0 N W.PointCoeff)]
    (I : Finset ι) (Din : DerivativeInput ι 𝒜 (TauCeti.AbsoluteGaloisGroup K ⧸ N)
      (H0 N W.PointCoeff) I) (Cπ : ℤ)
    (hH12 : ∀ i ∈ I, (2 : ℤ) ^ (a + 1) ∣ Din.aℓ i ∧ (2 : ℤ) ^ (a + 1) ∣ Din.ℓnum i + 1)
    (g : TauCeti.AbsoluteGaloisGroup K) :
    explicitConj1 N g (((W.kummerShortExact (2 ^ a) h2).restrict N).explicitDelta0
        (((Cπ : 𝒜) * ∏ j ∈ I, Din.D j) • Din.y I)) =
      ((W.kummerShortExact (2 ^ a) h2).restrict N).explicitDelta0
        (((Cπ : 𝒜) * ∏ j ∈ I, Din.D j) • Din.y I) :=
  H7_assembled I a (kummerSequenceTorsion W a h2 N) Din Cπ hH12
    (g : TauCeti.AbsoluteGaloisGroup K ⧸ N)

end Elliptic

end ZInQ.Manuscript.RC.GlueSweep.Heeg

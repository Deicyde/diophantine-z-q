import ZInQKernel.Contrib.CloudB3E2Norm.OldStrict

/-!
# The local identity at the old places

Manuscript `diophantine_zq.tex`, tex 3251–3270 (paragraph 7: "Localizing (H21) separates the cosets
into decomposition-group orbits: this is the local Mackey formula, a sum of the local
corestrictions from the transported places … Kummer of this sum equals the cohomological
transfer … Thus the old Kummer conditions proved in paragraph 5 survive (H20)").

**Scope.** This file works at the Shapiro level of (H20): one coefficient ring `k` for the points'
ambient module, the genuine coefficient module and the character, which must not kill the
points' division (e.g. `ℤ[Δ_f]` with the universal character; see "Coefficient ring" below). At
that level, the localization at an old place `v` of the genuine transferred Kummer class
`z_T = 𝒯_θ(κ(Q_T))` lies in the local Kummer condition (`kummerConditionIn`, lanes RC28/RC29),
from ONE named open statement, the coefficient/twist identification
`LocalTwistIdentification`, and the realization of the actual points (`hreal`). The passage to
the stage ring `A_i` with `θ = χ_h Ψ_i` is the coefficient push (H20), named separately as
`H20CoefficientPush` (`H20Push.lean`); the stage-level norm identity follows from the
Shapiro-level one and that push (`hzR_of_H20`). So the actual stage-level `hzR` is conditional on
`LocalTwistIdentification`, `hreal` and `H20CoefficientPush` (with the further inputs listed in
the earlier files), not on the first two alone.

* **The group-theoretic part (PROVED).** In degree one the transferred Kummer cocycle is the
  Kummer cocycle `g ↦ R(g) P̃ − P̃` of the weighted point `P̃ = ∑_δ R(r_δ) Q`, a division point of
  the weighted sum `P = ∑_δ R(r_δ) y` (`TwistedTransfer.kummer_weighted_sum`); restricted to the
  decomposition group it is the local Kummer cocycle of the same point. For any partition of
  `G/H` into finite sets (e.g. the orbits of the decomposition group, the double cosets
  `G_v \ G / G_{H_T}`), the weighted sum is the sum of the orbit sums (`wsum_eq_sum_orbitSum`),
  and an orbit sum `P_O = ∑_{δ ∈ O} R(r_δ) y` is fixed by every `g` stabilizing `O`
  (`orbitSum_fixed`); `realization_of_orbits` assembles realizations orbit by orbit. The
  identification of `P_O` with the local norm from the place of `H_T` above `v` corresponding to
  `O` is NOT formalized here: it is part of the realization input `hreal`.
* **`LocalTwistIdentification ψ jB` (Prop; kind GLUE).** A local ambient module `L` with
  `G_{K_v}`-action, a `k`-linear map `ψ : D → L` from the global ambient module (for the text:
  induced by an embedding `K_S → K̄_v`) and an additive map `jB : B(K̄_v) → L` from the points of
  the local twist `B = E^{(h)}` over `K̄_v`, such that: `ψ ∘ ι` is injective on the genuine
  coefficient module `M`; every `m`-torsion element of `L` comes from `M`; `ψ` and `jB` are
  equivariant (for the twisted action `R ∘ p_v` on `D`); and on `m`-torsion, `ψ ∘ ι ∘ ι_v = jB`,
  where `ι_v : B(K̄_v)[m] → M` is the Kummer coefficient map of the local condition (lane RC29's
  `kummerIota`). For the text this is the twist identification `E^{(h)}[2^i] ≅ E[2^i](χ_h)` over
  `K̄_v`, the comparison of points along `K_S → K̄_v`, and `t ↦ 1 ⊗ t` (the GLUE input recorded in
  `CoefModules/KummerAt.lean`).
* **The realization `hreal`.** `ψ(P) = ∑_j a_j • jB(P_j)` for local rational points `P_j ∈ B(K_v)`
  and scalars `a_j` (the actual points' local norms are `k`-combinations of local points of the
  twist).
* **`local_kummer_identity`** (PROVED): under the two, for every genuine cochain `z` with
  `ι ∘ z = 𝒯_θ(κ(Q))`, there is `m₀ ∈ M` with
  `z(p_v σ) = ∑_j a_j • ι_v(κ_{P_j}(σ)) + (σ m₀ − m₀)` for every `σ ∈ G_{K_v}`.
* **`res_mem_kummer_at`** (PROVED): hence the localization `res_v a` of a genuine cochain lies in
  the image of the local Kummer condition `kummerConditionIn k ι_v` (the explicit retained
  boundary is the constant `0`-cochain `m₀`).
* **`kummerOldConditions`** (definition) and **`exists_oldLift_of_inputs`** (PROVED): with the
  Kummer conditions at the old places `S₀`, the old-place strict-lift hypothesis
  (`∃ u, ι u = res a`) of the genuine Selmer data follows from `LocalTwistIdentification` and the
  realization at every old place (`OldPlaceInput`); `exists_hRloc_of_oldInputs` (PROVED): `hRloc`
  of `hzR_genuine_of_strictLifts` at the genuine relaxed data.
* Non-vacuity: `nonVacuity_localTwist_identity` (non-degenerate: `ι_v` injective, `M = B(K̄)[m]`),
  `nonVacuity_localTwist`, `nonVacuity_oldPlaceInput` (trivial `M`).

**Coefficient ring.** The framework (one coefficient ring `k` for the ambient module `D` of the
points, the genuine coefficient module `M` and the character `θ`) must be instantiated at a ring
over which the ambient modules are not killed by `m`, e.g. the group ring `ℤ[Δ_f]` of the ring
class group with its universal character `δ ↦ [δ]` (the Shapiro level of (H20), tex 3203–3215,
with `D = E(K̄) ⊗ ℤ[Δ_f]`, `M = E[2^m] ⊗ ℤ[Δ_f]`). At the stage ring `A_i = Acoef i` (with
`2^i = 0`) every module is `2^i`-torsion: division points degenerate (`2^i Q = y` forces `y = 0`),
and for `m = 2^i` every additive map from the divisible group `B(K̄_v)` to an `A_i`-module is zero,
so `LocalTwistIdentification` with a nonzero `ι_v` is uninhabitable. The passage to `A_i` and the
actual character `θ = χ_h Ψ_i` is the coefficient map of (H20) (`v ⊗ [δ] ↦ θ(δ) v`), applied to
the Selmer complexes AFTER the identity; it is not formalized here. (The `[Field k]` binder of the
genuine wrappers is removed in `StageRing.lean`.)

**What remains**: (1) `LocalTwistIdentification` itself (GLUE as above), at a coefficient ring
as in the previous paragraph; (2) the realization `hreal` of the actual points at the old places
(the orbit sums of the Heegner points over the ring class fields `H_T` as local norms, and these as
points of the local twist over `K_v`); (3) the coefficient change `ℤ[Δ_f] → A_i`, `δ ↦ θ(δ)`, of
(H20) for the Selmer complexes and their local conditions: the open statement
`H20CoefficientPush` (`H20Push.lean`, tex 3203–3215, 3262–3270, 3281–3290).

Kinds: definitions and PROVED; `LocalTwistIdentification` is the GLUE statement left open.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules

/-! ### Orbit decomposition of the weighted sum (the local Mackey formula in degree zero) -/

section Orbits

variable {G : Type*} [Group G] {k : Type*} [CommRing k] {D : Type*} [AddCommGroup D] [Module k D]
  (ρ : G →* Module.End k D) (H : Subgroup G) [H.Normal] (r : G ⧸ H → G)
  (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ) (θ : G ⧸ H →* kˣ)

/-- **The orbit sum** `P_O = ∑_{δ ∈ O} R(r_δ) x` over a set `O ⊆ G/H` (for a decomposition-group
orbit: the local norm from the corresponding place). Kind: definition. -/
def orbitSum (O : Finset (G ⧸ H)) (x : D) : D := ∑ δ ∈ O, R H ρ θ (r δ) x

/-- **The weighted sum is the sum of the orbit sums** (PROVED) for a partition of `G/H` into
pairwise disjoint sets. -/
theorem wsum_eq_sum_orbitSum [Fintype (G ⧸ H)] [DecidableEq (G ⧸ H)] {ι : Type*} (s : Finset ι)
    (O : ι → Finset (G ⧸ H)) (hdisj : (s : Set ι).PairwiseDisjoint O)
    (hcover : s.biUnion O = Finset.univ) (x : D) :
    wsum ρ H r θ x = ∑ i ∈ s, orbitSum ρ H r θ (O i) x := by
  rw [wsum, ← hcover, Finset.sum_biUnion hdisj]
  rfl

include hr in
/-- **An orbit sum of an `H`-fixed element is fixed by every `g` stabilizing the orbit**
(PROVED): `R(g) P_O = P_O` when `g O = O`. -/
theorem orbitSum_fixed (g : G) (O : Finset (G ⧸ H))
    (hO : ∀ δ ∈ O, (g : G ⧸ H) * δ ∈ O) (hO' : ∀ δ ∈ O, (g⁻¹ : G ⧸ H) * δ ∈ O) {y : D}
    (hy : ∀ h ∈ H, ρ h y = y) :
    R H ρ θ g (orbitSum ρ H r θ O y) = orbitSum ρ H r θ O y := by
  simp only [orbitSum, map_sum]
  have key : ∀ δ : G ⧸ H, R H ρ θ g (R H ρ θ (r δ) y) = R H ρ θ (r ((g : G ⧸ H) * δ)) y := by
    intro δ
    rw [← Module.End.mul_apply, ← R_r_mul_hc H r hr ρ θ g δ, Module.End.mul_apply,
      hy _ (hc_mem H r hr g δ)]
  simp_rw [key]
  refine Finset.sum_bij' (fun δ _ => (g : G ⧸ H) * δ) (fun δ _ => (g⁻¹ : G ⧸ H) * δ)
    (fun δ hδ => hO δ hδ) (fun δ hδ => hO' δ hδ) (fun δ _ => ?_) (fun δ _ => ?_)
    (fun δ _ => rfl)
  · simp [← mul_assoc]
  · simp [← mul_assoc]

/-- **Realization orbit by orbit** (PROVED): if the image of every orbit sum of a partition is a
`k`-combination `∑_j a i j • e i j`, so is the image of the weighted sum (indexed by pairs). -/
theorem realization_of_orbits [Fintype (G ⧸ H)] [DecidableEq (G ⧸ H)] {L : Type*}
    [AddCommGroup L] [Module k L] (ψ : D →ₗ[k] L) {ι : Type*} (s : Finset ι)
    (O : ι → Finset (G ⧸ H)) (hdisj : (s : Set ι).PairwiseDisjoint O)
    (hcover : s.biUnion O = Finset.univ) (x : D) {J : ι → Type*} (t : ∀ i, Finset (J i))
    (a : ∀ i, J i → k) (e : ∀ i, J i → L)
    (h : ∀ i ∈ s, ψ (orbitSum ρ H r θ (O i) x) = ∑ j ∈ t i, a i j • e i j) :
    ψ (wsum ρ H r θ x) = ∑ p ∈ s.sigma t, a p.1 p.2 • e p.1 p.2 := by
  rw [wsum_eq_sum_orbitSum ρ H r θ s O hdisj hcover, map_sum, Finset.sum_sigma]
  exact Finset.sum_congr rfl h

end Orbits

/-! ### The open statement and the pointwise local identity -/

section Pointwise

variable {G : Type*} [Group G] {k : Type*} [CommRing k] {D : Type*} [AddCommGroup D] [Module k D]
  (ρ : G →* Module.End k D) (H : Subgroup G) [H.Normal]
  (θ : G ⧸ H →* kˣ) {M : Type*} [AddCommGroup M] [Module k M] [DistribMulAction G M]
  (ι : M →ₗ[k] D)
  {F : Type} [Field F] [CharZero F] [DecidableEq F] (B : WeierstrassCurve F) [B.IsElliptic]
  (m : ℕ) [NeZero m] (φ : Field.absoluteGaloisGroup F →* G) (ιv : TorsAlg F B m →+ M)
  {L : Type*} [AddCommGroup L] [Module k L] [DistribMulAction (Field.absoluteGaloisGroup F) L]
  (ψ : D →ₗ[k] L) (jB : PtAlg F B →+ L)

/-- **The coefficient/twist identification at an old place** (Prop; kind GLUE; tex 3251–3270 with
the coefficient maps of tex 3413–3438). A local ambient module `L` with `G_{K_v}`-action, a
`k`-linear `ψ : D → L` (for the text: induced by an embedding `K_S → K̄_v`) and an additive
`jB : B(K̄_v) → L` (points of the local twist `B = E^{(h)}`), such that
1. `ψ ∘ ι` is injective on the genuine coefficient module `M`;
2. every `m`-torsion element of `L` comes from `M` through `ψ ∘ ι`;
3. `ψ` is equivariant for the twisted action `R ∘ φ` (`φ = p_v` the localization);
4. `jB` is Galois-equivariant;
5. on `B(K̄_v)[m]`, `ψ ∘ ι ∘ ι_v = jB` (`ι_v` the Kummer coefficient map of the local
   condition). -/
def LocalTwistIdentification : Prop :=
  Function.Injective (fun x : M => ψ (ι x)) ∧
    (∀ x : L, m • x = 0 → ∃ m₀ : M, ψ (ι m₀) = x) ∧
    (∀ (σ : Field.absoluteGaloisGroup F) (x : D), ψ (R H ρ θ (φ σ) x) = σ • ψ x) ∧
    (∀ (σ : Field.absoluteGaloisGroup F) (p : PtAlg F B), jB (σ • p) = σ • jB p) ∧
    (∀ t : TorsAlg F B m, ψ (ι (ιv t)) = jB (t : PtAlg F B))

variable [Fintype (G ⧸ H)] (r : G ⧸ H → G) (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ)

include hr in
/-- **The local identity at an old place, pointwise** (PROVED; tex 3251–3270). Under the
identification and the realization `ψ(∑_δ R(r_δ) y) = ∑_j a_j • jB(P_j)` of the weighted sum by
local rational points `P_j ∈ B(K_v)`, every genuine cochain `z` with `ι ∘ z = 𝒯_θ(κ(Q))` satisfies,
for one `m₀ ∈ M` and every `σ ∈ G_{K_v}`,
`z(φ σ) = ∑_j a_j • ι_v(κ_{P_j}(σ)) + (φ σ • m₀ − m₀)`. -/
theorem local_kummer_identity (hT : LocalTwistIdentification ρ H θ ι B m φ ιv ψ jB)
    [SMulCommClass (Field.absoluteGaloisGroup F) k L]
    (hιeq : ∀ (g : G) (x : M), ι (g • x) = R H ρ θ g (ι x))
    {Q y : D} (hQ : (m : ℤ) • Q = y) {J : Type*} (s : Finset J) (a : J → k)
    (P : J → B.toAffine.Point)
    (hreal : ψ (wsum ρ H r θ y) = ∑ j ∈ s, a j • jB (basePt F B (P j)))
    (z : (Fin 1 → G) → M)
    (hz : ∀ g : Fin 1 → G, ι (z g) = T H r hr ρ θ 1 (kummerCochain ρ H Q) g) :
    ∃ m₀ : M, ∀ σ : Field.absoluteGaloisGroup F,
      z (fun _ => φ σ) = ∑ j ∈ s, a j • ιv (kummerFun F B m (P j) σ) + (φ σ • m₀ - m₀) := by
  obtain ⟨hinj, htors, hψ, hjB, hcomp⟩ := hT
  obtain ⟨hk, hTk⟩ := kummer_weighted_sum H r hr ρ θ (m : ℤ) y Q hQ
  set Pt := ∑ δ : G ⧸ H, R H ρ θ (r δ) Q with hPt
  set X : L := ∑ j ∈ s, a j • jB (divPt F B m (P j)) with hX
  have hmX : m • X = ψ (wsum ρ H r θ y) := by
    rw [hreal, hX, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm, ← map_nsmul, nsmul_divPt]
  have hmτ : m • (ψ Pt - X) = 0 := by
    rw [smul_sub, hmX, ← map_nsmul, ← natCast_zsmul, hk]
    exact sub_self _
  obtain ⟨m₀, hm₀⟩ := htors _ hmτ
  refine ⟨m₀, fun σ => hinj ?_⟩
  have e : kummerCochain ρ H Q = fun x => ρ (x 0 : G) Q - Q := rfl
  change ψ (ι (z fun _ => φ σ)) = ψ (ι (∑ j ∈ s, a j • ιv (kummerFun F B m (P j) σ) +
    (φ σ • m₀ - m₀)))
  rw [hz, e, hTk]
  have hsum : ψ (ι (∑ j ∈ s, a j • ιv (kummerFun F B m (P j) σ))) = σ • X - X := by
    rw [map_sum, map_sum, hX, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smul, hcomp, coe_kummerFun, map_sub, hjB, smul_sub, smul_comm σ (a j)]
  have h1 : ψ (R H ρ θ (φ σ) Pt - Pt) = σ • ψ Pt - ψ Pt := by rw [map_sub, hψ]
  have h2 : ψ (ι (φ σ • m₀ - m₀)) = σ • (ψ Pt - X) - (ψ Pt - X) := by
    rw [map_sub, hιeq, map_sub, hψ, hm₀]
  rw [h1, map_add, map_add, hsum, h2]
  simp only [smul_sub]
  abel

end Pointwise

/-! ### The localization lies in the local Kummer condition -/

section Genuine

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  {D : Type} [AddCommGroup D] [Module k D] (ρ : GKS K S →* Module.End k D)
  (H : Subgroup (GKS K S)) [H.Normal] [Fintype (GKS K S ⧸ H)]
  (r : GKS K S ⧸ H → GKS K S) (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ H) = δ)
  (θ : GKS K S ⧸ H →* kˣ)

/-- The identity of `M`, read from the restricted module. Kind: definition. -/
def ofResModAdd {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    (φ : H →ₜ* G) (M : Type) [AddCommGroup M] : ResMod φ M →+ M :=
  AddMonoidHom.id M

/-- Evaluation of a `1`-cochain at a point, as a linear map. Kind: definition. -/
def cfunEval {G : Type} [Group G] [TopologicalSpace G] {N : Type} [AddCommGroup N] [Module k N]
    [DistribMulAction G N] [SMulCommClass G k N] [TopologicalSpace N] [ContinuousAdd N]
    [ContinuousConstSMul k N] (g : Fin 1 → G) : contCochain k G N 1 →ₗ[k] N where
  toFun c := cfun c g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The evaluation map evaluates. Kind: PROVED. -/
theorem cfunEval_apply {G : Type} [Group G] [TopologicalSpace G] {N : Type} [AddCommGroup N]
    [Module k N] [DistribMulAction G N] [SMulCommClass G k N] [TopologicalSpace N] [ContinuousAdd N]
    [ContinuousConstSMul k N] (g : Fin 1 → G) (c : contCochain k G N 1) :
    cfunEval (k := k) g c = cfun c g :=
  rfl

set_option linter.unusedSectionVars false

open scoped Classical in
include hr in
/-- **The localization at an old place lies in the local Kummer condition** (PROVED; tex
3251–3270). For a genuine global cochain `a` whose `ι`-image is the transferred Kummer cocycle
`𝒯_θ(κ(Q))`, under `LocalTwistIdentification` and the realization of the weighted sum by local
points at `v`, the localization `res_v a` lies in the image of the local Kummer condition
`kummerConditionIn k ι_v` in degree one. -/
theorem res_mem_kummer_at (v : HeightOneSpectrum (𝓞 K)) (B : WeierstrassCurve (v.adicCompletion K))
    [B.IsElliptic] (m : ℕ) [NeZero m]
    (ιv : TorsAlg (v.adicCompletion K) B m →+ ResMod (locMap K S v) M)
    (hιv : ∀ (σ : Gloc K v) (t : TorsAlg (v.adicCompletion K) B m), ιv (σ • t) = σ • ιv t)
    {L : Type} [AddCommGroup L] [Module k L] [DistribMulAction (Gloc K v) L]
    [SMulCommClass (Gloc K v) k L] (ψ : D →ₗ[k] L) (jB : PtAlg (v.adicCompletion K) B →+ L)
    (ι : M →ₗ[k] D) (hιeq : ∀ (g : GKS K S) (x : M), ι (g • x) = R H ρ θ g (ι x))
    (hT : LocalTwistIdentification ρ H θ ι B m (locMap K S v : Gloc K v →* GKS K S)
      ((ofResModAdd (locMap K S v) M).comp ιv) ψ jB)
    {Q y : D} (hQ : (m : ℤ) • Q = y) {J : Type} (s : Finset J) (a : J → k)
    (P : J → B.toAffine.Point)
    (hreal : ψ (wsum ρ H r θ y) = ∑ j ∈ s, a j • jB (basePt (v.adicCompletion K) B (P j)))
    (aT : (globalCx k (GKS K S) M).X 1)
    (hz : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := k) (M := M) aT g) = T H r hr ρ θ 1 (kummerCochain ρ H Q) g) :
    ∃ u : (kummerConditionIn k ιv hιv).X 1, (kummerConditionInι k ιv hιv).f 1 1 rfl u =
      (natHom (resCochains (k := k) (M := M) (locMap K S v))).f 1 1 rfl aT := by
  obtain ⟨m₀, hm₀⟩ := local_kummer_identity ρ H θ ι B m (locMap K S v : Gloc K v →* GKS K S)
    ((ofResModAdd (locMap K S v) M).comp ιv) ψ jB r hr hT hιeq hQ s a P hreal
    (gval (A := k) (M := M) aT) hz
  refine mem_kummer_of_eq_sum_add_d0 ιv hιv _ s a P (constCochain (show ResMod _ M from m₀)) ?_
  apply Subtype.ext
  funext g
  have hg : (fun i : Fin 1 => locMap K S v (g i)) = fun _ => locMap K S v (g 0) := by
    funext i
    rw [Fin.fin_one_eq_zero i]
  change cfunEval (k := k) g (show contCochain k (Gloc K v) (ResMod (locMap K S v) M) 1 from
      (natHom (resCochains (k := k) (M := M) (locMap K S v))).f 1 1 rfl aT) =
    cfunEval (k := k) g (∑ j ∈ s, kummerCocycleIn ιv (a j) (P j) + contD k (Gloc K v)
      (ResMod (locMap K S v) M) 0 (constCochain (show ResMod _ M from m₀)))
  have lhs : cfunEval (k := k) g (show contCochain k (Gloc K v) (ResMod (locMap K S v) M) 1 from
      (natHom (resCochains (k := k) (M := M) (locMap K S v))).f 1 1 rfl aT) =
      gval (A := k) (M := M) aT (fun i => locMap K S v (g i)) := rfl
  rw [lhs, map_add, map_sum, hg]
  refine (hm₀ (g 0)).trans (congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ => rfl) ?_)
  exact (cfun_contD_constCochain (k := k) (G := Gloc K v) (M := ResMod (locMap K S v) M)
    (show ResMod _ M from m₀) g).symm

end Genuine

/-! ### The old places of the genuine Selmer data -/

section Old

open NumberField IsDedekindDomain

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k] (M : Type) [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousSMul (GKS K S) M]

open scoped Classical in
/-- **The Kummer conditions at the old places** `v ∈ S₀` (lanes RC28/RC29's `kummerConditionIn`
for a local twist `B_v` and a Kummer coefficient map `ι_v`), as local conditions for RC32's
genuine Selmer data. Kind: definition. -/
def kummerOldConditions (m : ℕ) [NeZero m]
    (B : ∀ v : Places K S₀, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
    (ιv : ∀ v : Places K S₀, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M)
    (hιv : ∀ (v : Places K S₀) (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ιv v (σ • t) = σ • ιv v t) :
    LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1) (fun v => locMap K S v.1) M where
  U v := kummerConditionIn k (ιv v) (hιv v)
  i v := kummerConditionInι k (ιv v) (hιv v)

variable {K S₀ S k M} {D : Type} [AddCommGroup D] [Module k D] (ρ : GKS K S →* Module.End k D)
  (H : Subgroup (GKS K S)) [H.Normal] [Fintype (GKS K S ⧸ H)]
  (r : GKS K S ⧸ H → GKS K S) (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ H) = δ)
  (θ : GKS K S ⧸ H →* kˣ)

open scoped Classical in
/-- **The input at one old place** (Prop): a local ambient module with a coefficient/twist
identification (`LocalTwistIdentification`, GLUE) and a realization of the weighted sum
`∑_δ R(r_δ) y` by local rational points of the twist. Kind: definition (Prop). -/
def OldPlaceInput (v : HeightOneSpectrum (𝓞 K)) (B : WeierstrassCurve (v.adicCompletion K))
    [B.IsElliptic] (m : ℕ) [NeZero m]
    (ιv : TorsAlg (v.adicCompletion K) B m →+ ResMod (locMap K S v) M) (ι : M →ₗ[k] D) (y : D) :
    Prop :=
  ∃ (L : Type) (_ : AddCommGroup L) (_ : Module k L) (_ : DistribMulAction (Gloc K v) L)
    (_ : SMulCommClass (Gloc K v) k L) (ψ : D →ₗ[k] L) (jB : PtAlg (v.adicCompletion K) B →+ L),
    LocalTwistIdentification ρ H θ ι B m (locMap K S v : Gloc K v →* GKS K S)
      ((ofResModAdd (locMap K S v) M).comp ιv) ψ jB ∧
    ∃ (J : Type) (s : Finset J) (a : J → k) (P : J → B.toAffine.Point),
      ψ (wsum ρ H r θ y) = ∑ j ∈ s, a j • jB (basePt (v.adicCompletion K) B (P j))

set_option linter.unusedSectionVars false

open scoped Classical in
include hr in
/-- **The old-place strict lift from the local inputs** (PROVED): with the Kummer conditions at
the old places, if every old place satisfies `OldPlaceInput` for the weighted sum of `y`, a genuine
cochain `a` with `ι ∘ a = 𝒯_θ(κ(Q))` (`k Q = y`) lifts through the old conditions:
`∃ u, ι u = res a` in the genuine Selmer data. -/
theorem exists_oldLift_of_inputs (m : ℕ) [NeZero m]
    (B : ∀ v : Places K S₀, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
    (ιv : ∀ v : Places K S₀, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M)
    (hιv : ∀ (v : Places K S₀) (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ιv v (σ • t) = σ • ιv v t)
    (ι : M →ₗ[k] D) (hιeq : ∀ (g : GKS K S) (x : M), ι (g • x) = R H ρ θ g (ι x))
    {Q y : D} (hQ : (m : ℤ) • Q = y)
    (hin : ∀ v : Places K S₀, OldPlaceInput ρ H r θ v.1 (B v) m (ιv v) ι y)
    (aT : (globalCx k (GKS K S) M).X 1)
    (hz : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := k) (M := M) aT g) = T H r hr ρ θ 1 (kummerCochain ρ H Q) g) :
    ∃ u : (selData k (GKS K S) (fun v : Places K S₀ => Gloc K v.1) (fun v => locMap K S v.1) M
        (kummerOldConditions K S₀ S k M m B ιv hιv)).U.X 1,
      (selData k (GKS K S) (fun v : Places K S₀ => Gloc K v.1) (fun v => locMap K S v.1) M
        (kummerOldConditions K S₀ S k M m B ιv hιv)).ι.f 1 1 rfl u =
      (selData k (GKS K S) (fun v : Places K S₀ => Gloc K v.1) (fun v => locMap K S v.1) M
        (kummerOldConditions K S₀ S k M m B ιv hιv)).res.f 1 1 rfl aT := by
  refine exists_lift_selData _ aT fun v => ?_
  obtain ⟨L, _, _, _, _, ψ, jB, hT, J, s, a, P, hreal⟩ := hin v
  exact res_mem_kummer_at ρ H r hr θ v.1 (B v) m (ιv v) (hιv v) ψ jB ι hιeq hT hQ s a P hreal aT hz

end Old

/-! ### `hRloc` at the genuine relaxed data -/

section Relaxed

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [Field k] [TopologicalSpace k] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  {D : Type} [AddCommGroup D] [Module k D] (ρ : GKS K S →* Module.End k D)
  (H : Subgroup (GKS K S)) [H.Normal] [Fintype (GKS K S ⧸ H)]
  (r : GKS K S ⧸ H → GKS K S) (hr : ∀ δ, ((r δ : GKS K S) : GKS K S ⧸ H) = δ)
  (θ : GKS K S ⧸ H →* kˣ)

set_option linter.unusedSectionVars false

open scoped Classical in
include hr in
/-- **`hRloc` of `hzR_genuine_of_strictLifts` from the old-place inputs** (PROVED): at RC32's
genuine relaxed data with the Kummer conditions at the old places, the relaxed strict-lift
hypothesis holds as soon as every old place satisfies `OldPlaceInput`. -/
theorem exists_hRloc_of_oldInputs (m : ℕ) [NeZero m]
    (B : ∀ v : Places K S₀, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
    (ιv : ∀ v : Places K S₀, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M)
    (hιv : ∀ (v : Places K S₀) (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ιv v (σ • t) = σ • ιv v t) (w : Places K S)
    (ι : M →ₗ[k] D) (hιeq : ∀ (g : GKS K S) (x : M), ι (g • x) = R H ρ θ g (ι x))
    {Q y : D} (hQ : (m : ℤ) • Q = y)
    (hin : ∀ v : Places K S₀, OldPlaceInput ρ H r θ v.1 (B v) m (ιv v) ι y)
    (aT : (globalCx k (GKS K S) M).X 1)
    (hz : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := k) (M := M) aT g) = T H r hr ρ θ 1 (kummerCochain ρ H Q) g) :
    ∃ uR : (genuineRelaxed K S₀ S k M (kummerOldConditions K S₀ S k M m B ιv hιv) w).U.X 1,
      (genuineRelaxed K S₀ S k M (kummerOldConditions K S₀ S k M m B ιv hιv) w).ι.f 1 1 rfl uR =
        (genuineRelaxed K S₀ S k M (kummerOldConditions K S₀ S k M m B ιv hιv) w).res.f 1 1 rfl
          aT :=
  exists_lift_relaxedAt (genuineOld K S₀ S k M (kummerOldConditions K S₀ S k M m B ιv hιv))
    (genuineRes K S k M w) aT
    (exists_oldLift_of_inputs ρ H r hr θ m B ιv hιv ι hιeq hQ hin aT hz)

end Relaxed

/-! ### Non-vacuity -/

/-- **Non-vacuity of `LocalTwistIdentification`'s shape**: its five clauses hold for the zero
maps into the zero module `L = PUnit` when `M` is trivial (here `M = PUnit`), for any local data.
Kind: PROVED. -/
theorem nonVacuity_localTwist {G : Type} [Group G] {k : Type} [CommRing k] {D : Type}
    [AddCommGroup D] [Module k D] (ρ : G →* Module.End k D) (H : Subgroup G) [H.Normal]
    (θ : G ⧸ H →* kˣ) (ι : PUnit →ₗ[k] D) {F : Type} [Field F] [CharZero F] [DecidableEq F]
    (B : WeierstrassCurve F) [B.IsElliptic] (m : ℕ) [NeZero m]
    (φ : Field.absoluteGaloisGroup F →* G) (ιv : TorsAlg F B m →+ PUnit) :
    LocalTwistIdentification ρ H θ ι B m φ ιv (0 : D →ₗ[k] PUnit) (0 : PtAlg F B →+ PUnit) :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩,
    fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _,
    fun _ => Subsingleton.elim _ _⟩

open NumberField IsDedekindDomain in
open scoped Classical in
/-- **Non-vacuity of `OldPlaceInput`** (all of its hypotheses at once): for the trivial genuine
coefficient module `M = PUnit`, the zero maps into `L = PUnit` and the empty realization.
Kind: PROVED. -/
theorem nonVacuity_oldPlaceInput {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type} [CommRing k] {D : Type} [AddCommGroup D]
    [Module k D] (ρ : GKS K S →* Module.End k D) (H : Subgroup (GKS K S)) [H.Normal]
    [Fintype (GKS K S ⧸ H)] (r : GKS K S ⧸ H → GKS K S) (θ : GKS K S ⧸ H →* kˣ)
    (v : HeightOneSpectrum (𝓞 K)) (B : WeierstrassCurve (v.adicCompletion K)) [B.IsElliptic]
    (m : ℕ) [NeZero m] (ιv : TorsAlg (v.adicCompletion K) B m →+ ResMod (locMap K S v) PUnit)
    (y : D) :
    OldPlaceInput (M := PUnit) ρ H r θ v B m ιv 0 y :=
  ⟨PUnit, inferInstance, inferInstance, inferInstance, inferInstance, 0, 0,
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩,
      fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _,
      fun _ => Subsingleton.elim _ _⟩,
    Empty, ∅, fun e => e.elim, fun e => e.elim, Subsingleton.elim _ _⟩

/-- **A non-degenerate witness of `LocalTwistIdentification`** (Kind: PROVED): for every local
twist `B` and every `m`, the identification holds with coefficient ring `ℤ`, genuine coefficient
module `M = B(K̄)[m]` (nonzero for `m ≥ 2`), `ι_v = id` (injective), `D = L = B(K̄)` with the Galois
action, `ψ = jB = id`, trivial `H = ⊤` and trivial character. -/
theorem nonVacuity_localTwist_identity {F : Type} [Field F] [CharZero F] [DecidableEq F]
    (B : WeierstrassCurve F) [B.IsElliptic] (m : ℕ) [NeZero m] :
    LocalTwistIdentification (DistribMulAction.toModuleEnd ℤ (PtAlg F B))
      (⊤ : Subgroup (Field.absoluteGaloisGroup F)) 1
      ((AddSubgroup.torsionBy (PtAlg F B) (m : ℤ)).subtype.toIntLinearMap) B m (MonoidHom.id _)
      (AddMonoidHom.id (TorsAlg F B m)) (LinearMap.id : PtAlg F B →ₗ[ℤ] PtAlg F B)
      (AddMonoidHom.id (PtAlg F B)) :=
  ⟨fun x y h => Subtype.ext h,
    fun x hx => ⟨⟨x, (AddSubgroup.torsionBy.nsmul_iff).2 hx⟩, rfl⟩,
    fun σ x => by simp [R],
    fun σ p => rfl,
    fun t => rfl⟩

end ZInQ.Contrib.CloudB3E2.NormCochain

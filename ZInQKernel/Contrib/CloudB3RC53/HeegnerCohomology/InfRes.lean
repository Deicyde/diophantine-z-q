import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.Transgression
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Coefficients
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Interfaces

/-!
# HeegnerCohomology, part 1: the five-term sequence (H8) and the descent `d_a` (H9)

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-finite-heegner`, paragraph 4
"Descend once, before twisting", tex 3004–3032.

Elliot (tex 3006–3017) applies the five-term sequence for finite discrete coefficients
[Nekovář, *Selmer complexes*, formula (4.1.4.1), p. 96]

`0 → H¹(Γ, V_a^{G_M}) → H¹(B, V_a) → H¹(M, V_a)^Γ → H²(Γ, V_a^{G_M})`              (H8)

with `B = H_f`, `M = M_I`, `Γ = Gal(M/B) = G_B / G_M`, `V_a = E[2^a]`, and then uses that
multiplication by `2^e` is zero on `V_a^{G_M}` by (H2), "hence on every cochain and cohomology
group of `Γ` with those coefficients" (tex 3014–3016).

The RC10 lane records this input as the interface `InfResInput` (file
`ZInQKernel/Contrib/OneProof/RC/HeegnerAlgebra/Interfaces.lean`, with `FiveTerm` from
`.../HeegnerAlgebra/Descent.lean`).  This file discharges
that interface over the genuine continuous cohomology of a profinite group with discrete
coefficients (the explicit low-degree model of Tau Ceti: `H1`, `H2`, `explicitInfl1`,
`explicitResConj1`, `transgression`), for every closed normal subgroup:

* `fiveTermGenuine`: the five-term sequence (H8), exact at its first three nodes.  This is the
  sequence Elliot cites; it is proved here (from the Tau Ceti development), so the citation of
  Nekovář (4.1.4.1) is not needed as a printed leaf.  Status `PROVED`.
* `infResInputGenuine`: the interface `InfResInput` of RC10, with the two `2^e`-vanishing fields
  derived from the single hypothesis that `2^e` kills the `N`-invariants of the coefficients
  ((H2) for `V_a^{G_M} = E(M)[2^a]`).  Status `PROVED` (from (H2), which is RC10's
  `H2_assembled`).

The constructions produce RC10's own structures `ZInQ.Manuscript.RC.HeegnerAlgebra.FiveTerm`
and `ZInQ.Manuscript.RC.HeegnerAlgebra.InfResInput`.
-/

namespace ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

open TauCeti.ContCohomology
open ZInQ.Manuscript.RC.HeegnerAlgebra (FiveTerm InfResInput)

/-! ## The genuine five-term sequence -/

universe u v

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
  (N : Subgroup G) [N.Normal]

/-- **(H8)**, tex 3006–3012, `PROVED`: for a profinite group `G` (here `G_B`, `B = H_f`), a closed
normal subgroup `N` (here `G_M`, `M = M_I`; `G/N = Γ = Gal(M_I/H_f)`) and a discrete `G`-module
`M` (here `V_a = E[2^a]`), the inflation–restriction–transgression sequence
`0 → H¹(G/N, M^N) → H¹(G, M) → H¹(N, M)^{G/N} → H²(G/N, M^N)` in continuous cohomology, exact at
`H¹(G/N, M^N)`, `H¹(G, M)` and `H¹(N, M)^{G/N}`. -/
noncomputable def fiveTermGenuine (hN : IsClosed (N : Set G)) :
    FiveTerm (H1 (G ⧸ N) (FixedPoints.addSubgroup N M)) (H1 G M) (H1ConjInvariants G M N)
      (H2 (G ⧸ N) (FixedPoints.addSubgroup N M)) where
  inf := explicitInfl1 G M N
  res := explicitResConj1 G M N
  tg := transgression G M N hN
  inf_injective := explicitInfl1_injective G M N
  exact_B b := by
    rw [← AddMonoidHom.mem_ker, ← explicitInfResConj_exact]
    rfl
  exact_C c := by
    rw [← AddMonoidHom.mem_ker, ← fiveTerm_exact_H1N G M N hN]
    rfl

/-- `n` kills a continuous `H¹` once it kills the coefficients (integer form). -/
theorem zsmul_H1_eq_zero {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {V : Type*} [AddCommGroup V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [DistribMulAction Γ V] [ContinuousSMul Γ V]
    (e : ℕ) (h : ∀ m : V, ((2 : ℤ) ^ e) • m = 0) (x : H1 Γ V) : ((2 : ℤ) ^ e) • x = 0 := by
  have h' : ∀ m : V, (2 ^ e : ℕ) • m = 0 := fun m => by
    rw [← natCast_zsmul]; push_cast; exact h m
  rw [show ((2 : ℤ) ^ e) = ((2 ^ e : ℕ) : ℤ) by push_cast; rfl, natCast_zsmul]
  exact nsmul_H1_eq_zero h' x

/-- `n` kills a continuous `H²` once it kills the coefficients (integer form). -/
theorem zsmul_H2_eq_zero {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ]
    {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [DistribMulAction Γ V] [ContinuousSMul Γ V]
    (e : ℕ) (h : ∀ m : V, ((2 : ℤ) ^ e) • m = 0) (x : H2 Γ V) : ((2 : ℤ) ^ e) • x = 0 := by
  have h' : ∀ m : V, (2 ^ e : ℕ) • m = 0 := fun m => by
    rw [← natCast_zsmul]; push_cast; exact h m
  rw [show ((2 : ℤ) ^ e) = ((2 ^ e : ℕ) : ℤ) by push_cast; rfl, natCast_zsmul]
  exact nsmul_H2_eq_zero h' x

/-- **(H8) with the (H2) vanishing**, tex 3004–3017, `PROVED`: the RC10 interface `InfResInput`
for the genuine continuous cohomology.  The single hypothesis `hH2` says that `2^e` kills every
`N`-fixed element of the coefficients: for `N = G_M`, `M = M_I` and coefficients `V_a = E[2^a]`
this is `2^e E(M_I)[2^a] = 0`, a consequence of (H2) (`2^e E(H_d)[2^∞] = 0`, also for composita of
ring-class fields, tex 2893–2897; RC10's `H2_assembled`).  The vanishing on `H¹(Γ, V^{G_M})` and
`H²(Γ, V^{G_M})` follows, as Elliot says, "on every cochain and cohomology group of `Γ`". -/
noncomputable def infResInputGenuine (hN : IsClosed (N : Set G)) (e : ℕ)
    (hH2 : ∀ m : M, (∀ n : N, n • m = m) → ((2 : ℤ) ^ e) • m = 0) :
    InfResInput (H1 (G ⧸ N) (FixedPoints.addSubgroup N M)) (H1 G M) (H1ConjInvariants G M N)
      (H2 (G ⧸ N) (FixedPoints.addSubgroup N M)) e where
  seq := fiveTermGenuine G M N hN
  killA := zsmul_H1_eq_zero e (fun m => Subtype.ext (by
    simpa using hH2 m (fun n => m.2 n)))
  killD := zsmul_H2_eq_zero e (fun m => Subtype.ext (by
    simpa using hH2 m (fun n => m.2 n)))

/-! ## The Galois instance: `G = G_B`, coefficients `V_a = E[2^a]` -/

section Galois

set_option synthInstance.maxHeartbeats 400000

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K)

/-- **(H8)–(H9) for `V_a = E[2^a]`**, tex 3004–3017, `PROVED` from (H2): for the absolute Galois
group `G_B` of a field `B` (here `B = H_f`), a closed normal subgroup `N` (here `G_{M_I}`) and the
Galois module `V_a = E(B^sep)[2^a]` of an elliptic curve `E/B` (Tau Ceti's `TorsionCoeff`), the RC10
interface `InfResInput` holds as soon as `2^e` kills `V_a^N = E(M_I)[2^a]`, which is (H2). -/
noncomputable def infResInputTorsion (a : ℕ) (N : Subgroup (TauCeti.AbsoluteGaloisGroup K)) [N.Normal]
    (hN : IsClosed (N : Set (TauCeti.AbsoluteGaloisGroup K))) (e : ℕ)
    (hH2 : ∀ P : W.TorsionCoeff (2 ^ a), (∀ σ : N, σ • P = P) → ((2 : ℤ) ^ e) • P = 0) :
    InfResInput (H1 (TauCeti.AbsoluteGaloisGroup K ⧸ N) (FixedPoints.addSubgroup N (W.TorsionCoeff (2 ^ a))))
      (H1 (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)))
      (H1ConjInvariants (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) N)
      (H2 (TauCeti.AbsoluteGaloisGroup K ⧸ N) (FixedPoints.addSubgroup N (W.TorsionCoeff (2 ^ a)))) e :=
  infResInputGenuine (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) N hN e hH2

/-! ## The node -/

/-- **Node (H8)–(H9)**, tex 3004–3024 (ex:arith-finite-heegner, paragraph 4), `PROVED`.  For every
field `B` (with decidable equality), elliptic curve `E/B` given by a Weierstrass model, exponents
`a, e`, and closed normal subgroup `N ≤ G_B` such that `2^e` kills the `N`-fixed part of
`E(B^sep)[2^a]` ((H2)), and for every class `c ∈ H¹(N, E[2^a])^{G_B/N}`:

* (H8) inflation is injective, `ker(res) = im(inf)`, `ker(tg) = im(res)`;
* (H9) `2^e c = res(b)` for some `b ∈ H¹(G_B, E[2^a])` (tex 3017–3019), and `2^e b` does not
  depend on the choice of `b` (tex 3021–3022); its restriction is `2^{2e} c` (tex 3024). -/
def H8H9Node : Prop :=
  ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (a e : ℕ)
    (N : Subgroup (TauCeti.AbsoluteGaloisGroup K)) [N.Normal]
    (_hN : IsClosed (N : Set (TauCeti.AbsoluteGaloisGroup K)))
    (_hH2 : ∀ P : W.TorsionCoeff (2 ^ a), (∀ σ : N, σ • P = P) → ((2 : ℤ) ^ e) • P = 0),
    Function.Injective (explicitInfl1 (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) N) ∧
    (explicitInfl1 (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) N).range =
      (explicitResConj1 (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) N).ker ∧
    ∀ c : H1ConjInvariants (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) N,
      (∃ b, explicitResConj1 (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) N b =
        ((2 : ℤ) ^ e) • c) ∧
      ∀ b b', explicitResConj1 (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) N b =
          ((2 : ℤ) ^ e) • c →
        explicitResConj1 (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) N b' =
          ((2 : ℤ) ^ e) • c →
        ((2 : ℤ) ^ e) • b = ((2 : ℤ) ^ e) • b' ∧
        explicitResConj1 (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) N (((2 : ℤ) ^ e) • b) =
          ((2 : ℤ) ^ (2 * e)) • c

theorem h8H9Node_proof : H8H9Node := by
  intro K _ _ W a e N _ hN hH2
  let I := infResInputTorsion W a N hN e hH2
  have hB := I.seq.exact_B
  have hC := I.seq.exact_C
  have kA := I.killA
  have kD := I.killD
  change ∀ b, explicitResConj1 _ (W.TorsionCoeff (2 ^ a)) N b = 0 ↔
    ∃ x, explicitInfl1 _ (W.TorsionCoeff (2 ^ a)) N x = b at hB
  change ∀ c, transgression _ (W.TorsionCoeff (2 ^ a)) N hN c = 0 ↔
    ∃ b, explicitResConj1 _ (W.TorsionCoeff (2 ^ a)) N b = c at hC
  refine ⟨explicitInfl1_injective _ _ _, explicitInfResConj_exact _ _ _,
    fun c => ⟨?_, fun b b' hb hb' => ⟨?_, ?_⟩⟩⟩
  · rw [← hC, map_zsmul]; exact kD _
  · have h0 : explicitResConj1 _ _ N (b - b') = 0 := by
      rw [map_sub, hb, hb', sub_self]
    obtain ⟨x, hx⟩ := (hB _).mp h0
    have : ((2 : ℤ) ^ e) • (b - b') = 0 := by
      rw [← hx, ← map_zsmul, kA, map_zero]
    rwa [zsmul_sub, sub_eq_zero] at this
  · rw [map_zsmul, hb, smul_smul, ← pow_add, two_mul]

end Galois

end ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionTame

/-!
# An auxiliary one-place-per-prime variant of the full-condition identification

**Not the text's family identification.** In the text each prime `q` of the family splits in `K`
and contributes the TWO conjugate graph places over it (tex 5247: "the two-place local
determinant"; tex 5456–5457: "`A_q` is the direct sum of the two rank-two singular differentials at
the conjugate graph places"). The structure below instead identifies the new places with `F.Q`
bijectively, i.e. it allows exactly ONE new place over each prime; any instance with two new
places over the same `q` is excluded. The text-faithful two-place structure is the integration
team's `Identification3Q2` (`RC/Wiring/ClearingFull.lean`); this file is an auxiliary variant.

`Identification3Q K S S' hS F dK hK cE tK` extends `Identification3` (unchanged) by:

* `eQ : NewPlaces K S S' ≃ F.Q` — one new place per prime of the family;
* `lies : ∀ v, (eQ v : ℕ) ∈ v` — the new place `v` lies over the prime `eQ v`;
* `hqq : ∀ v, qq v = eQ v` — the residue cardinality of the tame model at `v` is that prime.

Consequences (PROVED, for this variant): `isEmpty_newPlaces_iff` (no new places iff `Q = ∅`),
`card_newPlaces` (`#(S' − S) = #Q` for this one-place variant; in the text's setting, with the
two conjugate places over each split `q`, it is `#(S' − S) = 2 · #Q`), `eNQ` (the singular
summands are indexed by `ι × Q`), and
`tame_singular_quasiIso_Q`: for every `q ∈ Q` the genuine singular quotient at the chosen place
over `q` is quasi-isomorphic to `[M₀ --(Φ − q)--> M₀]` in degrees one and two, with this `q`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)

variable (K : Type) [Field K] [NumberField K] (S S' : Set (HeightOneSpectrum (𝓞 K)))
  (hS : S ⊆ S')

/-- **Auxiliary one-place-per-prime variant** (GLUE, additive over `Identification3`): the new
places are identified bijectively with the family's primes. NOT the text's setting, which has two
conjugate places over each split prime (tex 5247, 5456–5457); see the integration team's
`Identification3Q2` (`RC/Wiring/ClearingFull.lean`) for the text-faithful two-place structure. -/
structure Identification3Q [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
    (F : Family) (dK hK cE tK : ℕ) extends Identification3 K S S' hS F.b dK hK cE tK where
  /-- one new place per prime of the family -/
  eQ : NewPlaces K S S' ≃ F.Q
  /-- the new place `v` lies over the prime `eQ v` -/
  lies : ∀ v : NewPlaces K S S', (((eQ v : ℕ) : ℤ) : 𝓞 K) ∈ v.1.asIdeal
  /-- the residue cardinality of the tame model at `v` is the prime `eQ v` -/
  hqq : ∀ v : NewPlaces K S S', qq v = (eQ v : ℕ)

namespace Identification3Q

variable {K S S' hS} [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')] {F : Family}
  {dK hK cE tK : ℕ} (M : Identification3Q K S S' hS F dK hK cE tK)

include M in
/-- **No new places iff the family has no primes** (`Q = ∅`). -/
theorem isEmpty_newPlaces_iff : IsEmpty (NewPlaces K S S') ↔ F.Q = ∅ := by
  rw [Equiv.isEmpty_congr M.eQ, Finset.isEmpty_coe_sort]

include M in
/-- **The number of new places is the number of primes of the family** (for this one-place
variant; in the text's setting, with two conjugate places over each split prime, it is twice the
number of primes). -/
theorem card_newPlaces : Fintype.card (NewPlaces K S S') = F.Q.card := by
  rw [Fintype.card_congr M.eQ, Fintype.card_coe]

/-- **The singular summands are indexed by `ι × Q`.** -/
def eNQ : M.C.N ≃ M.ιn × F.Q :=
  M.eN.trans (Equiv.prodCongr (Equiv.refl _) M.eQ)

/-- **For every prime `q ∈ Q`, the genuine singular quotient at the new place over `q` is the tame
`[M₀ --(Φ − q)--> M₀]` in degrees one and two**, with the residue cardinality equal to `q`
(PROVED from `tame_singular_quasiIso` and `hqq`). -/
theorem tame_singular_quasiIso_Q (q : F.Q) :
    M.qq (M.eQ.symm q) = (q : ℕ) ∧
      QuasiIso (tameQuotMap (M.tame (M.eQ.symm q))) := by
  refine ⟨?_, M.toIdentification3.tame_singular_quasiIso (M.eQ.symm q)⟩
  rw [M.hqq, Equiv.apply_symm_apply]

end Identification3Q

end ZInQ.Contrib.CloudB3RC53.ClearingComplex


/-! ## g12-det: `G12Weight` (the Hodge–Tate comparison), reduced to named pieces

`G12Weight` is copied verbatim from scratch/g0-mod-galois/part_galois.lean. Its conclusion
`∃ n, {n, n + 1 − k} = {0, −1}` says, for `k ≥ 1`, exactly `k = 2` (`n = 0`).
Reduction: `g12Weight_of : TwistExists → TwistConj → HTConj → SenTwist → FiniteImageHT →
G12Weight`, where `TwistExists`, `TwistConj`, `HTConj` are GLUE and `SenTwist`, `FiniteImageHT`
are LEAVES (Sen 1980; Tate 1967 with Ax–Sen–Tate). -/

section G12DetWeightSec

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

/-- (copied verbatim from part_galois.lean) -/
instance fact_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- **G12, the weight comparison (GLUE, unproved; h-trust C8 "Content", rv-h-c8).** From R14
(eigenform representations), R13 (their Hodge–Tate weights `{0, 1 − k}` for `k ≥ 2`, every
level), R15 (Deligne–Serre for `k = 1`), T18 (Chebotarev) and T19 (Brauer–Nesbitt): if an
irreducible `r : G_ℚ → GL₂(ℚ̄₅)` with weights `{0, −1}` at 5 is attached to a normalized eigenform
`g` of weight `k ≥ 1` up to a continuous twist `ψ` outside a finite set, then the weights of `r`
are `{n, n + 1 − k}` for an integer `n`. Argument: `r ≅ ρ_g ⊗ ψ` (traces agree on a dense set,
both semisimple); the Sen weights of `ρ_g ⊗ ψ` are `{0, 1−k} + s` (`s` the Sen weight of `ψ`,
a priori not an integer); equality with `{0, −1}` forces `s = 0`, `k = 2` for `k ≥ 2`
(model review: `ψ` itself need not be Hodge–Tate a priori, so the argument goes through Sen
weights); for `k = 1`, `ρ_g` has finite image, hence weights `{0, 0}`, so
`r` would have equal weights, contradicting `{0, −1}` (so the hypotheses are inconsistent). -/
def G12Weight : Prop :=
  HSyn.EigenformRepExists → PkgI4.EigenformHT → HSyn.DeligneSerreConseq → HSyn.FrobeniusDense →
  HSyn.BrauerNesbitt →
  ∀ (r : GaloisRep 5 2) (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N k)
    (ψ : GaloisChar 5) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (S : Finset ℕ),
    0 < N → 1 ≤ k → PkgI4.IsNormalizedEigenform g χ → r.IsIrreducible →
    r.HasHTWeightsAtSelf 5 {0, -1} → r.AttachedUpToTwist ψ ιC ιL g S →
    ∃ n : ℤ, ({n, n + 1 - k} : Multiset ℤ) = {0, -1}

/-! ### Named pieces -/

/-- `ρ'` is the twist `ψ ⊗ ρ`: `ρ'(σ) = ψ(σ) ρ(σ)`. -/
def IsTwist {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (ρ' : GaloisRep ℓ n) (ψ : GaloisChar ℓ)
    (ρ : GaloisRep ℓ n) : Prop :=
  ∀ σ, ρ'.mat σ = (ψ.toHom σ : PadicAlgCl ℓ) • ρ.mat σ

/-- `r` and `ρ'` are conjugate by a fixed matrix: `r(σ) = P ρ'(σ) P⁻¹`. -/
def IsConj {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (r ρ' : GaloisRep ℓ n) : Prop :=
  ∃ P : GL (Fin n) (PadicAlgCl ℓ), ∀ σ, r.toHom σ = P * ρ'.toHom σ * P⁻¹

/-- **The twist exists (GLUE, elementary).** `σ ↦ ψ(σ) ρ(σ)` is a continuous representation:
a homomorphism because scalars are central, continuous because `GL_n(ℚ̄_ℓ)` carries the topology
induced from `M_n × M_nᵐᵒᵖ` and `ψ`, `ψ⁻¹`, `ρ`, `ρ⁻¹` are continuous. -/
def TwistExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (ρ : GaloisRep ℓ n) (ψ : GaloisChar ℓ),
    ∃ ρ' : GaloisRep ℓ n, IsTwist ρ' ψ ρ

/-- **`r ≅ ψ ⊗ ρ_g` (GLUE, from T18 Chebotarev and T19 Brauer–Nesbitt).** If `r` is
irreducible, `ρ` semisimple and attached to `g`, `r` attached to `g` up to the twist `ψ` outside
`S`, and `ρ' = ψ ⊗ ρ`, then `r` and `ρ'` are conjugate. Argument (as in `g12Det_of`,
scratch/g0-mod-galois): `tr r = tr ρ'` at arithmetic Frobenius outside `S ∪ {p ∣ 5N}` (`ιC`
injective identifies the two `α`), hence everywhere (`eq_of_eq_on_arithFrob`, T18); `r` is
semisimple (Burnside-irreducible: an invariant subspace is invariant under `M₂(ℚ̄₅)`), `ρ'` is
semisimple (same invariant subspaces as `ρ`); Brauer–Nesbitt (T19, `G = G_ℚ`, `E = ℚ̄₅`). -/
def TwistConj : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (r ρ ρ' : GaloisRep ℓ 2) (ψ : GaloisChar ℓ)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (N : ℕ) (k : ℤ)
    (g : PkgI4.CF N k) (S : Finset ℕ),
    0 < N → r.IsIrreducible → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    r.AttachedUpToTwist ψ ιC ιL g S → IsTwist ρ' ψ ρ → IsConj r ρ'

/-- **Hodge–Tate weights are invariant under conjugation (GLUE, about the definition
`PkgI4.LocalHasHTWeights`; STANDARD).** Enlarge the finite coefficient field `E` to contain the
entries of `P` and `P⁻¹` and use that `htMult` does not change under a finite extension of `E`
(`(ℂ_p(i) ⊗ V)^G` commutes with `E'/E` base change) nor under an `E'`-linear isomorphism. -/
def HTConj : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (r ρ' : GaloisRep ℓ n) (S : Multiset ℤ),
    IsConj r ρ' → r.HasHTWeightsAtSelf ℓ S → ρ'.HasHTWeightsAtSelf ℓ S

/-- **Sen weights of a twist (LEAF; Sen, *Continuous cohomology and p-adic Galois
representations*, Invent. Math. 62 (1980), §2 Thm 4 and Cor. (Hodge–Tate iff the Sen operator `Θ`
is semisimple with integer eigenvalues, the Hodge–Tate weights), with
`Θ_{ψ⊗V} = Θ_ψ + Θ_V` (Sen 1980 §2; Fontaine–Ouyang, *Theory of p-adic Galois representations*,
§2.4-2.5); numbering UNVERIFIED).** If `ρ` and `ρ' = ψ ⊗ ρ` (restricted to `G_{ℚ_p}`) are both
Hodge–Tate, with weight multisets `S`, `S'` of full size `n`, then `S' = S + s` for an integer
`s`. Consequence of the published theorems: the Sen operators satisfy `Θ_{ρ'} = Θ_ρ + s_ψ`, both
are semisimple with eigenvalue multisets `S`, `S'`, so `S' = S + s_ψ` in `ℂ_p`, and `s_ψ ∈ ℤ`
when `n ≥ 1` (for `n = 0`, `s = 0`). (Full size is needed: `HasHTWeights S` with `card S < n`
holds for non-Hodge–Tate `ρ`, and then the statement fails.) -/
def SenTwist : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ ρ' : GaloisRep p n) (ψ : GaloisChar p)
    (S S' : Multiset ℤ),
    IsTwist ρ' ψ ρ → Multiset.card S = n → Multiset.card S' = n →
    ρ.HasHTWeightsAtSelf p S → ρ'.HasHTWeightsAtSelf p S' →
    ∃ s : ℤ, S' = S.map (· + s)

/-- **Finite image implies Hodge–Tate of weight 0 (LEAF; Tate, *p-divisible groups* (1967) §3
Thm 2 (`ℂ_p(i)^{G_L} = 0` for `i ≠ 0`) and Ax–Sen–Tate (`ℂ_p^{G_L} = L`), with Hilbert 90 for
the finite extension cut out by the image; Fontaine–Ouyang Prop. 2.15 / Sen 1980 Cor. of Thm 11;
numbering UNVERIFIED).** A representation of `G_ℚ` with finite image is Hodge–Tate at `p` with all
weights `0` (its image lies in `GL_n(E)` for a finite `E/ℚ_p`: finitely many algebraic entries).
-/
def FiniteImageHT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GaloisRep p n),
    (Set.range ρ.toHom).Finite → ρ.HasHTWeightsAtSelf p (Multiset.replicate n 0)

/-! ### Proof -/

/-- The conclusion of `G12Weight` is `k = 2` (for `k ≥ 1`). -/
theorem g12Weight_concl_iff (k : ℤ) (hk : 1 ≤ k) :
    (∃ n : ℤ, ({n, n + 1 - k} : Multiset ℤ) = {0, -1}) ↔ k = 2 := by
  constructor
  · rintro ⟨n, hn⟩
    have h0 : (0 : ℤ) ∈ ({n, n + 1 - k} : Multiset ℤ) := by rw [hn]; simp
    have h1 : (-1 : ℤ) ∈ ({n, n + 1 - k} : Multiset ℤ) := by rw [hn]; simp
    have hc : ((n + 1 - k : ℤ) ∈ ({0, -1} : Multiset ℤ)) := by rw [← hn]; simp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h0 h1 hc
    omega
  · rintro rfl
    exact ⟨0, by norm_num⟩

/-- **`G12Weight` from the named pieces** (and the leaves R14, R13, R15 it takes). -/
theorem g12Weight_of (hTE : TwistExists) (hTC : TwistConj) (hHC : HTConj) (hSen : SenTwist)
    (hFI : FiniteImageHT) : G12Weight := by
  intro hR hHT hDS _hFD _hBN r N k χ g ψ ιC ιL S hN hk hg hirr hw hatt
  obtain ⟨ρH, hss, hρatt⟩ := hR 5 ιC ιL N k χ g hN hk hg
  let ρ : GaloisRep 5 2 := ⟨ρH.toHom, ρH.continuous_toHom⟩
  have hss' : ρ.IsSemisimple := hss
  have hatt' : ρ.AttachedTo ιC ιL g := hρatt
  obtain ⟨ρ', htw⟩ := hTE 5 2 ρ ψ
  have hconj : IsConj r ρ' := hTC 5 r ρ ρ' ψ ιC ιL N k g S hN hirr hss' hatt' hatt htw
  have hw' : ρ'.HasHTWeightsAtSelf 5 {0, -1} := hHC 5 2 r ρ' _ hconj hw
  rcases eq_or_lt_of_le hk with h1 | h2
  · -- weight one: `ρ_g` has finite image, so `ψ ⊗ ρ_g` would have equal weights
    exfalso
    subst h1
    have hfin : (Set.range ρH.toHom).Finite := hDS 5 ιC ιL ρH N χ g hN hg hss hρatt
    have h0 : ρ.HasHTWeightsAtSelf 5 (Multiset.replicate 2 0) := hFI 5 2 ρ hfin
    obtain ⟨s, hs⟩ := hSen 5 2 ρ ρ' ψ _ _ htw (by simp) (by simp) h0 hw'
    have ha : (0 : ℤ) ∈ ({0, -1} : Multiset ℤ) := by simp
    have hb : (-1 : ℤ) ∈ ({0, -1} : Multiset ℤ) := by simp
    rw [hs] at ha hb
    simp only [Multiset.mem_map, Multiset.mem_replicate] at ha hb
    obtain ⟨a, ⟨-, rfl⟩, ha⟩ := ha
    obtain ⟨b, ⟨-, rfl⟩, hb⟩ := hb
    omega
  · -- weight `k ≥ 2`: weights `{0, 1 − k} + s = {0, −1}`
    have h := hHT 5 ιC ιL N k χ g ρ hN (by omega) hg hss' hatt'
    obtain ⟨s, hs⟩ := hSen 5 2 ρ ρ' ψ _ _ htw (by simp) (by simp) h hw'
    refine ⟨s, ?_⟩
    rw [hs]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    congr 1
    · ring
    · congr 1; ring

end G0Galois

end G12DetWeightSec

#print axioms G0Galois.g12Weight_concl_iff
#print axioms G0Galois.g12Weight_of

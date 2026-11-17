import ZInQKernel.HDecomp.Conductor.D1Local
import ZInQKernel.Contrib.HilbertDifferent.T21

/-!
# D1 with the Hilbert and Serre arithmetic inputs proved

These five endpoints retain the full number-field, prime, index and local-core
hypotheses of the existing D1 statements, while requiring no Hilbert/Serre proof
argument. The locked baseline interfaces remain available. The local and Krasner
forms use the existing subgroup/index lemmas on the identical ideal and field.
This is classical conductor support, with zero external open-problem credit;
it does not complete the Z/Q theorem, manuscript or protocol acceptance.

Supplier source and licenses: `HilbertDifferent/Attribution.lean` and the exact
source headers in the imported modules. `T20` supplies every natural ramification
index and one common terminating index. `T21` applies to every number field,
without Galois, tame or monogenicity assumptions. The completion comparisons in
those files transport the same prime, different ideal and ramification index;
the rational-place valuation is evaluated at the very same ramification index.

Source-to-consumer comparisons (implementation evidence, independent acceptance pending):
* `T20.hilbertDifferentFormula` uses `P ≠ ⊥`, proved here from `P | p` and `p.Prime`.
  Its `ramGroup` is definitionally `(P ^ (i+1)).inertia Gal(L/ℚ)`, exactly the baseline
  group for every `i : ℕ`. Its common terminating `n` covers the entire finite support;
  monotonicity proves `b < n` when the consumed `G_b` is nontrivial.
* `LocalGlobal/RamificationGroup` extends automorphisms via `decompositionHom` from
  the stabilizer to the completion, for every natural index, and uses its bijection
  in the Galois case to compare group orders. `T20` transports the different via
  the compatible integer-ring equivalences and preserves prime multiplicity.
* `T21.serreDifferentBound` requires only a number field and a prime `P | p`.
  Its rational base-prime comparison and valuation scaling give exactly
  `v_P(e) = e * padicValNat p e`. It excludes division by zero by proving `e ≠ 0`.
  There is no odd-prime, Galois, tame or monogenicity premise on that theorem.
* `D1_genuine` combines Hilbert divisibility with the Serre nondivisibility at
  `e - 1 + e * padicValNat p e + 1`, obtaining the sum bound for the same different.
  The inertia-cardinality identity gives `g 0 = e`; `g 0 ≥ 1` justifies the rational
  denominator in `phi`. `upper_break_le` consumes this sum and `e ≤ a!`.
  The original `a ≥ 1` and `b = 0` endpoint are preserved; `p = 2` is included.
* `D1_local` uses the core-free coset action to bound `e` by `a!`.
  `D1_local'` uses `index_localSub` to identify that same subgroup index with
  `e(P ∩ 𝓞 K | p) * f(P ∩ 𝓞 K | p)`. `D1_krasner` obtains the core condition
  from the stated unique-prime and global-core hypotheses; `D1_krasner'` derives
  the latter from the stated normal-closure equality. These maps and hypotheses
  are the baseline `D1Local` ones; existence of a Krasner approximation is not claimed.
The more general complete-DVR leaves in `PkgI6` are different promises and
are not discharged by these number-field endpoints.
-/

namespace ZInQ.Contrib.Conductor

open NumberField Finset GlueConductor GlueD1Local

theorem D1_genuine
    (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (p : ℕ) [hpF : Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [hPl : P.LiesOver (Ideal.span {(p : ℤ)})]
    (a : ℕ) (ha : 1 ≤ a) (hea : P.ramificationIdx ℤ ≤ a.factorial)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 := by
  have hp : p.Prime := hpF.out
  have hP0 : P ≠ ⊥ := by
    intro h
    have := hPl.over
    rw [h, Ideal.under_bot] at this
    have h2 := Ideal.span_singleton_eq_bot.mp this
    simp [hp.ne_zero] at h2
  set g := ramCard L P with hg_def
  have hanti : Antitone g := by
    intro i j hij
    apply Subgroup.card_le_of_le
    intro σ hσ x
    exact Ideal.pow_le_pow_right (by omega) (hσ x)
  have hg1 : ∀ i, 1 ≤ g i := fun i => Nat.card_pos
  have hgb : 2 ≤ g b := by
    have h1 := hg1 b
    have h2 : g b ≠ 1 := fun h => hb (Subgroup.card_eq_one.mp h)
    omega
  obtain ⟨n, hn, hdvd, -⟩ := ZInQKernel.Contrib.HilbertDifferent.hilbertDifferentFormula L P hP0
  have hbn : b < n := by
    by_contra h
    apply hb
    rw [eq_bot_iff, ← hn]
    intro σ hσ x
    exact Ideal.pow_le_pow_right (by omega) (hσ x)
  have he : g 0 = P.ramificationIdx ℤ := by
    show Nat.card ((P ^ (0 + 1)).inertia Gal(L/ℚ)) = _
    rw [zero_add, pow_one, Ideal.card_inertia_eq_ramificationIdxIn (Ideal.span {(p : ℤ)}) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P Gal(L/ℚ)]
  have hSer := ZInQKernel.Contrib.HilbertDifferent.serreDifferentBound L p hp P hPl
  have hsum : ∑ i ∈ range n, (g i - 1) ≤ g 0 - 1 + g 0 * padicValNat p (g 0) := by
    rw [he]
    by_contra hlt
    push Not at hlt
    exact hSer (dvd_trans (pow_dvd_pow P hlt) hdvd)
  exact upper_break_le p a hp ha g hanti hg1 b n hgb hbn (he ▸ hea) hsum

variable (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]

theorem D1_local
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hcore : (localSub L K P).normalCore = ⊥)
    (a : ℕ) (ha : 1 ≤ a) (hdeg : (localSub L K P).index ≤ a)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 :=
  D1_genuine L p P a ha (ramificationIdx_le_factorial_local L p P K hcore a hdeg) b hb

theorem D1_local'
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hcore : (localSub L K P).normalCore = ⊥)
    (a : ℕ) (ha : 1 ≤ a)
    (hdeg : (P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ ≤ a)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 :=
  D1_local L p P K hcore a ha ((index_localSub L p P K).trans_le hdeg) b hb

theorem D1_krasner
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hclos : K.fixingSubgroup.normalCore = ⊥)
    (hunique : ∀ v : Ideal (𝓞 K), v.IsPrime → v.LiesOver (Ideal.span {(p : ℤ)}) →
      v = P.under (𝓞 K))
    (a : ℕ) (ha : 1 ≤ a)
    (hdeg : (P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ ≤ a)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 :=
  D1_genuine L p P a ha (ramificationIdx_le_factorial_of_unique L p P K hclos hunique a hdeg)
    b hb

theorem D1_krasner'
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hclos : IntermediateField.normalClosure ℚ K L = ⊤)
    (hunique : ∀ v : Ideal (𝓞 K), v.IsPrime → v.LiesOver (Ideal.span {(p : ℤ)}) →
      v = P.under (𝓞 K))
    (a : ℕ) (ha : 1 ≤ a)
    (hdeg : (P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ ≤ a)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 :=
  D1_krasner L p P K (normalCore_fixingSubgroup_eq_bot L K hclos) hunique a ha hdeg b hb

end ZInQ.Contrib.Conductor

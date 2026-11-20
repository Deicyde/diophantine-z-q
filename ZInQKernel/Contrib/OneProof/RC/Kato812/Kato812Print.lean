import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Kato

/-!
# The support-sensitive Kato norm relation

Draft transcription for Appendix E. Kato, Astérisque 295 (2004),
Proposition 8.12, p. 186: read (AI reading of the published PDF).
See the checklist in `docs/research/rc-kato812.md` for the remaining checks.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Kato812

open PrintsArith ZInQ.Contrib.CloudB3RC53

/-- The fixed part of the omitted support in (K4), including the coefficient prime. -/
abbrev fixedSupport (E : WeierstrassCurve ℚ) : Finset ℕ :=
  (2 * CST.newformLevel E).primeFactors

/-- The excluded set for the untwisted system of §13.1, relative to the fixed part
of the omitted support. In (K8) the variable is instead the twisted index and its
excluded set also contains the prime factors of the full odd conductor `d`. -/
abbrev oldSigma (Sbad : Finset ℕ) (c ds : ℕ) : Finset ℕ :=
  Sbad ∪ (c * ds).primeFactors

/-- (K8): the exclusions for the twisted variable `m`, written as a union of
prime supports. Here `d` is the full odd part of the primitive conductor. -/
abbrev twistedSigma (E : WeierstrassCurve ℚ) (d c ds : ℕ) : Finset ℕ :=
  oldSigma (fixedSupport E) c ds ∪ d.primeFactors

/-- Draft of Kato 8.12 in the specialization used by (K4): coefficient prime 2,
rational weight-two form of level `newformLevel E`, trivial nebentypus, `r = r' = 1`,
fixed symbol ξ in SL₂(ℤ) (or a fixed integral combination of such symbols), and
fixed smoothers `c, ds`. Kato's smoother d is the manuscript's d_s.
The symbol and smoothers are implicit in `zAt m S`, while `S` is explicit.
The known gap is identifying the abstract modules and maps of `es` with
H¹(ℤ[ζ_m,1/2], V(f)(1)) and its corestrictions.

The support convention is Kato's (5.1.1), p. 152: for ξ in SL₂(ℤ) include
prime(mN) and the coefficient prime; for ξ = a(A) also include prime(A).
The draft requires positive levels, `m ∣ m'`, finite prime supports, the
inclusion `S ∪ prime(m') ⊆ S'`, and smoothers prime to 6 with support disjoint
from `S'`. The bounds `1 < c` and `1 < ds` are conditions of this draft.
We work with 2 in both supports as in (K4).
The existing primary-source audit records the product over `S' \ S`: a prime
dividing the form level is never an index of this product, even if it divides
`m'` or `m`. The good polynomial is evaluated at `q⁻¹ σ_q⁻¹`, with arithmetic
Frobenius on the lower cyclotomic field. -/
def KatoProp812Print (E : WeierstrassCurve ℚ) (c ds : ℕ)
    (es : EulerSystemData ℤ_[2]) (zAt : ∀ m : ℕ, Finset ℕ → es.H m) : Prop :=
  E.IsElliptic → 0 < CST.newformLevel E → CST.HasCuspFormAtLevel E (CST.newformLevel E) →
    1 < c → 1 < ds → Nat.Coprime (c * ds) 6 →
    ∀ (m m' : ℕ) (S S' : Finset ℕ),
      0 < m → 0 < m' → (h : m ∣ m') →
      (∀ q ∈ S', Nat.Prime q) →
      fixedSupport E ∪ m.primeFactors ⊆ S →
      S ∪ m'.primeFactors ⊆ S' →
      Disjoint (c * ds).primeFactors S' →
      es.cor m m' h (zAt m' S') =
        (∏ q ∈ S' \ S, eulerFactor (katoP E q) (invNat ℤ_[2] q) (frobUnit m q)) • zAt m S

/-- An existing prime of the form level cannot occur in the support difference of
the printed norm. In particular, there is no bad-prime polynomial to substitute
in this specialization. -/
theorem not_mem_normSupport_of_dvd_level {E : WeierstrassCurve ℚ}
    (hN : 0 < CST.newformLevel E) {m q : ℕ} {S S' : Finset ℕ}
    (hS : fixedSupport E ∪ m.primeFactors ⊆ S) (hq : q.Prime)
    (hqN : q ∣ CST.newformLevel E) : q ∉ S' \ S := by
  intro h
  exact (Finset.mem_sdiff.mp h).2 (hS (Finset.mem_union_left _
    (hq.mem_primeFactors (dvd_mul_of_dvd_right hqN 2) (Nat.mul_ne_zero (by decide) hN.ne'))))

end ZInQ.Manuscript.RC.Kato812

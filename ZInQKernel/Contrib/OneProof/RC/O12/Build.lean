import ZInQKernel.Contrib.OneProof.RC.O12.Fourier
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Model

/-! The good Hecke formula on the individual form for the shared constructor (tex 9660–9674,
9754–9769).

The constructor `buildConstituentModel` takes its Hecke data on one ambient domain: the good
primes outside the fixed finite set `avoid`, where `UnramifiedConstituents` tests every
constituent at once. The manuscript's good Hecke test at a prime `q ∉ U` is on the form at `U`
(tex 9660–9674, 9754–9769). The smallest extra input that gives `FourierData.FormwiseHecke`
for the constructor's model is that formula on `F_U` at the good primes `q ∉ U` that lie in
`avoid`, that is, the primes excluded from the ambient Hecke domain (`hexcl` below). At the good
primes outside `avoid` the constructor's own data give it (`FourierData.goodHecke_of_data`).
No hypothesis here is stronger than the formwise statement of the text. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12

open AddressGenuine PrintsArith TraceLimits
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

section Ambient

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {chiType : GalQ →* Multiplicative L}
variable {X : GaloisConstituentModel T R ap B chiType}

/-- **The formwise good Hecke formula from the ambient Hecke data and the excluded primes.**
At a good `q ∉ U` outside `avoid` the formula comes from the ambient operators and the Fourier
data of `F_U` (tex 9660–9668). At a good `q ∉ U` inside `avoid` it is the extra input `hexcl`:
the good Hecke formula on the form `F_U` alone (tex 9670–9674). Kind: PROVED. -/
theorem formwiseHecke_of_ambient (A : FourierData X) {avoid : Finset ℕ}
    (ops : GoodOperators T avoid X.frob X.ρ X.Λ)
    (D : ∀ U, DeterminantFourierData ops X.m (X.F U)) (hD : ∀ U, (D U).coeff = A.coeff)
    (hexcl : ∀ (U : Finset ℕ) (q : ℕ), (∀ s ∈ U, T.Good s) → T.Good q → q ∉ U →
      U.card + 1 ≤ B → q ∈ avoid → ∃ diamondF : X.Λ, ∀ n,
        A.coeff n (X.tΛ (X.frob q) (X.F U)) =
          A.coeff (q * n) (X.F U) + if q ∣ n then (q : X.O) * A.coeff (n / q) diamondF else 0) :
    A.FormwiseHecke := by
  intro U q hU hq hqU hUB
  by_cases hqa : q ∈ avoid
  · exact hexcl U q hU hq hqU hUB hqa
  · exact A.goodHecke_of_data ops U (D U) (hD U) hq hqa

end Ambient

section Build

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {I K O : Type} [Field K] [CommRing O] [Algebra O K]
variable {T : TypeData L ε} {avoid : Finset ℕ} {frob : ℕ → GalQ}
variable {ρ : I → GalQ →* GL (Fin 2) K} {Λ : Submodule O (I → K)} {m : Ideal O}
variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
variable [TopologicalSpace O] [CompactSpace O] [IsNoetherianRing O]
variable [ContinuousSMul O K] [Finite (O ⧸ m)]

/-- **The formwise good Hecke formula for the shared constructor.** For the model of
`buildConstituentModel`, Fourier data `A` on its coefficient family give
`FourierData.FormwiseHecke` from one extra input: the good Hecke formula on `F_U` at the good
primes `q ∉ U` in `avoid` (`hexcl`; tex 9660–9674, 9754–9769). Kind: PROVED.

This constructor is not a discharge for the genuine added-prime packets.
`htyp`, `hS` and `hlevel` force `avoid` to contain no good prime; together
with `hunr` they make every constituent unramified at every good added prime.
Thus it cannot carry the ramified blocks of tex 9754–9758 and 9866–9873.
Tex 9649–9668 also supplies finiteness only at each fixed packet. A genuine
family discharge must assemble separate packets with per-U openness and
inertia support S ∪ U; it is not constructed here. -/
theorem formwiseHecke_of_buildConstituentModel (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (B : ℕ)
    (chiType : GalQ →* Multiplicative L) (hchi : OpenTypeKernel chiType)
    (htyp : IsTypeChar T chiType)
    (hm2 : (2 : O) ∈ m) (hm : IsClosed (m : Set O)) (hΛ : Λ.FG)
    (F : Finset ℕ → Λ)
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (hcont : ContinuousOperators ρ Λ) (hunr : UnramifiedConstituents T avoid ρ)
    (ops : GoodOperators T avoid frob ρ Λ)
    (coeff : ℕ → Λ →ₗ[O] O)
    (coefK : (I → K) →ₗ[K] ({n : ℕ // n ≠ 0} → K))
    (hspec : ∀ (v : Λ) (n : {n : ℕ // n ≠ 0}), algebraMap O K (coeff n v) = coefK v n)
    (D : ∀ U, DeterminantFourierData ops m (F U)) (hD : ∀ U, (D U).coeff = coeff)
    (hcoeff : ∀ n, Continuous (coeff n))
    (read : Finset ℕ → ({n : ℕ // n ≠ 0} → O ⧸ m) →+ ZMod 2)
    (h2fresh : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g h,
      ∀ n : ℕ, n ≠ 0 → coeff n ⟨tV ρ g (tV ρ h (F U)),
        (stable_operators T hfrob (lattice_closed Λ hΛ) hcont hunr ops).1 g _
          ((stable_operators T hfrob (lattice_closed Λ hΛ) hcont hunr ops).1 h _ (F U).2)⟩ ∈ m)
    (S : Finset ℕ) (hS : TypeDetectsRadicals chiType S)
    (hlevel : T.m.primeFactors ∪ avoid ⊆ S) (hS2 : 2 ∈ S)
    (hzero : ∀ W, ¬ (∀ p ∈ W, T.Good p) → F W = 0)
    (A : FourierData (buildConstituentModel R ap B chiType hchi htyp hm2 hm hΛ F hfrob hcont
      hunr ops coeff coefK hspec D hD hcoeff read h2fresh S hS hlevel hS2 hzero))
    (hA : A.coeff = coeff)
    (hexcl : ∀ (U : Finset ℕ) (q : ℕ), (∀ s ∈ U, T.Good s) → T.Good q → q ∉ U →
      U.card + 1 ≤ B → q ∈ avoid → ∃ diamondF : Λ, ∀ n,
        coeff n ⟨tV ρ (frob q) (F U),
          (stable_operators T hfrob (lattice_closed Λ hΛ) hcont hunr ops).1 _ _ (F U).2⟩ =
          coeff (q * n) (F U) + if q ∣ n then (q : O) * coeff (n / q) diamondF else 0) :
    A.FormwiseHecke :=
  formwiseHecke_of_ambient A ops D (fun U => (hD U).trans hA.symm) (by
    intro U q hU hq hqU hUB hqa
    rw [hA]
    exact hexcl U q hU hq hqU hUB hqa)

end Build


end ZInQ.Manuscript.RC.O12

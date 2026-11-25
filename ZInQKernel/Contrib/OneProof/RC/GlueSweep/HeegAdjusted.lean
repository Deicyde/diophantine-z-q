import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.AdjustedRep
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Interfaces

/-!
# Lane RC22 (glue sweep), share Heeg: the adjusted representative at a derivative prime

Manuscript `diophantine_zq.tex` (11/5), proof of Proposition `ex:arith-finite-heegner`,
paragraph 6 "Exact finite precision for one derivative prime", tex 3122–3190.

Lane RC10 states the one-derivative-prime computation (H13)–(H19) as
`ZInQ.Manuscript.RC.HeegnerAlgebra.H19_assembled` over the interface `DerivativePrimeInput`.
Three of its fields, `cocycle`, `tors`, `kummer_upper`, are the choice of the adjusted
representative of `b_{I∪ℓ,a}` (tex 3122–3128, classified `ELLIOT` in RC10): a cocycle `b` with
values in `E[2^a] ⊆ E` whose restriction to `G_{H_{f n_I ℓ}}` is exactly `h ↦ h Z - Z`.  The
`CloudB3RC53` layer proves this step over genuine continuous cohomology
(`ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.exists_adjusted_rep`).  Here:

* `adjusted_rep_fields`: the three fields, for the cocycle `S.incl ∘ b₀` of the representative
  `b₀` constructed there;
* `H19_assembled_adjusted`: RC10's (H19) with those three fields discharged: the adjusted
  representative of the genuine class `v ∈ H¹(G, A)` satisfies `s_new = J f_old` at precision `2^m`.
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Heeg

open TauCeti.ContCohomology
open ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

variable {G : Type*} [Group G] [TopologicalSpace G]
  {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]

/-- **The adjusted representative gives RC10's fields `cocycle`, `tors`, `kummer_upper`**,
tex 3122–3128.  Kind: `PROVED`, from the remaining hypotheses, which are those of
`exists_adjusted_rep` (the `CloudB3RC53` layer) plus the identification of the second map with
`2^a`: a short exact sequence `S : 0 → A → B → B → 0` of discrete `G`-modules with
`S.proj = 2^a` (for `0 → E[2^a] → E → E → 0`, `G = G_{H_f}`), a subgroup `N` (for
`G_{H_{f n_I ℓ}}`), a class
`v ∈ H¹(G, A)` (for `b_{I∪ℓ,a}`) whose restriction to `N` is the Kummer class of `x' ∈ B^N`, and
`Z` with `S.proj Z = x'`.  Conclusion: some cocycle `b₀` represents `v`, and `b = S.incl ∘ b₀`
satisfies `b(gk) = b(g) + g b(k)` (`cocycle`), `2^a b(g) = 0` (`tors`), and `b(h) = h Z - Z` for
`h ∈ N` (`kummer_upper`).

Consumer: the fields `cocycle`, `tors`, `kummer_upper` of
`ZInQ.Manuscript.RC.HeegnerAlgebra.DerivativePrimeInput` (lane RC10, `ELLIOT`).  Discharger:
`ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.exists_adjusted_rep`. -/
theorem adjusted_rep_fields (a : ℕ) (S : DiscreteShortExact G A B B)
    (hproj : ∀ b, S.proj b = ((2 : ℤ) ^ a) • b) (N : Subgroup G)
    (v : H1 G A) (x' : H0 N B) (Z : B) (hZ : S.proj Z = (x' : B))
    (hv : explicitRes1 G A N v = (S.restrict N).explicitDelta0 x') :
    ∃ b₀ : Z1 G A, (b₀ : H1 G A) = v ∧
      (∀ g k : G, S.incl ((b₀ : G → A) (g * k)) =
        S.incl ((b₀ : G → A) g) + g • S.incl ((b₀ : G → A) k)) ∧
      (∀ g : G, ((2 : ℤ) ^ a) • S.incl ((b₀ : G → A) g) = 0) ∧
      (∀ h ∈ N, S.incl ((b₀ : G → A) h) = h • Z - Z) := by
  obtain ⟨b₀, hb₀, hN⟩ := exists_adjusted_rep S N v x' Z hZ hv
  refine ⟨b₀, hb₀, fun g k => ?_, fun g => ?_, fun h hh => hN ⟨h, hh⟩⟩
  · have hc := ((mem_Z1_iff (G := G) (M := A)).mp b₀.2).2 g k
    rw [hc, map_add, S.incl_equivariant, add_comm]
  · rw [← hproj]
    exact S.exact.apply_apply_eq_zero _

/-- **(H16)–(H19) with the adjusted representative discharged**, tex 3122–3190.  Kind: `PROVED`,
from the remaining hypotheses: the inputs of `exists_adjusted_rep` (a short exact sequence
`S : 0 → A → B → B → 0` of discrete `G`-modules with `S.proj = 2^a`, a normal subgroup `N` for
`G_{H_{f n_I ℓ}}`, a class `v ∈ H¹(G, A)` for `b_{I∪ℓ,a}` whose restriction to `N` is the Kummer
class of the `N`-invariant point `x' = L D_ℓ Y`), and the fields of RC10's `DerivativePrimeInput`
other than `cocycle`, `tors`, `kummer_upper`, with `Hup = N`: `hZ`, `hQ` (division points), `hY`,
`hTr` ((4.1), `PRINT` Cai–Chen–Liu 2.15, unweighted: the print once the unit index
`u_1 = [𝒪_K^× : ℤ^×]` is one, `D_K < -4`), `hXfix`, `hYfix`, `hH2` ((H2) upstairs), `hu'`, `hv'`
((H12)), `hinert`, `hYX` ((H4), `ELLIOT`), `hXF`, `hchar`, `hJ` (`GLUE`).  Conclusion: some cocycle
`b₀` represents `v`, and with `b = S.incl ∘ b₀`, at precision `2^m` (`a - m ≥ e`) the singular
coordinate of `b` at the derivative place is `J` applied to the finite coordinate
`f_old = (F² - 1) Q̄`.

Consumer: `ZInQ.Manuscript.RC.HeegnerAlgebra.H19_assembled` (lane RC10).  Discharger (fields
`cocycle`, `tors`, `kummer_upper`): `ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.exists_adjusted_rep`
via `adjusted_rep_fields`. -/
theorem H19_assembled_adjusted (a : ℕ) (S : DiscreteShortExact G A B B)
    (hproj : ∀ b, S.proj b = ((2 : ℤ) ^ a) • b) (N : Subgroup G) [N.Normal]
    (v : H1 G A) (x' : H0 N B)
    (hv : explicitRes1 G A N v = (S.restrict N).explicitDelta0 x')
    {Vb : Type*} [AddCommGroup Vb] (σ : G) (ℓ e m : ℕ) (L aℓ u' v' : ℤ) (X Y Z Q : B)
    (hx' : (x' : B) = L • Dact σ ℓ Y)
    (hZ : ((2 : ℤ) ^ a) • Z = L • Dact σ ℓ Y) (hQ : ((2 : ℤ) ^ a) • Q = L • X)
    (hY : σ ^ (ℓ + 1) • Y = Y) (hTr : Tract σ ℓ Y = aℓ • X)
    (hXfix : ∀ h ∈ N, h • X = X) (hYfix : ∀ h ∈ N, h • Y = Y)
    (hH2 : ∀ P : B, (∀ h ∈ N, h • P = P) → (∃ k : ℕ, ((2 : ℤ) ^ k) • P = 0) →
      ((2 : ℤ) ^ e) • P = 0)
    (hu' : (ℓ : ℤ) + 1 = 2 ^ a * u') (hv' : aℓ = 2 ^ a * v')
    (red : B →+ Vb) (F J : Vb →+ Vb) (hinert : red (σ • Z) = red Z)
    (hYX : red Y = F (red X)) (hXF : F (F (red X)) = red X)
    (hchar : ∀ w : Vb, F (F w) - aℓ • F w + (ℓ : ℤ) • w = 0)
    (hJ : ∀ w : Vb, ((2 : ℤ) ^ a) • w = 0 → F w - aℓ • w = J w) (hm : e ≤ a - m) :
    ∃ b₀ : Z1 G A, (b₀ : H1 G A) = v ∧
      ((2 : ℤ) ^ (a - m)) • red (S.incl ((b₀ : G → A) σ)) =
        J (((2 : ℤ) ^ (a - m)) • (F (F (red Q)) - red Q)) := by
  have hZx : S.proj Z = (x' : B) := by rw [hproj, hZ, hx']
  obtain ⟨b₀, hb₀, hcoc, htors, hup⟩ := adjusted_rep_fields a S hproj N v x' Z hZx hv
  refine ⟨b₀, hb₀, ?_⟩
  exact H19_assembled
    { Hup := N, normal := inferInstance, σ := σ, ℓ := ℓ, a := a, e := e, L := L, aℓ := aℓ,
      u' := u', v' := v', X := X, Y := Y, Z := Z, Q := Q,
      b := fun g => S.incl ((b₀ : G → A) g), cocycle := hcoc, tors := htors σ,
      kummer_upper := hup, hZ := hZ, hQ := hQ, hY := hY, hTr := hTr, hXfix := hXfix,
      hYfix := hYfix, hH2 := hH2, hu' := hu', hv' := hv', red := red, F := F, J := J,
      hinert := hinert, hYX := hYX, hXF := hXF, hchar := hchar, hJ := hJ } m hm

end ZInQ.Manuscript.RC.GlueSweep.Heeg

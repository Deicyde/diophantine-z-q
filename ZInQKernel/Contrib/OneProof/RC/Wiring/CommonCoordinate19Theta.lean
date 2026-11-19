import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate17Actual
import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitFamilyPinGenuine
import ZInQKernel.Contrib.CloudB3E2Norm.GenusQuad
import ZInQKernel.Contrib.CloudB3E2Norm.H20PiBridge
import ZInQKernel.Contrib.CloudB3E1RingClass.MovingPi
import ZInQKernel.Contrib.CloudB3RC53.Companion.Disc

/-!
# The character condition and the splitting of the step primes, derived

Manuscript `diophantine_zq.tex`: the finite character `θ = χ_h Ψ` of `Δ_f` (tex 2847–2855), the
address's twist `h_x = ∏ (q*)^{λ_q(x)}` (tex 2683–2684), the family's moving character
(Proposition `ex:arith-moving-character`, tex 2725–2741, 3500–3702), the final companion
`K = ℚ(√k)` (tex 2595–2603, 2716–2721) and the split primes of the families (tex 2720–2722).

Two inputs of lane E2's class provider (`CommonCoordinate18E2.lean`) are derived here.

**(i) `ThetaOfDelta`.** For a genuine family moving character `G` (lane RC0's
`GenuineFamilyMovingCharacter`, `InnerLimitFamilyPinGenuine.lean`) and a stage `s`, the
presentation's character at the stage is `π_s = ψ_s ∘ infl` with `ψ_s = G.toFamily.ψ s` on
`G_{K, S_r(s)}` and `infl : G_{K,S₀} → G_{K,S_r(s)}` (`S_r(s) ⊆ S₀`).
* **`thetaOfDelta_family`** (PROVED): `ThetaOfDelta f` for `θ = χ_{h_x} [π_s]` at every conductor
  `f` divisible by the moving conductor `r_s` and by the primes `q` with `λ_q(x) = 1`, the primes
  of `f` lying in the support `S₁`: the quadratic part by lane E2's genus theory
  (`quadOfDelta_family`), the moving part by lane E2's `piOfDelta_of_moving` with lane E1's
  factorization of `genuinePsi` through `Gal(H_r/K)` (`ringClassRes_eq_one_of_fix`).
* `thetaCond F x r` (definition): the conductor `r ∏_{λ_q(x) = 1} q`; `thetaOfDelta_thetaCond`
  (PROVED): the condition at `f_s = thetaCond F x r_s` and at every multiple of it. The moving
  conductor `r_s` varies with the stage, so the conductors of the Heegner points must depend on
  the stage (`f_s ∣ d_s`): there is no single base conductor for all stages.

**(ii) The splitting of the step primes.** For `K` with `r ∈ K`, `r² = k`, `ℚ(r) = K` (the form
of `ActualPresentation`) and `k < 0` squarefree, `k ≡ 1 (mod 4)`:
* `finrank_of_sqrt`, `isTotallyComplex_of_sqrt`, **`discr_of_sqrt`** (PROVED): `[K : ℚ] = 2`, `K`
  totally complex, `disc K = k` (lane RC53's `Companion.discr_eq_of_sq`; no transport to
  `ℚ(√k) ⊂ ℚ̄` is needed);
* `jacobiSym_of_split` (PROVED): an odd prime `q ∤ k` at which `k` is a square has
  `(k/q) = 1`;
* **`ActualPresentation.jacobiSym_discr_step`** (PROVED): `jacobiSym (disc K) q_i = 1` for the
  step primes, from the presentation's field `split`;
* `companion_facts` (PROVED): the three facts on `k` from the ELLIOT field `RCSteps.companion`
  (in its branch `¬ D.OddEmptyUnit`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain Polynomial
open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC.SelmerComplex (GKS inflMap)
open ZInQ.Manuscript.RC.CoefModules (KS)
open ZInQ.Contrib.CloudB3E2.NormCochain (ThetaOfDelta thetaOfDelta_of quadOfDelta_family
  piOfDelta_of_moving thetaOfDelta_mono inflMap_trans)
open ZInQ.Contrib.CloudB3E1RingClass (ringClassRes_eq_one_of_fix)

/-! ### (i) The character condition -/

section Theta

variable {K : Type} [Field K] [NumberField K] {ℓ : ℕ} {Q : Finset ℕ}

/-- **`ThetaOfDelta` for the family's moving character at a stage** (PROVED; tex 2683–2684,
2847–2855, 3500–3506): for `π_s = ψ_s ∘ infl` with `ψ_s` the genuine family's moving exponent at
the stage `s` (`G.toFamily.ψ s`, on `G_{K, S_r(s)}`, `S_r(s) ⊆ S₀`) and the address's twist
`h = h_x`, the character `χ_h [π_s]` is trivial on the elements fixing `H_f`, for every `f`
divisible by the moving conductor `r_s` and by the primes `q` with `λ_q(x) = 1`, with the primes
of `f` in `S₁`. -/
theorem thetaOfDelta_family (G : GenuineFamilyMovingCharacter K ℓ Q) (s : ℕ)
    {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (h1 : S₁ ⊆ S)
    (hSr : G.toFamily.Sr s ⊆ S₀) (sh : KS K S₀) {h : K}
    (hs : sh ^ 2 = algebraMap K (KS K S₀) h) (hs0 : sh ≠ 0)
    (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K)
    (F : Family) (x : Addr F.b) (hQ : ∀ q ∈ F.Q, q.Prime ∧ q ≠ 2) (hh : h = ((F.h x : ℤ) : K))
    (f : ℕ) [NeZero f] (hf : ∀ q ∈ F.Q, F.lam q x = 1 → q ∣ f) (hrf : G.r s ∣ f)
    (hSf : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S₁) :
    ThetaOfDelta hS h1 sh hs hs0 ((G.toFamily.ψ s).comp (inflMap K hSr)) f := by
  have : NeZero (G.r s) := ⟨(G.r_prime s).ne_zero⟩
  refine thetaOfDelta_of hS h1 sh hs hs0 _ f
    (quadOfDelta_family hS h1 sh hs hs0 hK2 hTC F x hQ hh f hf hSf)
    (piOfDelta_of_moving hS h1 _ hrf (fun v hv => hSf v (by
      obtain ⟨c, rfl⟩ := hrf
      push_cast
      exact v.asIdeal.mul_mem_right _ hv)) ?_)
  intro _ S' S₁' hS' h1' hr1 g hg
  change genuinePsi G.C (G.r s) (2 * s) (G.ξ₀ s) (inflMap K hSr (inflMap K hS' g)) = 1
  rw [← inflMap_trans hSr hS' g]
  have key := ringClassRes_eq_one_of_fix (hS := G.C.hSr (G.r s)) (G.r_prime s) (hSr.trans hS')
    h1' hr1 g hg
  exact (congrArg (fun y => AddMonoidHom.toMultiplicative (G.ξ₀ s)
    (Multiplicative.ofAdd (Additive.ofMul y))) key).trans (map_one _)

/-- **The conductor of the character at a stage** (tex 2847–2855): `f = r ∏_{λ_q(x) = 1} q`
for the moving conductor `r`. Kind: definition. -/
def thetaCond (F : Family) (x : Addr F.b) (r : ℕ) : ℕ :=
  r * ∏ q ∈ F.Q.filter (fun q => F.lam q x = 1), q

/-- The conductor is nonzero for a prime `r` and a family of primes (PROVED). -/
theorem thetaCond_ne_zero (F : Family) (x : Addr F.b) {r : ℕ} (hr : r.Prime)
    (hQ : ∀ q ∈ F.Q, q.Prime ∧ q ≠ 2) : thetaCond F x r ≠ 0 :=
  mul_ne_zero hr.ne_zero (Finset.prod_ne_zero_iff.2 fun q hq =>
    (hQ q (Finset.mem_of_mem_filter q hq)).1.ne_zero)

/-- `r ∣ thetaCond F x r` (PROVED). -/
theorem dvd_thetaCond_r (F : Family) (x : Addr F.b) (r : ℕ) : r ∣ thetaCond F x r :=
  dvd_mul_right r _

/-- `q ∣ thetaCond F x r` for `q ∈ Q` with `λ_q(x) = 1` (PROVED). -/
theorem dvd_thetaCond_q (F : Family) (x : Addr F.b) (r : ℕ) {q : ℕ} (hq : q ∈ F.Q)
    (hl : F.lam q x = 1) : q ∣ thetaCond F x r :=
  (Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hq, hl⟩)).mul_left r

/-- **`ThetaOfDelta` at every multiple of the conductor `f_s = r_s ∏_{λ_q(x) = 1} q`**
(PROVED; tex 2847–2855): `thetaOfDelta_family` at `f_s`, then `thetaOfDelta_mono`. The primes of
`d` lie in `S₁`. -/
theorem thetaOfDelta_thetaCond (G : GenuineFamilyMovingCharacter K ℓ Q) (s : ℕ)
    {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (h1 : S₁ ⊆ S)
    (hSr : G.toFamily.Sr s ⊆ S₀) (sh : KS K S₀) {h : K}
    (hs : sh ^ 2 = algebraMap K (KS K S₀) h) (hs0 : sh ≠ 0)
    (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K)
    (F : Family) (x : Addr F.b) (hQ : ∀ q ∈ F.Q, q.Prime ∧ q ≠ 2) (hh : h = ((F.h x : ℤ) : K))
    {d : ℕ} [NeZero d] (hfd : thetaCond F x (G.r s) ∣ d)
    (hSd : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S₁) :
    ThetaOfDelta hS h1 sh hs hs0 ((G.toFamily.ψ s).comp (inflMap K hSr)) d :=
  thetaOfDelta_family G s hS h1 hSr sh hs hs0 hK2 hTC F x hQ hh d
    (fun _ hq hl => (dvd_thetaCond_q F x (G.r s) hq hl).trans hfd)
    ((dvd_thetaCond_r F x (G.r s)).trans hfd) hSd

end Theta

/-! ### (ii) The splitting of the step primes -/

section Split

variable {K : Type} [Field K] [NumberField K]

/-- **`[K : ℚ] = 2`** for `K = ℚ(r)`, `r² = k < 0` (PROVED; the minimal polynomial is
`X² − k`). -/
theorem finrank_of_sqrt {r : K} {k : ℤ} (hr : r ^ 2 = ((k : ℤ) : K))
    (hgen : Algebra.adjoin ℚ {r} = ⊤) (hk0 : k < 0) : Module.finrank ℚ K = 2 := by
  have hk : ((k : ℤ) : ℚ) < 0 := by exact_mod_cast hk0
  have hirr : Irreducible (X ^ 2 - C ((k : ℤ) : ℚ) : ℚ[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => by nlinarith [sq_nonneg b])
  have hmin : minpoly ℚ r = X ^ 2 - C ((k : ℤ) : ℚ) := by
    refine (minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C _ two_ne_zero)).symm
    simp [hr]
  have hint : IsIntegral ℚ r := Algebra.IsIntegral.isIntegral r
  have htop : IntermediateField.adjoin ℚ {r} = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra ℚ {r} hgen
  rw [← IntermediateField.finrank_top', ← htop, IntermediateField.adjoin.finrank hint, hmin,
    natDegree_X_pow_sub_C]

omit [NumberField K] in
/-- **`K` is totally complex** when it contains a square root of a negative integer (PROVED). -/
theorem isTotallyComplex_of_sqrt {r : K} {k : ℤ} (hr : r ^ 2 = ((k : ℤ) : K)) (hk0 : k < 0) :
    IsTotallyComplex K := by
  refine ⟨fun w => ?_⟩
  by_contra hw
  rw [InfinitePlace.not_isComplex_iff_isReal, InfinitePlace.isReal_iff] at hw
  let ψ := hw.embedding
  have h := congrArg ψ hr
  rw [map_pow, map_intCast] at h
  have : ((k : ℤ) : ℝ) < 0 := by exact_mod_cast hk0
  nlinarith [sq_nonneg (ψ r)]

/-- **`disc K = k`** for `K = ℚ(r)`, `r² = k`, `k < 0` squarefree, `k ≡ 1 (mod 4)` (PROVED; lane
RC53's `Companion.discr_eq_of_sq`). -/
theorem discr_of_sqrt {r : K} {k : ℤ} (hr : r ^ 2 = ((k : ℤ) : K))
    (hgen : Algebra.adjoin ℚ {r} = ⊤) (hk0 : k < 0) (hksq : Squarefree k) (hk4 : k % 4 = 1) :
    discr K = k :=
  Companion.discr_eq_of_sq (finrank_of_sqrt hr hgen hk0) hksq hk4 (by omega) hr

/-- **A prime `q ∤ k` at which `k` is a square has `(k/q) = 1`** (PROVED). -/
theorem jacobiSym_of_split {k : ℤ} {q : ℕ} (hq : q.Prime)
    (hsplit : ¬ (q : ℤ) ∣ k ∧ IsSquare ((k : ℤ) : ZMod q)) : jacobiSym k q = 1 := by
  have := Fact.mk hq
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  exact (legendreSym.eq_one_iff q fun h0 =>
    hsplit.1 ((ZMod.intCast_zmod_eq_zero_iff_dvd k q).1 h0)).2 hsplit.2

/-- **The facts on the final companion** (PROVED from the ELLIOT field `RCSteps.companion`, tex
2595–2603, in its branch `¬ D.OddEmptyUnit`): `k < 0`, `k` squarefree, `k ≡ 1 (mod 4)`. -/
theorem companion_facts {ℓ : ℕ} {D : RCData ℓ} (St : RCSteps D) (hodd : ¬ D.OddEmptyUnit) :
    D.kfin < 0 ∧ Squarefree D.kfin ∧ D.kfin % 4 = 1 := by
  obtain ⟨hk0, hksq, -, -, -, hk4, -⟩ := St.companion hodd
  exact ⟨hk0, hksq, hk4⟩

variable {ℓ : ℕ} {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ} {Fam : Family} {x : Addr Fam.b}

/-- `[K : ℚ] = 2` for the presentation's field (PROVED from `r² = k`, `ℚ(r) = K`, `k < 0`). -/
theorem ActualPresentation.finrank_two (A : ActualPresentation C D Fam x) (hk0 : D.kfin < 0) :
    Module.finrank ℚ C.K = 2 :=
  finrank_of_sqrt A.hr A.hgen hk0

/-- The presentation's field is totally complex (PROVED from `r² = k < 0`). -/
theorem ActualPresentation.isTotallyComplex (A : ActualPresentation C D Fam x)
    (hk0 : D.kfin < 0) : IsTotallyComplex C.K :=
  isTotallyComplex_of_sqrt A.hr hk0

/-- `disc K = k` for the presentation's field (PROVED). -/
theorem ActualPresentation.discr_eq (A : ActualPresentation C D Fam x) (hk0 : D.kfin < 0)
    (hksq : Squarefree D.kfin) (hk4 : D.kfin % 4 = 1) : discr C.K = D.kfin :=
  discr_of_sqrt A.hr A.hgen hk0 hksq hk4

/-- **The step primes split: `jacobiSym (disc K) q_i = 1`** (PROVED from the presentation's field
`split` and the companion facts; tex 2720–2722, 4142–4146). This is the field `hsplit` of
`E2ChainInputs` (`CommonCoordinate18E2.lean`). -/
theorem ActualPresentation.jacobiSym_discr_step (A : ActualPresentation C D Fam x)
    (hk0 : D.kfin < 0) (hksq : Squarefree D.kfin) (hk4 : D.kfin % 4 = 1) {i : ℕ}
    (hi : i < A.ps.length) : jacobiSym (discr C.K) (A.ps.getD i 1) = 1 := by
  rw [A.discr_eq hk0 hksq hk4]
  obtain ⟨hqQ, -⟩ := mem_unusedAt.mp (A.mem_unused hi)
  exact jacobiSym_of_split (A.hprime _ hqQ).1 (A.split _ hqQ)

end Split

end ZInQ.Manuscript.RC.Wiring

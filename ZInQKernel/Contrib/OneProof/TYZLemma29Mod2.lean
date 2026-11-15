import ZInQKernel.Contrib.TYZDecomp.Leaves
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Adeles.FiniteBaseChange
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup

/-!
# `TYZLemma29Mod2` from Tian–Yuan–Zhang's Lemma 2.9 and Proposition 2.3 in printed form

Task h29-split; report `docs/research/h29-split.md`, scratch copy and log in `scratch/h29-split/`.

Tian–Yuan–Zhang (TYZ), *Genus periods, genus points and congruent number problem*, arXiv:1411.4728v1,
Asian J. Math. 21 (2017). Line numbers `Lnnnn` refer to the arXiv source `Period7.tex`, read by this task.

The hypothesis `h29 = ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2` of `ZInQ.OneProof.frozenTarget` is proved
(`tyzLemma29Mod2_of_printedLeaves`) from four statements over genuine definitions:

* `TYZLemma29Printed`: TYZ Lemma 2.9 (L1062–1066), `Σ ε(d₁, d₂)𝓛(d₁)𝓛(d₂) = Q(n)`, with the genus period
  `Q(n) = Σ_{t ∈ 2Cl_n} f_n(t)` (L566–568) of TYZ's test vector `f_n`;
* `TYZProp23Printed`: TYZ Proposition 2.3 (L580–586), `f_n((B̂^×)²) ⊂ 1 + 2ℤ`;
* `TYZTauExists`: the embedding `τ : K_n → B` TYZ fix (L527–534; Legendre, Jones–Pall Theorem 5);
* `TYZTestVectorExists`: `π_ℤ^{U_n}` has a generator `f_n` (L542–550, Theorem 2.6 at `χ = 1`).

`TYZTauExists` is in turn proved (`tyzTauExists_of_legendreJonesPall`) from `LegendreJonesPall`, the
three-square statement TYZ cite (Legendre; Jones–Pall, Theorem 5), so
`tyzLemma29Mod2_of_printedLeaves_threeSquares` proves `h29` from `LegendreJonesPall`, `TYZTestVectorExists`,
`TYZLemma29Printed`, `TYZProp23Printed`.

Here `B = ℍ[ℚ]`, `B̂ = ℍ[𝔸ᶠ_ℚ]`, `K̂_n = 𝔸ᶠ_{K_n}` (Tau Ceti's base change `𝔸ᶠ_{K_n} ≅ 𝔸ᶠ_ℚ ⊗ K_n`),
`Cl_n` through Tau Ceti's `FiniteAdeleRing.toClassGroup`, `U_n = R̂_n^× K_{n,2}^×` with `R_n = O_{K_n} + 4O_B`,
and `π_ℤ^{U_n}` is pinned by the Hecke eigenvalues `a_p(E)`, `E : y² = x³ − x`, at the odd primes (`InPiZ`).
The glue: the mod-2 reduction (`tyzLemma29Mod2_of_printed`: `ε = ±1` and `w_K ∈ {1, 3}` vanish mod 2), the
"therefore" of Proposition 2.3 (`genusPeriod_mod_two`: `Q(n) ≡ #2Cl_n = g(n)`), and the class-group step
(`odd_on_sqClasses`: a class in `2Cl_n` is `s²` up to `K^×` and `Ô_K^×`, under which `f_n` is invariant).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZDecomp.H29Split

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp NumberField

/-! ## §1. The printed forms -/

/-- `ℓ` is a sign choice of TYZ's `𝓛` on the squarefree classes `1, 3 (mod 8)`; this is the
hypothesis on `ℓ` in `TYZLemma29Mod2`. -/
def IsLcalSign (ℓ : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℂ)) ^ 2 = lcalSq m

theorem tyzLemma29Mod2_iff_forall : TYZLemma29Mod2 ↔ ∀ ℓ, IsLcalSign ℓ → LemmaTwoEight ℓ :=
  Iff.rfl

/-- The non-ordered decompositions `m = d₁d₂` with `d₂ ≡ 1 (mod 8)` of an odd squarefree `m > 1`,
indexed by one member `d`. For `m ≡ 3`, `d = d₂` (the other factor is `≡ 3`, so the pair is
determined by `d₂`). For `m ≡ 1`, both factors are `≡ 1` and `d ≠ m/d`; the pair `{d, m/d}` is
indexed by its smaller member (`d² < m`). -/
def pairIdx (m : ℕ) : Finset ℕ :=
  m.divisors.filter (fun d => d % 8 = 1 ∧ (m % 8 = 1 → d * d < m))

/-- **TYZ Lemma 2.9 (L1062–1066), printed form, odd classes, with the genus period `Q` as a
parameter.** For every sign choice `ℓ` of `𝓛` and squarefree `1 < m ≡ 1, 3 (mod 8)` there are signs
`ε = ±1` with `w · Σ_{m = d₁d₂, d₂ ≡ 1} ε 𝓛(d₁)𝓛(d₂) = Q(m)`, where `w = 1`, or `w = 3 = w_K` at
`m = 3`.

The factor `w`: TYZ's proof gives `w_K Σ ε𝓛𝓛 = Q(m)` with `w_K = [𝓞_K^× : {±1}]`, which is `3` for
`ℚ(√−3)` and `1` for the other `ℚ(√−m)`, `m > 1` odd squarefree (rv-nt-tyz B1, confirmed by
rv-tyz-inputs §1.2; it is not decided whether Lemma 2.9 or Theorem 2.1 is misprinted). The
disjunction is implied by the printed lemma (`w = 1`) and by the corrected one. Restricting to odd
`m > 1` and quantifying over all sign choices `ℓ` (a sign change of `ℓ` is absorbed by `ε`) also
weakens or preserves the print. -/
def Lemma29Printed (Q : ℕ → ℤ) : Prop :=
  ∀ ℓ : ℕ → ℤ, IsLcalSign ℓ → ∀ m : ℕ, Squarefree m → 1 < m → (m % 8 = 1 ∨ m % 8 = 3) →
    ∃ ε : ℕ → ℤ, (∀ d, ε d = 1 ∨ ε d = -1) ∧ ∃ w : ℤ, (w = 1 ∨ (m = 3 ∧ w = 3)) ∧
      w * ∑ d ∈ pairIdx m, ε d * (ℓ (m / d) * ℓ d) = Q m

/-- The conclusion of TYZ Lemma 2.9 at one `m`, for the value `Qm` of the genus period (the body of
`Lemma29Printed`, with `ℓ` quantified first). -/
def Lemma29At (m : ℕ) (Qm : ℤ) : Prop :=
  ∀ ℓ : ℕ → ℤ, IsLcalSign ℓ →
    ∃ ε : ℕ → ℤ, (∀ d, ε d = 1 ∨ ε d = -1) ∧ ∃ w : ℤ, (w = 1 ∨ (m = 3 ∧ w = 3)) ∧
      w * ∑ d ∈ pairIdx m, ε d * (ℓ (m / d) * ℓ d) = Qm

/-- **TYZ Proposition 2.3 (L580–586), conclusion, odd classes, with `Q` as a parameter**:
`Q(m) ≡ g(m) (mod 2)`, `g(m) = #2Cl(ℚ(√−m))` (`gNat`, TYZ L363). -/
def Prop23Cong (Q : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((Q m : ℤ) : ZMod 2) = (gNat m : ZMod 2)

/-- A family of integer functions on the class groups `Cl(𝓞_{ℚ(√−n)})`, `n ≠ 0` (the type of the
restriction of TYZ's test vectors `f_n` to `K̂_n^×`). -/
abbrev ClFun : Type := ∀ (n : ℕ) [NeZero n], ClassGroup (𝓞 (QNeg n)) → ℤ

/-- The subgroup `2Cl_n` of squares, as a finset. -/
def sqClasses (n : ℕ) [NeZero n] : Finset (ClassGroup (𝓞 (QNeg n))) := by
  classical
  exact Finset.univ.filter
    (fun t => t ∈ (powMonoidHom 2 : ClassGroup (𝓞 (QNeg n)) →* ClassGroup (𝓞 (QNeg n))).range)

/-- The genus period `Q_f(n) = Σ_{t ∈ 2Cl_n} f_n(t)` (`0` at `n = 0`). -/
def genusPeriod (f : ClFun) (n : ℕ) : ℤ :=
  if h : n = 0 then 0 else haveI : NeZero n := ⟨h⟩; ∑ t ∈ sqClasses n, f n t

/-- **TYZ Proposition 2.3 (L580–586), first assertion, restricted to `K̂^×` (odd classes)**: `f_n` takes
odd values on `2Cl_n`. (Printed: `f_n((B̂^×)²) ⊂ 1 + 2ℤ`; a class `t ∈ 2Cl_n` is `s²` up to `K^×` and
`Ô_K^×`, under which `f_n` is invariant, so the printed assertion gives this one.) -/
def Prop23Odd (f : ClFun) : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ t ∈ sqClasses n, Odd (f n t)

/-! ## §2. Glue -/

theorem mem_sqClasses {n : ℕ} [NeZero n] {t : ClassGroup (𝓞 (QNeg n))} :
    t ∈ sqClasses n ↔
      t ∈ (powMonoidHom 2 : ClassGroup (𝓞 (QNeg n)) →* ClassGroup (𝓞 (QNeg n))).range := by
  classical
  simp [sqClasses]

theorem one_mem_sqClasses (n : ℕ) [NeZero n] : (1 : ClassGroup (𝓞 (QNeg n))) ∈ sqClasses n :=
  mem_sqClasses.mpr (Subgroup.one_mem _)

/-- `#2Cl_n = g(n)`. -/
theorem card_sqClasses (n : ℕ) [NeZero n] : (sqClasses n).card = gCl n := by
  rw [gCl, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_sqClasses)

theorem gNat_of_ne {n : ℕ} [NeZero n] : gNat n = gCl n := by
  simp [gNat, NeZero.ne n]

theorem genusPeriod_of_ne (f : ClFun) {n : ℕ} [NeZero n] :
    genusPeriod f n = ∑ t ∈ sqClasses n, f n t := by
  simp [genusPeriod, NeZero.ne n]

theorem intCast_eq_one_of_odd {a : ℤ} (h : Odd a) : ((a : ℤ) : ZMod 2) = 1 :=
  ZMod.intCast_eq_one_iff_odd.mpr h

/-- **The "therefore" of Proposition 2.3**: odd values on `2Cl_n` give `Q(n) ≡ #2Cl_n = g(n)`. -/
theorem genusPeriod_mod_two (f : ClFun) {n : ℕ} [NeZero n]
    (hf : ∀ t ∈ sqClasses n, Odd (f n t)) :
    ((genusPeriod f n : ℤ) : ZMod 2) = (gNat n : ZMod 2) := by
  rw [genusPeriod_of_ne, gNat_of_ne, ← card_sqClasses]
  push_cast
  rw [Finset.sum_congr rfl fun t ht => intCast_eq_one_of_odd (hf t ht)]
  simp

theorem prop23Cong_of_odd {f : ClFun} (h : Prop23Odd f) : Prop23Cong (genusPeriod f) := by
  intro m hsq hcl
  have : NeZero m := ⟨hsq.ne_zero⟩
  exact genusPeriod_mod_two f (h m hsq hcl)

theorem cast_sum_eps (s : Finset ℕ) (ε a : ℕ → ℤ) (hε : ∀ d, ε d = 1 ∨ ε d = -1) :
    ((∑ d ∈ s, ε d * a d : ℤ) : ZMod 2) = ((∑ d ∈ s, a d : ℤ) : ZMod 2) := by
  push_cast
  refine Finset.sum_congr rfl fun d _ => ?_
  rcases hε d with h | h <;> rw [h] <;> simp [ZMod.neg_eq_self_mod_two]

theorem pairIdx_one {m : ℕ} (hm : m % 8 = 1) :
    pairIdx m = m.divisors.filter (fun d => d % 8 = 1 ∧ d * d < m) := by
  unfold pairIdx
  refine Finset.filter_congr fun d _ => ?_
  simp [hm]

theorem pairIdx_three {m : ℕ} (hm : m % 8 = 3) :
    pairIdx m = m.divisors.filter (fun d => d % 8 = 1) := by
  unfold pairIdx
  refine Finset.filter_congr fun d _ => ?_
  simp [hm]

/-- One instance of the printed lemma, read modulo 2. -/
theorem sum_mod_two_of_printed {Q : ℕ → ℤ} (hP : Lemma29Printed Q) {ℓ : ℕ → ℤ} (hℓ : IsLcalSign ℓ)
    {m : ℕ} (hsq : Squarefree m) (h1 : 1 < m) (hcl : m % 8 = 1 ∨ m % 8 = 3) :
    ((∑ d ∈ pairIdx m, ℓ (m / d) * ℓ d : ℤ) : ZMod 2) = ((Q m : ℤ) : ZMod 2) := by
  obtain ⟨ε, hε, w, hw, heq⟩ := hP ℓ hℓ m hsq h1 hcl
  have hw2 : ((w : ℤ) : ZMod 2) = 1 := by
    rcases hw with rfl | ⟨-, rfl⟩
    · simp
    · decide
  rw [← heq, ← cast_sum_eps _ ε _ hε]
  push_cast
  rw [hw2, one_mul]

/-- **The mod-2 reduction (glue)**: the printed Lemma 2.9 and the conclusion of Proposition 2.3,
for the same `Q`, give the target. -/
theorem tyzLemma29Mod2_of_printed {Q : ℕ → ℤ} (hP : Lemma29Printed Q) (hC : Prop23Cong Q) :
    TYZLemma29Mod2 := by
  intro ℓ hℓ
  constructor
  · intro m hsq h1 hm
    have := sum_mod_two_of_printed hP hℓ hsq h1 (Or.inl hm)
    rw [pairIdx_one hm, hC m hsq (Or.inl hm)] at this
    rw [← this]
    push_cast
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  · intro m hsq hm
    have h1 : 1 < m := by omega
    have := sum_mod_two_of_printed hP hℓ hsq h1 (Or.inr hm)
    rw [pairIdx_three hm, hC m hsq (Or.inr hm)] at this
    exact this

/-- **The split, over the genus period of a class-group function `f`**: Lemma 2.9 for `Q_f` and
Proposition 2.3's first assertion for `f` give the target, for every `f`. -/
theorem tyzLemma29Mod2_of_printedF {f : ClFun} (hP : Lemma29Printed (genusPeriod f))
    (hO : Prop23Odd f) : TYZLemma29Mod2 :=
  tyzLemma29Mod2_of_printed hP (prop23Cong_of_odd hO)

/-! ## §5. TYZ's objects over genuine definitions

TYZ §2.1 (L496–586) and §2.2 (L589–842), read in the source by this task (see the log). The
quaternion algebra `B` ramified at `2, ∞` is Hamilton's `ℍ[ℚ]` (`i² = j² = −1`, `ij = k = −ji`, TYZ
L520–523); `B̂ = B ⊗ 𝔸ᶠ_ℚ` is `ℍ[𝔸ᶠ_ℚ]`; `K̂_n = 𝔸ᶠ_{K_n}` maps to `B̂` through Tau Ceti's base change
`𝔸ᶠ_{K_n} ≅ 𝔸ᶠ_ℚ ⊗_ℚ K_n` and `τ`; `Cl_n = K_n^× \ K̂_n^× / Ô_{K_n}^×` through Tau Ceti's
`FiniteAdeleRing.toClassGroup`. TYZ's `π_ℤ^{U_n}` is pinned by its Hecke eigenvalues `a_p(E)` at the
odd primes (see `InPiZ`). -/

section Genuine

open IsDedekindDomain
open scoped Quaternion TensorProduct FiniteAdeleExtension

/-- `𝔸ᶠ_ℚ`, the finite adeles of `ℚ`. -/
abbrev AQ : Type := FiniteAdeleRing (𝓞 ℚ) ℚ

/-- `B → B̂`: `ℍ[ℚ] → ℍ[𝔸ᶠ_ℚ]`, coordinatewise. -/
def qι : ℍ[ℚ] →ₐ[ℚ] ℍ[AQ] where
  toFun q := ⟨algebraMap ℚ AQ q.re, algebraMap ℚ AQ q.imI, algebraMap ℚ AQ q.imJ,
    algebraMap ℚ AQ q.imK⟩
  map_one' := by apply Quaternion.ext <;> simp
  map_mul' a b := by
    apply Quaternion.ext <;>
      simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
        map_mul, map_add, map_sub]
  map_zero' := by apply Quaternion.ext <;> simp
  map_add' a b := by apply Quaternion.ext <;> simp
  commutes' r := by apply Quaternion.ext <;> simp [Algebra.algebraMap_eq_smul_one]

/-- **TYZ's maximal order `O_B = O_B' + ℤζ`**, `O_B' = ℤ + ℤi + ℤj + ℤk`, `ζ = (−1 + i + j + k)/2`
(TYZ L524–525): membership. -/
def IsHurwitz (q : ℍ[ℚ]) : Prop :=
  ∃ a b c d e : ℤ, q = ⟨a - e / 2, b + e / 2, c + e / 2, d + e / 2⟩

/-- `Ô_B = O_B ⊗ Ẑ ⊂ B̂`: `a + bi + cj + dk + eζ` with `a, …, e ∈ Ẑ`. -/
def hurwitzHat : Set ℍ[AQ] :=
  {x | ∃ a b c d e : AQ, a ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ ∧
    b ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ ∧ c ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ ∧
    d ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ ∧ e ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ ∧
    x = ⟨a - e * algebraMap ℚ AQ (1 / 2), b + e * algebraMap ℚ AQ (1 / 2),
      c + e * algebraMap ℚ AQ (1 / 2), d + e * algebraMap ℚ AQ (1 / 2)⟩}

/-- `√−n ∈ K_n = ℚ(√−n)`: Mathlib's `QuadraticAlgebra.omega`, with `ω² = −n`. -/
abbrev sqrtNeg (n : ℕ) : QNeg n := QuadraticAlgebra.omega

/-- **TYZ's embedding `τ : K_n → B`** (L527–534): `τ(O_{K_n}) ⊂ O_B`, and for `n ≡ 1 (mod 8)`,
`τ(√−n) = ai + bj + ck` with `n = a² + b² + c²`, `a, b, c ∈ ℤ`, `4 ∣ c`. -/
def AdmissibleTau (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) : Prop :=
  (∀ x : 𝓞 (QNeg n), IsHurwitz (τ (x : QNeg n))) ∧
    (n % 8 = 1 → ∃ a b c : ℤ, (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 ∧ 4 ∣ c ∧
      τ (sqrtNeg n) = ⟨0, (a : ℚ), (b : ℚ), (c : ℚ)⟩)

/-- `τ̂ : K̂_n = 𝔸ᶠ_{K_n} → B̂`: Tau Ceti's base change `𝔸ᶠ_{K_n} ≅ 𝔸ᶠ_ℚ ⊗_ℚ K_n`, then
`a ⊗ x ↦ a · τ(x)`. -/
def tauHat (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) :
    FiniteAdeleRing (𝓞 (QNeg n)) (QNeg n) →+* ℍ[AQ] :=
  (AlgHom.liftEquiv ℚ AQ (QNeg n) ℍ[AQ] ((qι).comp τ)).toRingHom.comp
    (TauCeti.GlobalNumberFields.finiteAdeleBaseChangeAlgEquiv ℚ (QNeg n)).symm.toRingHom

theorem tauHat_algebraMap (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (k : QNeg n) :
    tauHat n τ (algebraMap (QNeg n) _ k) = qι (τ k) := by
  simp [tauHat]

/-- `τ̂` on units: `K̂_n^× → B̂^×`. -/
def tauHatU (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) :
    (FiniteAdeleRing (𝓞 (QNeg n)) (QNeg n))ˣ →* ℍ[AQ]ˣ :=
  Units.map (tauHat n τ).toMonoidHom

/-- `R̂_n = R_n ⊗ Ẑ = τ̂(Ô_{K_n}) + 4Ô_B` for TYZ's order `R_n = O_{K_n} + 4O_B` (L543–544). -/
def RnHat (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) : AddSubgroup ℍ[AQ] :=
  AddSubgroup.closure
    (tauHat n τ '' (FiniteAdeleRing.integralAdeles (𝓞 (QNeg n)) (QNeg n) : Set _) ∪
      (fun y => 4 * y) '' hurwitzHat)

/-- `R̂_n^×`. -/
def RnUnits (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) : Set ℍ[AQ]ˣ :=
  {u | (u : ℍ[AQ]) ∈ RnHat n τ ∧ ((u⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) ∈ RnHat n τ}

/-- The finite place `2` of `ℚ`. -/
def IsPlaceTwo (v : HeightOneSpectrum (𝓞 ℚ)) : Prop := (2 : 𝓞 ℚ) ∈ v.asIdeal

/-- `K_{n,2}^× ⊂ B̂^×`: the units of `B̂` with component `1` away from `2` whose component at `2`
lies in `τ(K_n) ⊗ ℚ₂`, i.e. commutes with `τ(√−n)` (the centralizer of `τ(K_n)` in `B ⊗ ℚ₂`). -/
def K2Units (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) : Set ℍ[AQ]ˣ :=
  {x | Commute (x : ℍ[AQ]) (qι (τ (sqrtNeg n))) ∧ ∀ v, ¬ IsPlaceTwo v →
    (x : ℍ[AQ]).re v = 1 ∧ (x : ℍ[AQ]).imI v = 0 ∧ (x : ℍ[AQ]).imJ v = 0 ∧
      (x : ℍ[AQ]).imK v = 0}

/-- **TYZ's `U_n = R̂_n^× · K_{n,2}^×`** (L543), as the subgroup of `B̂^×` it generates (invariance
under a set and under the subgroup it generates are the same). -/
def Un (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) : Subgroup ℍ[AQ]ˣ :=
  Subgroup.closure (RnUnits n τ ∪ K2Units n τ)

open Classical in
/-- The idempotent of `𝔸ᶠ_ℚ` supported at the place `v`. -/
def eAt (v : HeightOneSpectrum (𝓞 ℚ)) : AQ :=
  ⟨fun w => if w = v then 1 else 0, Filter.Eventually.of_forall fun w => by
    dsimp only; split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

/-- `B → B̂` at the place `v` only: `α` at `v`, `1` elsewhere. -/
def ιAt (v : HeightOneSpectrum (𝓞 ℚ)) (α : ℍ[ℚ]) : ℍ[AQ] :=
  algebraMap AQ ℍ[AQ] (eAt v) * qι α + algebraMap AQ ℍ[AQ] (1 - eAt v)

/-- `a_p(E)` for TYZ's `E : y² = x³ − x` (L513): `a_p = p + 1 − #E(𝔽_p) = −Σ_x ((x³ − x)/p)`. -/
def apE (p : ℕ) : ℤ := -∑ x ∈ Finset.range p, jacobiSym ((x : ℤ) ^ 3 - x) p

/-- The Hurwitz quaternions of reduced norm `p`, as `2α = (a, b, c, d)` with `a ≡ b ≡ c ≡ d (mod 2)`
and `a² + b² + c² + d² = 4p`. -/
def hurwitzNorm (p : ℕ) : Finset (ℤ × ℤ × ℤ × ℤ) :=
  ((Finset.Icc (-(2 * p : ℤ)) (2 * p)) ×ˢ (Finset.Icc (-(2 * p : ℤ)) (2 * p)) ×ˢ
      (Finset.Icc (-(2 * p : ℤ)) (2 * p)) ×ˢ (Finset.Icc (-(2 * p : ℤ)) (2 * p))).filter
    (fun t => (t.1 - t.2.1) % 2 = 0 ∧ (t.1 - t.2.2.1) % 2 = 0 ∧ (t.1 - t.2.2.2) % 2 = 0 ∧
      t.1 ^ 2 + t.2.1 ^ 2 + t.2.2.1 ^ 2 + t.2.2.2 ^ 2 = 4 * p)

/-- `(a, b, c, d) ↦ (a + bi + cj + dk)/2`. -/
def quatOf (t : ℤ × ℤ × ℤ × ℤ) : ℍ[ℚ] :=
  ⟨(t.1 : ℚ) / 2, (t.2.1 : ℚ) / 2, (t.2.2.1 : ℚ) / 2, (t.2.2.2 : ℚ) / 2⟩

/-- **TYZ's `π_ℤ^{U_n}`** (L536–550): the integer-valued functions on `B̂^×` (values off `B̂^×` are
not used) that are left `B^×`-invariant, right `U_n`- and `𝔸ᶠ_ℚ^×`-invariant, and lie in `π`, the
Jacquet–Langlands transfer of the newform of `E` (level 32). Membership in `π` is imposed through the
Hecke eigenvalues: for every odd prime `p` (where `U_{n,p} = O_{B,p}^×`), the sum over the `24(p + 1)`
Hurwitz quaternions `α` of norm `p` of `f(x · α_p)` is `24 a_p(E) f(x)` (each of the `p + 1` cosets of
`T_p` is met by `|O_B^×| = 24` of them). By strong multiplicity one for `GL₂`, the injectivity of
Jacquet–Langlands and multiplicity one for `B^×`, the `U_n`-invariant forms with these eigenvalues are
exactly `π^{U_n}` (the one-dimensional representations have eigenvalue `p + 1 ≠ a_p`). This bridge is
standard but not printed in TYZ. -/
def InPiZ (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (f : ℍ[AQ] → ℤ) : Prop :=
  (∀ γ : ℍ[ℚ], γ ≠ 0 → ∀ x : ℍ[AQ]ˣ, f (qι γ * x) = f x) ∧
    (∀ x : ℍ[AQ]ˣ, ∀ u ∈ Un n τ, f ((x : ℍ[AQ]) * u) = f x) ∧
    (∀ x : ℍ[AQ]ˣ, ∀ z : AQˣ, f ((x : ℍ[AQ]) * algebraMap AQ ℍ[AQ] z) = f x) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → ∀ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ v.asIdeal →
      ∀ x : ℍ[AQ]ˣ, ∑ t ∈ hurwitzNorm p, f ((x : ℍ[AQ]) * ιAt v (quatOf t)) = 24 * apE p * f x)

/-- **TYZ's test vector `f_n`** (L550): a `ℤ`-generator of `π_ℤ^{U_n}`. -/
def IsTestVector (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (f : ℍ[AQ] → ℤ) : Prop :=
  InPiZ n τ f ∧ ∀ g, InPiZ n τ g → ∃ c : ℤ, ∀ x : ℍ[AQ]ˣ, g x = c * f x

/-- A finite idele of `K_n` in a given ideal class (Tau Ceti's `toClassGroup` is onto). -/
def clLift (n : ℕ) [NeZero n] (t : ClassGroup (𝓞 (QNeg n))) :
    (FiniteAdeleRing (𝓞 (QNeg n)) (QNeg n))ˣ :=
  (FiniteAdeleRing.toClassGroup_surjective (R := 𝓞 (QNeg n)) (K := QNeg n) t).choose

theorem toClassGroup_clLift (n : ℕ) [NeZero n] (t : ClassGroup (𝓞 (QNeg n))) :
    FiniteAdeleRing.toClassGroup (𝓞 (QNeg n)) (QNeg n) (clLift n t) = t :=
  (FiniteAdeleRing.toClassGroup_surjective (R := 𝓞 (QNeg n)) (K := QNeg n) t).choose_spec

/-- **TYZ's genus period** `Q(n) = Σ_{t ∈ 2Cl_n} f_n(t)` (L566–568), for the test vector `f` and the
embedding `τ`: `t` is read in `B̂^×` as `τ̂` of a finite idele in the class `t`. -/
def genusPeriodTV (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (f : ℍ[AQ] → ℤ) : ℤ :=
  ∑ t ∈ sqClasses n, f ((tauHatU n τ (clLift n t) : ℍ[AQ]ˣ) : ℍ[AQ])

/-! ### The printed leaves -/

/-- **TYZ §2.1, L527–534 (existence of `τ`)**: for squarefree `n ≡ 1, 3 (mod 8)` there is an
embedding `τ : K_n → B` with `τ(O_{K_n}) ⊂ O_B` and, for `n ≡ 1 (mod 8)`, `τ(√−n) = ai + bj + ck`,
`n = a² + b² + c²`, `4 ∣ c`. TYZ cite Legendre's three-square theorem and Jones–Pall [JP, Theorem 5]
for the `4 ∣ c` refinement. -/
def TYZTauExists : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∃ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ

/-- **TYZ §2.1, L542–550, with Theorem 2.6 at `χ = 1`**: `π_ℤ^{U_n}` is free of rank one over `ℤ`;
here only the existence of a generator `f_n` (a consequence) is stated. -/
def TYZTestVectorExists : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∃ f : ℍ[AQ] → ℤ, IsTestVector n τ f

/-- **TYZ Lemma 2.9 (L1062–1066), printed form, for squarefree `1 < n ≡ 1, 3 (mod 8)`**: for every
admissible `τ` and test vector `f_n`, `Σ ε(d₁, d₂)𝓛(d₁)𝓛(d₂) = Q(n)` with `ε = ±1`, over the
non-ordered decompositions `n = d₁d₂`, `d₁, d₂ > 0`, `d₂ ≡ 1 (mod 8)`, with the factor `w = w_K` at
`n = 3` admitted (`Lemma29At`; rv-nt-tyz B1, rechecked against TYZ's proof by this task). -/
def TYZLemma29Printed : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → 1 < n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVector n τ f →
      Lemma29At n (genusPeriodTV n τ f)

/-- **TYZ Proposition 2.3 (L580–586), first assertion, for squarefree `n ≡ 1, 3 (mod 8)`**:
`f_n((B̂^×)²) ⊂ 1 + 2ℤ`. -/
def TYZProp23Printed : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVector n τ f →
      ∀ h : ℍ[AQ]ˣ, Odd (f ((h * h : ℍ[AQ]ˣ) : ℍ[AQ]))

/-! ### Glue (proved) -/

theorem tauHatU_coe (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ])
    (x : (FiniteAdeleRing (𝓞 (QNeg n)) (QNeg n))ˣ) :
    ((tauHatU n τ x : ℍ[AQ]ˣ) : ℍ[AQ]) = tauHat n τ x := rfl

theorem tauHatU_unitEmbedding (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (k : (QNeg n)ˣ) :
    ((tauHatU n τ (FiniteAdeleRing.unitEmbedding (𝓞 (QNeg n)) (QNeg n) k) : ℍ[AQ]ˣ) : ℍ[AQ]) =
      qι (τ k) := by
  rw [tauHatU_coe, FiniteAdeleRing.unitEmbedding_apply, tauHat_algebraMap]

/-- `τ̂(Ô_{K_n}^×) ⊂ R̂_n^× ⊂ U_n`. -/
theorem tauHatU_mem_Un (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ])
    {a : (FiniteAdeleRing (𝓞 (QNeg n)) (QNeg n))ˣ}
    (ha : a ∈ FiniteAdeleRing.integralUnits (𝓞 (QNeg n)) (QNeg n)) : tauHatU n τ a ∈ Un n τ := by
  apply Subgroup.subset_closure
  left
  rw [FiniteAdeleRing.integralUnits_eq_units_integralAdeles, Submonoid.mem_units_iff] at ha
  refine ⟨AddSubgroup.subset_closure (Or.inl ⟨_, ha.1, rfl⟩), ?_⟩
  rw [← map_inv]
  exact AddSubgroup.subset_closure (Or.inl ⟨_, ha.2, rfl⟩)

/-- **The class-group step of Proposition 2.3's "therefore"**: a test-vector-type `f` that is odd on
squares of `B̂^×` is odd at every class of `2Cl_n` (read through `τ̂`). Uses that the kernel of
`K̂^× → Cl_n` is `Ô_K^× K^×` (Tau Ceti's `ker_toClassGroup`). -/
theorem odd_on_sqClasses {n : ℕ} [NeZero n] {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} {f : ℍ[AQ] → ℤ}
    (hf : InPiZ n τ f) (h23 : ∀ h : ℍ[AQ]ˣ, Odd (f ((h * h : ℍ[AQ]ˣ) : ℍ[AQ])))
    {t : ClassGroup (𝓞 (QNeg n))} (ht : t ∈ sqClasses n) :
    Odd (f ((tauHatU n τ (clLift n t) : ℍ[AQ]ˣ) : ℍ[AQ])) := by
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp (mem_sqClasses.mp ht)
  have hker : clLift n t * (clLift n s * clLift n s)⁻¹ ∈
      (FiniteAdeleRing.toClassGroup (𝓞 (QNeg n)) (QNeg n)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, toClassGroup_clLift, toClassGroup_clLift,
      ← hs, powMonoidHom_apply, pow_two, mul_inv_cancel]
  rw [FiniteAdeleRing.ker_toClassGroup, Subgroup.mem_sup] at hker
  obtain ⟨a, ha, b, ⟨k, rfl⟩, hab⟩ := hker
  rw [eq_mul_inv_iff_mul_eq] at hab
  have hX : clLift n t = FiniteAdeleRing.unitEmbedding (𝓞 (QNeg n)) (QNeg n) k *
      ((clLift n s * clLift n s) * a) := by
    rw [← hab]; ac_rfl
  have himg : ((tauHatU n τ (clLift n t) : ℍ[AQ]ˣ) : ℍ[AQ]) =
      qι (τ k) * (((tauHatU n τ (clLift n s) * tauHatU n τ (clLift n s)) * tauHatU n τ a :
        ℍ[AQ]ˣ) : ℍ[AQ]) := by
    rw [hX, map_mul, Units.val_mul, tauHatU_unitEmbedding, map_mul, map_mul]
  have hγ : τ (k : QNeg n) ≠ 0 := (map_ne_zero τ).mpr k.ne_zero
  rw [himg, hf.1 _ hγ, Units.val_mul, hf.2.1 _ _ (tauHatU_mem_Un n τ ha)]
  exact h23 _

open Classical in
/-- The class-group function of the chosen `τ` and `f_n` (any value off the classes `1, 3 (mod 8)`). -/
def tvFun (hτ : TYZTauExists) (hfx : TYZTestVectorExists) : ClFun := fun n _ t =>
  if h : Squarefree n ∧ (n % 8 = 1 ∨ n % 8 = 3) then
    (hfx n h.1 h.2 _ (hτ n h.1 h.2).choose_spec).choose
      ((tauHatU n (hτ n h.1 h.2).choose (clLift n t) : ℍ[AQ]ˣ) : ℍ[AQ])
  else 1

/-- **`h29` from the printed leaves**: TYZ Lemma 2.9 and Proposition 2.3 in printed form over TYZ's
genuine `B̂`, `U_n`, `π_ℤ^{U_n}`, `f_n`, `Q(n)`, with the existence of `τ` and of `f_n`, give
`TYZLemma29Mod2`. -/
theorem tyzLemma29Mod2_of_printedLeaves (hτ : TYZTauExists) (hfx : TYZTestVectorExists)
    (h29 : TYZLemma29Printed) (h23 : TYZProp23Printed) : TYZLemma29Mod2 := by
  refine tyzLemma29Mod2_of_printedF (f := tvFun hτ hfx) ?_ ?_
  · intro ℓ hℓ m hsq h1 hcl
    have : NeZero m := ⟨hsq.ne_zero⟩
    have hm : Squarefree m ∧ (m % 8 = 1 ∨ m % 8 = 3) := ⟨hsq, hcl⟩
    have key := h29 m hsq h1 hcl _ (hτ m hsq hcl).choose_spec _
      (hfx m hsq hcl _ (hτ m hsq hcl).choose_spec).choose_spec ℓ hℓ
    have hQ : genusPeriod (tvFun hτ hfx) m = genusPeriodTV m (hτ m hsq hcl).choose
        (hfx m hsq hcl _ (hτ m hsq hcl).choose_spec).choose := by
      rw [genusPeriod_of_ne]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [tvFun, dif_pos hm]
    rw [hQ]
    exact key
  · intro n _ hsq hcl t ht
    have hm : Squarefree n ∧ (n % 8 = 1 ∨ n % 8 = 3) := ⟨hsq, hcl⟩
    simp only [tvFun, dif_pos hm]
    have hf := (hfx n hsq hcl _ (hτ n hsq hcl).choose_spec).choose_spec
    exact odd_on_sqClasses hf.1 (h23 n hsq hcl _ (hτ n hsq hcl).choose_spec _ hf) ht

/-! ### `TYZTauExists` from the three-square theorem (glue: the explicit `τ`, `√−n ↦ ai + bj + ck`,
and `τ(O_{K_n}) ⊂ O_B` from the trace and norm of integral elements) -/

/-- **Legendre's three-square theorem, with the refinement TYZ cite at L533** (Jones–Pall, *Regular and
semi-regular positive ternary quadratic forms*, Acta Math. 70 (1939) 165–191, Theorem 5, as cited by TYZ,
bib L3290–3292; that theorem's wording UNVERIFIED): a squarefree `n ≡ 1, 3 (mod 8)` is `a² + b² + c²` with
`a, b, c ∈ ℤ`, and with `4 ∣ c` when `n ≡ 1 (mod 8)`. (Legendre: `n` is a sum of three squares iff it is not
`4^e(8m + 7)`; this is all the case `n ≡ 3 (mod 8)` uses, and there `a, b, c` are odd, which the glue
proves.) -/
def LegendreJonesPall : Prop :=
  ∀ n : ℕ, Squarefree n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∃ a b c : ℤ, (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 ∧ (n % 8 = 1 → 4 ∣ c)

/-- The pure quaternion `ai + bj + ck`. -/
def pq (a b c : ℤ) : ℍ[ℚ] := ⟨0, a, b, c⟩

theorem pq_mul_self {n : ℕ} {a b c : ℤ} (h : (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2) :
    pq a b c * pq a b c = (-(n : ℚ)) • (1 : ℍ[ℚ]) + (0 : ℚ) • pq a b c := by
  have hq : (n : ℚ) = (a : ℚ) ^ 2 + (b : ℚ) ^ 2 + (c : ℚ) ^ 2 := by exact_mod_cast h
  apply Quaternion.ext <;>
    simp [pq, hq] <;> ring

/-- `τ : K_n → B`, `√−n ↦ ai + bj + ck`. -/
def tauOf (n : ℕ) {a b c : ℤ} (h : (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2) : QNeg n →ₐ[ℚ] ℍ[ℚ] :=
  QuadraticAlgebra.lift ⟨pq a b c, pq_mul_self h⟩

theorem tauOf_apply (n : ℕ) {a b c : ℤ} (h : (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2) (x : QNeg n) :
    tauOf n h x = ⟨x.re, x.im * a, x.im * b, x.im * c⟩ := by
  rw [tauOf, QuadraticAlgebra.lift_apply_apply]
  apply Quaternion.ext <;> simp [pq, Algebra.smul_def]

/-- Integral elements of `ℚ(√−n)` have integral trace and norm. -/
theorem trace_norm_int {n : ℕ} [NeZero n] (x : 𝓞 (QNeg n)) :
    (∃ m : ℤ, (m : ℚ) = 2 * (x : QNeg n).re) ∧
      ∃ N : ℤ, (N : ℚ) = (x : QNeg n).re ^ 2 + n * (x : QNeg n).im ^ 2 := by
  have hx : IsIntegral ℤ (x : QNeg n) := x.2
  have hs : IsIntegral ℤ (star (x : QNeg n)) :=
    hx.map ((starRingEnd (QNeg n)).toIntAlgHom)
  have h1 : (x : QNeg n) + star (x : QNeg n) = algebraMap ℚ (QNeg n) (2 * (x : QNeg n).re) := by
    rw [QuadraticAlgebra.algebraMap_eq]
    ext <;> simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star, QuadraticAlgebra.re_C, QuadraticAlgebra.im_C] <;> ring
  have h2 : (x : QNeg n) * star (x : QNeg n) =
      algebraMap ℚ (QNeg n) ((x : QNeg n).re ^ 2 + n * (x : QNeg n).im ^ 2) := by
    rw [QuadraticAlgebra.algebraMap_eq]
    ext <;> simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star, QuadraticAlgebra.re_C, QuadraticAlgebra.im_C] <;> ring
  have i1 : IsIntegral ℤ (2 * (x : QNeg n).re) := by
    have := hx.add hs
    rw [h1] at this
    exact isIntegral_algebraMap_iff.mp this
  have i2 : IsIntegral ℤ ((x : QNeg n).re ^ 2 + n * (x : QNeg n).im ^ 2) := by
    have := hx.mul hs
    rw [h2] at this
    exact isIntegral_algebraMap_iff.mp this
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp i1
  obtain ⟨N, hN⟩ := IsIntegrallyClosed.isIntegral_iff.mp i2
  exact ⟨⟨m, by simpa using hm⟩, ⟨N, by simpa using hN⟩⟩

/-- `n w² ∈ ℤ` with `n` squarefree forces `w ∈ ℤ`. -/
theorem int_of_sqfree_mul_sq {n : ℕ} (hn : Squarefree n) {w : ℚ} {k : ℤ}
    (h : (n : ℚ) * w ^ 2 = k) : ∃ z : ℤ, (z : ℚ) = w := by
  have hden : (w.den : ℚ) ≠ 0 := by exact_mod_cast w.den_nz
  have hw : w = w.num / w.den := (Rat.num_div_den w).symm
  have key : (n : ℤ) * w.num ^ 2 = k * (w.den : ℤ) ^ 2 := by
    have : (n : ℚ) * (w.num : ℚ) ^ 2 = k * (w.den : ℚ) ^ 2 := by
      rw [hw] at h
      field_simp at h
      linarith
    exact_mod_cast this
  have hcop : IsCoprime ((w.den : ℤ) ^ 2) (w.num ^ 2) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact w.reduced
  have hd : (w.den : ℤ) ^ 2 ∣ (n : ℤ) * w.num ^ 2 := ⟨k, by rw [key]; ring⟩
  have hd2 : (w.den : ℤ) ^ 2 ∣ (n : ℤ) := hcop.dvd_of_dvd_mul_right hd
  have hd3 : w.den * w.den ∣ n := by
    have : ((w.den * w.den : ℕ) : ℤ) ∣ (n : ℤ) := by push_cast; rwa [← sq]
    exact_mod_cast this
  have h1 : w.den = 1 := Nat.isUnit_iff.mp (hn _ hd3)
  exact ⟨w.num, by rw [hw, h1]; simp⟩

theorem parity_one {m V N k : ℤ} (h : 4 * N = m ^ 2 + (8 * k + 1) * V ^ 2) :
    (∃ s, m = 2 * s) ∧ ∃ t, V = 2 * t := by
  rcases Int.even_or_odd' m with ⟨s, rfl | rfl⟩ <;> rcases Int.even_or_odd' V with ⟨t, rfl | rfl⟩
  · exact ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩
  all_goals (exfalso; ring_nf at h; omega)

theorem parity_three {m V N k : ℤ} (h : 4 * N = m ^ 2 + (8 * k + 3) * V ^ 2) :
    ((∃ s, m = 2 * s) ∧ ∃ t, V = 2 * t) ∨ ((∃ s, m = 2 * s + 1) ∧ ∃ t, V = 2 * t + 1) := by
  rcases Int.even_or_odd' m with ⟨s, rfl | rfl⟩ <;> rcases Int.even_or_odd' V with ⟨t, rfl | rfl⟩
  · exact Or.inl ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩
  · exfalso; ring_nf at h; omega
  · exfalso; ring_nf at h; omega
  · exact Or.inr ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩

theorem odd_of_three {a b c k : ℤ} (h : 8 * k + 3 = a ^ 2 + b ^ 2 + c ^ 2) :
    (∃ a', a = 2 * a' + 1) ∧ (∃ b', b = 2 * b' + 1) ∧ ∃ c', c = 2 * c' + 1 := by
  rcases Int.even_or_odd' a with ⟨a', rfl | rfl⟩ <;> rcases Int.even_or_odd' b with ⟨b', rfl | rfl⟩ <;>
    rcases Int.even_or_odd' c with ⟨c', rfl | rfl⟩
  all_goals first
    | exact ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩
    | (exfalso; ring_nf at h; omega)

/-- **Glue: the explicit `τ` is admissible.** -/
theorem admissible_tauOf {n : ℕ} [NeZero n] (hsq : Squarefree n) (hcl : n % 8 = 1 ∨ n % 8 = 3)
    {a b c : ℤ} (h : (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2) (h4 : n % 8 = 1 → 4 ∣ c) :
    AdmissibleTau n (tauOf n h) := by
  refine ⟨fun x => ?_, fun hn => ⟨a, b, c, h, h4 hn, ?_⟩⟩
  · obtain ⟨⟨m, hm⟩, ⟨N, hN⟩⟩ := trace_norm_int x
    set u := (x : QNeg n).re with hu
    set v := (x : QNeg n).im with hv
    have hV : (n : ℚ) * (2 * v) ^ 2 = ((4 * N - m ^ 2 : ℤ) : ℚ) := by
      push_cast; rw [hN, hm]; ring
    obtain ⟨V, hVv⟩ := int_of_sqfree_mul_sq hsq hV
    have hEq : 4 * N = m ^ 2 + (n : ℤ) * V ^ 2 := by
      have : ((4 * N : ℤ) : ℚ) = ((m ^ 2 + (n : ℤ) * V ^ 2 : ℤ) : ℚ) := by
        push_cast; rw [hN, hm, hVv]; ring
      exact_mod_cast this
    have hk : (n : ℤ) = 8 * ((n / 8 : ℕ) : ℤ) + ((n % 8 : ℕ) : ℤ) := by
      exact_mod_cast (Nat.div_add_mod n 8).symm
    rw [tauOf_apply]
    have hev : (∃ s, m = 2 * s) ∧ (∃ t, V = 2 * t) → IsHurwitz ⟨u, v * a, v * b, v * c⟩ := by
      rintro ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩
      have hus : u = s := by push_cast at hm; linarith
      have hvt : v = t := by push_cast at hVv; linarith
      refine ⟨s, t * a, t * b, t * c, 0, ?_⟩
      apply Quaternion.ext <;> simp [hus, hvt]
    rcases hcl with h1 | h3
    · rw [h1] at hk
      push_cast at hk
      rw [hk] at hEq
      exact hev (parity_one hEq)
    · rw [h3] at hk
      push_cast at hk
      rw [hk] at hEq
      rcases parity_three hEq with he | ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩
      · exact hev he
      · rw [hk] at h
        obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩ := odd_of_three h
        have hus : u = s + 1 / 2 := by push_cast at hm; linarith
        have hvt : v = t + 1 / 2 := by push_cast at hVv; linarith
        refine ⟨s + 1, 2 * t * a' + t + a', 2 * t * b' + t + b', 2 * t * c' + t + c', 1, ?_⟩
        have e1 : (x : QNeg n).re = s + 1 / 2 := hu ▸ hus
        have e2 : (x : QNeg n).im = t + 1 / 2 := hv ▸ hvt
        rw [e1, e2]
        apply Quaternion.ext <;> simp <;> ring
  · rw [tauOf_apply]
    apply Quaternion.ext <;> simp [sqrtNeg]

/-- **`TYZTauExists` from the three-square statement.** -/
theorem tyzTauExists_of_legendreJonesPall (h : LegendreJonesPall) : TYZTauExists := by
  intro n _ hsq hcl
  obtain ⟨a, b, c, habc, h4⟩ := h n hsq hcl
  exact ⟨tauOf n habc, admissible_tauOf hsq hcl habc h4⟩


/-- **`h29` from the printed leaves, with the existence of `τ` reduced to the three-square theorem.** -/
theorem tyzLemma29Mod2_of_printedLeaves_threeSquares (hL : LegendreJonesPall)
    (hfx : TYZTestVectorExists) (h29 : TYZLemma29Printed) (h23 : TYZProp23Printed) :
    TYZLemma29Mod2 :=
  tyzLemma29Mod2_of_printedLeaves (tyzTauExists_of_legendreJonesPall hL) hfx h29 h23

end Genuine

end ZInQ.Contrib.TYZDecomp.H29Split

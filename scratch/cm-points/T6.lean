import ZInQKernel.Contrib.TYZGenus.Package

noncomputable section
namespace ZInQ.Contrib.TYZGenus.Package
open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields ZInQ.RouteK.Rank5b ZInQ.PropN

/-- `ρ ∈ Gal(ℚ̄/ℚ)` acts on `H_{d,4} ⊂ ℚ̄` as the Artin symbol of `c ∈ Pic(𝒪_{d,4})`
(through ring-class's embedding `embed d : K_dˢ → ℚ̄` and Tau Ceti's `ringClassArtinEquiv`). -/
def ActsAsArtin4 (ρ : GalQ) (d : ℕ) [NeZero d] (c : Pic (O4 d)) : Prop :=
  ∀ x : H4 d, ρ (embed d (x : SeparableClosure (QNeg d))) =
    embed d ((artin4 d c x : H4 d) : SeparableClosure (QNeg d))

/-- **Leaf CM-2-TYZ (field of definition of TYZ's Heegner point)**: for squarefree `n ≡ 5 (mod 8)`,
`f₀(P_n)` (the Heegner point of `[16(n+1), −8, 1]`, discriminant `−64n`, order `𝒪_{n,4} = ℤ[4√−n]`)
is defined over the ring class field `H_{n,4}`. The instance `H(−64n) = H_{n,4}` of
`CM.CMFieldOfDefinition` (`cmFieldTYZ_of`). Sources: main theorem of complex multiplication /
Shimura reciprocity for `X₀(N)` (Shimura 1971 Thm. 5.4 and Ch. 6; Gross 1984 §3; UNVERIFIED
numbers); TYZ Proposition 3.2 (L1253–1260). Refereed. -/
def CMFieldOfDefinitionTYZ : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → tyzHeegnerPt n ∈ ptsOver (H4bar n)

theorem cmFieldTYZ_of {H : ℤ → IntermediateField ℚ Qbar} (h : CMFieldOfDefinition H)
    (hH : ∀ n : ℕ, n % 8 = 5 → Squarefree n → H (-64 * n) ≤ H4bar n) : CMFieldOfDefinitionTYZ := by
  intro n hn hsq
  have h1 := h (-64 * n) (tyzForm n hn)
  simp only [tyzHeegnerPt, hn, ↓reduceDIte]
  rw [mem_ptsOver_iff] at h1 ⊢
  revert h1
  rcases heegnerPt (tyzForm n hn) with _ | ⟨x, y, _⟩
  · intro _; trivial
  · intro h1; exact ⟨hH n hn hsq h1.1, hH n hn hsq h1.2⟩

/-- **Leaf TYZ-3.6 (Shimura reciprocity in TYZ's form, Corollary 3.9 / Theorem 3.6)**: `σ_{1+2ϖ}`
fixes `z_n = f_n(P_n)`: every `ρ` acting on `H_{n,4}` as the Artin symbol of
`sigmaClass n` fixes `z_n`. TYZ Corollary 3.9 (`π(1+2ϖ)f_n = f_n`) with Shimura reciprocity on
`P_n = [h, 1]` (rv-tyz-inputs §1.5, L1433–1683, re-derived there); refereed. Here `z_n` is
`CM.tyzZn n = (1 − [i]) f₀(P_n)` (the translation of TYZ's `f_n(P_n)` to `X₀(32)` of
`tyz-t1.md` §3.1, AI-derived and checked numerically there). -/
def TYZSigmaFixesZn : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 5 → Squarefree n →
    ∀ ρ : GalQ, ActsAsArtin4 ρ n (sigmaClass n) → galPt ρ (tyzZn n) = tyzZn n

/-- **Leaf TYZ-3.2 (the field of `z_n`)**: `z_n ∈ A(H'_n)`. Consequence of `CMFieldOfDefinitionTYZ`
(`z_n ∈ A(H_{n,4})`, since `i ∈ H_{n,4}`) and `TYZSigmaFixesZn` (`H'_n` is the fixed field of
`σ_{1+2ϖ}`, TYZ Proposition 3.2(1)); stated as one leaf (the Galois-theoretic deduction through
ring-class's embedding is not formalized). Refereed (TYZ L1253–1260, Theorem 3.6). -/
def TYZZnOverHprime : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → tyzZn n ∈ ptsOver (Hprimebar n)

theorem Lni_mono {e n : ℕ} (h : e ∣ n) (hn : n ≠ 0) : Lni e ≤ Lni n := by
  apply IntermediateField.adjoin.mono
  rintro x (hx | ⟨p, hp, hx⟩)
  · exact Or.inl hx
  · exact Or.inr ⟨p, Nat.primeFactors_mono h hn hp, hx⟩

theorem Lni_le_HHprime (n : ℕ) : Lni n ≤ HHprime n := le_sup_left

/-- **Glue: TYZ's class-5 genus points lie in `A(ℍ'_n)`**, for *every* choice of the finite set `Φ`
of automorphisms (TYZ's `Φ₀`), from `z_e ∈ A(H'_e)` and normality of `H'_e`. -/
theorem tyzGenusSum_mem (hz : TYZZnOverHprime) (hN : HprimeNormal) {n e : ℕ} (hsq : Squarefree n)
    (he : e ∈ n.divisors) (he5 : e % 8 = 5) (Φ : Finset GalQ) :
    genusSum Φ (tyzZn e) ∈ ptsOver (HHprime n) := by
  have hse : Squarefree e := hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)
  exact genusSum_mem_HHprime he he5 (hN e he5 hse) Φ (hz e he5 hse)

/-- **Glue for `GenusPtsDefined`**: if `Z` is TYZ's genus-point sum on class 5 (any `Φ e`) and
`Z(e) ∈ A(L_e)` on class 7 (TYZ L2558), then `GenusPtsDefined HHprime Z`. -/
theorem genusPtsDefined_of (hz : TYZZnOverHprime) (hN : HprimeNormal) (Φ : ℕ → Finset GalQ)
    (Z : ℕ → PtA) (h5 : ∀ e, e % 8 = 5 → Z e = genusSum (Φ e) (tyzZn e))
    (h7 : ∀ e, e % 8 = 7 → Squarefree e → Z e ∈ ptsOver (Lni e)) : GenusPtsDefined HHprime Z := by
  intro n hn hsq e he hec
  rcases hec with he5 | he7
  · rw [h5 e he5]; exact tyzGenusSum_mem hz hN hsq he he5 (Φ e)
  · have hn0 : n ≠ 0 := by omega
    have hse : Squarefree e := hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)
    have hle : Lni e ≤ HHprime n := (Lni_mono (Nat.dvd_of_mem_divisors he) hn0).trans (Lni_le_HHprime n)
    have := h7 e he7 hse
    rw [mem_ptsOver_iff] at this ⊢
    revert this
    rcases Z e with _ | ⟨x, y, _⟩
    · intro _; trivial
    · intro h; exact ⟨hle h.1, hle h.2⟩

/-- TYZ's genus points with the class-5 ones pinned by CM: `Z(e) = Σ_{t ∈ Φ e} t(z_e)` for
`e ≡ 5 (mod 8)` (TYZ L1318, `z_e = CM.tyzZn e`), and `Z7 e` otherwise (class 7: TYZ's `f_e(P_e)` for
`e ≡ 7` is not pinned here, see `docs/research/cm-points.md` §4). -/
def tyzGenusPt (Φ : ℕ → Finset GalQ) (Z7 : ℕ → PtA) (e : ℕ) : PtA :=
  if e % 8 = 5 then genusSum (Φ e) (tyzZn e) else Z7 e

/-- **The remaining bundled leaf, CM form**: for each squarefree `n ≡ 5 (mod 8)` there are a choice
`Φ` of TYZ's sets `Φ₀` (TYZ: any choice works, L2547–2554), class-7 genus points `Z7 e ∈ A(L_e)`
(TYZ L2558), `ε` and a lifting `β'` such that Theorem 3.3/3.5 (first assertion) and Lemma 3.21(1),
(4) hold for the genus points `tyzGenusPt Φ Z7`, whose class-5 values are pinned by the Heegner
points of `CM.lean`. Strictly finer than `GenusPointLeaf` (and than `TYZGenusPackage`). -/
def GenusPointLeafCM (ℓ : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∃ (Φ : ℕ → Finset GalQ) (Z7 : ℕ → PtA),
    (∀ e ∈ n.divisors, e % 8 = 7 → Z7 e ∈ ptsOver (Lni e)) ∧
    (∃ ε : ℕ → ℕ → GaussianInt, EpsClasses n ε ∧
      (ℓ n = 0 → IsOfFinAddOrder (Pseq ℓ ε (tyzGenusPt Φ Z7) n))) ∧
    (∃ σ : GalQ, IsBetaOneLift σ ∧
      (∀ e ∈ n.divisors, e % 8 = 5 → ∃ k : ℤ,
        galPt σ (tyzGenusPt Φ Z7 e) + tyzGenusPt Φ Z7 e = (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2) ∧
      (∀ e ∈ n.divisors, e % 8 = 7 →
        galPt σ (tyzGenusPt Φ Z7 e) + tyzGenusPt Φ Z7 e = (gNat e : ℤ) • tauG 1))

open ZInQ.Contrib.TYZDecomp in
/-- **Glue, CM form**: `z_e ∈ A(H'_e)`, normality of the `H'_d`, Lemma 3.18 for `ℍ'_n` and the CM-form
bundled leaf give `TYZGenusPackage`. -/
theorem genusPackage_of_cm (hz : TYZZnOverHprime) (hN : HprimeNormal) (h318 : Lemma318 HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : TYZGenusPackage := by
  refine genusPackage_of_genusPointLeaf HHprime iContained_HHprime (normalFields_HHprime hN) h318
    fun ℓ hℓ n hn hsq => ?_
  obtain ⟨Φ, Z7, h7, hP, hβ⟩ := hG ℓ hℓ n hn hsq
  refine ⟨tyzGenusPt Φ Z7, fun e he hec => ?_, hP, hβ⟩
  rcases hec with he5 | he7
  · simp only [tyzGenusPt, he5, ↓reduceIte]
    exact tyzGenusSum_mem hz hN hsq he he5 (Φ e)
  · have hn0 : n ≠ 0 := by omega
    have hle : Lni e ≤ HHprime n :=
      (Lni_mono (Nat.dvd_of_mem_divisors he) hn0).trans (Lni_le_HHprime n)
    have h75 : ¬ e % 8 = 5 := by omega
    simp only [tyzGenusPt, h75, ↓reduceIte]
    have := h7 e he he7
    rw [mem_ptsOver_iff] at this ⊢
    revert this
    rcases Z7 e with _ | ⟨x, y, _⟩
    · intro _; trivial
    · intro h; exact ⟨hle h.1, hle h.2⟩

open ZInQ.Contrib.TYZDecomp in
/-- **The premise `TYZThm35ReadingA` from the CM-form leaves.** -/
theorem tyzThm35ReadingA_of_cm (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hz : TYZZnOverHprime) (hN : HprimeNormal) (h318 : Lemma318 HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_leaves h11 h1 h29 (genusPackage_of_cm hz hN h318 hG)

end ZInQ.Contrib.TYZGenus.Package

#print axioms ZInQ.Contrib.TYZGenus.Package.tyzThm35ReadingA_of_cm

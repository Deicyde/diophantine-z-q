import ZInQKernel.OneProof.TYZSplit

/-!
# h33-sign: the sign of `[i]` in the leaf `TYZSplit.TYZThm33` (TYZ Theorem 3.3)

Task h33-sign (2026-11-15). Report: `docs/research/h33-sign.md`; log: `scratch/h33-sign/log.md`.

The leaf `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` is stated over the kernel's CM point
`TYZ35.basePt n`, which for `n ≡ 5 (mod 8)` is `tyzZn n = P − [i]P`, `P = f₀(P_n)` the Heegner point of
`[16(n+1), −8, 1]` and `[i] (x, y) = (−x, i y)` with `ιC i = I`. TYZ print `f_n = f₀ − f₀∘[i]` (L1198)
with `[i]` an automorphism of `X_U ≅ X₀(32)_{ℚ(i)}` whose normalization (which square root of `−1`
of `Γ(X_U, 𝒪) = ℚ(i)` is called `i`) is not printed at L1192. So TYZ's `z_n` is one of
`±(P − [i]P)`, `±(P + [i]P)` (the `±` from the identification `i₀`, L1174).

* §1 a verbatim copy of the leaf (`TYZThm33Copy`, `Iff.rfl` with the kernel's) and the same
  statement over an arbitrary family of CM points `z` (`TYZThm33With z`; the kernel's leaf is
  `TYZThm33With TYZ35.basePt`, again `Iff.rfl`).
* §2 the other reading `zAlt n = P + [i]P = [i](tyzZn n)`: its complex conjugate is `zAlt n − τ(1)`
  (`conj_zAlt`, from the kernel's proved `heegnerPt_tyzForm_conj`: Fricke involution and
  `τ ↦ τ + 1/4` on the eta model), so it satisfies TYZ's printed Theorem 3.6(1) `z̄_n = −z_n + τ(1)`
  (L1413) only if `P` is torsion (`torsion_of_alt_thm36`). The kernel's `tyzZn` satisfies it
  (`T321.tyzThm36ConjFive_of`, kernel).
* §3 `TYZThm33With z` only depends on `z` up to a sign at each `n` and up to "both torsion"
  (`tyzThm33With_imp`).
* §4 **main theorem** `tyzThm33With_iff_of_reading`: for every family `zT` of the shape TYZ define
  (`±(P ∓ [i]P)` for `n ≡ 5`, `±f₀(P_n)` for `n ≡ 7`) that satisfies TYZ's printed Theorem 3.6(1),
  conjugation part, `TYZThm33With zT ↔ TYZThm33`. So the leaf is TYZ's Theorem 3.3 for TYZ's own
  `z_n`, whichever way L1192–1198 is read: the sign is pinned by TYZ's Theorem 3.6(1).

Hypothesis used: the kernel leaf `CM.CMAlgebraic` (Heegner points of level 32 are algebraic).
No `sorry`, no `axiom`.
-/

noncomputable section

set_option maxRecDepth 8000

namespace ZInQ.Contrib.TYZGenus.H33Sign

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
  ZInQ.Contrib.TYZGenus.RingClass ZInQ.PropN NumberField TauCeti.ClassFieldTheory
  TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder ZInQ.RouteK.Rank5b
  ZInQ.Contrib.TYZGenus.CMBridge ZInQ.Contrib.TYZGenus.TYZ35 ZInQ.Contrib.TYZDecomp
  ZInQ.RouteK.Redei ZInQ.Literature ZInQ.Contrib.TYZGenus.TYZSplit

/-! ## §1. The leaf, verbatim, and over an arbitrary family of CM points -/

/-- Verbatim copy of `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` (ZInQKernel/OneProof/TYZSplit.lean
L157–176; docstring there). -/
def TYZThm33Copy : Prop :=
  ∀ ℓ : ℕ → ℤ, (∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℂ)) ^ 2 = lcalSq m) →
  ∃ (Q : ℕ → PtA) (m : ℕ → ℕ) (ε : ℕ → ℕ → GaussianInt),
    (∀ d, 0 < m d) ∧ (∀ d, InMinus d (Q d)) ∧ EpsTYZ ε ∧
    (∀ d : ℕ, Squarefree d → (d % 8 = 5 ∨ d % 8 = 6 ∨ d % 8 = 7) →
      (¬ ∃ F : ℂ → ℂ, IsLContinuation (curveC d) F ∧ analyticOrderAt F 1 ≤ 1) →
        IsOfFinAddOrder (Q d)) ∧
    ∀ n : ℕ, ∀ _ : NeZero n, Squarefree n → (n % 8 = 5 ∨ n % 8 = 7) →
      ∀ φ : ClG n → GalQ, IsPhi n φ → ∀ χ : ClG n →* ℤˣ,
        (¬ IsOfFinAddOrder (PchiG n φ χ) →
          ∃ d₀ d₁ : ℕ, d₀ * d₁ = n ∧ (d₀ % 8 = 5 ∨ d₀ % 8 = 6 ∨ d₀ % 8 = 7) ∧
            (d₁ % 8 = 1 ∨ d₁ % 8 = 2 ∨ d₁ % 8 = 3) ∧ IsChiPair n d₁ χ) ∧
        ∀ d₀ d₁ : ℕ, d₀ * d₁ = n → (d₀ % 8 = 5 ∨ d₀ % 8 = 6 ∨ d₀ % 8 = 7) →
          (d₁ % 8 = 1 ∨ d₁ % 8 = 2 ∨ d₁ % 8 = 3) → IsChiPair n d₁ χ →
          IsOfFinAddOrder ((m d₀ : GaussianInt) • PchiG n φ χ -
            (ε d₀ d₁ * 2 ^ h2G n * (ℓ d₁ : GaussianInt)) • Q d₀)

theorem tyzThm33Copy_iff : TYZThm33Copy ↔ TYZThm33 := Iff.rfl

/-- `P_χ` over an arbitrary family `z` of CM points (`PchiG` is `PchiGWith basePt`). -/
def PchiGWith (z : ℕ → PtA) (n : ℕ) [NeZero n] (φ : ClG n → GalQ) (χ : ClG n →* ℤˣ) : PtA :=
  ∑ t : ClG n, ((χ t : ℤˣ) : ℤ) • galPt (φ t) (z n)

/-- `TYZThm33` with `basePt` replaced by an arbitrary family `z` (otherwise verbatim). -/
def TYZThm33With (z : ℕ → PtA) : Prop :=
  ∀ ℓ : ℕ → ℤ, (∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℂ)) ^ 2 = lcalSq m) →
  ∃ (Q : ℕ → PtA) (m : ℕ → ℕ) (ε : ℕ → ℕ → GaussianInt),
    (∀ d, 0 < m d) ∧ (∀ d, InMinus d (Q d)) ∧ EpsTYZ ε ∧
    (∀ d : ℕ, Squarefree d → (d % 8 = 5 ∨ d % 8 = 6 ∨ d % 8 = 7) →
      (¬ ∃ F : ℂ → ℂ, IsLContinuation (curveC d) F ∧ analyticOrderAt F 1 ≤ 1) →
        IsOfFinAddOrder (Q d)) ∧
    ∀ n : ℕ, ∀ _ : NeZero n, Squarefree n → (n % 8 = 5 ∨ n % 8 = 7) →
      ∀ φ : ClG n → GalQ, IsPhi n φ → ∀ χ : ClG n →* ℤˣ,
        (¬ IsOfFinAddOrder (PchiGWith z n φ χ) →
          ∃ d₀ d₁ : ℕ, d₀ * d₁ = n ∧ (d₀ % 8 = 5 ∨ d₀ % 8 = 6 ∨ d₀ % 8 = 7) ∧
            (d₁ % 8 = 1 ∨ d₁ % 8 = 2 ∨ d₁ % 8 = 3) ∧ IsChiPair n d₁ χ) ∧
        ∀ d₀ d₁ : ℕ, d₀ * d₁ = n → (d₀ % 8 = 5 ∨ d₀ % 8 = 6 ∨ d₀ % 8 = 7) →
          (d₁ % 8 = 1 ∨ d₁ % 8 = 2 ∨ d₁ % 8 = 3) → IsChiPair n d₁ χ →
          IsOfFinAddOrder ((m d₀ : GaussianInt) • PchiGWith z n φ χ -
            (ε d₀ d₁ * 2 ^ h2G n * (ℓ d₁ : GaussianInt)) • Q d₀)

theorem tyzThm33_iff_with : TYZThm33 ↔ TYZThm33With basePt := Iff.rfl

/-! ## §2. The other reading of `[i]` fails TYZ's Theorem 3.6(1) -/

/-- An additive endomorphism maps torsion points to torsion points. -/
theorem tors_map (f : PtA →+ PtA) {P : PtA} (h : IsOfFinAddOrder P) : IsOfFinAddOrder (f P) := by
  obtain ⟨k, hk, hkP⟩ := h.exists_nsmul_eq_zero
  exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨k, hk, by rw [← map_nsmul, hkP, map_zero]⟩

theorem tors_neg {P : PtA} (h : IsOfFinAddOrder P) : IsOfFinAddOrder (-P) :=
  isOfFinAddOrder_neg_iff.mpr h

theorem tors_sub {P R : PtA} (h : IsOfFinAddOrder P) (h' : IsOfFinAddOrder R) :
    IsOfFinAddOrder (P - R) := by
  rw [sub_eq_add_neg]; exact h.add (tors_neg h')

/-- **The other reading of TYZ's `f_n = f₀ − f₀∘[i]`** (L1198) for `n ≡ 5 (mod 8)`: `[i]` acting as
complex multiplication by `−I` on the component of `P_n`, i.e. `z = P − [−i]P = P + [i]P`
(`P = f₀(P_n)`, the kernel's `tyzHeegnerPt n`). -/
def zAlt (n : ℕ) : PtA := tyzHeegnerPt n + iPt (tyzHeegnerPt n)

/-- `P + [i]P = [i](P − [i]P)`: the two readings differ by the unit `i` (not by `±1`). -/
theorem zAlt_eq_iPt (n : ℕ) : zAlt n = iPt (tyzZn n) := by
  simp only [zAlt, tyzZn, T321.iPt_sub, iPt_iPt]
  abel

/-- **Normalization of the kernel's `[i]`**: on `A(ℂ)` it is `(x, y) ↦ (−x, I·y)` (`ιC i = I`), which
pulls the invariant differential `dx/2y` back to `I·dx/2y`; so it is complex multiplication by `+I` in
the normalized sense `[α]^*ω = αω`, i.e. `τ(Iu) = [i]τ(u)` for TYZ's `ℂ`-linear uniformization `τ`
(L1381–1385). Pointwise form: if `(x(t), y(t))` is a path with `y ≠ 0`, then
`(−x)'/(2·(I·y)) = I·(x'/(2y))`. -/
theorem iPt_pullback_differential (x' y : ℂ) (hy : y ≠ 0) :
    (-x') / (2 * (Complex.I * y)) = Complex.I * (x' / (2 * y)) := by
  field_simp
  rw [Complex.I_sq]
  ring

/-- `τ(1) = tauG 2 = (0, 0)`. -/
theorem tauG_two : tauG 2 = pt00 := by
  rw [← one_add_one_eq_two, map_add, tauG_apply, one_smul, ptT_add_self]

theorem iPt_tauG_two : iPt (tauG 2) = tauG 2 := by rw [tauG_two, iPt_pt00]

theorem tauG_two_add_self : tauG 2 + tauG 2 = 0 := by rw [tauG_two, pt00_add_self]

/-- **Complex conjugation on the other reading**: `c(P + [i]P) = (P + [i]P) − τ(1)`; compare TYZ
Theorem 3.6(1) (L1413), `z̄_n = −z_n + τ(1)`, which the kernel's `tyzZn` satisfies
(`T321.tyzThm36ConjFive_of`). -/
theorem conj_zAlt (hA : CMAlgebraic) {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) {γ : GalQ}
    (hγ : IsComplexConj γ) : galPt γ (zAlt n) = zAlt n - tauG 2 := by
  have h := T321.tyzThm36ConjFive_of hA n hn hsq γ hγ
  have hi := T321.isComplexConj_apply_iQ hγ
  rw [zAlt_eq_iPt, T321.galPt_iPt_of_neg hi, h, T321.iPt_sub, iPt_tauG_two]
  abel

/-- The kernel's reading satisfies TYZ Theorem 3.6(1), conjugation part (kernel theorem, restated). -/
theorem conj_tyzZn (hA : CMAlgebraic) {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) {γ : GalQ}
    (hγ : IsComplexConj γ) : galPt γ (tyzZn n) = tauG 2 - tyzZn n :=
  T321.tyzThm36ConjFive_of hA n hn hsq γ hγ

/-- **If the other reading satisfied TYZ's Theorem 3.6(1), `f₀(P_n)` would be torsion.** -/
theorem torsion_of_alt_thm36 (hA : CMAlgebraic) {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n)
    {γ : GalQ} (hγ : IsComplexConj γ) (h : galPt γ (zAlt n) = tauG 2 - zAlt n) :
    IsOfFinAddOrder (tyzHeegnerPt n) := by
  rw [conj_zAlt hA hn hsq hγ] at h
  have e : zAlt n + zAlt n = 0 := by
    calc zAlt n + zAlt n = (zAlt n - tauG 2) + tauG 2 + zAlt n := by abel
      _ = (tauG 2 - zAlt n) + tauG 2 + zAlt n := by rw [h]
      _ = tauG 2 + tauG 2 := by abel
      _ = 0 := tauG_two_add_self
  have hz : IsOfFinAddOrder (zAlt n) :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2, by norm_num, by rw [two_nsmul]; exact e⟩
  have h2 : zAlt n - iPt (zAlt n) = 2 • tyzHeegnerPt n := by
    simp only [zAlt, iPt_add, iPt_iPt]
    rw [two_nsmul]
    abel
  have h2P : IsOfFinAddOrder (2 • tyzHeegnerPt n) := by
    rw [← h2]
    exact tors_sub hz (tors_map iHom hz)
  exact h2P.of_nsmul (by norm_num)

/-- If `f₀(P_n)` is torsion, so are both readings of `z_n`. -/
theorem torsion_readings {n : ℕ} (h : IsOfFinAddOrder (tyzHeegnerPt n)) :
    IsOfFinAddOrder (tyzZn n) ∧ IsOfFinAddOrder (zAlt n) :=
  ⟨tors_sub h (tors_map iHom h), h.add (tors_map iHom h)⟩

theorem gsmul_neg_left (c : GaussianInt) (P : PtA) : (-c) • P = -(c • P) := neg_smul c P

theorem gsmul_neg_right (c : GaussianInt) (P : PtA) : c • (-P) = -(c • P) := smul_neg c P

theorem gsmul_one (P : PtA) : (1 : GaussianInt) • P = P := one_smul GaussianInt P

theorem natCast_gsmul (k : ℕ) (P : PtA) : (k : GaussianInt) • P = k • P :=
  Nat.cast_smul_eq_nsmul GaussianInt k P

/-! ## §3. `TYZThm33With z` depends on `z n` only up to sign, or up to "both torsion" -/

theorem pchiGWith_congr {z z' : ℕ → PtA} {n : ℕ} [NeZero n] (h : z' n = z n)
    (φ : ClG n → GalQ) (χ : ClG n →* ℤˣ) : PchiGWith z' n φ χ = PchiGWith z n φ χ := by
  simp only [PchiGWith, h]

theorem pchiGWith_neg {z z' : ℕ → PtA} {n : ℕ} [NeZero n] (h : z' n = -z n)
    (φ : ClG n → GalQ) (χ : ClG n →* ℤˣ) : PchiGWith z' n φ χ = -PchiGWith z n φ χ := by
  simp only [PchiGWith, h, map_neg, zsmul_neg, Finset.sum_neg_distrib]

theorem pchiGWith_torsion {z : ℕ → PtA} {n : ℕ} [NeZero n] (h : IsOfFinAddOrder (z n))
    (φ : ClG n → GalQ) (χ : ClG n →* ℤˣ) : IsOfFinAddOrder (PchiGWith z n φ χ) := by
  unfold PchiGWith
  refine Finset.sum_induction _ IsOfFinAddOrder (fun a b ha hb => ha.add hb)
    IsOfFinAddOrder.zero (fun t _ => ?_)
  exact (tors_map (galPt (φ t)) h).zsmul

/-- **Transfer.** If at every squarefree `n ≡ 5, 7 (mod 8)` the points `z' n` and `z n` agree up to
sign, or are both torsion, then `TYZThm33With z → TYZThm33With z'`. (The sign is absorbed by `ε`:
`ε(d₀, d₁)` only occurs at `n = d₀d₁`, and `EpsTYZ` is invariant under `ε ↦ −ε`.) -/
theorem tyzThm33With_imp {z z' : ℕ → PtA}
    (hzz : ∀ n : ℕ, Squarefree n → (n % 8 = 5 ∨ n % 8 = 7) →
      z' n = z n ∨ z' n = -z n ∨ (IsOfFinAddOrder (z n) ∧ IsOfFinAddOrder (z' n)))
    (H : TYZThm33With z) : TYZThm33With z' := by
  classical
  intro ℓ hℓ
  obtain ⟨Q, m, ε, hm, hQ, hε, htors, hmain⟩ := H ℓ hℓ
  let s : ℕ → GaussianInt := fun n => if z' n = z n then 1 else -1
  have hs : ∀ n, s n = 1 ∨ s n = -1 := fun n => by
    by_cases h : z' n = z n
    · left; simp [s, h]
    · right; simp [s, h]
  refine ⟨Q, m, fun d₀ d₁ => s (d₀ * d₁) * ε d₀ d₁, hm, hQ, ?_, htors, ?_⟩
  · intro d₀ d₁ h0 h1
    dsimp only
    obtain ⟨e1, e2⟩ := hε d₀ d₁ h0 h1
    rcases hs (d₀ * d₁) with h | h <;> rw [h]
    · simp only [one_mul]; exact ⟨e1, e2⟩
    · refine ⟨fun c => ?_, fun c => ?_⟩
      · rcases e1 c with e | e <;> rw [e] <;> simp
      · rcases e2 c with e | e <;> rw [e] <;> simp
  · intro n hnz hsq hn8 φ hφ χ
    beta_reduce
    obtain ⟨H1, H2⟩ := hmain n hnz hsq hn8 φ hφ χ
    rcases hzz n hsq hn8 with e | e | ⟨tz, tz'⟩
    · -- same point
      have hsn : s n = 1 := by simp [s, e]
      rw [pchiGWith_congr e]
      refine ⟨H1, fun d₀ d₁ hd h0 h1 hc => ?_⟩
      rw [hd, hsn, one_mul]
      exact H2 d₀ d₁ hd h0 h1 hc
    · -- opposite point
      rw [pchiGWith_neg e]
      refine ⟨fun hnt => H1 (fun ht => hnt (tors_neg ht)), fun d₀ d₁ hd h0 h1 hc => ?_⟩
      have key := (H2 d₀ d₁ hd h0 h1 hc)
      rcases hs n with hsn | hsn
      · -- `z' n = z n` and `z' n = −z n`: then `z n` is 2-torsion-free-irrelevant; `P_χ = −P_χ`
        have ezz : z' n = z n := by
          by_contra hne
          simp only [s, hne, ite_false] at hsn
          have := congrArg Zsqrtd.re hsn
          norm_num at this
        have hP : PchiGWith z n φ χ = -PchiGWith z n φ χ := by
          rw [← pchiGWith_neg e, pchiGWith_congr ezz]
        rw [hd, hsn, one_mul, ← hP]
        exact key
      · rw [hd, hsn]
        have : (m d₀ : GaussianInt) • -PchiGWith z n φ χ -
            (-1 * ε d₀ d₁ * 2 ^ h2G n * (ℓ d₁ : GaussianInt)) • Q d₀ =
            -((m d₀ : GaussianInt) • PchiGWith z n φ χ -
              (ε d₀ d₁ * 2 ^ h2G n * (ℓ d₁ : GaussianInt)) • Q d₀) := by
          rw [gsmul_neg_right, show (-1 * ε d₀ d₁ * 2 ^ h2G n * (ℓ d₁ : GaussianInt)) =
            -(ε d₀ d₁ * 2 ^ h2G n * (ℓ d₁ : GaussianInt)) by ring, gsmul_neg_left]
          abel
        rw [this]
        exact tors_neg key
    · -- both torsion
      have tP := pchiGWith_torsion tz φ χ
      have tP' := pchiGWith_torsion tz' φ χ
      refine ⟨fun hnt => absurd tP' hnt, fun d₀ d₁ hd h0 h1 hc => ?_⟩
      have key := H2 d₀ d₁ hd h0 h1 hc
      have tmP : IsOfFinAddOrder ((m d₀ : GaussianInt) • PchiGWith z n φ χ) := by
        rw [natCast_gsmul]
        exact tP.nsmul
      have tmP' : IsOfFinAddOrder ((m d₀ : GaussianInt) • PchiGWith z' n φ χ) := by
        rw [natCast_gsmul]
        exact tP'.nsmul
      have tQ : IsOfFinAddOrder ((ε d₀ d₁ * 2 ^ h2G n * (ℓ d₁ : GaussianInt)) • Q d₀) := by
        have := tors_sub tmP key
        rwa [sub_sub_cancel] at this
      rw [hd, mul_assoc, mul_assoc, mul_smul, ← mul_assoc]
      refine tors_sub tmP' ?_
      rcases hs n with hsn | hsn <;> rw [hsn]
      · rw [gsmul_one]; exact tQ
      · rw [gsmul_neg_left, gsmul_one]; exact tors_neg tQ

theorem tyzThm33With_iff {z z' : ℕ → PtA}
    (hzz : ∀ n : ℕ, Squarefree n → (n % 8 = 5 ∨ n % 8 = 7) →
      z' n = z n ∨ z' n = -z n ∨ (IsOfFinAddOrder (z n) ∧ IsOfFinAddOrder (z' n))) :
    TYZThm33With z ↔ TYZThm33With z' := by
  refine ⟨tyzThm33With_imp hzz, tyzThm33With_imp fun n hsq hn => ?_⟩
  rcases hzz n hsq hn with e | e | ⟨t, t'⟩
  · exact Or.inl e.symm
  · exact Or.inr (Or.inl (by rw [e, neg_neg]))
  · exact Or.inr (Or.inr ⟨t', t⟩)

/-! ## §4. Main theorem: the leaf is TYZ's Theorem 3.3 for TYZ's own `z_n` -/

/-- **The sign of `[i]` is pinned by TYZ's Theorem 3.6(1).** Let `zT` be any family of CM points of
the shape TYZ define (L1174, L1192–1198, L1245–1252): for `n ≡ 5 (mod 8)` one of `±(P − [i]P)`,
`±(P + [i]P)` (`P = f₀(P_n)`; the two readings of `[i]` and the sign of `i₀`), for `n ≡ 7 (mod 8)`
one of `±f₀(P_n)` (`f_n = i₀`, sign of `i₀`), and assume it satisfies TYZ's printed Theorem 3.6(1),
conjugation part (L1413: `z̄_n = −z_n + τ(1)`, `τ(1) = (0, 0)`). Then TYZ's Theorem 3.3 for `zT`
(`TYZThm33With zT`) is equivalent to the kernel's leaf `TYZThm33`. -/
theorem tyzThm33With_iff_of_reading (hA : CMAlgebraic) (zT : ℕ → PtA)
    (h5 : ∀ n : ℕ, n % 8 = 5 → Squarefree n →
      zT n = tyzZn n ∨ zT n = -tyzZn n ∨ zT n = zAlt n ∨ zT n = -zAlt n)
    (h36 : ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∀ γ : GalQ, IsComplexConj γ →
      galPt γ (zT n) = tauG 2 - zT n)
    (h7 : ∀ n : ℕ, n % 8 = 7 → Squarefree n → zT n = tyzZ7 n ∨ zT n = -tyzZ7 n) :
    TYZThm33With zT ↔ TYZThm33 := by
  rw [tyzThm33_iff_with]
  refine (tyzThm33With_iff fun n hsq hn => ?_).symm
  obtain ⟨γ, hγ⟩ := exists_complexConj
  rcases hn with hn | hn
  · have hb : basePt n = tyzZn n := by simp [basePt, hn]
    rw [hb]
    rcases h5 n hn hsq with e | e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · have h := h36 n hn hsq γ hγ
      rw [e] at h
      have tP := torsion_of_alt_thm36 hA hn hsq hγ h
      obtain ⟨t1, t2⟩ := torsion_readings tP
      exact Or.inr (Or.inr ⟨t1, by rw [e]; exact t2⟩)
    · have h := h36 n hn hsq γ hγ
      rw [e, map_neg, sub_neg_eq_add] at h
      have h' : galPt γ (zAlt n) = tauG 2 - zAlt n := by
        have e2 := congrArg Neg.neg h
        rw [neg_neg] at e2
        rw [e2]
        calc -(tauG 2 + zAlt n) = (tauG 2 - zAlt n) - (tauG 2 + tauG 2) := by abel
          _ = tauG 2 - zAlt n := by rw [tauG_two_add_self, sub_zero]
      have tP := torsion_of_alt_thm36 hA hn hsq hγ h'
      obtain ⟨t1, t2⟩ := torsion_readings tP
      exact Or.inr (Or.inr ⟨t1, by rw [e]; exact tors_neg t2⟩)
  · have hb : basePt n = tyzZ7 n := by
      have : n % 8 ≠ 5 := by omega
      simp [basePt, this]
    rw [hb]
    rcases h7 n hn hsq with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)

/-- The kernel's own family satisfies the hypotheses (so the theorem is not vacuous). -/
theorem basePt_reading (hA : CMAlgebraic) :
    (∀ n : ℕ, n % 8 = 5 → Squarefree n →
      basePt n = tyzZn n ∨ basePt n = -tyzZn n ∨ basePt n = zAlt n ∨ basePt n = -zAlt n) ∧
    (∀ n : ℕ, n % 8 = 5 → Squarefree n → ∀ γ : GalQ, IsComplexConj γ →
      galPt γ (basePt n) = tauG 2 - basePt n) ∧
    (∀ n : ℕ, n % 8 = 7 → Squarefree n → basePt n = tyzZ7 n ∨ basePt n = -tyzZ7 n) := by
  refine ⟨fun n hn _ => Or.inl (by simp [basePt, hn]), fun n hn hsq γ hγ => ?_,
    fun n hn _ => Or.inl ?_⟩
  · have hb : basePt n = tyzZn n := by simp [basePt, hn]
    rw [hb]; exact conj_tyzZn hA hn hsq hγ
  · have : n % 8 ≠ 5 := by omega
    simp [basePt, this]

end ZInQ.Contrib.TYZGenus.H33Sign

#print axioms ZInQ.Contrib.TYZGenus.H33Sign.tyzThm33With_iff_of_reading
#print axioms ZInQ.Contrib.TYZGenus.H33Sign.basePt_reading
#print axioms ZInQ.Contrib.TYZGenus.H33Sign.torsion_of_alt_thm36
#print axioms ZInQ.Contrib.TYZGenus.H33Sign.tyzThm33Copy_iff

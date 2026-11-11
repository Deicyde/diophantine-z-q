import ZInQKernel.Hypotheses.Height

/-!
# wk-h, Tier 2: the Arakelov half of H as a signature of published theorems

Draft for `docs/research/wk-h.md` §4.2. Mathlib v4.35 has no abelian varieties over number fields
with Faltings heights, isogeny degrees or theta constants. This file therefore states the
Arakelov half of N5's proof (h-trust E2-E4, F1, F3) over a **signature** `ArakelovSig`: abstract
types and functions, one Prop field per published theorem. The intended model is the real one
(abelian varieties over number fields, the stable Faltings height in Faltings' normalization,
`J₁(N)`, the Hauptmodul coordinate of the discriminant-6 QM locus, even theta nulls).

Faithfulness is relative to that interpretation: a reader checks each field against its paper.
The residual `ModularLevelBound` (h-trust A1-D5: geometry, scalar descent, Pan, conductor) is
*not* a published theorem; it is Glazer's new argument plus its inputs, with no heights in it.

`jHeightBound_of_sig` (the Tier-2 reduction) has conclusion `JHeightBound` of
`scratch/wk-h/BackToU.lean`; `Jmap` and `heightX` are repeated here verbatim, since scratch files
do not import each other.
-/

namespace ZInQ.WkH

open ZInQ Real

/-- As in `BackToU.lean`. -/
def Jmap (u : ℚ) : ℚ :=
  -57600 * (u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60)) ^ 2 /
    (7 * u ^ 2 + 300 * u + 3600) ^ 6

/-- As in `BackToU.lean`. -/
noncomputable def heightX (R : ℝ) : ℝ := max 1 (max (heightCcm : ℝ) (heightQ R ^ 17))

/-- A bundled number field. -/
structure NF where
  K : Type
  [fld : Field K]
  [nf : NumberField K]

attribute [instance] NF.fld NF.nf

/-- `[K : ℚ]`. -/
noncomputable def NF.deg (K : NF) : ℕ := Module.finrank ℚ K.K

/-- Absolute logarithmic height of a point of `P⁹(K)`: Mathlib's `Height.logHeight` divided by
`[K : ℚ]`. -/
noncomputable def absLogHeight10 {K : NF} (z : Fin 10 → K.K) : ℝ :=
  Height.logHeight z / K.deg

/-- N5's theta-to-`j` map `Φ(z) = 3779136 (∏ z_m)⁴ / (∑ z_m⁸)⁵` (h-trust F1). -/
noncomputable def thetaJ {K : Type} [Field K] (z : Fin 10 → K) : K :=
  3779136 * (∏ m, z m) ^ 4 / (∑ m, z m ^ 8) ^ 5

/-- **The signature.** Abstract abelian varieties over number fields with the data that N5's
transfer and return steps use. -/
structure ArakelovSig where
  /-- abelian varieties over `K` -/
  AV : NF → Type
  dim : ∀ {K : NF}, AV K → ℕ
  /-- the stable Faltings height, Faltings' original normalization -/
  hF : ∀ {K : NF}, AV K → ℝ
  /-- isogenies over `K` and their degrees -/
  Isog : ∀ {K : NF}, AV K → AV K → Type
  deg : ∀ {K : NF} {A B : AV K}, Isog A B → ℕ
  /-- products -/
  prod : ∀ {K : NF}, AV K → AV K → AV K
  /-- `J₁(N)` base-changed to `K` -/
  J1 : ℕ → (K : NF) → AV K
  /-- `some j` iff `A` is a principally polarized abelian surface with QM by the maximal order of
  `B = (2,−3)`, with N5's polarization type, and Hauptmodul coordinate `j` (finite) -/
  jQM : ∀ {K : NF}, AV K → Option K.K
  /-- a field of definition of a level-2 theta structure, and the ten even theta nulls -/
  thetaField : ∀ {K : NF}, AV K → NF
  embed : ∀ {K : NF} (A : AV K), K.K →+* (thetaField A).K
  theta : ∀ {K : NF} (A : AV K), Fin 10 → (thetaField A).K

namespace ArakelovSig

variable (W : ArakelovSig)

/-- **Javanpeykar 2014, Thm 1.1.1**, at `X = X₁(N)` (genus and Belyi degree `≤ N²`; the stable
height is invariant under base change): `h_F(J₁(N)) ≤ 1.3·10⁷ N¹²`, `dim J₁(N) ≤ N²`. -/
def Javanpeykar : Prop :=
  ∀ (N : ℕ) (K : NF), W.hF (W.J1 N K) ≤ 13000000 * (N : ℝ) ^ 12 ∧ W.dim (W.J1 N K) ≤ N ^ 2

/-- **Gaudron–Rémond 2014, Thm 1.4** (with `g = dim A`, `d = [K:ℚ]`). -/
def GaudronRemond : Prop :=
  ∀ (K : NF) (A B : W.AV K), Nonempty (W.Isog A B) → ∃ φ : W.Isog A B,
    log (W.deg φ) ≤ 1024 * (W.dim A : ℝ) ^ 3 *
      (64 * (W.dim A : ℝ) ^ 2 * log (14 * W.dim A) + log K.deg +
        2 * log (max (W.hF A) (max (log K.deg) 1)))

/-- **Faltings 1983, Lemma 5** (height variation), with additivity and dimension. -/
def FaltingsVariation : Prop :=
  (∀ (K : NF) (A B : W.AV K) (φ : W.Isog A B),
      |W.hF A - W.hF B| ≤ log (W.deg φ) / 2 ∧ W.dim A = W.dim B ∧ 0 < W.deg φ) ∧
  (∀ (K : NF) (A Z : W.AV K),
      W.hF (W.prod A Z) = W.hF A + W.hF Z ∧ W.dim (W.prod A Z) = W.dim A + W.dim Z)

/-- **Bost's lower bound**, as recorded in GR14 §9: `h_F(Z) ≥ −(3/2) dim Z`. -/
def BostLower : Prop := ∀ (K : NF) (Z : W.AV K), -(3 / 2 : ℝ) * W.dim Z ≤ W.hF Z

/-- **Pazuki 2012, Cor. 1.3(2)**, `g = 2`, `r = 2`, Deligne metric (`X_D = max(1, h_F + log π)`),
for principally polarized surfaces (here: those on the QM locus). -/
def Pazuki : Prop :=
  ∀ (K : NF) (A : W.AV K), (W.jQM A).isSome →
    W.theta A ≠ 0 ∧
    absLogHeight10 (W.theta A) ≤ max 1 (W.hF A + log π) / 2 +
      1000 * 2 ^ 4 * (log (2 ^ 4)) ^ 5 * log (max 1 (W.hF A + log π) + 2)

/-- **Lin–Yang 2020 eqs. (2), (13), (14); Lauter–Naehrig–Yang 2015 §2.2; Igusa 1967**:
on the QM locus with `j` finite and nonzero, `j = Φ(theta nulls)` (h-trust F1, with
`scratch/h-v14/igusa_check.py`). -/
def IgusaLY : Prop :=
  ∀ (K : NF) (A : W.AV K) (j : K.K), W.jQM A = some j → j ≠ 0 →
    (∑ m, W.theta A m ^ 8) ≠ 0 ∧ thetaJ (W.theta A) = W.embed A j

/-- The published inputs of the Arakelov half. -/
def Literature : Prop :=
  W.Javanpeykar ∧ W.GaudronRemond ∧ W.FaltingsVariation ∧ W.BostLower ∧ W.Pazuki ∧ W.IgusaLY

/-- **Residual: modularity with a level bound** (h-trust A1-D5 and E1; Glazer's scalar descent and
conductor bound, Pan, Carayol, Faltings' Hom theorem, the Shimura-curve geometry, NoCM): for
`u ∉ 𝒞` there are a number field `L'` with `[L':ℚ] ≤ Q M`, the QM surface `A/L'` over `J(u)`,
an abelian variety `Z/L'` and `N ≤ Q M²` with an `L'`-isogeny `J₁(N) → A × Z`. -/
def ModularLevelBound (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet → ∃ (K : NF) (A Z : W.AV K) (N : ℕ),
    W.jQM A = some (algebraMap ℚ K.K (Jmap u)) ∧ W.dim A = 2 ∧
    (K.deg : ℝ) ≤ heightQ heightD * contactSupport S u ∧
    (N : ℝ) ≤ heightQ heightD * (contactSupport S u : ℝ) ^ 2 ∧
    Nonempty (W.Isog (W.J1 N K) (W.prod A Z))

end ArakelovSig

/-- **E3-E4 arithmetic (Glazer's transfer numerics, N5 L868-905), as a real-number lemma.**
Inputs: Javanpeykar (`hJ`), the genus and degree bounds, GR14 (`hL`), variation plus additivity
(`hvar`) and Bost (`hZ`). -/
theorem transfer_numerics {Q M hFJ g d L hA hZ : ℝ} (hQ : 10 ^ 12 ≤ Q) (hM : 1 ≤ M)
    (hg2 : 2 ≤ g) (hg : g ≤ Q ^ 3 * M ^ 4) (hd1 : 1 ≤ d) (hd : d ≤ Q * M)
    (hJ : hFJ ≤ Q ^ 13 * M ^ 24)
    (hL : L ≤ 1024 * g ^ 3 * (64 * g ^ 2 * log (14 * g) + log d +
      2 * log (max hFJ (max (log d) 1))))
    (hvar : hA + hZ ≤ hFJ + L / 2) (hZ : -(2 * g) ≤ hZ) :
    hA ≤ Q ^ 17 * M ^ 24 := by
  set P := Q * M ^ 4 with hPdef
  have hQ1 : (1 : ℝ) ≤ Q := le_trans (by norm_num) hQ
  have hM4 : (1 : ℝ) ≤ M ^ 4 := one_le_pow₀ hM
  have hP : (10 : ℝ) ^ 12 ≤ P := by
    calc (10 : ℝ) ^ 12 = 10 ^ 12 * 1 := by ring
      _ ≤ Q * M ^ 4 := by gcongr
  have hP0 : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hlogP : log P ≤ P := le_trans (log_le_sub_one_of_pos hP0) (by linarith)
  -- the three logarithms
  have hl1 : log (14 * g) ≤ 4 * P := by
    have h14 : 14 * g ≤ P ^ 4 := by
      have hM12 : (1 : ℝ) ≤ M ^ 12 := one_le_pow₀ hM
      have hQ3 : (1 : ℝ) ≤ Q ^ 3 := one_le_pow₀ hQ1
      calc 14 * g ≤ 14 * (Q ^ 3 * M ^ 4) := by linarith
        _ ≤ Q * (Q ^ 3 * M ^ 4) * M ^ 12 := by
            have : (14 : ℝ) ≤ Q := le_trans (by norm_num) hQ
            have h0 : 0 ≤ Q ^ 3 * M ^ 4 := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hM12 (mul_nonneg (by positivity : (0:ℝ) ≤ Q) h0)]
        _ = P ^ 4 := by rw [hPdef]; ring
    calc log (14 * g) ≤ log (P ^ 4) := log_le_log (by linarith) h14
      _ = 4 * log P := by rw [log_pow]; norm_num
      _ ≤ 4 * P := by linarith
  have hl2 : log d ≤ P := by
    have : d ≤ P := by
      calc d ≤ Q * M := hd
        _ ≤ Q * M ^ 4 := by
            gcongr
            calc M = M ^ 1 := (pow_one M).symm
              _ ≤ M ^ 4 := pow_le_pow_right₀ hM (by norm_num)
    linarith [log_le_log (by linarith) this]
  have hl3 : log (max hFJ (max (log d) 1)) ≤ 13 * P := by
    have hY : max hFJ (max (log d) 1) ≤ P ^ 13 := by
      have hP13 : P ≤ P ^ 13 := le_self_pow₀ (by linarith) (by norm_num)
      have hQM : Q ^ 13 * M ^ 24 ≤ P ^ 13 := by
        rw [hPdef, mul_pow, ← pow_mul]
        gcongr
        · norm_num
      refine max_le (hJ.trans hQM) (max_le ?_ ?_)
      · linarith [log_le_sub_one_of_pos (by linarith : (0:ℝ) < d)]
      · linarith
    calc log (max hFJ (max (log d) 1)) ≤ log (P ^ 13) :=
          log_le_log (lt_of_lt_of_le one_pos (le_max_of_le_right (le_max_right _ _))) hY
      _ = 13 * log P := by rw [log_pow]; norm_num
      _ ≤ 13 * P := by linarith
  -- assemble
  have hg0 : 0 ≤ g := by linarith
  have hlog14 : 0 ≤ log (14 * g) := log_nonneg (by linarith)
  have hL' : L ≤ 1024 * g ^ 3 * (64 * g ^ 2 * (4 * P) + P + 2 * (13 * P)) := by
    refine hL.trans ?_
    gcongr
  have hg3 : g ^ 3 ≤ (Q ^ 3 * M ^ 4) ^ 3 := by gcongr
  have hg2' : g ^ 2 ≤ (Q ^ 3 * M ^ 4) ^ 2 := by gcongr
  have hL'' : L ≤ 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (64 * (Q ^ 3 * M ^ 4) ^ 2 * (4 * P) + 27 * P) := by
    refine hL'.trans ?_
    have : 64 * g ^ 2 * (4 * P) + P + 2 * (13 * P) ≤
        64 * (Q ^ 3 * M ^ 4) ^ 2 * (4 * P) + 27 * P := by nlinarith
    have h0 : 0 ≤ 64 * g ^ 2 * (4 * P) + P + 2 * (13 * P) := by positivity
    calc 1024 * g ^ 3 * (64 * g ^ 2 * (4 * P) + P + 2 * (13 * P))
        ≤ 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (64 * g ^ 2 * (4 * P) + P + 2 * (13 * P)) := by gcongr
      _ ≤ _ := by gcongr
  -- final comparison, in the monomials `Q^k M^24`
  have hT : 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (64 * (Q ^ 3 * M ^ 4) ^ 2 * (4 * P) + 27 * P) ≤
      262144 * Q ^ 16 * M ^ 24 + 27648 * Q ^ 16 * M ^ 24 := by
    rw [hPdef]
    have hM8 : (1 : ℝ) ≤ M ^ 8 := one_le_pow₀ hM
    have hQ6 : (1 : ℝ) ≤ Q ^ 6 := one_le_pow₀ hQ1
    have e1 : 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (64 * (Q ^ 3 * M ^ 4) ^ 2 * (4 * (Q * M ^ 4))) =
        262144 * Q ^ 16 * M ^ 24 := by ring
    have e2 : 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (27 * (Q * M ^ 4)) = 27648 * (Q ^ 10 * M ^ 16) := by ring
    have e3 : Q ^ 10 * M ^ 16 ≤ Q ^ 16 * M ^ 24 := by
      have : Q ^ 16 * M ^ 24 = (Q ^ 10 * M ^ 16) * (Q ^ 6 * M ^ 8) := by ring
      rw [this]
      have h0 : 0 ≤ Q ^ 10 * M ^ 16 := by positivity
      nlinarith [one_le_mul_of_one_le_of_one_le hQ6 hM8]
    nlinarith [e1, e2, e3]
  have hgQ : 2 * g ≤ 2 * (Q ^ 3 * M ^ 4) := by linarith
  have hlow : Q ^ 3 * M ^ 4 ≤ Q ^ 16 * M ^ 24 := by
    have h1 : (1 : ℝ) ≤ Q ^ 13 := one_le_pow₀ hQ1
    have h2 : (1 : ℝ) ≤ M ^ 20 := one_le_pow₀ hM
    have : Q ^ 16 * M ^ 24 = (Q ^ 3 * M ^ 4) * (Q ^ 13 * M ^ 20) := by ring
    rw [this]
    have h0 : 0 ≤ Q ^ 3 * M ^ 4 := by positivity
    nlinarith [one_le_mul_of_one_le_of_one_le h1 h2]
  have hJ' : Q ^ 13 * M ^ 24 ≤ Q ^ 16 * M ^ 24 := by
    have : Q ^ 13 ≤ Q ^ 16 := pow_le_pow_right₀ hQ1 (by norm_num)
    gcongr
  have hfin : Q ^ 16 * M ^ 24 * 10 ^ 12 ≤ Q ^ 17 * M ^ 24 := by
    have : Q ^ 17 * M ^ 24 = Q ^ 16 * M ^ 24 * Q := by ring
    rw [this]; gcongr
  have hT0 : 0 ≤ Q ^ 16 * M ^ 24 := by positivity
  nlinarith

/-- **Tier-2 reduction.** The published Arakelov inputs and the residual modularity statement
imply `JHeightBound`. Proof plan: `ModularLevelBound` gives `K, A, Z, N`; `Javanpeykar` and
`N ≤ QM²` give `h_F(J) ≤ Q¹³M²⁴`, `g ≤ Q³M⁴`; `GaudronRemond` gives `φ : J₁(N) → A × Z`;
`FaltingsVariation` and `BostLower` give `h_F(A) + h_F(Z) ≤ h_F(J) + ½ log deg φ`,
`h_F(Z) ≥ −2g`; `transfer_numerics` gives `h_F(A) ≤ Q¹⁷M²⁴` (so `max(1,h_F(A)) ≤ X·M²⁴`);
`Pazuki` gives `h(z) ≤ 10⁴·2²⁴·max(1, h_F(A))`; `IgusaLY` and Mathlib's `logHeight_eval_le`
(degree 40, `ℓ¹` norms `3779136`, `10⁵`) give `h(J(u)) ≤ 40 h(z) + 22`, using that the absolute
height of a rational number does not change in an extension. -/
theorem jHeightBound_of_sig (W : ArakelovSig) (S : Finset ℕ) (hlit : W.Literature)
    (hmod : W.ModularLevelBound S) :
    ∀ u : ℚ, u ∉ contactSet →
      ratHeight (Jmap u) ≤
        (40 * 10000 * 2 ^ 24 + 22 : ℝ) * heightX heightD * (contactSupport S u : ℝ) ^ 24 := by
  sorry

end ZInQ.WkH

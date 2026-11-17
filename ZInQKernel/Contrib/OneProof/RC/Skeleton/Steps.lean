import ZInQKernel.Contrib.OneProof.RC.Skeleton.Setup
import ZInQKernel.Contrib.PoleRC.CRM

/-!
# Theorem 5.3, Lane RC0: the inputs of Elliot's deduction, one `Prop` each

Each input of the deduction of Theorem 5.3 (`hyp:RC`) is one `Prop` below, named after the
manuscript (`diophantine_zq.tex`, 11/5), with its tex lines, its kind and the lane expected to
discharge it. Kinds: `PRINT` (a printed theorem taken as a leaf), `ELLIOT` (Elliot's own step,
stated, not proved here), `GLUE` (textbook fact), `PURE` (pure mathematics, to be `PROVED` by the
named lane). The deduction itself is `Skeleton.restrictedConverse_of_steps`.

## The inputs, with tex lines, kind and the lane expected to discharge each

| input | tex | kind | lane |
|---|---|---|---|
| `DDSelmerParity` | 1793–1797 | PRINT (Dokchitser–Dokchitser Thm 1.8) + GLUE | RC8-prints-analytic |
| `ForwardRankZero` | 1086–1108 (r = 0), used 2627–2628 | PRINT (Kolyvagin Thm 1; Kato Cor 14.3) | RC8 / RC9 |
| `BitDegree` | 5668–5676 | PURE | RC1-boolean |
| `CubeParity` | 5680–5684 | PURE | RC1-boolean |
| `BooleanAddress` | 5676–5692 | PURE (from the two above) | RC1-boolean |
| `ConvolutionEstimate` | 5693–5726 | PURE | RC1-boolean (`difference_estimate`) |
| `RCSteps.lstar_ne_zero_iff` | 1825–1830 | ELLIOT/GLUE | RC11-even |
| `RCSteps.genus_partner` | 2404–2406 | ELLIOT | RC13-nonvanishing |
| `RCSteps.visibility` (O.8) | 9407–9445 | ELLIOT + PRINT (CST 1.1; Cornut–Jetchev 3.1) | RC12-odd (RC9) |
| `RCSteps.stages_advance` | 2491–2500, 2536–2551 | ELLIOT | RC12-odd |
| `RCSteps.one_admissible` | 2595 | ELLIOT | RC12-odd |
| `RCSteps.companion` | 2604–2613 | ELLIOT | RC2 / RC11 / RC13 |
| `RCSteps.gz_comparison` (3.4) | 2427–2439, 2713–2714 | PRINT (CST 1.1) + ELLIOT | CST task (no lane) |
| `RCSteps.final_family` (3.9) | 2695–2715, 10792–10858 | ELLIOT | RC2 / RC3 / RC12 / RC11 / RC13 |
| `RCSteps.calibration` (4.6) | 3989–4140 | ELLIOT (+ Kolyvagin, Milne, Edixhoven) | RC15-central |
| `RCSteps.common_coordinate` (4.7) | 4142–4317 | ELLIOT | RC15-central (RC4) |
| `RCSteps.height_one` | 4909–5205, 5703–5704 | ELLIOT | RC16-uniform |
| `RCSteps.clearing` (5.9) | 5486–5664 | ELLIOT | RC7-determinant |
| `RCSteps.base_zero` | 4319–4373 | ELLIOT + PRINT (CST 1.1) | RC15-central |

## The interface data `RCData ℓ`

Heegner points, theta coefficients, Kato/Heegner determinant coordinates and normalized central
values do not exist in Mathlib. `RCData ℓ` collects them for the fixed curve `E = E_ℓ` as abstract
data: their only meaning is what the `Prop`s below say about them, and each such `Prop` says what
the manuscript proves about the genuine object.

| field | manuscript object | tex |
|---|---|---|
| `S` | the fixed support (primes of `2N`, `h_*`, `k`, the theta prime, exclusions) | 1790–1793, 2700 |
| `prepared h` | `h` lies in the prepared filter containing one: the fixed local types (squareclasses at `2N`, sign) of the filter, prime to the fixed support | 2404–2410, 2700–2702 |
| `Lstar h` | normalized central value `L_*(h)` of `E^{(h)}` | 1825–1830 |
| `jgen h` | index valuation `j_gen(h)` of the genus point `P_h^{gen}` | 2411–2418 |
| `jrc h k` | index valuation `j_rc(h,k)` of the ring-class point `P_{h,k}^{rc}` | 2411–2418 |
| `hstar` | the negative genus partner `h_*` | 2404–2406 |
| `stages`, `Mθ`, `aθ`, `admissible` | the chosen nonprincipal ultrafilter on actual theta stages, the stage precision `M_θ`, the phase-removed odd coefficients `a_{M_θ}(D)`, the stage support `(D/ℓ₀) = 1` | 2491–2551 |
| `δo` | the odd ultrafilter minimum `δ = δ_o` | 2536–2551 |
| `kfin` | the final companion `k`, `K = ℚ(√k)` | 2604–2613 |
| `uPrim F x`, `uTilde F x` | the primitive coordinate `u_{prim,x}` and the corrected coordinate `ũ_x = (η u_{rel})_x` of Definition `ex:arith-coordinate` and Lemma `ex:arith-common-coordinate`, for the fixed `K` and the binary family `F` | 3882–3892, 4142–4317 |
-/

noncomputable section

namespace ZInQ.Manuscript.RC

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower Filter

attribute [local instance] Nat.fact_prime_two

/-- The fixed curve `E = E_ℓ` and its twists `E^{(h)} = E_{hℓ}` (`twist_curve`). -/
abbrev Eℓ (ℓ : ℕ) : WeierstrassCurve ℚ := curve (ℓ : ℚ)

/-- `E^{(h)}` for an integer `h`. -/
abbrev Etw (ℓ : ℕ) (h : ℤ) : WeierstrassCurve ℚ := twist (h : ℚ) (Eℓ ℓ)

/-- The 2-adic valuation of an integer (`vZ 0 = ⊤`). -/
def vZ (n : ℤ) : WithTop ℤ := v2 (n : ℚ_[2])

/-- **The interface data of the deduction for the fixed `ℓ`** (see the module docstring). -/
structure RCData (ℓ : ℕ) where
  /-- the fixed support -/
  S : Finset ℕ
  /-- `h` lies in the prepared filter containing one (fixed local types at `2N`) -/
  prepared : ℤ → Prop
  /-- normalized central values `L_*(h)` -/
  Lstar : ℤ → ℚ
  /-- genus index valuation `j_gen(h)` -/
  jgen : ℤ → ℤ
  /-- ring-class index valuation `j_rc(h, k)` -/
  jrc : ℤ → ℤ → ℤ
  /-- the negative genus partner `h_*` -/
  hstar : ℤ
  /-- the chosen nonprincipal ultrafilter on the actual theta stages -/
  stages : Ultrafilter ℕ
  /-- the precision `M_θ` of stage `θ` -/
  Mθ : ℕ → ℕ
  /-- the phase-removed odd coefficients `a_{M_θ}(D)` at stage `θ` -/
  aθ : ℕ → ℤ → ℤ
  /-- the stage support: `D` admissible at stage `θ` with `(D/ℓ₀) = 1` -/
  admissible : ℕ → ℤ → Prop
  /-- the odd ultrafilter minimum `δ_o` -/
  δo : ℤ
  /-- the final companion `k` -/
  kfin : ℤ
  /-- the primitive coordinate `u_{prim,x}` (fixed `K`, binary family `F`, address `x`) -/
  uPrim : (F : Family) → Addr F.b → PowerSeries ℚ_[2]
  /-- the corrected coordinate `ũ_x` -/
  uTilde : (F : Family) → Addr F.b → PowerSeries ℚ_[2]

namespace RCData

variable {ℓ : ℕ} (D : RCData ℓ)

/-- **The intrinsic odd limit symbol is a unit at the empty configuration** (lines 2593–2596): the
odd symbol `A_o(D) = [v₂ a(D) = δ_o + ω(D)]` (Definition `ex:sec7-symbol`) at `D = 1`, as an
ultrafilter limit over the stages: `v₂ a_{M_θ}(1) = δ_o` on a set of stages in the ultrafilter. -/
def OddEmptyUnit : Prop :=
  ∀ᶠ θ in (D.stages : Filter ℕ), vZ (D.aθ θ 1) = D.δo

/-- **The family satisfies (3.9)** for the fixed `k` with constants `C_o, C_e`
(Proposition `ex:sec7-final-family`, lines 2695–2715; App G `ex:app-final-family`, 10792–10858):
`F` is admissible (good odd primes outside the support, split in `K`, nonzero `λ_q`), and at every
nonzero address `h_x` keeps the fixed local types (`prepared`), `ord_{s=1} L(E^{(h_x)},s) = 1`, `L_*(h_x k) ≠ 0`, `j_gen(h_x) ≤ ω(h_x) + C_o`,
`v₂ L_*(h_x k) ≤ 2ω(h_x) + C_e`. -/
def FinalFamilyAt (Co Ce : ℤ) (F : Family) : Prop :=
  F.Admissible D.S D.kfin ∧ ∀ x : Addr F.b, x ≠ 0 →
    D.prepared (F.h x) ∧ AnalyticRankOne (Etw ℓ (F.h x)) ∧ D.Lstar (F.h x * D.kfin) ≠ 0 ∧
    D.jgen (F.h x) ≤ omega (F.h x) + Co ∧
    padicValRat 2 (D.Lstar (F.h x * D.kfin)) ≤ 2 * omega (F.h x) + Ce

end RCData

/-- **`s₂(E/K) = 1`** for `K = ℚ(√k)`, stated over the twist (lines 2627–2647): the
sum-and-difference isogeny gives `s₂(E/K) = s₂(E/ℚ) + s₂(E^{(k)}/ℚ)`, so `s₂(E/K) = 1` is
`corank Sel_{2^∞}(E/ℚ) = 1` together with `corank Sel_{2^∞}(E^{(k)}/ℚ) = 0`. (DEPARTURE of form:
the Selmer group over `K` is not defined; its corank is replaced by the two rational coranks, which
is the identity Elliot proves and uses.) -/
def SelmerCorankOneOverK (ℓ : ℕ) (k : ℤ) : Prop :=
  SelmerCorankOne (Eℓ ℓ) ∧ Z2Corank (selmerTwoPower (Etw ℓ k)) 0

/-! ## Inputs that do not mention the interface data -/

/-- **Dokchitser–Dokchitser Selmer parity, as used at lines 1793–1797** (PRINT + GLUE; lane
RC8-prints-analytic). `E_ℓ` has a rational 2-isogeny, so the `2^∞`-Selmer parity theorem
(T. and V. Dokchitser, *Root numbers and parity of ranks of elliptic curves*, J. reine angew. Math.
658 (2011), Theorem 1.8 as the 11/5 text cites it; Version 19 cites instead *On the
Birch–Swinnerton-Dyer quotients modulo squares*, Ann. of Math. 172 (2010), Theorem 1.4, p. 568;
locators UNVERIFIED here, lane RC8 reads the prints) gives root number `w(E) = (−1)^{corank}`,
so `corank Sel_{2^∞} = 1` gives `w(E) = −1`; with modularity (BCDT) and the functional equation
(GLUE) the analytic order at `s = 1` is odd. Mathlib has no root numbers, so the statement is the
parity of the analytic order, which is the only consequence the deduction uses (lines 5736–5741). -/
def DDSelmerParity : Prop :=
  ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 → SelmerCorankOne (Eℓ ℓ) →
    ∃ n : ℕ, Odd n ∧ AnalyticOrder (Eℓ ℓ) n

/-- **The forward theorem in analytic rank zero** (`lem:forward-rank`, lines 1086–1108, the case
`r = 0`; PRINT: Kolyvagin, MPIM preprint 90-69, Theorem 1, and independently Kato, Astérisque 295,
Corollary 14.3; lanes RC8/RC9). Used at lines 2627–2628: `L(E^{(k)}, 1) ≠ 0` gives
`s₂(E^{(k)}/ℚ) = 0`. -/
def ForwardRankZero : Prop :=
  ∀ A : WeierstrassCurve ℚ, A.IsElliptic → CentralNonzero A → Z2Corank (selmerTwoPower A) 0

/-- `φ : 𝔽₂^b → 𝔽₂` has Boolean degree at most `n`: some polynomial over `𝔽₂` of total degree at
most `n` represents it on the cube (the form of lane RC1-boolean's `HasBoolDegLE`). -/
def BoolDegLE {b : ℕ} (φ : Addr b → ZMod 2) (n : ℕ) : Prop :=
  ∃ P : MvPolynomial (Fin b) (ZMod 2), P.totalDegree ≤ n ∧ ∀ x : Addr b, MvPolynomial.eval x P = φ x

/-- The bit of index `j` of a 2-adic integer: the binary digit of index `j` of its residue modulo
`2^{j+1}` (the form of lane RC1-boolean's `padicBit`). -/
def bit (j : ℕ) (z : ℤ_[2]) : ZMod 2 := (((PadicInt.toZModPow (j + 1) z).val / 2 ^ j : ℕ) : ZMod 2)

/-- The sign-value function `x ↦ Σ_g x(g) α_g` of an element `α` of `ℤ₂[G]`, `G ≅ 𝔽₂^b` (lines
5666–5667; lane RC1-boolean's `signEval (dotPairing b) α`). -/
def signVal {b : ℕ} (α : Addr b → ℤ_[2]) (x : Addr b) : ℤ_[2] :=
  ∑ g : Addr b, (chi x g : ℤ_[2]) * α g

/-- **The Boolean bit-degree lemma** (lines 5668–5676; PURE, lane RC1-boolean): bit `j ≥ 1` of the
sign-value function of an element of `ℤ₂[G]` has Boolean degree at most `2^{j−1}`. -/
def BitDegree : Prop :=
  ∀ (b : ℕ) (α : Addr b → ℤ_[2]) (j : ℕ), 1 ≤ j →
    BoolDegLE (fun x : Addr b => bit j (signVal α x)) (2 ^ (j - 1))

/-- **Cube parity** (lines 5680–5684; PURE, lane RC1-boolean): a Boolean function on `𝔽₂^b` of
degree `< b` has support of even cardinality. -/
def CubeParity : Prop :=
  ∀ (b : ℕ) (φ : Addr b → ZMod 2) (n : ℕ), BoolDegLE φ n → n < b →
    Even (Finset.univ.filter fun x => φ x ≠ 0).card

/-- **The missing address** (lines 5676–5692; PURE, lane RC1-boolean, from `BitDegree` and
`CubeParity`): `q` coefficient equalities modulo `2^M` between the sign-value functions of `q`
elements of `ℤ₂[G]` at `x` and at `0`, with `q (2^{M−1} − 1) < b`, have a common solution
`x ≠ 0` (the product of the complementary indicators has degree `< b`, so the solution set has
even cardinality and contains `0`). The skeleton applies it to the coefficients of `f` from
`−L_T(M)` through `0` and the constant coefficient of `d`, `q = L_T(M) + 2`. -/
def BooleanAddress : Prop :=
  ∀ (b M q : ℕ) (α : Fin q → Addr b → ℤ_[2]), q * (2 ^ (M - 1) - 1) < b →
    ∃ x : Addr b, x ≠ 0 ∧ ∀ j, (2 : ℤ_[2]) ^ M ∣ signVal (α j) x - signVal (α j) 0

/-- **The convolution estimate (5.11)** (lines 5693–5726; PURE, lane RC1-boolean, its
`difference_estimate`, whose statement this is, argument for argument). Elements of `𝒪` enter by
their Laurent coefficients `ℤ → ℤ₂`, elements of `Λ[1/2]` by their coefficients `ℕ → ℚ₂`, and
`f ũ = d` by the convolution of coefficients. At an address where every negative coefficient of
`f_x` vanishes modulo `2^M`, `f_x(0) ≡ f_0(0)` and `d_x(0) ≡ d_0(0)` modulo `2^M`, with
`c = v₂ f_0(0) < M`, `f_0 ∈ Λ`, `ũ_x ∈ Λ[1/2]`: `‖ũ_x(0) − ũ_0(0)‖ ≤ 2^{2c−M}`, i.e.
`v₂(ũ_x(0) − ũ_0(0)) ≥ M − 2c`. -/
def ConvolutionEstimate : Prop :=
  ∀ (F₀ Fx : ℤ → ℤ_[2]) (U₀ Ux : ℕ → ℚ_[2]) (D₀ Dx : ℤ → ℤ_[2]) (c M : ℕ),
    (∃ (e : ℕ) (g : ℕ → ℤ_[2]), ∀ n, Ux n = (g n : ℚ_[2]) / 2 ^ e) →
    HasSum (fun k : ℕ => (F₀ (0 - k) : ℚ_[2]) * U₀ k) (D₀ 0) →
    (∀ n : ℤ, HasSum (fun k : ℕ => (Fx (n - k) : ℚ_[2]) * Ux k) (Dx n)) →
    (∀ i < 0, F₀ i = 0) → F₀ 0 ≠ 0 → (F₀ 0).valuation = c → c < M →
    (∀ i < 0, (2 : ℤ_[2]) ^ M ∣ Fx i) →
    (2 : ℤ_[2]) ^ M ∣ Fx 0 - F₀ 0 →
    (2 : ℤ_[2]) ^ M ∣ Dx 0 - D₀ 0 →
    ‖Ux 0 - U₀ 0‖ ≤ (2 : ℝ) ^ (2 * (c : ℤ) - M)

/-! ## Inputs about the interface data -/

/-- **The inputs of the deduction about the data `D`, one field per step.** -/
structure RCSteps {ℓ : ℕ} (D : RCData ℓ) : Prop where
  /-- **Normalized central values** (lines 1825–1830; ELLIOT/GLUE, the normalization by the fixed
  periods; lane RC11-even): `L_*(h) = 0` exactly when `L(E^{(h)}, 1) = 0`. -/
  lstar_ne_zero_iff : ∀ h : ℤ, h ≠ 0 → (D.Lstar h ≠ 0 ↔ CentralNonzero (Etw ℓ h))
  /-- **The genus partner** (lines 2404–2406; ELLIOT, via the nonvanishing proposition; lane
  RC13-nonvanishing): `h_* < 0` with `L_*(h_*) ≠ 0`. -/
  genus_partner : D.hstar < 0 ∧ D.Lstar D.hstar ≠ 0
  /-- **Visibility (O.8)** (App F `ex:app-visibility`, lines 9407–9445; ELLIOT, resting on
  Cai–Shu–Tian Thm 1.1 (separate project task) and (3.8) via Cornut–Jetchev Thm 3.1 (lane RC9);
  lane RC12-odd): one constant `C_det` such that at every stage and admissible `D`,
  `v₂ a_M(D) < M` implies `ord_{s=1} L(E^{(D)}, s) = 1` and `j_gen(D) ≤ v₂ a_M(D) + C_det`. -/
  visibility : ∃ Cdet : ℤ, ∀ θ : ℕ, ∀ Dd : ℤ, D.admissible θ Dd → vZ (D.aθ θ Dd) < D.Mθ θ →
    AnalyticRankOne (Etw ℓ Dd) ∧ (D.jgen Dd : WithTop ℤ) ≤ vZ (D.aθ θ Dd) + Cdet
  /-- **Arbitrarily advanced stages** (lines 2491–2500, (3.7), and the nonprincipal ultrafilter,
  2536–2551; ELLIOT; lane RC12-odd): the precision `M_θ` tends to infinity along the ultrafilter. -/
  stages_advance : Tendsto D.Mθ (D.stages : Filter ℕ) atTop
  /-- **`D = 1` lies in every moving support** (line 2595; ELLIOT): `(1/ℓ₀) = 1`. -/
  one_admissible : ∀ θ : ℕ, D.admissible θ 1
  /-- **The final companion** (lines 2604–2613; ELLIOT: a unit `k` of a separate even symbol on
  negative discriminants square at `2N`, so `L(E^{(k)}, 1) ≠ 0`; lanes RC2-symbols,
  RC11-even, RC13-nonvanishing). Used only in the remaining branch. `k` is a negative squarefree
  integer, `K = ℚ(√k) ≠ ℚ(i), ℚ(√−3)`, the primes of `k` lie in the fixed support, and
  `L(E^{(k)},1) ≠ 0`. -/
  companion : ¬ D.OddEmptyUnit → D.kfin < 0 ∧ Squarefree D.kfin ∧ D.kfin ≠ -1 ∧
    D.kfin ≠ -3 ∧ (∀ p : ℕ, p.Prime → (p : ℤ) ∣ D.kfin → p ∈ D.S) ∧
    CentralNonzero (Etw ℓ D.kfin)
  /-- **The Gross–Zagier comparison (3.4) with the fixed `k`** (lines 2427–2439, used at 2713–2714
  and App G 10868–10872; PRINT: Cai–Shu–Tian, Algebra & Number Theory 8 (2014), Theorem 1.1, applied
  twice (separate project task), plus ELLIOT's index-at-most-two comparison; no dedicated lane):
  for a known simple zero `h` of the prepared filter, prime to the support, with every prime of `h`
  split in `K` and `L_*(hk) ≠ 0`,
  `2j_rc(h,k) − 2j_gen(h) = v₂L_*(hk) − v₂L_*(h_*) + ε`, `|ε| ≤ 2`, "up to the one fixed initial
  period convention": that convention is the constant `C_per` (in App G it is part of
  `C_{H,final}`). -/
  gz_comparison : ∃ Cper : ℤ, ∀ h : ℤ, D.prepared h → AnalyticRankOne (Etw ℓ h) →
    D.Lstar (h * D.kfin) ≠ 0 →
    (∀ q : ℕ, q.Prime → (q : ℤ) ∣ h → q ∉ D.S ∧ jacobiSym D.kfin q = 1) →
    ∃ ε : ℤ, |ε| ≤ 2 ∧ 2 * D.jrc h D.kfin - 2 * D.jgen h =
      padicValRat 2 (D.Lstar (h * D.kfin)) - padicValRat 2 (D.Lstar D.hstar) + Cper + ε
  /-- **The final family (3.9)** (Proposition `ex:sec7-final-family`, lines 2695–2715, App G
  10792–10858; ELLIOT; lanes RC2-symbols (addresses), RC3-ksplit (the K-split seed),
  RC12-odd, RC11-even, RC13-nonvanishing). In the remaining branch, constants `C_o, C_e` fixed
  before `b`, and for every sufficiently large `b` one family over `𝔽₂^b` satisfying (3.9). -/
  final_family : ¬ D.OddEmptyUnit → ∃ Co Ce : ℤ, ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
    ∃ F : Family, F.b = b ∧ D.FinalFamilyAt Co Ce F
  /-- **The central calibration (4.6)** (Proposition `ex:arith-central-calibration`, lines
  3989–4140; ELLIOT, resting on `lem:forward-rank` (Kolyvagin Thm 1, PRINT), Milne ADT I.7.3
  (7.3.1) and Edixhoven Thm 5.3 / Rem 5.4.1 (lane RC9); lane RC15-central): one error bound `C_cal` such that at a known simple zero `h_x` with
  `L(E^{(h_x k)}, 1) ≠ 0`, `v₂ u_{prim,x}(0) = 2j_rc(h_x,k) − 4ω(h_x) − s(h_x) − s(h_x k)
  − Σ_{p|k} t_p + O(1)` with `0 ≤ t_p ≤ 2`. -/
  calibration : ∃ Ccal : ℤ, ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∀ x : Addr F.b, AnalyticRankOne (Etw ℓ (F.h x)) →
      CentralNonzero (Etw ℓ (F.h x * D.kfin)) →
      ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ Ccal ∧
        v2 (central (D.uPrim F x)) =
          ((2 * D.jrc (F.h x) D.kfin - 4 * omega (F.h x) - shaLength (Etw ℓ (F.h x)) -
            shaLength (Etw ℓ (F.h x * D.kfin)) - ∑ p ∈ D.kfin.natAbs.primeFactors, (t p : ℤ) +
              err : ℤ) : WithTop ℤ)
  /-- **The unused-prime comparison (4.7)** (Lemma `ex:arith-common-coordinate`, lines
  4142–4317; ELLIOT; lane RC15-central, with RC4-moving for the moving character): the
  corrected coordinate is a `Λ`-unit multiple of the primitive one at every character,
  `ũ_x = ε_x u_{prim,x}` with `ε_x ∈ Λ^×`. -/
  common_coordinate : ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    ∃ ε : PowerSeries ℚ_[2], LamUnit ε ∧ D.uTilde F x = ε * D.uPrim F x
  /-- **Height-one regularity** (lines 5207–5230 "by the height-one argument above", from
  Proposition `ex:limits-uniform-lower-bound`, 4909–5205; ELLIOT; lane RC16-uniform): every
  `ũ_x` of the final family lies in `Λ[1/2]`. -/
  height_one : ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    InLamHalf (D.uTilde F x)
  /-- **Determinant clearing (5.9)** (Proposition `ex:limits-fixed-field-clearing`, lines
  5486–5664; ELLIOT, lane RC7-determinant): constants `c_det = a + 4(h_K + 2c_E + 2t_K)` and
  `d_K` fixed with `K` (before `M` and `b`), and, for the determinant precision `M` and the final
  family (chosen after `M`), `f, d ∈ 𝒪[G]` with
  `f_x ũ_x = d_x` at every character, `f_0 ∈ Λ`, `v₂ f_0(0) ≤ c_det`, and negative Laurent support
  of every `f_x` modulo `2^M` bounded by `L_T(M) = 16(d_K + 5)M`. -/
  clearing : ∃ cdet dK : ℕ, ∀ M : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∃ f d : GrpRingO F.b,
      (∀ x : Addr F.b, MulRel (evalCoeff f x) (D.uTilde F x) (evalCoeff d x)) ∧
      (∀ i : ℤ, i < 0 → evalCoeff f 0 i = 0) ∧
      v2 (evalCoeff f 0 0 : ℚ_[2]) ≤ (cdet : ℤ) ∧
      ∀ x : Addr F.b, ∀ i : ℤ, i < -((16 * (dK + 5) * M : ℕ) : ℤ) →
        (2 : ℤ_[2]) ^ M ∣ evalCoeff f x i
  /-- **The base-zero lemma** (Lemma `ex:arith-base-zero`, lines 4319–4373; ELLIOT, with the
  conductor-one height formula of Cai–Shu–Tian Thm 1.1 as PRINT (separate project task); lane
  RC15-central): with `L(E^{(k)}, 1) ≠ 0` and
  `s₂(E/K) = 1`, if `L'(E/K, 1) = 0` then `ũ_0(0) = 0`. -/
  base_zero : SelmerCorankOneOverK ℓ D.kfin → CentralNonzero (Etw ℓ D.kfin) →
    LKDerivZero (Eℓ ℓ) D.kfin → ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
      central (D.uTilde F 0) = 0

end ZInQ.Manuscript.RC

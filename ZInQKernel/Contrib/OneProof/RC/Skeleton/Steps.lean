import ZInQKernel.Contrib.OneProof.RC.Skeleton.Setup

/-!
# Theorem 5.3, Lane RC0: Elliot's finer steps behind `BranchPackageNode`, one `Prop` each

The blueprint's node `ZInQ.Contrib.CloudB3RC53.BranchPackageNode` (Branch 1, or the fixed-field
package `FixedFieldPackage` of Branch 2) bundles Sections 7–9 and Appendices E–G of the 11/5
manuscript (`diophantine_zq.tex`). This file states the inputs from which `Skeleton.lean` proves
that node, following Elliot's text: one `Prop` per input, named after the manuscript, with its tex
lines, its kind and the lane expected to discharge it. Kinds: `PRINT` (a printed theorem taken as
a leaf), `ELLIOT` (Elliot's own step, stated, not proved here), `GLUE` (textbook fact). The
printed leaves already stated by the blueprint (`Prints`: BCDT Theorem A, Kolyvagin Theorem 1,
Dokchitser–Dokchitser, Cai–Shu–Tian) are used, not restated.

## The inputs, with tex lines, kind and the lane expected to discharge each

| input | tex | kind | lane |
|---|---|---|---|
| `Prints` (blueprint: `bcdt`, `kolyvagin`) | 1086–1108, used 2627–2628 | PRINT | RC8 / RC9 (stated by batch 3) |
| `KummerCorankZero` | 1101–1104 | GLUE (Kummer sequence) | RC9 |
| `RCSteps.lstar_ne_zero_iff` | 1825–1830 | ELLIOT/GLUE | RC11-even |
| `RCSteps.genus_partner` | 2404–2406 | ELLIOT | RC13-nonvanishing |
| `RCSteps.visibility` (O.8) | 9407–9445 | ELLIOT + PRINT (CST 1.1; Cornut–Jetchev 3.1) | RC12-odd |
| `RCSteps.stages_advance` | 2491–2500, 2536–2551 | ELLIOT | batch 3 (GenusOdd) |
| `RCSteps.one_admissible` | 2595 | ELLIOT | RC12-odd |
| `RCSteps.companion` | 2604–2613 | ELLIOT | RC2 / RC11 / RC13 |
| `RCSteps.gz_comparison` (3.4) | 2427–2439, 2713–2714 | PRINT (CST 1.1) + ELLIOT | batch 3 (GenusOdd) |
| `RCSteps.final_family` (3.9) | 2695–2715, 10792–10858 | ELLIOT | batch 3 (AppGEndpoints), with RC2 / RC3 / RC11 / RC12 / RC13 |
| `RCSteps.calibration` (4.6) | 3989–4140 | ELLIOT (+ Kolyvagin, Milne, Edixhoven) | RC15-central |
| `RCSteps.common_coordinate` (4.7) | 4142–4317 | ELLIOT | RC15-central (RC4) |
| `RCSteps.height_one` | 4909–5205, 5703–5704 | ELLIOT | RC16-uniform |
| `RCSteps.clearing` (5.9) | 5486–5664 | ELLIOT | RC7-determinant (batch 3: RankCounts, PairedFunctional) |
| `RCSteps.base_zero` | 4319–4373 | ELLIOT + PRINT (CST 1.1) | RC15-central |

## The interface data `RCData ℓ`

Heegner points, theta coefficients, Kato/Heegner determinant coordinates and normalized central
values do not exist in Mathlib. `RCData ℓ` collects them for the fixed curve `E = E_ℓ` as abstract
data: their only meaning is what the `Prop`s below say about them, and each such `Prop` says what
the manuscript proves about the genuine object.

| field | manuscript object | tex |
|---|---|---|
| `S` | the fixed support (primes of `2N`, `h_*`, `k`, the theta prime, exclusions) | 1790–1793, 2700 |
| `prepared h` | `h` lies in the prepared filter containing one (fixed local types at `2N`, prime to the support) | 2404–2410, 2700–2702 |
| `Lstar h` | normalized central value `L_*(h)` of `E^{(h)}` | 1825–1830 |
| `jgen h` | index valuation `j_gen(h)` of the genus point `P_h^{gen}` | 2411–2418 |
| `jrc h k` | index valuation `j_rc(h,k)` of the ring-class point `P_{h,k}^{rc}` | 2411–2418 |
| `hstar` | the negative genus partner `h_*` | 2404–2406 |
| `stages`, `Mθ`, `aθ`, `admissible` | the nonprincipal ultrafilter on actual theta stages, the precision `M_θ`, the phase-removed odd coefficients `a_{M_θ}(D)`, the stage support `(D/ℓ₀) = 1` | 2491–2551 |
| `δo` | the odd ultrafilter minimum `δ = δ_o` | 2536–2551 |
| `kfin` | the final companion `k`, `K = ℚ(√k)` | 2604–2613 |
| `uPrim F x`, `uTilde F x` | the primitive coordinate `u_{prim,x}` and the corrected coordinate `ũ_x = (η u_{rel})_x`, for the fixed `K` and the binary family `F`, in `ℚ₂[[t]]` | 3882–3892, 4142–4317 |
-/

noncomputable section

namespace ZInQ.Manuscript.RC

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 Filter Topology

attribute [local instance] Nat.fact_prime_two

/-- `E^{(h)}` for the fixed curve `E = E_ℓ` and an integer `h` (`qtwist_curve`: it is `E_{hℓ}`). -/
abbrev Etw (ℓ : ℕ) (h : ℤ) : WeierstrassCurve ℚ := qtwist (Ecurve ℓ) (h : ℚ)

/-- `E_ℓ^{(h)} = E_{hℓ}` (PROVED). -/
theorem Etw_eq (ℓ : ℕ) (h : ℤ) : Etw ℓ h = curve ((h : ℚ) * ℓ) := qtwist_curve _ _

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
odd symbol `A_o(D) = [v₂ a(D) = δ_o + ω(D)]` (Definition `ex:sec7-symbol`, 2069–2078) at `D = 1`,
as an ultrafilter limit over the stages: `v₂ a_{M_θ}(1) = δ_o` on a set of stages in the
ultrafilter. -/
def OddEmptyUnit : Prop :=
  ∀ᶠ θ in (D.stages : Filter ℕ), vZ (D.aθ θ 1) = D.δo

/-- **The family satisfies (3.9)** for the fixed `k` with constants `C_o, C_e`
(Proposition `ex:sec7-final-family`, lines 2695–2715; App G `ex:app-final-family`, 10792–10858):
`F` is admissible (good odd primes outside the support, split in `K`, nonzero `λ_q`), and at every
nonzero address `h_x` keeps the fixed local types (`prepared`), `ord_{s=1} L(E^{(h_x)},s) = 1`,
`L_*(h_x k) ≠ 0`, `j_gen(h_x) ≤ ω(h_x) + C_o`, `v₂ L_*(h_x k) ≤ 2ω(h_x) + C_e`. -/
def FinalFamilyAt (Co Ce : ℤ) (F : Family) : Prop :=
  F.Admissible D.S D.kfin ∧ ∀ x : Addr F.b, x ≠ 0 →
    D.prepared (F.h x) ∧ AnalyticRank (Etw ℓ (F.h x)) 1 ∧ D.Lstar (F.h x * D.kfin) ≠ 0 ∧
    D.jgen (F.h x) ≤ omega (F.h x) + Co ∧
    padicValRat 2 (D.Lstar (F.h x * D.kfin)) ≤ 2 * omega (F.h x) + Ce

end RCData

/-- **`s₂(E/K) = 1`** for `K = ℚ(√k)`, stated over the twist (lines 2627–2647): the
sum-and-difference isogeny gives `s₂(E/K) = s₂(E/ℚ) + s₂(E^{(k)}/ℚ)`, so `s₂(E/K) = 1` is
`corank Sel_{2^∞}(E/ℚ) = 1` together with `corank Sel_{2^∞}(E^{(k)}/ℚ) = 0`. (DEPARTURE of form:
the Selmer group over `K` is not defined; its corank is replaced by the two rational coranks, which
is the identity Elliot proves and uses.) -/
def SelmerCorankOneOverK (ℓ : ℕ) (k : ℤ) : Prop :=
  SelmerCorankOne (Ecurve ℓ) ∧ Z2Corank (selmerTwoPower (Etw ℓ k)) 0

/-- **The Kummer sequence in rank zero** (GLUE; `lem:forward-rank`, lines 1101–1104: "the ordinary
Kummer sequence `0 → A(ℚ) ⊗ ℚ₂/ℤ₂ → Sel_{2^∞}(A/ℚ) → Ш(A/ℚ)[2^∞] → 0` gives the corank
assertion"; Silverman X.4; lane RC9): rank zero and finite `Ш` give `corank Sel_{2^∞} = 0`. With
the blueprint's Kolyvagin leaf (`Prints.kolyvagin`, `r = 0`) it is the forward theorem used at
2627–2628. -/
def KummerCorankZero : Prop :=
  ∀ A : WeierstrassCurve ℚ, A.IsElliptic → Module.rank ℤ A.toAffine.Point = 0 →
    Finite (sha A) → Z2Corank (selmerTwoPower A) 0

/-- **The inputs of the deduction about the data `D`, one field per step.** -/
structure RCSteps {ℓ : ℕ} (D : RCData ℓ) : Prop where
  /-- **Normalized central values** (lines 1825–1830; ELLIOT/GLUE, the normalization by the fixed
  periods; lane RC11-even): `L_*(h) = 0` exactly when `L(E^{(h)}, 1) = 0`. -/
  lstar_ne_zero_iff : ∀ h : ℤ, h ≠ 0 → (D.Lstar h ≠ 0 ↔ AnalyticRank (Etw ℓ h) 0)
  /-- **The genus partner** (lines 2404–2406; ELLIOT, via the nonvanishing proposition; lane
  RC13-nonvanishing): `h_* < 0` with `L_*(h_*) ≠ 0`. -/
  genus_partner : D.hstar < 0 ∧ D.Lstar D.hstar ≠ 0
  /-- **Visibility (O.8)** (App F `ex:app-visibility`, lines 9407–9445; ELLIOT, resting on
  Cai–Shu–Tian Thm 1.1 and (3.8) via Cornut–Jetchev Thm 3.1; lane RC12-odd): one constant
  `C_det` such that at every stage and admissible `D`, `v₂ a_M(D) < M` implies
  `ord_{s=1} L(E^{(D)}, s) = 1` and `j_gen(D) ≤ v₂ a_M(D) + C_det`. -/
  visibility : ∃ Cdet : ℤ, ∀ θ : ℕ, ∀ Dd : ℤ, D.admissible θ Dd → vZ (D.aθ θ Dd) < D.Mθ θ →
    AnalyticRank (Etw ℓ Dd) 1 ∧ (D.jgen Dd : WithTop ℤ) ≤ vZ (D.aθ θ Dd) + Cdet
  /-- **Arbitrarily advanced stages** (lines 2491–2500, (3.7), and the nonprincipal ultrafilter,
  2536–2551; ELLIOT; batch 3, GenusOdd): `M_θ → ∞` along the ultrafilter. -/
  stages_advance : Tendsto D.Mθ (D.stages : Filter ℕ) atTop
  /-- **`D = 1` lies in every moving support** (line 2595; ELLIOT; lane RC12-odd):
  `(1/ℓ₀) = 1`. -/
  one_admissible : ∀ θ : ℕ, D.admissible θ 1
  /-- **The final companion** (lines 2604–2613; ELLIOT: a unit `k` of a separate even symbol on
  negative discriminants square at `2N`, so `L(E^{(k)}, 1) ≠ 0`; lanes RC2-symbols, RC11-even,
  RC13-nonvanishing). Used only in the remaining branch. `k` is a negative squarefree integer,
  `K = ℚ(√k) ≠ ℚ(i), ℚ(√−3)`, the primes of `k` lie in the fixed support, `L(E^{(k)},1) ≠ 0`. -/
  companion : ¬ D.OddEmptyUnit → D.kfin < 0 ∧ Squarefree D.kfin ∧ D.kfin ≠ -1 ∧
    D.kfin ≠ -3 ∧ (∀ p : ℕ, p.Prime → (p : ℤ) ∣ D.kfin → p ∈ D.S) ∧
    AnalyticRank (Etw ℓ D.kfin) 0
  /-- **The Gross–Zagier comparison (3.4) with the fixed `k`** (lines 2427–2439, used at 2713–2714
  and App G 10868–10872; PRINT: Cai–Shu–Tian, Algebra & Number Theory 8 (2014), Theorem 1.1 (the
  blueprint's `CST.CSTThm11Split`), applied twice, plus ELLIOT's index-at-most-two comparison;
  batch 3, GenusOdd): for a known simple zero `h` of the prepared filter, prime to the support,
  with every prime of `h` split in `K` and `L_*(hk) ≠ 0`,
  `2j_rc(h,k) − 2j_gen(h) = v₂L_*(hk) − v₂L_*(h_*) + ε`, `|ε| ≤ 2`, "up to the one fixed initial
  period convention": that convention is the constant `C_per` (in App G it is part of
  `C_{H,final}`). -/
  gz_comparison : ∃ Cper : ℤ, ∀ h : ℤ, D.prepared h → AnalyticRank (Etw ℓ h) 1 →
    D.Lstar (h * D.kfin) ≠ 0 →
    (∀ q : ℕ, q.Prime → (q : ℤ) ∣ h → q ∉ D.S ∧ jacobiSym D.kfin q = 1) →
    ∃ ε : ℤ, |ε| ≤ 2 ∧ 2 * D.jrc h D.kfin - 2 * D.jgen h =
      padicValRat 2 (D.Lstar (h * D.kfin)) - padicValRat 2 (D.Lstar D.hstar) + Cper + ε
  /-- **The final family (3.9)** (Proposition `ex:sec7-final-family`, lines 2695–2715, App G
  10792–10858; ELLIOT; batch 3, AppGEndpoints, with lanes RC2-symbols (addresses), RC3-ksplit (the
  K-split seed), RC12-odd, RC11-even, RC13-nonvanishing). In the remaining branch, constants
  `C_o, C_e` fixed before `b`, and for every sufficiently large `b` one family over `𝔽₂^b`
  satisfying (3.9). -/
  final_family : ¬ D.OddEmptyUnit → ∃ Co Ce : ℤ, ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
    ∃ F : Family, F.b = b ∧ D.FinalFamilyAt Co Ce F
  /-- **The central calibration (4.6)** (Proposition `ex:arith-central-calibration`, lines
  3989–4140; ELLIOT, resting on `lem:forward-rank` (Kolyvagin Thm 1, PRINT), Milne ADT I.7.3
  (7.3.1) and Edixhoven Thm 5.3 / Rem 5.4.1 (lane RC9); lane RC15-central): one error bound
  `C_cal` such that at a known simple zero `h_x` with `L(E^{(h_x k)}, 1) ≠ 0`,
  `v₂ u_{prim,x}(0) = 2j_rc(h_x,k) − 4ω(h_x) − s(h_x) − s(h_x k) − Σ_{p|k} t_p + O(1)`,
  `0 ≤ t_p ≤ 2`. -/
  calibration : ∃ Ccal : ℤ, ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 →
      ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ Ccal ∧
        v2 (central (D.uPrim F x)) =
          ((2 * D.jrc (F.h x) D.kfin - 4 * omega (F.h x) - shaLength (Etw ℓ (F.h x)) -
            shaLength (Etw ℓ (F.h x * D.kfin)) - ∑ p ∈ D.kfin.natAbs.primeFactors, (t p : ℤ) +
              err : ℤ) : WithTop ℤ)
  /-- **The unused-prime comparison (4.7)** (Lemma `ex:arith-common-coordinate`, lines
  4142–4317; ELLIOT; lane RC15-central, with RC4-moving for the moving character): the corrected
  coordinate is a `Λ`-unit multiple of the primitive one at every character,
  `ũ_x = ε_x u_{prim,x}` with `ε_x ∈ Λ^×`. -/
  common_coordinate : ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    ∃ ε : PowerSeries ℚ_[2], LamUnit ε ∧ D.uTilde F x = ε * D.uPrim F x
  /-- **Height-one regularity** (lines 5703–5704 "by the height-one argument above", from
  Proposition `ex:limits-uniform-lower-bound`, 4909–5205; ELLIOT; lane RC16-uniform): every
  `ũ_x` of the final family lies in `Λ[1/2]`. -/
  height_one : ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    InLamHalf (D.uTilde F x)
  /-- **Determinant clearing (5.9)** (Proposition `ex:limits-fixed-field-clearing`, lines
  5486–5664; ELLIOT; lane RC7-determinant, with batch 3's RankCounts (5.7) and
  PairedFunctional (the exponent `a`)): constants `c_det = a + 4(h_K + 2c_E + 2t_K)` and `d_K`
  fixed with `K` (before `M` and `b`), and, for the determinant precision `M` and the final family
  (chosen after `M`), coefficient data of `f = 2^a Δ⁴, d = η Δ Q ∈ 𝒪[G]` with the coordinates
  `ũ_x` of the family, `f` in `𝒪[G]` (coefficients tending to `0` at `−∞`), `f_x ũ_x = d_x` at
  every character, negative Laurent support of every `f_x` modulo `2^M` bounded by
  `L_T(M) = 16(d_K + 5)M`, `f_0 ∈ Λ` and `c = v₂ f_0(0) ≤ c_det`. In the blueprint's vocabulary
  (`CoordData`, `signEval`, `PoleBound`, `BaseRegular`). -/
  clearing : ∃ cdet dK : ℕ, ∀ M : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∃ (C : CoordData F.b) (c : ℕ),
      (∀ x j, C.u x j = PowerSeries.coeff j (D.uTilde F x)) ∧ c ≤ cdet ∧
      (∀ g, Tendsto (C.F g) atBot (𝓝 0)) ∧
      (∀ x (n : ℤ), HasSum (fun j : ℕ => (signEval C.F x (n - j) : ℚ_[2]) * C.u x j)
        (signEval C.D x n : ℚ_[2])) ∧
      PoleBound C (16 * (dK + 5) * M) M ∧ BaseRegular C c
  /-- **The base-zero lemma** (Lemma `ex:arith-base-zero`, lines 4319–4373; ELLIOT, with the
  conductor-one height formula of Cai–Shu–Tian Thm 1.1 as PRINT; lane RC15-central): with
  `L(E^{(k)}, 1) ≠ 0` and `s₂(E/K) = 1`, if `L'(E/K, 1) = 0` (here: the blueprint's
  `ProductOrderGeTwo`, which is `L'(E/K,1) = 0` together with `L(E/K,1) = 0`) then
  `ũ_0(0) = 0`. -/
  base_zero : SelmerCorankOneOverK ℓ D.kfin → AnalyticRank (Etw ℓ D.kfin) 0 →
    ProductOrderGeTwo (Ecurve ℓ) D.kfin → ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
      central (D.uTilde F 0) = 0

end ZInQ.Manuscript.RC

import ZInQKernel.Contrib.OneProof.RC.Skeleton.Setup

/-!
# Theorem 5.3, Lane RC0: Elliot's finer steps behind `BranchPackageNode`, one `Prop` each

The blueprint's node `ZInQ.Contrib.CloudB3RC53.BranchPackageNode` (Branch 1, or the fixed-field
package `FixedFieldPackage` of Branch 2) bundles Sections 7–9 and Appendices E–G of the 11/5
manuscript (`diophantine_zq.tex`). This file states the inputs from which `Skeleton.lean` proves
that node, following Elliot's text: one `Prop` per input, named after the manuscript, with its tex
lines, its kind and the lane expected to discharge it. Kinds: `PRINT` (a printed theorem taken as
a leaf), `ELLIOT` (Elliot's own step, stated, not proved here), `GLUE` (textbook fact or cited
statement). The cited results already stated by the blueprint (`Prints`: the printed leaves BCDT
Theorem A, Dokchitser–Dokchitser and Cai–Shu–Tian, and Kolyvagin Theorem 1, a cited statement,
GLUE: its source is the MPIM preprint MPI/90-69) are used, not restated.

## The inputs, with tex lines, kind and the lane expected to discharge each

| input | tex | kind | lane |
|---|---|---|---|
| `Prints` (blueprint: `bcdt`, `kolyvagin`) | 1086–1108, used 2616–2626 | PRINT (BCDT Thm A) + GLUE (Kolyvagin Thm 1) | RC8 / RC9 (stated by batch 3) |
| `KummerCorankZero` | 1098–1104 | GLUE (Kummer sequence) | RC9 |
| `RCSteps.lstar_ne_zero_iff` | 1825–1830 | ELLIOT/GLUE | RC11-even |
| `RCSteps.genus_partner` | 2404–2408 | ELLIOT | RC13-nonvanishing |
| `RCSteps.visibility` (O.8) | 9407–9445 | ELLIOT + PRINT (CST 1.1; Cornut–Jetchev 3.1) | RC12-odd |
| `RCSteps.stages_advance` | App G 10190–10191, App F 8233, 8400–8401 | definition (PROVED from `PreDataSpec`) | batch 3 (GenusOdd) |
| `RCSteps.one_admissible` | 2586 (App F 8209–8212) | definition (PROVED from `PreDataSpec`) | RC12-odd |
| `RCSteps.companion` | 2595–2603 (2720–2721) | ELLIOT | RC2 / RC11 / RC13 |
| `RCSteps.gz_comparison` (3.4) | 2436–2440, 2692–2693 | PRINT (CST 1.1) + ELLIOT | batch 3 (GenusOdd) |
| `RCSteps.final_family` (3.9) | 2674–2712, 10792–10858 | ELLIOT | batch 3 (AppGEndpoints), with RC2 / RC3 / RC11 / RC12 / RC13 |
| `RCSteps.calibration` (4.6) | 3987–4141 | ELLIOT (+ Kolyvagin, Milne, Edixhoven) | RC15-central |
| `RCSteps.common_coordinate` (4.7) | 4142–4328 | ELLIOT | RC15-central (RC4) |
| `RCSteps.height_one` | 4909–5205, 5703–5704 | ELLIOT | RC16-uniform |
| `RCSteps.clearing` (5.9) | 5487–5645 | ELLIOT | RC7-determinant (batch 3: RankCounts, PairedFunctional) |
| `RCSteps.base_zero` | 4330–4376 | ELLIOT + PRINT (CST 1.1) | RC15-central |

DEPARTURE (scope): `calibration`, `common_coordinate`, `height_one`, `clearing` and `base_zero` are
demanded in both branches. The text constructs `k`, the family and the coordinates only in the
remaining branch (tex 2589–2593; (5.6)–(5.9) are stated "in the branch where the odd empty
configuration is not a unit", 5209–5211, 5228–5229). A discharge chooses the companion of tex
2595–2600 in Branch 1 as well; that choice does not use the branch hypothesis.

## The interface data `RCData ℓ`

Heegner points, theta coefficients, Kato/Heegner determinant coordinates and normalized central
values do not exist in Mathlib. `RCData ℓ` collects them for the fixed curve `E = E_ℓ` as abstract
data: their only meaning is what the `Prop`s below say about them, and each such `Prop` says what
the manuscript proves about the genuine object.

| field | manuscript object | tex |
|---|---|---|
| `S` | the fixed support: the primes of `2N`, of `h_*` and of the final `k`, and the fixed exclusions (the stage's theta prime `ℓ₀` is not in `S`; it enters through `admissible θ`). DEPARTURE (order): since `S` contains the primes of `k`, the prepared filter, the stage support, `δ_o` and the constants of (3.3)–(3.6) are formed after `k` is fixed, whereas the text fixes `K` after the odd minimum (2703–2704) and shows that omitting the primes of `k` preserves it (2602–2603, 2611–2612) | 2016–2025, 2376–2378, 2407–2408, 10291–10293 |
| `prepared h` | `h` lies in the prepared filter containing one (fixed local types at `2N`, prime to the support) | 2404–2410, 2678–2680 |
| `Lstar h` | normalized central value `L_*(h)` of `E^{(h)}` | 1825–1830 |
| `jgen h` | index valuation `j_gen(h)` of the genus point `P_h^{gen}` | 2411–2418 |
| `jrc h k` | index valuation `j_rc(h,k)` of the ring-class point `P_{h,k}^{rc}` | 2411–2418 |
| `hstar` | the negative genus partner `h_*` | 2404–2408 |
| `stages`, `Mθ`, `aθ`, `admissible` | the nonprincipal ultrafilter on actual theta stages, the precision `M_θ`, the phase-removed odd coefficients `a_{M_θ}(D)`, the stage support `(D/ℓ₀) = 1` | 2491–2551 |
| `δo` | the odd ultrafilter minimum `δ = δ_o` | 2536–2551 |
| `kfin` | the final companion `k`, `K = ℚ(√k)` | 2595–2603 |
| `uPrim F x`, `uTilde F x` | the primitive coordinate `u_{prim,x}` and the corrected coordinate `ũ_x = (η u_{rel})_x`, for the fixed `K` and the binary family `F`, in `ℚ₂[[t]]` (DEPARTURE: regular at `t = 0`; faithful where the text proves regularity, at `x ≠ 0` of a final family and at `x = 0` under full Selmer corank one for `E/K` (`s₂(E/K) = 1`, which holds in Branch 2 for the chosen `k`, tex 2616–2626), tex 4153–4155, 4922–4923, 5196–5199, 5703–5704) | 3882–3892, 4142–4328 |
-/

noncomputable section

namespace ZInQ.Manuscript.RC

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 Filter Topology

attribute [local instance] Nat.fact_prime_two

/-- `E^{(h)}` for the fixed curve `E = E_ℓ` and an integer `h` (`qtwist_curve`: it is `E_{hℓ}`). -/
abbrev Etw (ℓ : ℕ) (h : ℤ) : WeierstrassCurve ℚ := qtwist (Ecurve ℓ) (h : ℚ)

/-- `E_ℓ^{(h)} = E_{hℓ}` (PROVED). -/
theorem Etw_eq (ℓ : ℕ) (h : ℤ) : Etw ℓ h = curve ((h : ℚ) * ℓ) := qtwist_curve _ _

/-- **`d` is a unit square at the prime `p`**: `p ∤ d` and `d` is a square modulo `p` (`p` odd), or
`d ≡ 1 (mod 8)` (`p = 2`); for `p ∤ d` this is "`d` is a square in `ℚ_p`" (Hensel). The same body as
the shared layer's `GenusOdd.SquareAt` (tex 2350–2352, 2405–2406). -/
def UnitSquareAt (p : ℕ) (d : ℤ) : Prop :=
  ¬ (p : ℤ) ∣ d ∧ (p = 2 → d % 8 = 1) ∧ (p ≠ 2 → IsSquare (d : ZMod p))

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
  /-- the phase-removed odd coefficients `a_{M_θ}(D)` at stage `θ`: an integer representative
  modulo `2^{M_θ}` (tex 2080–2082); every reader depends only on the residue -/
  aθ : ℕ → ℤ → ℤ
  /-- the stage support: `D` admissible at stage `θ` with `(D/ℓ₀) = 1`. DEPARTURE unless App F's
  "prescribed unit classes" (tex 8209–8210) include the class of 1 at the primes of `h_*`: the
  stage support carries the added unit-squareclass condition of 1 at those primes (tex 8564–8565,
  9094–9095). The fixed witness `D_w` satisfies it (tex 8254–8258), and `δ_o` is the minimum of
  that source. -/
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

/-- **The intrinsic odd limit symbol is a unit at the empty configuration** (lines 2584–2585, App G
10236–10243, 10508–10517): the
odd symbol `A_o(D) = [v₂ a(D) = δ_o + ω(D)]` (Definition `ex:sec7-symbol`, 2069–2078) at `D = 1`,
as an ultrafilter limit over the stages: `v₂ a_{M_θ}(1) = δ_o` on a set of stages in the
ultrafilter. -/
def OddEmptyUnit : Prop :=
  ∀ᶠ θ in (D.stages : Filter ℕ), vZ (D.aθ θ 1) = D.δo

/-- **The family satisfies (3.9)** for the fixed `k` with constants `C_o, C_e`
(Proposition `ex:sec7-final-family`, statement 2674–2694, proof 2695–2712; App G
`ex:app-final-family`, 10792–10858):
`F` is admissible (good odd primes outside the support, split in `K`, nonzero `λ_q`), and at every
nonzero address `h_x` keeps the fixed local types (`prepared`), `ord_{s=1} L(E^{(h_x)},s) = 1`,
`L_*(h_x k) ≠ 0`, `j_gen(h_x) ≤ ω(h_x) + C_o`, `v₂ L_*(h_x k) ≤ 2ω(h_x) + C_e`.
DEPARTURE: the text's family also has a terminal of every nonzero activation (tex 2243–2245,
10561–10562), so `h_x ≠ 1` at `x ≠ 0`; `FinalFamilyAt` omits this, so the steps quantified over
final families also range over families with `h_x = 1` at some `x ≠ 0`. The predicate permits
dimension zero and repeated members: an empty prime set gives `h_x = 1` at every address, and in
positive dimension its rank-one clause then requires analytic rank one of the base curve. -/
def FinalFamilyAt (Co Ce : ℤ) (F : Family) : Prop :=
  F.Admissible D.S D.kfin ∧ ∀ x : Addr F.b, x ≠ 0 →
    D.prepared (F.h x) ∧ AnalyticRank (Etw ℓ (F.h x)) 1 ∧ D.Lstar (F.h x * D.kfin) ≠ 0 ∧
    D.jgen (F.h x) ≤ omega (F.h x) + Co ∧
    padicValRat 2 (D.Lstar (F.h x * D.kfin)) ≤ 2 * omega (F.h x) + Ce

end RCData

/-- **`s₂(E/K) = 1`** for `K = ℚ(√k)`, stated over the twist (lines 2616–2626): the
sum-and-difference isogeny gives `s₂(E/K) = s₂(E/ℚ) + s₂(E^{(k)}/ℚ)`, so `s₂(E/K) = 1` is
`corank Sel_{2^∞}(E/ℚ) = 1` together with `corank Sel_{2^∞}(E^{(k)}/ℚ) = 0`. (DEPARTURE of form:
the Selmer group over `K` is not defined; its corank is replaced by the two rational coranks, which
is the identity Elliot proves and uses.) -/
def SelmerCorankOneOverK (ℓ : ℕ) (k : ℤ) : Prop :=
  SelmerCorankOne (Ecurve ℓ) ∧ Z2Corank (selmerTwoPower (Etw ℓ k)) 0

/-- **The Kummer sequence in rank zero** (GLUE; `lem:forward-rank`, lines 1098–1104: "the ordinary
Kummer sequence `0 → A(ℚ) ⊗ ℚ₂/ℤ₂ → Sel_{2^∞}(A/ℚ) → Ш(A/ℚ)[2^∞] → 0` gives the corank
assertion"; Silverman X.4; lane RC9): rank zero and finite `Ш` give `corank Sel_{2^∞} = 0`. With
the blueprint's Kolyvagin statement (`Prints.kolyvagin`, `r = 0`; a cited statement, GLUE: its
source is the MPIM preprint MPI/90-69) it is the forward theorem used at 2616–2626. -/
def KummerCorankZero : Prop :=
  ∀ A : WeierstrassCurve ℚ, A.IsElliptic → Module.rank ℤ A.toAffine.Point = 0 →
    Finite (sha A) → Z2Corank (selmerTwoPower A) 0

/-- **The inputs of the deduction about the data `D`, one field per step.** -/
structure RCSteps {ℓ : ℕ} (D : RCData ℓ) : Prop where
  /-- **Normalized central values** (lines 1825–1830; ELLIOT/GLUE, the normalization by the fixed
  periods; lane RC11-even): `L_*(h) = 0` exactly when `L(E^{(h)}, 1) = 0`. -/
  lstar_ne_zero_iff : ∀ h : ℤ, h ≠ 0 → (D.Lstar h ≠ 0 ↔ AnalyticRank (Etw ℓ h) 0)
  /-- **The genus partner** (lines 2404–2408; ELLIOT, via the nonvanishing proposition; lane
  RC13-nonvanishing): `h_* < 0` with `L_*(h_*) ≠ 0`. -/
  genus_partner : D.hstar < 0 ∧ D.Lstar D.hstar ≠ 0
  /-- **Visibility (O.8)** (App F `ex:app-visibility`, lines 9407–9445; ELLIOT, resting on
  Cai–Shu–Tian Thm 1.1 and (3.8) via Cornut–Jetchev Thm 3.1; lane RC12-odd): one constant
  `C_det` such that at every stage and admissible `D`, `v₂ a_M(D) < M` implies
  `ord_{s=1} L(E^{(D)}, s) = 1` and `j_gen(D) ≤ v₂ a_M(D) + C_det`. -/
  visibility : ∃ Cdet : ℤ, ∀ θ : ℕ, ∀ Dd : ℤ, D.admissible θ Dd → vZ (D.aθ θ Dd) < D.Mθ θ →
    AnalyticRank (Etw ℓ Dd) 1 ∧ (D.jgen Dd : WithTop ℤ) ≤ vZ (D.aθ θ Dd) + Cdet
  /-- **Arbitrarily advanced stages** ((3.7) and the nonprincipal ultrafilter: App G 10190–10191,
  App F 8233, 8400–8401; ELLIOT; batch 3, GenusOdd): `M_θ → ∞` along the ultrafilter. -/
  stages_advance : Tendsto D.Mθ (D.stages : Filter ℕ) atTop
  /-- **`D = 1` lies in every moving support** (line 2586, App F 8209–8212; ELLIOT; lane RC12-odd):
  `(1/ℓ₀) = 1`. -/
  one_admissible : ∀ θ : ℕ, D.admissible θ 1
  /-- **The final companion** (lines 2595–2603, 2720–2721; ELLIOT: "a separate even symbol on
  negative discriminants square at `2N`, excluding the fixed odd support, the ramification support
  of `E[8]`, and the exceptional imaginary fields. Choose a unit `k` of this symbol. Then
  `L(E^{(k)},1) ≠ 0`"; lanes RC2-symbols, RC11-even, RC13-nonvanishing). Used only in the remaining
  branch. Recorded: `k` is a negative squarefree integer, `k ≡ 1 (mod 4)` and a unit square at
  every prime of `2N` (a negative odd fundamental discriminant square at `2N`, as for the companions
  of tex 2349–2352), `K = ℚ(√k) ≠ ℚ(i), ℚ(√−3)`, the primes of `k` lie in the fixed support, `k` is
  prime to `h_*` (the fixed odd support contains the primes of `h_*`, tex 2460–2462), and
  `L(E^{(k)},1) ≠ 0`. The congruence, the squares at `2N` and the coprimality are the conditions
  under which Cai–Shu–Tian applies at the final `k` (used by the shared layer's GenusOdd). -/
  companion : ¬ D.OddEmptyUnit → D.kfin < 0 ∧ Squarefree D.kfin ∧ D.kfin ≠ -1 ∧
    D.kfin ≠ -3 ∧ (∀ p : ℕ, p.Prime → (p : ℤ) ∣ D.kfin → p ∈ D.S) ∧ D.kfin % 4 = 1 ∧
    (∀ p : ℕ, p.Prime → p ∣ 2 * CST.newformLevel (Ecurve ℓ) → UnitSquareAt p D.kfin) ∧
    IsCoprime D.kfin D.hstar ∧ AnalyticRank (Etw ℓ D.kfin) 0
  /-- **The Gross–Zagier comparison (3.4) with the fixed `k`** (lines 2436–2440, used at 2692–2693
  and App G 10871–10876; PRINT: Cai–Shu–Tian, Algebra & Number Theory 8 (2014), Theorem 1.1 (the
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
  /-- **The final family (3.9)** (Proposition `ex:sec7-final-family`, lines 2674–2712, App G
  10792–10858; ELLIOT; batch 3, AppGEndpoints, with lanes RC2-symbols (addresses), RC3-ksplit (the
  K-split seed), RC12-odd, RC11-even, RC13-nonvanishing). In the remaining branch, constants
  `C_o, C_e` fixed before `b`, and for every sufficiently large `b` one family over `𝔽₂^b`
  satisfying (3.9). -/
  final_family : ¬ D.OddEmptyUnit → ∃ Co Ce : ℤ, ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
    ∃ F : Family, F.b = b ∧ D.FinalFamilyAt Co Ce F
  /-- **The central calibration (4.6)** (Proposition `ex:arith-central-calibration`, lines
  3987–4141; ELLIOT, resting on `lem:forward-rank` (Kolyvagin Thm 1, cited statement, GLUE),
  Milne ADT I.7.3 (7.3.1) and Edixhoven Thm 5.3 / Rem 5.4.1 (lane RC9); lane RC15-central):
  one error bound
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
  4142–4328; ELLIOT; lane RC15-central, with RC4-moving for the moving character): the corrected
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
  5487–5645; ELLIOT; lane RC7-determinant, with batch 3's RankCounts (5.7) and
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
  /-- **The base-zero lemma** (Lemma `ex:arith-base-zero`, lines 4330–4376; ELLIOT, with the
  conductor-one height formula of Cai–Shu–Tian Thm 1.1 as PRINT; lane RC15-central): with
  `L(E^{(k)}, 1) ≠ 0` and `s₂(E/K) = 1`, if `L'(E/K, 1) = 0` (here: the blueprint's
  `ProductOrderGeTwo`, which is `L'(E/K,1) = 0` together with `L(E/K,1) = 0`) then
  `ũ_0(0) = 0`. -/
  base_zero : SelmerCorankOneOverK ℓ D.kfin → AnalyticRank (Etw ℓ D.kfin) 0 →
    ProductOrderGeTwo (Ecurve ℓ) D.kfin → ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
      central (D.uTilde F 0) = 0

end ZInQ.Manuscript.RC

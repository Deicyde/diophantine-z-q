# cm-bridge: CM leaves rewired to ring class field theory; `GenusFieldLeLni` proved; TYZ Lemma 3.21(4) reduced to TYZ Theorem 3.6(3) with all glue proved

Task cm-bridge, 2026-11-13. Lean: `scratch/cm-bridge/Bridge.lean` (imports the built
`ZInQKernel.Contrib.TYZGenus.RingClassBridge`; no `sorry`, no `axiom`; 2120 lines). Numerical check:
`scratch/cm-bridge/thm36_7.py` → `thm36_7.out` (PARI/GP via cypari2, 400 digits, helper `heeg.py` copied
from cm-numeric). Results log: `scratch/cm-bridge/log.md`. Axiom audit: `scratch/cm-bridge/audit-out.txt`.
Marks: **VERIFIED** (compiled, computed, or read in a named source), **STANDARD**, **SPECULATIVE**,
**UNVERIFIED** (theorem numbers from memory).

## 0. Main result

```lean
theorem tyzThm35ReadingA_of_ringClassD_sigmaShiftsF0_lemma318_thm35First_lemma321Five_thm36Seven
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hcm : CM.CMFieldOfDefinition ringClassFieldD) (hsh : TYZSigmaShiftsF0)
    (h318 : Lemma318Literal HHprime) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (h5 : Lemma321Five) (h36 : TYZThm36Seven) : ZInQ.Literature.TYZThm35ReadingA
```

(namespace `ZInQ.Contrib.TYZGenus.CMBridge`; VERIFIED compiled with `lake env lean`, axioms
`[propext, Classical.choice, Quot.sound]`.) Compared with cm-numeric's
`tyzThm35ReadingA_of_pinnedLeaves` (13 hypotheses), **seven hypotheses are gone**:

| cm-numeric hypothesis | status now | how |
|---|---|---|
| `IInH4` | proved | ring-class's `RingClassBridge.iInH4` |
| `HprimeNormal` | proved | ring-class's `RingClassBridge.hprimeNormal` |
| `CMFieldOfDefinitionTYZ` | derived from `CM.CMFieldOfDefinition ringClassFieldD` | `cmFieldTYZ_of_ringClassD` (ring-class) |
| `CMFieldOfDefinition7` | derived from `CM.CMFieldOfDefinition ringClassFieldD` | `cmFieldOfDefinition7_of` (§10; `ringClassFieldD_neg`) |
| `TYZSigmaFixesZn` | derived from `TYZSigmaShiftsF0` | `tyzSigmaFixesZn_of'` (§10; `IInHprime` now proved, `iInHprime` from `Lni_le_Hprimebar`) |
| `GenusFieldLeLni` | **proved** | `genusFieldLeLni` (§11) |
| `Lemma321Seven` (TYZ Lemma 3.21(4)) | **derived from TYZ Theorem 3.6(3)** (`TYZThm36Seven`) | `lemma321Seven_of'` (§12–§13; all glue proved) |

So both CM leaves of the class-7 branch collapse into the single general CM leaf that task tyz-cm
works on, and the class-7 genus-point lemma is replaced by the more primary printed theorem it is
derived from in TYZ.

## 1. Remaining leaves (the hypotheses of the main theorem)

| leaf | content | source | kind |
|---|---|---|---|
| `TYZThm11Integral`, `TYZLcalOne`, `TYZLemma29Mod2` | the `𝓛`-leaves | tyz-decomp (`ZInQKernel/Contrib/TYZDecomp/Leaves.lean`) | leaf (unchanged) |
| `CM.CMFieldOfDefinition ringClassFieldD` | Heegner points of discriminant `D` on `A = X₀(32)` lie in `A(ring class field of disc. D)` | Shimura reciprocity (Gross 1984 §3, Shimura 1971; UNVERIFIED numbers) | leaf; task tyz-cm |
| `TYZSigmaShiftsF0` | `Art(σ_{1+2ϖ}) f₀(P_n) = f₀(P_n) + (0,0)` | TYZ Prop. `heckeaction5`(1) L1488–1490 + Shimura reciprocity (cm-numeric; VERIFIED numerically there, 15 cases) | leaf (unchanged) |
| `Lemma318Literal HHprime` | torsion of `A(ℍ'_n)` is killed by `2(1+[i])` | TYZ Lemma `torsion2`, L2230 (VERIFIED read) | leaf (unchanged; §4) |
| `Thm35First ℓ tyzZ` | TYZ Thm 3.3/3.5 for the pinned genus points | TYZ | leaf (unchanged) |
| `Lemma321Five` | TYZ Lemma 3.21(1) for the pinned class-5 genus points | TYZ L2508–2510 | leaf (unchanged; §4) |
| `TYZThm36Seven` | **new**: `γ(z_n) + ρ(z_n) = τ(1/2)` for complex conjugation `γ` and `ρ|_{H_n} = Art([𝔭₂])^{−5}` | TYZ Theorem `CM point2`(3), L1424–1427 (VERIFIED read) | leaf; VERIFIED numerically (12/12) |

`TYZThm36Seven` in Lean (§12):

```lean
def PosOrient (n : ℕ) [NeZero n] : Prop :=
  0 < (ιC (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega))).im
def p2Ideal (n : ℕ) [NeZero n] : Ideal (𝓞 (QNeg n)) :=   -- (open Classical)
  if h : n % 4 = 3 then
    if PosOrient n then
      Ideal.span {2, ZInQ.RouteK.Redei.thetaO n h - (((tyzDelta n + 1) / 2 : ℕ) : 𝓞 (QNeg n))}
    else
      Ideal.span {2, 1 - ZInQ.RouteK.Redei.thetaO n h - (((tyzDelta n + 1) / 2 : ℕ) : 𝓞 (QNeg n))}
  else ⊤
def p2Class (n : ℕ) [NeZero n] : Pic (OK n) :=
  (ClassGroup.mk0 ⟨p2Ideal n, p2Ideal_mem n⟩ : ClassGroup (𝓞 (QNeg n)))
def IsComplexConj (γ : GalQ) : Prop := ∀ x : Qbar, ιC (γ x) = starRingEnd ℂ (ιC x)
def TYZThm36Seven : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 7 → Squarefree n → ∀ γ ρ : GalQ, IsComplexConj γ →
    ActsAsArtinO n (OK n) ρ ((p2Class n)⁻¹ ^ 5) →
      galPt γ (tyzZ7 n) + galPt ρ (tyzZ7 n) = tauG 1
```

* `𝔭₂` is the prime of `𝓞_{K_n}` whose image in `ℂ` (through ring-class's `embed n` and `CM`'s `ιC`)
  is `(2, (i√n − δ)/2)`, `δ = tyzDelta n`: `(2, (√−n − δ)/2) = (2, θ − (δ+1)/2)` if `ιC(embed √−n) = +i√n`
  (`PosOrient`), else its conjugate `(2, 1 − θ − (δ+1)/2)`. It is TYZ's place `v₂` with
  `v₂(√−n − δ) ≥ 6` (L1424; `(√−n − δ)/2 ∈ 𝔭₂`, its conjugate is not, `N((√−n−δ)/2) = (n+δ²)/4 ≡ 0
  (mod 32)`), with `√−n` read as `i√n` — the reading that the numerical check confirms (below);
  `N𝔭₂ = 2` is proved for both branches (`normP2`). **The orientation is essential**: the first version
  of this leaf used `(2, (√−n − δ)/2)` for the abstract `√−n`, so it depended on the arbitrary
  embedding `embed n` and was false for one of the two choices (independent review, §5); fixed.
* TYZ's `σ` is the geometric Artin map, uniformizers ↦ geometric Frobenius (L1247–1250, VERIFIED read),
  so `σ_{ϖ^5}` acts on the (unramified) Hilbert class field as `Frob_{v₂}^{−5} = Art([𝔭₂])^{−5}`;
  Tau Ceti's `ringClassArtinEquiv` is arithmetic (`isArithFrobAt_ringClassArtinEquiv_picClass`).
* `tyzZ7 n` is cm-numeric's pinned class-7 CM point (Heegner point of `[(n+δ²)/4, δ, 1]`, TYZ L1196,
  L1203–1205); `τ(1/2) = tauG 1 = (2, −4)`.
* Not vacuous: `exists_complexConj` and `exists_actsAsArtinO` (proved) give `γ` and `ρ`.
* **Numerical check** (`thm36_7.py`, VERIFIED computed): for the 12 squarefree `n ≡ 7 (mod 8)`,
  `7 ≤ n ≤ 103`, `conj(z_n) + ρ(z_n) − (2,−4) = 0` to 400 digits, with `ρ(z_n)` computed by Shimura
  reciprocity in the direction cm-numeric VERIFIED (`shimura.out`: `Art(𝔞)` sends the Heegner point of
  `[𝔟]` to that of `[𝔟𝔞⁻¹]`), i.e. `ρ(z_n)` = Heegner point (`B ≡ δ mod 64`) of the class `[𝔭₂]^5`. The
  opposite sign `Art([𝔭₂])^{+5}` fails for the 7 values with `[𝔭₂]^{10} ≠ 1` (n = 23, 31, 39, 55, 71,
  87, 95), so the sign is pinned by the data.

## 2. What is proved (Bridge.lean)

§0–§9: cm-numeric's `Class7.lean` verbatim (namespace renamed `CMNumeric → CMBridge`; the `rfl` checks of
§0 against cm-points' `Package` still compile).

**§10 rewiring.** `iInHprime : IInHprime` (`i ∈ L_n(i) ⊆ H'_n`, ring-class's `Lni_le_Hprimebar`);
`cmFieldOfDefinition7_of : CM.CMFieldOfDefinition ringClassFieldD → CMFieldOfDefinition7`
(`ringClassFieldD_neg`: for squarefree `n ≡ 3 (mod 4)` the ring class field of discriminant `−n` is
`H_n`); `tyzSigmaFixesZn_of' : TYZSigmaShiftsF0 → TYZSigmaFixesZn`; `tyzThm35ReadingA_of_rewired`.

**§11 `genusFieldLeLni : GenusFieldLeLni`** (genus field of `ℚ(√−e)`, squarefree `e ≡ 7 (mod 8)`, inside
`L_e(i) = ℚ(i, √p : p ∣ e)`). Proof: a prime `𝔭 ∤ 2e` of `K_e` split completely in
`K_e(i, √p : p ∣ e)` (`genusAmb`) has `−1` and every `p ∣ e` square mod `𝔭`; then `|O/𝔭| ≡ 1 (mod 4)` and
`|O/𝔭|` is a square mod `p` (`FiniteField.isSquare_odd_prime_iff`, Mathlib's quadratic reciprocity), so
every genus character `χ_p` (`RouteK.Redei.chi`) is trivial on `[𝔭]` (`chi_eq_one_of_isSquare`), so
`[𝔭] ∈ Cl²` (`picSquares_eq_iInf_ker_chi`), i.e. `𝔭` splits in the genus field; Bauer
(`le_of_splitSet_diff_subset`) gives `G_e ⊆ genusAmb`, and `genusAmb` maps into `L_e(i)` because it
contains `√−e = ±i∏√p` (`LniK`). New glue lemma: `picClass_maximal` (Tau Ceti's `picClass` for the
maximal order is `ClassGroup.mk0`).

**§12 `lemma321Seven_of : CMFieldOfDefinition7 → TYZThm36Seven → BetaOnGenus7 → Lemma321Seven`.**
TYZ's proof (L2547–2566) made Lean: `Z(e)^{σ} = Z(e)^{γρ}` on `A(G_e)` (glue `BetaOnGenus7`), then
`γρ t_c z = τ − t_{c⁻¹} z` from the leaf, commutativity on `A(H_e)` and complex conjugation inverting
`Cl` (`actsO_conj`, from ring-class's `actsAsArtin4_conj` and restriction `actsO_of_acts4`), and
reindexing `c ↦ c⁻¹` over `2Cl_e` (`sum_sqClasses_inv`, `card_sqClasses : #2Cl_e = g(e)`). Also
`exists_complexConj` (complex conjugation in `Gal(ℚ̄/ℚ)`, via `AlgHom.fieldRange_of_normal`).

**§13 `betaOnGenus7 : BetaOnGenus7`** (on the genus field, a `β₁`-lift agrees with `γ ∘ Art([𝔭₂])^{−5}`),
from three genus-theory facts, all proved:

* `genusField_le_genusStar`: `G_n ⊆ K_n(√p* : p ∣ n)` (Bauer, with `isSquare_pstar_iff`: in a finite
  field of odd characteristic `≠ p`, `p*` is a square iff `|F|` is a square mod `p`; from Mathlib's
  `quadraticChar_odd_prime`, `quadraticChar_neg_one`);
* `sqrtPstarInHilbert`: `√p* ∈ H_n` (Bauer; `norm_sq_mod_prime3`: `4N(β) ≡ t² (mod p)` for `p ∣ n`);
* `artinPstarChi`: `Art(c)(√p*) = χ_p(c)·√p*` (`maxSubfield_kerChi`: the fixed field of `ker χ_p` is
  `K_n(√p*)`, Bauer in both directions; Galois correspondence `fixingSubgroup_fixedField`);
* `normP2`: `N𝔭₂ = 2` (`(2) = 𝔭₂𝔭̄₂`, neither is `(1)`, `N(2) = 4`).

Assembly `betaOnGenus7_of`: the equalizer of `σ ∘ embed` and `γρ ∘ embed` is a field over `K_n`
(`eqField`) containing every `√p*`: `σ√p* = betaOneSign(p*)√p*`, `γ√p* = sgn(p*)√p*`
(`IsComplexConj.apply_sqrt`), `ρ√p* = χ_p([𝔭₂])√p* = (2/p)√p*` (`ZMod.exists_sq_eq_two_iff`), and
`betaOneSign(p*) = sgn(p*)·(2/p)` (`betaOneSign_pstar`).

## 3. Compile status

`lake build ZInQKernel.Contrib.TYZGenus.RingClassBridge` (clean), then
`lake env lean scratch/cm-bridge/Bridge.lean`: 0 errors (≈40 s; only linter style warnings), VERIFIED
2026-11-13. `#print axioms` for 27 declarations (`audit-out.txt`), including `genusFieldLeLni`,
`betaOnGenus7_of`, `sqrtPstarInHilbert`, `artinPstarChi`, `normP2`, `lemma321Seven_of'` and the main
theorem: all `[propext, Classical.choice, Quot.sound]`. The file keeps cm-numeric's
`set_option maxRecDepth 8000`. Pitfall met: `rw [restrict_ringClassArtinEquiv] at h` at `K = QNeg d`
hits max recursion / a kernel deterministic timeout; proving the restriction identity once for a general
`K` (`coe_artin_restrict`) and specializing avoids it.

## 4. What was not done

* **`Lemma321Five`** (TYZ Lemma 3.21(1)) stays a leaf. TYZ's proof needs (a) the existence of a lift of
  `β₁` to `Gal(ℚ̄/ℚ)` acting on every quadratic field by `betaOneSign` (the leaf asserts `∃ σ`; deriving
  it needs Kummer theory for the maximal elementary 2-extension of `ℚ`), (b) genus theory for `H'_n`
  (the subfield of `H'_n` fixed by `2Cl'_n` is `L_n`, i.e. genus characters on `Pic(𝒪_{n,4})`, not in
  the project), and (c) a pinned form of TYZ Theorem 3.6(1) (`z_n^{σ_ϖ} = z_n + τ((1+i)/2)`,
  `z̄_n = −z_n + τ(1)`, with `σ_ϖ` = the Artin symbol of the odd part of `(√−n − 1)` in `Pic(𝒪_{n,4})`).
  SPECULATIVE estimate: one more task of the size of this one.
* **`Lemma318Literal`** (TYZ Lemma `torsion2`) stays a leaf: its proof (L2230–2300, VERIFIED read) uses
  total ramification of `℘` in `F(A[℘])`, ramification bounds in `ℍ'_n`, and supersingular reduction at a
  prime `p ≡ 3 (mod 8)` inert in the `K_{d₀}`; none of this exists in Lean today.
* `TYZSigmaShiftsF0`, `Thm35First`, the `𝓛`-leaves and `CM.CMFieldOfDefinition ringClassFieldD` were
  not attacked (the last is task tyz-cm's).

## 5. Review

Independent statement review of `TYZThm36Seven` (AI subagent, read-only, no Lean, 2026-11-13; no human
review). Checked against Period7.tex L1196–1210, L1235–1252, L1408–1428: (1) `𝔭₂` is TYZ's `v₂` — OK;
(2) geometric `σ_{ϖ^5}` on `H_n` is the arithmetic `Art([𝔭₂])^{−5}` — OK; (3) `tyzZ7 n` is TYZ's `z_n`
and the pinned `δ` cannot make the statement false (`z_n` depends on `δ mod 64` only; `δ ↦ −δ`
conjugates `z_n` and `v₂` together) — OK; (4) `τ(1/2) = tauG 1 = (2, −4)` — OK; (5) not vacuous — OK.
**Finding (blocking, fixed):** the first `p2Ideal` was not oriented relative to `ιC`, so the leaf was
the wrong-sign statement (numerically false) for one of the two possible `embed n`. Fixed with
`PosOrient` (§1); `normP2`, `betaOnGenus7`, `lemma321Seven_of'` and the main theorem recompiled
unchanged otherwise. The reviewer also judged that `thm36_7.py` tests exactly the Lean statement under
the `+i√n` orientation (Shimura direction taken from cm-numeric's VERIFIED `shimura.out`).

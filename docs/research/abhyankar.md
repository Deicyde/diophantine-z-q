# abhyankar: `SGRDirect.NVLocal.TameBranchNormal` proved (no new leaf); `nvLocalInertia` discharged

Task abhyankar, branch `wip/abhyankar` (base 60a3fac7 + merge of `origin/wip/nv-local` c137bf8c).
Contributor file `ZInQKernel/Contrib/OneProof/Abhyankar.lean`, helpers in `ZInQKernel/Contrib/OneProof/Abhyankar/`.

## 1. Result

`TameBranchNormal` (nv-local, `ZInQKernel/Contrib/OneProof/SGRDirectNVLocal.lean:627`) is **proved outright**, from
Mathlib and glue already proved in the chain. No hypothesis, no new leaf. All claims below are VERIFIED (compiled).

```lean
theorem Abhyankar.tameBranchNormal : SGRDirect.NVLocal.TameBranchNormal
theorem Abhyankar.nvLocalInertia : SGRDirect.NVLocalInertia
  -- := SGRDirect.NVLocal.nvLocalInertia_of_tame tameBranchNormal
```

`#print axioms` (scratch/abhyankar/axioms.txt, scratch/abhyankar/discharges.txt):

```
'Abhyankar.tameBranchNormal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Abhyankar.nvLocalInertia' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The statement proved, verbatim (a verbatim copy in `scratch/abhyankar/Statement.lean` is checked equal to the
original by `rfl` and proved by `Abhyankar.tameBranchNormal`):

```lean
def TameBranchNormal : Prop :=
  ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsGalois K L] (m : Ideal R) [m.IsMaximal],
    IsRegularLocalRing (Localization.AtPrime m) → ringKrullDim (Localization.AtPrime m) = 2 →
    ∀ f g : R, m = Ideal.span {f, g} → (Ideal.span {f}).IsPrime →
    ∀ p : ℕ, p.Prime → (p : R) ∈ m → Module.finrank K L < p →
    (∀ P : Ideal R, P.IsPrime → P.height = 1 → P ≤ m → f ∉ P → g ∉ P →
      ∀ P' : Ideal (integralClosure R L), P'.IsPrime → P'.under R = P →
        P'.ramificationIdx R = 1) →
    ∀ 𝔓 : Ideal (integralClosure R L), 𝔓.IsMaximal → 𝔓.under R = m →
    ∀ Q : Ideal (integralClosure R L), Q.IsPrime → Q.under R = Ideal.span {f} → Q ≤ 𝔓 →
      (∀ Q' : Ideal (integralClosure R L), Q'.IsPrime → Q'.under R = Ideal.span {f} → Q' ≤ 𝔓 →
        Q' = Q) ∧
      (∀ (F : Type) [CommRing F] [Algebra (integralClosure R L ⧸ Q) F]
          [IsFractionRing (integralClosure R L ⧸ Q) F] (z : F),
        IsIntegral (integralClosure R L ⧸ Q) z →
        ∃ a s : integralClosure R L, s ∉ 𝔓 ∧
          algebraMap _ F (Ideal.Quotient.mk Q s) * z = algebraMap _ F (Ideal.Quotient.mk Q a))
```

The statement is true as stated (no correction needed). Its hypotheses are all used: regularity and dimension
2 (purity, the Kummer base), `m = (f, g)` (normal crossings), `[L : K] < p` with `p ∈ m` (tameness, `[Ω : L]`
prime to `p`), unramified off `fg = 0` (base change), Galois (`e | [L : K]`, needed by Abhyankar's lemma for
DVRs). nv-local's third test case (`§2.3`) shows the hypothesis off `fg = 0` cannot be dropped.

## 2. `#discharges`

Output (scratch/abhyankar/discharges.txt; `scratch/abhyankar/Discharges.lean` imports Main, Discharges and
`ZInQKernel.Contrib.OneProof.Abhyankar`):

```
DISCHARGES [OpenResearchLeaves23.gonzalezRotgerProp56X6] by GRCountX6.prop56X6_of_r5fpCount
  still assumes: [LeafQM.AV.R5fpCount]
  ...
#discharges: 61 open hypotheses, 2376 theorems checked, 6 discharge one
```

The six lines are earlier contributions in the import closure (GRCountX6, GapSHPair, R16Split, SGA7PersistsNF,
UnipotentForward, MumfordRigidity), unchanged. None of this task's theorems matches an open hypothesis **at this
base**, as expected: the field it discharges, `nvLocalInertia`, exists only after sgr-fold (`wip/sgr-fold`,
`OpenGlue8.nvLocalInertia : SGRDirect.NVLocalInertia`), which is not merged here (it adds its own `TailZ36.lean`).

## 3. Autofold spec

`scratch/abhyankar/autofold.json`:

```json
{"name": "abhyankar-fold",
 "imports": ["ZInQKernel.Contrib.OneProof.Abhyankar"],
 "discharges": [
   {"field": "nvLocalInertia", "proof": "_root_.Abhyankar.nvLocalInertia"}]}
```

* Dry-run at this base: `autofold: not a field of the current bundles: ['nvLocalInertia']`
  (scratch/abhyankar/autofold-dryrun-at-base.txt). **It can be dry-run for real only once sgr-fold has landed.**
* Dry-run on sgr-fold's tree (files of `origin/wip/sgr-fold` b7dfa3da extracted with `git archive` into `/tmp`,
  this task's contributor file copied in, nothing merged): succeeds,
  `strict count: 45/10 on 55 -> 45/9 on 54; strictest 43/12 -> 43/11` (GLUE −1, strict and strictest);
  generated module in scratch/abhyankar/autofold-dryrun-on-sgr-fold.txt. Since `OpenGlue8` has the one field
  `nvLocalInertia`, the generated `OpenGlue9` is an empty structure (`⟨⟩`); scratch/abhyankar/EmptyBundleTest.lean
  checks that this parses and that the discharge term has the field's type. The integration lead may instead drop
  the bundle by hand: in sgr-fold's `TailZ36.lean`, `openGlue7_of_OpenGlue8` with
  `nvLocalInertia := _root_.Abhyankar.nvLocalInertia`, and `OpenGlue8` removed from `sixContactMin_of_open30` and
  `frozenTarget`.
* Leaf table: **no new leaf.** The only inputs beyond Mathlib are chain theorems already proved:
  `HDec.HSyn.t2_proved : PkgI2.AbhyankarDVR` (Abhyankar's lemma for DVRs), `TPurity3.purityGlobalDim2'`,
  `TPurity3.normalFreeDim2`, `TPurity3.isIntegrallyClosed_of_dim2`, `TsKummer.unramBaseChange`,
  `TsKummer.fu_of_unram`, `TsKummer.intCl_isLocalization`, `TsKummer.ramificationIdx_map_algEquiv`,
  `PropTSGlue.isSeparable_of_finrank_lt`, and nv-local's `ramificationIdx_map_localization`.

Net effect with sgr-fold: `shimuraIntegralModelRep` and `quotientP1Coordinate` leave the proof (sgr-fold's bypass)
and the glue field that bypass introduced, `nvLocalInertia`, is proved; no open field is added.

## 4. Method

Notation: `A = R_m` (regular local of dimension 2, maximal ideal `(f, g)`), `S = A^L`, `N = [L : K] < p`.
The proof follows nv-local §2.3 (Abhyankar's lemma in dimension 2, SGA 1 XIII 5.2–5.3 and Grothendieck–Murre,
LNM 208, §2.3; locators UNVERIFIED), split into named Props (`Abhyankar/Defs.lean`), each compiled.

| step | Lean | file | content |
|---|---|---|---|
| 0 | `tameBranchNormal_of_local : TBNLocal → TameBranchNormal` | Transport | localize at `m`: `S_A` is the localization of `R^L` at `R ∖ m` (`TsKummer.intCl_isLocalization`); heights (`IsLocalization.height_under`), ramification indices, unique branch and normality transported; a fraction field of `S/Q` is one of `S_A/QS_A` |
| — | `tbnLocal_of_pieces` | Assembly | `Ω = L(t, u)`, `t^N = f`, `u^N = g`, inside an algebraic closure (`exists_kummer_field`, `[Ω : L] = d₁d₂`, `dᵢ ≤ N`, so prime to `p`); purity `TPurity3.purityGlobalDim2'` makes the integral closure `S'` of `A'' = A[t, u]` in `Ω` étale over `A''` |
| 1 | `kummerBase : KummerBase` | KummerBase | `A''` finite over `A`, every element `r + (t, u)`, every maximal ideal contains `(t, u)`: local with maximal ideal `(t, u)`; dimension 2 (going down over the integrally closed `A`, Krull's height theorem): regular |
| 2 | `kummerUnram_of_branch`, `kummerUnramBranch` | KummerUnram(+Basic, +Tame), KummerBranch, KummerBranchFinal | `S'` finite over `A''` and unramified at height-one primes `Q`. With `P₀ = Q ∩ A` of height one: if `f, g ∉ P₀`, `L/K` is unramified over `A_{P₀}` (hypothesis; residue separability from `[L:K] < p`, `tame_at`), so its base change to `A''_P` is (`TsKummer.unramBaseChange`, `unram_of_baseChange`, `unramifiedAt_of_local` via `TsKummer.fu_of_unram`). If `f ∈ P₀`: `branch_e` — T2 at `A_(f)` for `Ω₁ = L(t)` (index `N`, `e | N` by the Galois formula `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`), `(t)` has index `N` over `A` in `A₁ = A[t, g]` (a DVR with uniformizer `t` after localizing), indices multiply (`A₁ → A₁^{Ω₁}` free by `TPurity3.normalFreeDim2`): index `1`; then `branch_final` — residue fields separable (`[Ω₁ : Frac A₁_(t)] ≤ N < p`, `finrank_le_of_adjoin`) and base change from `A₁_(t)` to `A''_P`. If `g ∈ P₀`: the same with `f, t` and `g, u` exchanged (`(g)` prime by `span_prime_of_pair`) |
| 3 | `etaleBranch : EtaleBranch` | EtaleBranch | `C = S'_{𝔓'}` has maximal ideal `(t, u)C` (`Algebra.FormallyUnramified.map_maximalIdeal`); `C/tC` has principal maximal ideal with `ū` not nilpotent, so it is a DVR (`principal_local_structure`, adapted from `CurveGlueCI.isDomain_of_dim_one`): every prime `∋ t` strictly inside `𝔓'` localizes to `tC`, and `(S'/Q')_{𝔓'} = C/tC` is integrally closed |
| 4 | `branchDescent : BranchDescent` | Descent | uniqueness by going down for `S ⊆ S'`; normality: for `z = a/b` integral over `S/Q`, the colon ideal `(bS' + J) : a` (`J` = intersection of the finitely many primes of `S'` over `Q`, minimal primes of `QS'`) meets `S ∖ 𝔓` (else a maximal `𝔓' ⊇` it over `𝔓` contradicts step 3 there, after prime avoidance); then `Tr_{Ω/L}` maps `S'` into `S` and `J` into `Q` (`trace_eq_sum_embeddings` into an algebraic closure: every conjugate lies in every prime over `Q`), giving `(d s) a ≡ b Tr(y) mod Q`, `d = [Ω : L] ∉ 𝔓` |

Contributor file and helpers (sizes 2.5–30 KB each, 159 KB in total over 12 files):
`Abhyankar.lean` (final theorems), `Abhyankar/Defs.lean`, `Assembly.lean`, `Transport.lean`, `KummerBase.lean`,
`KummerUnramBasic.lean`, `KummerUnramTame.lean`, `KummerUnram.lean`, `KummerBranch.lean`,
`KummerBranchFinal.lean`, `EtaleBranch.lean`, `Descent.lean`. The contributor file imports only these helpers,
which import `ZInQKernel.Contrib.OneProof.SGRDirectNVLocal` (the module defining the statement); none imports
`ZInQKernel.OneProof.Main`. Build: `lake build ZInQKernel.Contrib.OneProof.Abhyankar`.

## 5. Notes

* Theorem numbers from memory are UNVERIFIED (no network): SGA 1 XIII 5.2–5.3, SGA 1 X 3.6, Grothendieck–Murre
  LNM 208 §2.3. None is used as a hypothesis.
* The named Props of `Abhyankar/Defs.lean` and `KummerUnramBranch` are intermediate steps, all proved; they are
  not proposed as fields.

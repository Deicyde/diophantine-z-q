# nv-local: `NVLocalInertia` reduced to a general statement about tame covers (`TameBranchNormal`)

Task nv-local, 2026-11-15/16. Base `56478c75` (sgr-direct on main `43513d87`).

- **Lean** (new): `ZInQKernel/Contrib/OneProof/SGRDirectNVLocal.lean` (about 1000 lines), namespace
  `SGRDirect.NVLocal`. It imports `ZInQKernel.Contrib.OneProof.SGRDirectElkies`, which imports `SGRDirectNV`, where
  `NVLocalInertia` is declared.
- **Scratch** (`scratch/nv-local/`):
  - `log.md`;
  - `NVLocal.lean`, a copy of the Contrib file;
  - `Core-first.lean`, the first compiled version (its `BranchRegular` still had an existence clause);
  - `Discharges.lean` with `Discharges-output.txt`;
  - `autofold.json`.
- **Marks:** **VERIFIED** (compiled, read, or computed), **STANDARD** (published; locators from memory are
  **UNVERIFIED**, there is no network), **SPECULATIVE**.

## 0. Verdict

**`NVLocalInertia` is not proved outright. It is proved from one strictly smaller GLUE Prop, `TameBranchNormal`**,
a statement of general commutative algebra with no project-specific definitions (VERIFIED: `lake build`, standard
axioms):

```lean
theorem SGRDirect.NVLocal.nvLocalInertia_of_tame (h : TameBranchNormal) : SGRDirect.NVLocalInertia

theorem SGRDirect.NVLocal.heckeVertWitness_of_tame (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hTB : TameBranchNormal) (hEl : QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted) :
    HDec.HeckeRestNV.HeckeVertWitness
```

- `NVLocalInertia` is **true as stated** (STANDARD; §2.3). No statement was changed.
- **`TameBranchNormal`.**
  - *Hypotheses.* `R_m` is a regular local ring of dimension 2 with `m = (f, g)` and residue characteristic `p`.
    `L/Frac R` is Galois of degree `< p`, and it is unramified at the height-one primes near `m` off the divisor
    `fg = 0`.
  - *Conclusion.* At every closed point `𝔓` of the normalization, the branch of `f = 0` is unique and normal.
- The proof goes through an intermediate Prop `BranchRegular`, the same statement in the setting of the Hecke
  cover over `ℤ[X]`, `ℚ[X]` and `ℚ(X)`. Both reductions are compiled:
  - `BranchRegular → NVLocalInertia` is the Galois and arithmetic half of h-b1's step 3: the inertia comparison and
    the unramified residue fields.
  - `TameBranchNormal → BranchRegular` is the translation from `ℤ[X]`: horizontal primes, `BranchData`,
    localizations and Gauss's lemma.
- **Rating of the new leaf `TameBranchNormal`: not printed form; GLUE (project, local commutative algebra).** It is
  a consequence of Abhyankar's lemma (SGA 1 XIII 5.2–5.3) and Zariski–Nagata purity (SGA 1 X 3.1); both locators
  are UNVERIFIED. No published statement has this form (§2.2).
- **Counts.** `tameBranchNormal` replaces `nvLocalInertia` one for one in sgr-direct's bypass fold. So that fold
  still goes **−1 GLUE**: `shimuraIntegralModelRep` and `quotientP1Coordinate` out, `tameBranchNormal` in. The
  **−2 GLUE** target needs `TameBranchNormal` proved. §4 gives the route.

## 1. What compiles (VERIFIED)

| declaration | content |
|---|---|
| `eq_one_of_inertia_of_unram` | `K` a number field, `P` a prime of `𝓞 K` with `P.ramificationIdx ℤ = 1`, and `σ ∈ Aut(K/ℚ)` with `σx − x ∈ P` for all `x ∈ 𝓞 K`. Then `σ = 1`. |
| `primeOf`, `primeOf_isPrime`, `mem_primeOf_of_mem` | for `ψ : C → L` with `ker ψ ⊆ 𝔓` and `𝓞 L` inside `{ψ c₁ / ψ c₂ : c₂ ∉ 𝔓}`: the prime `{y : y·ψ(d₂) = ψ(d₁), d₁ ∈ 𝔓, d₂ ∉ 𝔓}` of `𝓞 L`, which contains `p` when `p ∈ 𝔓` |
| `inertia_primeOf`, `eq_one_of_primeOf` | an automorphism `σ` of `L` with `σ(ψ c) = ψ(c')` and `c' ≡ c mod 𝔓` lies in the inertia of `primeOf`; if that prime is unramified then `σ = 1` |
| `zqIncl`, `galB`, `galC_mem` | the inclusion of the `ℤ[X]`-closure `C` in the `ℚ[X]`-closure `B`, and the Galois action on both |
| `exists_int_mul_mem` | every `y ∈ B` has a nonzero integer multiple in `C` (Mathlib's `IsIntegral.exists_multiple_integral_of_isLocalization`) |
| `exists_branch` | through every maximal `𝔓 ⊂ C` over `(p, dX − a)` passes a branch: a prime `Q` of `B` over `X − b` with `Q ∩ C ⊆ 𝔓` (going down) |
| `BranchRegular` (def), `nvLocalInertia_of_branchRegular` | the intermediate Prop (§2.1) and `BranchRegular → NVLocalInertia` |
| `ramificationIdx_map_localization` | the ramification index is unchanged by localizing the base at any submonoid missing the prime. It generalizes Mathlib's `IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx`. |
| `TameBranchNormal` (def) | the new GLUE Prop (§2.1) |
| `maximal_eq_span`, `secGen_isPrimitive`, `secGen_map`, `span_secGen_eq`, `span_secGen_isPrime` | `m = (dX − a, p)`; `dX − a` is primitive; `(dX − a) = ker(X ↦ b)` (Gauss's lemma) |
| `isLocalization_B` | `B` is the localization of `C` at the nonzero integers |
| `unram_near` | the height-one primes `P ⊆ m` of `ℤ[X]` off `(dX − a)` and `(p)` are unramified in `C`. This comes from `BranchData` and distinctness mod `p`, with the index moved from `B` by `ramificationIdx_map_localization`. |
| `branchRegular_of_tame` | `TameBranchNormal → BranchRegular` |
| `nvLocalInertia_of_tame`, `heckeVertWitness_of_branchRegular`, `heckeVertWitness_of_tame` | the composites |

**Checks.**
- `lake build +ZInQKernel.Contrib.OneProof.SGRDirectNVLocal` succeeds (22 s on the copied build tree).
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for the twelve theorems listed in
  `scratch/nv-local/Discharges.lean` (output in `Discharges-output.txt`).
- `#discharges` reports "63 open hypotheses, 1923 theorems checked, 7 discharge one".
  - None of the seven is from this file, as expected: `HeckeVertWitness` and `NVLocalInertia` are not open
    fields of the current bundles.
  - The seven are the same as in sgr-direct's run.
- The file has no code that runs at build time. Its only options are `maxHeartbeats` and
  `synthInstance.maxHeartbeats` on the two long proofs, and the `haveI` linter switch.

**The proof of `nvLocalInertia_of_branchRegular`** (`g = 1` in the conclusion):
1. **A closed point.** Let `q` be a vertical prime of `C` and `τ ∈ InertiaZ E q`.
   - `exists_secIdeal` gives the maximal ideal `m = (p, dX − a)` of `ℤ[X]`, where `b = a/d`.
   - Going up gives a maximal `𝔓 ⊇ q` over `m`.
2. **The branch.** `exists_branch` gives a branch `Q` through `𝔓`. `BranchRegular` says it is the only one and is
   normal at `𝔓`.
3. **`τQ = Q`.** The prime `τQ` lies over `X − b` and has `τQ ∩ C ⊆ 𝔓`:
   - if `c ∈ τQ ∩ C` then `τ⁻¹c ∈ Q ∩ C ⊆ 𝔓`;
   - and `c − τ⁻¹c ∈ q ⊆ 𝔓`.

   By uniqueness `τQ = Q`, so `τ` acts on `κ = B/Q`.
4. **The residue field.** `IsAlgClosed.lift` gives `φ : κ → ℚ̄`.
   - Let `L = ℚ(φ(κ))`. It is finite over ℚ (`PropTSGlue.finiteDimensional_residue`) and unramified at `p` (the
     hypothesis of `NVLocalInertia`).
   - Transport the action of `τ` to `σ ∈ Aut(L/ℚ)`, and set `ψ := e ∘ mk_Q ∘ zqIncl : C → L`.
5. **Inertia.** By normality, `𝓞 L ⊆ {ψ c₁ / ψ c₂ : c₂ ∉ 𝔓}`.
   - Since `τ ≡ id mod q ⊆ 𝔓`, `σ` lies in the inertia of `primeOf`.
   - That prime is unramified, so `σ = 1`.
6. **Conclusion.** `σ = 1` means `τ ∈ InertiaQ E Q`.

**The proof of `branchRegular_of_tame`.**
1. **The setting.** Take `R = ℤ[X]`, `K = ℚ(X)`, `L = E`, `m = 𝔓 ∩ ℤ[X]`, `f = dX − a`, `g = p`.
2. **The hypotheses of `TameBranchNormal`.**
   - `ℤ[X]_m` is regular of dimension 2 (`regular_dim2_intPoly`).
   - `m = (f, g)` and `(f)` is prime, by Gauss's lemma.
   - Unramifiedness near `m` is `unram_near`.
3. **The branch.** The branch `Q ⊂ B` gives the prime `Q ∩ C` over `(f)`.
4. **Uniqueness.** Uniqueness in `C` gives uniqueness in `B`, since `Q = (Q ∩ C)B` (`isLocalization_B`).
5. **Normality.** `B/Q` is a fraction ring of `C/(Q ∩ C)` (built by hand: units through `Ideal.Quotient.exists_inv`,
   denominators by `exists_int_mul_mem`). So the normality clause of `TameBranchNormal` gives that of
   `BranchRegular`.

## 2. `TameBranchNormal`

### 2.1 Statement

```lean
def TameBranchNormal : Prop :=
  ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsGalois K L] (m : Ideal R) [m.IsMaximal],
    IsRegularLocalRing (Localization.AtPrime m) → ringKrullDim (Localization.AtPrime m) = 2 →
    ∀ f g : R, m = Ideal.span {f, g} → (Ideal.span {f}).IsPrime →
    ∀ p : ℕ, p.Prime → (p : R) ∈ m → Module.finrank K L < p →
    (∀ P : Ideal R, P.IsPrime → P.height = 1 → P ≤ m → f ∉ P → g ∉ P →
      ∀ P' : Ideal (integralClosure R L), P'.IsPrime → P'.under R = P → P'.ramificationIdx R = 1) →
    ∀ 𝔓 : Ideal (integralClosure R L), 𝔓.IsMaximal → 𝔓.under R = m →
    ∀ Q : Ideal (integralClosure R L), Q.IsPrime → Q.under R = Ideal.span {f} → Q ≤ 𝔓 →
      (∀ Q' : Ideal (integralClosure R L), Q'.IsPrime → Q'.under R = Ideal.span {f} → Q' ≤ 𝔓 → Q' = Q) ∧
      (∀ (F : Type) [CommRing F] [Algebra (integralClosure R L ⧸ Q) F]
          [IsFractionRing (integralClosure R L ⧸ Q) F] (z : F), IsIntegral (integralClosure R L ⧸ Q) z →
        ∃ a s : integralClosure R L, s ∉ 𝔓 ∧
          algebraMap _ F (Ideal.Quotient.mk Q s) * z = algebraMap _ F (Ideal.Quotient.mk Q a))
```

In words, with `S` the integral closure of `R` in `L`:
- **(UB)** all primes of `S` over `(f)` inside `𝔓` coincide;
- **(N)** the localization of `S/Q` at `𝔓` is integrally closed.

Notes on the hypotheses:
- Tameness is automatic. The residue characteristic is `p`, the degree is `< p`, and the residue fields of `(f)`
  and `(g)` have characteristic 0 or `p`.
- In the setting of `BranchRegular` the hypotheses are verified by the compiled `branchRegular_of_tame`.

**`BranchRegular`** (the intermediate Prop) is the same statement in the Hecke-cover setting:
- `E/ℚ(X)` Galois of degree `< p` with `BranchData`;
- `S` `p`-integral and distinct mod `p`, and `b ∈ S`;
- `𝔓` maximal in `C` over `(p, dX − a)`.

For every prime `Q` of `B` over `X − b` with `Q ∩ C ⊆ 𝔓`:
- (UB) every such `Q'` equals `Q`;
- (N) every `z ∈ B/Q` integral over `ℤ` is `c₁/c₂` with `c₁, c₂ ∈ C` and `c₂ ∉ 𝔓`.

### 2.2 Rating

**Not printed form; GLUE.**
- It is the geometric half of h-b1 §3 step 3, in general form. That step assumes strict henselization and says
  "unique branch through `𝔓`, residue degree 1 on it". rv-h-b1 found that step "holds as stated".
- The published statements behind it are about tame covers étale-locally:
  - Abhyankar's lemma (SGA 1 XIII 5.2): after extracting `n`-th roots of a normal-crossings divisor, a tame
    cover becomes étale;
  - the tame local fundamental group of `Spec A^{sh} ∖ D` is `Ẑ'(1)^r` (SGA 1 XIII 5.3; Grothendieck–Murre,
    LNM 208).

  Locators UNVERIFIED.
- Neither published statement is this Zariski-local statement about one branch. So it is not proposed as a LEAF.

### 2.3 Why it is true (paper proof; SPECULATIVE until compiled)

Notation: `A = R_m`, `S` the integral closure of `A` in `L`, `G = Gal(L/K)`, `n = |G| < p`.

1. **Tameness.** Near `m` only `(f)` and `(g)` ramify, by hypothesis, and both tamely: inertia orders divide
   `n < p`, and residue extensions of degree `< p` are separable.
2. **The Kummer base change.** Let `N = n` and `ζ = ζ_N`, a unit since `p ∤ N`.
   - Let `A' = A[ζ][T, U]/(T^N − f, U^N − g)`, localized at a maximal ideal. It is a regular local ring of
     dimension 2 with parameters `T, U`.
   - Let `Ω = L(ζ, T, U)`. It is Galois over `K`.
   - `Γ = Gal(Ω/L)` has order dividing `φ(N)N²`, which is prime to `p`.
3. **Unramified in codimension 1.** Let `S'` be the integral closure of `A'` in `Ω`. Its height-one primes are of
   three kinds:
   - `(U)`, over `(g)`. The kernel's T2 (`PkgI2.AbhyankarDVR`, proved: `t2_proved`) gives `e = N` over the DVR
     `A_(g)`. Since `e((U) | (g)) = N`, the tower gives `e = 1`, with separable residue extensions.
   - `(T)`, over `(f)`: the same argument.
   - Any other prime lies over a height-one prime `P ∌ fg`. There `L` and `K(ζ, T, U)` are both unramified, so
     their compositum is unramified: the inertia of `Ω/K` restricts trivially to both fields, which generate `Ω`.
4. **Purity.** `PropTSGlue.purityGlobalDim2` (proved) shows that `S'` is étale over `A'`.
5. **Specialization.** `S'/TS'` is étale over the DVR `A'/T`. So it is normal, and its local rings are DVRs.
   Hence, for each maximal ideal `𝔐` of `S'`:
   - (UB') exactly one prime of `S'` over `(T)` lies in `𝔐`;
   - (N') for that prime `Q'`, `(S'/Q')_𝔐` is a DVR.
6. **Descent to `S`.**
   - **(UB).** By going down for `S ⊆ S'`, two branches through `𝔓` lift to branches through one `𝔐`. These
     coincide by (UB').
   - **(N).** For `Q'` over `Q`, let `D = Stab_Γ(Q')`. The ideals `γQ'` are pairwise comaximal at `𝔓`, by (UB').
     CRT and the Reynolds operator of the tame group `Γ` then give `(S/Q)_𝔓 ≅ T^D`, where `T` is the
     semilocalization of `S'/Q'`, which is normal by (N').
   - An element integral over `(S/Q)_𝔓` lies in `T` and is `D`-invariant, hence lies in `(S/Q)_𝔓`. ∎

**Test cases** (by hand; `p` a large prime), in the setting of `BranchRegular`:

| cover | (UB) | (N) |
|---|---|---|
| `ℚ(X)(√(p(X − b)))`, `S = R[z]`, `z² = p(X − b)` | `S/(X − b) = ℤ_(p)[z]/(z²)` has one minimal prime | `S/Q = ℤ_(p)`: holds |
| `ℚ(√(pu))(X)`, `u` a `p`-adic unit (vertical ramification only) | `S/(X − b) = ℤ_(p)[√(pu)]`, a domain | it is a DVR (Eisenstein): holds |
| `ℚ(X)(√(X − b + p²))` (branch point `b − p² ≡ b`, so distinctness fails) | `S/(X − b) = ℤ_(p)[y]/(y² − p²)` has two branches `y = ±p` through one closed point | **(UB) fails**, so the hypothesis "unramified off `fg = 0`" is needed |

## 3. Relation to sgr-direct and to the fold

- sgr-direct's composite `heckeVertWitness_of_nvElkies` needed one open Prop, `NVLocalInertia`.
  `heckeVertWitness_of_tame` needs `TameBranchNormal` instead. The other inputs are the same bundle fields:
  `r1r2`, `t5`, `qmAutCard`, `serreRigidity3`, `alFixedPoints`, `elkiesX6StarPrinted`.
- **Fold.** As in sgr-direct §5, no fold was executed; `scratch/nv-local/autofold.json` records the plan.
  - `HeckeVertWitness` is not a top-level field. The fold is a bypass at generation 5: regenerate the bundles
    without `shimuraIntegralModelRep` and `quotientP1Coordinate`, with the new field
    `tameBranchNormal : SGRDirect.NVLocal.TameBranchNormal`.
  - In `glue4_of_open5`, use
    `heckeVertWitness := SGRDirect.NVLocal.heckeVertWitness_of_tame … n.tameBranchNormal r.elkiesX6StarPrinted`.
  - Strict count 56 → 55 (GLUE −1), the same as sgr-direct's plan.
- **Leaf table.**

| new leaf | kind | flag | strict | printed form? |
|---|---|---|---|---|
| `tameBranchNormal : SGRDirect.NVLocal.TameBranchNormal` | project glue | — | GLUE | no: a Zariski-local consequence of Abhyankar's lemma and purity; no published statement of this form (§2.2) |

## 4. What a proof of `TameBranchNormal` needs

- Every route to the local structure at `𝔓` has to remove the ramification along `g = p`. That requires
  extracting a root of `g`, which changes the base ring.
  - The route of §2.3, h-b1's route, and the report's variant (sgr-direct §6) all do this.
  - Purity (`purityGlobalDim2`) and T2 (`AbhyankarDVR`) are stated for general rings and are reused.
- **Steps to compile**, in the order of §2.3:
  1. The Kummer base `A'`: regular local of dimension 2.
  2. `Ω` as a splitting field, with `L ↪ Ω` and `Gal(Ω/L)` tame.
  3. `S'`, finite and normal.
  4. Unramifiedness at every height-one prime of `A'`: T2 twice, plus base change.
  5. Purity.
  6. Étale over a DVR implies normal; hence (UB') and (N').
  7. Descent: going down for (UB); Reynolds operator plus CRT for (N).
- Estimated at several thousand lines of Lean.

## 5. What remains

1. **`TameBranchNormal`** (GLUE): a self-contained commutative-algebra target with no project definitions; route
   in §2.3 and §4.
2. **The deep fold** (sgr-direct §5), with `tameBranchNormal` in place of `nvLocalInertia`.

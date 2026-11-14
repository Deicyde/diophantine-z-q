# tyz-35: `Thm35First ℓ tyzZ` reduced to TYZ Theorem 3.3 (with Lemma 3.14) for the pinned CM points

Task tyz-35, 2026-11-13/14. Lean: `scratch/tyz-35/Thm35.lean` (imports the built
`ZInQKernel.Contrib.TYZGenus.RingClassBridge`; §0–§9 a verbatim copy of cm-bridge's `Bridge.lean`
§0–§9, namespace `CMBridge → TYZ35`) and `scratch/tyz-35/Final.lean` (all of `Bridge.lean` §0–§15 plus the
new sections, giving cm-bridge's main theorem with the new leaf). Results log: `scratch/tyz-35/log.md`.
Axiom audit: `scratch/tyz-35/audit-out.txt`. Pure-Python check: `scratch/tyz-35/convention.py` →
`convention.out`.
Marks: **VERIFIED** (compiled, computed, or read in a named source), **STANDARD**, **SPECULATIVE**,
**UNVERIFIED** (theorem numbers from memory). TYZ = Tian–Yuan–Zhang, arXiv:1411.4728v1 (Asian J. Math.
21 (2017)). `Period7.tex` is **not on this host**: TYZ line numbers `Lnnnn` are quoted from `nt-tyz.md`,
`rv-tyz-inputs.md`, `tyz-t1.md`, `cm-points.md`, `cm-numeric.md`, `ring-class.md`, not re-read.

## 0. Main result

**`Thm35First ℓ tyzZ` is proved, for every `ℓ` with `ℓ 1 = 1` (in particular every `IsTYZLcal ℓ`),
from one leaf, `TYZThm33Pinned ℓ`: TYZ Theorem 3.3 together with Lemma 3.14 (`char'`), stated for the
pinned CM points.** Everything between them is proved in Lean (VERIFIED compiled, axioms
`[propext, Classical.choice, Quot.sound]`; namespace `ZInQ.Contrib.TYZGenus.TYZ35`):

```lean
theorem thm35First_of_thm33 (ℓ : ℕ → ℤ) (hℓ1 : ℓ 1 = 1) (h : TYZThm33Pinned ℓ) :
    Thm35First ℓ tyzZ
theorem thm35First_of_lcal_thm33 (h33 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → TYZThm33Pinned ℓ) :
    ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ
```

and, in `Final.lean`, cm-bridge's headline with `Thm35First` replaced (VERIFIED compiled, standard axioms):

```lean
theorem tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm33_lemma321Five
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hS : Shimura.ShimuraReciprocityModFn)
    (h318 : Lemma318Literal HHprime) (h33 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → TYZThm33Pinned ℓ)
    (h5 : Lemma321Five) : ZInQ.Literature.TYZThm35ReadingA
```

`Thm35First` is TYZ Theorem 3.5's first assertion (`P(n)` represents `𝒫(n)`; `𝒫(n) = 0` if `𝓛(n) = 0`);
TYZ derive it from Theorem 3.3 by the character formula and induction on `n` (L2343–2380). That
derivation is now Lean. Theorem 3.3 itself stays a leaf (as expected): its proof is the explicit
Gross–Zagier formula (TYZ Theorem A.9, from Yuan–Zhang–Zhang) plus Gross–Zagier/Kolyvagin and Néron–Tate
heights, none of which can be stated over genuine Lean definitions today.

## 1. What `Thm35First ℓ tyzZ` asks (VERIFIED by reading the Lean definitions)

`Thm35First ℓ Z` (verbatim copy of `Package.Thm35First`): for every squarefree `n ≡ 5 (mod 8)` there is
`ε : ℕ → ℕ → ℤ[i]` in TYZ's classes (`EpsClasses n ε`: `±i` on `(d₀,d₁) ≡ (5,3)`, `±1` on `(5,1)`, `(7,1)`,
`(7,3)`, for `d₀d₁ ∣ n`) such that `ℓ n = 0 → P(n)` is torsion in `A(ℚ̄)`, `A = X₀(32): y² = x³ + 4x`, where
`P = Pseq ℓ ε Z` is TYZ's recursion

`P(d) = Z(d) − Σ_{d₁ ∣ d, d₁ > 1, d₁ ≡ 1,3 (8)} ε(d/d₁, d₁) ℓ(d₁) P(d/d₁)` (TYZ L1320–1327; `ε` acts through
`[i]`).

For `Z = tyzZ` (cm-numeric/cm-bridge's pinned genus points):
* `e ≡ 5`: `Z(e) = Σ_{ρ∈Φ₀(e)} ρ(z_e)`, `z_e = (1 − [i]) f₀(P_e)`, `f₀(P_e)` the Heegner point of
  `[16(e+1), −8, 1]` (discriminant `−64e`), `Φ₀(e)` a chosen set of lifts to `Gal(ℚ̄/ℚ)` of Artin symbols
  of squares of `Pic(𝒪_{e,4})`, exactly one over each element of `2Cl_e` (`IsPhi0`).
* `e ≡ 7`: `Z(e) = Σ_{c∈2Cl_e} liftMax(c)(z_e)`, `z_e` the Heegner point of `[(e+δ²)/4, δ, 1]`
  (discriminant `−e`), `liftMax c` a lift of the Artin symbol of `c` on the Hilbert class field.

Only classes 5 and 7 occur in the recursion (`d ≡ 5, 7`, `d₁ ≡ 1, 3` ⇒ `d/d₁ ≡ 5, 7`); `ℓ` is read only
at `d₁ ≡ 1, 3` (squarefree) and at `n`, where `ℓ n = 0` means "no continuation of `L(E_n, s)` of order
`≤ 1` at `s = 1`" (`IsTYZLcal`). Nothing in the statement is junk-sensitive except that `z_e` must be
TYZ's point; cm-numeric/cm-bridge pinned and numerically checked it. The statement is neither vacuous
nor trivially true: for rank-≥2 `n` it says that a specific combination of Heegner points is torsion.

## 2. The leaf `TYZThm33Pinned ℓ` (Lean, §T of `Thm35.lean`)

Definitions (all over genuine objects):
* `gchar n T c = Π_{q∈T} sgn(χ_q(c))`, `χ_q([𝔞]) = (N𝔞/q)` the project's genus character
  (`RouteK.Redei.chi`), `T ⊆` primes of `n`, `c ∈ Cl(K_n) = Pic(OK n)`.
* `basePt n` = `z_n` (`CM.tyzZn n` for `n ≡ 5`, `tyzZ7 n` otherwise).
* `IsLiftFamily n f`: `f : Cl(K_n) → Gal(ℚ̄/ℚ)`, `f c` acts on `H_n` as the Artin symbol of `c`
  (Tau Ceti's `ringClassArtinEquiv`), and for `n ≡ 5` on `H_{n,4}` as the Artin symbol of some class of
  `Pic(𝒪_{n,4})`.
* `Pchi n f T = Σ_{c} gchar n T c • f(c)(z_n)` — TYZ's `P_χ = Σ_{t∈Φ} χ(t) z_n^t`.
* `pairSet n d₀ d₁` = primes of `d₁` if `d₁ ≡ 1 (mod 4)`, of `d₀` otherwise: TYZ's `χ_{d₀,d₁}`
  (the character of `K_n(√d₁) = K_n(√−d₀)` for `n ≡ 5`, of the unramified one of `K_n(√±d₁)` for `n ≡ 7`).
* `h2 n = #ramSet n − 1` (2-rank of `Cl(K_n)` by genus theory; `k` for `n ≡ 5`, `k − 1` for `n ≡ 7`).

```lean
def TYZThm33Pinned (ℓ : ℕ → ℤ) : Prop :=
  ∃ (Q : ℕ → PtA) (m : ℕ → ℕ) (ε : ℕ → ℕ → GaussianInt),
    (∀ d, 0 < m d) ∧
    (∀ d₀ d₁ : ℕ, d₀ % 8 = 5 → d₁ % 8 = 3 → ε d₀ d₁ = gi ∨ ε d₀ d₁ = -gi) ∧
    (∀ d₀ d₁ : ℕ, (d₀ % 8 = 5 ∧ d₁ % 8 = 1 ∨ d₀ % 8 = 7 ∧ d₁ % 8 = 1 ∨ d₀ % 8 = 7 ∧ d₁ % 8 = 3) →
      ε d₀ d₁ = 1 ∨ ε d₀ d₁ = -1) ∧
    (∀ n : ℕ, Squarefree n → n % 8 = 5 → ℓ n = 0 → IsOfFinAddOrder (Q n)) ∧
    ∀ n : ℕ, ∀ _ : NeZero n, Squarefree n → (n % 8 = 5 ∨ n % 8 = 7) →
      ∀ f : Pic (OK n) → GalQ, IsLiftFamily n f →
        (∀ d₀ d₁ : ℕ, d₀ * d₁ = n → (d₁ % 8 = 1 ∨ d₁ % 8 = 3) →
          IsOfFinAddOrder ((m d₀ : GaussianInt) • Pchi n f (pairSet n d₀ d₁) -
            (ε d₀ d₁ * 2 ^ h2 n * (ℓ d₁ : GaussianInt)) • Q d₀)) ∧
        (n % 8 = 5 → ∀ d₀ d₁ : ℕ, d₀ * d₁ = n → (d₁ % 8 = 5 ∨ d₁ % 8 = 7) →
          IsOfFinAddOrder (Pchi n f (pairSet n d₀ d₁)))
```

Reading: `𝒫(d) := Q(d)/m(d) ∈ A(ℚ̄) ⊗ ℚ` (one vector per `d`, the same at every level `n`), and
`P_{χ_{d₀,d₁}} = ε(d₀,d₁) 2^{h₂(n)} 𝓛(d₁) 𝒫(d₀)` in `A(ℚ̄) ⊗ ℚ` (`m P_χ − ε2^{h₂}ℓQ` torsion), `P_χ`
torsion for the excluded characters (`n ≡ 5`, `d₁ ≡ 5, 7`), and `𝒫(n) = 0` when `𝓛(n) = 0`.

**Why it is a consequence of the published results, not stronger.**
1. TYZ Theorem 3.3 (L1299–1311, quoted in `nt-tyz.md` §1.2): `P_χ` is non-torsion only for
   `χ = χ_{d₀,d₁}`, `d₀ ≡ 5,6,7`, `d₁ ≡ 1,2,3`; then `P_χ = ε(d₀,d₁) 2^{h₂(n)} 𝓛(d₁) 𝒫(d₀)` in
   `A(H'_n(i)) ⊗ ℚ`, `ε = ±i` on `(5,3)`, `±1` otherwise; `𝒫(d) = 2^{−1−ρ(d)}𝓛(d)α_d` (Theorem 3.5's
   statement), so `𝒫(n) = 0` if `𝓛(n) = 0` (L1295). Witnesses: `Q/m` any representation of TYZ's `𝒫`
   (rational multiple of `α_d`); `ε` TYZ's, multiplied by the sign of `ℓ(d₁)/𝓛(d₁)` (`IsTYZLcal`:
   `ℓ² = 𝓛²` on classes 1, 3; `ℓ 1 = 1 = 𝓛(1)`), extended arbitrarily in the classes to all pairs.
   `ℓ n = 0` ⇔ order `≥ 2` ⇔ `𝓛(n) = 0` (TYZ L338–345; the continuation exists by modularity).
2. The "excluded" clause for `n ≡ 5`: the `2^k` sets `T` give `2^k` distinct characters (genus theory;
   `RouteK.Redei.exists_chi_eq` proves the genus map is onto `𝔽₂^k` for `n ≡ 1 (mod 4)`), and the map
   `T ↔ (d₀, d₁)` is a bijection, so `χ_{d₀,d₁}` with `d₁ ≡ 5, 7` is none of the contributing characters.
3. The character convention (VERIFIED computed, `convention.out`, 26 values of `n`, 0 mismatches):
   `χ_{pairSet}` equals tyz-t1's `χ_{d₁} ↔ K(√d₁)` for `n ≡ 5` (the convention under which tyz-t1
   VERIFIED Theorem 3.3 numerically: 73 contributing pairs, 102 excluded characters, `tmany.py`), equals
   the character of the unramified `K(√±d₁)` for `n ≡ 7`, is a class invariant, and `χ_T = χ_{T^c}` for
   `n ≡ 7`. For `n ≡ 7` the leaf itself (with this convention) was tested here (`heeg7.py`, §6).
4. **HUMAN CHECK (source needed).** (a) `∀ f`: TYZ's `P_χ` is defined with their set `Φ` of
   representatives; the leaf quantifies over every lift family. For `n ≡ 7` this is harmless
   (`z_n ∈ A(H_n)`, cm-bridge `CMFieldOfDefinition7`). For `n ≡ 5` two lifts of `c` differ on `H'_n` by the
   kernel of `Cl'_n → Cl_n`, and the claim that this changes `P_χ` only by torsion rests on
   `Gal(H_{n,4}/H_n) = ⟨σ_{1+2ϖ}, σ_ϖ²⟩`, the first fixing `z_n`, the second adding `τ(1)` (TYZ Prop. 3.2,
   Thm. 3.6(1), as quoted in `tyz-t1.md` §3.1; `σ_{1+2ϖ}` is cm-bridge's derived `TYZSigmaFixesZn`).
   If TYZ's Theorem 3.3 is stated for an arbitrary `Φ`, the `∀ f` form is literally TYZ's. Numerically
   the fibre points agree mod torsion on 27 values (`fibre5.py`, §6). (b) TYZ's
   definition of `χ_{d₀,d₁}` (which of `K_n(√d₁)`, `K_n(√−d₁)`); fixed here by tyz-t1's numerics for
   `n ≡ 5` and by unramifiedness for `n ≡ 7`. (c) `h₂(n)` = 2-rank of `Cl_n` (`= k`, `k − 1`, tyz-t1 §2).
5. Not vacuous: `Q = 0` fails (rank-one `d₀`), and `Q` must serve every level `n` at once — the
   cross-level content that tyz-t1 §1 identifies as the substance of Theorem 3.3.

**Leaf or glue.** `TYZThm33Pinned` is a LEAF (published, refereed: TYZ Theorem 3.3 with Lemma 3.14, and
the definition of `𝒫`). Its constant rests on the computation TYZ do not print (L2014–2015), written out
and tested in `tyz-t1.md` (AI-derived; caveat inherited). Only the `n ≡ 5, 7` part of TYZ's theorem is
used (classes `6` never occur).

## 3. The glue (all proved; §G of `Thm35.lean`)

| step | Lean | content |
|---|---|---|
| torsion | `torG`, `quot_cancel` | torsion points as a `ℤ[i]`-submodule; `A(ℚ̄)/tors` torsion-free |
| character formula | `sum_gchar`, `sum_Pchi` | `Σ_T χ_T(c) = 2^k [c ∈ Cl²]` (`Finset.prod_add_one`, genus theory `picSquares_eq_iInf_ker_chi`); `Σ_T P_T = 2^k Σ_{c∈2Cl} z^{f c}` (TYZ L998) |
| product formula | `prod_sgn_chi_eq_one` | `Π_{q∣n} χ_q = 1` for `n ≡ 3 (mod 4)`: the genus map's image contains the sum-zero hyperplane (`exists_chi_eq`) and has order `#Cl[2] = 2^{t−1}` (`range_sq_eq_ker_genusMap_and_card`) |
| subsets ↔ divisors | `divSet_prod`, `prod_divSet`, `sum_finset_eq_sum_divisors`, `divSet_div` | `T ↦ Π T` bijection onto the divisors of squarefree `n`; complement = primes of `n/e` |
| characters ↔ pairs | `gmap_gmap`, `gmap_div`, `Pchi_compl`, `sum_Pchi_divisors` | `Σ_T P_T = Σ_{d₁∣n} P_{χ_{n/d₁,d₁}}` (involution for `n ≡ 1 (4)`; complement invariance for `n ≡ 3 (4)`) |
| contributing part | `sum_divisors_seven`, `contrib` | `n ≡ 5`: excluded terms torsion; `n ≡ 7`: `d₁ ↦ n/d₁` swaps excluded and contributing halves (factor 2 = `2^k/2^{h₂}`) |
| `Φ₀` as a lift family | `liftAny`, `exists_liftFamily` | a lift family `f` with `f(2Cl_n) = Φ₀(n)` (`n ≡ 5`, from `phi0_spec`, `artinO_inj`, `actsO_of_acts4`, `picToMax_surjective`), resp. `f = liftMax` (`n ≡ 7`), so `Σ_{c∈2Cl} z^{f c} = tyzZ n` exactly |
| level identity | `level_identity` | `M·Z(n) ≡ Σ_{d₁ contributing} R(d₁) ε ℓ(d₁) Q(n/d₁)` mod torsion (`M = Π m`, cancel `2^k`) |
| induction | `thm35First_of_thm33` | renormalize `ε'(d₀,d₁) = ε(d₀,d₁)ε(d₀,1)`, `Q' = ε(·,1)Q`; then `m(d)P(d) ≡ Q'(d)` by strong induction (TYZ L2343–2380); at `n` with `ℓ n = 0`, `Q(n)` torsion ⇒ `P(n)` torsion |

## 4. Compile status

`lake build ZInQKernel.Contrib.TYZGenus.RingClassBridge` (10286 jobs, clean), then
`lake env lean scratch/tyz-35/Thm35.lean`: 0 errors, no `sorry` (≈35 s), VERIFIED 2026-11-14.
`#print axioms` (`audit-out.txt`): `thm35First_of_thm33`, `thm35First_of_lcal_thm33`, `level_identity`,
`prod_sgn_chi_eq_one`, `sum_Pchi`, `exists_liftFamily`, `sum_Pchi_divisors`: all
`[propext, Classical.choice, Quot.sound]`.
`lake build ZInQKernel.Contrib.TYZGenus.ShimuraFricke` (10301 jobs, clean), then
`lake env lean scratch/tyz-35/Final.lean`: 0 errors, no `sorry`; `thm35First_of_lcal_thm33` and
`tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm33_lemma321Five`: `[propext, Classical.choice,
Quot.sound]`, VERIFIED 2026-11-13.

## 5. What remains / caveats

* `TYZThm33Pinned` is the leaf; formalizing it needs Néron–Tate heights on `A`, the explicit
  Gross–Zagier formula (YZZ / TYZ Theorem A.9) and Kolyvagin — out of reach today.
* HUMAN CHECK items of §2.4 (choice of `Φ`, convention for `χ_{d₀,d₁}`, `h₂`), all against
  `Period7.tex`, which is not on this host.
* PARI is not available on this host (`~/pyenv/bin/python` does not exist; cypari2 not in the offline
  uv cache). The numerics below are pure-Python re-implementations (double precision) of tyz-t1's
  Heegner model; they are samples, not proofs.

## 6. Numerical checks (VERIFIED computed; scripts and outputs in `scratch/tyz-35/`)

| script → output | what | sample | result |
|---|---|---|---|
| `convention.py` → `convention.out` | the leaf's `χ_{d₀,d₁} = χ_{pairSet}` equals tyz-t1's `χ_{d₁} ↔ K(√d₁)` (n ≡ 5), the unramified `K(√±d₁)` character (n ≡ 7); class invariance; `χ_T = χ_{T^c}` (n ≡ 7) | 26 n ≤ 4199 | 0 mismatches |
| `heeg7.py` → `heeg7.out` | **n ≡ 7 part of Theorem 3.3 as encoded in the leaf**: `16 P_{χ_{d₀,d₁}}(n) = ±16·2^{h₂(n)−h₂(d₀)}𝓛(d₁)·ε·P_{χ=1}(d₀)` mod `Λ`, `ε = i` on `(5,3)`, `1` on `(7,1)`; `P` torsion when `𝓛(d₁) = 0`; complements | 27 n ≡ 7, 15 ≤ n ≤ 903; 43 pairs with `d₁ > 1` (32 of type (5,3)), `𝓛(d₁) ∈ {0,1,2,3}`; 70 complement checks | 0 mismatches. First numerical test of the n ≡ 7 cross-level part (tyz-t1 tested only n ≡ 5 and χ = 1 at n ≡ 7) |
| `fibre5.py` → `fibre5.out` | HUMAN CHECK (a): within each fibre of `Pic(ℤ[4√−n]) → Cl(K_n)` (computed exactly) the conjugates of `f₀(P_n)` agree mod torsion, so `P_χ` does not depend on the lift family | 27 n ≡ 5, 5 ≤ n ≤ 445; 648 fibre pairs | 0 non-torsion differences; control: 1 of 1040 cross-fibre pairs torsion |

* Integration: `Thm35.lean` §0–§9 and `Final.lean` §0–§15 duplicate cm-bridge's definitions
  (namespace `TYZ35`); keep one copy when integrating. `Final.lean` uses tyz-cm's files as merged in
  cm-bridge (`ShimuraFricke`).

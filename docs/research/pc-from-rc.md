# pc-from-rc: Theorem 5.2 from Theorem 5.3 (fork issue #83)

Task pc-from-rc, 2026-11-17, base `19fdd483`. Lean 4.35.0, Mathlib v4.35.0.
Source: `diophantine_zq.tex` Section 5 (lines 973–1121), read for this task.

## Main result

**Proved in Lean** (no `sorry`; `#print axioms` gives only `propext`, `Classical.choice`,
`Quot.sound` for every theorem listed here):

```
ZInQ.Manuscript.PoleRC.poleCompleteness_of_restrictedConverse_final
    (SelmerCorankOne : WeierstrassCurve ℚ → Prop)
    (hRC : Manuscript.RestrictedConverse SelmerCorankOne)   -- Theorem 5.3 (target statement)
    (h54 : Lemma54At SelmerCorankOne)                       -- Lemma 5.4 at E_ℓ (interface)
    (hK  : KolyvaginRankOne)                                -- Lemma 5.5: BCDT Thm A + Kolyvagin Thm 1 (printed leaves)
    (hMW : MordellWeil)                                     -- Mordell's theorem (textbook leaf)
    (hR  : MatrixRealization)                               -- lines 1033–1060 (GLUE, ELLIOT: S11–S12)
    (hTwo : LocalTwo) (hThree : LocalThree)
    (hBad : LocalBad) (hGood : LocalGood) :                 -- local images of the Kummer map (textbook GLUE)
  Manuscript.PoleCompleteness                               -- Theorem 5.2 (target statement)
```

in `ZInQKernel/Contrib/OneProof/PoleCompletenessFromRC.lean`. The target statements
`Manuscript.PoleCompleteness` and `Manuscript.RestrictedConverse` in
`ZInQKernel/Hypotheses/PoleManuscript.lean` were not changed.

The two deliverables, also proved in Lean:

* **First deliverable.** `poleCompleteness_of_crm : CRM → SimultaneousConstruction →
  Manuscript.PoleCompleteness`. Here `CRM` says: in the domain of Theorem 5.3, an explicit 2-Selmer
  system of `E_ℓ` of dimension 3 that contains `(β, 1)` gives a rational point in the class
  `(β, 1)` (Kummer coordinates `(x + 3ℓ, x − ℓ)`). This proof contains the full squareclass
  bookkeeping (lines 1020–1032) and the rescaling to the eleven witnesses with `w = (eHz)⁻¹`
  (lines 1107–1121), with no further hypotheses. The simultaneous construction is then reduced to
  two Props: `simultaneousConstruction_of : MatrixRealization → DimThreeCount →
  SimultaneousConstruction`. The dimension-three count itself is proved
  (`dimThreeCount_of_local`) from the four local-image Props. Its core, "the local equations force
  `v = 0`, `δ = 0`, `u ∈ ker K`" (line 1068), is a Lean proof for the genuine matrix `K`
  (`kmat_forces`).
* **Second deliverable.** `crm_of_restrictedConverse : RestrictedConverse P → Lemma54At P →
  KolyvaginRankOne → MordellWeil → DescentGlueM → CRM`. The complete 2-descent `DescentGlueM` is
  proved (`descentGlueM`), so `CRM` follows from Theorem 5.3, the Lemma 5.4 interface and the
  Lemma 5.5 leaves alone.

**What remains open** (hypotheses of the final theorem):

| statement | kind | status |
| --- | --- | --- |
| `Manuscript.RestrictedConverse P` | Theorem 5.3, the target | open (proved in the manuscript's §§6–…; not this task) |
| `Lemma54At P` | interface for the abstract `SelmerCorankOne` | open by design: `P` is abstract; becomes Lemma 5.4 (Poonen–Stoll) once `P` and `Sel₂` are genuine |
| `KolyvaginRankOne` | LEAF, consequence of printed theorems (BCDT Thm A + Kolyvagin Thm 1) | printed leaf, unread (see item 0.5) |
| `MordellWeil` | LEAF, textbook (Mordell 1922; Silverman VIII.6.7, number UNVERIFIED) | printed leaf |
| `MatrixRealization` | GLUE, ELLIOT (manuscript cites S11–S12) | not proved; numerically supported (§5) |
| `LocalTwo`, `LocalThree`, `LocalBad`, `LocalGood` | GLUE, textbook local computations of the Kummer image of `E_ℓ` over `ℚ₂`, `ℚ₃`, `ℚ_q` (`q ∣ ℓ`), `ℚ_p` (`p ∤ 6ℓ`) | not proved; numerically supported (§5) |

`LocalReal`, the fifth local image (the real place), is proved (`localReal`).

## 0. Known issues with the cited sources and the text

1. **S11–S12.** The manuscript credits the simultaneous construction of `n` and `nθ` to its
   supplementary files S11–S12 (lines 1033–1035). As instructed, I did not use them.
   `MatrixRealization` is the explicit content of lines 1036–1060 and is labelled ELLIOT.
2. **The shape of a Selmer representative (line 1062) is asserted, not derived.** A class with
   positive second coordinate is written `(3^δ ∏ q_i^{u_i}, ∏ q_i^{v_i})`, with no factor `2` and
   positive first coordinate. This comes from the local images at the real place (`a > 0`) and at
   `2`. For `ℓ ≡ 3 (mod 4)` the image at `2` is `{a, b odd, b ≡ 1 (mod 4)}` (computed: VERIFIED
   by sampling); the text does not state this. ELLIOT. In Lean it is the hypothesis `LocalTwo`.
3. **"The matrix properties force v = 0, δ = 0, u ∈ ker K" (line 1068) uses more than the printed
   properties.** The Lean proof (`dimThree_linear_algebra`, `kmat_forces`) also needs:
   * three identities that come from quadratic reciprocity: `Kᵀ = K + ssᵗ + diag(s)`, `sᵗ1 = 1`
     (`ℓ ≡ 3 (mod 4)`) and `λᵗ1 = 0` (`(3/ℓ) = 1` for `ℓ ≡ 11 (mod 12)`);
   * duality (`λ ∉ im K` gives `w` with `wᵗK = 0` and `wᵗλ = 1`) and `rank Kᵀ = rank K`;
   * the 2-adic equation `sᵗv = σ`, and the classes with negative second coordinate.

   All of these are proved in Lean (`kmat_transpose`, `sgn_dot_one`, `lam_dot_one`,
   `exists_left_kernel_of_not_mem_range`, `card_ker_transpose`). The text states none of them
   (ELLIOT). The claim itself is correct.
4. **The Boolean assignment (lines 1055–1058) is a sketch.** "Free `q₀`-symbols toggle the new
   diagonal entries; the determinant's full-product coefficient is one." I read this as: the
   determinant is multilinear over `𝔽₂` in the free symbols, its top coefficient is the
   nonsingular `n`-block, and a nonzero multilinear polynomial takes a nonzero value. This reading
   is SPECULATIVE. The rank-one correction `K♯ = K + λaᵗ` leaves `a` undefined, and the link from
   the bordered matrix to `ker K = ⟨1, 1_β⟩` and `λ ∉ im K` is not spelled out. ELLIOT. Not
   formalized (an on-the-spot construction would be needed; per instructions, not built).
5. **Lemma 5.5 citations.** Kolyvagin is cited as the MPIM preprint MPI/90-69 (1990), "On the
   Mordell–Weil group and the Shafarevich–Tate group of modular elliptic curves", Theorems 1–5,
   pp. 4–5. This is a preprint, not a refereed print. A paper with that title is in the
   Proceedings of the ICM 1990 (Kyoto); that is from memory, UNVERIFIED. BCDT is cited as the
   author manuscript; the refereed version is J. Amer. Math. Soc. 14 (2001) 843–939 (STANDARD).
   Neither was read for this task; theorem numbers are as the manuscript gives them (UNVERIFIED).
6. **Lemma 5.4** has a proof in the manuscript (Kummer sequence plus Cassels–Tate, Poonen–Stoll,
   Ann. of Math. 150 (1999)). With `SelmerCorankOne` abstract it can only enter as an interface
   hypothesis (`Lemma54At`). It becomes Lemma 5.4 only when `SelM` is identified with
   `Sel₂(E_ℓ/ℚ)` (Silverman X.1.4) and `P` with the corank predicate.
7. **The route needs only "rank ≥ 1" from Lemma 5.5.** Once `#SelM ℓ = 8`, a point of infinite
   order already makes the Kummer map onto (`descentGlueM`). Finiteness of `Ш` and Kato
   Corollary 14.3 (cited for `r = 0`) are not used.

No statement was found false.

## 1. Files (all new; every file imports only `PoleManuscript.lean`, Mathlib, other PoleRC files and proved Route K modules; none imports `ZInQKernel.OneProof.Main`)

| file | content |
| --- | --- |
| `Contrib/PoleRC/Defs.lean` | `LocM` (Kummer image in x-form), `SelM` (explicit 2-Selmer system), `CRM`, `SimultaneousConstruction` |
| `Contrib/PoleRC/Rescale.lean` | `point_of_locM`, `polePoly_eq_zero_of`, `witnesses_of_points` (lines 1107–1121) |
| `Contrib/PoleRC/Bookkeeping.lean` | `bookkeeping` (lines 1020–1032) |
| `Contrib/PoleRC/Reduction.lean` | `poleCompleteness_of_crm` |
| `Contrib/PoleRC/CRM.lean` | `Lemma54At`, `KolyvaginRankOne`, `MordellWeil`, `DescentGlueM`, `crm_of_restrictedConverse` |
| `Contrib/PoleRC/Matrix.lean` | `lsym`, `Kmat`, `lam`, `sgn`, `oneB`, `MatrixConditions`, `DimThreeCount`, `MatrixRealization`, `simultaneousConstruction_of` |
| `Contrib/PoleRC/LinAlg.lean` | `dimThree_linear_algebra` (abstract `𝔽₂`) |
| `Contrib/PoleRC/Recip.lean` | reciprocity identities for `Kmat`, `kmat_forces` |
| `Contrib/PoleRC/QClass.lean` | square classes at odd `q` (`qcls`), multiplicativity |
| `Contrib/PoleRC/Count.lean` | `LocalReal` (proved), `LocalTwo`, `LocalThree`, `LocalBad`, `LocalGood`, `dimThreeCount_of_local` |
| `Contrib/PoleRC/KummerM.lean` | Kummer maps of `E_ℓ` at its roots are homomorphisms |
| `Contrib/PoleRC/DescentM.lean` | `deltaM`, halving lemma, `ker δ = 2E`, image in `SelM`, `#E[2] = 4`, `descentGlueM` |
| `Contrib/OneProof/PoleCompletenessFromRC.lean` | the final theorems |
| `scratch/pc-from-rc/` | `log.md`, numerical checks (`*.py`), axiom checks, `#discharges` output, `autofold.json` |

About 2700 lines of Lean in total.

## 2. The statements

`E_ℓ : y² = x(x − ℓ)(x + 3ℓ)` (`Manuscript.curve`). Kummer coordinates `(x + 3ℓ, x − ℓ)`.

* `LocM K ℓ a b`: either `a, b` are squares, or some `x ∈ K` makes `(x + 3ℓ)/a`, `(x − ℓ)/b` and
  `x/(ab)` squares (zero allowed). For `a, b ≠ 0` this says `(a, b)` is in the Kummer image of
  `E_ℓ(K)`. The direction "image ⇒ `LocM`" is proved over `ℚ` (`locM_of_deltaM`).
* `SelM ℓ`: pairs of squarefree integers with `LocM` over `ℝ` and every `ℚ_p`; `ncard = 8` is
  dimension 3.
* `CRM`: `∀ ℓ > 0` squarefree, `ℓ ≡ 11 (mod 12)`, `#SelM ℓ = 8 → (β, 1) ∈ SelM ℓ → LocM ℚ ℓ β 1`.
* `MatrixConditions ℓ β`: `1_β ∉ {0, 1}`, `K1_β = 0`, `ker K ⊆ {0, 1, 1_β, 1 + 1_β}`, and
  `λ ∉ im K`, with `(Kv)_i = Σ_{j≠i}[q_j/q_i](v_j + v_i)` and `λ_i = [3/q_i]` over the primes of `ℓ`.
* `MatrixRealization`: for `β, θ` positive squarefree with `β ≡ 17`, `θ ≡ 1 (mod 24)`, coprime and
  mutually local squares, there is `n > 0` with `n ≡ 11 (mod 12)`, `nθ` squarefree, `β ∣ n`, such
  that `MatrixConditions n β` and `MatrixConditions (nθ) β` both hold.
* `LocalTwo`: for squarefree `ℓ ≡ 3 (mod 4)` and squarefree `a, b`: `LocM ℚ₂ ℓ a b ↔ a` odd `∧ b ≡ 1 (mod 4)`.
* `LocalThree`: for squarefree `ℓ ≡ 2 (mod 3)`: `LocM ℚ₃ ℓ a b ↔ b ≡ 1 (mod 3)`.
* `LocalBad`: for `q ∣ ℓ`, `q ≠ 2, 3`: `LocM ℚ_q ℓ a b ↔ (a, b) ∈ ⟨(ℓ, 1), (3, −ℓ)⟩` in square
  classes at `q`.
* `LocalGood`: for `p ∤ 6ℓ`: `LocM ℚ_p ℓ a b ↔ p ∤ a ∧ p ∤ b`.
* `KolyvaginRankOne`: `∀ E/ℚ` elliptic, `AnalyticRankOne E → Module.rank ℤ E(ℚ) = 1`.
* `MordellWeil`: `∀ E/ℚ` elliptic, `E(ℚ)` is finitely generated.

## 3. Ratings of the new leaves

* `KolyvaginRankOne`: **printed form, as a consequence.** It combines BCDT Theorem A
  (modularity) with Kolyvagin Theorem 1, over Mathlib's `LSeries` and `Point`. The Lean statement
  keeps only the rank, since Mathlib has no `Ш`, so it is weaker than the print. It combines two
  prints in the way `Literature.GrossZagier` does. Flag: "unread: new printed leaf; locator
  UNVERIFIED (MPIM preprint MPI/90-69; BCDT JAMS 2001)".
* `MordellWeil`: **printed form** (textbook theorem). Flag: unread, locator UNVERIFIED.
* `Lemma54At`: **not a leaf**; an interface on the abstract predicate (item 0.6).
* `LocalTwo/Three/Bad/Good`: **glue**, not printed in this form. They are standard local
  computations (for example Silverman X.1 and X.4 and the exercises there). Each is numerically
  supported.
* `MatrixRealization`: **glue**, ELLIOT.

## 4. The proof as formalized

1. `bookkeeping`. Write `B = N/D²` and `N = k²r` with `r` squarefree. Let `r₀ = gcd(r, 2730)` and
   `r₁ = r/r₀`. Choose `f ∈ {1,5,7,13,35,65,91,455}` with `f r₁ ≡ 17 (mod 24)`; these eight
   numbers represent `(ℤ/24)ˣ`. Set `m = r₀f/gcd(r₀,f)²` (a positive divisor of `2730`, giving
   the bits `bᵢ`), `β = f r₁`, and `A = mB = β s²`. Let `θ` be the squarefree part of
   `T = D² − N/m ≡ 1 (mod 24)`; then `H = T(mB/D)²`. The local squares hold in `ZMod p`.
2. `SimultaneousConstruction` ⇐ `MatrixRealization` + `DimThreeCount`.
3. `DimThreeCount` from the local images (`Count.lean`):
   * **Necessity.** A Selmer class has `a > 0` and `a, b` supported on `{3} ∪ supp ℓ`. Its local
     conditions give `E1: Ku + λ∘v = δλ`, `E2: Kv + s∘v = σs`, `E3: sᵗv = σ`, `E4: (λ+s)ᵗv = σ`,
     through `qcls` computations.
   * `kmat_forces` then gives `v = σ1`, `δ = σ` and `Ku = 0`.
   * `(a, b) ↦ (ind a, σ(b))` is injective on `SelM`, with image `{0, 1, 1_β, 1+1_β} × 𝔽₂`.
   * **Sufficiency.** The eight classes `(3^σ c, (−ℓ)^σ)` with `c ∈ {1, ℓ, β, ℓ/β}` lie in `SelM`.
4. `CRM` at `n` and `nθ`. `witnesses_of_points` takes `q = t₁/s`, `e = n/q²`, rescales the second
   point by `c², c³` and divides by `q², q³`, giving `z = c t₂/(sq)` and `w = (eHz)⁻¹`.
5. `CRM` from Theorem 5.3: Lemma 5.4 gives `P(E_ℓ)`, Theorem 5.3 gives analytic rank 1, and
   `KolyvaginRankOne` gives rank 1, hence a point of infinite order. Mordell–Weil and
   `descentGlueM` then give the conclusion. `descentGlueM` combines:
   * the Kummer homomorphism (chord identity from Mathlib's `addPolynomial_slope`);
   * the halving lemma `x' = x + r₁r₂ + r₁r₃ + r₂r₃`, with tangent slope `r₁ + r₂ + r₃`;
   * `ker δ = 2E` (`ℓ` is not a square, since `ℓ ≡ 3 (mod 4)`), and `#E[2] = 4`;
   * Route K's counting lemma `eight_le_card_quotient_two`.

## 5. Numerical checks (plain python3; PARI and sympy are not installed on this host)

* `local2.py`: for `ℓ ≡ 3 (mod 4)` (all residues mod 32) the 2-adic image is exactly
  `{a odd, b ≡ 1 (mod 4)}`. VERIFIED (sampled).
* `compare.py`: for all 55 squarefree `ℓ < 700`, `ℓ ≡ 11 (mod 12)`, the brute-force Selmer set
  (local searches at `p ∣ 6ℓ` and over `ℝ`) equals the set predicted by the five local images.
  0 mismatches. VERIFIED.
* `localprops.py` (checks each local Prop separately, including a good prime): did not finish
  within its time limit; NOT RUN to completion.
* `selmer.py`: at `ℓ = 323` and `ℓ = 5627 = 17·331`, `MatrixConditions` holds and brute force
  gives `#Sel = 8` with `(17, 1) ∈ Sel`. VERIFIED.
* `batch.py`, `batch2.py`: for 60 random `(β, θ)` (30 with `θ = 1`, 30 with `θ > 1`, all with
  the bookkeeping conditions), a random search over the slot shape `n = β q₀ p₁⋯p_{d−1}`
  (`q₀ ≡ 7`, `p_k ≡ 1 (mod 12)`) finds `n` with `MatrixConditions` for `n` and `nθ` in all 60
  cases. This is evidence for `MatrixRealization`, not a proof.

## 6. `#discharges` and autofold

`Manuscript.PoleCompleteness` is not a field of any bundle of `ZInQ.OneProof.frozenTarget`. The
`#discharges` run (`scratch/pc-from-rc/discharges-output.txt`; 34 open hypotheses, 12080 theorems
checked) therefore lists no PoleRC theorem. Autofold does not apply: no bundle field changes.
`scratch/pc-from-rc/autofold.json` records this and lists the new leaves with their kinds and
flags, for use if the manuscript-faithful headline (issue #74) takes `PoleCompleteness`.

## 7. What remains, in order of value

1. **`MatrixRealization`** (ELLIOT). It needs a precise construction: a symbol pattern for the
   slots, proved to satisfy the matrix conditions for `n` and `nθ`. The realization by primes in
   prescribed classes (reciprocity, CRT, Dirichlet `Nat.setOf_prime_and_eq_mod_infinite`) is
   standard and could be done in Lean. The pattern needs a lead decision: the text's sketch has to
   be completed on the spot.
2. **The local images.** The "only if" halves are `p`-adic valuation arguments; Route K's
   `Selmer/BadOdd.lean`, `Two.lean` and `Good.lean` are models. The "if" halves are needed only for
   the eight classes; at `2`, `3` and `q ∣ ℓ` they reduce to torsion points, because `LocM`
   depends only on square classes. The genuinely hard part is `LocalGood`'s "if" half: unramified
   classes are soluble at good primes. That needs `#E(ℚ_p)/2E(ℚ_p) = 4` or a point count over
   `𝔽_p`. Route K's character-sum proof is specific to `y² = x³ − d²x` and does not transfer.
3. `Lemma54At`: fix `SelmerCorankOne` (another design pass).

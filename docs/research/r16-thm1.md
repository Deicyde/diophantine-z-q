# r16-thm1: Shimura 1973 Theorem 1 (AI page read) in place of the Diamond–Shurman rows `afShimura`, `heckeJ1DS`

Task r16-thm1 (round 2 of r16-shimura73, 2026-11-17). Lean: `ZInQKernel/Contrib/OneProof/R16Thm1.lean` (namespace
`R16Thm1`; imports `R16ShimuraLi` from round 1 and `R16CoreYDS965`). Scratch: `scratch/r16-thm1/` (log `log.md`).
Round 1: `docs/research/r16-shimura73.md`.

## Main result

* **`afShimura` and `heckeJ1DS` are discharged** without Diamond–Shurman citations (VERIFIED, compiled, standard
  axioms):
  * `heckeJ1DS_of_bSh : BShStandardModel → AfTateLam.HeckeJ1DS`. B-Sh is the ON THE SPOT bridge "Shimura's
    standard model with `ξ_p`, `⟨d⟩` is the kernel's `IsX1Gen` model with `IsHeckeT`, `IsDiamond`". Its Lean
    content (existence of those operators over `ℚ`) is the statement of `HeckeJ1DS`. The fold changes the
    supplier, from Diamond–Shurman §6.3/§7.9 to Shimura's standard model, which Shimura 1971 §7.3 defines. That
    book is not cited by the manuscript. The mathematical content stays the same.
  * `afShimura_of_shimura73 : ShimuraThm1Printed → ShimuraQuotientIsAf → AfTateLam.AfShimura`.
    `ShimuraThm1Printed` is restated to match the read: (i)–(iii) unconditional, and the Euler clause total with its
    Fricke proviso. The action clause `IsAfAction` is **derived in Lean** from clause (ii). For `T_p` this is
    direct. For `⟨d⟩` the proof uses (ii) at `n = p²` with `ξ_{p²} = T_p² − p⟨p⟩` at a prime `p ≡ d (mod N)`
    (Dirichlet, Mathlib) and `a_p² − a_{p²} = χ(p) p`.
* **One glue step is needed, and the read does not supply it:** `ShimuraQuotientIsAf` says Shimura's quotient is
  Diamond–Shurman's `J/I_f J` (`ν` kills `I_f J` and is universal). The kernel needs it only because
  `afCharpolyDS965` (kept as is, flagged) is phrased over DS's `J/I_f J`. See Known issues 2.
* **Li supplies the proviso:** `euler_of_shimura73_li` (proved) shows the leaf's `A` satisfies the total Euler
  identity. As in round 1, this does not give the per-embedding characteristic polynomial, so `afCharpolyDS965`
  (DS 9.6.5) stays, flagged. Whether to restate `R16CoreY` in total form with Brauer–Nesbitt glue or to keep
  DS 9.6.5 flagged is the owner's call.
* **Fold:** `scratch/r16-thm1/autofold.json`, no generation step (both fields are top fields of
  `OpenResearchLeaves48`). Dry run `strict count: 4/27 on 31 -> 4/28 on 32; strictest 4/27 -> 4/28`, so **+1 GLUE**
  and `--allow-rise` is needed. `igusaGL2DS*` is untouched.

## Known issues (exact locations)

1. **Misprint in Shimura 1973, Theorem 1, Euler-factor clause** (pp. 526–527; AI page read): "`a_n^σ f`" should
   read "`a_n^σ f_σ`". Harmless: the intended meaning is clear and the leaf states the corrected form.
2. **The read's clauses (i)–(iii) do not pin Shimura's `A` as `J/I_f J`** (this task; not a source error).
   Clauses (ii)–(iv) are unchanged if `ν` is composed with an isogeny `A → A'`. So "quotient" must mean connected
   kernel for the printed uniqueness to hold, and the leaf reads it that way (`KerConnected`, reading-dependent).
   Even then, `ker ν = I_f J` needs `dim J/I_f J ≤ [K_f : ℚ]`, which is multiplicity one. This is named as the glue
   `ShimuraQuotientIsAf`; the proof sketch (ON THE SPOT) is in its docstring. A reader of p. 527 should record the
   exact wording of (i) and of the uniqueness clause. If the print says the quotient is `J/𝔞J` with `𝔞` the
   annihilator of `f` (SPECULATIVE), the glue becomes a consequence of the leaf.
3. **The curve is Shimura's "standard model", which the 1973 paper defines only by citing Shimura 1971 §7.3.**
   That book is cited neither by the manuscript nor in the theorem's statement. The bridge to the kernel's model and
   operators is `BShStandardModel`, ON THE SPOT.
4. **Kept from round 1 (Known issue 1 there):** the manuscript's inference at diophantine_zq.tex L770–773 passes
   from the total Euler identity to "`r_5` is a constituent of the Tate module of `A_f`". That needs per-embedding
   traces: Faltings semisimplicity, then Chebotarev or Brauer–Nesbitt, then the traces per embedding. None of these
   is written. Not repaired here.
5. **Kept from round 1 (Known issue 3 there):** applying Li to every `f_σ` needs the conjugates to be newforms
   (`ConjNewform`). This is uncited at the step.

## 1. The leaves and glue (Lean: `R16Thm1.lean`)

| name | statement | kind | printed form? |
| --- | --- | --- | --- |
| `ShimuraThm1Printed` | for a newform `f ∈ S₂(Γ₁(N))` (`N ≥ 2`, nebentypus `χ`), any model `X` with `IsX1Gen`, Jacobian `J`, and `T_p`, `⟨d⟩` with `IsHeckeT`/`IsDiamond`: `K_f` finite; `∃ A ν θ` with (i) `ν` surjective, `ker ν` connected; (ii) `ν ∘ ξ_n = θ(a_n) ∘ ν` in `Hom⁰` (integral form `HeckeCompat`) at `n = p` and `n = p²`, `p ∤ N`, `ξ_{p²} = T_p² − p⟨p⟩`; (iii) `dim A = [K_f : ℚ]`; and `FrickeStable → EulerIdentity` (total, over all embeddings) | published (pending review) | **Yes, printed form, weakened**: the AI page read's Theorem 1 at `Γ = Γ₁(N)`. Dropped: (iv) (no cotangent/q-expansion dictionary for `J₁(N)` in the kernel, no consumer), uniqueness (wording not in the read note), the proviso's `Γ₀(N)` branch (this instance is `Γ₁(N)`). (ii) is used only at `n = p, p²`. The Euler clause's exceptional set is unspecified. Two reading-dependent points: "quotient" as connected kernel (Known issues 2), and `ξ_{p²} = T_p² − p⟨p⟩`, which is Shimura's Hecke relation `T(p)² = T(p²) + p T(p,p)` (Shimura 1971 §3.5, number UNVERIFIED), part of B-Sh. |
| `BShStandardModel` | for every model `X` with `IsX1Gen`, a rational point and Jacobian `J`: `∃ T_p, ⟨d⟩ ∈ End(J)` over `ℚ` with `IsHeckeT`, `IsDiamond` | consequence (GLUE) | **No, ON THE SPOT**: not printed in Shimura 1973. It would rest on Shimura 1971 §7.2–7.3 (unread, uncited). Same Lean statement as `HeckeJ1DS`. |
| `ShimuraQuotientIsAf` | for `(A, ν, θ)` with Shimura's clauses (i)–(iii): `KillsIf ν` and universality among homomorphisms killing `I_f J` | consequence (GLUE) | **No**: glue. Proof sketch ON THE SPOT: (a) (ii) plus `Hom` torsion-free gives `ν` kills `I_f J`; (b) multiplicity one gives `ker ν = I_f J` (Shimura 1971 Thm 7.14 / DS Prop. 6.6.4, UNVERIFIED); (c) `J → J/B` is universal. |
| `LiFrickePrinted`, `ConjNewform` | unchanged from round 1 | as round 1 | as round 1 (Li: printed form, locator UNVERIFIED; ConjNewform: GLUE, uncited) |

Definitions: `comp`, `HeckeCompat` (`∃ m > 0, e`: `m x = 1 ⊗ e`, `m (ν ∘ t) = e ∘ ν`; equivalent to the `Hom⁰`
equation because `Hom` is torsion-free, and it is the weaker form), `KerConnected` (no non-trivial factorization of
`ν` through an isogeny; uses the kernel's `IsIsogenyMor`), `unitOf`, `xiSq`, `ShimuraClauses`. No new structures.

The round-1 `R16ShimuraLi.ShimuraThm1Printed` (existential `A`, no Hecke compatibility) is superseded by
`R16Thm1.ShimuraThm1Printed`. It is left in place, since the round-1 report and spec refer to it.

## 2. Proofs (VERIFIED, compiled; `scratch/r16-thm1/Axioms-output.txt`: `[propext, Classical.choice, Quot.sound]`)

* `heckeJ1DS_of_bSh` (`:= h`).
* `isAfAction_of (h2 : 2 ≤ N) (hf : IsNormalizedEigenform f χ) (hQ : IsAfQuotient …) (hT …) (hS …) : IsAfAction …`.
  It uses the glue lemmas `postC`/`preC` (composition is additive), `Rel` closed under `*`, `−` and natural
  casts, `nsmul_cancel` in `End⁰ = ℚ ⊗ End`, `exists_rel` (universality), `hom_ext_of_isAfQuotient` (reproved;
  `HeckePin` is not in the build), `coeff_sq_relation`, and Mathlib's `Nat.forall_exists_prime_gt_and_eq_mod`.
* `afShimura_of_shimura73`, `euler_of_shimura73_li` (uses round 1's `frickeStable_of_li`), and
  `r16CoreY_of_shimura73 : BShStandardModel → ShimuraThm1Printed → ShimuraQuotientIsAf → AfCharpolyDS965 →
  IgusaGL2DS → MumfordTorsionAlgClosed → R16CoreY`.

## 3. Fold (`scratch/r16-thm1/autofold.json`)

* Discharges `heckeJ1DS := R16Thm1.heckeJ1DS_of_bSh n.bShStandardModel` and
  `afShimura := R16Thm1.afShimura_of_shimura73 n.shimuraThm1Printed n.shimuraQuotientIsAf`. **No generation step**:
  both are fields of the top bundle `OpenResearchLeaves48`, unlike round 1's `r16CoreY`.
* Dry run, in the worktree (`--dry-run` writes nothing): `strict count: 4/27 on 31 -> 4/28 on 32; strictest 4/27 ->
  4/28` (`--allow-rise` needed). Output: `scratch/r16-thm1/FoldDryRun.lean.txt`.
* `scratch/r16-thm1/FoldCheck.lean` (the dry-run module with line 1 stripped) compiles.
  `HDec.HSyn.sixContactMin_of_open68` depends on `[propext, Classical.choice, Quot.sound]`.
* The fold was applied for real on a temporary copy (`git archive HEAD` into `/tmp`, nothing in the worktree). It
  wrote TailZ75 and switched Main to `sixContactMin_of_open68`. `render_open.py --check` there only complains that
  OpenStatements is not regenerated (that needs the Lean build: the maintainers' next step).
* **GLUE count against the base:** base 4 LEAF / 27 GLUE on 31. After the fold: 4 / 28 on 32. Out go
  `heckeJ1DS` (GLUE) and `afShimura` (GLUE). In come `bShStandardModel` (GLUE), `shimuraThm1Printed` (GLUE while
  pending review) and `shimuraQuotientIsAf` (GLUE). If a reviewer rates `shimuraThm1Printed` LEAF (the AI page read
  counts as a reading), the count becomes 5 / 27 on 32.
* **`#discharges`** (`scratch/r16-thm1/DischargesCheck-output.txt`): "36 open hypotheses, 15794 theorems checked,
  21 discharge one", including
  `DISCHARGES [OpenResearchLeaves48.afShimura] by R16Thm1.afShimura_of_shimura73, still assumes:
  [R16Thm1.ShimuraThm1Printed, R16Thm1.ShimuraQuotientIsAf]` and
  `DISCHARGES [OpenResearchLeaves48.heckeJ1DS] by R16Thm1.heckeJ1DS_of_bSh, still assumes:
  [R16Thm1.BShStandardModel]`, both with standard axioms.
* **Exact kinds rows** (from the temporary fold; `scratch/r16-thm1/kinds-diff.txt`). Removed: `afShimura`,
  `heckeJ1DS`. Added (bundle `research`, rated_by `r16-thm1; pending review`; packet, label, tier and area_issue
  copied from the old rows, area `elliotglazer/diophantine-z-q#37`):
  * `shimuraThm1Printed`: published, GLUE/GLUE. Flag: "pending review: new printed leaf from the AI page read of
    Shimura 1973 Thm 1 (counts as a reading under the owner's ruling); 'quotient' read as connected kernel
    (reading-dependent); misprint in the Euler clause ('a_n^sigma f' for 'a_n^sigma f_sigma') recorded in
    docs/research/r16-thm1.md". Source: Shimura, J. Math. Soc. Japan 25 (1973), 523–544, Theorem 1 (pp. 526–527;
    AI page read).
  * `bShStandardModel`: consequence, GLUE/GLUE. Flag: "pending review: ON THE SPOT bridge B-Sh …; rests on Shimura
    1971 sections 7.2-7.3 (unread, not cited …)".
  * `shimuraQuotientIsAf`: consequence, GLUE/GLUE. Flag: "pending review: glue, not a statement of Shimura 1973
    Thm 1 as read; needed only because afCharpolyDS965 is phrased over DS's J/I_f J; proof sketch ON THE SPOT uses
    multiplicity one (Shimura 1971 Thm 7.14 / DS Prop 6.6.4, numbers UNVERIFIED)".
* **Recommendation.** The fold is ready and compiles. It replaces Diamond–Shurman by the manuscript's own source
  (Shimura 1973 Thm 1) for the quotient and the Hecke action. The cost is one more GLUE row, and the glue's own
  proof sketch still uses multiplicity one, which is DS 6.6.4 or Shimura 1971. Fold if the owner wants the
  manuscript's sources visible on the rows; otherwise the DS rows are no weaker.

## Manuscript check

The r16 route is the paragraph diophantine_zq.tex L755–794 ("Modularity and a uniform conductor bound"), from the
newform `f` to the Tate-module constituent and its use at three and five.

| tex lines | step | verdict | reason |
| --- | --- | --- | --- |
| L767–768 | absorb the finite character, take the primitive newform `f` | OK | standard newform theory (Atkin–Lehner–Li). The Lean `R16CoreY` starts from a newform. |
| L768–770 | Li's Fricke formula (Li 1975, p. 296, before Lemma 6) makes the span of the coefficient conjugates Fricke-stable | gap filled | Li's formula is for newforms. Applying it to every `f_σ` needs the conjugates to be newforms (`ConjNewform`, uncited, GLUE). With that, Lean proves `FrickeStable` (`R16ShimuraLi.frickeStable_of_li`). Li's page is not read (UNVERIFIED locator). |
| L770–771 | Shimura's quotient construction (Shimura 1973 Thm 1, unconditional (i)–(iv)) | OK | per the AI page read: the `ℚ`-rational quotient, the `K_f`-action compatible with `ξ_n`, and `dim A = [K_f : ℚ]` are printed without proviso. The manuscript does not need `A = J/I_f J`, which only the kernel's DS-phrased rows need (Known issues 2). The curve is Shimura's standard model (Shimura 1971 §7.3, uncited; Known issues 3). |
| L771 | Shimura's Euler-factor identity under the proviso | OK | the print's proviso (`Γ = Γ₀(N)` or `span{f_σ}` Fricke-stable) is what L768–770 supplies. The clause is total, over all embeddings (`euler_of_shimura73_li`, proved from the leaves). Misprint "`a_n^σ f`" for "`a_n^σ f_σ`" in the print (Known issues 1). |
| L771–773 | "therefore" `r_5` is a constituent of the Tate module of `A_f` | unverified (gap, not filled) | the total Euler identity does not see `θ`. The conclusion needs Faltings semisimplicity, then Chebotarev or Brauer–Nesbitt, then per-embedding traces, and none of these is written (round 1, Known issue 1). The Lean route instead uses DS 9.6.5 (`afCharpolyDS965`, flagged). |
| L773–774 | dual: `r_5^∨` is a cohomological constituent; duality preserves the conductor | OK | the conductor of the contragredient equals the conductor (inertia invariants of `V` and `V^∨` have the same dimension, and Swan conductors agree). Not on the Lean route, which uses the Tate-module normalization. |
| L776–794 | `r_3` identified with the modular Tate representation (ℓ-independence on the reduction, Chebotarev, semisimplicity) | unverified | uses the modular traces at three per embedding, so it needs the same per-embedding input as L771–773. The Lean route does not use `r16` at three (round 1, §4). |

## What remains

* A reader of Shimura 1973 p. 527 should record the exact wording of clause (i) and of the uniqueness clause.
  Under the reading "quotient `J/𝔞J`", `ShimuraQuotientIsAf` follows from the leaf. Otherwise it stays glue, whose
  proof uses multiplicity one.
* B-Sh needs Shimura 1971 §7.2–7.3 read, or an argument that the kernel's `IsX1Gen` model with DS's double cosets
  is Shimura's standard model.
* The owner's call on `afCharpolyDS965`: keep DS 9.6.5 flagged, or restate `R16CoreY` in total form with
  Brauer–Nesbitt glue.

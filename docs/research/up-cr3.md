# up-cr3: the pole-completeness side in upstream Versions 13–16 and the 214-variable proposal

Status: research note (task up-cr3, 2026-11-11). Base: `origin/main` 520e27e5. The step log is
`scratch/up-cr3/log.md`; scripts and outputs are in `scratch/up-cr3/`. No Lean was run. No file
under `ZInQKernel/`, `blueprint/` or another note was changed.

Sources read (read-only):
- `~/upstream`, branch `codex/version16-fable-corrections`, commit d76bcde:
  - `manuscripts/quartic_v13.tex`, `quartic_v14.tex`, `quartic_v16.tex`;
  - `research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex` (CRLF line endings);
  - `research/version16/` (README, FINDINGS.json, protocol/CURRENT-CORRECTIONS.md,
    review/current/REVIEW.md);
  - `docs/manuscript-revisions/version10/sources.json`;
  - for the history, `manuscripts/quartic_v9.tex` through `quartic_v12.tex`.
- `~/upstream-p214`, branch `proposal/quartic-214-protocol-d`, commit 110cf72:
  `research/quartic214/PROOF.md` and `proofs/source-carry.md`, `proofs/existence.md`.
- N5 = `diophantine_zq.tex` in this worktree.

Line numbers are those of the files above; "V16 1736" means `quartic_v16.tex` line 1736. Upstream
text is paraphrased. Quotations are at most a line.

Marks:
- **VERIFIED**: read in the source (version, file and line given), or checked by a script in
  `scratch/up-cr3/`.
- **STANDARD**: a published theorem, with a reference.
- **SPECULATIVE**: an assessment.

## Verdict

**No.** No upstream version gives a route that lets the fork narrow or remove CR₃. None gives a
cheaper published input than Tian–Yuan–Zhang with Proposition N and Gross–Zagier.

1. From N5 through V16, the pole side is the same mathematics. The template is
   `E_ℓ : y² = x(x−ℓ)(x+3ℓ)`. PC is deduced from a restricted 2-converse RC for the non-CM
   curves `E_ℓ` with `ℓ ≡ 11 (mod 12)`. Points come from Kummer exactness once rank 1 and
   finite Ш are known. (VERIFIED, §1.)
2. RC is still proved inside the manuscript, in about 8,300 lines (V16 2570–6720 and
   Appendices 13339–17543). It is modelled on two unrefereed OpenAI preprints of 7 October
   2026, which the manuscript cites "for attribution" only. Version 16's own release records
   say that the audit behind it left two RC sources unread: Kato 1999 and Ribet 1990. (VERIFIED,
   §1.3, §3.)
3. Every later pole module also takes its completeness from the same RC. This covers V16's
   seven-variable `Ψ(b)` and the "linear-unit ordinary pole" in the quartic constructions, and the
   214-variable proposal. None uses explicit points, rationally connected fibres or another
   converse theorem. (VERIFIED, §1.4–1.5.) So upstream claims no design that the barriers
   exclude, and the two do not disagree anywhere (§1.6).
4. Upstream has none of the fork's fixes on this side. It keeps the template `x + 3ℓ`. It never
   cites Tian–Yuan–Zhang, Kriz or Smith. It keeps Kolyvagin's theorem, and BCDT through
   Silverman, even where rank ≥ 1 would suffice. Its analog of Proposition 0 is an unproved prose
   paragraph. (VERIFIED, §2.)

Replacing CR₃ by upstream's route would trade one hypothesis for a much larger one. CR₃'s
narrowest form `CertifiedRankTYZClRk` rests on a refereed theorem (TYZ, Asian J. Math. 2017, read in
arXiv v1), a short repair (Proposition N, two model reviews) and Gross–Zagier. Upstream's route
would replace that by an 8,300-line unrefereed 2-converse whose own audit is incomplete. It would
also mean returning to the template the fork replaced. (SPECULATIVE, an assessment.)

## 1. The analogs of N5 Theorems 5.2 and 5.3

### 1.1 Location (VERIFIED)

| Version | file | `sec:pole` | PC (`hyp:PC`) | RC (`hyp:RC`) | RC proof |
| --- | --- | --- | --- | --- | --- |
| N5 | `diophantine_zq.tex` | 973–1122 | 1001 | 1005 | 1760–5744, App. 6825–10935 |
| V13 | `manuscripts/quartic_v13.tex` | 1049–1207 | 1080 | 1090 | 1878–5930, App. 12236–16468 |
| V14 | `manuscripts/quartic_v14.tex` | 1681–1874 | 1712 | 1722 | 2546–6703, App. 13314–17518 |
| V15 | `research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex` | 1705–1898 | 1736 | 1746 | 2570–6727, App. 13339–17543 |
| V16 | `manuscripts/quartic_v16.tex` | 1705–1898 | 1736 | 1746 | 2570–6727, App. 13339–17543 |

The script `scratch/up-cr3/extract.sh` cuts out `sec:pole` (up to `\section{Multiplication`). The
pairwise diffs (log, step 1) show the following.

- **N5 → V13.** Only two additions. V13 1050–1051 says the construction adapts
  `[openaihtp, Section 3]`. V13 1084–1088 (V16 1740–1745) says RC is the `E = E_ℓ`, `s₂(E) = 1`
  case of `[openaipointwise, Thm 1.1]` and also follows from `[openaigoldfeld, Thm 1.1]`. These
  preprints are "cited for attribution, not assumed as additional converse inputs".
  V9 equals N5 here. V10, V11 and V12 equal V13 (empty diffs).
- **V13 → V14.** Proof details only.
  - Non-CM is now argued from Fowler's monic class polynomial instead of "nonintegral `j`" (V16
    1754–1756; the computation is at V16 2585–2601).
  - The Poonen–Stoll locators are made precise (V16 1826).
  - Modularity is cited as BCDT through Silverman C.13.6, and Kolyvagin's pages as 430–431
    (V16 1840–1847).
  - The modular quotient `J₁(N) → A` used for Kato's Corollary 14.3 is built explicitly (V16
    1848–1880).
- **V14 → V15.** One added sentence pointing to `v15:picard-norm` (V16 1871).
- **V15 → V16.** Identical in `sec:pole`.

### 1.2 Template, curves, converse and point production (VERIFIED, V16 1709–1898)

- **Template.** `Q_pole` has 11 witnesses. It requires points `(A, r₁) ∈ E_e` and
  `(Az², zr₂) ∈ E_{eH}` with `A = mB`, `H = A(A − B²)` and `m` a signed divisor of 2730
  (V16 1709–1721). Soundness is a one-sided valuation lemma with exceptional set
  `S₀ = {2,3,5,7,13}` (V16 1723–1734).
- **PC.** The hypotheses are unchanged from N5: square reduced denominator, `0 < B < 1/2`, and
  `v_p(B) ≥ 4` on `S₀` (V16 1736–1739).
- **RC** (V16 1746–1752). For squarefree `ℓ ≡ 11 (mod 12)`,
  `corank Sel_{2^∞}(E_ℓ) = 1 ⇒ ord_{s=1} L(E_ℓ, s) = 1`. Here `j = 35152/9`, so the curves are
  non-CM.
- **Descent** (V16 1761–1808). This is N5's S11–S12 Rédei-matrix construction, unchanged. It
  produces `n` and `nθ` with `dim Sel₂ = 3` and extra Kummer class `(β, 1)`.
- **Points** (V16 1887–1897). The corank lemma (V16 1815–1832) gives corank 1. RC then gives
  analytic rank 1. The forward lemma (Kolyvagin; V16 1834–1886) gives rank 1 and finite Ш, so
  `Ш[2] = 0`. Kummer exactness then gives rational points of abscissa class `β`, which are
  rescaled to the witnesses. **No explicit point is constructed.**

### 1.3 How RC is proved, and its status (VERIFIED)

- V16 2570–2576 says that the organization of RC's proof "follows" openaipointwise, namely its
  ring-class interpolation, determinant transfer, coefficient systems and fixed-curve assembly.
- The bibliography gives:
  - openaipointwise: "A pointwise 2-converse for elliptic curves with rational two-torsion",
    OpenAI preprint, 7 Oct 2026, Theorem 1.1 (V16 39551–39555);
  - openaigoldfeld: V16 39556–39560.
- Upstream's source register lists both as "Unpublished attribution source only"
  (`docs/manuscript-revisions/version10/sources.json` 52–64). Neither PDF is in either clone
  (`find -iname '*pointwise*'` is empty), so their statements could not be read here.
- RC concludes at V16 6720. Its inputs include:
  - Kato (Astérisque 295) Theorem 13.4(2), with Kato 1999 Theorem 0.8 at the prime 2 (V16
    2779–2784);
  - Nekovář's Selmer complexes, Waldspurger, Bump–Friedberg–Hoffstein, and Ribet 1990 (V16
    15102–15122);
  - Gross–Zagier and Kolyvagin.

  This is the same architecture as N5 (rs-pole §3.1).

### 1.4 Later pole modules in V16 (VERIFIED)

- **Seven-variable `Ψ(b)`** (V16 8793–8798). The equations are
  `p² = B(1−e)(1+3e)` and `Bq² = (s² − Bh)(s² + 3Bh)` with `B = 17b`: the same family
  `x(x−ℓ)(x+3ℓ)`, with exceptional set `{2,3,17}`. Its completeness, Lemma `hyp:o8-pole`
  (V16 8803–8815), is proved from RC and the corank lemma. V16 7622–7625 says this lemma is proved
  from RC and is not inferred from PC.
- **Lemma "Simultaneous realization from the existing restricted converse"** (V16 8870–8961; V13
  7787, V14 8846, V15 8870). It repeats the descent with more detail and ends with RC and the
  forward lemma.
- **Proposition "Linear-unit ordinary pole"** (V16 10671–10700; also in V13 9577). Soundness is
  by valuation parity. Completeness holds "under the same inherited realization and rank
  hypotheses" (V16 10680–10682), that is, from RC.

### 1.5 The 214-variable proposal (VERIFIED)

- `research/quartic214/PROOF.md` line 25 carries over from V15 the statements of "rank, RC, Kato
  full-index/limiting-class, GI, Gaussian prime, scalar and pole".
- `proofs/source-carry.md` C04 (lines 11–17) restates RC word for word for `E_ℓ`,
  `ℓ ≡ 11 (mod 12)`. It is applied to `n_pole` and `n_pole·θ` through the V15 descent (V15
  8870–8970), with points obtained after Ш is shown finite.
- `proofs/existence.md` 86 keeps the pole input's squareclasses at 2, 3 and 17.
- So the proposal has no new pole route.

### 1.6 Comparison with Route K and the barriers

Route K's two curves for the pole are the congruent number curves `x − ℓ` and `x + ℓ`, that is
`C_d : y² = x³ − d²x`, which have CM by `ℤ[i]` (slot-k.md, rs-pole §4.1). Upstream's
`E_ℓ = x(x−ℓ)(x+3ℓ)` are quadratic twists of the non-CM conductor-24 curve (rs-pole, notation).
The two families are disjoint.

The barriers apply in the same way to upstream's gadgets and to the fork's. The barrier results
are Theorem G (el-gadget §1–§2) and Lemma G (el-special §4), as repaired in rv-cr3-barrier.
- **Fibres.** In `Q_pole`, `Ψ` and the linear-unit module, the fibre over `B` is a conic in
  `(e, r₁)` with a genus-1 quartic over it. So the fibre is not rationally connected (VERIFIED from
  V16 1709–1721 and 8793–8798, as rv-cr3-barrier §1 found for the fork's `polePoly`).
- **Soundness.** Soundness is a valuation-parity argument that works equally for `ℚ_p`-points, so
  it is local and uniform (LUS) (V16 1723–1734 and 10685–10703).
- **Witnesses.** Completeness takes its witnesses from a rank theorem, never from an explicit
  family.

Upstream therefore never claims a rationally connected gadget, or explicit witnesses with LUS
soundness. There is no statement for the barriers to contradict. (VERIFIED by the reading above.)

Upstream also leaves open what rv-cr3-barrier leaves open: whether some gadget whose soundness is
not LUS could avoid a rank input. Nothing in Versions 13–16 or the 214 proposal attempts this.
(VERIFIED, absence after grep; any such route is SPECULATIVE.)

## 2. The fork's fixes, one by one

| Fork fix (fork source) | V13–V16 | Locus |
| --- | --- | --- |
| Route K's template `x ∓ ℓ`, congruent number curves `C_d` (slot-k.md; rs-pole §4.1) | **None.** Keeps `x + 3ℓ`, non-CM `E_ℓ`. | V16 1712–1721, 1747–1756; also `Ψ` V16 8793–8798 |
| CR₃ (positive rank for `C_d`) as the hypothesis in place of PC (KERNEL_PLAN; cr3-trust §0) | **Different.** PC is a theorem, derived from RC, which the manuscript proves itself (8,300 lines). No hypothesis is isolated. | V16 1736–1758, 2570–6720 |
| Proposition 0: the explicit system is `Sel₂(C_d)`, with local analysis at 2 (nt-prop0; descent-alt §4.1; Lean-proved per cr3-trust E1) | **Partial analog, unproved.** A prose description of the local images of `E_ℓ` at odd good primes, at `p ∣ ℓ`, at 3, at 2 and at ∞. Only the 2-adic part has a sketch. | V16 1793–1808; fuller at V16 8925–8961 (V13 7845, V14 8904, V15 8928) |
| TYZ Theorem 1.2 false as printed, completed by Proposition N (nt-tyz §1.4, §4) | **Not applicable.** TYZ is never cited. | grep `Tian`, `Yuan` in V13–V16 finds only `Yuan2024`, a different paper (V16 7743) |
| Kriz not needed (nt-tyz §5.1; cr3-trust D4) | **Not applicable.** Kriz is never cited. Its role (a 2-converse) is played by the in-manuscript RC. | V16 2570–2576 |
| Gross–Zagier plus an auxiliary field instead of Kolyvagin, for rank ≥ 1 (cr3-trust D1–D3; rs-pole §2.3 "Kolyvagin is not needed after RC") | **None.** Uses Kolyvagin's Theorem 1, with Theorems 3–5 for the auxiliary field and Heegner height, to get rank 1 and finite Ш, although `dim Sel₂ = 3` and rank ≥ 1 already give `Ш[2] = 0`. Modularity comes from BCDT through Silverman C.13.6, not from the conductor-24 twist observation of rs-pole §2.3. | V16 1834–1886 (V13 1171–1195) |

Notes on the table.
- **The 2-adic claim, checked.** Upstream's analog of Proposition 0 says that at 2 every point of
  `E_ℓ` gives even valuations to both coordinates (V16 8931–8936). This was checked on 30
  squarefree `ℓ ≡ 11 (mod 12)` from 11 to 371, with 11,833 `ℚ₂`-points `x = a·2^k`
  (`a` odd, `|a| < 256`, `|k| ≤ 6`): there are no violations, and `j = 35152/9` in every case
  (VERIFIED, `scratch/up-cr3/local2.py`, `out_local2.txt`). This checks only the necessity half.
  The other half, that `(β, 1)` is locally soluble everywhere (V16 8955–8960), is asserted in
  prose. The fork's Proposition 0 for `C_d` is proved in Lean.
- **The forward lemma.** Upstream's later revisions on the pole side are locator and
  proof-detail repairs to this lemma (V13→V14, §1.1). The mathematics is unchanged.

## 3. Version 16's stated limits about Kato 1999 and Ribet 1990

### 3.1 The limits (VERIFIED)

- `research/version16/README.md` 19: the fourth Fable 5.2 audit "leaves Kato 1999 and Ribet 1990
  unread". The same line says it also left the modified-modulus Tao–Ziegler proof outside its
  scope, and that the release is not a new whole-proof audit.
- `research/version16/FINDINGS.json` 33: Kato 1999 pages 314–318 and Ribet 1990 pages 440–443 were
  "unread by Fable".
- `protocol/CURRENT-CORRECTIONS.md` 23: the uninspected Kato and Ribet pages "remain an explicit
  limitation" of that audit.
- `review/current/REVIEW.md` 55 repeats this. It adds that an earlier "four-contract review"
  checked the enlarged-index Kato interface, without claiming all the local-control results.
- `README.md` 21 refers to earlier independent Kato and Ribet reviews. Their content was not
  examined here.

### 3.2 What the two results are used for (VERIFIED)

Both are inputs to RC only. Neither is used in PC's descent, in the corank lemma or in the forward
lemma.

- **Kato 1999** (K. Kato, *Euler systems, Iwasawa theory, and Selmer groups*, Kodai Math. J. 22
  (1999) 313–372; V16 bibliography 39545–39550).
  - It justifies applying Kato (Astérisque 295) Theorem 13.4(2), the Euler-system divisibility,
    **at p = 2** (V16 2779–2784).
  - In Appendix `app:even-source` (V16 13780–13870) it is used in three ways:
    - Example 0.6.2 and Serre's open-image theorem put an open subgroup of `SL₂(ℤ₂)` in the
      image of `G_{ℚ^ab}`. This supplies the unipotent required by condition 0.6(ii).
    - The index set of §0.1 is matched with the enlarged classes (K8).
    - The Euler factors of (0.1.1) are matched with the norm relations.
  - This is the even-coefficient bound in RC.
- **Ribet 1990** (K. Ribet, Invent. Math. 100 (1990) 431–476, Proposition 3.3, Remarks 3.5(a)–(b)
  and Proposition 3.6; V16 39489–39493).
  - It is used in Appendix `app:odd-source`, in the paragraph "The finite-field evaluation map"
    (V16 15078–15122).
  - There it describes enhanced supersingular curves through an Eichler order of level `N` in
    the quaternion algebra ramified at `ℓ₀` and ∞. Frobenius acts on the supersingular set as an
    involution, so those coarse points lie in `X₀(N)(𝔽_{ℓ₀²})`.
  - This is part of RC's odd-theta-form argument.

### 3.3 Consequence for the fork (SPECULATIVE)

The fork's route uses neither source:
- RC is deleted by Route K;
- CR₃ rests on TYZ, Proposition N and Gross–Zagier (cr3-trust §1).

So Version 16's open audit items on this side do not affect the fork. They make upstream's route
weaker, not stronger, as a replacement for CR₃.

## 4. Could an upstream ingredient still narrow CR₃? (SPECULATIVE)

- **openaipointwise Theorem 1.1, if it covers CM curves.** V16 1740 describes RC as its
  `E = E_ℓ`, `s₂(E) = 1` case, so the theorem concerns curves with rational two-torsion. If it
  also covers the CM curves `C_d`, then three steps would give `dim Sel₂(C_d) = 3 ⇒ rank ≥ 1` for
  every squarefree `d`, with no Tian–Yuan–Zhang genus condition:
  1. the corank lemma (V16 1815–1832);
  2. Theorem 1.1 itself;
  3. Gross–Zagier with an auxiliary field (cr3-trust D2–D3).

  That would discharge all the `#Sel₂ = 8` forms of CR₃. But it would replace a refereed theorem
  by an unrefereed preprint that nobody here could read. Upstream does not even assume that
  preprint: it re-proves only the non-CM `E_ℓ` case. For the CM family, Kriz's 2-converse
  (arXiv:2002.04767, Theorem 10.13, unrefereed) is already the known alternative, and the fork
  does not need it (nt-tyz §5.1). It is not known here whether the preprint covers CM curves.
  This is not a cheaper published input.
- **Transferring upstream's in-manuscript RC proof to the congruent-number family.** That RC
  proof is specific to non-CM curves: it uses Serre's open image (V16 13787) and the non-CM
  check (V16 2577–2601). Adapting it to `C_d`, which has CM, would be new work of the same size.
  This is not a narrowing.
- **No cheaper published input appears.** No version cites any published result that would
  replace Tian–Yuan–Zhang with Proposition N and Gross–Zagier. Every published input upstream uses
  on this side feeds RC: BCDT, Kolyvagin, Kato 2004 and 1999, Nekovář, Waldspurger,
  Bump–Friedberg–Hoffstein, Ribet 1990, Gross–Zagier and Poonen–Stoll.

## 5. Next step

Nothing in upstream calls for a change to CR₃, `CertifiedRankTYZClRk` or Route K. The one open
upstream item that could bear on CR₃ is the statement of openaipointwise Theorem 1.1: its exact
hypotheses on `E`, in particular whether CM curves are covered, and how `s₂` is defined. If a
later task can read that PDF (upstream pins revision `4eaee875…`), record the statement in
cr3-map-literature.md as an unrefereed alternative next to Kriz. It would not replace TYZ.

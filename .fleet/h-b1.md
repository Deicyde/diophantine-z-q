# h-b1: route B1 (integral model → tame specialization), audit record

Deliverable: `docs/research/h-b1.md`; scripts: `scratch/h-b1/b1_checks.py` (+ output); log:
`scratch/h-b1/log.md`.

**Result.** Lemma PR of h-map §3.2 is proved without any integral model of `Y₃`:
(i) for `p ∉ S` (indeed every `p ≥ 17`) the fibre field `K` is unramified at `p` unless some
`v_p(u−c)` is positive and odd; (ii) the fibre surface `A` has good reduction at every `v ∤ 3`.
Every use of b11 in N5 (L441-534, L529-530, L563-566, L847-850) has an exact replacement
(table §5); L814 (`v | 3`) never used b11 (Raynaud's criterion only).

**Key finding.** Beckmann's theorem alone does *not* do it: "p ∤ |G| and étale branch locus ⇒
no vertical ramification" is false in general (`y² = p·j(27j+16)`, fibre `ℚ(√43p)`,
VERIFIED). The missing hypothesis is supplied by a new half-page argument, **Lemma NV**: the
fibres over the branch points are CM points with maximal orders (VERIFIED), hence unramified at
`p ≥ 5` by Shimura reciprocity; Abhyankar's lemma puts the vertical inertia inside the inertia
at `∞` and at `−16/27`, whose images in the Atkin–Lehner group `(ℤ/2)²` differ; so it is trivial.
Specialization (Prop. TS) is then proved directly from SGA 1 (purity + Abhyankar); potentially
good reduction from SGA 7 (Morita's argument); good reduction from the rational level-3
structure + Serre–Tate.

**Computations (VERIFIED).** `|Γ'| = 144 = 2⁴3²` (refines h-map's 4·72), so tameness holds for
all `p ≥ 5`; J-identities and prime supports; 30/30 sampled specializations match the
`M_S(u)` parity rule.

**Remains.** Lemma NV / Prop. TS are unreviewed (one review, focus §3 step 3); all published
locators (Beckmann, SGA 1/7, Serre–Tate, Deligne, Shimura, Kottwitz, Vignéras, Morita) are
UNVERIFIED (no network); the identification of N5's `Y₃ = Sh_{K₃}` with the moduli problem
over ℚ should be checked. W1, W3, W4 untouched.

**Verdict.** B1 (amended by Lemma NV) removes `b11`, Buzzard 1997 (A002) and the stable-model /
tame-quotient theory (A078) from H's justification. Rating: high that Lemma PR holds as proved;
medium-high that the record survives review unchanged.

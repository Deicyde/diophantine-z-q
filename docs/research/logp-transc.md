# logp-transc: transcendence of `log [p̃]` (Brinon-Conrad Thm 9.2.10) and the image of `A_cris` — scoped stop

Task logp-transc, 2026-11-17. Base: fork main 5500325f with `origin/wip/htmult-model` (36bbcafa, containing
`wip/pb-dimform` 3d69c488) merged; nothing else merged. Results log: `scratch/logp-transc/log.md`. Model work; no person
has reviewed it.

Marks: **VERIFIED** (compiled here, or read in a source available here), **STANDARD** (published, exact reference),
**UNVERIFIED** (from memory; no network, no Brinon-Conrad or Fontaine print on this host), **SPECULATIVE**,
**on-the-spot** (provenance (c): a step in neither the manuscript nor a source it cites; never LEAF).

## 1. Verdict

**Scoped stop on both co-steps, with the finishable parts proved.** Neither `BergerBst.LogPTildeTranscendental` nor the
image-of-`A_cris` statement is proved. Both need theories that are missing and large (§4, §5), and the stop rule applies:
nothing was built in their place and no leaf was added.

What is proved (VERIFIED: compiled with `lake env lean`, no `sorry`, axioms `[propext, Classical.choice, Quot.sound]`,
new file `ZInQKernel/Contrib/OneProof/LogPTranscendence.lean`, scratch copy `scratch/logp-transc/LogPTranscendence.lean`):

1. **`B_cris ⊆ B_max`** in `B_dR`, for every `w ∈ ker θ` used to write `A_cris` (`bcrisOf_le_bmax`), with
   `B_cris^+ ⊆ B_max^+` and `BstFOf ⊆ Bst`. The tree had `A_cris ⊆ A_max` only for generators `w` of `ker θ`.
2. **The Galois half of the transcendence, in Lean.** For any `G_{ℚ_p}`-stable `ℚ_p`-subalgebra `B ⊆ B_dR` and any `u`
   with `σ(u) − u ∈ B`, `u` is transcendental over `B` as soon as `u ∉ Frac(B) + B_dR^{G_{ℚ_p}}`
   (`transcendental_of_logCore`). Conversely the transcendence gives that condition when `B_dR^{G_{ℚ_p}} ⊆ B`
   (`logCore_of_transcendental`). So the condition `LogCore` is exactly what remains.
3. Applied to `u = log [p̃]`:
   * `logPTildeTranscendental_of_core`: `LogCore (B_max) (log [p̃])` for every `p` implies
     `BergerBst.LogPTildeTranscendental`;
   * `transcendental_bcris_of_core`: the weaker `LogCore (B_cris) (log [p̃])` implies the transcendence over `B_cris`;
   * `logCore_of_notInFrac`: given `B_dR^{G_{ℚ_p}} = ℚ_p` in element form (proved in the tree in dimension form,
     `BdRInv.bdRInvariantsPrinted_proof`), the core is the sharp statement `log [p̃] ∉ Frac(B)`.
4. **Transfer to Brinon-Conrad's form.** `LogPTildeTranscendental` gives the injectivity of `B_cris[X] → B_dR`,
   `X ↦ log [p̃]` (`transcendental_bcrisOf`, Thm 9.2.10 at `K = ℚ_p`), for every `w`, and the identification
   `BstFOf ≅ B_cris[X]` of Brinon-Conrad's abstract `B_st` (Def. 9.2.3) with its image (`bcrisPolyEquiv`,
   `bstFOf_eq_adjoin`).

**The one missing statement for co-step (i)** is the degree-one case `log [p̃] ∉ Frac(B_max)` (or the weaker
`log [p̃] ∉ Frac(B_cris)`). Every proof known here uses the Frobenius `φ` of `B_max` (or `B_cris`), which the tree does
not have and cannot get cheaply, because the tree's `A_max` is a subring of `B_dR^+` and `φ` does not act on `B_dR^+`
(§4).

**Co-step (ii)** needs Brinon-Conrad's abstract `A_cris` (the `p`-adic completion of the divided-power envelope of
`A_inf` along `ker θ`). Mathlib v4.35 has divided-power structures but no divided-power envelope (VERIFIED, §5). §5
states the smallest faithful statement.

**Ratings.** No re-rating follows: `panPrintedF` and `bergerSurveyF` still depend on co-steps (i) and (ii) as before.
What changed is the size of co-step (i): it is now the single Prop `LogCore (B_max) (log [p̃])` (or its `B_cris`
form), with everything between it and Thm 9.2.10's injectivity proved.

This was a proof-only task: no bundle field, statement or kinds row changed, nothing was folded. The only file added
under `ZInQKernel/` is `ZInQKernel/Contrib/OneProof/LogPTranscendence.lean`. It imports
`ZInQKernel.Contrib.OneProof.PanBergerFontaine`, does not import `ZInQKernel.OneProof.Main`, and nothing imports it.

## 2. The new theorems (namespace `HDec.PkgI4.LogPTransc`)

PLACEHOLDER

## 3. Which properties of `B_max` / `B_cris` the proofs use

The Galois reduction (`transcendental_of_logCore`) uses only these properties, all already in the tree:

| property | where in the tree |
|---|---|
| `B_dR` is a field of characteristic 0 (a `ℚ_p`-algebra) | `ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham` |
| `σ ↦ bdrAct p σ` acts on `B_dR` by ring maps (so injectively) | `bdrAct` (`ZInQKernel/Contrib/G9/I4Layer.lean`) |
| `B_max` is `G_{ℚ_p}`-stable | `BergerBst.bmax_stable` |
| `B_cris` (at `ξ`) is `G_{ℚ_p}`-stable | new `bcris_gStable`, from `FontaineSt.bdrAct_acris`, `tInv_mem_of`, `tInvSet_stable` |
| `σ(log [p̃]) = log [p̃] + log [u_σ]`, `u_σ = σ(p̃)/p̃`, `u_σ^♯ = 1` | `BergerBst.bdrAct_logPTilde`, `exists_uSigma` |
| `log [ε] ∈ A_max` and `∈ A_cris` for `ε^♯ = 1` | `BergerBst.logTeich_mem_amax`, `FontaineSt.logTeich_mem_acris` |
| `A_cris ⊆ A_max` | `FontaineSt.acrisOf_le_amax` (generators), new `acrisOf_le_amax_any` (any `w ∈ ker θ`) |
| `1/t ∈ B_max` | `BmaxOne.bmaxOf_eq` |

Note that `log [u_σ] = c(σ)·t` with `c` the Kummer cocycle of `p` is not needed in this form: the proof only uses
`σ(u) − u ∈ B`. The sharp form `logCore_of_notInFrac` adds `B_dR^{G_{ℚ_p}} = ℚ_p` (element form), proved in the tree
in dimension form (`BdRInv.bdRInvariantsPrinted_proof`, `ZInQKernel/Contrib/OneProof/BdRInvariants.lean`); the step
from dimension form to element form and the import were not done (the import pulls `ZInQKernel.OneProof.H.TailS`).

The core `LogCore` would need properties the tree does not have (§4): the Frobenius `φ` of `B_max`, and an arithmetic
input that separates the Kummer class of `p` from those of units.

## 4. Co-step (i): what is missing for `log [p̃] ∉ Frac(B_max)`

### 4.1 What Brinon-Conrad do, and what this task could check

The reading desk's locators (`scratch/pb-dimform/bc-reading.md`, VERIFIED as a reading): `B_st` is defined abstractly
as `B_cris[X]` (Def. 9.2.3 p. 138), embedded in `B_dR` on p. 142 by `X ↦ log [q]`, and Thm 9.2.10 p. 143 states that
`K ⊗_{K_0} B_st → B_dR` is injective. The reading desk notes that BC only sketch this proof. This host has no copy
of BC, so the sketch itself could not be read; the argument below is the standard one (UNVERIFIED that BC's sketch has
exactly these steps).

It has two halves:

1. **Galois half (proved here in Lean).** If `log [p̃]` is algebraic over `B`, the minimal-degree relation and the
   Galois action `σ(log [p̃]) = log [p̃] + c(σ) t` force `log [p̃] ∈ Frac(B) + B_dR^{G}` (§2, `transcendental_of_logCore`).
   With `B_dR^{G_{ℚ_p}} = ℚ_p` (in the tree) this is `log [p̃] ∈ Frac(B)`.
2. **Arithmetic half (missing).** `log [p̃] ∉ Frac(B)`, for `B = B_max` or `B_cris`.

### 4.2 Why the Galois action alone cannot give the arithmetic half (on-the-spot, standard)

For a unit `v ∈ ℤ_p^×`, take `ṽ = (v, v^{1/p}, …) ∈ 𝓞_ℂ_p^♭`. Then `[ṽ]/v − 1 ∈ ker θ ⊆ ξ A_inf[1/p]`, and the same
estimate as `logTeich_mem_amax` (`([ṽ]/v − 1)^n/n = (p^n/n) c^n (ξ/p)^n` with `p^n/n ∈ ℤ_p → 0`) puts
`log([ṽ]/v)` in `A_max`. It satisfies `σ(log([ṽ]/v)) = log([ṽ]/v) + c_v(σ) t` with `c_v` the Kummer cocycle of `v`.
So the element `log [p̃]` and the elements `log([ṽ]/v) ∈ B_max` have the same kind of Galois behaviour. Any proof of
`log [p̃] ∉ Frac(B_max)` must use that `p` is not a unit: through the Frobenius `φ` (`φ(log [p̃]) = p·log [p̃]`
versus `φ(log([ṽ]/v)) = p·log([ṽ]/v) + (p − 1) log_p v`) or through the analytic structure of `B_max`. (This
paragraph is a proof sketch, not compiled.)

### 4.3 What a proof needs (SPECULATIVE as to the shortest route; the ingredients are STANDARD)

The route through the Frobenius (Fontaine; Colmez for `B_max`; exact references UNVERIFIED):

(a) **An abstract `A_max` and its injection into `B_dR^+`.** The tree's `A_max` is defined as a subring of `B_dR^+`
    (`BergerBst.Amax`: evaluations of restricted series). `φ` does not preserve `ker θ` and does not act on `B_dR^+`,
    so `φ` on `A_max` must be defined on the abstract ring (the `p`-adic completion of `A_inf[ξ/p]`) and transported,
    which needs the injectivity of the abstract ring into `B_dR^+`. This is the `A_max` analogue of co-step (ii).
    Size: comparable to §5 (several hundred to a few thousand lines; SPECULATIVE estimate).

(b) **`φ` on `B_max`**: an injective ring endomorphism commuting with `G_{ℚ_p}`, with `φ(t) = p t`, and its extension to
    `Frac(B_max)`. Moderate once (a) is there.

(c) **`φ(β) − pβ` is invariant**, for `β := log [p̃] − y ∈ Frac(B_max)` (`y ∈ ℚ_p`), so it lies in
    `B_dR^{G} = ℚ_p` (in the tree), and after a shift by `ℚ_p`, `φ(β) = pβ` and `σ(β) − β = c(σ) t`.

(d) **An arithmetic separation of `p` from the units.** One standard way: the fundamental exact sequence
    `0 → ℚ_p t → (B_max^+)^{φ = p} → ℂ_p → 0` (via `θ`) and the elements `log([ṽ]/v) + log_p v` of
    `(B_max^+)^{φ = p}` show that a solution `β` would make `c` a `ℚ_p`-multiple of a unit's Kummer cocycle plus a
    coboundary; restricted to `G_{ℚ_p(μ_{p^∞})}` this contradicts Kummer theory (the Kummer classes of `p` and of a unit
    are `ℚ_p`-independent). It also needs a step from `Frac(B_max)` to `B_max` (the `G`-regularity of `B_max`, or a
    direct argument). Each of these is a substantial piece of `p`-adic Hodge theory (the fundamental exact sequence
    alone is a well-known hard theorem); together they are a large missing theory in the sense of the stop rule.

The other standard route (through crystalline representations: if `log [p̃] ∈ B_cris` the Kummer extension of `ℚ_p`
by `ℚ_p(1)` attached to `p` is crystalline; contradiction with `dim H^1_f(ℚ_p(1)) = 1`, which the units already
fill) needs `D_cris`, the `G`-regularity of `B_cris`, `B_cris^{G} = ℚ_p` and the Bloch-Kato dimension formula, which
is larger.

### 4.4 What follows if the core were present

`LogCore (B_max) (log [p̃])` for every `p` gives, by compiled proofs: `BergerBst.LogPTildeTranscendental`
(`logPTildeTranscendental_of_core`), hence `B_st ≅ B_max[X]` (`BergerBst.bstEquivPolynomial`), the injectivity of
`B_cris[X] → B_dR` for every `w ∈ ker θ` (`transcendental_bcrisOf`) and `BstFOf ≅ B_cris[X]` (`bcrisPolyEquiv`), i.e.
co-step (i). The weaker `LogCore (B_cris) (log [p̃])` gives the `B_cris` statements directly
(`transcendental_bcris_of_core`).

## 5. Co-step (ii): `A_cris`

### 5.1 What is missing

* Brinon-Conrad's `A_cris` (p. 128, per the lead's statement of the co-step and the reading desk) is the `p`-adic
  completion of the divided-power envelope `D_{ker θ}(A_inf)` (compatible with the canonical divided powers on
  `pℤ_p`), with a map `j : A_cris → B_dR^+` whose injectivity BC omit; p. 129 describes the image as the
  `Σ a_n ξ^n/n!`, `a_n → 0` `p`-adically. The tree's `FontaineSt.AcrisOf` is that description.
* VERIFIED (search of `.lake/packages/mathlib/Mathlib/RingTheory/DividedPowers/`): Mathlib v4.35 has
  `Basic.lean`, `DPMorphism.lean`, `Padic.lean` (the divided powers `x^n/n!` on `pℤ_p`), `RatAlgebra.lean`,
  `SubDPIdeal.lean`, and no divided-power envelope (no file of the directory mentions an envelope). The tree has none
  either (VERIFIED by search of `ZInQKernel/`).
* So the tree cannot express BC's abstract `A_cris`, and by the stop rule no substitute was built.

### 5.2 Smallest faithful statement (not compiled; not a leaf; for the record)

With `A = A_inf = W(𝓞_ℂ_p^♭)`, `I = ker θ = (ξ)`:

1. `D := D_{I}(A)` with its universal property: `D` is an `A`-algebra with a divided-power ideal `(Ī, γ)` compatible
   with `(pℤ_p, x^n/n!)`, `I·D ⊆ Ī`, initial among such (Mathlib's `DividedPowers` and `DPMorphism` give the
   language; the existence of `D` is the missing theorem).
2. `A_cris := AdicCompletion (Ideal.span {p}) D`.
3. `j : A_cris →+* B_dR^+` the unique ring map that is compatible with `A → B_dR^+` and continuous from the `p`-adic
   topology to the topology on `B_dR^+/Fil^m` given by the lattice image of `D` (each `B_dR^+/Fil^m = A[1/p]/ξ^m`).
4. **Statement:** `Set.range j = AcrisOf p ξ (theta_xi' p)` and `Function.Injective j`.

The inclusion `range j ⊆ AcrisOf` and its converse are a regrouping of `p`-adically convergent sums of finite sums
`Σ a_n ξ^n/n!` (moderate). The injectivity is the hard part: the known proofs compute `D/p` (a divided-power polynomial
algebra over `𝓞_ℂ_p^♭/(p̃^p)`) and show `ker j ⊆ p·A_cris`, whence `ker j = 0` by `p`-adic separatedness (UNVERIFIED
as to BC's or Fontaine's exact route).

A smaller statement is available if one accepts BC's concrete description of the envelope (the reading desk reads
p. 128 as "generated by divided powers of any generator of `ker θ`"): `D = A[ξ^n/n! : n ≥ 1] ⊆ A[1/p]`. Then items 1-3
are expressible in the tree today (a subalgebra of `AinfP`, Mathlib's `AdicCompletion`), and only the identification
with the envelope (a theorem about divided-power envelopes of a regular element, UNVERIFIED as to where BC prove or
cite it) is outside. This task did not build it, because the lead's instruction was not to build a substitute for the
envelope.

### 5.3 What would follow

With item 4, `AcrisOf` is BC's `A_cris` at definition level, so `BcrisOf` and `BstFOf` (built from `AcrisOf`) are
BC's `B_cris` and, with co-step (i), BC's `B_st`; the reviewer's co-step (ii) on both rows would be closed.

## 6. Known issues

PLACEHOLDER

## 7. Manuscript check

PLACEHOLDER

## 8. Checks and deliverables

PLACEHOLDER

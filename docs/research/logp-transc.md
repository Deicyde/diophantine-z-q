# logp-transc: transcendence of `log [p̃]` (Brinon-Conrad Thm 9.2.10) and the image of `A_cris` — scoped stop

Task logp-transc, 2026-11-17. Base: fork main 5500325f with `origin/wip/htmult-model` (36bbcafa, containing
`wip/pb-dimform` 3d69c488) merged; nothing else merged. Results log: `scratch/logp-transc/log.md`. Model work; no person
has reviewed it.

Marks: **VERIFIED** (compiled here, or read in a source available here), **STANDARD** (published, exact reference),
**UNVERIFIED** (from memory; no network, no Brinon-Conrad or Fontaine print on this host), **SPECULATIVE**,
**on-the-spot** (provenance (c): a step in neither the manuscript nor a source it cites; never LEAF).

## 1. Verdict

**Scoped stop on both co-steps. Everything around the two missing theories is proved.** Neither
`BergerBst.LogPTildeTranscendental` nor the image-of-`A_cris` statement is proved. Each needs a theory that is
missing and large (§4, §5), so the stop rule applies: nothing was built in their place and no leaf was added.

**Main result** (VERIFIED: compiled with `lake env lean`, no `sorry`, axioms `[propext, Classical.choice, Quot.sound]`):

```lean
theorem logPTildeTranscendental_iff_notInFrac :
    LogPTildeTranscendental ↔
      ∀ (p : ℕ) [Fact p.Prime], NotInFrac p (Bmax p) (toBdR p (logPTilde p))
```

Here `NotInFrac p B u` says there are no `a ≠ 0` and `b` in `B` with `a · u = b`, i.e. `u ∉ Frac(B)`. So Fontaine's
transcendence of `log [p̃]` over `B_max` is equivalent to its degree-one case, `log [p̃] ∉ Frac(B_max)`. The proof
is the Galois half of the standard argument (the minimal-polynomial argument with
`σ(log [p̃]) = log [p̃] + log [u_σ]`), together with the tree's `B_dR^{G_{ℚ_p}} = ℚ_p`.

The other proved results:

1. **`B_cris ⊆ B_max`** in `B_dR`, for every `w ∈ ker θ` used to write `A_cris` (`bcrisOf_le_bmax`). Also
   `B_cris^+ ⊆ B_max^+` and `BstFOf ⊆ Bst`. The tree had `A_cris ⊆ A_max` only for generators `w` of `ker θ`.
2. **Brinon-Conrad Thm 9.2.10 at `K = ℚ_p`, given the transcendence.** `LogPTildeTranscendental` gives:
   * the injectivity of `B_cris[X] → B_dR`, `X ↦ log [p̃]`, for every `w` (`transcendental_bcrisOf`);
   * `BstFOf ≅ B_cris[X]` (`bcrisPolyEquiv`, `bstFOf_eq_adjoin`). This identifies BC's abstract `B_st`
     (Def. 9.2.3) with its image in `B_dR`.
3. **The same reduction over `B_cris`.** The weaker `log [p̃] ∉ Frac(B_cris)` already gives the transcendence over
   `B_cris` (`transcendental_bcris_of_notInFrac`).
4. **The reduction works for any ring.** For any `G_{ℚ_p}`-stable `ℚ_p`-subalgebra `B ⊆ B_dR` and any `u` with
   `σ(u) − u ∈ B`, `u` is transcendental over `B` as soon as `u ∉ Frac(B) + B_dR^{G_{ℚ_p}}`
   (`transcendental_of_logCore`). This step does not use `B_dR^{G} = ℚ_p`.

**The one missing statement for co-step (i)** is `log [p̃] ∉ Frac(B_max)` (or `∉ Frac(B_cris)`).

* The Galois action alone cannot give it. For units `v`, the elements `log([ṽ]/v)` lie in `B_max` and have the same
  kind of Galois behaviour (§4.2).
* Every proof known here uses the Frobenius `φ` of `B_max`, and also an arithmetic input that separates `p` from the
  units (§4.3).
* The tree has no `φ` on `B_max`, and cannot get one cheaply. Its `A_max` is a subring of `B_dR^+`, and `φ` does not
  act on `B_dR^+`.

**Co-step (ii)** needs BC's abstract `A_cris`, the `p`-adic completion of the divided-power envelope of `A_inf` along
`ker θ`. Mathlib v4.35 has divided-power structures but no divided-power envelope (VERIFIED). §5 gives the smallest
faithful statement and what is needed for it.

**Ratings.** Nothing is re-rated: `panPrintedF` and `bergerSurveyF` still depend on co-steps (i) and (ii). Co-step (i)
is now one Prop, `∀ p, log [p̃] ∉ Frac(B_max)`. Everything between that Prop and the identification of BC's `B_st`
with `BstFOf` is proved.

**Manuscript.** No error was found. §7 has the line-by-line check.

This was a proof-only task. No bundle field, statement or kinds row changed, and nothing was folded. Two files were
added under `ZInQKernel/`, and nothing imports them:

* `ZInQKernel/Contrib/OneProof/LogPTranscendence.lean`, which imports `ZInQKernel.Contrib.OneProof.PanBergerFontaine`;
* `ZInQKernel/Contrib/OneProof/LogPTranscendenceBdR.lean`, which imports that file and
  `ZInQKernel.Contrib.OneProof.BdRInvariants`.

Neither imports `ZInQKernel.OneProof.Main`. Their scratch copies are in `scratch/logp-transc/`.

## 2. The new theorems (namespace `HDec.PkgI4.LogPTransc`)

Notation: `u = toBdR p (logPTilde p)` is `log [p̃] = log([p̃]/p) ∈ B_dR^+ ⊆ B_dR`, `p̃ = (p, p^{1/p}, …)`. `Bmax`, `Bst`
are bst-construct's (`BergerBst`); `AcrisOf`, `BcrisOf`, `BstFOf` are pb-p1's (`FontaineSt`), at an arbitrary
`w ∈ ker θ` unless `ξ` is written.

### 2.1 `B_cris ⊆ B_max` (`LogPTranscendence.lean` §1)

```lean
theorem acrisOf_le_amax_any {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    AcrisOf p w hw ⊆ (Amax p : Set (BDeRhamPlus 𝓞_ℂ_[p] p))
theorem bcrisPlusOf_le_bmaxPlus (hw) : BcrisPlusOf p w hw ≤ BmaxPlus p
theorem bcrisOf_le_bmax {ε₀} (h : IsGenEps p ε₀) (hw) : BcrisOf p h w hw ≤ Bmax p
theorem bstFOf_le_bst {ε₀} (h : IsGenEps p ε₀) (hw) : BstFOf p h w hw ≤ Bst p
```

Proof: `w = ξ c` (bdr-kertheta's `ker θ = (ξ)`), so `A_cris(w) ⊆ A_cris(ξ)` (`acrisOf_le`) `⊆ A_max`
(`acrisOf_le_amax`, i.e. `ω^n/n! = (p^n/n!) (ω/p)^n`, `p^n/n! ∈ ℤ_p`); `1/t` is in both (`bmaxOf_eq`, `bstOf_eq`).

### 2.2 The Galois reduction (`LogPTranscendence.lean` §2-§3)

```lean
def GStable (B : Subalgebra ℚ_[p] (BdR p)) : Prop := ∀ (σ : GQp p), ∀ x ∈ B, bdrAct p σ x ∈ B
def LogCore (B : Subalgebra ℚ_[p] (BdR p)) (u : BdR p) : Prop :=
  ∀ a b : B, a ≠ 0 → ∀ y : BdR p, (∀ σ : GQp p, bdrAct p σ y = y) → (a : BdR p) * (u - y) ≠ b
def NotInFrac (B : Subalgebra ℚ_[p] (BdR p)) (u : BdR p) : Prop :=
  ∀ a b : B, a ≠ 0 → (a : BdR p) * u ≠ b

theorem transcendental_of_logCore (B : Subalgebra ℚ_[p] (BdR p)) (hB : GStable p B) (u : BdR p)
    (hu : ∀ σ : GQp p, ∃ δ : B, bdrAct p σ u = u + δ) (hcore : LogCore p B u) :
    Transcendental B u
theorem logCore_of_transcendental (B : Subalgebra ℚ_[p] (BdR p)) (u : BdR p)
    (hinv : ∀ y : BdR p, (∀ σ : GQp p, bdrAct p σ y = y) → y ∈ B) (ht : Transcendental B u) :
    LogCore p B u
theorem logCore_of_notInFrac (B) (u)
    (hinv : ∀ y : BdR p, (∀ σ, bdrAct p σ y = y) → ∃ c : ℚ_[p], y = algebraMap ℚ_[p] (BdR p) c)
    (h : NotInFrac p B u) : LogCore p B u
theorem logCore_mono {B B'} (hBB' : B ≤ B') {u} (h : LogCore p B' u) : LogCore p B u
```

Proof of `transcendental_of_logCore` (on-the-spot write-up of the standard argument; BC's sketch at p. 143 not read
here):

1. Let `P ∈ B[X]` be nonzero of least degree `d` with `P(u) = 0` (`Nat.find`). Then `d ≥ 1`, because `B → B_dR` is
   injective.
2. For `σ`, with `σ(u) = u + δ` and `δ ∈ B`, set `P_σ := taylor δ (P^σ)`, i.e. `P_σ(X) = P^σ(X + δ)`. Then
   `P_σ(u) = σ(P(u)) = 0` (`aeval_map_sigB`), and `P_σ` has degree `d` with leading coefficient `σ(a_d)`.
3. `Q := σ(a_d)·P − a_d·P_σ` kills `u` and has degree `< d`, so `Q = 0` by minimality. Its `X^{d−1}` coefficient
   (`coeff_taylor_pred`: the `X^{d−1}` coefficient of `f(X + r)` is `f_{d−1} + d r f_d`) gives
   `σ(a_d) a_{d−1} = a_d (σ(a_{d−1}) + d δ σ(a_d))` (`top_coeff_relation`).
4. With `e = (d a_d)^{−1}` in the field `B_dR`, `y := u + a_{d−1} e` is `G_{ℚ_p}`-invariant, and
   `a_d (u − y) = −a_{d−1}/d ∈ B`. This contradicts `LogCore`.

### 2.3 `log [p̃]` (`LogPTranscendence.lean` §4-§5)

```lean
theorem bmax_gStable : GStable p (Bmax p)
theorem bcris_gStable {ε₀} (h : IsGenEps p ε₀) : GStable p (BcrisOf p h ξ (theta_xi' p))
theorem logPTilde_shift (B)
    (hB : ∀ (ε : PreTilt 𝓞_ℂ_[p] p) (h : PreTilt.untilt ε = 1), toBdR p (logTeich p h) ∈ B) (σ : GQp p) :
    ∃ δ : B, bdrAct p σ (toBdR p (logPTilde p)) = toBdR p (logPTilde p) + δ
theorem logPTildeTranscendental_of_core
    (hcore : ∀ (p : ℕ) [Fact p.Prime], LogCore p (Bmax p) (toBdR p (logPTilde p))) :
    LogPTildeTranscendental
theorem transcendental_bcris_of_core {ε₀} (h : IsGenEps p ε₀)
    (hcore : LogCore p (BcrisOf p h ξ (theta_xi' p)) (toBdR p (logPTilde p))) :
    Transcendental (BcrisOf p h ξ (theta_xi' p)) (toBdR p (logPTilde p))
theorem transcendental_of_le {B B'} (hBB' : B ≤ B') {u} (h : Transcendental B' u) : Transcendental B u
theorem transcendental_bcrisOf (ht : LogPTildeTranscendental) {ε₀} (h : IsGenEps p ε₀) {w}
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    Function.Injective (aeval (R := BcrisOf p h w hw) (toBdR p (logPTilde p)))
theorem bstFOf_eq_adjoin (h) (hw) :
    BstFOf p h w hw = (Algebra.adjoin (BcrisOf p h w hw) {toBdR p (logPTilde p)}).restrictScalars ℚ_[p]
def bcrisPolyEquiv (ht : LogPTildeTranscendental) (h) (hw) :
    Polynomial (BcrisOf p h w hw) ≃ₐ[BcrisOf p h w hw] Algebra.adjoin (BcrisOf p h w hw) {toBdR p (logPTilde p)}
theorem bcrisPolyEquiv_X (ht) (h) (hw) : (bcrisPolyEquiv p ht h hw X : BdR p) = toBdR p (logPTilde p)
```

### 2.4 With `B_dR^{G_{ℚ_p}} = ℚ_p` (`LogPTranscendenceBdR.lean`)

```lean
theorem bdr_invariant_eq_algebraMap (y : BdR p) (hy : ∀ σ : GQp p, bdrAct p σ y = y) :
    ∃ c : ℚ_[p], y = algebraMap ℚ_[p] (BdR p) c
theorem logCore_iff_notInFrac (B : Subalgebra ℚ_[p] (BdR p)) (u : BdR p) :
    LogCore p B u ↔ NotInFrac p B u
theorem logPTildeTranscendental_of_notInFrac
    (h : ∀ (p : ℕ) [Fact p.Prime], NotInFrac p (Bmax p) (toBdR p (logPTilde p))) : LogPTildeTranscendental
theorem logPTildeTranscendental_iff_notInFrac :
    LogPTildeTranscendental ↔ ∀ (p : ℕ) [Fact p.Prime], NotInFrac p (Bmax p) (toBdR p (logPTilde p))
theorem transcendental_bcris_of_notInFrac {ε₀} (h : IsGenEps p ε₀)
    (hc : NotInFrac p (BcrisOf p h ξ (theta_xi' p)) (toBdR p (logPTilde p))) :
    Transcendental (BcrisOf p h ξ (theta_xi' p)) (toBdR p (logPTilde p))
```

`bdr_invariant_eq_algebraMap` turns bdr-inv's `dim_{ℚ_p} B_dR^{G_F} = [F : ℚ_p]` at `F = ℚ_p` into the element form:
`B_dR^{G} ∋ 1` and has dimension 1 (`finrank_eq_one_iff_of_nonzero'`).

### 2.5 What this proves of the two co-steps

* **(i)** Proved: everything except the degree-one statement `log [p̃] ∉ Frac(B_max)`. That statement is equivalent
  to `LogPTildeTranscendental` and implies BC Thm 9.2.10's injectivity at `K = ℚ_p` and `BstFOf ≅ B_cris[X]`. Also
  proved: `B_cris ⊆ B_max`, which the lead's request asked for.
* **(ii)** Nothing new is proved. The abstract `A_cris` cannot be expressed in the tree (§5).

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

Note that `log [u_σ] = c(σ)·t`, with `c` the Kummer cocycle of `p`, is not needed in this form: the proof only uses
`σ(u) − u ∈ B`. The sharp form (`LogPTranscendenceBdR.lean`) adds `B_dR^{G_{ℚ_p}} = ℚ_p`. The tree proves that in
dimension form (`BdRInv.bdRInvariantsPrinted_proof`, `ZInQKernel/Contrib/OneProof/BdRInvariants.lean`), and
`bdr_invariant_eq_algebraMap` turns it into the element form. The import pulls in `ZInQKernel.OneProof.H.TailS` but
not `ZInQKernel.OneProof.Main`.

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
   With `B_dR^{G_{ℚ_p}} = ℚ_p` (in the tree; element form `bdr_invariant_eq_algebraMap`) this is `log [p̃] ∈ Frac(B)`.
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

The compiled proofs show that `∀ p, log [p̃] ∉ Frac(B_max)` gives:

* `BergerBst.LogPTildeTranscendental` (`logPTildeTranscendental_of_notInFrac`; the two are equivalent);
* `B_st ≅ B_max[X]` (`BergerBst.bstEquivPolynomial`);
* the injectivity of `B_cris[X] → B_dR` for every `w ∈ ker θ` (`transcendental_bcrisOf`);
* `BstFOf ≅ B_cris[X]` (`bcrisPolyEquiv`).

Together these are co-step (i). The weaker `log [p̃] ∉ Frac(B_cris)` gives the `B_cris` statements directly
(`transcendental_bcris_of_notInFrac`).

A faithful Lean statement of the missing Prop is the one in the main theorem, `NotInFrac p (Bmax p) (toBdR p
(logPTilde p))`. It is stated over genuine definitions: `Bmax ⊆ B_dR` and `log [p̃]` are concrete. With `BcrisOf` in
place of `Bmax`, it is the degree-one case of Fontaine's transcendence of `log [p̃]` over `Frac(B_cris)`. For `B_max`
it is the degree-one case of the `B_max` version (Colmez). Both locators are UNVERIFIED. As the lead instructed, it is
**not** added as a leaf.

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

(i) **Brinon-Conrad Thm 9.2.10, p. 143: the proof is a sketch** (reading desk, `scratch/pb-dimform/bc-reading.md`).
  * The Galois half is written out and compiled here (§2.2), as an on-the-spot fill.
  * Whether BC's sketch contains the arithmetic half (`log [p̃] ∉ Frac(B_cris)`), proves it, or cites Fontaine for
    it could not be checked: this host has no copy of BC (UNVERIFIED).
  * The reading desk notes that the full proof is in Fontaine, Astérisque 223, which the manuscript does not cite.
    The reading desk places it in §4.3. `BergerBst.LogPTildeTranscendental`'s docstring places it in Exp. II §3.
    Both locators are UNVERIFIED and may refer to different numbering schemes. The lead or the reading desk should
    fix one locator.

(ii) **BC p. 128: the injectivity of `j : A_cris → B_dR^+` is omitted** (the reviewer). The p. 129 sentence describes
  the image. `AcrisOf` is that description, and co-step (ii) stays open (§5).

(iii) **The core cannot come from the Galois action alone** (§4.2; a structural remark, sketched and not compiled).
  The units' `log([ṽ]/v)` lie in `A_max` and have the same shape of Galois action as `log [p̃]`. So any proof of the
  core must use `v_p(p) = 1` through `φ` or through the analytic structure of `B_max`. The cited sources state this
  step as a separate input, and it is the expensive part.

(iv) **Normalization `log(p) = 0`.** BC's embedding (p. 142) sends `X ↦ log [q] = log_dR([q]/q) + log_K(q)`, which is
  canonical once `log_K(p)` is fixed (p. 143). The tree uses `q = p`, `q̃ = p̃` and `log(p) = 0`, so `X ↦ log_dR([p̃]/p)`
  (`BstFOf`'s docstring). Another choice of `log_K(p) ∈ ℚ_p` shifts `X` by a constant, and transcendence is invariant
  under such shifts. No issue.

(v) **The manuscript cites BC at other locators.** The bibitem (L11019-11022) lists only Thm 5.2.1 and Props 6.3.3
  and 6.3.8, which are cited at L10975 and L10994 for de Rham closure and descent. The definitions of `A_cris`,
  `B_cris` and `B_st` (pp. 128-143) are in the same cited notes but at locators the manuscript does not name. This
  places them in provenance (b) (inside a cited source), not (a).

(vi) **Lean (no source issue):** `IsField.toField` on `B_dR` does not give instances that agree reducibly with
  `B_dR`'s ring operations: `NoZeroDivisors` and `IsSimpleRing` synthesis fails. The proofs use `IsDomain` and
  explicit inverses instead. Subtraction in `(↥B)[X]`, for a `Subalgebra B`, times out in instance search, so the
  proofs write `P + C (−c)`. Recorded in `scratch/logp-transc/log.md`.

No error was found in the manuscript or in the sources' statements used here.


## 7. Manuscript check

One line per step of `diophantine_zq.tex` that this work formalizes or relies on.

* **L738-741** (Berger's `p`-adic monodromy theorem makes the de Rham representation potentially semistable, as
  Pan's theorem requires): **unverified.** The text is right as written (Berger 2002, cited). Its implicit definition
  of "potentially semistable" is Fontaine's, over `B_st ⊆ B_dR`. Identifying BC's abstract `B_st` (Def. 9.2.3) with
  the tree's `BstFOf` needs BC Thm 9.2.10's injectivity, and that is open. This task reduces it to the one Prop
  `log [p̃] ∉ Frac(B_max)` (`logPTildeTranscendental_iff_notInFrac`, `transcendental_bcrisOf`), which is not proved.
* **L755-758** (Pan Thm 1.0.4 at `ℓ = 5`, Tate convention, no residual-image proviso): **unverified.** The text is
  right as written. Pan's hypothesis "potentially semistable" rests on the same `B_st` identification as L738-741,
  which is reduced here and not proved. Co-step (ii) (BC p. 128-129, abstract `A_cris` versus `AcrisOf`) also stays
  open for both lines.
* **L10972-10975 and L11019-11022** (BC cited for Thm 5.2.1 and Prop 6.3.3; the bibitem): **OK.** This work does not
  use those statements. It uses BC's §9 definitions (pp. 128-143) from the same notes, at locators the bibitem does not
  list (Known issue (v)).


## 8. Checks and deliverables

VERIFIED (this host, Lean 4.35.0, Mathlib v4.35.0):

* `lake build ZInQKernel.Contrib.OneProof.PanBergerFontaine`: built (10669 jobs; the merged files had no oleans).
* `lake build ZInQKernel.Contrib.OneProof.BdRInvariants`: built.
* `lake build ZInQKernel.Contrib.OneProof.LogPTranscendence`: built.
* `lake env lean` on each of: `ZInQKernel/Contrib/OneProof/LogPTranscendence.lean`,
  `ZInQKernel/Contrib/OneProof/LogPTranscendenceBdR.lean`, and their scratch copies. No errors, no warnings, no `sorry`.
* `#print axioms` of all 34 new declarations (29 + 5) gives `[propext, Classical.choice, Quot.sound]`. The output is
  in `scratch/logp-transc/axioms.txt`, produced by `scratch/logp-transc/LogPTranscendenceAxioms.lean` and
  `LogPTranscendenceBdRAxioms.lean`, which are the files plus `#print axioms` lines.

Deliverables:

* `ZInQKernel/Contrib/OneProof/LogPTranscendence.lean` and `ZInQKernel/Contrib/OneProof/LogPTranscendenceBdR.lean`
  (new; no edits elsewhere under `ZInQKernel/`; neither imports `ZInQKernel.OneProof.Main`);
* `scratch/logp-transc/` (scratch copies, axiom files, build logs `build1.txt` and `build2.txt`, results log
  `log.md`);
* this report, and `.fleet/logp-transc.md`.

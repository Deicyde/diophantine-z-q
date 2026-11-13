# t-different: textbook leaves T20, T21, T22 (ramification)

## Verdict

* **T20 (Hilbert's different formula), local form `PkgI6.HilbertDifferentFormula` (I6.7): PROVED**
  in Lean, sorry-free, over the verbatim statement: `PkgI6.hilbertDifferentFormula` in
  `scratch/t-different/HilbertLocal.lean` (axioms `propext`, `Classical.choice`, `Quot.sound`).
* **T21 (Serre's bound `v(𝔇) ≤ e − 1 + v(e)`), local form `PkgI6.DifferentBound` (I6.6): PROVED**
  in Lean, sorry-free, over the verbatim statement: `PkgI6.differentBound` in
  `scratch/t-different/DifferentBound.lean` (same three axioms).
* **T22 (Herbrand: `PkgI6.HerbrandQuotient`, `PkgI6.HerbrandTransitivity`): not proved.**  See §4
  for the plan and what exists.
* The **global** forms `GlueConductor.HilbertDifferentFormula` and
  `GlueConductor.SerreDifferentBound` (the ones `GlueConductor.D1_genuine` consumes) are **not**
  proved: they need the transport from the completion (or the localization at the decomposition
  field) to `𝓞_L`, which h-decomposition.md already lists as a citation (Serre III §4, I §7).
  h-decomposition.md §2 accepts either form for T20 and T21, so with the local forms T20 and T21
  are closed as leaves; the local-to-global transport remains a standard citation.

All statements were copied verbatim into `scratch/t-different/Statements.lean` (compiles) and,
because scratch files cannot import each other, again into each proof file (the definitions
`lowerRam`, `HilbertDifferentFormula`, `DifferentBound` are character-for-character those of
`scratch/h-decomposition/Leaves.lean` lines 5029-5100, with `lowerRam` referred to as
`TDifferent.lowerRam` in `HilbertLocal.lean`).

## 1. What Mathlib 4.35 has (VERIFIED by reading `.lake/packages/mathlib`)

* `Mathlib/RingTheory/DedekindDomain/Different.lean`: `differentIdeal`,
  `conductor_mul_differentIdeal` (`conductor(x)·𝔇 = (f'(x))` when `K(x) = L`),
  `pow_sub_one_dvd_differentIdeal` (the lower bound `e − 1`), `not_dvd_differentIdeal_of_intTrace_notMem`,
  `dvd_differentIdeal_iff` (`P ∣ 𝔇` iff ramified).  No upper bound, no Hilbert formula.
* No lower/upper ramification groups, no Herbrand function, no monogenicity theorem.
* Usable inputs: `MulSemiringAction.charpoly`, `Module.Basis.traceDual_powerBasis_eq` (Euler's formula
  `Tr(x^i / f'(x))`), `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` (deprecated, still
  present: `e f = [L : K]` for a local `B`), `Algebra.trace_trace`, `Field.exists_primitive_element`,
  `IsPrecomplete.prec`, Nakayama (`Submodule.le_of_le_smul_of_le_jacobson_bot`),
  `card_inertia_eq_ramificationIdxIn` (`|G_0| = e`, for T22).

## 2. T20, local (proved)

`scratch/t-different/HilbertLocal.lean`.  Route = Serre, *Corps locaux* III §6 Prop. 12 and
IV §1 Prop. 4 (UNVERIFIED locators, from memory):

1. `TDifferent.exists_adjoin_eq_top` (monogenicity): DVRs `A → B`, `B` finite and torsion-free over
   `A`, residue field of `A` perfect ⇒ `∃ x, A[x] = B`.  Proof: a primitive element `α` of `k_B/k_A`,
   a lift `x`; `x` or `x + π` makes `g(y) ∈ 𝔪 \ 𝔪²` for a lift `g` of the minimal polynomial of `α`
   (Taylor expansion, separability); then `B = A[y] + 𝔪^j` for every `j` and Nakayama over `A`.
   Completeness is not used.
2. `TDifferent.aeval_derivative_minpoly_eq_prod`: if `B = A[x]` and `Frac B/Frac A` is Galois,
   `f'(x) = ∏_{σ ≠ 1} (x − σx)` (degree count via `galRestrict` and `IsGalois.card_aut_eq_finrank`).
3. `TDifferent.mem_inertia_iff_of_adjoin`: if `B = A[x]`, `σ ∈ G_I ↔ σx − x ∈ I`.
4. `TDifferent.sum_card_sub_one`: `∑_{i<N} (|G_i| − 1) = ∑_{σ≠1} i_G(σ)`.
5. `TDifferent.hilbertDifferentFormula_of_adjoin_eq_top`: with Mathlib's conductor formula
   (conductor `= ⊤` since `B = A[x]`) `𝔇 = (f'(x)) = ∏ 𝔪^{i_G(σ)}`, and `G_N = 1` for
   `N = ∑ i_G(σ)`.
6. `PkgI6.hilbertDifferentFormula : PkgI6.HilbertDifferentFormula`.

## 3. T21, local (proved)

`scratch/t-different/DifferentBound.lean`.

1. `TDifferent.map_maximalIdeal_eq_pow`: `𝔪_A B = 𝔪_B^e`, `e = Ideal.ramificationIdx (maximalIdeal B) A`.
2. `PkgI6.differentBound_of_trace`: `DifferentBound` follows from `e ∈ Tr_{B/A}(B)`
   (`TraceContainsRamificationIdx`).  If `e = 0` in `B` the right side is `⊥`; otherwise
   `(e) = 𝔪_A^k`, `𝔇 = 𝔪_B^d`, and `d ≥ e(k+1)` would give `(𝔪_A^{k+1})B ∣ 𝔇`, contradicting
   `not_dvd_differentIdeal_of_intTrace_notMem` because `Tr(z) = e ∉ 𝔪_A^{k+1}`.
3. `TDifferent.exists_limit` (`B` is `𝔪_A`-adically precomplete, via coordinates in a basis) and
   `TDifferent.exists_root_of_residue` (Hensel's lemma in `B`, by Newton iteration
   `u ↦ u − w·g(u)` with a fixed inverse `w` of `g'(x)`; the limit is taken along `u_{e m}`).
4. `TDifferent.exists_intTrace_eq_ramificationIdx`: with `u` a Hensel root of a monic lift `g` of
   the minimal polynomial of a generator of `k_B/k_A`: `minpoly_A u = g`, `E = K(u)` has
   `[E : K] = f`, so `[L : E] = e` by `e f = [L : K]`; Euler's formula gives
   `Tr_{E/K}(u^{f−1}/g'(u)) = 1`, so `Tr_{L/K}(u^{f−1}/g'(u)) = e·1`, and `u^{f−1}/g'(u) ∈ B`.
5. `PkgI6.differentBound : PkgI6.DifferentBound`.

## 4. T22 (not proved): status and plan

Statements `PkgI6.HerbrandQuotient`, `PkgI6.HerbrandTransitivity` checked: compile, and match
Serre IV §3 Props. 14, 15 (`φ(u) = ∫_0^u |G_t|/|G_0|`, `G_t = G_{⌈t⌉}`, `G_t = G` for `t ≤ −1`,
`ψ(v) = sInf {u ≥ −1 | v ≤ φ(u)}`); no defect found.  A proof along Serre's lines needs, in this
setting: (a) Serre IV §1 Prop. 3, `e'·i_{G/H}(σ) = ∑_{s↦σ} i_G(s)` (from the monogenic generators
of `B/A` and `C/A` proved here and the identity `f^σ(x) = ∏_{s↦σ}(x − s x)` for `f` the minimal
polynomial of `x` over `C`); (b) `|H_0| = e(B/C)` (Mathlib's `card_inertia_eq_ramificationIdxIn`,
after building `IsGaloisGroup (B ≃ₐ[C] B) C B`); (c) the formula
`φ(u) = (1/g_0) ∑_s min(i_G(s), u+1) − 1` from the integral definition; (d) the coset lemma
`i_G(s'h) = min(i_G(s'), i_G(h))` for `s'` of maximal `i_G` in its coset (pure group theory); (e) the
inverse-function facts for `ψ`; (f) the plumbing between `B ≃ₐ[A] B`, `B ≃ₐ[C] B` and
`C ≃ₐ[A] C` (surjectivity of restriction).  With (a)-(d) transitivity is a finite computation:
`∑_{s↦σ} min(i_G(s), u+1) = h_0 · min(i_{G/H}(σ), φ_{B/C}(u) + 1)`.

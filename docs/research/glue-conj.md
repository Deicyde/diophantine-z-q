# glue-conj: `LeafConj` is glue (proved in Lean)

Status: research note (task glue-conj, 2026-11-12). Lean files: `scratch/glue-conj/Conj.lean`
(298 lines, self-contained, `import Mathlib`) and `scratch/glue-conj/UnramConj.lean` (942 lines,
glue-b3-unram's `Unram.lean` with the proof inserted). Log: `scratch/glue-conj/log.md`. No file
under `ZInQKernel/`, `blueprint/` or other tasks' notes or scratch was edited.

## 1. Main result

**(VERIFIED, compiled; axioms `propext`, `Classical.choice`, `Quot.sound`.)**
`GlueConj.leafConj : LeafConj` proves glue-b3-unram's leaf L-conj in exactly the form that
glue-b3-unram states it. The definitions `GQ`, `Qbar`, `LiesOver`, `inertiaGQ` and `LeafConj`
are copied verbatim; the md5 sums of the definition blocks match those in
`scratch/glue-b3-unram/Unram.lean`. The statement:

> for a prime `p` and valuation subrings `w, w'` of `ℚ̄` with `v_w(p) < 1` and `v_{w'}(p) < 1`,
> there is `σ ∈ G_ℚ` with `σ⁻¹ s σ ∈ I_w` for every `s ∈ I_{w'}`.

Here `I_w` is the image in `G_ℚ` of Mathlib's `ValuationSubring.inertiaSubgroup`.

In `UnramConj.lean`, `GlueB3Unram.unramified_outside_final` no longer has the `hConj` hypothesis:
its signature now starts `(hA : LeafB3a) (hB : LeafB3b)`, and the rest is unchanged. The proof
passes `leafConj` to `unramified_outside_of_unramifiedAt`. **B3 (v) (N5, `diophantine_zq.tex`
L702-712) now rests on the two leaves L-B3a and L-B3b only.** Finite ramification (`finRam`,
glue-b3-unram), the unramifiedness of the cyclotomic character (`cycUnram`) and conjugacy
(`leafConj`) are all proved glue. The file compiles with no errors, and all eight
`#print axioms` lines show only the three standard axioms.

## 2. Proof (all steps compiled)

Let `B = integralClosure ℤ ℚ̄` be the algebraic integers, and `Gal = ℚ̄ ≃ₐ[ℚ] ℚ̄`, which is
definitionally `GQ`.

1. **Center of a place** (`centerIdeal`, `mem_centerIdeal`, `centerIdeal_under`). Every
   valuation subring contains `B`, because valuation rings are integrally closed (Mathlib's
   `IsIntegrallyClosed.isIntegral_iff`). The center `𝔓_w = {b ∈ B | v_w(b) < 1}` is the comap
   of the maximal ideal of `w`, so it is prime. Its trace on `ℤ` is a prime containing `p`, hence
   equals `pℤ` (`Int.ideal_span_isMaximal_of_prime`).
2. **Transitivity on centers** (`exists_smul_eq`). The group `Gal` acts on `B`, and the fixed
   points of the action are `ℤ` (`InfiniteGalois.mem_bot_iff_fixed`, plus `ℤ` integrally closed).
   With the discrete topology on `B` the action is continuous, since stabilizers are open by
   `stabilizer_isOpen_of_isIntegral` and `continuousSMul_iff_stabilizer_isOpen`. `Gal` is
   compact (Mathlib instance) and totally separated (Mathlib instance). Mathlib's
   `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` (A. Yang) then gives `g` with
   `𝔓_{w'} = g • 𝔓_w`. That lemma contains the compactness argument (cofiltered limit of
   non-empty finite sets).
3. **Transport** (`val_smul_lt_one_iff`, `centerIdeal_smul`). `v_{g•w}(y) < 1 ↔ v_w(g⁻¹y) < 1`,
   so `𝔓_{g•w} = g • 𝔓_w = 𝔓_{w'}`.
4. **Center lemma** (`le_of_center`). If two valuation subrings `w₁, w₂` of `ℚ̄` over `p` have
   the same center on `B`, then `w₁ ≤ w₂`. Proof: take `x ∈ w₁`, set `K = ℚ(x)` (a number
   field) and `v = 𝔓 ∩ 𝓞_K` (a height-one prime, since it contains `p`). Mathlib's
   `HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq` (the localization `(𝓞_K)_v` is a
   valuation ring) writes `x·d = n` or `x·n = d` with `n ∈ 𝓞_K` and `d ∈ 𝓞_K \ v`. Comparing
   valuations gives `v_{w₂}(x) ≤ 1`. In the second case, if `v_{w₂}(x) > 1` then `n` lies in the
   common center, which contradicts `v_{w₁}(x) ≤ 1`. Applying the lemma both ways gives
   `w' = g • w`.
5. **Conjugate inertia** (`inertia_conj`). If `w' = g • w`, then `g⁻¹ I_{w'} g ≤ I_w`: the
   element `g⁻¹ t g` stabilizes `w`, and it acts trivially on the residue field because
   `v_w(g⁻¹ t g y − y) = v_{g•w}(t(gy) − gy) < 1`.

## 3. What remains

- For B3 (v): the leaves **L-B3a** (at an odd prime, inertia has at most one nontrivial
  continuous quadratic character) and **L-B3b** (the Legendre character mod an odd `p` is
  ramified at every place over `p`). Both are stated in glue-b3-unram §3, unchanged here.
  L-B3b looks provable as glue from Mathlib's cyclotomic ramification results together with
  glue-b3-unram's bridge (`inertia_le_of_unramifiedAt`, in the converse direction).
  SPECULATIVE; not attempted.
- Integration: when glue-b3-unram's file goes into the project, the `Conj` section of
  `UnramConj.lean` can be pasted in as is (it uses only `GQ`, `Qbar`, `LiesOver`,
  `inertiaGQ`, `LeafConj` and the `IsGalois ℚ ℚ̄` instance of that file). After that,
  `unramified_outside_final` drops `hConj`. Every caller that passed a `LeafConj` hypothesis
  then drops that argument.
- The leaf table of `docs/research/h-decomposition.md` / glue-b3-unram §3 should reclassify
  L-conj from leaf to glue (not edited here, because those are other tasks' notes).

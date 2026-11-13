# t40-igusa results log

Target: `ZInQ.RLeaf.IgusaTransitive` (ZInQKernel/Contrib/RLeaf/X1RationalCusp.lean).

## 2026-11-13 setup
- Fresh start (no earlier log). Branch wip/t40-igusa at 57a7fa26; merged origin/main (05a66d25)
  once; that merge touched no file under ZInQKernel/HDecomp or ZInQKernel/Contrib/RLeaf (VERIFIED,
  git diff --stat).
- Existing API used (VERIFIED, read): `X1Belyi.nTors`, `X1Belyi.xCoord_map`
  (`x(σP) = σ(x(P))`, ZInQKernel/HDecomp/ModCurves/X1Belyi.lean:172),
  `ZInQ.RLeaf.t36_torsionStructure` (T36, `E[N] ≅ (ℤ/N)²` over alg. closed char-0 fields),
  `WeierstrassCurve.Affine.Point.map` (Mathlib, additive hom of points along an algebra hom).

## Decision: which proof of Igusa's theorem to formalize
Candidates (all locators UNVERIFIED: no network):
1. Lang, *Elliptic functions*, Ch. 6 (Fricke functions of level N) and Shimura 1971, Thm 6.6
   (modular functions of level N). Needs: complex uniformization `ℂ/Λ_τ ≅ E_τ(ℂ)` with the
   Weierstrass ℘ addition law, so that the N-torsion x-coordinates of `E_{j(τ)}` are the values
   `℘((aτ+b)/N; τ)`; the Fricke functions `f_a` as meromorphic functions on ℍ with
   `f_a ∘ γ = f_{aγ}`; an embedding of the N-division field of `E_j` over `ℚ(j)` into the
   field of meromorphic functions on ℍ sending `j ↦ j(τ)`; the q-expansion principle for the
   arithmetic part. Mathlib 4.35 has modular forms, Eisenstein series and q-expansions, but no
   ℘-uniformization of elliptic curves and no identification of division polynomials with ℘
   values; Tau Ceti has the Tate curve (p-adic/formal uniformization) and Weil pairings, not the
   complex uniformization. (SPECULATIVE effort: many thousands of lines.)
2. Deligne–Rapoport: irreducibility of the moduli of level-N structures (needs moduli stacks,
   connectedness of fibres via ℂ or via Igusa curves). Not formalizable with Mathlib today.
3. Igusa's own proof (char p, Hasse invariant / Igusa curves, specialization). Needs reduction
   of the generic curve mod p, supersingular points, ramification of the Igusa cover. Not
   available in Mathlib or Tau Ceti.
4. Purely algebraic attempt via the Tate curve at `j = ∞` (Tau Ceti TateCurve/): gives the
   decomposition group at ∞ as `{[[c,k],[0,1]]}` in the Tate basis (ζ_N, q^{1/N}); its orbits on
   primitive vectors are indexed by the second coordinate up to sign, so local information at
   the only multiplicative place of `E_j` cannot give transitivity; a global input (irreducibility
   of `X(N)` / monodromy of the j-line, `PSL₂(ℤ) = ℤ/2 * ℤ/3`) is unavoidable. (Argument VERIFIED
   by hand computation; see docs/research/t40-igusa.md §2.)
Decision: none of the proofs fits in this task. Reduce `IgusaTransitive` to Igusa's theorem in
its weakest published form (`SL₂(ℤ/N)` in the image, on x-coordinates, Shimura 6.6's geometric
part), prove all the glue (SL₂(ℤ/N)-transitivity on order-N vectors, Galois action on points),
and also derive that leaf from Igusa's theorem as usually stated (GL₂, on points, any basis).

## Step 1: IgusaSL2.lean (VERIFIED, compiled with `lake env lean`, no warnings/errors)
File ZInQKernel/Contrib/RLeaf/IgusaSL2.lean. Proved, axioms [propext, Classical.choice, Quot.sound]:
- `exists_det_eq_one_of_addOrderOf : 0 < N → addOrderOf u = N → ∃ c d, u.1 * d - u.2 * c = 1`
- `exists_SL2_first_column` (SL₂(ℤ/N) moves (1,0) to any vector of order N)
- `igusaTransitive_of_igusaSL2X : IgusaSL2X → IgusaTransitive`
- `igusaSL2X_of_igusaGL2 : IgusaGL2 → IgusaSL2X` (basis from T36)
- `igusaTransitive_of_igusaGL2 : IgusaGL2 → IgusaTransitive`
Named leaves (def … : Prop): `IgusaSL2X` (SL₂ part on x-coordinates; Shimura 6.6 geometric part),
`IgusaGL2` (Igusa 1959 as usually stated: surjectivity onto GL₂(ℤ/N), points, every basis).

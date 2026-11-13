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

## Step 2: IgusaX0.lean (VERIFIED, compiled with `lake env lean`, clean)
`IgusaTransitive ↔ X0Transitive ∧ TateMuN` (`igusaTransitive_iff`), axioms standard three.
- `X0Transitive`: Galois transitive on cyclic subgroups of order N (∃σ, σP ∈ ⟨P'⟩). Published:
  irreducibility of Φ_N(X,j) over ℂ(j) (Lang EF Ch 5 §2 Thm 3; Cox Thm 11.18; UNVERIFIED numbers).
- `TateMuN`: ∃ Q₀ of order N whose generators R have x(R) = τ(x(Q₀)) for some τ. Published:
  Tate curve (Silverman ATAEC V.3.1, V.5.3, UNVERIFIED numbers) with Q₀ = image of ζ_N.
- Both are consequences of IgusaTransitive (proved), so each is strictly weaker or equal; their
  conjunction is equivalent to it. X0Transitive is the X₀(N) (degree ψ(N)) statement; TateMuN is
  local at j = ∞.
- Helper lemmas proved: `xCoord_neg`, `eq_or_eq_neg_of_xCoord_eq`, `addOrderOf_galPt`,
  `xCoord_galPt`.

## Step 3: IgusaLocal.lean (VERIFIED, compiled with `lake env lean`; standard axioms)
- `TateMuNOver Ω` (Ω alg. closed, Algebra Qj Ω, DecidableEq Ω): TateMuN over Ω.
- `tateMuN_of_over Ω : TateMuNOver Ω → TateMuN` PROVED: N-torsion of E_j(Ω) is the image of
  E_j(Kbar)[N] (`exists_map_eq_of_nsmul_eq_zero`, injective map between sets of N² points, T36
  on both sides); τ ∈ Aut(Ω/Qj) restricts to Kbar (`exists_restrict`, `AlgEquiv.restrictNormal`).
- `jInv : Qj →+* Qj` (j ↦ 1/j, `jInv_X`), `jInvLaurent : Qj →+* ℚ((t))` (j ↦ t⁻¹,
  `jInvLaurent_X`), `TateOmega` = AlgebraicClosure ℚ((t)) with Qj-algebra via jInvLaurent.
- Leaf `TateMuNLocal := TateMuNOver TateOmega`; `tateMuN_of_local`,
  `igusaTransitive_of_x0_tateMuNLocal : X0Transitive → TateMuNLocal → IgusaTransitive`.
- Pitfall: `Algebra ℚ (RatFunc ℚ)` diamond (RatFunc.instAlgebraOfPolynomial vs
  DivisionRing.toRatAlgebra) — `convert` + `Subsingleton.elim` (algebra_rat_subsingleton).
  Mathlib's `Algebra (RatFunc F) F⸨X⸩` is the scoped instance `RatFunc.liftAlgebra`
  (`open scoped RatFunc`); `AlgebraicClosure k` inherits every `Algebra R k`, hence the type
  synonym `TateOmega`.
- Coordination: task t40-tate (message 2026-11-13 ~10:00) reports TateCuspLaurent PROVED on
  origin/wip/t40-tate and plans to prove TateMuN in its own file TateCuspMuN.lean; agreed.

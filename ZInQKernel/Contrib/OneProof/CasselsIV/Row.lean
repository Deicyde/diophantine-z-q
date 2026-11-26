import ZInQKernel.Contrib.OneProof.CasselsTatePairing

/-!
# Cassels (1962), Theorem 1.1, at `k = ℚ`, as a single-print row

J. W. S. Cassels, *Arithmetic on curves of genus 1. IV. Proof of the Hauptvermutung*,
J. reine angew. Math. 211 (1962), 95–112: Theorem 1.1, p. 95, with §3 (viii), p. 104.

This file states the theorem at `k = ℚ` in the tree's vocabulary and proves nothing:

* `SelmerTwoPower.CasselsIVThm11 E`: Theorem 1.1 for one curve `E/ℚ`;
* `SelmerTwoPower.CasselsIVThm11Elliptic`: Theorem 1.1 for every elliptic curve over `ℚ`, the
  most faithful instance of the print at `k = ℚ`.

`CasselsIV/Glue.lean` derives from it the form printed by Poonen–Stoll
(`SelmerTwoPower.CasselsTatePairingPS`), which is all that pole completeness reads.

## The dictionary

* `C`, an abelian variety of dimension 1 over `k = ℚ`: an elliptic curve `E/ℚ`
  (`WeierstrassCurve ℚ` with `E.IsElliptic`).
* `Ш`: Cassels's group of "classes of principal homogeneous spaces for `C` defined over `k` which
  are everywhere locally trivial" (p. 95). Cassels identifies these classes with Galois cohomology
  in §1, p. 98: a "1—1 correspondence between `WC` and `H¹(Γ, 𝔊̄)`", where "`𝔊̄` is the group of
  points of `C` defined over the algebraic closure `k̄` of `k` and `Γ` is the galois group of
  `k̄/k`", with continuous cocycles (p. 98, footnote 12: "continuous cocycles when `Γ` has the
  Krull topology and `𝔊̄` the discrete topology"); p. 108 repeats "`WC = H¹(Γ, 𝔊̄)`". Also p. 98:
  "`Ш` is just the intersection of the kernels of the maps `WC(k) → WC(k_𝔭)`, where `k_𝔭` runs
  through all the local completions of `k`". "Everywhere locally trivial" means trivial under the
  restriction map `j_𝔭` for every valuation `𝔭` of `k` (p. 105, (5.1)), and the archimedean
  valuations are among them: p. 108 treats "a finite extension of a `p`-adic field (or the
  reals)". The tree's `sha E`
  (`SelmerTwoPower.sha`) is the subgroup of `H¹(G_ℚ, E(ℚˢ))`, continuous cohomology with discrete
  coefficients, of the classes that restrict to zero at every `ℚ_p` (`embFin`) **and** at `ℝ`
  (`embInf`, `RealCompletion`). So the real place is included. In characteristic `0` the
  separable closure is the algebraic closure.
* The step from homogeneous spaces to `H¹` (the Weil–Châtelet identification) is not formalised in
  the tree. The row is stated on the cohomological side, which is the side on which Cassels builds
  the pairing (§3, from a continuous cocycle `{a_σ}` for `η`).
* `Q/Z`: `QZ = ℚ ⧸ ℤ`.
* "naturally-defined": not formalised. The row is an existence statement, so it is weaker than the
  print in this respect.
-/

noncomputable section

namespace ZInQ.Manuscript.SelmerTwoPower

/-- **Cassels (1962), Theorem 1.1, at `k = ℚ`, for one curve `E`.** This is the statement for a
given curve, meaningful only for an elliptic `E`: Cassels's `C` is an abelian variety of
dimension 1. The row is `CasselsIVThm11Elliptic`, which carries the guard `E.IsElliptic`; applied
to a singular cubic, this unguarded helper says more than Cassels does. Cassels, *Arithmetic on
curves of genus 1. IV. Proof of the Hauptvermutung*, J. reine angew. Math. 211 (1962), p. 95:

"Theorem 1.1. Let `k` be an algebraic numberfield, `C` an abelian variety of dimension 1 and `Ш`
the corresponding Tate-Šafarevič group of classes of principal homogeneous spaces for `C` defined
over `k` which are everywhere locally trivial. Then there exists a naturally-defined
skew-symmetric form `l(ξ, η)` defined for `ξ, η ∈ Ш` and taking values in the group `Q/Z` of the
rationals modulo 1 which has the following property:
Let `m` be a natural number and suppose that `l(ξ, η) = 0` for all `ξ ∈ Ш` such that `mξ = 0`;
then `η = mH` for some `H ∈ Ш`."

Clause by clause:

* `l : sha E →+ sha E →+ QZ`: the form `l`, bilinear (p. 104, §4: "We have completed the
  construction of the bilinear form `l(ξ, η)` (`ξ, η ∈ Ш`)").
* `∀ ξ, l ξ ξ = 0`: "skew-symmetric", in the sense Cassels proves, §3 (viii), p. 104:
  "`l(ξ, η)` is skewsymmetric, i.e. `l(ξ, ξ) = 0` for all `ξ`."
* the last clause: the property of the last sentence, with `η` in the second slot as printed. -/
def CasselsIVThm11 (E : WeierstrassCurve ℚ) : Prop :=
  ∃ l : sha E →+ sha E →+ QZ, (∀ ξ, l ξ ξ = 0) ∧
    ∀ m : ℕ, 0 < m → ∀ η : sha E, (∀ ξ : sha E, m • ξ = 0 → l ξ η = 0) →
      ∃ H : sha E, η = m • H

/-- **Cassels (1962), Theorem 1.1, at `k = ℚ`, for every elliptic curve over `ℚ`**: the theorem
as printed, for every abelian variety of dimension 1 over the number field `ℚ`
(`CasselsIVThm11` at each `E` with `E.IsElliptic`). -/
def CasselsIVThm11Elliptic : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → CasselsIVThm11 E

end ZInQ.Manuscript.SelmerTwoPower

end

#print axioms ZInQ.Manuscript.SelmerTwoPower.CasselsIVThm11
#print axioms ZInQ.Manuscript.SelmerTwoPower.CasselsIVThm11Elliptic

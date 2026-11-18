import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.RingTheory.NoetherNormalization

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
Only upstream lines [(14, 265)] are retained.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory

universe u v w x


/-!
# Dimension of a finite type domain over a field

Let `k` be a field, let `S` be a `k`-algebra of finite type which is a domain and let `K` be its
field of fractions. This file proves Stacks 00P0: the Krull dimension of `S` is the transcendence
degree of `K` over `k`, and the local ring of `S` at any maximal ideal has that same dimension.

Noether normalization (Stacks 00OY) provides an injective finite `k`-algebra map
`P = k[Y_0, …, Y_{r - 1}] → S` with `r = dim S`. Transcendence degree is unchanged along an
algebraic extension of domains, so `trdeg_k K = trdeg_k S = trdeg_k P = r`, which is the first
assertion. For the second, let `𝔪 ⊆ S` be maximal and `𝔮 = 𝔪 ∩ P`. Then `𝔮` is maximal, hence of
height `r`, and `P` is a normal domain, so `P → S` satisfies going down and
`height 𝔪 = height 𝔮 + height 𝔪(S ⧸ 𝔮S) ≥ r` (Stacks 00ON, in Mathlib
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`). The reverse inequality is
`height 𝔪 ≤ dim S = r`.

## Main results

* `ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg` (Stacks 00P0):
  `dim S = trdeg_k K`, and `dim S_𝔪 = trdeg_k K` for every maximal ideal `𝔪` of `S`.

## Implementation notes

The transcendence degree computation is `trdeg_eq_natCast_of_isAlgebraic`: for a tower
`R ⊆ S ⊆ A` of rings with `A` a domain algebraic over `S`, a transcendence degree of `S` over `R`
which is a natural number is also the transcendence degree of `A` over `R`. It is
`lift_trdeg_add_eq` (Stacks 030H) together with `trdeg_eq_zero`, with the `Cardinal.lift`s — what
lets the three rings live in three different universes — cancelled inside, since the value is a
natural number. Applied to `k ⊆ P ⊆ S` and then to `k ⊆ S ⊆ K` it computes `trdeg_k K` from
`trdeg_k P = r`, which is `MvPolynomial.trdeg_of_isDomain`.

That every maximal ideal `𝔮` of `P` has height `r` is `height_eq_of_isMaximal_mvPolynomial`,
proved by induction on the number of variables. For `r = 0` the ring is `k`, of dimension `0`. The
step is `height_eq_of_isMaximal_polynomial`: over a Noetherian Jacobson ring `R` all of whose
maximal ideals have height `n`, a maximal ideal `Q` of `R[X]` has height `n + 1`, because its
contraction to `R` is maximal (Zariski's lemma, `Polynomial.isMaximal_comap_C_of_isJacobsonRing`)
and `Polynomial.height_eq_height_add_one` adds the one. It is applied to `𝔮` transported along
`k[Y_0, …, Y_r] ≅ k[Y_0, …, Y_{r - 1}][X]`, heights being invariant under a ring equivalence.

The second half is `height_eq_of_module_finite_mvPolynomial`, stated for a Noetherian domain `S`
carrying a `P = MvPolynomial (Fin r) k`-algebra structure with `Module.Finite P S`,
`FaithfulSMul P S` and `dim S = r` — that is all the normalization is used for. What Stacks 00OY
contributes is that structure: `P` becomes the base of `S` through the algebra structure
`(MvPolynomial.aeval y).toAlgebra`, so that `algebraMap P S` is the map `MvPolynomial.aeval y`
the tag produces, and the tower `k ⊆ P ⊆ S` then holds because `aeval y` is a `k`-algebra map.

Both halves bound a height by a Krull dimension, in the form `height_le_of_ringKrullDim_eq`: a
prime of a ring of dimension `n : ℕ` has height at most `n`, the coercion `ℕ∞ → WithBot ℕ∞` of
`Ideal.height_le_ringKrullDim_of_isPrime` being undone inside.

The source's proof invokes Stacks 00OR — all local rings of `S` at maximal ideals have the same
dimension, read off maximal chains of primes in a regular ring — to reduce the second assertion
to the first. The going down formula for heights along `P → S` (Stacks 00ON) is used in its
place: it is in Mathlib, and it computes `height 𝔪` for one maximal `𝔪` at a time rather than
comparing two of them, so no separate reduction step is needed.

## References

* [StacksProject 00P0](https://stacks.math.columbia.edu/tag/00P0)
-/

namespace Stacks.KrullDimension.TranscendenceDegree


open Cardinal in
#cloudR2Vendor trdeg_eq_natCast_of_isAlgebraic in
/-- If `A` is a domain algebraic over `S` and `R ⊆ S ⊆ A` is a tower of rings with injective
structure maps, then a transcendence degree `n : ℕ` of `S` over `R` is also that of `A`
over `R`. -/
private lemma trdeg_eq_natCast_of_isAlgebraic (R : Type*) (S : Type v) (A : Type w)
    [CommRing R] [Nontrivial R] [CommRing S] [CommRing A] [NoZeroDivisors A] [Algebra R S]
    [Algebra R A] [Algebra S A] [IsScalarTower R S A] [FaithfulSMul R S] [FaithfulSMul S A]
    [Algebra.IsAlgebraic S A] {n : ℕ} (h : Algebra.trdeg R S = n) :
    Algebra.trdeg R A = n := by
  have h' := lift_trdeg_add_eq R S A
  rw [trdeg_eq_zero (R := S) (A := A), lift_zero, add_zero, h] at h'
  exact lift_injective.{v} (by simpa using h'.symm)
#cloudR2Vendor height_le_of_ringKrullDim_eq in

/-- A prime ideal of a ring of Krull dimension `n : ℕ∞` has height at most `n`. -/
private lemma height_le_of_ringKrullDim_eq {R : Type*} [CommRing R] {n : ℕ∞}
    (h : ringKrullDim R = n) (I : Ideal R) [I.IsPrime] : I.height ≤ n := by
  have h' := Ideal.height_le_ringKrullDim_of_isPrime (I := I)
  rw [h] at h'
  exact_mod_cast h'

open Polynomial in
#cloudR2Vendor height_eq_of_isMaximal_polynomial in
/-- If every maximal ideal of a Noetherian Jacobson ring `R` has height `n`, then every maximal
ideal of `R[X]` has height `n + 1`. -/
private lemma height_eq_of_isMaximal_polynomial {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsJacobsonRing R] {n : ℕ} (hR : ∀ p : Ideal R, p.IsMaximal → p.height = n)
    (Q : Ideal R[X]) [Q.IsMaximal] : Q.height = n + 1 := by
  have hq : (Q.comap (C : R →+* R[X])).IsMaximal := isMaximal_comap_C_of_isJacobsonRing Q
  have : Q.LiesOver (Q.comap (C : R →+* R[X])) := ⟨by rw [Ideal.under_def, algebraMap_eq]⟩
  rw [height_eq_height_add_one (Q.comap (C : R →+* R[X])) Q, hR _ hq]
#cloudR2Vendor height_eq_of_isMaximal_mvPolynomial in

/-- Every maximal ideal of a polynomial ring in `r` variables over a field has height `r`. -/
private lemma height_eq_of_isMaximal_mvPolynomial (k : Type u) [Field k] {r : ℕ}
    (𝔮 : Ideal (MvPolynomial (Fin r) k)) [𝔮.IsMaximal] : 𝔮.height = r := by
  induction r with
  | zero =>
    simpa using height_le_of_ringKrullDim_eq (n := 0)
      (by simp [ringKrullDim_eq_zero_of_field]) 𝔮
  | succ r ih =>
    have e := (MvPolynomial.finSuccEquiv k r).toRingEquiv
    have : (Ideal.map e 𝔮).IsMaximal := Ideal.map_isMaximal_of_equiv e
    rw [← RingEquiv.height_map e 𝔮, height_eq_of_isMaximal_polynomial fun p hp => @ih p hp]
    push_cast
    ring
#cloudR2Vendor height_eq_of_module_finite_mvPolynomial in

/-- Every maximal ideal of a Noetherian domain of Krull dimension `r` which is finite and faithful
over the polynomial algebra in `r` variables over a field has height `r`. -/
private lemma height_eq_of_module_finite_mvPolynomial (k : Type u) [Field k] {r : ℕ} {S : Type v}
    [CommRing S] [IsDomain S] [IsNoetherianRing S] [Algebra (MvPolynomial (Fin r) k) S]
    [Module.Finite (MvPolynomial (Fin r) k) S] [FaithfulSMul (MvPolynomial (Fin r) k) S]
    (hdim : ringKrullDim S = r) (𝔪 : Ideal S) [𝔪.IsMaximal] : 𝔪.height = r := by
  have : Algebra.IsIntegral (MvPolynomial (Fin r) k) S := Algebra.IsIntegral.of_finite _ _
  set 𝔮 : Ideal (MvPolynomial (Fin r) k) := 𝔪.comap (algebraMap _ S)
  have : 𝔮.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔪
  have : 𝔪.LiesOver 𝔮 := ⟨rfl⟩
  refine le_antisymm (height_le_of_ringKrullDim_eq hdim 𝔪) ?_
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown 𝔮 𝔪,
    height_eq_of_isMaximal_mvPolynomial k 𝔮]
  exact le_self_add
#cloudR2Vendor solution in

/-- The statement of Stacks 00P0: for a domain `S` of finite type over a field `k` with field of
fractions `K`, `dim S = trdeg_k K`, and the localization of `S` at every maximal ideal has the same
dimension. A Noether normalization `k[Y_0, …, Y_{r - 1}] → S` with `r = dim S` gives
`trdeg_k K = r`, and every maximal ideal of `S` has height `r` by going down. -/
theorem solution
    (k : Type u) [Field k] (S : Type v) [CommRing S] [IsDomain S] [Algebra k S]
    [Algebra.FiniteType k S] (K : Type w) [Field K] [Algebra S K] [IsFractionRing S K]
    [Algebra k K] [IsScalarTower k S K] :
    ringKrullDim S = (Cardinal.toENat (Algebra.trdeg k K) : WithBot ℕ∞) ∧
      ∀ (𝔪 : Ideal S) [𝔪.IsMaximal] (A : Type x) [CommRing A] [Algebra S A]
          [IsLocalization.AtPrime A 𝔪],
        ringKrullDim A = (Cardinal.toENat (Algebra.trdeg k K) : WithBot ℕ∞) := by
  obtain ⟨t, ht⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k S).FG)
  obtain ⟨r, y, -, hinj, hfin, hdim⟩ :=
    exists_finite_inj_aeval_ringKrullDim_eq_of_adjoin_eq_top k t.finite_toSet ht
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have : Algebra.IsAlgebraic S K := IsLocalization.isAlgebraic K (nonZeroDivisors S)
  let inst : Algebra (MvPolynomial (Fin r) k) S := (MvPolynomial.aeval y : _ →ₐ[k] S).toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin r) k) S :=
    IsScalarTower.of_algebraMap_eq fun x => by simp [inst, RingHom.algebraMap_toAlgebra]
  have : Module.Finite (MvPolynomial (Fin r) k) S := hfin
  have : FaithfulSMul (MvPolynomial (Fin r) k) S :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have hS : Algebra.trdeg k S = (r : Cardinal.{v}) :=
    trdeg_eq_natCast_of_isAlgebraic k (MvPolynomial (Fin r) k) S
      (by simp [MvPolynomial.trdeg_of_isDomain])
  have htr : Cardinal.toENat (Algebra.trdeg k K) = (r : ℕ∞) := by
    rw [trdeg_eq_natCast_of_isAlgebraic k S K hS]
    simp
  refine ⟨?_, fun 𝔪 _ A _ _ _ => ?_⟩
  · rw [hdim, htr]
    rfl
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔪 A, htr,
      height_eq_of_module_finite_mvPolynomial k hdim 𝔪]

end Stacks.KrullDimension.TranscendenceDegree

/-!
# Dimension of a finite type domain over a field

Let `k` be a field, let `S` be a `k`-algebra of finite type which is a domain, and let `K` be the
field of fractions of `S`. Then the Krull dimension of `S` is the transcendence degree of `K` over
`k`, and so is the dimension of the local ring of `S` at every maximal ideal (Stacks 00P0).

The proof is the source's: all local rings of `S` at maximal ideals have the same dimension
(Lemma 00OR), so it suffices to compute `dim S`; Noether normalization (Lemma 00OY) produces an
injective finite `k`-algebra map `k[y_1, …, y_d] → S` with `d = dim S`, and a finite extension of
domains induces a finite, hence algebraic, extension `k(y_1, …, y_d) ⊆ K` of fraction fields, so
`trdeg_k K = d`.

## Main results

* `ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg`: both assertions of the source,
  for an arbitrary field of fractions `K` of `S` and an arbitrary model of the local ring.

## Implementation notes

`Algebra.trdeg k K` is a `Cardinal` while `ringKrullDim S` lives in `WithBot ℕ∞`, so the equality
is stated through `Cardinal.toENat`. This loses nothing: `Cardinal.toENat` is injective on the
finite cardinals and sends the infinite ones to `⊤`, so the equation says exactly that `dim S` is
the transcendence degree whatever the latter is. That the transcendence degree is in fact finite
is not part of the assertion but comes for free from `trdeg_lt_aleph0`, since `k ⊆ K` is
essentially of finite type (`Algebra.EssFiniteType.of_isLocalization` and
`Algebra.EssFiniteType.comp`).

The field of fractions is an abstract one, `IsFractionRing S K` together with
`IsScalarTower k S K`, rather than the concrete `FractionRing S`, so that the lemma applies to
any other model of `K`, such as the residue field `κ(𝔭)` of a prime of a finite type algebra,
without transporting along `IsLocalization.algEquiv`. For the same reason the local ring is an
abstract `IsLocalization.AtPrime A 𝔪` in its own universe, as in Lemma 00OQ;
`Localization.AtPrime 𝔪` is one instantiation, and `IsLocalization.AtPrime.ringKrullDim_eq_height`
rewrites the second conjunct into the equivalent statement `𝔪.height = trdeg_k K` about `S`
alone.

The source's "finite type `k`-algebra" is `Algebra.FiniteType k S`, and its "integral domain" is
`IsDomain S`, which also supplies the nontriviality that keeps `ringKrullDim S ≠ ⊥`. The two
assertions are carried by one theorem, neither being an instance of the other: the first computes
a global dimension, the second a family of local ones.

Faithfulness. (1) No hypothesis is dead: `Field k` and `Algebra.FiniteType k S` are used by both
conjuncts — for `S = k[x_1, x_2, …]` the dimension is infinite while the transcendence degree of
`K` over `k` is `ℵ₀`, and over the base `ℤ` in place of a field `S = ℤ` has dimension `1` and
`K = ℚ` transcendence degree `0` — `IsDomain S` is the source's "integral domain" and is used by
both, there being no field of fractions and no common dimension of the local rings at maximal
ideals without it (`S = k[x] × k[y, z]` has them of dimensions `1` and `2`), and the scalar tower
is what makes `Algebra.trdeg k K` the transcendence degree of `K` over the *given* `k`-structure
of `S`. (2) The scalars and base are the source's: the transcendence degree is taken
over `k`, of the fraction field of `S` itself, and both Krull dimensions are those of `S` and of
its localizations as `S`-algebras; no base change occurs. (3) The maps the source names are
pinned: `IsFractionRing S K` pins `K` as a localization of `S` at its nonzero divisors along
`algebraMap S K`, and `IsLocalization.AtPrime A 𝔪` pins `A` as the localization of `S` at the
complement of `𝔪`, rather than positing the existence of some field or some local ring of the
right dimension. (4) The instantiation is not degenerate: for `k = ℚ` and `S = ℚ[x]` one has
`K = ℚ(x)`, `trdeg = 1 = dim S`, and every localization at a maximal ideal `(f)` is a discrete
valuation ring, of dimension `1`; for `S = ℚ[x, y]/(y ^ 2 - x ^ 3)` the transcendence degree is
again `1` and the conclusion holds also at the maximal ideal `(x, y)` of the cusp, where the local
ring is not regular. For `S = k` both conjuncts read `0 = 0`, so the statement is consistent but
not vacuous.

## References

* [StacksProject 00P0](https://stacks.math.columbia.edu/tag/00P0)
-/
#cloudR2Vendor ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg in



/-- **Stacks 00P0.** Let `k` be a field, let `S` be a finite type `k`-algebra which is a domain,
and let `K` be its field of fractions. Then the Krull dimension of `S` is the transcendence
degree of `K` over `k`, and the local ring of `S` at every maximal ideal has that same
dimension. -/

theorem ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg
    (k : Type u) [Field k] (S : Type v) [CommRing S] [IsDomain S] [Algebra k S]
    [Algebra.FiniteType k S] (K : Type w) [Field K] [Algebra S K] [IsFractionRing S K]
    [Algebra k K] [IsScalarTower k S K] :
    ringKrullDim S = (Cardinal.toENat (Algebra.trdeg k K) : WithBot ℕ∞) ∧
      ∀ (𝔪 : Ideal S) [𝔪.IsMaximal] (A : Type x) [CommRing A] [Algebra S A]
          [IsLocalization.AtPrime A 𝔪],
        ringKrullDim A = (Cardinal.toENat (Algebra.trdeg k K) : WithBot ℕ∞) :=
  Stacks.KrullDimension.TranscendenceDegree.solution k S K


end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort

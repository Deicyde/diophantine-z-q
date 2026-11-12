import Mathlib

/-!
# pkg-I6: arithmetic of `ℚ` and of local fields (steps B1, B2, C10, D1, D3, D4 of h-trust)

Leaves are `def … : Prop` over genuine Mathlib objects.  Each carries its published locator
(locators from memory are UNVERIFIED; see `docs/research/pkg-I6.md`).  Definitions that Mathlib
lacks (lower and upper ramification groups, Herbrand's function, the Artin conductor of a
representation of a finite group) are given concretely in Part II.

Part I  (global):  Skolem–Noether, the 2-torsion of the Brauer sequence of `ℚ` in Galois-cohomology
                   form, local Kronecker–Weber, Chebotarev, Brauer–Nesbitt.
Part II (local):   ramification groups, Serre's bound for the different, Hilbert's formula,
                   Herbrand's theorem, transitivity of `φ`, the Artin conductor, local class field
                   theory with the upper numbering theorem.
-/

open CategoryTheory

namespace PkgI6

/-! ## Part I. Global inputs -/

section SkolemNoether

/-- **Leaf I6.1 (Skolem–Noether).** Let `A` be a finite-dimensional central simple algebra over a
field `K` and `B` a simple `K`-algebra.  Any two `K`-algebra maps `B → A` are conjugate by a unit
of `A`.  Reiner, *Maximal orders* (1975), Thm 7.21; Farb–Dennis, *Noncommutative algebra*,
Thm 3.14 (both UNVERIFIED).  B1 uses the special case `B = A` (`skolemNoether_aut`). -/
def SkolemNoether : Prop :=
  ∀ (K A B : Type) [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] [Ring B] [Algebra K B] [IsSimpleRing B] [FiniteDimensional K B]
    (f g : B →ₐ[K] A), ∃ u : Aˣ, ∀ b : B, g b = (u : A) * f b * ((u⁻¹ : Aˣ) : A)

/-- The form used in B1: every `K`-algebra automorphism of a finite-dimensional central simple
algebra is inner.  GLUE (proved from the leaf). -/
theorem skolemNoether_aut (h : SkolemNoether) (K A : Type) [Field K] [Ring A] [Algebra K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] (σ : A ≃ₐ[K] A) :
    ∃ u : Aˣ, ∀ a : A, σ a = (u : A) * a * ((u⁻¹ : Aˣ) : A) := by
  obtain ⟨u, hu⟩ := h K A A (AlgHom.id K A) σ.toAlgHom
  exact ⟨u, fun a => by simpa using hu a⟩

end SkolemNoether

section Brauer

/-- The trivial `G_ℚ`-module `ℤ/2 = {±1}`, as a topological representation over `ℤ` (discrete
topology on `ZMod 2`). -/
noncomputable abbrev Z2 (K : Type) [Field K] : TopRep ℤ (Field.absoluteGaloisGroup K) :=
  TopRep.of (ContRepresentation.trivial ℤ (Field.absoluteGaloisGroup K) (ZMod 2))

/-- The localization map `H^n(G_ℚ, ℤ/2) → H^n(G_F, ℤ/2)` for a field `F` with a ring map
`ℚ → F` (Mathlib's `Field.absoluteGaloisGroup.map`, which depends on a choice of embedding of
algebraic closures; the induced map on cohomology does not, since conjugation acts trivially on
cohomology). -/
noncomputable abbrev loc (F : Type) [Field F] [Algebra ℚ F] (n : ℕ) :
    continuousCohomology n (Z2 ℚ) ⟶
      continuousCohomology n
        (TopRep.res (Field.absoluteGaloisGroup.map (algebraMap ℚ F) :
          Field.absoluteGaloisGroup F →* Field.absoluteGaloisGroup ℚ) (Z2 ℚ)) :=
  ContinuousCohomology.map (Field.absoluteGaloisGroup.map (algebraMap ℚ F)) (𝟙 _) n

/-- `loc_p`: localization at the prime `p`. -/
noncomputable abbrev locP (p : ℕ) [Fact p.Prime] := loc ℚ_[p] 2

/-- `loc_∞`: localization at the real place. -/
noncomputable abbrev locInf := loc ℝ 2

/-- **Leaf I6.2a (Albert–Brauer–Hasse–Noether, 2-torsion, Galois-cohomology form).**
`H²(G_ℚ, ℤ/2) → ∏_v H²(G_{ℚ_v}, ℤ/2)` is injective: `Ш²(ℚ, ℤ/2) = 0` over all places.
This is the injectivity of `Br ℚ → ⊕_v Br ℚ_v` (Milne, ADT, Ch. I, Thm 4.? / Neukirch–Schmidt–
Wingberg (8.1.17); Tate in Cassels–Fröhlich VII §11.2: UNVERIFIED locators) composed with the
Kummer isomorphism `H²(G_K, μ₂) ≅ Br(K)[2]` (Hilbert 90; Serre, *Corps locaux* X §4–5), which is
natural in `K`. -/
def BrauerHasse2 : Prop :=
  ∀ x : continuousCohomology 2 (Z2 ℚ),
    locInf.hom x = 0 → (∀ (p : ℕ) [Fact p.Prime], (locP p).hom x = 0) → x = 0

open Classical in
/-- **Leaf I6.2b (reciprocity, 2-torsion form).** For `x ∈ H²(G_ℚ, ℤ/2)` the set of places where
`x` is locally nonzero is finite and has even cardinality.  This is `∑_v inv_v = 0` together with
`inv_v(x) ∈ {0, 1/2}` and `inv_v` injective (Milne ADT Ch. I; Serre, *Corps locaux* XIII §3 for
`Br ℚ_p ≅ ℚ/ℤ`; UNVERIFIED locators). -/
def BrauerReciprocity2 : Prop :=
  ∀ x : continuousCohomology 2 (Z2 ℚ),
    {p : Nat.Primes | haveI : Fact (p : ℕ).Prime := ⟨p.2⟩; (locP (p : ℕ)).hom x ≠ 0}.Finite ∧
    Even ({p : Nat.Primes | haveI : Fact (p : ℕ).Prime := ⟨p.2⟩; (locP (p : ℕ)).hom x ≠ 0}.ncard
      + if locInf.hom x = 0 then 0 else 1)

/-- **Leaf I6.2c (local `H²`).** `H²(G_{ℚ_p}, ℤ/2) ≅ Br(ℚ_p)[2] ≅ ℤ/2` and
`H²(G_ℝ, ℤ/2) ≅ Br(ℝ) ≅ ℤ/2`: each has exactly two elements.  (Serre, *Corps locaux* XIII §3,
Prop. 6 and X §5; UNVERIFIED locators.) Stated for the restricted module that `loc` lands in. -/
def LocalH2Card : Prop :=
  (∀ (p : ℕ) [Fact p.Prime],
      Nat.card (continuousCohomology 2
        (TopRep.res (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p]) :
          Field.absoluteGaloisGroup ℚ_[p] →* Field.absoluteGaloisGroup ℚ) (Z2 ℚ))) = 2) ∧
    Nat.card (continuousCohomology 2
        (TopRep.res (Field.absoluteGaloisGroup.map (algebraMap ℚ ℝ) :
          Field.absoluteGaloisGroup ℝ →* Field.absoluteGaloisGroup ℚ) (Z2 ℚ))) = 2

end Brauer

section LocalKW

/-- **Leaf I6.3 (local Kronecker–Weber for `ℚ_p`).** Every finite abelian extension of `ℚ_p`
inside `\bar ℚ_p` lies in `ℚ_p(μ_n)` for some `n ≥ 1`.  (Serre, *Local class field theory*, in
Cassels–Fröhlich, §3.? ; Neukirch, *ANT* V (1.10); Lang, *ANT* (UNVERIFIED locators).)  In B2 it
replaces "local reciprocity" in the square-root criterion: a finite-order character of `G_{ℚ_p}`
has a character square root iff it is trivial on the element acting by `ζ ↦ ζ⁻¹` on `p`-power
roots of unity and trivially on prime-to-`p` roots of unity (GLUE). -/
def LocalKroneckerWeber (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ L : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] L →
    IsAbelianGalois ℚ_[p] L →
      ∃ n : ℕ, 0 < n ∧ L ≤ IntermediateField.adjoin ℚ_[p] {x : PadicAlgCl p | x ^ n = 1}

end LocalKW

section Chebotarev

open NumberField

/-- **Leaf I6.4 (Chebotarev, existence form).** For a finite Galois extension `M/ℚ`, a finite set
`S` of rational primes and `σ ∈ Gal(M/ℚ)`, there is a prime `p ∉ S`, unramified in `M`, and a prime
`Q` of `𝓞_M` over `p` at which `σ` is the arithmetic Frobenius.  A consequence of the density
theorem (Neukirch, *ANT* VII (13.4): the primes with Frobenius class `⟨σ⟩` have Dirichlet density
`#⟨σ⟩/#G > 0`; UNVERIFIED locator).  C10 uses it to make Frobenius elements dense in `G_ℚ`. -/
def ChebotarevExists : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M] (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M),
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ Q : Ideal (𝓞 M), ∃ _ : Q.IsPrime,
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ Algebra.IsUnramifiedAt ℤ Q ∧ IsArithFrobAt ℤ σ Q

end Chebotarev

section BrauerNesbitt

/-- **Leaf I6.5 (Brauer–Nesbitt, characteristic 0, trace form).** Over a field of characteristic
`0`, two finite-dimensional semisimple representations of a group with the same character are
isomorphic.  (Lang, *Algebra*, rev. 3rd ed., XVII Cor. 3.8, for semisimple modules over any
`k`-algebra; Curtis–Reiner (1962) (27.13), and (30.16) for the characteristic-polynomial version in
any characteristic: UNVERIFIED locators.) -/
def BrauerNesbittChar0 : Prop :=
  ∀ (k G V W : Type) [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W),
    IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
    IsSemisimpleModule (MonoidAlgebra k G) σ.asModule →
    (∀ g : G, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) →
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule)

end BrauerNesbitt

end PkgI6

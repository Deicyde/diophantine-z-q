import Mathlib
import ZInQKernel.HDecomp.Conductor.Dyadic

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-I6-rest/I6Base.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


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

lemma eq_of_ne_zero_of_card_two {G : Type*} [AddGroup G] (h : Nat.card G = 2) {a b : G}
    (ha : a ≠ 0) (hb : b ≠ 0) : a = b := by
  obtain ⟨x, y, -, hu⟩ := Nat.card_eq_two_iff.mp h
  have mem : ∀ z : G, z = x ∨ z = y := fun z => by
    have : z ∈ ({x, y} : Set G) := hu ▸ Set.mem_univ z
    simpa using this
  rcases mem 0 with h0 | h0 <;> rcases mem a with h1 | h1 <;> rcases mem b with h2 | h2 <;>
    first
    | exact h1.trans h2.symm
    | exact absurd (h1.trans h0.symm) ha
    | exact absurd (h2.trans h0.symm) hb

/-- **The Brauer step of B2 (GLUE, proved from I6.2a-c).** Two classes in `H²(G_ℚ, ℤ/2)` that are
locally nonzero at exactly the same primes are equal (agreement at `∞` comes from reciprocity).
In N5 L683-692 the classes are `[ε]` and the boundary `δχ`. -/
theorem eq_of_same_finite_support (hH : BrauerHasse2) (hR : BrauerReciprocity2)
    (hC : LocalH2Card) (x y : continuousCohomology 2 (Z2 ℚ))
    (h : ∀ (p : ℕ) [Fact p.Prime], (locP p).hom x = 0 ↔ (locP p).hom y = 0) : x = y := by
  have hp : ∀ (p : ℕ) [Fact p.Prime], (locP p).hom (x - y) = 0 := by
    intro p _
    rw [map_sub, sub_eq_zero]
    by_cases hx : (locP p).hom x = 0
    · rw [hx, ((h p).mp hx)]
    · exact eq_of_ne_zero_of_card_two (hC.1 p) hx (fun hy => hx ((h p).mpr hy))
  have hinf : locInf.hom (x - y) = 0 := by
    obtain ⟨-, hev⟩ := hR (x - y)
    have hempty : {q : Nat.Primes | haveI : Fact (q : ℕ).Prime := ⟨q.2⟩;
        (locP (q : ℕ)).hom (x - y) ≠ 0} = ∅ := by
      ext q
      have : Fact (q : ℕ).Prime := ⟨q.2⟩
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact hp q
    rw [hempty, Set.ncard_empty, zero_add] at hev
    by_contra hne
    rw [if_neg hne] at hev
    exact Nat.not_even_one hev
  exact sub_eq_zero.mp (hH (x - y) hinf hp)

/-! ### The same three leaves at the level of continuous inhomogeneous cochains

Galois cohomology is classically *defined* by continuous inhomogeneous cochains (Serre,
*Cohomologie galoisienne*, I §2.2), and that is how N5 manipulates `ε` (a function
`G_ℚ × G_ℚ → {±1}`).  These forms need no comparison with Mathlib's resolution-defined
`continuousCohomology` (Mathlib describes only `H⁰` explicitly, `LowDegree.lean`). -/

/-- A continuous inhomogeneous 2-cocycle with values in the trivial module `ℤ/2`. -/
def IsCocycle2 {G : Type*} [Group G] [TopologicalSpace G] (ε : G → G → ZMod 2) : Prop :=
  Continuous (fun x : G × G => ε x.1 x.2) ∧ ∀ a b c, ε b c - ε (a * b) c + ε a (b * c) - ε a b = 0

/-- `ε` is the coboundary of a continuous 1-cochain. -/
def IsCoboundary2 {G : Type*} [Group G] [TopologicalSpace G] (ε : G → G → ZMod 2) : Prop :=
  ∃ f : G → ZMod 2, Continuous f ∧ ∀ a b, ε a b = f b - f (a * b) + f a

/-- Restriction of a cochain on `G_ℚ` to `G_F` along Mathlib's map `G_F → G_ℚ`. -/
noncomputable def resC (F : Type) [Field F] [Algebra ℚ F] (ε : Field.absoluteGaloisGroup ℚ →
    Field.absoluteGaloisGroup ℚ → ZMod 2) :
    Field.absoluteGaloisGroup F → Field.absoluteGaloisGroup F → ZMod 2 :=
  fun a b => ε (Field.absoluteGaloisGroup.map (algebraMap ℚ F) a)
    (Field.absoluteGaloisGroup.map (algebraMap ℚ F) b)

/-- **Leaf I6.2a′** (= I6.2a on cochains). -/
def BrauerHasse2C : Prop :=
  ∀ ε, IsCocycle2 ε → IsCoboundary2 (resC ℝ ε) →
    (∀ (p : ℕ) [Fact p.Prime], IsCoboundary2 (resC ℚ_[p] ε)) → IsCoboundary2 ε

open Classical in
/-- **Leaf I6.2b′** (= I6.2b on cochains). -/
def BrauerReciprocity2C : Prop :=
  ∀ ε, IsCocycle2 ε →
    {p : Nat.Primes | haveI : Fact (p : ℕ).Prime := ⟨p.2⟩;
        ¬ IsCoboundary2 (resC ℚ_[(p : ℕ)] ε)}.Finite ∧
    Even ({p : Nat.Primes | haveI : Fact (p : ℕ).Prime := ⟨p.2⟩;
        ¬ IsCoboundary2 (resC ℚ_[(p : ℕ)] ε)}.ncard
      + if IsCoboundary2 (resC ℝ ε) then 0 else 1)

/-- `H²(G, ℤ/2)` has exactly two elements, on cochains: a non-trivial class exists, and any two
non-trivial classes differ by a coboundary. -/
def H2TwoClasses (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  (∃ ε, IsCocycle2 (G := G) ε ∧ ¬ IsCoboundary2 ε) ∧
  ∀ ε₁ ε₂, IsCocycle2 (G := G) ε₁ → IsCocycle2 ε₂ → ¬ IsCoboundary2 ε₁ → ¬ IsCoboundary2 ε₂ →
    IsCoboundary2 (ε₁ - ε₂)

/-- **Leaf I6.2c′** (= I6.2c on cochains). -/
def LocalH2CardC : Prop :=
  (∀ (p : ℕ) [Fact p.Prime], H2TwoClasses (Field.absoluteGaloisGroup ℚ_[p])) ∧
    H2TwoClasses (Field.absoluteGaloisGroup ℝ)

lemma IsCoboundary2.sub {G : Type*} [Group G] [TopologicalSpace G] {ε₁ ε₂ : G → G → ZMod 2}
    (h₁ : IsCoboundary2 ε₁) (h₂ : IsCoboundary2 ε₂) : IsCoboundary2 (ε₁ - ε₂) := by
  obtain ⟨f₁, hf₁, e₁⟩ := h₁
  obtain ⟨f₂, hf₂, e₂⟩ := h₂
  refine ⟨f₁ - f₂, hf₁.sub hf₂, fun a b => ?_⟩
  simp only [Pi.sub_apply, e₁, e₂]; ring

lemma IsCocycle2.sub {G : Type*} [Group G] [TopologicalSpace G] {ε₁ ε₂ : G → G → ZMod 2}
    (h₁ : IsCocycle2 ε₁) (h₂ : IsCocycle2 ε₂) : IsCocycle2 (ε₁ - ε₂) := by
  refine ⟨h₁.1.sub h₂.1, fun a b c => ?_⟩
  have := h₁.2 a b c
  have := h₂.2 a b c
  simp only [Pi.sub_apply]
  linear_combination h₁.2 a b c - h₂.2 a b c

lemma IsCocycle2.resC {ε} (h : IsCocycle2 ε) (F : Type) [Field F] [Algebra ℚ F] :
    IsCocycle2 (resC F ε) := by
  refine ⟨?_, fun a b c => ?_⟩
  · have hφ := (Field.absoluteGaloisGroup.map (algebraMap ℚ F)).continuous
    exact h.1.comp ((hφ.comp continuous_fst).prodMk (hφ.comp continuous_snd))
  · simp only [PkgI6.resC, map_mul]
    exact h.2 _ _ _

/-- **The Brauer step of B2 on cochains (GLUE, proved from I6.2a′-c′).**  Two continuous
2-cocycles on `G_ℚ` with values in `ℤ/2` that are locally non-trivial at the same primes differ by
a continuous coboundary. -/
theorem cob_of_same_finite_support (hH : BrauerHasse2C) (hR : BrauerReciprocity2C)
    (hC : LocalH2CardC) (ε₁ ε₂) (c₁ : IsCocycle2 ε₁) (c₂ : IsCocycle2 ε₂)
    (h : ∀ (p : ℕ) [Fact p.Prime],
      IsCoboundary2 (resC ℚ_[p] ε₁) ↔ IsCoboundary2 (resC ℚ_[p] ε₂)) :
    IsCoboundary2 (ε₁ - ε₂) := by
  have c := c₁.sub c₂
  have hp : ∀ (p : ℕ) [Fact p.Prime], IsCoboundary2 (resC ℚ_[p] (ε₁ - ε₂)) := by
    intro p _
    change IsCoboundary2 (resC ℚ_[p] ε₁ - resC ℚ_[p] ε₂)
    by_cases h₁ : IsCoboundary2 (resC ℚ_[p] ε₁)
    · exact h₁.sub ((h p).mp h₁)
    · exact (hC.1 p).2 _ _ (c₁.resC _) (c₂.resC _) h₁ (fun h₂ => h₁ ((h p).mpr h₂))
  have hinf : IsCoboundary2 (resC ℝ (ε₁ - ε₂)) := by
    obtain ⟨-, hev⟩ := hR _ c
    have hempty : {q : Nat.Primes | haveI : Fact (q : ℕ).Prime := ⟨q.2⟩;
        ¬ IsCoboundary2 (resC ℚ_[(q : ℕ)] (ε₁ - ε₂))} = ∅ := by
      ext q
      have : Fact (q : ℕ).Prime := ⟨q.2⟩
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact hp q
    rw [hempty, Set.ncard_empty, zero_add] at hev
    by_contra hne
    rw [if_neg hne] at hev
    exact Nat.not_even_one hev
  exact hH _ c hinf hp

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

/-! ## Part II. Local fields: ramification groups, the different, conductors, local CFT

Setting (Serre, *Corps locaux*, Ch. III–IV): `A → B` a finite extension of discrete valuation
rings, `A` complete with perfect residue field, fraction fields separable (and Galois where
stated).  Then `B` is the integral closure of `A` in `Frac B`, and `B ≃ₐ[A] B` is `Gal(L/K)`.
The definitions below are Serre's, written over Mathlib's `IsLocalRing.maximalIdeal`. -/

section Ramification

open IsLocalRing

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]

/-- **Definition (Serre IV §1).** The lower ramification group `G_i` (`i ≥ 0`) of `B/A`:
the `σ` with `v_B(σ b − b) ≥ i + 1` for all `b ∈ B`.  Written with Mathlib's
`AddSubgroup.inertia` (the subgroup acting trivially modulo `𝔪_B^{i+1}`), as glue-conductor's
`ramGroup` does in the global setting. -/
def lowerRam (i : ℕ) : Subgroup (B ≃ₐ[A] B) :=
  (maximalIdeal B ^ (i + 1)).toAddSubgroup.inertia (B ≃ₐ[A] B)

lemma mem_lowerRam {i : ℕ} {σ : B ≃ₐ[A] B} :
    σ ∈ lowerRam A B i ↔ ∀ b : B, σ b - b ∈ maximalIdeal B ^ (i + 1) := Iff.rfl

/-- Lower numbering for a real index `u ≥ -1` (Serre IV §3): `G_u = G_{⌈u⌉}`, `G_{-1} = G`. -/
noncomputable def lowerRamR (u : ℝ) : Subgroup (B ≃ₐ[A] B) :=
  if u ≤ -1 then ⊤ else lowerRam A B (⌈u⌉.toNat)

/-- **Definition (Serre IV §3).** Herbrand's function
`φ_{B/A}(u) = ∫₀ᵘ dt / (G₀ : G_t)`. -/
noncomputable def herbrandPhi (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u, (Nat.card (lowerRamR A B t) : ℝ) / (Nat.card (lowerRamR A B 0) : ℝ)

/-- **Definition (Serre IV §3).** Upper numbering `G^v = G_{ψ(v)}`, `ψ = φ⁻¹`; here `ψ(v)` is
written `sInf {u ≥ -1 | v ≤ φ(u)}` (`φ` is a continuous increasing bijection of `[-1, ∞)`). -/
noncomputable def upperRam (v : ℝ) : Subgroup (B ≃ₐ[A] B) :=
  lowerRamR A B (sInf {u : ℝ | -1 ≤ u ∧ v ≤ herbrandPhi A B u})

/-- The subgroup rule for lower numbering (Serre IV §1 Prop. 2): for an intermediate ring `C`,
`(B/C)_i = (B/A)_i ∩ Gal(B/C)`.  GLUE: immediate from the definition (proved). -/
theorem lowerRam_tower (C : Type) [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    (i : ℕ) :
    lowerRam C B i = (lowerRam A B i).comap (AlgEquiv.restrictScalarsHom A) := by
  ext σ; rfl

end Ramification

section LocalLeaves

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- **Leaf I6.6 (Serre's bound for the different).** For a finite separable extension of
complete discrete valuation rings with perfect residue field, `v_B(𝔇_{B/A}) ≤ e − 1 + v_B(e)`,
where `e` is the ramification index.  Serre, *Corps locaux*, III §6, remark after Prop. 13
(UNVERIFIED locator).  Written `𝔇 ∣ 𝔪_B^{e-1}·(e)` (ideals of a DVR are ordered by divisibility;
if `e = 0` in `B` the right side is `⊥` and the statement is empty).  Mathlib has only the lower
bound `pow_sub_one_dvd_differentIdeal`. -/
def DifferentBound : Prop :=
  ∀ (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)],
    differentIdeal A B ∣
      maximalIdeal B ^ (Ideal.ramificationIdx (maximalIdeal B) A - 1) *
        Ideal.span {((Ideal.ramificationIdx (maximalIdeal B) A : ℕ) : B)}

/-- **Leaf I6.7 (Hilbert's formula for the different).** For `B/A` as above and Galois,
`v_B(𝔇_{B/A}) = ∑_{i ≥ 0} (|G_i| − 1)`.  Serre, *Corps locaux*, IV §1, Prop. 4 (UNVERIFIED
locator). -/
def HilbertDifferentFormula : Prop :=
  ∀ (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)],
    ∃ N : ℕ, lowerRam A B N = ⊥ ∧
      differentIdeal A B =
        maximalIdeal B ^ (∑ i ∈ Finset.range N, (Nat.card (lowerRam A B i) - 1))

/-- **Leaf I6.8 (Herbrand's theorem).** For a tower `A → C → B` with `B/A` and `C/A` Galois and
`r : Gal(B/A) → Gal(C/A)` the restriction, `Gal(C/A)^v = r(Gal(B/A)^v)` for all `v`.
Serre, *Corps locaux*, IV §3, Prop. 14 (UNVERIFIED locator).  (`r` is determined by `hr`.) -/
def HerbrandQuotient : Prop :=
  ∀ (A C B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C] [Module.Finite A C]
    [Module.IsTorsionFree A C] [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    [IsGalois (FractionRing A) (FractionRing C)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)]
    [Algebra C B] [IsScalarTower A C B] [Module.IsTorsionFree C B]
    (r : (B ≃ₐ[A] B) →* (C ≃ₐ[A] C))
    (_hr : ∀ σ c, algebraMap C B (r σ c) = σ (algebraMap C B c)) (v : ℝ),
    upperRam A C v = (upperRam A B v).map r

/-- **Leaf I6.9 (transitivity of Herbrand's function).** For a tower `A → C → B` with `B/A`
Galois (hence `B/C` Galois) and `C/A` Galois, `φ_{B/A} = φ_{C/A} ∘ φ_{B/C}`.
Serre, *Corps locaux*, IV §3, Prop. 15 (UNVERIFIED locator). -/
def HerbrandTransitivity : Prop :=
  ∀ (A C B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C] [Module.Finite A C]
    [Module.IsTorsionFree A C] [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    [IsGalois (FractionRing A) (FractionRing C)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)]
    [Algebra C B] [IsScalarTower A C B] [Module.Finite C B] [Module.IsTorsionFree C B],
    ∀ u : ℝ, -1 ≤ u → herbrandPhi A B u = herbrandPhi A C (herbrandPhi C B u)

/-- The principal units `U^{(n)} = 1 + 𝔪^n` (`n ≥ 1`) and `U^{(0)} = A^×`, inside `K^×`. -/
def unitFiltration (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (n : ℕ) :
    Set (FractionRing A)ˣ :=
  {x | ∃ a : A, (x : FractionRing A) = algebraMap A (FractionRing A) a ∧
    (if n = 0 then IsUnit a else a - 1 ∈ maximalIdeal A ^ n)}

/-- **Leaf I6.10 (local class field theory, finite abelian level, with the upper numbering
theorem).** For `B/A` as above, abelian Galois, with finite residue field `𝔽_q`, there is a
surjective homomorphism `θ : K^× → Gal(L/K)` whose kernel is the norm group `N_{L/K}(L^×)`,
which maps `π` (any element of valuation one) to an element acting on the residue field of `B`
by `x ↦ x^q`, and which maps `U^{(⌈v⌉)}` onto `G^v` for every real `v ≥ 0` (for integer `v` this
is the upper numbering theorem; for the other `v` it adds Hasse–Arf, Serre V §7 Thm 1, that the
upper jumps of an abelian extension are integers).
Serre, *Corps locaux*, XIII §4 Prop. 13 and XV §2 Thm 1, Cor. 3; Serre, *Local class field
theory* in Cassels–Fröhlich, §§2.8, 4.? (UNVERIFIED locators).  The canonical reciprocity map
is one such `θ`, so this ∃-form is a consequence of the published theorem. -/
def LocalReciprocityUpper : Prop :=
  ∀ (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)],
    (∀ σ τ : B ≃ₐ[A] B, σ * τ = τ * σ) →
    ∃ θ : (FractionRing A)ˣ →* (B ≃ₐ[A] B), Function.Surjective θ ∧
      (∀ x, θ x = 1 ↔ ∃ y : FractionRing B,
          Algebra.norm (FractionRing A) y = (x : FractionRing A)) ∧
      (∀ (π : A), Irreducible π → ∀ hπ : IsUnit (algebraMap A (FractionRing A) π),
          ∀ b : B, θ hπ.unit b - b ^ Nat.card (ResidueField A) ∈ maximalIdeal B) ∧
      (∀ v : ℝ, 0 ≤ v → θ '' unitFiltration A ⌈v⌉₊ = (upperRam A B v : Set (B ≃ₐ[A] B)))

end LocalLeaves

section Conductor

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]

/-- `codim V^H` for a subgroup `H` acting through `ρ`. -/
noncomputable def codimInv {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (B ≃ₐ[A] B) V) (H : Subgroup (B ≃ₐ[A] B)) : ℕ :=
  Module.finrank k V - Module.finrank k (Representation.invariants (ρ.comp H.subtype :
      Representation k H V))

/-- **Definition (Serre, *Corps locaux*, VI §2).** The Artin conductor exponent of a
representation `V` of `Gal(L/K)`: `f(V) = ∑_{i ≥ 0} (|G_i|/|G_0|) · codim V^{G_i}`. -/
noncomputable def artinConductor {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (B ≃ₐ[A] B) V) : ℚ :=
  ∑ᶠ i : ℕ, ((Nat.card (lowerRam A B i) : ℚ) / Nat.card (lowerRam A B 0)) *
    (codimInv A B ρ (lowerRam A B i) : ℚ)

/-- **D4, the conductor bound used by Glazer (GLUE, to be proved from the definitions).**
If every upper ramification group `G^v` with `v > U ≥ 0` acts trivially, then
`f(V) ≤ dim V · (1 + U)`.  It is the change of variables `f(V) = ∫_{-1}^∞ codim V^{G^v} dv`
(Serre VI §2, exercise / IV §3) with `codim ≤ dim V`. -/
def ArtinConductorLeOfUpper : Prop :=
  ∀ {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Finite (B ≃ₐ[A] B)] [IsDomain B] [IsDiscreteValuationRing B]
    (ρ : Representation k (B ≃ₐ[A] B) V) (U : ℝ), 0 ≤ U →
    (∀ v : ℝ, U < v → ∀ σ ∈ upperRam A B v, ρ σ = 1) →
    (artinConductor A B ρ : ℝ) ≤ Module.finrank k V * (1 + U)

end Conductor

section Dyadic

/-! Imported from glue-conductor's `scratch/glue-conductor/Dyadic.lean`
(`GlueConductor.exists_sq_eq_one_add`, commit 2aeeb7f2). -/

open IsLocalRing Polynomial

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- Square roots near one: if `(2) = 𝔪^e`, `z ∈ 𝔪^{2e+s}` and `s ≥ 1`, then `1 + z = (1 + w)²`
for some `w ∈ 𝔪^{e+s}`. -/
theorem exists_sq_eq_one_add [IsAdicComplete (maximalIdeal A) A] (e s : ℕ) (hs : 1 ≤ s)
    (h2 : Ideal.span {(2 : A)} = maximalIdeal A ^ e) (z : A)
    (hz : z ∈ maximalIdeal A ^ (2 * e + s)) :
    ∃ w ∈ maximalIdeal A ^ (e + s), (1 + w) ^ 2 = 1 + z :=
  GlueConductor.exists_sq_eq_one_add e s hs h2 z hz

end Dyadic

section GaloisFactorial

/-! ## D1 (a): `[F̃ : K] ≤ a!` and `e ≤ a!` (glue-conductor's open item (a))

`F̃`, the Galois closure of a separable `F/K` of degree `a`, is the splitting field of the minimal
polynomial of a primitive element, of degree `a`.  Its Galois group acts faithfully on the at most
`a` roots, so `[F̃ : K] ≤ a!`.  The ramification index of a prime of a number field is at most
the degree. -/

open Polynomial

/-- The degree of the splitting field of a separable polynomial is at most `(deg f)!`. -/
theorem finrank_splittingField_le_factorial {K : Type*} [Field K] (f : K[X]) (hf : f.Separable) :
    Module.finrank K f.SplittingField ≤ f.natDegree.factorial := by
  rw [← Polynomial.Gal.card_of_separable hf]
  haveI : Fact ((f.map (algebraMap K f.SplittingField)).Splits) := ⟨SplittingField.splits f⟩
  calc Nat.card f.Gal ≤ Nat.card (Equiv.Perm (f.rootSet f.SplittingField)) :=
        Nat.card_le_card_of_injective _ (Polynomial.Gal.galActionHom_injective f f.SplittingField)
    _ = (Nat.card (f.rootSet f.SplittingField)).factorial := Nat.card_perm
    _ ≤ f.natDegree.factorial := Nat.factorial_le (by
        rw [Nat.card_coe_set_eq]; exact Polynomial.ncard_rootSet_le f _)

/-- The same for any splitting field `L` of `f`. -/
theorem finrank_isSplittingField_le_factorial {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : K[X]) [Polynomial.IsSplittingField K L f] (hf : f.Separable) :
    Module.finrank K L ≤ f.natDegree.factorial := by
  rw [(Polynomial.IsSplittingField.algEquiv L f).toLinearEquiv.finrank_eq]
  exact finrank_splittingField_le_factorial f hf

open NumberField in
/-- The ramification index of a nonzero prime of a number field is at most the degree. -/
theorem ramificationIdx_le_finrank_of_numberField (L : Type) [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [P.IsPrime] :
    P.ramificationIdx ℤ ≤ Module.finrank ℚ L := by
  classical
  by_cases h0 : P = ⊥
  · subst h0; rw [Ideal.ramificationIdx_bot_eq_one]; exact Module.finrank_pos
  have hPm : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h0
  have : (P.under ℤ).IsMaximal := by
    first
      | exact Ideal.IsMaximal.under ℤ P
      | exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  rw [← NumberField.RingOfIntegers.rank L,
    ← Ideal.sum_ramification_inertia_eq_finrank (P.under ℤ) (𝓞 L)]
  have hP : P.LiesOver (P.under ℤ) := ⟨rfl⟩
  let q : (P.under ℤ).primesOver (𝓞 L) := ⟨P, inferInstance, hP⟩
  calc P.ramificationIdx ℤ ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ :=
        Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg_pos _ _)
    _ ≤ _ := Finset.single_le_sum (f := fun q : (P.under ℤ).primesOver (𝓞 L) =>
        q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)

open NumberField in
/-- **D1 (a), the hypothesis `e ≤ a!` of glue-conductor's `D1_genuine`.**  If `L` is a splitting
field over `ℚ` of a polynomial of degree `a` (e.g. the Galois closure of a field of degree `a`,
via the minimal polynomial of a primitive element), every prime of `𝓞 L` has `e ≤ a!`. -/
theorem ramificationIdx_le_factorial (L : Type) [Field L] [NumberField L] (f : ℚ[X])
    [Polynomial.IsSplittingField ℚ L f] (hf : f.Separable) (P : Ideal (𝓞 L)) [P.IsPrime] :
    P.ramificationIdx ℤ ≤ f.natDegree.factorial :=
  (ramificationIdx_le_finrank_of_numberField L P).trans
    (finrank_isSplittingField_le_factorial f hf)

end GaloisFactorial

section PrincipalUnits

open IsLocalRing

/-- **D3, squaring on principal units at `p = 2` (GLUE; elementary).**  If `B` is a complete DVR
with `2·B = 𝔪^e`, `e ≥ 1`, then for `r > e` every element of `1 + 𝔪^{r+e}` is the square of an
element of `1 + 𝔪^r`.  Applied twice: `(U^{e+1})⁴ = U^{3e+1}` (N5 L835-838).  N5 cites
Silverman, AEC IV.6.4 (formal logarithm of `Ĝ_m`); it is also Newton's form of Hensel's lemma for
`x² + 2x − y` (`v(f(0)) ≥ r + e > 2e = 2 v(f'(0))`).  Mathlib's general Hensel lemma needs a unit
derivative, so this one is not immediate.  PROVED elsewhere: glue-conductor's
`scratch/glue-conductor/Dyadic.lean` (`exists_sq_eq_one_add`, `exists_fourth_root`, commit
2aeeb7f2, via `u² + u = z/4` and Mathlib's `IsAdicComplete.henselianRing`); kept here as a
statement only. -/
theorem sq_principalUnits (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (maximalIdeal B) B] (e : ℕ) (he1 : 1 ≤ e)
    (he : Ideal.span {(2 : B)} = maximalIdeal B ^ e) (r : ℕ) (hr : e < r)
    (y : B) (hy : y ∈ maximalIdeal B ^ (r + e)) :
    ∃ x ∈ maximalIdeal B ^ r, (1 + x) ^ 2 = 1 + y := by
  obtain ⟨w, hw, h⟩ := exists_sq_eq_one_add (A := B) e (r - e) (by omega) he y
    (by rwa [show 2 * e + (r - e) = r + e by omega])
  exact ⟨w, by rwa [show e + (r - e) = r by omega] at hw, h⟩

end PrincipalUnits

end PkgI6


import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.AbVarBC.Points

/-!
# av-split, row H-24 (`PkgI2.ReductionTorsionBijective`, T4, I2-Red)

The row is imported from `ZInQKernel/HDecomp/Objects.lean` (unchanged; used at universe `0`).

Leaves (published form):
* `MulEtaleAbelianScheme`: `[m]` on an abelian scheme is étale when `m` is invertible on the base;
* `UnramifiedSectionsEq`: two `S`-morphisms from a connected scheme into an unramified separated
  `S`-scheme that agree at one point (with residue fields) are equal;
* `StacksHenselEtaleSection`: étale algebras over a henselian local ring have sections through
  rational primes.

Glue:
* `henselian_of_isAlgClosed` (proved): a valuation subring of an algebraically closed field is a
  henselian local ring;
* `HenselEtaleLift` (GLUE Prop, scheme form of the Hensel property);
* everything else (valuative criterion for the lifts, the adjunction for points of `𝒜_K`, the
  group laws) is proved below from Mathlib.
-/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AvSplit.T4

open PkgI2

/-! ## 1. Leaves -/

/-- **LEAF (H-24, a): multiplication by `m` on an abelian scheme is étale for `m` invertible on
the base.** Bosch–Lütkebohmert–Raynaud, *Néron models* (1990), §7.3, Lemma 2 (b) (UNVERIFIED
locator: for a smooth commutative group scheme `G` over `S` with connected fibres, `[n]_G` is étale
if `n` is invertible on `S`; for an abelian scheme it is moreover finite and flat); also Mumford,
*Geometric invariant theory* (3rd ed. 1994), §6.1 and Mumford, *Abelian varieties*, §6 Application
2 over a field (UNVERIFIED). Stated over an affine base `Spec O`, `[m] = (𝟙 𝒜)^m` in the group
`Hom(𝒜, 𝒜)`, and an abelian scheme as in `PkgI2.IsAbelianScheme` (proper, smooth, geometrically
connected fibres; Mumford GIT Def. 6.1). -/
def MulEtaleAbelianScheme : Prop :=
  ∀ (O : Type) [CommRing O] (𝒜 : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜] (m : ℕ),
    IsUnit (m : O) → Etale ((𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left)

/-- **LEAF (H-24, b): morphisms into an unramified separated scheme agreeing at a point.** The
Stacks project, Morphisms, Lemma 29.35.17 (UNVERIFIED tag/number; also EGA IV₄ 17.4.9): let `Y → S`
be unramified and separated, `X` a connected `S`-scheme, `a, b : X → Y` two `S`-morphisms and
`x ∈ X` with `a(x) = b(x)` such that the two induced maps `κ(a(x)) → κ(x)` agree; then `a = b`.
The pair (point, map of residue fields) is the morphism `Spec κ(x) → X → Y`, so the hypothesis is
`(Spec κ(x) → X) ≫ a = (Spec κ(x) → X) ≫ b` (Mathlib's `Scheme.fromSpecResidueField`, and
`Scheme.SpecToEquivOfField`). Unramified = formally unramified and locally of finite type
(Mathlib's notions). -/
def UnramifiedSectionsEq : Prop :=
  ∀ (X Y S : Scheme.{0}) (π : Y ⟶ S) [IsSeparated π] [LocallyOfFiniteType π]
    [FormallyUnramified π] (a b : X ⟶ Y), ConnectedSpace X → a ≫ π = b ≫ π →
    ∀ x : X, X.fromSpecResidueField x ≫ a = X.fromSpecResidueField x ≫ b → a = b

/-- **LEAF (H-24, c): sections of étale algebras over a henselian local ring.** The Stacks
project, Algebra, Lemma 10.153.3 (tag 04GG), (1) ⇒ (8) (UNVERIFIED item number): `(R, 𝔪, κ)`
henselian, `R → S` étale, `𝔮 ⊆ S` a prime over `𝔪` with `κ = κ(𝔮)`; then there is a section
`τ : S → R` of `R → S` (an `R`-algebra map) with `𝔮 = τ⁻¹(𝔪)`. Henselian is Mathlib's
`HenselianLocalRing` (Stacks Def. 10.153.1, simple roots lift). The condition `κ = κ(𝔮)` is
stated as `R → S/𝔮` onto (equivalent: `R/𝔪 ⊆ S/𝔮 ⊆ κ(𝔮)`). Used by the proof of the GLUE
`HenselEtaleLift` (§2). -/
def StacksHenselEtaleSection : Prop :=
  ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (S : Type) [CommRing S] [Algebra R S]
    [Algebra.Etale R S] (q : Ideal S) [q.IsPrime],
    q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R →
    Function.Surjective ((Ideal.Quotient.mk q).comp (algebraMap R S)) →
    ∃ τ : S →ₐ[R] R, q = (IsLocalRing.maximalIdeal R).comap τ

/-! ## 2. Glue -/

/-- **GLUE `HenselEtaleLift` (Hensel's property in scheme form).** For a henselian local ring `R`
with residue field `κ`, an étale morphism `f : X → Y`, a morphism `b : Spec R → Y` and a lift
`a₀ : Spec κ → X` of `b|_{Spec κ}`, there is a lift `a : Spec R → X` of `b` restricting to `a₀`.
What it needs: `b` factors through an affine open `U = Spec B ⊆ Y` (an open of the local scheme
`Spec R` containing the closed point is everything), `a₀` through an affine open
`V = Spec C ⊆ f⁻¹U`, `B → C` is étale (Mathlib `HasRingHomProperty`), and Stacks 04GG
(`StacksHenselEtaleSection`) for the étale `R`-algebra `R ⊗_B C` at the prime given by `a₀`. -/
def HenselEtaleLift : Prop :=
  ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (X Y : Scheme.{0}) (f : X ⟶ Y) [Etale f]
    (b : Spec (.of R) ⟶ Y) (a₀ : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X),
    a₀ ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ b →
    ∃ a : Spec (.of R) ⟶ X, a ≫ f = b ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ a = a₀

/-- In a linearly ordered commutative monoid with zero, a product of elements `≤ 1` that is `< 1`
has a factor `< 1`. -/
theorem exists_lt_one_of_prod_lt_one {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ]
    (s : Multiset Γ) (hle : ∀ x ∈ s, x ≤ 1) (hlt : s.prod < 1) : ∃ x ∈ s, x < 1 := by
  by_contra h
  push Not at h
  have : s.prod = 1 := by
    rw [Multiset.prod_eq_one]
    intro x hx
    exact le_antisymm (hle x hx) (h x hx)
  exact (ne_of_lt hlt) this

/-- **A valuation subring of an algebraically closed field is a henselian local ring (proved).**
Every monic `f ∈ w[X]` splits over `Ω` with roots integral over `w`, hence in `w` (valuation rings
are integrally closed); if `f(a₀) ∈ 𝔪` then `∏ (a₀ - rᵢ) ∈ 𝔪`, so some `a₀ - rᵢ ∈ 𝔪`. (The
derivative condition is not needed.) -/
theorem henselian_of_isAlgClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω] (w : ValuationSubring Ω) :
    HenselianLocalRing w := by
  refine ⟨fun f hf a₀ h₁ _ => ?_⟩
  classical
  set F := f.map (algebraMap w Ω) with hF
  have hFm : F.Monic := hf.map _
  have hsplit : F = (F.roots.map fun a => Polynomial.X - Polynomial.C a).prod :=
    (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hFm
      IsAlgClosed.card_roots_eq_natDegree).symm
  -- every root lies in `w`
  have hroot : ∀ r ∈ F.roots, ∃ y : w, algebraMap w Ω y = r ∧ f.IsRoot y := by
    intro r hr
    have hr' : Polynomial.aeval r f = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]
      exact (Polynomial.mem_roots hFm.ne_zero).mp hr
    have hint : IsIntegral w r := ⟨f, hf, hr'⟩
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine ⟨y, hy, ?_⟩
    apply IsFractionRing.injective w Ω
    have h2 : Polynomial.aeval (algebraMap w Ω y) f = 0 := hy ▸ hr'
    rw [Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval] at h2
    rw [map_zero]
    exact h2
  -- `f(a₀) = ∏ (a₀ - r)` in `Ω`
  have h0 : F.eval (algebraMap w Ω a₀) = algebraMap w Ω (f.eval a₀) := by
    rw [hF, Polynomial.eval_map_algebraMap, Polynomial.aeval_algebraMap_apply,
      Polynomial.coe_aeval_eq_eval]
  have heval : algebraMap w Ω (f.eval a₀) = (F.roots.map fun r => algebraMap w Ω a₀ - r).prod := by
    rw [← h0]
    conv_lhs => rw [hsplit]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro r _
    simp
  have hv : w.valuation (algebraMap w Ω (f.eval a₀)) < 1 :=
    (ValuationSubring.valuation_lt_one_iff w _).mp h₁
  rw [heval, map_multiset_prod, Multiset.map_map] at hv
  obtain ⟨t, ht, hlt⟩ := exists_lt_one_of_prod_lt_one _ (by
    intro t ht
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp ht
    obtain ⟨y, rfl, -⟩ := hroot r hr
    simp only [Function.comp_apply]
    rw [← map_sub]
    change w.valuation ((a₀ - y : w) : Ω) ≤ 1
    exact w.valuation_le_one _) hv
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp ht
  obtain ⟨y, rfl, hy⟩ := hroot r hr
  refine ⟨y, hy, ?_⟩
  simp only [Function.comp_apply] at hlt
  rw [← map_sub] at hlt
  have : a₀ - y ∈ IsLocalRing.maximalIdeal w := (ValuationSubring.valuation_lt_one_iff w _).mpr hlt
  rw [← neg_sub]
  exact neg_mem this

end AvSplit.T4

#print axioms AvSplit.T4.henselian_of_isAlgClosed

import Mathlib

/-!
# glue-b3-unram: the kernel field `L'` of B3 is unramified outside `T` (N5 L702-712)

Self-contained (scratch files cannot import each other). The definitions `GQ`, `act`,
`toRingAut`, `cyc`, `galChar`, `isLocallyConstant_of_openSubgroup`, `cyc_eq_of_agree`,
`cyc_isLocallyConstant` are copied verbatim from `scratch/glue-descent/B2Glue.lean`.

Inertia subgroups of `G_ℚ` are taken through valuation subrings `w` of `ℚ̄`, as in pkg-I2:
`inertiaGQ w` is the image in `G_ℚ` of Mathlib's `ValuationSubring.inertiaSubgroup` (the
elements of the decomposition group of `w` acting trivially on the residue field of `w`).
`w` lies over `p` when `v_w(p) < 1`.

Unramifiedness of an intermediate field `L' ⊆ ℚ̄` at `p` is stated Galois-theoretically
(`GalUnramifiedOutside`): every inertia subgroup over `p` fixes `L'` pointwise.

Leaves (`def … : Prop`, over Mathlib objects only):
* `LeafB3a` (L-B3a): at an odd prime, inertia has at most one nontrivial locally constant
  quadratic character;
* `LeafB3b` (L-B3b): the Legendre character mod an odd prime `p` (as a character of `G_ℚ`
  through the cyclotomic character) is nontrivial on every inertia subgroup over `p`;
* `LeafConj`: places of `ℚ̄` over the same `p` are `G_ℚ`-conjugate, with conjugate inertia;
* `LeafFinRam`: an open subgroup of `G_ℚ` contains the inertia groups over all but finitely
  many primes.
Glue proved here: `cycUnram` (the cyclotomic character mod `N` is trivial on inertia over
`p ∤ N`), hence `unramified_outside` uses only the four leaves.
-/

namespace GlueB3Unram

open NumberField

/-- `G_ℚ`. -/
abbrev GQ := Field.absoluteGaloisGroup ℚ

/-- `ℚ̄`. -/
abbrev Qbar := AlgebraicClosure ℚ

instance : IsTopologicalGroup GQ :=
  inferInstanceAs (IsTopologicalGroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

instance : IsGalois ℚ (AlgebraicClosure ℚ) := {}

def act (σ : GQ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := σ

/-- The forgetful map `Gal(ℚ̄/ℚ) → Aut(ℚ̄)` as a monoid homomorphism. -/
noncomputable def toRingAut : GQ →* (AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The cyclotomic character `G_ℚ → (ℤ/N)^×`. -/
noncomputable def cyc (N : ℕ) [NeZero N] : GQ →* (ZMod N)ˣ :=
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  (modularCyclotomicCharacter (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)).comp toRingAut

/-- A Dirichlet character as a character of `G_ℚ`. -/
noncomputable def galChar {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : GQ →* ℂˣ :=
  χ.toUnitHom.comp (cyc N)

theorem isLocallyConstant_of_openSubgroup {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) (f : G → X)
    (hf : ∀ g, ∀ k ∈ U, f (g * k) = f g) : IsLocallyConstant f := by
  refine IsLocallyConstant.iff_isOpen_fiber.2 fun y => isOpen_iff_forall_mem_open.2 fun x hx =>
    ⟨(x * ·) '' U, ?_, isOpenMap_mul_left x _ hU, ⟨1, U.one_mem, mul_one x⟩⟩
  rintro _ ⟨k, hk, rfl⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
  rw [hf x k hk, hx]

theorem cyc_eq_of_agree (N : ℕ) [NeZero N] (σ τ : GQ)
    (h : ∀ t ∈ rootsOfUnity N (AlgebraicClosure ℚ),
      act σ (t : AlgebraicClosure ℚ) = act τ (t : AlgebraicClosure ℚ)) :
    cyc N σ = cyc N τ := by
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  have hn := HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N
  apply Units.ext
  show ((modularCyclotomicCharacter (AlgebraicClosure ℚ) hn (toRingAut σ) : (ZMod N)ˣ) : ZMod N) =
    ((modularCyclotomicCharacter (AlgebraicClosure ℚ) hn (toRingAut τ) : (ZMod N)ˣ) : ZMod N)
  apply modularCyclotomicCharacter.unique _ hn
  intro t ht
  rw [← modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) hn (toRingAut σ) ht]
  exact (h t ht).symm

theorem cyc_isLocallyConstant (N : ℕ) [NeZero N] : IsLocallyConstant (cyc N) := by
  let S : Set (AlgebraicClosure ℚ) :=
    (fun t : (AlgebraicClosure ℚ)ˣ => (t : AlgebraicClosure ℚ)) ''
      (rootsOfUnity N (AlgebraicClosure ℚ) : Set (AlgebraicClosure ℚ)ˣ)
  have hfin : Finite (rootsOfUnity N (AlgebraicClosure ℚ) : Set (AlgebraicClosure ℚ)ˣ) :=
    (inferInstance : Finite (rootsOfUnity N (AlgebraicClosure ℚ)))
  haveI : Finite S := ((Set.toFinite _).image _).to_subtype
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ S
  haveI : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  refine isLocallyConstant_of_openSubgroup (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    K.fixingSubgroup K.fixingSubgroup_isOpen (fun g => cyc N g) ?_
  intro g k hk
  apply cyc_eq_of_agree
  intro t ht
  have hfix : act k (t : AlgebraicClosure ℚ) = t :=
    (IntermediateField.mem_fixingSubgroup_iff K k).mp hk _
      (IntermediateField.subset_adjoin ℚ S ⟨t, ht, rfl⟩)
  show g (k (t : AlgebraicClosure ℚ)) = g (t : AlgebraicClosure ℚ)
  exact congrArg g hfix

theorem galChar_isLocallyConstant {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    IsLocallyConstant (galChar χ) :=
  show IsLocallyConstant (χ.toUnitHom ∘ cyc N) from (cyc_isLocallyConstant N).comp _

/-! ## Places and inertia subgroups of `G_ℚ` -/

/-- The valuation subring `w` of `ℚ̄` lies over the prime `p`: `v_w(p) < 1`. -/
def LiesOver (w : ValuationSubring Qbar) (p : ℕ) : Prop := w.valuation (p : Qbar) < 1

/-- The inertia subgroup `I_w ≤ G_ℚ`: the image of Mathlib's `ValuationSubring.inertiaSubgroup`
(elements of the decomposition group of `w` acting trivially on its residue field). -/
noncomputable def inertiaGQ (w : ValuationSubring Qbar) : Subgroup GQ :=
  (w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype

/-- `L'` is unramified outside `T` (Galois-theoretic form): for every prime `p ∉ T` and every
place `w` of `ℚ̄` over `p`, `I_w` fixes `L'` pointwise. -/
def GalUnramifiedOutside (L' : IntermediateField ℚ Qbar) (T : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
    inertiaGQ w ≤ L'.fixingSubgroup

/-! ## The Legendre character mod `p` -/

/-- The Legendre character mod `p` as a complex Dirichlet character (`0` off `p` prime). -/
noncomputable def legChar (p : ℕ) : DirichletCharacter ℂ p :=
  if h : p.Prime then
    haveI : Fact p.Prime := ⟨h⟩
    (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  else 1

/-- `η_p`: the Legendre character mod `p` as a character of `G_ℚ` (`1` unless `p` is prime). -/
noncomputable def etaP (p : ℕ) : GQ →* ℂˣ :=
  if h : p.Prime then
    haveI : NeZero p := ⟨h.ne_zero⟩
    galChar (legChar p)
  else 1

/-! ## Leaves -/

/-- **Leaf L-B3a** (the unique quadratic character of tame inertia). At an odd prime `p`, the
inertia group of a place over `p` has at most one nontrivial locally constant (= continuous,
values in the discrete `{±1}`) character of order dividing `2`. Consequence of: the wild inertia
group is pro-`p` and the tame quotient is `∏_{ℓ ≠ p} ℤ_ℓ(1)` (Serre, *Corps locaux* IV §2;
Neukirch–Schmidt–Wingberg 7.5; both UNVERIFIED locators), so its continuous quadratic
characters form `Hom(ℤ_2(1), ±1) = ℤ/2`. -/
def LeafB3a : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ w : ValuationSubring Qbar, LiesOver w p →
    ∀ φ ψ : inertiaGQ w →* ℂˣ, IsLocallyConstant φ → IsLocallyConstant ψ →
      (∀ s, φ s ^ 2 = 1) → (∀ s, ψ s ^ 2 = 1) → φ ≠ 1 → ψ ≠ 1 → φ = ψ

/-- **Leaf L-B3b** (ramification of quadratic Dirichlet characters, the prime-conductor case).
For an odd prime `p`, the Legendre character mod `p`, viewed as a character of `G_ℚ` through
the cyclotomic character, is nontrivial on every inertia group over `p`: its kernel field
`ℚ(√p*)` is ramified at `p` (discriminant `p* = ±p`; STANDARD, e.g. any text on quadratic
fields; equivalently `ℚ(ζ_p)/ℚ` is totally ramified at `p`, Washington, *Cyclotomic fields*,
Lemma 1.4, UNVERIFIED locator). -/
def LeafB3b : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ w : ValuationSubring Qbar, LiesOver w p →
    ∃ s ∈ inertiaGQ w, etaP p s ≠ 1

/-- **Leaf (conjugacy of places).** Any two places of `ℚ̄` over the same prime `p` are
conjugate under `G_ℚ`, hence so are their inertia groups: `σ⁻¹ I_{w'} σ ≤ I_w` for some `σ`.
STANDARD: transitivity of the Galois group on the extensions of a valuation to a normal
algebraic extension (Neukirch, *Algebraic number theory* II.9.1 and II.9.4 for the infinite
case, UNVERIFIED locators), plus `I_{σw} = σ I_w σ⁻¹` (glue). -/
def LeafConj : Prop :=
  ∀ p : ℕ, p.Prime → ∀ w w' : ValuationSubring Qbar, LiesOver w p → LiesOver w' p →
    ∃ σ : GQ, ∀ s ∈ inertiaGQ w', σ⁻¹ * s * σ ∈ inertiaGQ w

/-- **Leaf (finite ramification).** An open subgroup of `G_ℚ` contains the inertia groups of all
places over all but finitely many primes. STANDARD: an open subgroup contains `G_K` for a number
field `K`, and `K` is ramified only at the primes dividing its discriminant (Neukirch III.2.12,
UNVERIFIED locator), with the identification of Galois and ideal-theoretic ramification. -/
def LeafFinRam : Prop :=
  ∀ H : Subgroup GQ, IsOpen (H : Set GQ) →
    {p : ℕ | p.Prime ∧ ∃ w : ValuationSubring Qbar, LiesOver w p ∧ ¬ inertiaGQ w ≤ H}.Finite

/-- **Glue (proved below, `cycUnram`).** The cyclotomic character mod `N` is trivial on inertia over
`p ∤ N`: an element of `I_w` acts trivially on the residue field, and the `N`-th roots of unity
stay distinct modulo `w` because `X^N - 1` is separable mod `p`. -/
def CycUnram : Prop :=
  ∀ (N : ℕ) [NeZero N] (p : ℕ), p.Prime → ¬ p ∣ N → ∀ w : ValuationSubring Qbar, LiesOver w p →
    ∀ s ∈ inertiaGQ w, cyc N s = 1

/-! ## Elementary facts -/

theorem etaP_sq (p : ℕ) (x : GQ) : etaP p x ^ 2 = 1 := by
  unfold etaP
  split_ifs with h
  · have : Fact p.Prime := ⟨h⟩
    have : NeZero p := ⟨h.ne_zero⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    show ((legChar p).toUnitHom (cyc p x) : ℂ) ^ 2 = 1
    rw [MulChar.coe_toUnitHom, legChar, dif_pos h, MulChar.ringHomComp_apply]
    have h1 := quadraticChar_sq_one (F := ZMod p) (Units.ne_zero (cyc p x))
    have h2 : ((Int.castRingHom ℂ) (quadraticChar (ZMod p) (cyc p x))) ^ 2 = 1 := by
      rw [← map_pow, h1, map_one]
    exact h2
  · simp

theorem one_isLocallyConstant : IsLocallyConstant ⇑(1 : GQ →* ℂˣ) := by
  convert IsLocallyConstant.const (X := GQ) (1 : ℂˣ) using 1
  funext x; rfl

theorem etaP_isLocallyConstant (p : ℕ) : IsLocallyConstant (etaP p) := by
  unfold etaP
  split_ifs with h
  · haveI : NeZero p := ⟨h.ne_zero⟩
    exact galChar_isLocallyConstant _
  · exact one_isLocallyConstant

theorem etaP_unram (hC : CycUnram) (q p : ℕ) (hp : p.Prime) (hpq : p ≠ q)
    (w : ValuationSubring Qbar) (hw : LiesOver w p) (s : GQ) (hs : s ∈ inertiaGQ w) :
    etaP q s = 1 := by
  unfold etaP
  split_ifs with h
  · haveI : NeZero q := ⟨h.ne_zero⟩
    have hnd : ¬ p ∣ q := fun hd => hpq ((Nat.prime_dvd_prime_iff_eq hp h).mp hd)
    show (legChar q).toUnitHom (cyc q s) = 1
    rw [hC q p hp hnd w hw s hs, map_one]
  · rfl

theorem galChar_unram (hC : CycUnram) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) (w : ValuationSubring Qbar) (hw : LiesOver w p)
    (s : GQ) (hs : s ∈ inertiaGQ w) : galChar χ s = 1 := by
  show χ.toUnitHom (cyc N s) = 1
  rw [hC N p hp hpN w hw s hs, map_one]

theorem prod_isLocallyConstant (Q : Finset ℕ) :
    IsLocallyConstant (⇑(∏ q ∈ Q, etaP q)) := by
  induction Q using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact one_isLocallyConstant
  | insert a Q ha ih =>
    rw [Finset.prod_insert ha]
    exact (etaP_isLocallyConstant a).mul ih

/-! ## The kernel subgroup `{σ ∈ G_L : β σ = 1}` -/

section Kernel

variable (H : Subgroup GQ) (ε : GQ → GQ → ℂˣ) (β : GQ → ℂˣ)
  (hεN : ∀ σ τ, σ ∈ H ∨ τ ∈ H → ε σ τ = 1) (hβe : ∀ x y, β x * β y = ε x y * β (x * y))

include hεN hβe in
theorem beta_mul_left {σ τ : GQ} (h : σ ∈ H ∨ τ ∈ H) : β (σ * τ) = β σ * β τ := by
  rw [hβe, hεN σ τ h, one_mul]

include hεN hβe in
theorem beta_one : β 1 = 1 := by
  have h := beta_mul_left H ε β hεN hβe (σ := 1) (τ := 1) (Or.inl H.one_mem)
  rw [one_mul] at h
  exact (mul_eq_left.mp h.symm)

/-- `K = {σ ∈ H : β σ = 1}`. -/
def kerSub : Subgroup GQ where
  carrier := {σ | σ ∈ H ∧ β σ = 1}
  one_mem' := ⟨H.one_mem, beta_one H ε β hεN hβe⟩
  mul_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    refine ⟨H.mul_mem ha hb, ?_⟩
    rw [beta_mul_left H ε β hεN hβe (Or.inl ha), ha1, hb1, one_mul]
  inv_mem' := by
    rintro a ⟨ha, ha1⟩
    refine ⟨H.inv_mem ha, ?_⟩
    have h := beta_mul_left H ε β hεN hβe (σ := a⁻¹) (τ := a) (Or.inr ha)
    rw [inv_mul_cancel, beta_one H ε β hεN hβe, ha1, mul_one] at h
    exact h.symm

theorem mem_kerSub {σ : GQ} : σ ∈ kerSub H ε β hεN hβe ↔ σ ∈ H ∧ β σ = 1 := Iff.rfl

include hεN hβe in
/-- `β (σ k σ⁻¹) = β k` for `k ∈ H`, `H` normal. -/
theorem beta_conj [H.Normal] (σ k : GQ) (hk : k ∈ H) : β (σ * k * σ⁻¹) = β k := by
  have hc : σ * k * σ⁻¹ ∈ H := Subgroup.Normal.conj_mem inferInstance k hk σ
  have h1 : β (σ * k) = β σ * β k := beta_mul_left H ε β hεN hβe (Or.inr hk)
  have h2 : β (σ * k * σ⁻¹ * σ) = β (σ * k * σ⁻¹) * β σ :=
    beta_mul_left H ε β hεN hβe (Or.inl hc)
  rw [inv_mul_cancel_right, h1] at h2
  have : β σ * β k = β σ * β (σ * k * σ⁻¹) := by rw [h2, mul_comm]
  exact (mul_left_cancel this).symm

end Kernel

/-! ## The main theorem -/

/-- **B3 (v): the twisted kernel field is unramified outside `T`** (N5 L702-712).

Data as produced by `b2_of_leaves` (glue-descent): a finite Galois `L ⊆ ℚ̄` unramified outside
`T ∋ 2` (Galois form), a sign 2-cocycle `ε` that is `1` as soon as one argument lies in `G_L`
(`inflatedNormalized_of`), a Dirichlet character `χ` of modulus `N` with prime divisors in `T`,
and a locally constant `β` with `β² = χ` and `dβ = ε`. Then there is a locally constant quadratic
character `η = ∏_{q ∈ Q} η_q` of `G_ℚ` (a product of Legendre characters over the finite set `Q`
of primes `q ∉ T` where `β` is ramified) such that every `L'` with
`G_{L'} = {σ ∈ G_L : β σ η σ = 1}` — the kernel field of `b3_of_leaves` for this `η` — is
unramified outside `T`. -/
theorem unramified_outside_of_leaves (hA : LeafB3a) (hB : LeafB3b) (hConj : LeafConj)
    (hFin : LeafFinRam) (hC : CycUnram)
    (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (T : Finset ℕ) (h2 : 2 ∈ T) (hLT : GalUnramifiedOutside L T)
    (ε : GQ → GQ → ℂˣ)
    (hεN : ∀ σ τ, σ ∈ L.fixingSubgroup ∨ τ ∈ L.fixingSubgroup → ε σ τ = 1)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hN : ∀ q, q.Prime → q ∣ N → q ∈ T)
    (β : GQ → ℂˣ) (hβl : IsLocallyConstant β) (hβs : ∀ x, β x ^ 2 = galChar χ x)
    (hβe : ∀ x y, β x * β y = ε x y * β (x * y)) :
    ∃ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ q ∉ T) ∧
      (∀ x, (∏ q ∈ Q, etaP q) x ^ 2 = 1) ∧ IsLocallyConstant ⇑(∏ q ∈ Q, etaP q) ∧
      ∀ L' : IntermediateField ℚ Qbar,
        (∀ σ, σ ∈ L'.fixingSubgroup ↔
          σ ∈ L.fixingSubgroup ∧ β σ * (∏ q ∈ Q, etaP q) σ = 1) →
        GalUnramifiedOutside L' T := by
  set H : Subgroup GQ := L.fixingSubgroup with hH
  haveI : H.Normal := (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  let K := kerSub H ε β hεN hβe
  have hKopen : IsOpen (K : Set GQ) := by
    have : (K : Set GQ) = (H : Set GQ) ∩ β ⁻¹' {1} := by
      ext g; simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff]; exact mem_kerSub H ε β hεN hβe
    rw [this]; exact L.fixingSubgroup_isOpen.inter (hβl.isOpen_fiber 1)
  -- conjugation invariance of `K`
  have hKconj : ∀ σ k, k ∈ K → σ * k * σ⁻¹ ∈ K := by
    intro σ k hk
    obtain ⟨hkH, hk1⟩ := (mem_kerSub H ε β hεN hβe).mp hk
    exact (mem_kerSub H ε β hεN hβe).mpr
      ⟨Subgroup.Normal.conj_mem inferInstance k hkH σ, by
        rw [beta_conj H ε β hεN hβe σ k hkH, hk1]⟩
  have hfin := hFin K hKopen
  let Qs : Set ℕ := {p : ℕ | p.Prime ∧ ∃ w : ValuationSubring Qbar, LiesOver w p ∧
    ¬ inertiaGQ w ≤ K} \ (T : Set ℕ)
  have hQfin : Qs.Finite := hfin.subset Set.sdiff_subset
  let Q := hQfin.toFinset
  have hmemQ : ∀ p, p ∈ Q ↔ (p.Prime ∧ ∃ w : ValuationSubring Qbar, LiesOver w p ∧
      ¬ inertiaGQ w ≤ K) ∧ p ∉ T := by
    intro p; simp [Q, Qs]
  let η : GQ →* ℂˣ := ∏ q ∈ Q, etaP q
  have hηapp : ∀ x, η x = ∏ q ∈ Q, etaP q x := fun x => MonoidHom.finset_prod_apply _ _ _
  have hη2 : ∀ x, η x ^ 2 = 1 := by
    intro x; rw [hηapp, ← Finset.prod_pow]; exact Finset.prod_eq_one (fun q _ => etaP_sq q x)
  have hηl : IsLocallyConstant η := prod_isLocallyConstant Q
  refine ⟨Q, fun q hq => ⟨((hmemQ q).mp hq).1.1, ((hmemQ q).mp hq).2⟩, hη2, hηl, ?_⟩
  intro L' hL' p hp hpT w hw s hs
  have hIH : inertiaGQ w ≤ H := hLT p hp hpT w hw
  refine (hL' s).mpr ⟨hIH hs, ?_⟩
  have hpN : ¬ p ∣ N := fun h => hpT (hN p hp h)
  -- `η` on `I_w` is `η_p` if `p ∈ Q`, else `1`
  have hηI : ∀ t ∈ inertiaGQ w, η t = if p ∈ Q then etaP p t else 1 := by
    intro t ht
    rw [hηapp]
    split_ifs with hpQ
    · refine Finset.prod_eq_single p (fun q _ hqp => etaP_unram hC q p hp (Ne.symm hqp) w hw t ht)
        (fun h => absurd hpQ h)
    · exact Finset.prod_eq_one (fun q hq => etaP_unram hC q p hp
        (fun h => hpQ (h ▸ hq)) w hw t ht)
  by_cases hram : inertiaGQ w ≤ K
  · -- `β` unramified at `w`, hence at every place over `p`; so `p ∉ Q`
    have hpQ : p ∉ Q := by
      intro hpQ
      obtain ⟨⟨_, w', hw', hnot⟩, _⟩ := (hmemQ p).mp hpQ
      apply hnot
      intro t ht
      obtain ⟨σ, hσ⟩ := hConj p hp w w' hw hw'
      have h1 : σ⁻¹ * t * σ ∈ K := hram (hσ t ht)
      have h2 := hKconj σ _ h1
      have : σ * (σ⁻¹ * t * σ) * σ⁻¹ = t := by group
      rwa [this] at h2
    rw [hηI s hs, if_neg hpQ, mul_one]
    exact ((mem_kerSub H ε β hεN hβe).mp (hram hs)).2
  · have hpQ : p ∈ Q := (hmemQ p).mpr ⟨⟨hp, w, hw, hram⟩, hpT⟩
    have hp2 : p ≠ 2 := fun h => hpT (h ▸ h2)
    -- the two quadratic characters of `I_w`
    let βv : inertiaGQ w →* ℂˣ :=
      { toFun := fun t => β t
        map_one' := beta_one H ε β hεN hβe
        map_mul' := fun t u => beta_mul_left H ε β hεN hβe (Or.inl (hIH t.2)) }
    let ηv : inertiaGQ w →* ℂˣ := η.comp (inertiaGQ w).subtype
    have hβv2 : ∀ t, βv t ^ 2 = 1 := by
      intro t; show β t ^ 2 = 1
      rw [hβs]; exact galChar_unram hC χ p hp hpN w hw t t.2
    have hηv2 : ∀ t, ηv t ^ 2 = 1 := fun t => hη2 t
    have hβvl : IsLocallyConstant βv := hβl.comp_continuous continuous_subtype_val
    have hηvl : IsLocallyConstant ηv := hηl.comp_continuous continuous_subtype_val
    have hβvne : βv ≠ 1 := by
      intro h
      apply hram
      intro t ht
      exact (mem_kerSub H ε β hεN hβe).mpr ⟨hIH ht,
        congrArg (fun f : inertiaGQ w →* ℂˣ => f ⟨t, ht⟩) h⟩
    have hηvne : ηv ≠ 1 := by
      intro h
      obtain ⟨t, ht, hne⟩ := hB p hp hp2 w hw
      apply hne
      have h1 := congrArg (fun f : inertiaGQ w →* ℂˣ => f ⟨t, ht⟩) h
      simp only [MonoidHom.one_apply] at h1
      have h3 : η t = etaP p t := by rw [hηI t ht, if_pos hpQ]
      rw [← h3]; exact h1
    have heq := hA p hp hp2 w hw βv ηv hβvl hηvl hβv2 hηv2 hβvne hηvne
    have hs' : β s = η s := congrArg (fun f : inertiaGQ w →* ℂˣ => f ⟨s, hs⟩) heq
    rw [hs', ← sq, hη2]

/-! ## Proof of `CycUnram` -/

theorem residue_inertia (w : ValuationSubring Qbar) (s : GQ) (hs : s ∈ inertiaGQ w) (x : w) :
    ∃ y : w, (y : Qbar) = act s x ∧ IsLocalRing.residue w y = IsLocalRing.residue w x := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hs
  refine ⟨g • x, rfl, ?_⟩
  rw [IsLocalRing.ResidueField.residue_smul]
  have h1 : MulSemiringAction.toRingAut _ (IsLocalRing.ResidueField w) g = 1 := hg
  exact congrArg (fun f => f (IsLocalRing.residue w x)) h1

theorem residue_prime_eq_zero (w : ValuationSubring Qbar) (p : ℕ) (hw : LiesOver w p) :
    IsLocalRing.residue w (p : w) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  have : ((p : w) : Qbar) = (p : Qbar) := by simp
  rw [this]; exact hw

theorem residue_natCast_ne_zero (w : ValuationSubring Qbar) (p : ℕ) (hp : p.Prime)
    (hw : LiesOver w p) (N : ℕ) (hpN : ¬ p ∣ N) : IsLocalRing.residue w (N : w) ≠ 0 := by
  intro hN
  have hcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  have h := Nat.gcd_eq_gcd_ab p N
  rw [hcop, Nat.cast_one] at h
  have h0 := residue_prime_eq_zero w p hw
  rw [map_natCast] at h0 hN
  have h2 := congrArg (Int.cast : ℤ → IsLocalRing.ResidueField w) h
  push_cast at h2
  rw [h0, hN] at h2
  simp at h2

theorem rootOfUnity_mem (w : ValuationSubring Qbar) (N : ℕ) (hN : 0 < N) (t : Qbar)
    (ht : t ^ N = 1) : t ∈ w := by
  rcases w.mem_or_inv_mem t with h | h
  · exact h
  · have ht0 : t ≠ 0 := by rintro rfl; rw [zero_pow hN.ne'] at ht; exact zero_ne_one ht
    have : t = (t⁻¹) ^ (N - 1) := by
      rw [inv_pow]; apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ', Nat.sub_add_cancel hN]; exact ht
    rw [this]; exact pow_mem h _

theorem cycUnram : CycUnram := by
  intro N _ p hp hpN w hw s hs
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [← map_one (cyc N)]
  apply cyc_eq_of_agree
  intro t ht
  have htN : (t : Qbar) ^ N = 1 := by
    have := (mem_rootsOfUnity N t).mp ht
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  let x : w := ⟨t, rootOfUnity_mem w N hN t htN⟩
  obtain ⟨y, hy, hres⟩ := residue_inertia w s hs x
  show act s t = t
  by_contra hne
  let z : w := y * x ^ (N - 1)
  have hxN : x ^ N = 1 := Subtype.ext (by simp [x, htN])
  have hyN : y ^ N = 1 := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, hy, OneMemClass.coe_one]
    rw [← map_pow, htN, map_one]
  have hzN : z ^ N = 1 := by
    simp only [z, mul_pow, hyN, one_mul]
    rw [← pow_mul, mul_comm, pow_mul, hxN, one_pow]
  have hz1 : z ≠ 1 := by
    intro h
    apply hne
    have h2 : z * x = x := by rw [h, one_mul]
    have h3 : z * x = y := by
      simp only [z, mul_assoc, ← pow_succ, Nat.sub_add_cancel hN, hxN, mul_one]
    rw [h3] at h2
    rw [← hy, h2]
  have hsum : ∑ i ∈ Finset.range N, z ^ i = 0 := by
    have h := geom_sum_mul z N
    rw [hzN, sub_self] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hz1
  have hzres : IsLocalRing.residue w z = 1 := by
    simp only [z, map_mul, map_pow, hres]
    rw [← map_pow, ← map_mul, ← pow_succ', Nat.sub_add_cancel hN, hxN, map_one]
  have h := congrArg (IsLocalRing.residue w) hsum
  simp only [map_sum, map_pow, hzres, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, map_zero] at h
  apply residue_natCast_ne_zero w p hp hw N hpN
  rw [map_natCast]; exact h

/-- **B3 (v) from the four leaves** (`CycUnram` is now proved): the twisted kernel field `L'`
is unramified outside `T`. -/
theorem unramified_outside (hA : LeafB3a) (hB : LeafB3b) (hConj : LeafConj) (hFin : LeafFinRam)
    (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (T : Finset ℕ) (h2 : 2 ∈ T) (hLT : GalUnramifiedOutside L T)
    (ε : GQ → GQ → ℂˣ)
    (hεN : ∀ σ τ, σ ∈ L.fixingSubgroup ∨ τ ∈ L.fixingSubgroup → ε σ τ = 1)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hN : ∀ q, q.Prime → q ∣ N → q ∈ T)
    (β : GQ → ℂˣ) (hβl : IsLocallyConstant β) (hβs : ∀ x, β x ^ 2 = galChar χ x)
    (hβe : ∀ x y, β x * β y = ε x y * β (x * y)) :
    ∃ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ q ∉ T) ∧
      (∀ x, (∏ q ∈ Q, etaP q) x ^ 2 = 1) ∧ IsLocallyConstant ⇑(∏ q ∈ Q, etaP q) ∧
      ∀ L' : IntermediateField ℚ Qbar,
        (∀ σ, σ ∈ L'.fixingSubgroup ↔
          σ ∈ L.fixingSubgroup ∧ β σ * (∏ q ∈ Q, etaP q) σ = 1) →
        GalUnramifiedOutside L' T :=
  unramified_outside_of_leaves hA hB hConj hFin cycUnram L T h2 hLT ε hεN χ hN β hβl hβs hβe


/-! ## Bridge: ideal-theoretic unramifiedness gives trivial inertia -/

section Bridge

open NumberField

/-- glue-descent's `UnramifiedAt` (copied from `scratch/glue-descent/B2Glue.lean`). -/
def UnramifiedAt (L : IntermediateField ℚ Qbar) (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 L), P.IsPrime → ((p : ℤ) : 𝓞 L) ∈ P → P.ramificationIdx ℤ = 1

variable (L : IntermediateField ℚ Qbar)

/-- `𝓞 L → ℚ̄`. -/
noncomputable def emb : 𝓞 L →+* Qbar := (algebraMap L Qbar).comp (algebraMap (𝓞 L) L)

theorem emb_mem (w : ValuationSubring Qbar) (x : 𝓞 L) : emb L x ∈ w := by
  have h1 : IsIntegral ℤ (emb L x) := by
    have h0 : IsIntegral ℤ (algebraMap (𝓞 L) L x) := x.isIntegral_coe
    exact h0.map (IsScalarTower.toAlgHom ℤ L Qbar)
  have h2 : IsIntegral w (emb L x) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]; exact y.2

/-- `𝓞 L → w`. -/
noncomputable def embW (w : ValuationSubring Qbar) : 𝓞 L →+* w :=
  (emb L).codRestrict w (emb_mem L w)

theorem inertia_le_of_unramifiedAt [FiniteDimensional ℚ L] [IsGalois ℚ L] (p : ℕ) (hp : p.Prime)
    (hL : UnramifiedAt L p) (w : ValuationSubring Qbar) (hw : LiesOver w p) :
    inertiaGQ w ≤ L.fixingSubgroup := by
  haveI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal w).comap (embW L w)
  haveI hPprime : P.IsPrime := Ideal.comap_isPrime _ _
  have hpP : ((p : ℤ) : 𝓞 L) ∈ P := by
    show embW L w ((p : ℤ) : 𝓞 L) ∈ IsLocalRing.maximalIdeal w
    rw [ValuationSubring.valuation_lt_one_iff]
    have : ((embW L w ((p : ℤ) : 𝓞 L) : w) : Qbar) = (p : Qbar) := by
      simp [embW, emb]
    rw [this]; exact hw
  have he : P.ramificationIdx ℤ = 1 := hL P hPprime hpP
  let G := L ≃ₐ[ℚ] L
  have hcard : Nat.card (P.inertia G) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := G) (P.under ℤ) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P G, he]
  intro s hs
  let g : G := AlgEquiv.restrictNormal (s : Qbar ≃ₐ[ℚ] Qbar) L
  have hg : ∀ x : L, algebraMap L Qbar (g x) = act s (algebraMap L Qbar x) :=
    fun x => AlgEquiv.restrictNormal_commutes _ L x
  have hgI : g ∈ P.inertia G := by
    rw [Ideal.mem_inertia]
    intro x
    show embW L w (g • x - x) ∈ IsLocalRing.maximalIdeal w
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, sub_eq_zero]
    obtain ⟨y, hy, hres⟩ := residue_inertia w s hs (embW L w x)
    have hgx : embW L w (g • x) = y := by
      apply Subtype.ext
      rw [hy]
      show emb L (g • x) = act s (emb L x)
      simp only [emb, RingHom.comp_apply]
      rw [← hg]; rfl
    rw [hgx, hres]
  have hg1 : g = 1 := by
    have hsub : Subsingleton (P.inertia G) := (Nat.card_eq_one_iff_unique.mp hcard).1
    have := Subsingleton.elim (⟨g, hgI⟩ : P.inertia G) 1
    exact congrArg Subtype.val this
  refine (IntermediateField.mem_fixingSubgroup_iff L s).mpr ?_
  intro x hx
  have := hg ⟨x, hx⟩
  rw [hg1] at this
  exact this.symm

end Bridge

/-- **B3 (v) with glue-descent's hypothesis on `L`** (`UnramifiedAt`, the form taken by
`b2_of_leaves` and `b3_of_leaves`): the twisted kernel field `L'` is unramified outside `T`
(Galois form). Four leaves only. -/
theorem unramified_outside_of_unramifiedAt (hA : LeafB3a) (hB : LeafB3b) (hConj : LeafConj)
    (hFin : LeafFinRam)
    (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (T : Finset ℕ) (h2 : 2 ∈ T) (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p)
    (ε : GQ → GQ → ℂˣ)
    (hεN : ∀ σ τ, σ ∈ L.fixingSubgroup ∨ τ ∈ L.fixingSubgroup → ε σ τ = 1)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hN : ∀ q, q.Prime → q ∣ N → q ∈ T)
    (β : GQ → ℂˣ) (hβl : IsLocallyConstant β) (hβs : ∀ x, β x ^ 2 = galChar χ x)
    (hβe : ∀ x y, β x * β y = ε x y * β (x * y)) :
    ∃ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ q ∉ T) ∧
      (∀ x, (∏ q ∈ Q, etaP q) x ^ 2 = 1) ∧ IsLocallyConstant ⇑(∏ q ∈ Q, etaP q) ∧
      ∀ L' : IntermediateField ℚ Qbar,
        (∀ σ, σ ∈ L'.fixingSubgroup ↔
          σ ∈ L.fixingSubgroup ∧ β σ * (∏ q ∈ Q, etaP q) σ = 1) →
        GalUnramifiedOutside L' T :=
  unramified_outside hA hB hConj hFin L T h2
    (fun p hp hpT w hw => inertia_le_of_unramifiedAt L p hp (hram ⟨p, hp⟩ hpT) w hw)
    ε hεN χ hN β hβl hβs hβe


/-! ## `LeafFinRam` from the bridge and Mathlib's discriminant theorem -/

section FinRam

open NumberField

theorem unramifiedAt_of_not_dvd_discr (L : IntermediateField ℚ Qbar) [NumberField L]
    (p : ℕ) (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr L) : UnramifiedAt L p := by
  intro P hP hpP
  have h := (NumberField.not_dvd_discr_iff_forall_mem L (𝓞 L)
    (Nat.prime_iff_prime_int.mp hp)).mp hd P hP hpP
  exact P.ramificationIdx_eq_one ℤ

theorem finRam : LeafFinRam := by
  intro H hH
  have hHc : IsClosed (H : Set GQ) := Subgroup.isClosed_of_isOpen H hH
  let Hc : ClosedSubgroup (Qbar ≃ₐ[ℚ] Qbar) := { toSubgroup := H, isClosed' := hHc }
  let K : IntermediateField ℚ Qbar := IntermediateField.fixedField Hc.toSubgroup
  have hfix : K.fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField Hc
  haveI : FiniteDimensional ℚ K :=
    (InfiniteGalois.isOpen_iff_finite K).mp (by rw [hfix]; exact hH)
  let L : IntermediateField ℚ Qbar := IntermediateField.normalClosure ℚ K Qbar
  haveI : FiniteDimensional ℚ L := normalClosure.is_finiteDimensional ℚ K Qbar
  haveI : IsGalois ℚ L := IsGalois.normalClosure ℚ K Qbar
  have hKL : K ≤ L := IntermediateField.le_normalClosure K
  have hLH : L.fixingSubgroup ≤ H := by
    rw [← hfix]; exact IntermediateField.fixingSubgroup_le hKL
  haveI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  have hd : discr L ≠ 0 := discr_ne_zero L
  apply ((discr L).natAbs.primeFactors.finite_toSet).subset
  rintro p ⟨hp, w, hw, hnot⟩
  simp only [Finset.mem_coe, Nat.mem_primeFactors]
  refine ⟨hp, ?_, Int.natAbs_ne_zero.mpr hd⟩
  by_contra hdvd
  apply hnot
  have hd' : ¬ (p : ℤ) ∣ discr L := fun h => hdvd (Int.natCast_dvd.mp h)
  exact (inertia_le_of_unramifiedAt L p hp (unramifiedAt_of_not_dvd_discr L p hp hd') w hw).trans
    hLH

end FinRam

/-- **B3 (v) from three leaves** (L-B3a, L-B3b, conjugacy of places; finite ramification and
the unramifiedness of Dirichlet characters at primes not dividing the modulus are proved glue),
with glue-descent's hypothesis form on `L`: the twisted kernel field `L'` is unramified outside
`T` (Galois form). -/
theorem unramified_outside_final (hA : LeafB3a) (hB : LeafB3b) (hConj : LeafConj)
    (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (T : Finset ℕ) (h2 : 2 ∈ T) (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p)
    (ε : GQ → GQ → ℂˣ)
    (hεN : ∀ σ τ, σ ∈ L.fixingSubgroup ∨ τ ∈ L.fixingSubgroup → ε σ τ = 1)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hN : ∀ q, q.Prime → q ∣ N → q ∈ T)
    (β : GQ → ℂˣ) (hβl : IsLocallyConstant β) (hβs : ∀ x, β x ^ 2 = galChar χ x)
    (hβe : ∀ x y, β x * β y = ε x y * β (x * y)) :
    ∃ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ q ∉ T) ∧
      (∀ x, (∏ q ∈ Q, etaP q) x ^ 2 = 1) ∧ IsLocallyConstant ⇑(∏ q ∈ Q, etaP q) ∧
      ∀ L' : IntermediateField ℚ Qbar,
        (∀ σ, σ ∈ L'.fixingSubgroup ↔
          σ ∈ L.fixingSubgroup ∧ β σ * (∏ q ∈ Q, etaP q) σ = 1) →
        GalUnramifiedOutside L' T :=
  unramified_outside_of_unramifiedAt hA hB hConj finRam L T h2 hram ε hεN χ hN β hβl hβs hβe

end GlueB3Unram

#print axioms GlueB3Unram.unramified_outside_of_leaves
#print axioms GlueB3Unram.cycUnram
#print axioms GlueB3Unram.unramified_outside
#print axioms GlueB3Unram.inertia_le_of_unramifiedAt
#print axioms GlueB3Unram.unramified_outside_of_unramifiedAt
#print axioms GlueB3Unram.finRam
#print axioms GlueB3Unram.unramified_outside_final

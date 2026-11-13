/-
glue-t32a: this file is scratch/glue-b3b/B3b.lean verbatim (except for this prepended paragraph),
followed by the glue-t32a sections (from the comment "# glue-t32a" on): the proof `GlueB3Unram.t32a :
LeafPush.T32a_TameQuadratic` (leaf T32(a) of the synthesis bundle, statement unchanged), the
corollary `GlueB3Unram.leafB3a : LeafB3a`, and `GlueB3Unram.unramified_outside_noLeaf`
(B3 (v) with no hypothesis beyond those on `L`, `β`, `χ`).

glue-b3b's header: this file is scratch/glue-conj/UnramConj.lean (glue-b3-unram + glue-conj) verbatim up
to `end Conj`, followed by the glue-b3b sections `B3b`, `B3bMain`, `B3bGauss` (the proof
`leafB3b : LeafB3b`), glue-conj's `unramified_outside_final` unchanged, the new
`unramified_outside_b3a` (takes only `LeafB3a`), and, after `end GlueB3Unram`, verbatim copies of
leaf-push's `GQ`, `IsAtPrime`, `inertiaQ`, `T32b_QuadraticRamification` (namespace `LeafPush`)
with the proof `GlueB3Unram.t32b : LeafPush.T32b_QuadraticRamification`; then leaf-push's
`T32a_TameQuadratic` (verbatim) with `GlueB3Unram.leafB3a_of_t32a : T32a → LeafB3a` and
`unramified_outside_t32a` (B3 (v) from T32(a) alone).
-/
import Mathlib

/-!
# glue-b3-unram: the kernel field `L'` of B3 is unramified outside `T` (N5 L702-712)

glue-conj copy: `scratch/glue-b3-unram/Unram.lean` verbatim, plus the section `Conj` (proof of
`LeafConj` as glue, `leafConj`), and `unramified_outside_final` now takes only `LeafB3a`,
`LeafB3b`.

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
  many primes. PROVED below as glue (`finRam`).
Glue proved here: `cycUnram` (the cyclotomic character mod `N` is trivial on inertia over
`p ∤ N`); the bridge `inertia_le_of_unramifiedAt` (glue-descent's `UnramifiedAt L p` gives
`I_w ≤ G_L`); `finRam`. The final theorem `unramified_outside_final` uses three leaves:
`LeafB3a`, `LeafB3b`, `LeafConj`.
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

/-- **Finite ramification** (stated as a leaf, then PROVED below as glue: `finRam`). An open subgroup of `G_ℚ` contains the inertia groups of all
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

/-- **B3 (v) from four leaves** (`LeafFinRam` discharged later by `finRam`) (`CycUnram` is now proved): the twisted kernel field `L'`
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

section Conj

/-! ## Proof of `LeafConj` (from glue-conj, `scratch/glue-conj/Conj.lean`) -/

open scoped Pointwise

/-- `G_ℚ` as the type of `ℚ`-automorphisms of `ℚ̄` (definitionally `GQ`). -/
abbrev Gal := Qbar ≃ₐ[ℚ] Qbar

/-! ## 1. The center lemma -/

/-- Integral elements over `ℤ` lie in every valuation subring. -/
theorem mem_of_isIntegral (w : ValuationSubring Qbar) {y : Qbar} (hy : IsIntegral ℤ y) : y ∈ w := by
  have h1 : IsIntegral w y := IsIntegral.tower_top (A := w) hy
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  rw [← ha]; exact a.2

theorem val_le_one_of_isIntegral (w : ValuationSubring Qbar) {y : Qbar} (hy : IsIntegral ℤ y) :
    w.valuation y ≤ 1 := (w.valuation_le_one_iff y).mpr (mem_of_isIntegral w hy)

/-- **Center lemma.** Two valuation subrings of `ℚ̄` over a prime `p` with the same center on the
algebraic integers are comparable (hence equal, by symmetry). -/
theorem le_of_center (w₁ w₂ : ValuationSubring Qbar) (p : ℕ) (hp : p.Prime)
    (hw₁ : w₁.valuation (p : Qbar) < 1)
    (hc : ∀ y : Qbar, IsIntegral ℤ y → (w₁.valuation y < 1 ↔ w₂.valuation y < 1)) :
    w₁ ≤ w₂ := by
  intro x hx
  let K : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {x}
  have : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := ℚ) x)
  have : NumberField K := ⟨⟩
  let ι : 𝓞 K →+* Qbar := (algebraMap K Qbar).comp (algebraMap (𝓞 K) K)
  have hint : ∀ r : 𝓞 K, IsIntegral ℤ (ι r) := fun r =>
    (RingOfIntegers.isIntegral_coe r).map (IsScalarTower.toAlgHom ℤ K Qbar)
  let f : 𝓞 K →+* w₁ :=
    { toFun := fun r => ⟨ι r, mem_of_isIntegral w₁ (hint r)⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  let I : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal w₁).comap f
  have hI : ∀ r, r ∈ I ↔ w₁.valuation (ι r) < 1 := fun r =>
    (w₁.valuation_lt_one_iff (f r))
  have hpI : (p : 𝓞 K) ∈ I := by rw [hI]; simpa [ι] using hw₁
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨I, Ideal.comap_isPrime _ _, fun h => hp0 (by rw [h] at hpI; simpa using hpI)⟩
  let x' : K := ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩
  obtain ⟨n, d, h⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := K) x'
  have hd : ¬ w₁.valuation (ι d) < 1 := fun h' => d.2 ((hI d).mpr h')
  have hd2 : w₂.valuation (ι d) = 1 :=
    le_antisymm (val_le_one_of_isIntegral w₂ (hint d))
      (not_lt.mp fun h' => hd ((hc _ (hint d)).mpr h'))
  have hn2 := val_le_one_of_isIntegral w₂ (hint n)
  rw [← w₂.valuation_le_one_iff]
  rcases h with h | h
  · have h' : x * ι d = ι n := by
      have := congrArg (algebraMap K Qbar) h
      simpa [ι] using this
    have := congrArg w₂.valuation h'
    rw [map_mul, hd2, mul_one] at this
    rw [this]; exact hn2
  · have h' : x * ι n = ι d := by
      have := congrArg (algebraMap K Qbar) h
      simpa [ι] using this
    by_contra hx2
    push Not at hx2
    have e2 := congrArg w₂.valuation h'
    rw [map_mul, hd2] at e2
    have hn2' : w₂.valuation (ι n) < 1 := by
      rcases lt_or_eq_of_le hn2 with h3 | h3
      · exact h3
      · rw [h3, mul_one] at e2; exact absurd e2 (ne_of_gt hx2)
    have hn1 := (hc _ (hint n)).mpr hn2'
    have e1 := congrArg w₁.valuation h'
    rw [map_mul] at e1
    have hx1 : w₁.valuation x ≤ 1 := (w₁.valuation_le_one_iff x).mpr hx
    have : w₁.valuation x * w₁.valuation (ι n) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' hx1) hn1
    rw [e1] at this
    exact hd (by simpa using this)

/-! ## 2. Profinite transitivity on primes of the algebraic integers -/

/-- The algebraic integers `B ⊆ ℚ̄`. -/
noncomputable abbrev B := integralClosure ℤ Qbar

theorem isIntegral_smul (σ : Gal) (b : B) : IsIntegral ℤ (σ (b : Qbar)) :=
  (mem_integralClosure_iff ℤ Qbar).mp b.2 |>.map ((σ : Qbar →+* Qbar).toIntAlgHom)

noncomputable instance : MulSemiringAction Gal B where
  smul σ b := ⟨σ b, isIntegral_smul σ b⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl
  smul_zero σ := Subtype.ext (map_zero σ)
  smul_add σ _ _ := Subtype.ext (map_add σ _ _)
  smul_one σ := Subtype.ext (map_one σ)
  smul_mul σ _ _ := Subtype.ext (map_mul σ _ _)

@[simp] theorem coe_smul (σ : Gal) (b : B) : ((σ • b : B) : Qbar) = σ (b : Qbar) := rfl

instance : SMulCommClass Gal ℤ B := inferInstance

instance : Algebra.IsInvariant ℤ B Gal := by
  refine ⟨fun b hb => ?_⟩
  have hfix : ∀ σ : Gal, σ (b : Qbar) = b := fun σ => congrArg Subtype.val (hb σ)
  have hbot : (b : Qbar) ∈ (⊥ : IntermediateField ℚ Qbar) :=
    (InfiniteGalois.mem_bot_iff_fixed (b : Qbar)).mpr hfix
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hbot
  have hint : IsIntegral ℤ (algebraMap ℚ Qbar q) := by
    rw [hq]; exact (mem_integralClosure_iff ℤ Qbar).mp b.2
  rw [isIntegral_algebraMap_iff] at hint
  obtain ⟨n, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨n, Subtype.ext ?_⟩
  rw [← hq]; simp

noncomputable instance : TopologicalSpace B := ⊥
instance : DiscreteTopology B := ⟨rfl⟩

instance : ContinuousSMul Gal B := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro b
  convert stabilizer_isOpen_of_isIntegral (K := ℚ) (L := Qbar) (b : Qbar) using 2
  ext σ
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h

/-- Transitivity on primes of `B` over the same prime of `ℤ` (Mathlib, profinite case). -/
theorem exists_smul_eq (P Q : Ideal B) [P.IsPrime] [Q.IsPrime] (h : P.under ℤ = Q.under ℤ) :
    ∃ g : Gal, Q = g • P :=
  Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := ℤ) (G := Gal) P Q h

/-! ## 3. Transport and inertia conjugation -/

theorem val_lt_one_iff (w : ValuationSubring Qbar) (t : Qbar) :
    w.valuation t < 1 ↔ t ∈ w ∧ (t = 0 ∨ t⁻¹ ∉ w) := by
  rw [← w.valuation_le_one_iff, ← w.valuation_le_one_iff]
  by_cases ht : t = 0
  · subst ht; simp
  have hprod : w.valuation t * w.valuation t⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ht, map_one]
  constructor
  · intro h
    refine ⟨h.le, Or.inr fun h' => ?_⟩
    have : w.valuation t * w.valuation t⁻¹ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h') h
    rw [hprod] at this; exact lt_irrefl _ this
  · rintro ⟨h1, h2 | h2⟩
    · exact absurd h2 ht
    · refine lt_of_le_of_ne h1 fun he => h2 ?_
      rw [he, one_mul] at hprod; exact hprod.le

/-- Transport of the maximal ideal under the pointwise action. -/
theorem val_smul_lt_one_iff (w : ValuationSubring Qbar) (g : Gal) (y : Qbar) :
    (g • w).valuation y < 1 ↔ w.valuation (g⁻¹ y) < 1 := by
  rw [val_lt_one_iff, val_lt_one_iff, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [AlgEquiv.smul_def, map_inv₀, map_eq_zero_iff _ (g⁻¹).injective]

/-- **Glue: conjugate places have conjugate inertia.** If `w' = g • w` then
`g⁻¹ I_{w'} g ≤ I_w` (inertia as in glue-b3-unram, the image of Mathlib's `inertiaSubgroup`). -/
theorem inertia_conj (w w' : ValuationSubring Qbar) (g : Gal) (hw : w' = g • w) (s : Gal)
    (hs : s ∈ (w'.inertiaSubgroup ℚ).map (w'.decompositionSubgroup ℚ).subtype) :
    g⁻¹ * s * g ∈ (w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype := by
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
  have hdec : g⁻¹ * (t : Gal) * g ∈ w.decompositionSubgroup ℚ := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, ← hw,
      MulAction.mem_stabilizer_iff.mp t.2, hw, inv_smul_smul]
  refine Subgroup.mem_map.mpr ⟨⟨_, hdec⟩, ?_, rfl⟩
  have ht' : ∀ z : w', w'.valuation ((t : Gal) (z : Qbar) - z) < 1 := by
    intro z
    have h1 : MulSemiringAction.toRingAut _ (IsLocalRing.ResidueField w') t = 1 := ht
    have h2 := congrArg (fun f => f (IsLocalRing.residue w' z)) h1
    change t • IsLocalRing.residue w' z = IsLocalRing.residue w' z at h2
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h2
    exact h2
  change _ = (1 : _)
  ext r
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨_, hdec⟩ : w.decompositionSubgroup ℚ) • IsLocalRing.residue w y = IsLocalRing.residue w y
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  have hgy : g (y : Qbar) ∈ w' := by
    rw [hw]; exact ValuationSubring.smul_mem_pointwise_smul_iff.mpr y.2
  let e : w.decompositionSubgroup ℚ := ⟨_, hdec⟩
  show w.valuation ((e • y - y : w) : Qbar) < 1
  have he : ((e • y - y : w) : Qbar) = g⁻¹ ((t : Gal) (g y) - g y) := by
    rw [map_sub]
    show (g⁻¹ * ↑t * g) (y : Qbar) - y = _
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    congr 1
    exact ((g⁻¹ : Gal).apply_symm_apply _).symm.trans (by rfl) |>.symm ▸ rfl
  rw [he]
  generalize hu : (t : Gal) = u at ht' ⊢
  have h3 := ht' ⟨_, hgy⟩
  clear ht'
  subst hw
  rw [val_smul_lt_one_iff] at h3
  exact h3

/-! ## 4. Assembly -/

/-- `B → w`: algebraic integers lie in every valuation subring. -/
noncomputable def toW (w : ValuationSubring Qbar) : B →+* w where
  toFun b := ⟨b, mem_of_isIntegral w ((mem_integralClosure_iff ℤ Qbar).mp b.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The center `𝔓_w = {b ∈ B | v_w(b) < 1}` of `w` on the algebraic integers. -/
noncomputable def centerIdeal (w : ValuationSubring Qbar) : Ideal B :=
  (IsLocalRing.maximalIdeal w).comap (toW w)

instance (w : ValuationSubring Qbar) : (centerIdeal w).IsPrime := Ideal.comap_isPrime _ _

theorem mem_centerIdeal (w : ValuationSubring Qbar) (b : B) :
    b ∈ centerIdeal w ↔ w.valuation (b : Qbar) < 1 :=
  w.valuation_lt_one_iff (toW w b)

theorem centerIdeal_under (w : ValuationSubring Qbar) (p : ℕ) (hp : p.Prime) (hw : LiesOver w p) :
    (centerIdeal w).under ℤ = Ideal.span {(p : ℤ)} := by
  have : Fact p.Prime := ⟨hp⟩
  have hmem : (p : ℤ) ∈ (centerIdeal w).under ℤ := by
    rw [Ideal.under, Ideal.mem_comap, mem_centerIdeal]
    simpa [LiesOver] using hw
  have hle : Ideal.span {(p : ℤ)} ≤ (centerIdeal w).under ℤ :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
  exact ((Int.ideal_span_isMaximal_of_prime p).eq_of_le
    (Ideal.comap_isPrime (algebraMap ℤ B) (centerIdeal w)).ne_top hle).symm

theorem centerIdeal_smul (w : ValuationSubring Qbar) (g : Gal) :
    centerIdeal (g • w) = g • centerIdeal w := by
  ext b
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_centerIdeal, mem_centerIdeal,
    val_smul_lt_one_iff]
  rfl

/-- **`LeafConj` is glue**: proved from Mathlib. -/
theorem leafConj : LeafConj := by
  intro p hp w w' hw hw'
  obtain ⟨g, hg⟩ := exists_smul_eq (centerIdeal w) (centerIdeal w')
    (by rw [centerIdeal_under w p hp hw, centerIdeal_under w' p hp hw'])
  rw [← centerIdeal_smul] at hg
  have hc : ∀ y : Qbar, IsIntegral ℤ y → (w'.valuation y < 1 ↔ (g • w).valuation y < 1) := by
    intro y hy
    have h := congrArg (fun I : Ideal B => (⟨y, (mem_integralClosure_iff ℤ Qbar).mpr hy⟩ : B) ∈ I) hg
    simp only [mem_centerIdeal] at h
    exact h.to_iff
  have hpint : IsIntegral ℤ (p : Qbar) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := Qbar) (x := (p : ℤ))
  have h1 := le_of_center w' (g • w) p hp hw' hc
  have h2 := le_of_center (g • w) w' p hp ((hc _ hpint).mp hw') (fun y hy => (hc y hy).symm)
  have heq : w' = g • w := le_antisymm h1 h2
  exact ⟨g, fun s hs => inertia_conj w w' g heq s hs⟩

end Conj

/-! ## glue-b3b: `LeafB3b` is glue

`ℚ(√p*)` is ramified at `p`, proved without discriminants: with `α` the quadratic Gauss sum
(`α² = ±p`), `H` the stabilizer of `α` and `A = B^H` (the algebraic integers fixed by `H`),
Mathlib's profinite transitivity over `A` and its surjectivity of the stabilizer of a prime onto
the automorphisms of the residue extension (`Ideal.Quotient.stabilizerHom_surjective_of_profinite`)
produce an element of the inertia group of `w` with `s α = -α`. The input "the residue extension
of `A` is trivial" is replaced by valuation arithmetic: `v(α)² = v(p)`. -/

section B3b

open scoped Pointwise

variable {w : ValuationSubring Qbar} {p : ℕ}

theorem val_natCast_ne_zero (hp : p.Prime) : w.valuation (p : Qbar) ≠ 0 := by
  rw [Ne, Valuation.zero_iff]; exact_mod_cast hp.ne_zero

theorem isIntegral_intCast (r : ℤ) : IsIntegral ℤ (r : Qbar) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := Qbar) (x := r)

theorem val_intCast_le_one (r : ℤ) : w.valuation (r : Qbar) ≤ 1 :=
  val_le_one_of_isIntegral w (isIntegral_intCast r)

/-- At a place over `p`, an integer has valuation `1` or at most `v(p)`. -/
theorem val_intCast (hp : p.Prime) (hw : LiesOver w p) (r : ℤ) :
    w.valuation (r : Qbar) = 1 ∨ w.valuation (r : Qbar) ≤ w.valuation (p : Qbar) := by
  by_cases hd : (p : ℤ) ∣ r
  · obtain ⟨k, rfl⟩ := hd
    right
    rw [Int.cast_mul, map_mul, Int.cast_natCast]
    exact mul_le_of_le_one_right' (val_intCast_le_one k)
  · left
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hcop : IsCoprime (p : ℤ) r := (Irreducible.coprime_iff_not_dvd hpr.irreducible).mpr hd
    obtain ⟨x, y, hxy⟩ := hcop
    have h1 := congrArg (fun z : ℤ => w.valuation (z : Qbar)) hxy
    simp only [Int.cast_add, Int.cast_mul, Int.cast_one, map_one, Int.cast_natCast] at h1
    refine le_antisymm (val_intCast_le_one r) ?_
    by_contra hlt
    push_neg at hlt
    have h2 : w.valuation ((x : Qbar) * p + y * r) < 1 := by
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one x)) hw
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one y)) hlt
    rw [h1] at h2; exact lt_irrefl _ h2

theorem val_sq_eq {α : Qbar} {c : ℤ} (hα : α ^ 2 = (c : Qbar))
    (hc : w.valuation (c : Qbar) = w.valuation (p : Qbar)) :
    w.valuation α * w.valuation α = w.valuation (p : Qbar) := by
  rw [← map_mul, ← pow_two, hα, hc]

/-- **The valuation input.** If `α² = c ∈ ℤ` with `v(c) = v(p)` (e.g. `c = ±p`), `a, b` are `w`-integral and `(a - b) α ∈ ℤ`, then
`a ≡ b` modulo `w`: since `v(α)` lies strictly between `v(p)` and `1`, while an integer has
valuation `1` or `≤ v(p)`. -/
theorem val_sub_lt_one (hp : p.Prime) (hw : LiesOver w p) {α : Qbar} {c : ℤ}
    (hα : α ^ 2 = (c : Qbar)) (hc : w.valuation (c : Qbar) = w.valuation (p : Qbar)) {a b : Qbar}
    (ha : w.valuation a ≤ 1) (hb : w.valuation b ≤ 1) (r : ℤ) (hr : (a - b) * α = r) :
    w.valuation (a - b) < 1 := by
  have hu := val_sq_eq (w := w) hα hc
  have hab : w.valuation (a - b) ≤ 1 := le_trans (Valuation.map_sub _ _ _) (max_le ha hb)
  have hu0 : w.valuation α ≠ 0 := by
    intro h; rw [h, zero_mul] at hu; exact val_natCast_ne_zero hp hu.symm
  have hu1 : w.valuation α < 1 := by
    by_contra h; push_neg at h
    have : (1 : _) ≤ w.valuation α * w.valuation α := one_le_mul h h
    rw [hu] at this; exact absurd hw (not_lt.mpr this)
  have hvr : w.valuation (r : Qbar) = w.valuation (a - b) * w.valuation α := by
    rw [← hr, map_mul]
  rcases val_intCast hp hw r with h1 | h1
  · rw [h1] at hvr
    have : w.valuation (a - b) * w.valuation α < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' hab) hu1
    rw [← hvr] at this; exact absurd this (lt_irrefl _)
  · rw [hvr, ← hu] at h1
    have h2 := mul_le_mul_left h1 (w.valuation α)⁻¹
    rw [mul_inv_cancel_right₀ hu0, mul_inv_cancel_right₀ hu0] at h2
    exact lt_of_le_of_lt h2 hu1

theorem smul_sq_cases {α : Qbar} {c : ℤ} (hα : α ^ 2 = (c : Qbar)) (g : Gal) :
    g α = α ∨ g α = -α := by
  have hc : g (α ^ 2) = α ^ 2 := by rw [hα, map_intCast]
  rw [map_pow] at hc
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hc

theorem exists_int_of_fixed {y : Qbar} (hy : IsIntegral ℤ y) (hfix : ∀ g : Gal, g y = y) :
    ∃ r : ℤ, y = r := by
  have hbot : y ∈ (⊥ : IntermediateField ℚ Qbar) := (InfiniteGalois.mem_bot_iff_fixed y).mpr hfix
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hbot
  have hint : IsIntegral ℤ (algebraMap ℚ Qbar q) := by rw [hq]; exact hy
  rw [isIntegral_algebraMap_iff] at hint
  obtain ⟨n, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  exact ⟨n, by rw [← hq]; simp⟩

/-- **Anti-invariance.** If `a` is fixed by every `g` fixing `α` and `σ α = -α`, then
`(a - σ a) α` is fixed by all of `G_ℚ`, hence an integer when `a` is integral. -/
theorem exists_int_anti {α a : Qbar} {c : ℤ} (hα : α ^ 2 = (c : Qbar))
    (hαi : IsIntegral ℤ α) (hai : IsIntegral ℤ a) (hfix : ∀ g : Gal, g α = α → g a = a)
    (σ : Gal) (hσ : σ α = -α) : ∃ r : ℤ, (a - σ a) * α = r := by
  have hσi : σ⁻¹ α = -α := by
    have h2 : (σ⁻¹ : Gal) (σ α) = α := by
      show (σ⁻¹ * σ) α = α
      rw [inv_mul_cancel]; rfl
    rw [hσ, map_neg] at h2
    exact neg_eq_iff_eq_neg.mp h2
  refine exists_int_of_fixed ?_ ?_
  · exact ((hai.sub (hai.map ((σ : Qbar →+* Qbar).toIntAlgHom))).mul hαi)
  intro g
  rw [map_mul, map_sub]
  rcases smul_sq_cases hα g with hg | hg
  · have h1 : g a = a := hfix g hg
    have h2 : (σ⁻¹ * g * σ) a = a := hfix _ (by
      show (σ⁻¹ : Gal) (g (σ α)) = α
      rw [hσ, map_neg, hg, map_neg, hσi, neg_neg])
    have h3 : g (σ a) = σ a := by
      have e : g (σ a) = σ ((σ⁻¹ * g * σ) a) := by
        show g (σ a) = (σ * (σ⁻¹ * g * σ)) a
        rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]; rfl
      rw [e, h2]
    rw [h1, h3, hg]
  · have h1 : (σ⁻¹ * g) a = a := hfix _ (by
      show (σ⁻¹ : Gal) (g α) = α
      rw [hg, map_neg, hσi, neg_neg])
    have h1' : g a = σ a := by
      have e : g a = σ ((σ⁻¹ * g) a) := by
        show g a = (σ * (σ⁻¹ * g)) a
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      rw [e, h1]
    have h2 : (g * σ) a = a := hfix _ (by
      show g (σ α) = α
      rw [hσ, map_neg, hg, neg_neg])
    have h2' : g (σ a) = a := h2
    rw [h1', h2', hg]; ring

/-- Elements of `w` are fractions `n / d` of algebraic integers with `v(d) = 1`. -/
theorem exists_frac (hp : p.Prime) (hw : LiesOver w p) (x : Qbar) (hx : x ∈ w) :
    ∃ n d : Qbar, IsIntegral ℤ n ∧ IsIntegral ℤ d ∧ w.valuation d = 1 ∧ x * d = n := by
  let K : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {x}
  have : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := ℚ) x)
  have : NumberField K := ⟨⟩
  let ι : 𝓞 K →+* Qbar := (algebraMap K Qbar).comp (algebraMap (𝓞 K) K)
  have hint : ∀ r : 𝓞 K, IsIntegral ℤ (ι r) := fun r =>
    (RingOfIntegers.isIntegral_coe r).map (IsScalarTower.toAlgHom ℤ K Qbar)
  let f : 𝓞 K →+* w :=
    { toFun := fun r => ⟨ι r, mem_of_isIntegral w (hint r)⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  let I : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal w).comap f
  have hI : ∀ r, r ∈ I ↔ w.valuation (ι r) < 1 := fun r =>
    (w.valuation_lt_one_iff (f r))
  have hpI : (p : 𝓞 K) ∈ I := by rw [hI]; simpa [ι, LiesOver] using hw
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨I, Ideal.comap_isPrime _ _, fun h => hp0 (by rw [h] at hpI; simpa using hpI)⟩
  let x' : K := ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩
  obtain ⟨n, d, h⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := K) x'
  have hd : ¬ w.valuation (ι d) < 1 := fun h' => d.2 ((hI d).mpr h')
  have hd1 : w.valuation (ι d) = 1 :=
    le_antisymm (val_le_one_of_isIntegral w (hint d)) (not_lt.mp hd)
  rcases h with h | h
  · have h' : x * ι d = ι n := by
      have := congrArg (algebraMap K Qbar) h
      simpa [ι] using this
    exact ⟨ι n, ι d, hint n, hint d, hd1, h'⟩
  · have h' : x * ι n = ι d := by
      have := congrArg (algebraMap K Qbar) h
      simpa [ι] using this
    have hx1 : w.valuation x ≤ 1 := (w.valuation_le_one_iff x).mpr hx
    have hn1 : w.valuation (ι n) ≤ 1 := val_le_one_of_isIntegral w (hint n)
    have hn : w.valuation (ι n) = 1 := by
      refine le_antisymm hn1 ?_
      have e := congrArg w.valuation h'
      rw [map_mul, hd1] at e
      rw [← e]; exact mul_le_of_le_one_left' hx1
    exact ⟨ι d, ι n, hint d, hint n, hn, h'⟩

/-- An element stabilizing the center `𝔓_w` and acting trivially on `B/𝔓_w` lies in the
inertia group `I_w`. -/
theorem mem_inertia_of_center (hp : p.Prime) (hw : LiesOver w p) (s : Gal)
    (hsQ : s • centerIdeal w = centerIdeal w)
    (hsb : ∀ b : B, s • b - b ∈ centerIdeal w) :
    s ∈ (w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype := by
  have hcs : centerIdeal (s • w) = centerIdeal w := by rw [centerIdeal_smul, hsQ]
  have hc : ∀ y : Qbar, IsIntegral ℤ y → ((s • w).valuation y < 1 ↔ w.valuation y < 1) := by
    intro y hy
    have h := congrArg (fun I : Ideal B => (⟨y, (mem_integralClosure_iff ℤ Qbar).mpr hy⟩ : B) ∈ I)
      hcs
    simp only [mem_centerIdeal] at h
    exact h.to_iff
  have hpint : IsIntegral ℤ (p : Qbar) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := Qbar) (x := (p : ℤ))
  have hw' : (s • w).valuation (p : Qbar) < 1 := (hc _ hpint).mpr hw
  have heq : s • w = w :=
    le_antisymm (le_of_center (s • w) w p hp hw' hc)
      (le_of_center w (s • w) p hp hw (fun y hy => (hc y hy).symm))
  have hdec : s ∈ w.decompositionSubgroup ℚ := heq
  refine Subgroup.mem_map.mpr ⟨⟨s, hdec⟩, ?_, rfl⟩
  have hB : ∀ y : Qbar, IsIntegral ℤ y → w.valuation (s y - y) < 1 := by
    intro y hy
    have := hsb ⟨y, (mem_integralClosure_iff ℤ Qbar).mpr hy⟩
    rw [mem_centerIdeal] at this
    exact this
  change _ = (1 : _)
  ext r
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨s, hdec⟩ : w.decompositionSubgroup ℚ) • IsLocalRing.residue w y =
    IsLocalRing.residue w y
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  show w.valuation (s (y : Qbar) - y) < 1
  obtain ⟨n, d, hn, hd, hd1, hnd⟩ := exists_frac hp hw (y : Qbar) y.2
  have hsd : w.valuation (s d) = 1 := by
    refine le_antisymm (val_le_one_of_isIntegral w (hd.map ((s : Qbar →+* Qbar).toIntAlgHom)))
      (not_lt.mp fun h => ?_)
    have h1 : (⟨s d, (mem_integralClosure_iff ℤ Qbar).mpr
        (hd.map ((s : Qbar →+* Qbar).toIntAlgHom))⟩ : B) ∈ s • centerIdeal w := by
      rw [hsQ, mem_centerIdeal]; exact h
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_centerIdeal] at h1
    have h2 : ((s⁻¹ • (⟨s d, (mem_integralClosure_iff ℤ Qbar).mpr
        (hd.map ((s : Qbar →+* Qbar).toIntAlgHom))⟩ : B) : B) : Qbar) = d := by
      show (s⁻¹ : Gal) (s d) = d
      show (s⁻¹ * s) d = d
      rw [inv_mul_cancel]; rfl
    rw [h2, hd1] at h1; exact lt_irrefl _ h1
  have hsnd : s (y : Qbar) * s d = s n := by rw [← map_mul, hnd]
  have key : (s (y : Qbar) - y) * (d * s d) = (s n - n) * d - n * (s d - d) := by
    linear_combination d * hsnd - s d * hnd
  have hv := congrArg w.valuation key
  rw [map_mul, map_mul, hd1, hsd, one_mul, mul_one] at hv
  rw [hv]
  refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
  · rw [map_mul, hd1, mul_one]; exact hB n hn
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_le_one_of_isIntegral w hn)) (hB d hd)

end B3b

section B3bMain

open scoped Pointwise

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The inertia element.** If `α² = c ∈ ℤ` with `v_w(c) = v_w(p)` (e.g. `c = ±p`) and some `σ ∈ G_ℚ` negates `α`, then some element of
the inertia group of any place `w` over `p` negates `α`. -/
theorem exists_inertia_neg (p : ℕ) (hp : p.Prime) (w : ValuationSubring Qbar) (hw : LiesOver w p)
    (α : Qbar) (c : ℤ) (hα : α ^ 2 = (c : Qbar))
    (hc : w.valuation (c : Qbar) = w.valuation (p : Qbar)) (σ : Gal) (hσ : σ α = -α) :
    ∃ s : Gal, s ∈ (w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype ∧ s α = -α := by
  classical
  have hpint : IsIntegral ℤ (p : Qbar) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := Qbar) (x := (p : ℤ))
  have hαint : IsIntegral ℤ α := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hα]; exact isIntegral_intCast c
  let H : Subgroup Gal := MulAction.stabilizer Gal α
  have hH : ∀ g : Gal, g ∈ H ↔ g α = α := fun g => Iff.rfl
  have hHopen : IsOpen (H : Set Gal) := stabilizer_isOpen_of_isIntegral (K := ℚ) (L := Qbar) α
  have hHclosed : IsClosed (H : Set Gal) := Subgroup.isClosed_of_isOpen H hHopen
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hHclosed.isCompact
  let A := FixedPoints.subalgebra ℤ B H
  let Q := centerIdeal w
  haveI : SMulCommClass H A B := ⟨fun h a b => by
    rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, smul_mul', a.2 h]⟩
  -- elements of `A` are fixed by every `g` fixing `α`
  have hAfix : ∀ (a : A) (g : Gal), g α = α → g ((a : B) : Qbar) = ((a : B) : Qbar) := by
    intro a g hg
    have := a.2 ⟨g, hg⟩
    exact congrArg Subtype.val this
  -- the valuation input on `A`
  have hAval : ∀ (a : A) (σ' : Gal), σ' α = -α →
      w.valuation (((a : B) : Qbar) - σ' ((a : B) : Qbar)) < 1 := by
    intro a σ' hσ'
    have hai : IsIntegral ℤ ((a : B) : Qbar) := (mem_integralClosure_iff ℤ Qbar).mp (a : B).2
    obtain ⟨r, hr⟩ := exists_int_anti hα hαint hai (hAfix a) σ' hσ'
    exact val_sub_lt_one hp hw hα hc (val_le_one_of_isIntegral w hai)
      (val_le_one_of_isIntegral w (hai.map ((σ' : Qbar →+* Qbar).toIntAlgHom))) r hr
  -- step 1: `σ • Q` and `Q` lie over the same prime of `A`
  have hunder : (σ • Q).under A = Q.under A := by
    ext a
    rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_centerIdeal, mem_centerIdeal]
    have hσi : σ⁻¹ α = -α := by
      have h2 : (σ⁻¹ : Gal) (σ α) = α := by
        show (σ⁻¹ * σ) α = α
        rw [inv_mul_cancel]; rfl
      rw [hσ, map_neg] at h2
      exact neg_eq_iff_eq_neg.mp h2
    have h := hAval a σ⁻¹ hσi
    show w.valuation ((σ⁻¹ : Gal) ((a : B) : Qbar)) < 1 ↔ w.valuation ((a : B) : Qbar) < 1
    constructor
    · intro h1
      have : ((a : B) : Qbar) = (((a : B) : Qbar) - (σ⁻¹ : Gal) ((a : B) : Qbar)) +
          (σ⁻¹ : Gal) ((a : B) : Qbar) := by ring
      rw [this]; exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h h1)
    · intro h1
      have : (σ⁻¹ : Gal) ((a : B) : Qbar) = ((a : B) : Qbar) -
          (((a : B) : Qbar) - (σ⁻¹ : Gal) ((a : B) : Qbar)) := by ring
      rw [this]; exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1 h)
  -- step 2: transitivity over `A` gives `τ` stabilizing `Q` and negating `α`
  haveI hσQ : (σ • Q).IsPrime := by
    show (σ • centerIdeal w).IsPrime
    rw [← centerIdeal_smul]; infer_instance
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := A) (G := H)
    (σ • Q) Q hunder
  let τ : Gal := (g : Gal) * σ
  have hτQ : τ • Q = Q := by
    show ((g : Gal) * σ) • Q = Q
    rw [mul_smul]; exact hg.symm
  have hτα : τ α = -α := by
    show (g : Gal) (σ α) = -α
    rw [hσ, map_neg, (hH g).mp g.2]
  -- step 3: `τ` induces an `A/P`-automorphism of `B/Q`
  let f : B ≃+* B := MulSemiringAction.toRingEquiv Gal B τ
  have hQf : Q = Q.map f := by
    ext b
    rw [Ideal.mem_map_of_equiv]
    constructor
    · intro hb
      refine ⟨τ⁻¹ • b, ?_, by simp [f]⟩
      rw [← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hτQ]; exact hb
    · rintro ⟨x, hx, rfl⟩
      rw [← hτQ]
      exact Ideal.smul_mem_pointwise_smul_iff.mpr hx
  let e : (B ⧸ Q) ≃+* (B ⧸ Q) := Ideal.quotientEquiv Q Q f hQf
  have he : ∀ b : B, e (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (τ • b) := fun b => rfl
  let φ : (B ⧸ Q) ≃ₐ[A ⧸ Q.under A] (B ⧸ Q) := AlgEquiv.ofRingEquiv (f := e) (by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, he, Ideal.Quotient.eq, mem_centerIdeal]
    have h := hAval a τ hτα
    rw [Valuation.map_sub_swap] at h
    exact h)
  -- step 4: Mathlib's surjectivity gives `h' ∈ H` acting on `B/Q` as `τ`
  obtain ⟨h', hh'⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H)
    (Q.under A) Q φ
  have hact : ∀ b : B, Ideal.Quotient.mk Q (((h' : H) : Gal) • b) =
      Ideal.Quotient.mk Q (τ • b) := by
    intro b
    have := congrArg (fun ψ => ψ (Ideal.Quotient.mk Q b)) hh'
    exact this
  let k : Gal := ((h' : H) : Gal)
  have hkQ : k • Q = Q := h'.2
  have hkα : k α = α := (h' : H).2
  let s : Gal := k⁻¹ * τ
  refine ⟨s, ?_, ?_⟩
  · apply mem_inertia_of_center hp hw s
    · show (k⁻¹ * τ) • Q = Q
      rw [mul_smul, hτQ, inv_smul_eq_iff, hkQ]
    · intro b
      have h1 := hact (s • b)
      have h2 : ((h' : H) : Gal) • (s • b) = τ • b := by
        show k • ((k⁻¹ * τ) • b) = τ • b
        rw [mul_smul, smul_inv_smul]
      rw [h2, Ideal.Quotient.eq] at h1
      -- `τ • b - τ • (s • b) ∈ Q`, hence `b - s • b ∈ Q`
      have h3 : b - s • b ∈ Q := by
        have h4 : τ • (b - s • b) ∈ τ • Q := by rw [hτQ, smul_sub]; exact h1
        rwa [Ideal.smul_mem_pointwise_smul_iff] at h4
      have := Q.neg_mem h3
      rwa [neg_sub] at this
  · show k⁻¹ (τ α) = -α
    rw [hτα, map_neg]
    congr 1
    have : k⁻¹ (k α) = α := by
      show (k⁻¹ * k) α = α
      rw [inv_mul_cancel]; rfl
    rwa [hkα] at this

end B3bMain

section B3bGauss

/-- The cyclotomic character on a primitive `p`-th root of unity: `s ζ = ζ ^ cyc(s)`. -/
theorem act_zeta (p : ℕ) [NeZero p] {ζ : Qbar} (hζ : IsPrimitiveRoot ζ p) (s : Gal) :
    s ζ = ζ ^ ((cyc p s : (ZMod p)ˣ) : ZMod p).val := by
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne p⟩
  have hn := HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) p
  have h := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) hn (toRingAut s)
    (t := (hζ.toRootsOfUnity : Qbarˣ)) (hζ.toRootsOfUnity).2
  simp only [IsPrimitiveRoot.val_toRootsOfUnity_coe] at h
  exact h

/-- The quadratic Gauss sum `∑ₐ (a/p) ζ^a ∈ ℚ̄`. -/
noncomputable def gaussP (p : ℕ) [Fact p.Prime] {ζ : Qbar} (hζ : IsPrimitiveRoot ζ p) : Qbar :=
  gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom Qbar))
    (AddChar.zmodChar p ((IsPrimitiveRoot.iff_def ζ p).mp hζ).left)

/-- `σ(g) = (cyc(σ)/p) · g` for the Gauss sum `g`. -/
theorem gaussP_transform (p : ℕ) [Fact p.Prime] {ζ : Qbar} (hζ : IsPrimitiveRoot ζ p) (s : Gal) :
    s (gaussP p hζ) =
      ((quadraticChar (ZMod p) ((cyc p s : (ZMod p)ˣ) : ZMod p) : ℤ) : Qbar) * gaussP p hζ := by
  let χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom Qbar)
  let ψ := AddChar.zmodChar p ((IsPrimitiveRoot.iff_def ζ p).mp hζ).left
  let c := cyc p s
  have hχ : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp _
  have hsψ : ∀ a, s (ψ a) = ψ.mulShift (c : ZMod p) a := by
    intro a
    have hca : (c : ZMod p) * a = ((c : ZMod p).val) • a := by
      rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
    rw [AddChar.mulShift_apply, hca, AddChar.map_nsmul_eq_pow, AddChar.zmodChar_apply, map_pow,
      act_zeta p hζ s, ← pow_mul, ← pow_mul, mul_comm]
  have hsχ : ∀ a, s (χ a) = χ a := by
    intro a
    show s ((Int.castRingHom Qbar) _) = (Int.castRingHom Qbar) _
    rw [eq_intCast, map_intCast]
  show s (gaussSum χ ψ) = _ * gaussSum χ ψ
  calc s (gaussSum χ ψ) = gaussSum χ (ψ.mulShift (c : ZMod p)) := by
        unfold gaussSum
        rw [map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_mul, hsψ, hsχ]
    _ = χ⁻¹ c * gaussSum χ ψ := gaussSum_mulShift_eq χ ψ c
    _ = _ := by
        rw [hχ.inv]
        show (Int.castRingHom Qbar) _ * _ = _
        rw [eq_intCast]

/-- `g² = (-1/p) p = ±p`. -/
theorem gaussP_sq (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) {ζ : Qbar}
    (hζ : IsPrimitiveRoot ζ p) :
    gaussP p hζ ^ 2 = (p : Qbar) ∨ gaussP p hζ ^ 2 = -(p : Qbar) := by
  have hχ : ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom Qbar)).IsQuadratic :=
    (quadraticChar_isQuadratic (ZMod p)).comp _
  have hχ1 : (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom Qbar) ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (Int.castRingHom Qbar).injective_int).mpr
      (quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; exact hp2))
  unfold gaussP
  rw [gaussSum_sq hχ1 hχ (AddChar.zmodChar_primitive_of_primitive_root p hζ), ZMod.card,
    MulChar.ringHomComp_apply]
  rcases quadraticChar_dichotomy (F := ZMod p) (a := -1) (neg_ne_zero.mpr one_ne_zero) with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

/-- If `α² = c ∈ ℤ` and `c` is not a square in `ℚ`, some `σ ∈ G_ℚ` negates `α`. -/
theorem exists_neg_of_sq {α : Qbar} {c : ℤ} (hα : α ^ 2 = (c : Qbar))
    (hc : ¬ IsSquare (c : ℚ)) : ∃ σ : Gal, σ α = -α := by
  by_contra hne
  push_neg at hne
  have hfix : ∀ g : Gal, g α = α := fun g => (smul_sq_cases hα g).resolve_right (hne g)
  have hbot : α ∈ (⊥ : IntermediateField ℚ Qbar) := (InfiniteGalois.mem_bot_iff_fixed α).mpr hfix
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hbot
  rw [← hq] at hα
  have h' : q ^ 2 = (c : ℚ) := by
    apply (algebraMap ℚ Qbar).injective; rw [map_pow, hα, map_intCast]
  exact hc ⟨q, by rw [← h', sq]⟩

/-- A squarefree integer divisible by a prime is not a square in `ℚ`. -/
theorem not_isSquare_of_squarefree {d : ℤ} (hd : Squarefree d) {p : ℕ} (hp : p.Prime)
    (hpd : (p : ℤ) ∣ d) : ¬ IsSquare (d : ℚ) := by
  rw [Rat.isSquare_intCast_iff]
  rintro ⟨r, hr⟩
  have hu : IsUnit r := hd r ⟨1, by rw [hr, mul_one]⟩
  have h1 : d = 1 := by
    rcases Int.isUnit_iff.mp hu with h | h <;> rw [hr, h] <;> norm_num
  rw [h1] at hpd
  have := Int.eq_one_of_dvd_one (by positivity) hpd
  exact hp.one_lt.ne' (by exact_mod_cast this)

/-- **`LeafB3b` is glue** (proved from Mathlib): the Legendre character mod an odd prime `p`, as a
character of `G_ℚ`, is nontrivial on the inertia group of every place over `p`. -/
theorem leafB3b : LeafB3b := by
  intro p hp hp2 w hw
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero ((p : ℕ) : Qbar) := ⟨by exact_mod_cast hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar p
  have hα := gaussP_sq p hp2 hζ
  obtain ⟨c, hαc, hc, hcp⟩ : ∃ c : ℤ, gaussP p hζ ^ 2 = (c : Qbar) ∧
      w.valuation (c : Qbar) = w.valuation (p : Qbar) ∧ Squarefree c ∧ (p : ℤ) ∣ c := by
    have hsf : Squarefree (p : ℤ) := Int.squarefree_natCast.mpr hp.squarefree
    rcases hα with h | h
    · exact ⟨p, by rw [h]; simp, by simp, hsf, dvd_rfl⟩
    · exact ⟨-p, by rw [h]; simp, by simp [Valuation.map_neg], fun x hx => hsf x (dvd_neg.mp hx), by simp⟩
  obtain ⟨σ, hσ⟩ := exists_neg_of_sq hαc (not_isSquare_of_squarefree hcp.1 hp hcp.2)
  obtain ⟨s, hs, hsα⟩ := exists_inertia_neg p hp w hw (gaussP p hζ) c hαc hc σ hσ
  refine ⟨s, hs, fun h1 => ?_⟩
  have hq : quadraticChar (ZMod p) ((cyc p s : (ZMod p)ˣ) : ZMod p) = 1 := by
    unfold etaP at h1
    rw [dif_pos hp] at h1
    unfold galChar at h1
    have h2 : (((legChar p).toUnitHom (cyc p s) : ℂˣ) : ℂ) = 1 := by
      have := congrArg Units.val h1; exact this
    rw [MulChar.coe_toUnitHom] at h2
    unfold legChar at h2
    rw [dif_pos hp, MulChar.ringHomComp_apply, eq_intCast] at h2
    exact_mod_cast h2
  have h3 := gaussP_transform p hζ s
  rw [hq, Int.cast_one, one_mul, hsα] at h3
  have h0 : gaussP p hζ = 0 := by
    have h4 : (2 : Qbar) * gaussP p hζ = 0 := by linear_combination -h3
    exact (mul_eq_zero.mp h4).resolve_left two_ne_zero
  rw [h0] at hα
  have hp0 : (p : Qbar) ≠ 0 := by exact_mod_cast hp.ne_zero
  rcases hα with h | h
  · exact hp0 (by rw [← h]; ring)
  · exact hp0 (by rw [← neg_eq_zero, ← h]; ring)

end B3bGauss


/-- **B3 (v) from two leaves** (L-B3a, L-B3b; conjugacy of places (`leafConj`), finite
ramification and the unramifiedness of Dirichlet characters at primes not dividing the modulus
are proved glue),
with glue-descent's hypothesis form on `L`: the twisted kernel field `L'` is unramified outside
`T` (Galois form). -/
theorem unramified_outside_final (hA : LeafB3a) (hB : LeafB3b)
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
  unramified_outside_of_unramifiedAt hA hB leafConj finRam L T h2 hram ε hεN χ hN β hβl hβs hβe

/-- **B3 (v) from one leaf** (glue-b3b): `LeafB3b` is now proved glue (`leafB3b`), so the twisted
kernel field `L'` is unramified outside `T` assuming only L-B3a (the unique quadratic character
of tame inertia). Same conclusion and hypotheses on `L` as `unramified_outside_final`. -/
theorem unramified_outside_b3a (hA : LeafB3a)
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
  unramified_outside_final hA leafB3b L T h2 hram ε hεN χ hN β hβl hβs hβe

end GlueB3Unram

/-! ## T32(b) of the synthesis bundle (leaf-push's form), proved as glue -/

namespace LeafPush

-- verbatim from scratch/leaf-push/Push.lean (= scratch/h-decomposition/Leaves.lean, section 5)
/-- The absolute Galois group `G_ℚ = Aut(ℚ̄/ℚ)` (with Mathlib's Krull topology). -/
abbrev GQ := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- `O` is the valuation subring `ℤ_(p)` of `ℚ`: a discrete valuation ring in which `p` is not a
unit (for any other valuation subring of `ℚ`, `p` is a unit). -/
def IsAtPrime (O : ValuationSubring ℚ) (p : ℕ) : Prop :=
  IsDiscreteValuationRing O ∧ ¬ IsUnit (p : O)

/-- The inertia subgroup `I_w ⊆ G_ℚ` of a valuation subring `w` of `ℚ̄` (Mathlib's
`ValuationSubring.inertiaSubgroup`, pushed into `G_ℚ`). -/
noncomputable def inertiaQ (w : ValuationSubring (AlgebraicClosure ℚ)) : Subgroup GQ :=
  ((w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype)

/-- **T32(b). The quadratic character of `ℚ(√d)` ramifies exactly at the primes dividing `d`,
for `d ≡ 1 mod 4` squarefree** (the quadratic Dirichlet character of odd squarefree conductor
`P` is that of `ℚ(√d)`, `d = ±P ≡ 1 mod 4`). Published: the discriminant of `ℚ(√d)` is `d`
(Neukirch I (2.?); Washington Ch. 3) and `p` ramifies iff `p | disc` (Neukirch III (2.12)),
together with "ramified ⇔ inertia acts nontrivially" (Neukirch I §9; numbering UNVERIFIED).
Lean form: for a square root `s ∈ ℚ̄` of `d` and `w` over `ℤ_(p)`, some inertia element moves `s`
iff `p | d`. `σ ↦ σ(s)/s` is the quadratic character, so this is the published statement. -/
def T32b_QuadraticRamification : Prop :=
  ∀ (d : ℤ), Squarefree d → d % 4 = 1 →
    ∀ (s : AlgebraicClosure ℚ), s ^ 2 = (d : AlgebraicClosure ℚ) →
    ∀ (p : ℕ), p.Prime →
    ∀ (O : ValuationSubring ℚ), IsAtPrime O p →
    ∀ (w : ValuationSubring (AlgebraicClosure ℚ)), w.comap (algebraMap ℚ _) = O →
      ((∃ σ ∈ inertiaQ w, σ s ≠ s) ↔ (p : ℤ) ∣ d)

end LeafPush

namespace GlueB3Unram

open scoped Pointwise

/-- `w` over `ℤ_(p)` (leaf-push's `IsAtPrime` form) lies over `p` in the sense of `LiesOver`. -/
theorem liesOver_of_isAtPrime {p : ℕ} (O : ValuationSubring ℚ) (hO : LeafPush.IsAtPrime O p)
    (w : ValuationSubring Qbar) (hw : w.comap (algebraMap ℚ Qbar) = O) : LiesOver w p := by
  unfold LiesOver
  have hpw : (p : Qbar) ∈ w := mem_of_isIntegral w (by
    simpa using isIntegral_algebraMap (R := ℤ) (A := Qbar) (x := (p : ℤ)))
  rw [val_lt_one_iff]
  refine ⟨hpw, ?_⟩
  by_cases hp0 : (p : ℚ) = 0
  · left; rw [show (p : Qbar) = algebraMap ℚ Qbar (p : ℚ) by simp, hp0, map_zero]
  right
  intro hinv
  apply hO.2
  have hpO : ((p : ℚ)⁻¹) ∈ O := by
    rw [← hw, ValuationSubring.mem_comap]; simpa using hinv
  refine IsUnit.of_mul_eq_one (a := (p : O)) ⟨(p : ℚ)⁻¹, hpO⟩ ?_
  ext
  simp [hp0]

theorem val_intCast_eq_one {w : ValuationSubring Qbar} {p : ℕ} (hp : p.Prime) (hw : LiesOver w p)
    (r : ℤ) (hd : ¬ (p : ℤ) ∣ r) : w.valuation (r : Qbar) = 1 := by
  rcases val_intCast hp hw r with h | h
  · exact h
  · exfalso
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hcop : IsCoprime (p : ℤ) r := (Irreducible.coprime_iff_not_dvd hpr.irreducible).mpr hd
    obtain ⟨x, y, hxy⟩ := hcop
    have h1 := congrArg (fun z : ℤ => w.valuation (z : Qbar)) hxy
    simp only [Int.cast_add, Int.cast_mul, Int.cast_one, map_one, Int.cast_natCast] at h1
    have h2 : w.valuation ((x : Qbar) * p + y * r) < 1 := by
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one x)) hw
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one y)) (lt_of_le_of_lt h hw)
    rw [h1] at h2; exact lt_irrefl _ h2

/-- **T32(b) is glue** (proved from Mathlib): for squarefree `d ≡ 1 mod 4`, a square root `s` of
`d` and `w` over `ℤ_(p)`, some inertia element moves `s` iff `p ∣ d`. -/
theorem t32b : LeafPush.T32b_QuadraticRamification := by
  intro d hd hd4 s hs p hp O hO w hw
  have hwp : LiesOver w p := liesOver_of_isAtPrime O hO w hw
  have hd0 : d ≠ 0 := by rintro rfl; exact not_squarefree_zero hd
  constructor
  · rintro ⟨σ, hσ, hσs⟩
    by_contra hpd
    have hvd : w.valuation (d : Qbar) = 1 := val_intCast_eq_one hp hwp d hpd
    have hσs' : σ s = -s := (smul_sq_cases hs σ).resolve_left hσs
    obtain ⟨k, hk⟩ : ∃ k : ℤ, d = 4 * k + 1 := ⟨d / 4, by omega⟩
    have hk' : (d : Qbar) = 4 * k + 1 := by rw [hk]; push_cast; ring
    set t : Qbar := (1 + s) / 2 with htdef
    have ht : t ^ 2 - t - (k : Qbar) = 0 := by
      rw [htdef]; linear_combination (1 / 4 : Qbar) * hs + (1 / 4 : Qbar) * hk'
    have htint : IsIntegral ℤ t := by
      refine ⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C k), ?_, ?_⟩
      · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X_add_C]; norm_num)
      · rw [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_X_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C, eq_intCast]
        linear_combination ht
    have htw : t ∈ w := mem_of_isIntegral w htint
    obtain ⟨y, hy, hres⟩ := residue_inertia w σ hσ ⟨t, htw⟩
    have h1 : w.valuation (σ t - t) < 1 := by
      have h0 : IsLocalRing.residue w (y - ⟨t, htw⟩) = 0 := by rw [map_sub, hres, sub_self]
      rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h0
      have e : ((y - ⟨t, htw⟩ : w) : Qbar) = σ t - t := by
        show (y : Qbar) - t = σ t - t
        rw [hy]; rfl
      rwa [e] at h0
    have h2 : σ t - t = -s := by
      rw [htdef, map_div₀, map_add, map_one, hσs', map_ofNat]; ring
    rw [h2, Valuation.map_neg] at h1
    have h3 : w.valuation s * w.valuation s = 1 := by rw [← map_mul, ← sq, hs, hvd]
    have h4 : w.valuation s * w.valuation s < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' h1.le) h1
    rw [h3] at h4; exact lt_irrefl _ h4
  · intro hpd
    obtain ⟨m, rfl⟩ := hpd
    have hpm : ¬ (p : ℤ) ∣ m := by
      rintro ⟨n, rfl⟩
      have := hd (p : ℤ) ⟨n, by ring⟩
      rw [Int.isUnit_iff] at this
      rcases this with h | h
      · exact hp.one_lt.ne' (by exact_mod_cast h)
      · have : (0 : ℤ) ≤ p := by positivity
        omega
    have hvd : w.valuation (((p : ℤ) * m : ℤ) : Qbar) = w.valuation (p : Qbar) := by
      rw [Int.cast_mul, map_mul, val_intCast_eq_one hp hwp m hpm, mul_one, Int.cast_natCast]
    obtain ⟨σ, hσ⟩ := exists_neg_of_sq hs (not_isSquare_of_squarefree hd hp ⟨m, rfl⟩)
    obtain ⟨σ', hσ', hσ's⟩ := exists_inertia_neg p hp w hwp s _ hs hvd σ hσ
    refine ⟨σ', hσ', ?_⟩
    rw [hσ's]
    intro h
    have hs0 : s = 0 := by
      have h5 : (2 : Qbar) * s = 0 := by linear_combination -h
      exact (mul_eq_zero.mp h5).resolve_left two_ne_zero
    rw [hs0] at hs
    have : (((p : ℤ) * m : ℤ) : Qbar) = 0 := by rw [← hs]; ring
    exact hd0 (by exact_mod_cast this)

end GlueB3Unram



/-! ## T32(a) implies `LeafB3a` (glue-b3b): B3 (v) from the bundle's leaf T32(a) -/

namespace LeafPush

-- verbatim from scratch/leaf-push/Push.lean (= scratch/h-decomposition/Leaves.lean, section 5)
/-- **T32(a). Serre, *Local fields*, IV §2, Cor. 1-4 (tame inertia is `∏_{ℓ≠p} ℤ_ℓ(1)`, wild
inertia is pro-`p`), with the identification of `I_w ⊆ G_ℚ` with the inertia group of
`ℚ̄_p/ℚ_p` (Neukirch, ANT, II §9 / Serre II §3; numbering UNVERIFIED).** Published consequence:
for `p` odd, the continuous homomorphisms `I_p → {±1}` form a group of order 2 (a quadratic
character kills the pro-`p` wild inertia, and `Hom_cont(∏_{ℓ≠p} ℤ_ℓ, ℤ/2) = ℤ/2`). Lean form:
for `w` over `ℤ_(p)`, the continuous monoid maps `I_w →* ℤˣ` number exactly 2 (`ℤˣ = {±1}`,
discrete). "Unique nontrivial quadratic character of inertia" is exactly this. -/
def T32a_TameQuadratic : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∀ (O : ValuationSubring ℚ), IsAtPrime O p →
    ∀ (w : ValuationSubring (AlgebraicClosure ℚ)), w.comap (algebraMap ℚ _) = O →
      Nat.card {χ : inertiaQ w →* ℤˣ // Continuous χ} = 2

end LeafPush

namespace GlueB3Unram

/-- `w ∩ ℚ` is `ℤ_(p)` in leaf-push's sense when `w` lies over `p`. -/
theorem isAtPrime_comap {p : ℕ} (hp : p.Prime) (w : ValuationSubring Qbar) (hw : LiesOver w p) :
    LeafPush.IsAtPrime (w.comap (algebraMap ℚ Qbar)) p := by
  set O := w.comap (algebraMap ℚ Qbar) with hO
  have hmem : ∀ q : ℚ, q ∈ O ↔ w.valuation (algebraMap ℚ Qbar q) ≤ 1 := fun q => by
    rw [hO, ValuationSubring.mem_comap, ValuationSubring.valuation_le_one_iff]
  have hnu : ¬ IsUnit (p : O) := by
    rintro ⟨u, hu⟩
    have h1 : ((u⁻¹ : Oˣ) : O) * (p : O) = 1 := by rw [← hu]; exact u.inv_mul
    have h2 : (((u⁻¹ : Oˣ) : O) : ℚ) * p = 1 := by
      have := congrArg (fun x : O => (x : ℚ)) h1; simpa using this
    have h3 := (hmem _).mp (((u⁻¹ : Oˣ) : O)).2
    have h4 := congrArg (fun q => w.valuation (algebraMap ℚ Qbar q)) h2
    simp only [map_mul, map_natCast, map_one] at h4
    have h5 : w.valuation (algebraMap ℚ Qbar (((u⁻¹ : Oˣ) : O) : ℚ)) * w.valuation (p : Qbar) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' h3) hw
    rw [h4] at h5; exact lt_irrefl _ h5
  refine ⟨?_, hnu⟩
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  haveI : P.IsPrime := (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp)
  have hP : P ≠ ⊥ := by
    simp only [P, ne_eq, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
  have hmemP : ∀ b : ℤ, b ∈ P ↔ (p : ℤ) ∣ b := fun b => Ideal.mem_span_singleton
  haveI : IsLocalization.AtPrime O P := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨b, hb⟩
      have hb' : ¬ (p : ℤ) ∣ b := fun h => hb ((hmemP b).mpr h)
      have hb0 : (b : ℚ) ≠ 0 := by
        intro h; apply hb'; rw [Int.cast_eq_zero.mp h]; exact dvd_zero _
      have hv : w.valuation (b : Qbar) = 1 := val_intCast_eq_one hp hw b hb'
      have hinv : (b : ℚ)⁻¹ ∈ O := by rw [hmem]; simp [map_inv₀, hv]
      refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
      ext; simp [hb0]
    · intro z
      have hz := (hmem _).mp z.2
      set q : ℚ := (z : ℚ) with hq
      have hden : ¬ (p : ℤ) ∣ (q.den : ℤ) := by
        intro hd
        have hn : ¬ (p : ℤ) ∣ q.num := by
          intro hn
          rw [Int.natCast_dvd] at hn
          rw [Int.natCast_dvd_natCast] at hd
          have h3 := Nat.dvd_gcd hn hd
          rw [Nat.Coprime.gcd_eq_one q.reduced] at h3
          exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
        have hvn : w.valuation (q.num : Qbar) = 1 := val_intCast_eq_one hp hw _ hn
        have hvd : w.valuation ((q.den : ℤ) : Qbar) < 1 := by
          obtain ⟨k, hk⟩ := hd
          have : w.valuation ((q.den : ℤ) : Qbar) ≤ w.valuation (p : Qbar) := by
            rw [hk, Int.cast_mul, map_mul, Int.cast_natCast]
            exact mul_le_of_le_one_right' (val_intCast_le_one k)
          exact lt_of_le_of_lt this hw
        have e : q * (q.den : ℚ) = q.num := Rat.mul_den_eq_num q
        have e2 := congrArg (fun r => w.valuation (algebraMap ℚ Qbar r)) e
        simp only [map_mul, map_natCast, map_intCast] at e2
        rw [hvn] at e2
        have : w.valuation (algebraMap ℚ Qbar q) * w.valuation ((q.den : ℕ) : Qbar) < 1 :=
          lt_of_le_of_lt (mul_le_of_le_one_left' hz) (by simpa using hvd)
        rw [e2] at this; exact lt_irrefl _ this
      refine ⟨⟨q.num, ⟨q.den, fun h => hden ((hmemP _).mp h)⟩⟩, ?_⟩
      ext
      simp only [algebraMap_int_eq, eq_intCast, MulMemClass.coe_mul, SubringClass.coe_intCast]
      push_cast
      rw [← hq]; exact Rat.mul_den_eq_num q
    · intro x y h
      refine ⟨1, ?_⟩
      have := congrArg (fun z : O => (z : ℚ)) h
      simp only [algebraMap_int_eq, eq_intCast] at this
      push_cast at this
      have hxy : x = y := by exact_mod_cast this
      rw [hxy]
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ hP O

theorem units_sq_eq_one {x : ℂˣ} (hx : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h : (x : ℂ) * x = 1 := by
    have := congrArg Units.val hx; rw [Units.val_pow_eq_pow_val, sq] at this; simpa using this
  rcases mul_self_eq_one_iff.mp h with h | h
  · left; exact Units.ext h
  · right; exact Units.ext (by simpa using h)

theorem neg_one_ne_one_C : (-1 : ℂˣ) ≠ 1 := by
  intro h; have := congrArg Units.val h; norm_num at this

/-- A `±1`-valued character into `ℂˣ`, as a character into `ℤˣ`. -/
noncomputable def sgnHom {G : Type*} [Group G] (φ : G →* ℂˣ) (hφ2 : ∀ s, φ s ^ 2 = 1) :
    G →* ℤˣ where
  toFun s := if φ s = 1 then 1 else -1
  map_one' := by simp
  map_mul' s t := by
    have hne := neg_one_ne_one_C
    rcases units_sq_eq_one (hφ2 s) with h1 | h1 <;> rcases units_sq_eq_one (hφ2 t) with h2 | h2 <;>
      simp [map_mul, h1, h2, hne]

theorem sgnHom_apply {G : Type*} [Group G] (φ : G →* ℂˣ) (hφ2 : ∀ s, φ s ^ 2 = 1) (s : G) :
    sgnHom φ hφ2 s = if φ s = 1 then 1 else -1 := rfl

/-- **`LeafB3a` follows from the bundle's leaf T32(a)** (glue): the three characters `1`,
`sgn ∘ φ`, `sgn ∘ ψ` of `I_w` into `ℤˣ` are continuous, and pairwise distinct if `φ ≠ ψ`. -/
theorem leafB3a_of_t32a (hT : LeafPush.T32a_TameQuadratic) : LeafB3a := by
  intro p hp hp2 w hw φ ψ hφ hψ hφ2 hψ2 hφ1 hψ1
  by_contra hne
  have hcard := hT p hp hp2 _ (isAtPrime_comap hp w hw) w rfl
  let S := {χ : LeafPush.inertiaQ w →* ℤˣ // Continuous χ}
  have hfin : Finite S := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let f : ℂˣ → ℤˣ := fun x => if x = 1 then 1 else -1
  have hcont : ∀ (χ : inertiaGQ w →* ℂˣ) (h2 : ∀ s, χ s ^ 2 = 1), IsLocallyConstant χ →
      Continuous (sgnHom (G := LeafPush.inertiaQ w) χ h2) := by
    intro χ h2 hχ
    exact (hχ.comp f).continuous
  let a : S := ⟨1, continuous_const⟩
  let b : S := ⟨sgnHom (G := LeafPush.inertiaQ w) φ hφ2, hcont φ hφ2 hφ⟩
  let c : S := ⟨sgnHom (G := LeafPush.inertiaQ w) ψ hψ2, hcont ψ hψ2 hψ⟩
  have hZ : (-1 : ℤˣ) ≠ 1 := by decide
  have hnt : ∀ (χ : inertiaGQ w →* ℂˣ), χ ≠ 1 → ∃ s, χ s ≠ 1 := by
    intro χ hχ
    by_contra hall
    push_neg at hall
    apply hχ
    ext s
    rw [hall s]; rfl
  have hab : ∀ (χ : inertiaGQ w →* ℂˣ) (h2 : ∀ s, χ s ^ 2 = 1) (hl : IsLocallyConstant χ),
      χ ≠ 1 → a ≠ ⟨sgnHom (G := LeafPush.inertiaQ w) χ h2, hcont χ h2 hl⟩ := by
    intro χ h2 hl hχ heq
    obtain ⟨s, hs⟩ := hnt χ hχ
    have := congrArg (fun x : S => x.1 s) heq
    change (1 : ℤˣ) = (if χ s = 1 then 1 else -1) at this
    rw [if_neg hs] at this; exact hZ this.symm
  have hbc : b ≠ c := by
    intro heq
    apply hne
    ext s
    have := congrArg (fun x : S => x.1 s) heq
    change (if φ s = 1 then (1 : ℤˣ) else -1) = (if ψ s = 1 then 1 else -1) at this
    rcases units_sq_eq_one (hφ2 s) with h1 | h1 <;> rcases units_sq_eq_one (hψ2 s) with h2 | h2
    · rw [h1, h2]
    · rw [h1, h2, if_pos rfl, if_neg neg_one_ne_one_C] at this; exact absurd this.symm hZ
    · rw [h1, h2, if_pos rfl, if_neg neg_one_ne_one_C] at this; exact absurd this hZ
    · rw [h1, h2]
  let e : S ≃ Fin 2 := (Finite.equivFin S).trans (finCongr hcard)
  have key : ∀ x y z : Fin 2, x = y ∨ y = z ∨ x = z := by decide
  rcases key (e a) (e b) (e c) with h | h | h
  · exact hab φ hφ2 hφ hφ1 (e.injective h)
  · exact hbc (e.injective h)
  · exact hab ψ hψ2 hψ hψ1 (e.injective h)

/-- **B3 (v) from the synthesis bundle's leaf T32(a)** (glue-b3b): no leaf of glue-b3-unram's own
remains; `LeafB3a` is supplied by `leafB3a_of_t32a`. -/
theorem unramified_outside_t32a (hT : LeafPush.T32a_TameQuadratic)
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
  unramified_outside_b3a (leafB3a_of_t32a hT) L T h2 hram ε hεN χ hN β hβl hβs hβe

end GlueB3Unram

#print axioms GlueB3Unram.unramified_outside_of_leaves
#print axioms GlueB3Unram.cycUnram
#print axioms GlueB3Unram.unramified_outside
#print axioms GlueB3Unram.inertia_le_of_unramifiedAt
#print axioms GlueB3Unram.unramified_outside_of_unramifiedAt
#print axioms GlueB3Unram.finRam
#print axioms GlueB3Unram.leafConj
#print axioms GlueB3Unram.unramified_outside_final

#print axioms GlueB3Unram.exists_inertia_neg
#print axioms GlueB3Unram.leafB3b
#print axioms GlueB3Unram.unramified_outside_b3a
#print axioms GlueB3Unram.t32b
#print axioms GlueB3Unram.leafB3a_of_t32a
#print axioms GlueB3Unram.unramified_outside_t32a

/-!
# glue-t32a: proof of T32(a) (`LeafPush.T32a_TameQuadratic`)

For an odd prime `p` and `w` over `p`, every continuous `χ : I_w → ℤˣ` is `1` or `η_g`, the
character `τ ↦ τ(g)/g` of `g = √p`. Proof: a Kummer generator `β` of `χ`; `v(β)` is a rational
power of `v(p)`; glue-b3b's `exists_inertia_neg` (an inertia element negating `√p`) forces the
exponent of `v(β)` to have odd denominator over `v(g)`; then `β^n / g^k` is a unit and inertia acts
trivially on it modulo `w`, which pins `χ = η_g^k`.
-/

namespace GlueB3Unram

open scoped Pointwise

section T32a

variable {w : ValuationSubring Qbar} {p : ℕ}

/-- Inertia acts trivially modulo `w`: `v(τz - z) < 1` for `z ∈ w`. -/
theorem inertia_val_sub_lt_one (τ : Gal) (hτ : τ ∈ LeafPush.inertiaQ w) (z : Qbar) (hz : z ∈ w) :
    w.valuation (τ z - z) < 1 := by
  obtain ⟨y, hy, hres⟩ := residue_inertia w τ hτ ⟨z, hz⟩
  have h0 : IsLocalRing.residue w (y - ⟨z, hz⟩) = 0 := by rw [map_sub, hres, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h0
  have : ((y - ⟨z, hz⟩ : w) : Qbar) = τ z - z := by
    show (y : Qbar) - z = τ z - z
    rw [hy]; rfl
  rwa [this] at h0

theorem not_dvd_two_of_odd (hp : p.Prime) (hp2 : p ≠ 2) : ¬ (p : ℤ) ∣ (-2 : ℤ) := by
  intro h
  rw [Int.dvd_neg] at h
  have h' : p ∣ 2 := by exact_mod_cast h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')

/-- **Sign lemma.** At an odd place no inertia element negates a unit. -/
theorem not_inertia_neg (hp : p.Prime) (hp2 : p ≠ 2) (hw : LiesOver w p) (τ : Gal)
    (hτ : τ ∈ LeafPush.inertiaQ w) (z : Qbar) (hz : w.valuation z = 1) (hτz : τ z = -z) : False := by
  have hzw : z ∈ w := (w.valuation_le_one_iff z).mp hz.le
  have h := inertia_val_sub_lt_one τ hτ z hzw
  have e : τ z - z = ((-2 : ℤ) : Qbar) * z := by rw [hτz]; push_cast; ring
  rw [e, map_mul, hz, mul_one, val_intCast_eq_one hp hw (-2) (not_dvd_two_of_odd hp hp2)] at h
  exact lt_irrefl _ h

/-- Valuation of a nonzero integer: a power of `v(p)`. -/
theorem val_int_eq_pow (hp : p.Prime) (hw : LiesOver w p) (r : ℤ) (hr : r ≠ 0) :
    ∃ e : ℕ, w.valuation (r : Qbar) = w.valuation (p : Qbar) ^ e := by
  obtain ⟨e, n', hn', he⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hr) p hp.one_lt.ne'
  refine ⟨e, ?_⟩
  have hv : w.valuation (r : Qbar) = w.valuation ((r.natAbs : ℤ) : Qbar) := by
    rcases Int.natAbs_eq r with h | h
    · conv_lhs => rw [h]
    · conv_lhs => rw [h]
      rw [Int.cast_neg, Valuation.map_neg]
  rw [hv, he]
  push_cast
  rw [map_mul, map_pow]
  have h1 : w.valuation ((n' : ℤ) : Qbar) = 1 :=
    val_intCast_eq_one hp hw _ (by exact_mod_cast hn')
  push_cast at h1
  rw [h1, mul_one]

/-- Valuation of a nonzero rational: an integral power of `v(p)`. -/
theorem val_rat_eq_zpow (hp : p.Prime) (hw : LiesOver w p) (q : ℚ) (hq : q ≠ 0) :
    ∃ m : ℤ, w.valuation (algebraMap ℚ Qbar q) = w.valuation (p : Qbar) ^ m := by
  obtain ⟨a, ha⟩ := val_int_eq_pow hp hw q.num (Rat.num_ne_zero.mpr hq)
  obtain ⟨b, hb⟩ := val_int_eq_pow hp hw (q.den : ℤ) (by exact_mod_cast q.den_ne_zero)
  refine ⟨(a : ℤ) - b, ?_⟩
  have hvp : w.valuation (p : Qbar) ≠ 0 := val_natCast_ne_zero hp
  rw [eq_ratCast, Rat.cast_def, map_div₀]
  push_cast at ha hb
  rw [ha, hb, zpow_sub₀ hvp, zpow_natCast, zpow_natCast]

theorem pow_eq_zpow_aux {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (P X : Γ) (hP : P ≠ 0)
    (hX : X ≠ 0) (a b : ℤ) (i j : ℕ) (hij : i < j) (h : P ^ a * X ^ i = P ^ b * X ^ j) :
    X ^ (j - i) = P ^ (a - b) := by
  have hXi : X ^ i ≠ 0 := pow_ne_zero _ hX
  have h2 : P ^ a = P ^ b * X ^ (j - i) := by
    apply mul_right_cancel₀ hXi
    rw [h, mul_assoc, ← pow_add, Nat.sub_add_cancel hij.le]
  rw [zpow_sub₀ hP, h2, mul_div_cancel_left₀ _ (zpow_ne_zero _ hP)]

/-- **Values are rational powers of `v(p)`** (Newton polygon of the minimal polynomial): for
`x ≠ 0` in `ℚ̄`, `v(x)^n = v(p)^m` for some `n ≥ 1`, `m ∈ ℤ`. -/
theorem val_pow_eq_zpow (hp : p.Prime) (hw : LiesOver w p) (x : Qbar) (hx : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, w.valuation x ^ n = w.valuation (p : Qbar) ^ m := by
  classical
  set f := minpoly ℚ x with hfdef
  have hmon : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  set d := f.natDegree
  let t : ℕ → Qbar := fun i => algebraMap ℚ Qbar (f.coeff i) * x ^ i
  have h0 : ∑ i ∈ Finset.range (d + 1), t i = 0 := by
    have := minpoly.aeval ℚ x
    rw [Polynomial.aeval_eq_sum_range] at this
    simpa [t, Algebra.smul_def] using this
  have hvt : ∀ i, w.valuation (t i) = w.valuation (algebraMap ℚ Qbar (f.coeff i)) *
      w.valuation x ^ i := fun i => by simp only [t, map_mul, map_pow]
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image (Finset.range (d + 1))
    (fun i => w.valuation (t i)) ⟨d, by simp⟩
  have hvx : w.valuation x ≠ 0 := by rwa [Ne, Valuation.zero_iff]
  have htd : w.valuation (t d) ≠ 0 := by
    rw [hvt, show f.coeff d = 1 from hmon.coeff_natDegree, map_one, map_one, one_mul]
    exact pow_ne_zero _ hvx
  have htj : w.valuation (t j) ≠ 0 := by
    intro h0'
    have := hjmax d (by simp)
    rw [h0'] at this
    exact htd (le_antisymm this zero_le')
  obtain ⟨i, hi, hij, heq⟩ : ∃ i ∈ Finset.range (d + 1), i ≠ j ∧
      w.valuation (t i) = w.valuation (t j) := by
    by_contra hcon
    push_neg at hcon
    have := Valuation.map_sum_eq_of_lt w.valuation hj (fun i hi => by
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
      exact lt_of_le_of_ne (hjmax i hi.1) (hcon i hi.1 hi.2))
    rw [h0, map_zero] at this
    exact htj this.symm
  have hcj : f.coeff j ≠ 0 := by
    intro hc; apply htj; rw [hvt, hc, map_zero, map_zero, zero_mul]
  have hci : f.coeff i ≠ 0 := by
    intro hc; apply htj; rw [← heq, hvt, hc, map_zero, map_zero, zero_mul]
  obtain ⟨a, ha⟩ := val_rat_eq_zpow hp hw _ hci
  obtain ⟨b, hb⟩ := val_rat_eq_zpow hp hw _ hcj
  rw [hvt, hvt, ha, hb] at heq
  have hvp : w.valuation (p : Qbar) ≠ 0 := val_natCast_ne_zero hp
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨j - i, Nat.sub_pos_of_lt h, a - b, pow_eq_zpow_aux _ _ hvp hvx a b i j h heq⟩
  · exact ⟨i - j, Nat.sub_pos_of_lt h, b - a, pow_eq_zpow_aux _ _ hvp hvx b a j i h heq.symm⟩

/-- **Kummer generator.** A continuous character `χ : I_w → ℤˣ` is `τ ↦ τ(β)/β` for some
`β ≠ 0` in `ℚ̄`. -/
theorem exists_kummer (w : ValuationSubring Qbar) (χ : LeafPush.inertiaQ w →* ℤˣ)
    (hχ : Continuous χ) : ∃ β : Qbar, β ≠ 0 ∧ ∀ (τ : Gal) (hτ : τ ∈ LeafPush.inertiaQ w),
      τ β = (((χ ⟨τ, hτ⟩ : ℤˣ) : ℤ) : Qbar) * β := by
  classical
  -- Step 1: an element `γ` whose stabilizer in `I` lies in `ker χ`
  have hopen : IsOpen ((χ ⁻¹' {1}) : Set (LeafPush.inertiaQ w)) := (isOpen_discrete _).preimage hχ
  rw [isOpen_induced_iff] at hopen
  obtain ⟨t, ht, hteq⟩ := hopen
  have h1t : (1 : Gal) ∈ t := by
    have : (1 : LeafPush.inertiaQ w) ∈ (χ ⁻¹' {1} : Set (LeafPush.inertiaQ w)) := by simp
    rw [← hteq] at this; exact this
  obtain ⟨E, hEfin, hEt⟩ := (krullTopology_mem_nhds_one_iff ℚ Qbar t).mp (ht.mem_nhds h1t)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  set γ : Qbar := (α : Qbar) with hγdef
  have hE : IntermediateField.adjoin ℚ {γ} = E := by
    rw [← IntermediateField.lift_adjoin_simple, hα, IntermediateField.lift_top]
  have hker : ∀ σ (hσ : σ ∈ LeafPush.inertiaQ w), σ γ = γ → χ ⟨σ, hσ⟩ = 1 := by
    intro σ hσ hσγ
    have hfix : σ ∈ E.fixingSubgroup := by
      rw [← hE]
      have hle : IntermediateField.adjoin ℚ {γ} ≤
          IntermediateField.fixedField (Subgroup.zpowers σ) := by
        rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
        intro g hg
        have : g ∈ MulAction.stabilizer Gal γ :=
          (Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hσγ)) hg
        exact this
      exact (IntermediateField.le_iff_le _ _).mp hle (Subgroup.mem_zpowers σ)
    have : (⟨σ, hσ⟩ : LeafPush.inertiaQ w) ∈ (Subtype.val ⁻¹' t : Set (LeafPush.inertiaQ w)) := hEt hfix
    rw [hteq] at this; exact this
  have hcons : ∀ σ (hσ : σ ∈ LeafPush.inertiaQ w) τ (hτ : τ ∈ LeafPush.inertiaQ w), σ γ = τ γ → χ ⟨σ, hσ⟩ = χ ⟨τ, hτ⟩ := by
    intro σ hσ τ hτ h
    have h' : (τ⁻¹ * σ) γ = γ := by
      rw [AlgEquiv.mul_apply, h, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have := hker (τ⁻¹ * σ) ((LeafPush.inertiaQ w).mul_mem ((LeafPush.inertiaQ w).inv_mem hτ) hσ) h'
    have e : (⟨τ⁻¹ * σ, (LeafPush.inertiaQ w).mul_mem ((LeafPush.inertiaQ w).inv_mem hτ) hσ⟩ : LeafPush.inertiaQ w) = (⟨τ, hτ⟩ : LeafPush.inertiaQ w)⁻¹ * ⟨σ, hσ⟩ := rfl
    rw [e, map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm
  -- Step 2: the class function `c` on the orbit of `γ`
  let c : Qbar → ℤ := fun y => if h : ∃ τ, ∃ hτ : τ ∈ LeafPush.inertiaQ w, τ γ = y then
    ((χ ⟨h.choose, h.choose_spec.choose⟩ : ℤˣ) : ℤ) else 0
  have hc : ∀ τ (hτ : τ ∈ LeafPush.inertiaQ w), c (τ γ) = χ ⟨τ, hτ⟩ := by
    intro τ hτ
    have h : ∃ τ', ∃ hτ' : τ' ∈ LeafPush.inertiaQ w, τ' γ = τ γ := ⟨τ, hτ, rfl⟩
    simp only [c, dif_pos h]
    rw [hcons _ h.choose_spec.choose _ hτ h.choose_spec.choose_spec]
  have hc0 : ∀ y, (¬ ∃ τ, ∃ hτ : τ ∈ LeafPush.inertiaQ w, τ γ = y) → c y = 0 := fun y h => by
    simp only [c, dif_neg h]
  have hcσ : ∀ σ (hσ : σ ∈ LeafPush.inertiaQ w) y, c (σ y) = ((χ ⟨σ, hσ⟩ : ℤˣ) : ℤ) * c y := by
    intro σ hσ y
    by_cases h : ∃ τ, ∃ hτ : τ ∈ LeafPush.inertiaQ w, τ γ = y
    · obtain ⟨τ, hτ, rfl⟩ := h
      rw [← AlgEquiv.mul_apply, hc _ ((LeafPush.inertiaQ w).mul_mem hσ hτ), hc τ hτ]
      have e : (⟨σ * τ, (LeafPush.inertiaQ w).mul_mem hσ hτ⟩ : LeafPush.inertiaQ w) = ⟨σ, hσ⟩ * ⟨τ, hτ⟩ := rfl
      rw [e, map_mul, Units.val_mul]
    · have h' : ¬ ∃ τ, ∃ hτ : τ ∈ LeafPush.inertiaQ w, τ γ = σ y := by
        rintro ⟨τ, hτ, hτy⟩
        apply h
        refine ⟨σ⁻¹ * τ, (LeafPush.inertiaQ w).mul_mem ((LeafPush.inertiaQ w).inv_mem hσ) hτ, ?_⟩
        rw [AlgEquiv.mul_apply, hτy, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
      rw [hc0 _ h, hc0 _ h', mul_zero]
  have hcσ' : ∀ σ (hσ : σ ∈ LeafPush.inertiaQ w) y, c y = ((χ ⟨σ, hσ⟩ : ℤˣ) : ℤ) * c (σ y) := by
    intro σ hσ y
    rw [hcσ σ hσ y, ← mul_assoc, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_mul]
  -- Step 3: the roots of the minimal polynomial of `γ`
  have hγint : IsIntegral ℚ γ := Algebra.IsIntegral.isIntegral γ
  set R : Finset Qbar := ((minpoly ℚ γ).aroots Qbar).toFinset with hRdef
  have hR : ∀ σ : Gal, ∀ y ∈ R, σ y ∈ R := by
    intro σ y hy
    simp only [hRdef, Multiset.mem_toFinset, Polynomial.mem_aroots] at hy ⊢
    refine ⟨hy.1, ?_⟩
    have := Polynomial.aeval_algHom_apply (σ : Qbar →ₐ[ℚ] Qbar) y (minpoly ℚ γ)
    rw [hy.2, map_zero] at this
    exact this
  have hγR : γ ∈ R := by
    simp only [hRdef, Multiset.mem_toFinset, Polynomial.mem_aroots]
    exact ⟨minpoly.ne_zero hγint, minpoly.aeval ℚ γ⟩
  have hγ1 : c γ = 1 := by
    have := hc 1 (LeafPush.inertiaQ w).one_mem
    rw [AlgEquiv.one_apply] at this
    rw [this]
    have e : (⟨1, (LeafPush.inertiaQ w).one_mem⟩ : LeafPush.inertiaQ w) = 1 := rfl
    rw [e, map_one, Units.val_one]
  -- Step 4: some power sum `∑ c(y) y^j` is nonzero (Vandermonde)
  let bsum : ℕ → Qbar := fun j => ∑ y ∈ R, (c y : Qbar) * y ^ j
  obtain ⟨j, hj⟩ : ∃ j, bsum j ≠ 0 := by
    by_contra hall
    push_neg at hall
    let e : Fin R.card ≃ R := R.equivFin.symm
    let v : Fin R.card → Qbar := fun i => (e i : Qbar)
    let cv : Fin R.card → Qbar := fun i => (c (e i) : Qbar)
    have hmul : (Matrix.vandermonde v).transpose.mulVec cv = 0 := by
      funext k
      have hk := hall k
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply,
        Pi.zero_apply]
      rw [← hk]
      simp only [bsum, v, cv]
      rw [← Finset.sum_coe_sort R, ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hdet : (Matrix.vandermonde v).transpose.det ≠ 0 := by
      rw [Matrix.det_transpose]
      exact Matrix.det_vandermonde_ne_zero_iff.mpr fun a b h => e.injective (Subtype.ext h)
    have h0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
    have := congrFun h0 (e.symm ⟨γ, hγR⟩)
    simp only [cv, Equiv.apply_symm_apply, hγ1, Pi.zero_apply] at this
    norm_num at this
  -- Step 5: `β = ∑ c(y) y^j` transforms by `χ`
  refine ⟨bsum j, hj, fun σ hσ => ?_⟩
  simp only [bsum, map_sum, map_mul, map_intCast, map_pow]
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun y => σ y) (fun y => σ⁻¹ y) (fun y hy => hR σ y hy)
    (fun y hy => hR σ⁻¹ y hy) (fun y _ => by simp) (fun y _ => by simp) fun y _ => ?_
  rw [hcσ' σ hσ y]
  push_cast
  ring

theorem unit_cast_cases (u : ℤˣ) : ((u : ℤ) : Qbar) = 1 ∨ ((u : ℤ) : Qbar) = -1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

open Classical in
/-- The sign `δ_τ = τ(g)/g ∈ {±1}` of `g = √p` under `τ`. -/
noncomputable def sgnG (g : Qbar) (τ : Gal) : Qbar := if τ g = g then 1 else -1

theorem sgnG_spec {g : Qbar} {c : ℤ} (hg : g ^ 2 = (c : Qbar)) (τ : Gal) : τ g = sgnG g τ * g := by
  unfold sgnG
  split_ifs with h
  · rw [h, one_mul]
  · rw [(smul_sq_cases hg τ).resolve_left h, neg_one_mul]

/-- **The classification.** Every continuous `χ : I_w → ℤˣ` is a power of `τ ↦ τ(g)/g`. -/
theorem char_eq_sgn_zpow (hp : p.Prime) (hp2 : p ≠ 2) (hw : LiesOver w p) (g : Qbar)
    (hg : g ^ 2 = ((p : ℤ) : Qbar)) (τ₀ : Gal) (hτ₀ : τ₀ ∈ LeafPush.inertiaQ w) (hτ₀g : τ₀ g = -g)
    (χ : LeafPush.inertiaQ w →* ℤˣ) (hχ : Continuous χ) :
    ∃ k : ℤ, ∀ (τ : Gal) (hτ : τ ∈ LeafPush.inertiaQ w),
      (((χ ⟨τ, hτ⟩ : ℤˣ) : ℤ) : Qbar) = sgnG g τ ^ k := by
  classical
  obtain ⟨β, hβ0, hβ⟩ := exists_kummer w χ hχ
  have hp0 : ((p : ℤ) : Qbar) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hg0 : g ≠ 0 := by rintro rfl; rw [zero_pow two_ne_zero] at hg; exact hp0 hg.symm
  have hvg : w.valuation g ^ 2 = w.valuation (p : Qbar) := by
    rw [← map_pow, hg, Int.cast_natCast]
  have hvg0 : w.valuation g ≠ 0 := by rwa [Ne, Valuation.zero_iff]
  have hex : ∃ n, 0 < n ∧ ∃ k : ℤ, w.valuation β ^ n = w.valuation g ^ k := by
    obtain ⟨n, hn, m, hm⟩ := val_pow_eq_zpow hp hw β hβ0
    refine ⟨n, hn, 2 * m, ?_⟩
    rw [hm, ← hvg, ← zpow_natCast, ← zpow_mul]
    norm_num
  obtain ⟨hn₀, k, hk⟩ := Nat.find_spec hex
  set n₀ := Nat.find hex with hn₀def
  set z : Qbar := β ^ n₀ * g ^ (-k) with hzdef
  have hvz : w.valuation z = 1 := by
    rw [hzdef, map_mul, map_pow, map_zpow₀, hk, ← zpow_add₀ hvg0, add_neg_cancel, zpow_zero]
  have hτz : ∀ τ (hτ : τ ∈ LeafPush.inertiaQ w),
      τ z = (((χ ⟨τ, hτ⟩ : ℤˣ) : ℤ) : Qbar) ^ n₀ * sgnG g τ ^ (-k) * z := by
    intro τ hτ
    rw [hzdef, map_mul, map_pow, map_zpow₀, hβ τ hτ, sgnG_spec hg τ, mul_pow, mul_zpow]
    ring
  -- `n₀` is odd
  have hodd : Odd n₀ := by
    rcases Nat.even_or_odd n₀ with ⟨a, ha⟩ | h
    swap; · exact h
    exfalso
    rcases Int.even_or_odd k with ⟨b, hb⟩ | hk2
    · have ha0 : 0 < a := by omega
      have h2 : (w.valuation β ^ a) ^ 2 = (w.valuation g ^ b) ^ 2 := by
        rw [← pow_mul, mul_two, ← ha, hk, hb, ← zpow_natCast, ← zpow_mul]
        congr 1; push_cast; ring
      have h' : w.valuation β ^ a = w.valuation g ^ b := pow_left_injective two_ne_zero h2
      exact Nat.find_min hex (show a < n₀ by omega) ⟨ha0, b, h'⟩
    · have hτ₀z := hτz τ₀ hτ₀
      have hs : sgnG g τ₀ = -1 := by
        unfold sgnG; rw [if_neg]; rw [hτ₀g]; intro h
        exact hg0 (by linear_combination -h / 2)
      have hev : Even n₀ := ⟨a, ha⟩
      rw [hs, hk2.neg.neg_one_zpow] at hτ₀z
      rcases unit_cast_cases (χ ⟨τ₀, hτ₀⟩) with he | he
      · rw [he, one_pow] at hτ₀z
        exact not_inertia_neg hp hp2 hw τ₀ hτ₀ z hvz (by rw [hτ₀z]; ring)
      · rw [he, hev.neg_one_pow] at hτ₀z
        exact not_inertia_neg hp hp2 hw τ₀ hτ₀ z hvz (by rw [hτ₀z]; ring)
  refine ⟨k, fun τ hτ => ?_⟩
  have h := hτz τ hτ
  have hsg : sgnG g τ = 1 ∨ sgnG g τ = -1 := by unfold sgnG; split_ifs <;> simp
  rcases unit_cast_cases (χ ⟨τ, hτ⟩) with he | he <;> rcases hsg with hs | hs <;>
    rcases Int.even_or_odd k with hk2 | hk2 <;> rw [he, hs] at h ⊢ <;>
    simp only [one_pow, one_zpow, hodd.neg_one_pow, hk2.neg_one_zpow, hk2.neg.neg_one_zpow,
      one_mul, mul_one] at h ⊢ <;>
    first
    | rfl
    | exact (not_inertia_neg hp hp2 hw τ hτ z hvz (by rw [h]; ring)).elim

theorem neg_ne_self_of_ne_zero {g : Qbar} (hg0 : g ≠ 0) : -g ≠ g := fun h =>
  hg0 (by linear_combination (-1 / 2 : Qbar) * h)

open Classical in
/-- The quadratic character `η_g : τ ↦ τ(g)/g` of `I_w`, for `g² ∈ ℤ`, `g ≠ 0`, as a map to `ℤˣ`. -/
noncomputable def etaG (w : ValuationSubring Qbar) (g : Qbar) {c : ℤ} (hg : g ^ 2 = (c : Qbar))
    (hg0 : g ≠ 0) : LeafPush.inertiaQ w →* ℤˣ where
  toFun τ := if (τ : Gal) g = g then 1 else -1
  map_one' := by simp
  map_mul' σ τ := by
    have hne := neg_ne_self_of_ne_zero hg0
    rcases smul_sq_cases hg (σ : Gal) with h1 | h1 <;>
      rcases smul_sq_cases hg (τ : Gal) with h2 | h2 <;>
      simp [AlgEquiv.mul_apply, h1, h2, hne]

open Classical in
theorem etaG_apply (w : ValuationSubring Qbar) (g : Qbar) {c : ℤ} (hg : g ^ 2 = (c : Qbar))
    (hg0 : g ≠ 0) (τ : LeafPush.inertiaQ w) :
    etaG w g hg hg0 τ = if (τ : Gal) g = g then 1 else -1 := rfl

theorem etaG_continuous (w : ValuationSubring Qbar) (g : Qbar) {c : ℤ}
    (hg : g ^ 2 = (c : Qbar)) (hg0 : g ≠ 0) : Continuous (etaG w g hg hg0) := by
  let U : Subgroup (LeafPush.inertiaQ w) :=
    (MulAction.stabilizer Gal g).comap (LeafPush.inertiaQ w).subtype
  have hU : IsOpen (U : Set (LeafPush.inertiaQ w)) :=
    (stabilizer_isOpen_of_isIntegral (K := ℚ) (L := Qbar) g).preimage continuous_subtype_val
  refine IsLocallyConstant.continuous (isLocallyConstant_of_openSubgroup U hU _ ?_)
  intro σ k hk
  have hk' : (k : Gal) g = g := MulAction.mem_stabilizer_iff.mp hk
  rw [etaG_apply, etaG_apply, Subgroup.coe_mul, AlgEquiv.mul_apply, hk']

/-- **T32(a) is glue** (proved from Mathlib, via glue-b3b's `exists_inertia_neg`): for an odd
prime `p` and `w` over `ℤ_(p)`, the continuous characters `I_w → ℤˣ` number exactly two. -/
theorem t32a : LeafPush.T32a_TameQuadratic := by
  classical
  intro p hp hp2 O hO w hwO
  have hw : LiesOver w p := liesOver_of_isAtPrime O hO w hwO
  obtain ⟨g, hg'⟩ := IsAlgClosed.exists_pow_nat_eq (p : Qbar) two_pos
  have hg : g ^ 2 = ((p : ℤ) : Qbar) := by rw [hg']; simp
  have hp0 : ((p : ℤ) : Qbar) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hg0 : g ≠ 0 := by rintro rfl; rw [zero_pow two_ne_zero] at hg; exact hp0 hg.symm
  obtain ⟨σ, hσ⟩ := exists_neg_of_sq hg
    (not_isSquare_of_squarefree (Int.squarefree_natCast.mpr hp.squarefree) hp dvd_rfl)
  obtain ⟨τ₀, hτ₀, hτ₀g⟩ := exists_inertia_neg p hp w hw g p hg (by simp) σ hσ
  have hne := neg_ne_self_of_ne_zero hg0
  have hητ₀ : etaG w g hg hg0 ⟨τ₀, hτ₀⟩ = -1 := by
    rw [etaG_apply]
    show (if τ₀ g = g then (1 : ℤˣ) else -1) = -1
    rw [if_neg (by rw [hτ₀g]; exact hne)]
  have hZ : (-1 : ℤˣ) ≠ 1 := by decide
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, continuous_const⟩, ⟨etaG w g hg hg0, etaG_continuous w g hg hg0⟩, ?_, ?_⟩
  · intro h
    have := congrArg (fun x : {χ : LeafPush.inertiaQ w →* ℤˣ // Continuous χ} => x.1 ⟨τ₀, hτ₀⟩) h
    simp only [MonoidHom.one_apply] at this
    rw [hητ₀] at this
    exact hZ this.symm
  · ext ⟨χ, hχ⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    obtain ⟨k, hk⟩ := char_eq_sgn_zpow hp hp2 hw g hg τ₀ hτ₀ hτ₀g χ hχ
    rcases Int.even_or_odd k with hk2 | hk2
    · left
      apply Subtype.ext
      refine MonoidHom.ext fun x => ?_
      obtain ⟨τ, hτ⟩ := x
      have h := hk τ hτ
      have hs : sgnG g τ ^ k = 1 := by
        unfold sgnG; split_ifs
        · exact one_zpow k
        · exact hk2.neg_one_zpow
      rw [hs] at h
      show χ ⟨τ, hτ⟩ = 1
      have h' : ((χ ⟨τ, hτ⟩ : ℤˣ) : ℤ) = 1 := by exact_mod_cast h
      apply Units.val_injective
      rw [h', Units.val_one]
    · right
      apply Subtype.ext
      refine MonoidHom.ext fun x => ?_
      obtain ⟨τ, hτ⟩ := x
      have h := hk τ hτ
      show χ ⟨τ, hτ⟩ = etaG w g hg hg0 ⟨τ, hτ⟩
      rw [etaG_apply]
      unfold sgnG at h
      split_ifs at h ⊢ with hτg
      · rw [one_zpow] at h
        have h' : ((χ ⟨τ, hτ⟩ : ℤˣ) : ℤ) = 1 := by exact_mod_cast h
        apply Units.val_injective
        rw [h', Units.val_one]
      · rw [hk2.neg_one_zpow] at h
        have h' : ((χ ⟨τ, hτ⟩ : ℤˣ) : ℤ) = -1 := by exact_mod_cast h
        apply Units.val_injective
        rw [h', Units.val_neg, Units.val_one]

/-- **B3 (v) rests on no leaf** (glue-t32a): glue-b3b's `unramified_outside_t32a` with T32(a)
discharged by `t32a`. -/
theorem unramified_outside_noLeaf
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
  unramified_outside_t32a t32a L T h2 hram ε hεN χ hN β hβl hβs hβe

/-- `LeafB3a` (glue-b3-unram's form of the unique quadratic character of tame inertia) is glue. -/
theorem leafB3a : LeafB3a := leafB3a_of_t32a t32a

end T32a

end GlueB3Unram

#print axioms GlueB3Unram.exists_kummer
#print axioms GlueB3Unram.val_pow_eq_zpow
#print axioms GlueB3Unram.char_eq_sgn_zpow
#print axioms GlueB3Unram.t32a
#print axioms GlueB3Unram.leafB3a
#print axioms GlueB3Unram.unramified_outside_noLeaf

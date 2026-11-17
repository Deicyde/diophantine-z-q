import Mathlib

/-!
# Lane RC16-uniform: the common kernel and finite realization of a rank-two test

This file formalizes the algebra in the proof of the manuscript lemma
`ex:limits-kernel-detection` ("The common kernel and finite realization of a rank-two test",
tex lines 4747-4831), part of Elliot Glazer's proof of Theorem 5.3.

The proof (tex lines 4765-4831) has four algebraic steps, formalized here in order.

1. (tex 4766-4777) *The kernel argument.* `H` is the exact kernel (acting trivially), `z` is the
   scalar element, central modulo `H`, acting by the scalar `μ` (`μ = u⁴` in the manuscript).
   For a cocycle `b` zero on the kernel, "`(u^4-1)b(g)=(g-1)b(z)`" (`cocycle_scalar_identity`), so
   `b` is a coboundary when `u⁴ - 1` is invertible (`coboundary_of_vanishes_on_kernel`).
   Hence restriction to the kernel is injective on `H¹` (`isCoboundary_sub_of_restriction_eq`,
   and in Mathlib's group cohomology `H1π_eq_iff_restriction_eq`). Restrictions of cocycles to
   the kernel are additive and conjugation-equivariant (`restriction_additive`,
   `restriction_equivariant`); coboundaries vanish there (`coboundary_vanishes_on_kernel`).
   The separate residual argument "its scalar difference is `t`, invertible in `𝔽₂((t))`" is
   `invariants_eq_zero_of_scalar`.
2. (tex 4782-4792) *Goursat.* For an irreducible module with scalar endomorphisms, a submodule
   of `W × W` with both projections onto is everything or the graph of a scalar isomorphism
   (`submodule_prod_eq_top_or_graph`). Hence the span of the joint values of two independent
   classes on the kernel is the full sum (`joint_span_eq_top`).
3. (tex 4792-4799) *Polarization.* A quadratic map vanishing on the values of an additive map
   vanishes on their span, in every characteristic (`quadratic_vanishes_on_span`); so one actual
   kernel element supplies a rank-two localization (`exists_rank_two_localization`). The three
   steps are assembled in `kernel_element_detects_two_classes`.
4. (tex 4809-4831) *Finite Chebotarev and (5.4).* The arithmetic content of (5.4) is an input,
   recorded as the interface `ExactChebotarevRealization`. The step "Only afterward compose with
   the inclusion `I_j`" is the algebra `matrix_identity_mul_inclusion`.

Kinds used in the docstrings: `PROVED` (Lean proof); `ELLIOT/PRINT` (an input stated as an
interface and not proved here: finite Chebotarev and the inner-limit exactness behind (5.4)).
The namespace `NonVacuity` contains models showing that the hypotheses are satisfiable.
-/

namespace ZInQ.Manuscript.RC.Uniform

universe u

/-! ## Step 1: cocycles, the exact kernel and the scalar element (tex 4766-4777) -/

section Cocycles

variable {k G W : Type*} [CommRing k] [Group G] [AddCommGroup W] [Module k W]

/-- An inhomogeneous 1-cocycle (crossed homomorphism) for the representation `ρ`:
`b(gh) = b(g) + g·b(h)`. The equivalence with Mathlib's `groupCohomology.cocycles₁` is
`isCocycle_iff_mem_cocycles₁`. -/
def IsCocycle (ρ : Representation k G W) (b : G → W) : Prop :=
  ∀ g h : G, b (g * h) = b g + ρ g (b h)

/-- A 1-coboundary: `b(g) = (g - 1) w` for one fixed `w`. The equivalence with Mathlib's
`groupCohomology.coboundaries₁` is `isCoboundary_iff_mem_coboundaries₁`. -/
def IsCoboundary (ρ : Representation k G W) (b : G → W) : Prop :=
  ∃ w : W, ∀ g : G, b g = ρ g w - w

variable {ρ : Representation k G W}

namespace IsCocycle

/-- A cocycle vanishes at `1`. Kind: PROVED. -/
theorem map_one {b : G → W} (hb : IsCocycle ρ b) : b 1 = 0 := by
  have h := hb 1 1
  rw [mul_one, _root_.map_one, Module.End.one_apply] at h
  simpa using h

/-- `g·b(g⁻¹) = -b(g)` for a cocycle. Kind: PROVED. -/
theorem map_inv {b : G → W} (hb : IsCocycle ρ b) (g : G) : ρ g (b g⁻¹) = -b g := by
  have h := hb g g⁻¹
  rw [mul_inv_cancel, hb.map_one] at h
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h.symm

/-- Cocycles are closed under addition. Kind: PROVED. -/
theorem add {b₁ b₂ : G → W} (h₁ : IsCocycle ρ b₁) (h₂ : IsCocycle ρ b₂) :
    IsCocycle ρ (b₁ + b₂) := by
  intro g h
  simp only [Pi.add_apply, h₁ g h, h₂ g h, map_add]
  abel

/-- Cocycles are closed under scalars. Kind: PROVED. -/
theorem smul (a : k) {b : G → W} (hb : IsCocycle ρ b) : IsCocycle ρ (a • b) := by
  intro g h
  simp only [Pi.smul_apply, hb g h, smul_add, map_smul]

/-- Cocycles are closed under subtraction. Kind: PROVED. -/
theorem sub {b₁ b₂ : G → W} (h₁ : IsCocycle ρ b₁) (h₂ : IsCocycle ρ b₂) :
    IsCocycle ρ (b₁ - b₂) := by
  intro g h
  simp only [Pi.sub_apply, h₁ g h, h₂ g h, map_sub]
  abel

end IsCocycle

/-- A coboundary is a cocycle. Kind: PROVED. -/
theorem IsCoboundary.isCocycle {b : G → W} (hb : IsCoboundary ρ b) : IsCocycle ρ b := by
  obtain ⟨w, hw⟩ := hb
  intro g h
  rw [hw, hw, hw, map_mul, Module.End.mul_apply, map_sub]
  abel

/-- **Restriction to the kernel is additive** (tex 4794, "additivity"; tex 5099, "additivity on
`H`").

Kind: PROVED. `H` is the exact kernel: every `h ∈ H` acts trivially. For a cocycle `c`,
`c(h₁h₂) = c(h₁) + c(h₂)` for `h₁, h₂ ∈ H`. -/
theorem restriction_additive (H : Subgroup G) (hH : ∀ h ∈ H, ∀ w : W, ρ h w = w)
    {c : G → W} (hc : IsCocycle ρ c) :
    ∀ h₁ ∈ H, ∀ h₂ ∈ H, c (h₁ * h₂) = c h₁ + c h₂ := by
  intro h₁ hh₁ h₂ _
  rw [hc h₁ h₂, hH h₁ hh₁]

/-- **Restriction to the kernel is equivariant** (used at tex 4788-4792: the joint values on the
exact kernel span a `k[G]`-submodule).

Kind: PROVED. For a cocycle `c` and `h` in the trivially acting subgroup `H`,
`c(g h g⁻¹) = g·c(h)`. -/
theorem restriction_equivariant (H : Subgroup G) (hH : ∀ h ∈ H, ∀ w : W, ρ h w = w)
    {c : G → W} (hc : IsCocycle ρ c) :
    ∀ h ∈ H, ∀ g : G, c (g * h * g⁻¹) = ρ g (c h) := by
  intro h hh g
  rw [hc (g * h) g⁻¹, hc g h, map_mul, Module.End.mul_apply, hH h hh, hc.map_inv]
  abel

/-- **Coboundaries vanish on the kernel** (tex 5099-5100, "a coboundary is zero on `H`").

Kind: PROVED. `(h - 1) w = 0` for `h` in the trivially acting subgroup `H`. -/
theorem coboundary_vanishes_on_kernel (H : Subgroup G) (hH : ∀ h ∈ H, ∀ w : W, ρ h w = w)
    (w : W) : ∀ h ∈ H, ρ h w - w = 0 := by
  intro h hh
  rw [hH h hh, sub_self]

/-- A coboundary vanishes on the trivially acting subgroup `H` (tex 5099-5100). Kind: PROVED. -/
theorem IsCoboundary.vanishes_on_kernel (H : Subgroup G) (hH : ∀ h ∈ H, ∀ w : W, ρ h w = w)
    {b : G → W} (hb : IsCoboundary ρ b) : ∀ h ∈ H, b h = 0 := by
  obtain ⟨w, hw⟩ := hb
  intro h hh
  rw [hw, coboundary_vanishes_on_kernel H hH w h hh]

/-- **The scalar identity** (tex 4766-4773):
"For a cocycle zero on the kernel, `(u^4-1)b(g)=(g-1)b(z)`."

Kind: PROVED. `H` is the exact kernel (every `h ∈ H` acts trivially); `z` is "central modulo
this kernel, though not in the kernel itself" (`z g z⁻¹ g⁻¹ ∈ H` for all `g`) and acts by the
scalar `μ` (in the manuscript `ρ(z) = u⁴I`, so `μ = u⁴`). For a cocycle `b` zero on `H`:
`(μ - 1) • b g = ρ g (b z) - b z`.

DEPARTURE: the arithmetic objects (the exact kernel of sequences; the scalar element
`z = g²τg²τ⁻¹` of (H1), tex 2884-2892, with `ρ_T(z) = u⁴I`) are replaced by abstract hypotheses
on a subgroup `H` and an element `z`; the scalar `u⁴` is a general `μ : k`. Normality of `H` is
not needed for this identity. -/
theorem cocycle_scalar_identity (H : Subgroup G) (hH : ∀ h ∈ H, ∀ w : W, ρ h w = w)
    (z : G) (hz : ∀ g : G, z * g * z⁻¹ * g⁻¹ ∈ H) (μ : k) (hμ : ρ z = μ • LinearMap.id)
    {b : G → W} (hb : IsCocycle ρ b) (hbH : ∀ h ∈ H, b h = 0) (g : G) :
    (μ - 1) • b g = ρ g (b z) - b z := by
  obtain ⟨n, hn, hzg⟩ : ∃ n ∈ H, z * g = n * (g * z) := ⟨_, hz g, by group⟩
  have h1 : b (z * g) = b z + μ • b g := by
    rw [hb z g, hμ, LinearMap.smul_apply, LinearMap.id_apply]
  have h2 : b (n * (g * z)) = b g + ρ g (b z) := by
    rw [hb n (g * z), hbH n hn, hH n hn, zero_add, hb g z]
  rw [hzg, h2] at h1
  rw [sub_smul, one_smul, sub_eq_sub_iff_add_eq_add, add_comm (μ • b g), ← h1, add_comm]

/-- **A cocycle zero on the kernel is a coboundary** (tex 4770-4774):
"`(u^4-1)b(g)=(g-1)b(z)` makes it a coboundary over characteristic zero."

Kind: PROVED. With the hypotheses of `cocycle_scalar_identity` and `μ - 1` a unit,
`b g = ρ g w - w` for `w = (μ - 1)⁻¹ • b z` (written with `Ring.inverse`).

DEPARTURE: "over characteristic zero" (where `u⁴ - 1 ≠ 0`) is replaced by the weaker hypothesis
`IsUnit (μ - 1)`; see `coboundary_of_vanishes_on_kernel_field` for the field form with
`μ = u⁴`. -/
theorem coboundary_of_vanishes_on_kernel (H : Subgroup G) (hH : ∀ h ∈ H, ∀ w : W, ρ h w = w)
    (z : G) (hz : ∀ g : G, z * g * z⁻¹ * g⁻¹ ∈ H) (μ : k) (hμ : ρ z = μ • LinearMap.id)
    (hunit : IsUnit (μ - 1)) {b : G → W} (hb : IsCocycle ρ b) (hbH : ∀ h ∈ H, b h = 0) :
    ∀ g : G, b g = ρ g (Ring.inverse (μ - 1) • b z) - Ring.inverse (μ - 1) • b z := by
  intro g
  rw [map_smul, ← smul_sub, ← cocycle_scalar_identity H hH z hz μ hμ hb hbH g, smul_smul,
    Ring.inverse_mul_cancel _ hunit, one_smul]

/-- `IsCoboundary` form of `coboundary_of_vanishes_on_kernel` (tex 4770-4774). Kind: PROVED. -/
theorem isCoboundary_of_vanishes_on_kernel (H : Subgroup G)
    (hH : ∀ h ∈ H, ∀ w : W, ρ h w = w) (z : G) (hz : ∀ g : G, z * g * z⁻¹ * g⁻¹ ∈ H) (μ : k)
    (hμ : ρ z = μ • LinearMap.id) (hunit : IsUnit (μ - 1)) {b : G → W} (hb : IsCocycle ρ b)
    (hbH : ∀ h ∈ H, b h = 0) : IsCoboundary ρ b :=
  ⟨_, coboundary_of_vanishes_on_kernel H hH z hz μ hμ hunit hb hbH⟩

/-- Field form of `coboundary_of_vanishes_on_kernel`, with the manuscript scalar `μ = u⁴`
(tex 4770-4774). Over a field (for instance a characteristic-zero test field, where
`u⁴ ≠ 1`), a cocycle zero on the kernel is the coboundary of `w = (u⁴ - 1)⁻¹ • b z`.
Kind: PROVED. -/
theorem coboundary_of_vanishes_on_kernel_field {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {σ : Representation K G V} (H : Subgroup G) (hH : ∀ h ∈ H, ∀ w : V, σ h w = w)
    (z : G) (hz : ∀ g : G, z * g * z⁻¹ * g⁻¹ ∈ H) (u : K) (hμ : σ z = u ^ 4 • LinearMap.id)
    (hu : u ^ 4 ≠ 1) {b : G → V} (hb : IsCocycle σ b) (hbH : ∀ h ∈ H, b h = 0) :
    ∀ g : G, b g = σ g ((u ^ 4 - 1)⁻¹ • b z) - (u ^ 4 - 1)⁻¹ • b z := by
  have hunit : IsUnit (u ^ 4 - 1) := isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hu)
  have h := coboundary_of_vanishes_on_kernel H hH z hz (u ^ 4) hμ hunit hb hbH
  simpa only [Ring.inverse_eq_inv'] using h

/-- **Restriction to the kernel is injective on `H¹`** (tex 4750-4752, "restriction of the
evaluated cohomology to this kernel is injective", proved at tex 4766-4774).

Kind: PROVED. Two cocycles with the same restriction to `H` differ by a coboundary. Since
coboundaries vanish on `H` (`coboundary_vanishes_on_kernel`) and `H¹(H, W)` of the trivially
acting `H` is `Hom(H, W)`, this is injectivity of `H¹(G, W) → H¹(H, W)`. -/
theorem isCoboundary_sub_of_restriction_eq (H : Subgroup G)
    (hH : ∀ h ∈ H, ∀ w : W, ρ h w = w) (z : G) (hz : ∀ g : G, z * g * z⁻¹ * g⁻¹ ∈ H) (μ : k)
    (hμ : ρ z = μ • LinearMap.id) (hunit : IsUnit (μ - 1)) {c₁ c₂ : G → W}
    (hc₁ : IsCocycle ρ c₁) (hc₂ : IsCocycle ρ c₂) (heq : ∀ h ∈ H, c₁ h = c₂ h) :
    IsCoboundary ρ (c₁ - c₂) :=
  isCoboundary_of_vanishes_on_kernel H hH z hz μ hμ hunit (hc₁.sub hc₂)
    (fun h hh => by rw [Pi.sub_apply, heq h hh, sub_self])

/-- **Independence of classes gives independence of restrictions** (tex 4788-4792, "contradicting
independence", via the kernel argument of tex 4766-4774).

Kind: PROVED. If no nontrivial combination `a c₁ + b c₂` is a coboundary (the classes are
independent in `H¹`), then no nontrivial combination vanishes on the kernel. -/
theorem restriction_independent_of_classes_independent (H : Subgroup G)
    (hH : ∀ h ∈ H, ∀ w : W, ρ h w = w) (z : G) (hz : ∀ g : G, z * g * z⁻¹ * g⁻¹ ∈ H) (μ : k)
    (hμ : ρ z = μ • LinearMap.id) (hunit : IsUnit (μ - 1)) {c₁ c₂ : G → W}
    (hc₁ : IsCocycle ρ c₁) (hc₂ : IsCocycle ρ c₂)
    (hindep : ∀ a b : k, IsCoboundary ρ (a • c₁ + b • c₂) → a = 0 ∧ b = 0) :
    ∀ a b : k, (∀ h ∈ H, a • c₁ h + b • c₂ h = 0) → a = 0 ∧ b = 0 := by
  intro a b hab
  exact hindep a b (isCoboundary_of_vanishes_on_kernel H hH z hz μ hμ hunit
    ((hc₁.smul a).add (hc₂.smul b)) (fun h hh => by simpa using hab h hh))

/-- **Residual invariants vanish** (tex 4775-4777): "To eliminate residual invariants, use
moving-prime inertia: its scalar difference is `t`, invertible in `𝔽₂((t))`. These are two
separate arguments."

Kind: PROVED. An element `s` acting by a scalar `λ` with `λ - 1` a unit has no nonzero fixed
vectors. (In the manuscript `λ = 1 + t`, so `λ - 1 = t`; see the `example` below.) -/
theorem invariants_eq_zero_of_scalar (s : G) (lam : k) (hs : ρ s = lam • LinearMap.id)
    (hunit : IsUnit (lam - 1)) {w : W} (hw : ρ s w = w) : w = 0 := by
  rw [hs, LinearMap.smul_apply, LinearMap.id_apply] at hw
  have h : (lam - 1) • w = 0 := by rw [sub_smul, one_smul, hw, sub_self]
  rwa [hunit.smul_eq_zero] at h

/-- The manuscript's residual scalar difference: `(1 + t) - 1 = t` is a unit of `𝔽₂((t))`. -/
example : IsUnit ((1 + HahnSeries.single (1 : ℤ) (1 : ZMod 2)) - 1 : LaurentSeries (ZMod 2)) := by
  rw [add_sub_cancel_left]
  exact isUnit_iff_ne_zero.mpr (HahnSeries.single_ne_zero one_ne_zero)

end Cocycles

/-! ### Bridge to Mathlib's group cohomology `H¹` -/

section MathlibH1

open groupCohomology

variable {k G W : Type u} [CommRing k] [Group G] [AddCommGroup W] [Module k W]
  (ρ : Representation k G W)

/-- `IsCocycle` agrees with Mathlib's `groupCohomology.cocycles₁ (Rep.of ρ)`. Kind: PROVED. -/
theorem isCocycle_iff_mem_cocycles₁ (b : G → W) :
    IsCocycle ρ b ↔ b ∈ cocycles₁ (Rep.of ρ) := by
  rw [mem_cocycles₁_iff]
  exact forall₂_congr fun g h => by rw [add_comm]

/-- `IsCoboundary` agrees with Mathlib's `groupCohomology.coboundaries₁ (Rep.of ρ)`.
Kind: PROVED. -/
theorem isCoboundary_iff_mem_coboundaries₁ (b : G → W) :
    IsCoboundary ρ b ↔ b ∈ coboundaries₁ (Rep.of ρ) := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, funext fun g => by rw [d₀₁_hom_apply]; exact (hw g).symm⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, fun g => by rw [← hw, d₀₁_hom_apply]⟩

/-- **Kernel argument in Mathlib's `H¹`** (tex 4770-4774). Kind: PROVED. The class in
`groupCohomology.H1 (Rep.of ρ)` of a cocycle zero on the kernel is zero. -/
theorem H1π_eq_zero_of_vanishes_on_kernel (H : Subgroup G) (hH : ∀ h ∈ H, ∀ w : W, ρ h w = w)
    (z : G) (hz : ∀ g : G, z * g * z⁻¹ * g⁻¹ ∈ H) (μ : k) (hμ : ρ z = μ • LinearMap.id)
    (hunit : IsUnit (μ - 1)) (b : cocycles₁ (Rep.of ρ)) (hbH : ∀ h ∈ H, b h = 0) :
    H1π (Rep.of ρ) b = 0 := by
  rw [H1π_eq_zero_iff, ← isCoboundary_iff_mem_coboundaries₁]
  exact isCoboundary_of_vanishes_on_kernel H hH z hz μ hμ hunit
    ((isCocycle_iff_mem_cocycles₁ ρ b).mpr b.2) hbH

/-- **Restriction to the kernel is injective on `H¹`, in Mathlib's `H¹`** (tex 4750-4752,
4766-4774). Kind: PROVED. Two classes of `groupCohomology.H1 (Rep.of ρ)` agree if and only if
their representing cocycles agree on the kernel `H` (for the trivially acting `H`,
`H¹(H, W) = Hom(H, W)`, so this is injectivity, and well-definedness, of restriction). -/
theorem H1π_eq_iff_restriction_eq (H : Subgroup G) (hH : ∀ h ∈ H, ∀ w : W, ρ h w = w)
    (z : G) (hz : ∀ g : G, z * g * z⁻¹ * g⁻¹ ∈ H) (μ : k) (hμ : ρ z = μ • LinearMap.id)
    (hunit : IsUnit (μ - 1)) (x y : cocycles₁ (Rep.of ρ)) :
    H1π (Rep.of ρ) x = H1π (Rep.of ρ) y ↔ ∀ h ∈ H, x h = y h := by
  rw [H1π_eq_iff, ← isCoboundary_iff_mem_coboundaries₁]
  have hx : IsCocycle ρ x := (isCocycle_iff_mem_cocycles₁ ρ x).mpr x.2
  have hy : IsCocycle ρ y := (isCocycle_iff_mem_cocycles₁ ρ y).mpr y.2
  constructor
  · intro hc h hh
    have := hc.vanishes_on_kernel H hH h hh
    rwa [Pi.sub_apply, sub_eq_zero] at this
  · intro heq
    exact isCoboundary_sub_of_restriction_eq H hH z hz μ hμ hunit hx hy heq

end MathlibH1

/-! ## Step 2: Goursat and the joint span (tex 4778-4792) -/

section Goursat

variable {k A W : Type*} [CommRing k] [Ring A] [Algebra k A] [AddCommGroup W] [Module A W]
  [Module k W] [IsScalarTower k A W]

/-- **Goursat for an irreducible module with scalar endomorphisms** (tex 4790-4792):
"A proper submodule with both projections onto would be the graph of a scalar isomorphism".

Kind: PROVED. `W` is a simple `A`-module (`A` is, for instance, `k[G]` or the span of the image
of `G`) all of whose `A`-endomorphisms are `k`-scalars ("absolutely irreducible with scalar
endomorphisms", tex 4783-4784). A submodule `P ≤ W × W` with both projections onto is `⊤` or the
graph `{(w, c • w)}` of a nonzero scalar `c` acting bijectively (a "scalar isomorphism").

Proof note: proved directly (the two "kernels" `{w | (w, 0) ∈ P}` and `{w | (0, w) ∈ P}` are
`⊥` or `⊤` by simplicity, then the vertical line test `Submodule.exists_eq_graph` and `hEnd`),
not through Mathlib's `Submodule.goursat`. -/
theorem submodule_prod_eq_top_or_graph [IsSimpleModule A W]
    (hEnd : ∀ φ : W →ₗ[A] W, ∃ c : k, φ = c • LinearMap.id) (P : Submodule A (W × W))
    (hfst : P.map (LinearMap.fst A W W) = ⊤) (hsnd : P.map (LinearMap.snd A W W) = ⊤) :
    P = ⊤ ∨ ∃ c : k, c ≠ 0 ∧ Function.Bijective (fun w : W => c • w) ∧
      P = LinearMap.graph (c • LinearMap.id : W →ₗ[A] W) := by
  have : Nontrivial W := IsSimpleModule.nontrivial A W
  have hex₁ : ∀ a : W, ∃ b, (a, b) ∈ P := by
    intro a
    have ha : a ∈ P.map (LinearMap.fst A W W) := by rw [hfst]; exact Submodule.mem_top
    obtain ⟨p, hp, hpa⟩ := Submodule.mem_map.mp ha
    refine ⟨p.2, ?_⟩
    rw [LinearMap.fst_apply] at hpa
    rw [← hpa]
    exact hp
  have hex₂ : ∀ b : W, ∃ a, (a, b) ∈ P := by
    intro b
    have hb : b ∈ P.map (LinearMap.snd A W W) := by rw [hsnd]; exact Submodule.mem_top
    obtain ⟨p, hp, hpb⟩ := Submodule.mem_map.mp hb
    refine ⟨p.1, ?_⟩
    rw [LinearMap.snd_apply] at hpb
    rw [← hpb]
    exact hp
  set K₁ : Submodule A W := P.comap (LinearMap.inl A W W) with hK₁
  set K₂ : Submodule A W := P.comap (LinearMap.inr A W W) with hK₂
  have hmem₁ : ∀ w, w ∈ K₁ ↔ (w, (0 : W)) ∈ P := fun w => by
    rw [hK₁, Submodule.mem_comap, LinearMap.inl_apply]
  have hmem₂ : ∀ w, w ∈ K₂ ↔ ((0 : W), w) ∈ P := fun w => by
    rw [hK₂, Submodule.mem_comap, LinearMap.inr_apply]
  rcases eq_bot_or_eq_top K₁ with h₁ | h₁
  · rcases eq_bot_or_eq_top K₂ with h₂ | h₂
    · -- both kernels vanish: `P` is the graph of an `A`-linear map, a scalar by `hEnd`
      right
      have huniq : ∀ a b b' : W, (a, b) ∈ P → (a, b') ∈ P → b = b' := by
        intro a b b' hb hb'
        have h0 : ((0 : W), b - b') ∈ P := by
          have := P.sub_mem hb hb'
          rwa [Prod.mk_sub_mk, sub_self] at this
        rw [← hmem₂, h₂, Submodule.mem_bot, sub_eq_zero] at h0
        exact h0
      have hbij : Function.Bijective (Prod.fst ∘ P.subtype) := by
        constructor
        · rintro ⟨⟨a, b⟩, hp⟩ ⟨⟨a', b'⟩, hp'⟩ hfa
          simp only [Function.comp_apply, Submodule.subtype_apply] at hfa
          subst hfa
          have := huniq a b b' hp hp'
          subst this
          rfl
        · intro a
          obtain ⟨b, hb⟩ := hex₁ a
          exact ⟨⟨(a, b), hb⟩, rfl⟩
      obtain ⟨φ, hφ⟩ := Submodule.exists_eq_graph hbij
      obtain ⟨c, hc⟩ := hEnd φ
      rw [hc] at hφ
      have hgraph : ∀ a b : W, (a, b) ∈ P ↔ b = c • a := fun a b => by
        rw [hφ, LinearMap.mem_graph_iff, LinearMap.smul_apply, LinearMap.id_apply]
      have hinj : Function.Injective (fun w : W => c • w) := by
        intro w w' hww'
        have hP : (w - w', c • (w - w')) ∈ P := (hgraph _ _).mpr rfl
        simp only at hww'
        rw [smul_sub, hww', sub_self, ← hmem₁, h₁, Submodule.mem_bot, sub_eq_zero] at hP
        exact hP
      refine ⟨c, ?_, ⟨hinj, ?_⟩, hφ⟩
      · rintro rfl
        obtain ⟨w, hw⟩ := exists_ne (0 : W)
        exact hw (hinj (by simp only [zero_smul]))
      · intro b
        obtain ⟨a, ha⟩ := hex₂ b
        exact ⟨a, ((hgraph a b).mp ha).symm⟩
    · -- `(0, W) ⊆ P`; with the first projection onto, `P = ⊤`
      left
      rw [eq_top_iff]
      rintro ⟨a, b⟩ -
      obtain ⟨b', hb'⟩ := hex₁ a
      have h0 : ((0 : W), b - b') ∈ P := by
        rw [← hmem₂, h₂]; exact Submodule.mem_top
      have := P.add_mem hb' h0
      rwa [Prod.mk_add_mk, add_zero, add_sub_cancel] at this
  · -- `(W, 0) ⊆ P`; with the second projection onto, `P = ⊤`
    left
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    obtain ⟨a', ha'⟩ := hex₂ b
    have h0 : (a - a', (0 : W)) ∈ P := by
      rw [← hmem₁, h₁]; exact Submodule.mem_top
    have := P.add_mem ha' h0
    rwa [Prod.mk_add_mk, add_zero, add_sub_cancel] at this

/-- The span over `A` of the joint values of two families, independent in the sense that no
nontrivial `k`-combination vanishes identically, is all of `W × W` (tex 4788-4792, the `A`-span
form). Kind: PROVED. -/
theorem joint_span_eq_top_of_independent [IsSimpleModule A W]
    (hEnd : ∀ φ : W →ₗ[A] W, ∃ c : k, φ = c • LinearMap.id) {ι : Type*} (x₁ x₂ : ι → W)
    (hind : ∀ a b : k, (∀ i, a • x₁ i + b • x₂ i = 0) → a = 0 ∧ b = 0) :
    Submodule.span A (Set.range fun i => (x₁ i, x₂ i)) = ⊤ := by
  have : Nontrivial W := IsSimpleModule.nontrivial A W
  have : Nontrivial k := Module.nontrivial k W
  set P := Submodule.span A (Set.range fun i => (x₁ i, x₂ i)) with hP
  have hfst : P.map (LinearMap.fst A W W) = ⊤ := by
    rw [hP, Submodule.map_span, ← Set.range_comp]
    rcases eq_bot_or_eq_top
        (Submodule.span A (Set.range ((LinearMap.fst A W W) ∘ fun i => (x₁ i, x₂ i)))) with
      h | h
    · exfalso
      have hx₁ : ∀ i, x₁ i = 0 := fun i => by
        have hi : ((LinearMap.fst A W W) ∘ fun i => (x₁ i, x₂ i)) i ∈
            Submodule.span A (Set.range ((LinearMap.fst A W W) ∘ fun i => (x₁ i, x₂ i))) :=
          Submodule.subset_span ⟨i, rfl⟩
        rw [h, Submodule.mem_bot] at hi
        simpa using hi
      exact one_ne_zero (hind 1 0 (fun i => by rw [hx₁ i, smul_zero, zero_smul, add_zero])).1
    · exact h
  have hsnd : P.map (LinearMap.snd A W W) = ⊤ := by
    rw [hP, Submodule.map_span, ← Set.range_comp]
    rcases eq_bot_or_eq_top
        (Submodule.span A (Set.range ((LinearMap.snd A W W) ∘ fun i => (x₁ i, x₂ i)))) with
      h | h
    · exfalso
      have hx₂ : ∀ i, x₂ i = 0 := fun i => by
        have hi : ((LinearMap.snd A W W) ∘ fun i => (x₁ i, x₂ i)) i ∈
            Submodule.span A (Set.range ((LinearMap.snd A W W) ∘ fun i => (x₁ i, x₂ i))) :=
          Submodule.subset_span ⟨i, rfl⟩
        rw [h, Submodule.mem_bot] at hi
        simpa using hi
      exact one_ne_zero (hind 0 1 (fun i => by rw [hx₂ i, smul_zero, zero_smul, add_zero])).2
    · exact h
  rcases submodule_prod_eq_top_or_graph hEnd P hfst hsnd with h | ⟨c, -, -, hgraph⟩
  · exact h
  · exfalso
    have hx : ∀ i, x₂ i = c • x₁ i := fun i => by
      have hi : (x₁ i, x₂ i) ∈ P := Submodule.subset_span ⟨i, rfl⟩
      rw [hgraph, LinearMap.mem_graph_iff, LinearMap.smul_apply, LinearMap.id_apply] at hi
      exact hi
    have := (hind c (-1) (fun i => by rw [hx i, neg_one_smul, add_neg_cancel])).2
    exact one_ne_zero (neg_eq_zero.mp this)

end Goursat

section JointSpan

variable {k G A W : Type*} [CommRing k] [Group G] [Ring A] [Algebra k A] [AddCommGroup W]
  [Module A W] [Module k W] [IsScalarTower k A W]

/-- **The joint span is the full sum** (tex 4788-4792): "For two independent cohomology classes on
these tests, the span of their joint values on the exact kernel projects onto both copies of this
absolutely irreducible representation. A proper submodule with both projections onto would be the
graph of a scalar isomorphism, contradicting independence. Thus the span is the full sum."

Kind: PROVED. `G` acts on `W` through `ι : G →* A` (`ρ g w = ι g • w`), and `A` is the `k`-span
of the image of `G` (for instance `A = k[G]`, see `joint_span_eq_top_monoidAlgebra`, or the
matrix span of the image). `W` is a simple `A`-module with scalar endomorphisms. `H` is a normal
subgroup acting trivially; `c₁, c₂` are cocycles such that no nontrivial `k`-combination vanishes
on `H` (independence of the restrictions; it follows from independence of the classes by the
kernel argument, `restriction_independent_of_classes_independent`; it contains the hypothesis
that both restrictions are nonzero). Then the `k`-span of the joint values
`{(c₁ h, c₂ h) : h ∈ H}` is all of `W × W`.

The `k`-span is a `k[G]`-submodule by `restriction_equivariant` ("equivalently, by
equivariance"), so it equals the `A`-span; then `joint_span_eq_top_of_independent` applies. -/
theorem joint_span_eq_top [IsSimpleModule A W]
    (hEnd : ∀ φ : W →ₗ[A] W, ∃ c : k, φ = c • LinearMap.id) (ρ : Representation k G W)
    (ι : G →* A) (hι : Submodule.span k (Set.range ι) = ⊤) (hρ : ∀ (g : G) (w : W), ρ g w = ι g • w)
    (H : Subgroup G) [hN : H.Normal] (hH : ∀ h ∈ H, ∀ w : W, ρ h w = w) {c₁ c₂ : G → W}
    (hc₁ : IsCocycle ρ c₁) (hc₂ : IsCocycle ρ c₂)
    (hind : ∀ a b : k, (∀ h ∈ H, a • c₁ h + b • c₂ h = 0) → a = 0 ∧ b = 0) :
    Submodule.span k (Set.range fun h : H => (c₁ h, c₂ h)) = ⊤ := by
  set S : Set (W × W) := Set.range fun h : H => (c₁ h, c₂ h) with hS
  have hSstab : ∀ g : G, ∀ x ∈ S, (ρ g x.1, ρ g x.2) ∈ S := by
    rintro g _ ⟨h, rfl⟩
    refine ⟨⟨g * h * g⁻¹, hN.conj_mem h h.2 g⟩, ?_⟩
    simp only [restriction_equivariant H hH hc₁ h h.2 g, restriction_equivariant H hH hc₂ h h.2 g]
  have hGstab : ∀ g : G, ∀ x ∈ Submodule.span k S, ι g • x ∈ Submodule.span k S := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        have hgx : ι g • x = (ρ g x.1, ρ g x.2) :=
          Prod.ext (by simp only [Prod.smul_fst, hρ]) (by simp only [Prod.smul_snd, hρ])
        rw [hgx]
        exact Submodule.subset_span (hSstab g x hx)
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  have hAstab : ∀ a : A, ∀ x ∈ Submodule.span k S, a • x ∈ Submodule.span k S := by
    intro a x hx
    have ha : a ∈ Submodule.span k (Set.range ι) := by rw [hι]; exact Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem a ha =>
        obtain ⟨g, rfl⟩ := ha
        exact hGstab g x hx
    | zero => rw [zero_smul]; exact zero_mem _
    | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
    | smul r a _ ha => rw [smul_assoc]; exact Submodule.smul_mem _ r ha
  let N : Submodule A (W × W) :=
    { carrier := Submodule.span k S
      add_mem' := fun hx hy => add_mem hx hy
      zero_mem' := zero_mem _
      smul_mem' := fun a x hx => hAstab a x hx }
  have hle : Submodule.span A S ≤ N :=
    Submodule.span_le.mpr (fun x hx => (Submodule.subset_span hx : x ∈ Submodule.span k S))
  have htop : Submodule.span A S = ⊤ :=
    joint_span_eq_top_of_independent hEnd (fun h : H => c₁ h) (fun h : H => c₂ h)
      (fun a b hab => hind a b (fun h hh => hab ⟨h, hh⟩))
  rw [htop] at hle
  rw [eq_top_iff]
  intro x _
  exact hle Submodule.mem_top

/-- The image of `G` spans the group algebra `k[G]` over `k`. Kind: PROVED. -/
theorem span_range_of_monoidAlgebra : Submodule.span k (Set.range (MonoidAlgebra.of k G)) = ⊤ := by
  rw [eq_top_iff]
  rintro f -
  induction f using MonoidAlgebra.induction_on with
  | of g => exact Submodule.subset_span ⟨g, rfl⟩
  | add f g hf hg => exact add_mem hf hg
  | smul r f hf => exact Submodule.smul_mem _ r hf

/-- `joint_span_eq_top` for `A = k[G]` (tex 4788-4792). `W` is a simple `k[G]`-module with scalar
endomorphisms, and `G` acts through `Representation.ofModule'`. Kind: PROVED. -/
theorem joint_span_eq_top_monoidAlgebra [Module (MonoidAlgebra k G) W]
    [IsScalarTower k (MonoidAlgebra k G) W] [IsSimpleModule (MonoidAlgebra k G) W]
    (hEnd : ∀ φ : W →ₗ[MonoidAlgebra k G] W, ∃ c : k, φ = c • LinearMap.id)
    (H : Subgroup G) [H.Normal]
    (hH : ∀ h ∈ H, ∀ w : W, Representation.ofModule' (k := k) (G := G) W h w = w)
    {c₁ c₂ : G → W} (hc₁ : IsCocycle (Representation.ofModule' (k := k) (G := G) W) c₁)
    (hc₂ : IsCocycle (Representation.ofModule' (k := k) (G := G) W) c₂)
    (hind : ∀ a b : k, (∀ h ∈ H, a • c₁ h + b • c₂ h = 0) → a = 0 ∧ b = 0) :
    Submodule.span k (Set.range fun h : H => (c₁ h, c₂ h)) = ⊤ :=
  joint_span_eq_top hEnd (Representation.ofModule' (k := k) (G := G) W) (MonoidAlgebra.of k G)
    span_range_of_monoidAlgebra (fun _ _ => rfl) H hH hc₁ hc₂ hind

end JointSpan

/-! ## Step 3: polarization and the rank-two localization (tex 4792-4799) -/

section Polarization

/-- **Polarization** (tex 4793-4795, 4798): "If the determinant ... vanished on every actual
kernel element, additivity and polarization would make it vanish on the entire span"; "The
polarization identity itself is also valid in characteristic two".

Kind: PROVED, with no characteristic assumption. If `x : H → M` is additive
(`x (h₁ * h₂) = x h₁ + x h₂`) and the quadratic map `Q` vanishes at every value `x h`, then the
polar form `Q(u+v) - Q(u) - Q(v)` vanishes on all pairs of values, and `Q` vanishes on the whole
`k`-span of the values. -/
theorem quadratic_vanishes_on_span {k M N H : Type*} [CommRing k] [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] [Mul H] (Q : QuadraticMap k M N) (x : H → M)
    (hx : ∀ h₁ h₂ : H, x (h₁ * h₂) = x h₁ + x h₂) (hQ : ∀ h : H, Q (x h) = 0) :
    ∀ v ∈ Submodule.span k (Set.range x), Q v = 0 := by
  have hpol : ∀ h₁ h₂ : H, QuadraticMap.polar Q (x h₁) (x h₂) = 0 := by
    intro h₁ h₂
    rw [QuadraticMap.polar, ← hx, hQ, hQ, hQ, sub_zero, sub_zero]
  have hpol₁ : ∀ u ∈ Submodule.span k (Set.range x), ∀ h : H,
      QuadraticMap.polar Q u (x h) = 0 := by
    intro u hu h
    induction hu using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨h', rfl⟩ := hu
        exact hpol h' h
    | zero => exact QuadraticMap.polar_zero_left Q _
    | add u v _ _ hu hv => rw [QuadraticMap.polar_add_left, hu, hv, add_zero]
    | smul a u _ hu => rw [QuadraticMap.polar_smul_left, hu, smul_zero]
  have hpol₂ : ∀ u ∈ Submodule.span k (Set.range x), ∀ v ∈ Submodule.span k (Set.range x),
      QuadraticMap.polar Q u v = 0 := by
    intro u hu v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨h, rfl⟩ := hv
        exact hpol₁ u hu h
    | zero => exact QuadraticMap.polar_zero_right Q _
    | add v v' _ _ hv hv' => rw [QuadraticMap.polar_add_right, hv, hv', add_zero]
    | smul a v _ hv => rw [QuadraticMap.polar_smul_right, hv, smul_zero]
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨h, rfl⟩ := hv
      exact hQ h
  | zero => exact QuadraticMap.map_zero Q
  | add u v hu' hv' hu hv =>
      have hsplit : Q (u + v) = QuadraticMap.polar Q u v + Q u + Q v := by
        rw [QuadraticMap.polar]
        abel
      rw [hsplit, hpol₂ u hu' v hv', hu, hv, add_zero, add_zero]
  | smul a u _ hu => rw [QuadraticMap.map_smul, hu, smul_zero]

variable {k W : Type*} [CommRing k] [AddCommGroup W] [Module k W]

/-- The determinant of the `2 × 2` matrix whose columns are the finite localizations `π w₁` and
`π w₂` (tex 4793, "the determinant of their two finite localizations"). -/
def locDet (π : W →ₗ[k] (Fin 2 → k)) (w₁ w₂ : W) : k :=
  (Matrix.of ![π w₁, π w₂]).transpose.det

/-- `locDet` written out: `det[π w₁ | π w₂] = (π w₁)₀ (π w₂)₁ - (π w₂)₀ (π w₁)₁`.
Kind: PROVED. -/
theorem locDet_eq (π : W →ₗ[k] (Fin 2 → k)) (w₁ w₂ : W) :
    locDet π w₁ w₂ = π w₁ 0 * π w₂ 1 - π w₂ 0 * π w₁ 1 := by
  rw [locDet, Matrix.det_transpose, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The bilinear form `((w₁, w₂), (w₁', w₂')) ↦ det[π w₁ | π w₂']` on `W × W`; its diagonal is
`locDet`. -/
def locDetBilin (π : W →ₗ[k] (Fin 2 → k)) : LinearMap.BilinMap k (W × W) k :=
  LinearMap.mk₂ k (fun p q : W × W => π p.1 0 * π q.2 1 - π q.2 0 * π p.1 1)
    (fun p p' q => by simp only [Prod.fst_add, map_add, Pi.add_apply]; ring)
    (fun c p q => by simp only [Prod.smul_fst, map_smul, Pi.smul_apply, smul_eq_mul]; ring)
    (fun p q q' => by simp only [Prod.snd_add, map_add, Pi.add_apply]; ring)
    (fun c p q => by simp only [Prod.smul_snd, map_smul, Pi.smul_apply, smul_eq_mul]; ring)

/-- The determinant of the two finite localizations as a quadratic map on `W × W`:
`Q(w₁, w₂) = det[π w₁ | π w₂]`. -/
def locDetQuad (π : W →ₗ[k] (Fin 2 → k)) : QuadraticMap k (W × W) k :=
  (locDetBilin π).toQuadraticMap

/-- `locDetQuad π (w₁, w₂) = locDet π w₁ w₂`. Kind: PROVED. -/
theorem locDetQuad_apply (π : W →ₗ[k] (Fin 2 → k)) (p : W × W) :
    locDetQuad π p = locDet π p.1 p.2 := by
  rw [locDetQuad, LinearMap.BilinMap.toQuadraticMap_apply, locDet_eq]
  rfl

/-- **One actual element supplies a rank-two localization** (tex 4792-4796): "If the determinant
of their two finite localizations vanished on every actual kernel element, additivity and
polarization would make it vanish on the entire span, impossible. Hence one actual element
supplies a rank-two localization".

Kind: PROVED. `π : W → k²` is the (surjective) finite localization. If the joint values
`{(c₁ h, c₂ h) : h ∈ H}` of two cocycles span `W × W` (`joint_span_eq_top`), then some
`h ∈ H` has `det[π (c₁ h) | π (c₂ h)] ≠ 0`. ("impossible": since `π` is onto, lifts `w₁, w₂`
of the standard basis give `det[π w₁ | π w₂] = 1`.)

DEPARTURE: the finite localization at the new prime is abstracted to a surjective `k`-linear map
`π : W → k²` applied to the kernel values of the cocycles. -/
theorem exists_rank_two_localization [Nontrivial k] {G : Type*} [Group G]
    (ρ : Representation k G W) (H : Subgroup G) (hH : ∀ h ∈ H, ∀ w : W, ρ h w = w)
    {c₁ c₂ : G → W} (hc₁ : IsCocycle ρ c₁) (hc₂ : IsCocycle ρ c₂) (π : W →ₗ[k] (Fin 2 → k))
    (hπ : Function.Surjective π)
    (hspan : Submodule.span k (Set.range fun h : H => (c₁ h, c₂ h)) = ⊤) :
    ∃ h ∈ H, locDet π (c₁ h) (c₂ h) ≠ 0 := by
  by_contra hne
  have hcon : ∀ h ∈ H, locDet π (c₁ h) (c₂ h) = 0 :=
    fun h hh => by_contra fun hne' => hne ⟨h, hh, hne'⟩
  have hadd : ∀ h₁ h₂ : H, (fun h : H => (c₁ h, c₂ h)) (h₁ * h₂) =
      (fun h : H => (c₁ h, c₂ h)) h₁ + (fun h : H => (c₁ h, c₂ h)) h₂ := by
    intro h₁ h₂
    simp only [Subgroup.coe_mul, restriction_additive H hH hc₁ h₁ h₁.2 h₂ h₂.2,
      restriction_additive H hH hc₂ h₁ h₁.2 h₂ h₂.2, Prod.mk_add_mk]
  have hvan := quadratic_vanishes_on_span (locDetQuad π) (fun h : H => (c₁ h, c₂ h)) hadd
    (fun h => by rw [locDetQuad_apply]; exact hcon h h.2)
  obtain ⟨w₁, hw₁⟩ := hπ (Pi.single 0 1)
  obtain ⟨w₂, hw₂⟩ := hπ (Pi.single 1 1)
  have h := hvan (w₁, w₂) (by rw [hspan]; exact Submodule.mem_top)
  rw [locDetQuad_apply, locDet_eq, hw₁, hw₂] at h
  simp at h

end Polarization

/-! ### The three steps assembled (tex 4778-4796) -/

section Assembled

variable {k G A W : Type*} [CommRing k] [Group G] [Ring A] [Algebra k A] [AddCommGroup W]
  [Module A W] [Module k W] [IsScalarTower k A W]

/-- **One new prime detects two classes: the algebra** (tex 4752-4755 and 4766-4796): "two
independent classes have a rank-two localization at a single actual kernel element".

Kind: PROVED. Hypotheses: `W` is a simple `A`-module with scalar endomorphisms, `G` acts through
`ι : G →* A` whose image spans `A`; `H` is a normal subgroup acting trivially; `z` is central
modulo `H` and acts by a scalar `μ` with `μ - 1` a unit (`μ = u⁴`, characteristic zero);
`c₁, c₂` are cocycles whose classes are independent (no nontrivial combination is a coboundary);
`π : W → k²` is a surjective finite localization. Conclusion: some `h ∈ H` has
`det[π (c₁ h) | π (c₂ h)] ≠ 0`. The proof chains `restriction_independent_of_classes_independent`,
`joint_span_eq_top` and `exists_rank_two_localization`. -/
theorem kernel_element_detects_two_classes [IsSimpleModule A W]
    (hEnd : ∀ φ : W →ₗ[A] W, ∃ c : k, φ = c • LinearMap.id) (ρ : Representation k G W)
    (ι : G →* A) (hι : Submodule.span k (Set.range ι) = ⊤) (hρ : ∀ (g : G) (w : W), ρ g w = ι g • w)
    (H : Subgroup G) [H.Normal] (hH : ∀ h ∈ H, ∀ w : W, ρ h w = w)
    (z : G) (hz : ∀ g : G, z * g * z⁻¹ * g⁻¹ ∈ H) (μ : k) (hμ : ρ z = μ • LinearMap.id)
    (hunit : IsUnit (μ - 1)) {c₁ c₂ : G → W} (hc₁ : IsCocycle ρ c₁) (hc₂ : IsCocycle ρ c₂)
    (hindep : ∀ a b : k, IsCoboundary ρ (a • c₁ + b • c₂) → a = 0 ∧ b = 0)
    (π : W →ₗ[k] (Fin 2 → k)) (hπ : Function.Surjective π) :
    ∃ h ∈ H, locDet π (c₁ h) (c₂ h) ≠ 0 := by
  have : Nontrivial W := IsSimpleModule.nontrivial A W
  have : Nontrivial k := Module.nontrivial k W
  have hind := restriction_independent_of_classes_independent H hH z hz μ hμ hunit hc₁ hc₂ hindep
  exact exists_rank_two_localization ρ H hH hc₁ hc₂ π hπ
    (joint_span_eq_top hEnd ρ ι hι hρ H hH hc₁ hc₂ hind)

end Assembled

/-! ## Step 4: finite Chebotarev and the exact matrix identity (5.4) (tex 4809-4831) -/

section ExactIdentity

/-- **Interface for (5.4)** (tex 4755-4758 and 4809-4827). Kind: ELLIOT/PRINT, an input that is
stated and not proved here (finite Chebotarev is a print input; the exact equality over `Λ`
through the inner ultrafilter is Elliot's, via `ex:limits-inner-limit`, tex 4391-4407):
"Chebotarev is applied at finite stages, not to the product group. ... Include their quotient,
the required Tate precision, ring-class and quadratic fields and old diagrams in one compositum.
The element just found, multiplied by conjugation, is a single actual automorphism of that
compositum. ... Choose the new prime and a place above it to realize that representative. ...
Taking the same inner ultrafilter gives an exact equality of `Λ`-matrices `L_j=E_{σ_j^2}` (5.4)."

Data, for each instance `j : J`:
* `Γ j`: the finite quotient `Gal(M_j/ℚ)` of one compositum `M_j` (an abstract finite group);
* `τ j`, `h j`: the images in `Γ j` of complex conjugation and of the kernel element just found;
* `P j`: the admissible new primes (outside the finitely many already used), each with a chosen
  place above it, and `frob j ℓ ∈ Γ j` the Frobenius at the chosen place;
* `E j σ`: the `Λ`-matrix of evaluations of the original basis cochains at `σ` (they factor
  through `Γ j`);
* `L j ℓ`: the `Λ`-matrix of localizations at the new prime `ℓ`.

The proposition: for every `j` there is a new prime `ℓ` whose Frobenius realizes the
representative `σ_j = τ_j h_j`, and `L_j = E_{σ_j^2}` holds exactly over `Λ`.

DEPARTURE: the finite stages of precision `n(i) → ∞` and the inner ultrafilter that produce the
exact identity over `Λ` are not modelled; their output, the exact identity (5.4), is the
interface. -/
def ExactChebotarevRealization {J Λ m n : Type*} (Γ : J → Type*) [∀ j, Group (Γ j)]
    [∀ j, Finite (Γ j)] (τ h : ∀ j, Γ j) (P : J → Type*) (frob : ∀ j, P j → Γ j)
    (E : ∀ j, Γ j → Matrix m n Λ) (L : ∀ j, P j → Matrix m n Λ) : Prop :=
  ∀ j, ∃ ℓ : P j, frob j ℓ = τ j * h j ∧ L j ℓ = E j (frob j ℓ ^ 2)

/-- The interface `ExactChebotarevRealization` is satisfiable (non-vacuity). -/
example : ExactChebotarevRealization (J := Unit) (Λ := ℤ) (m := Fin 2) (n := Fin 2)
    (fun _ => Multiplicative (ZMod 2)) (fun _ => 1) (fun _ => 1) (fun _ => Unit) (fun _ _ => 1)
    (fun _ _ => 1) (fun _ _ => 1) :=
  fun _ => ⟨(), by simp, rfl⟩

/-- The interface `ExactChebotarevRealization` has content: it fails when `L ≠ E`. -/
example : ¬ ExactChebotarevRealization (J := Unit) (Λ := ℤ) (m := Fin 2) (n := Fin 2)
    (fun _ => Multiplicative (ZMod 2)) (fun _ => 1) (fun _ => 1) (fun _ => Unit) (fun _ _ => 1)
    (fun _ _ => 1) (fun _ _ => 0) := by
  intro h54
  obtain ⟨_, _, hL⟩ := h54 ()
  have := congrFun (congrFun hL 0) 0
  simp at this

/-- **Composition with the inclusion** (tex 4825-4829): "Only afterward compose with the inclusion
`I_j` from an `𝒪`-minimal model: `L_jI_j=E_{σ_j^2}I_j`. The denominators in `I_j` may depend on
`j`; equality (5.4) makes this irrelevant."

Kind: PROVED (trivial algebra): from `L = E` one gets `L I = E I`, for any `I`. -/
theorem matrix_identity_mul_inclusion {R m n p : Type*} [NonUnitalNonAssocSemiring R] [Fintype n]
    (L E : Matrix m n R) (I : Matrix n p R) (h : L = E) : L * I = E * I := by
  rw [h]

/-- (5.4) composed with the inclusions (tex 4825-4829). Kind: PROVED from the interface
`ExactChebotarevRealization`. The inclusion matrices `I j` have entries in a ring `R` receiving
`Λ` (they may carry `j`-dependent denominators); `L_j I_j = E_{σ_j^2} I_j` holds exactly. -/
theorem ExactChebotarevRealization.mul_inclusion {J Λ R m n p : Type*} [Semiring Λ]
    [Semiring R] [Fintype n] (Γ : J → Type*) [∀ j, Group (Γ j)] [∀ j, Finite (Γ j)]
    (τ h : ∀ j, Γ j) (P : J → Type*) (frob : ∀ j, P j → Γ j) (E : ∀ j, Γ j → Matrix m n Λ)
    (L : ∀ j, P j → Matrix m n Λ) (h54 : ExactChebotarevRealization Γ τ h P frob E L)
    (f : Λ →+* R) (I : J → Matrix n p R) :
    ∀ j, ∃ ℓ : P j, frob j ℓ = τ j * h j ∧
      (L j ℓ).map f * I j = (E j (frob j ℓ ^ 2)).map f * I j := by
  intro j
  obtain ⟨ℓ, hfrob, hL⟩ := h54 j
  exact ⟨ℓ, hfrob, matrix_identity_mul_inclusion _ _ _ (by rw [hL])⟩

end ExactIdentity

/-! ## Non-vacuity: models satisfying the hypotheses -/

namespace NonVacuity

/-! ### Step 1: `G = ℚˣ × ℤ` acting on `ℚ` through `ℚˣ`; kernel `1 × ℤ`; `z = (2, 0)` -/

/-- `ℚˣ × ℤ` acting on `ℚ` by multiplication through the first factor. -/
noncomputable abbrev ρ₁ : Representation ℚ (ℚˣ × Multiplicative ℤ) ℚ :=
  (Algebra.lsmul ℚ ℚ ℚ).toMonoidHom.comp
    ((Units.coeHom ℚ).comp (MonoidHom.fst ℚˣ (Multiplicative ℤ)))

/-- `ρ₁ g w = g₁ w`. -/
theorem ρ₁_apply (g : ℚˣ × Multiplicative ℤ) (w : ℚ) : ρ₁ g w = (g.1 : ℚ) * w := by
  simp [ρ₁]

/-- The hypotheses of `cocycle_scalar_identity` / `coboundary_of_vanishes_on_kernel` hold together,
with a nontrivial kernel `H = 1 × ℤ`, the scalar element `z = (2, 0)` (`μ = 2`) and the nonzero
cocycle `g ↦ g₁ - 1`, which vanishes on `H`. -/
example : IsCoboundary ρ₁ (fun g => (g.1 : ℚ) - 1) := by
  have hH : ∀ h ∈ (MonoidHom.fst ℚˣ (Multiplicative ℤ)).ker, ∀ w : ℚ, ρ₁ h w = w := by
    intro h hh w
    rw [MonoidHom.mem_ker, MonoidHom.coe_fst] at hh
    rw [ρ₁_apply, hh, Units.val_one, one_mul]
  refine isCoboundary_of_vanishes_on_kernel _ hH (Units.mk0 2 two_ne_zero, 1) ?_ 2 ?_ ?_ ?_ ?_
  · intro g
    rw [mul_comm _ g, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  · ext
    simp
  · norm_num
  · intro g h
    simp only [ρ₁_apply, Prod.fst_mul, Units.val_mul]
    ring
  · intro h hh
    rw [MonoidHom.mem_ker, MonoidHom.coe_fst] at hh
    rw [hh, Units.val_one, sub_self]

/-! ### Step 2 (Goursat): `A = k = ℚ`, `W = ℚ` -/

/-- `ℚ`-linear endomorphisms of `ℚ` are scalars. -/
theorem hEnd_rat : ∀ φ : ℚ →ₗ[ℚ] ℚ, ∃ c : ℚ, φ = c • LinearMap.id :=
  fun φ => ⟨φ 1, LinearMap.ext_ring (by simp)⟩

/-- The hypotheses of `submodule_prod_eq_top_or_graph` are satisfiable. -/
example : (∀ φ : ℚ →ₗ[ℚ] ℚ, ∃ c : ℚ, φ = c • LinearMap.id) ∧ IsSimpleModule ℚ ℚ :=
  ⟨hEnd_rat, inferInstance⟩

/-! ### Step 2 (joint span): `G = H = ℚ²` acting trivially on `ℚ`, `c₁, c₂` the coordinates -/

/-- The hypotheses of `joint_span_eq_top` hold together: `A = k = ℚ`, `W = ℚ`,
`G = H = Multiplicative (ℚ × ℚ)` acting trivially, `c₁, c₂` the two coordinates. -/
example : Submodule.span ℚ (Set.range fun h : (⊤ : Subgroup (Multiplicative (ℚ × ℚ))) =>
    ((Multiplicative.toAdd (h : Multiplicative (ℚ × ℚ))).1,
      (Multiplicative.toAdd (h : Multiplicative (ℚ × ℚ))).2)) = ⊤ := by
  refine joint_span_eq_top (k := ℚ) (A := ℚ) hEnd_rat 1 1 ?_ ?_ ⊤ ?_
    (c₁ := fun g : Multiplicative (ℚ × ℚ) => (Multiplicative.toAdd g).1)
    (c₂ := fun g : Multiplicative (ℚ × ℚ) => (Multiplicative.toAdd g).2) ?_ ?_ ?_
  · rw [eq_top_iff]
    intro x _
    have h1 : (1 : ℚ) ∈ Set.range (1 : Multiplicative (ℚ × ℚ) →* ℚ) := ⟨1, rfl⟩
    simpa using Submodule.smul_mem _ x (Submodule.subset_span h1)
  · intro g w
    simp
  · intro h _ w
    simp
  · intro g h
    simp
  · intro g h
    simp
  · intro a b hab
    have h1 := hab (Multiplicative.ofAdd (1, 0)) trivial
    have h2 := hab (Multiplicative.ofAdd (0, 1)) trivial
    simp only [toAdd_ofAdd, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at h1 h2
    exact ⟨h1, h2⟩

/-! ### Step 3: `W = ℚ²`, `G = H = W × W` acting trivially, `π = id` -/

/-- The hypotheses of `exists_rank_two_localization` hold together. -/
example : ∃ h ∈ (⊤ : Subgroup (Multiplicative ((Fin 2 → ℚ) × (Fin 2 → ℚ)))),
    locDet (LinearMap.id : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ)) (Multiplicative.toAdd h).1
      (Multiplicative.toAdd h).2 ≠ 0 := by
  refine exists_rank_two_localization
    (1 : Representation ℚ (Multiplicative ((Fin 2 → ℚ) × (Fin 2 → ℚ))) (Fin 2 → ℚ)) ⊤
    (fun _ _ _ => rfl) (c₁ := fun g => (Multiplicative.toAdd g).1)
    (c₂ := fun g => (Multiplicative.toAdd g).2) ?_ ?_ LinearMap.id (fun x => ⟨x, rfl⟩) ?_
  · intro g h
    simp
  · intro g h
    simp
  · have huniv : (Set.range fun h : (⊤ : Subgroup (Multiplicative ((Fin 2 → ℚ) × (Fin 2 → ℚ)))) =>
        ((fun g => (Multiplicative.toAdd g).1) (h : Multiplicative ((Fin 2 → ℚ) × (Fin 2 → ℚ))),
          (fun g => (Multiplicative.toAdd g).2)
            (h : Multiplicative ((Fin 2 → ℚ) × (Fin 2 → ℚ))))) = Set.univ :=
      Set.eq_univ_of_forall fun x => ⟨⟨Multiplicative.ofAdd x, trivial⟩, rfl⟩
    rw [huniv, Submodule.span_univ]

/-! ### The assembled statement: `G = (W × W) ⋊ GL(W)` with `W = ℚ²` and `A = End(W)`

This is the shape of the manuscript's situation: the kernel `H = W × W` acts trivially, the
quotient `GL(W)` acts absolutely irreducibly (its `ℚ`-span is `End(W)`), the scalar `2` is
central, and the two coordinate cocycles have independent classes. -/

/-- The diagonal action of `GL(W)` on `W × W`, written multiplicatively. -/
noncomputable def diagAct : (Module.End ℚ (Fin 2 → ℚ))ˣ →* MulAut (Multiplicative
    ((Fin 2 → ℚ) × (Fin 2 → ℚ))) where
  toFun u := AddEquiv.toMultiplicative
    (DistribMulAction.toAddAut (Module.End ℚ (Fin 2 → ℚ))ˣ ((Fin 2 → ℚ) × (Fin 2 → ℚ)) u)
  map_one' := by ext x <;> simp
  map_mul' u v := by ext x <;> simp [mul_smul]

/-- The group `(W × W) ⋊ GL(W)`. -/
abbrev GW := Multiplicative ((Fin 2 → ℚ) × (Fin 2 → ℚ)) ⋊[diagAct] (Module.End ℚ (Fin 2 → ℚ))ˣ

/-- `(W × W) ⋊ GL(W)` acting on `W` through `GL(W)`. -/
noncomputable def ιW : GW →* Module.End ℚ (Fin 2 → ℚ) :=
  (Units.coeHom (Module.End ℚ (Fin 2 → ℚ))).comp SemidirectProduct.rightHom

/-- The `ℚ`-span of `GL(W)` is `End(W)`: `f = c - (c - f)` with `c` outside the finite spectrum. -/
theorem span_range_ιW : Submodule.span ℚ (Set.range ιW) = ⊤ := by
  rw [eq_top_iff]
  rintro f -
  obtain ⟨c, hc⟩ := (Module.End.finite_spectrum f).infinite_compl.nonempty
  have hu : IsUnit (algebraMap ℚ (Module.End ℚ (Fin 2 → ℚ)) c - f) := spectrum.notMem_iff.mp hc
  have h1 : (1 : Module.End ℚ (Fin 2 → ℚ)) ∈ Set.range ιW := ⟨1, by simp [ιW]⟩
  have h2 : (algebraMap ℚ (Module.End ℚ (Fin 2 → ℚ)) c - f) ∈ Set.range ιW :=
    ⟨SemidirectProduct.inr hu.unit, by simp [ιW]⟩
  have hf : f = c • (1 : Module.End ℚ (Fin 2 → ℚ)) -
      (algebraMap ℚ (Module.End ℚ (Fin 2 → ℚ)) c - f) := by
    rw [Algebra.algebraMap_eq_smul_one]
    abel
  rw [hf]
  exact sub_mem (Submodule.smul_mem _ c (Submodule.subset_span h1)) (Submodule.subset_span h2)

/-- `End(W)`-linear endomorphisms of `W` are scalars. -/
theorem hEnd_W : ∀ φ : (Fin 2 → ℚ) →ₗ[Module.End ℚ (Fin 2 → ℚ)] (Fin 2 → ℚ),
    ∃ c : ℚ, φ = c • LinearMap.id := by
  intro φ
  refine ⟨φ (Pi.single 0 1) 0, LinearMap.ext fun w => ?_⟩
  let f : Module.End ℚ (Fin 2 → ℚ) := (LinearMap.proj 0 : (Fin 2 → ℚ) →ₗ[ℚ] ℚ).smulRight w
  have hf : f • (Pi.single 0 1 : Fin 2 → ℚ) = w := by simp [f, Module.End.smul_def]
  calc φ w = φ (f • (Pi.single 0 1 : Fin 2 → ℚ)) := by rw [hf]
    _ = f • φ (Pi.single 0 1) := φ.map_smul f _
    _ = (φ (Pi.single 0 1) 0) • w := by simp [f, Module.End.smul_def]
    _ = ((φ (Pi.single 0 1) 0) • LinearMap.id :
        (Fin 2 → ℚ) →ₗ[Module.End ℚ (Fin 2 → ℚ)] (Fin 2 → ℚ)) w := rfl

/-- `(W × W) ⋊ GL(W)` acting on `W` through `GL(W)`, as a representation. -/
noncomputable abbrev ρW : Representation ℚ GW (Fin 2 → ℚ) := ιW

/-- `ρW g w = g.right w`. -/
theorem ρW_apply (g : GW) (w : Fin 2 → ℚ) :
    ρW g w = (g.right : Module.End ℚ (Fin 2 → ℚ)) w := rfl

/-- The scalar `2` as an element of `GL(W)`. -/
noncomputable def two : (Module.End ℚ (Fin 2 → ℚ))ˣ :=
  Units.map (algebraMap ℚ (Module.End ℚ (Fin 2 → ℚ))).toMonoidHom (Units.mk0 2 two_ne_zero)

/-- The unit `two` is the scalar `2`. -/
theorem coe_two : (two : Module.End ℚ (Fin 2 → ℚ)) = algebraMap ℚ _ 2 := rfl

/-- The hypotheses of `kernel_element_detects_two_classes` hold together, in the model
`G = (W × W) ⋊ GL(W)`, `H = W × W`, `z = 2 ∈ GL(W)`, `c₁, c₂` the two coordinate cocycles,
`π = id`. -/
example : ∃ h ∈ (SemidirectProduct.rightHom : GW →* _).ker,
    locDet (LinearMap.id : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ)) (Multiplicative.toAdd h.left).1
      (Multiplicative.toAdd h.left).2 ≠ 0 := by
  have hH : ∀ h ∈ (SemidirectProduct.rightHom : GW →* _).ker, ∀ w : Fin 2 → ℚ,
      ρW h w = w := by
    intro h hh w
    have hh' : h.right = 1 := hh
    rw [ρW_apply, hh', Units.val_one, Module.End.one_apply]
  refine kernel_element_detects_two_classes (A := Module.End ℚ (Fin 2 → ℚ)) hEnd_W ρW ιW
    span_range_ιW (fun _ _ => rfl) _ hH (SemidirectProduct.inr two) ?_ 2 ?_ ?_
    (c₁ := fun g => (Multiplicative.toAdd g.left).1) (c₂ := fun g => (Multiplicative.toAdd g.left).2)
    ?_ ?_ ?_ LinearMap.id (fun x => ⟨x, rfl⟩)
  · intro g
    have hc : ∀ r : (Module.End ℚ (Fin 2 → ℚ))ˣ, two * r = r * two := fun r =>
      Units.ext (by rw [Units.val_mul, Units.val_mul, coe_two, Algebra.commutes])
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      SemidirectProduct.rightHom_inr, hc, mul_inv_cancel_right, mul_inv_cancel]
  · ext w i
    simp [ιW, coe_two, Algebra.algebraMap_eq_smul_one]
  · norm_num
  · intro g h
    rw [ρW_apply]
    simp [diagAct, SemidirectProduct.mul_left, Units.smul_def, Module.End.smul_def]
  · intro g h
    rw [ρW_apply]
    simp [diagAct, SemidirectProduct.mul_left, Units.smul_def, Module.End.smul_def]
  · rintro a b ⟨w, hw⟩
    have h1 := hw (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single 0 1, 0)))
    have h2 := hw (SemidirectProduct.inl (Multiplicative.ofAdd (0, Pi.single 0 1)))
    have e1 := congrFun h1 0
    have e2 := congrFun h2 0
    simp [ιW] at e1 e2
    exact ⟨e1, e2⟩

end NonVacuity

end ZInQ.Manuscript.RC.Uniform

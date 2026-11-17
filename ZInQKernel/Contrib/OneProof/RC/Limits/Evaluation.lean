import Mathlib

/-!
# Lane RC6-limits: evaluation at a finite stage

This file formalizes the finite-stage linear algebra of the first two paragraphs of the proof of
Lemma `ex:limits-outer-evaluation` ("Evaluation, coefficient change and the outer DVR",
statement at tex lines 4651-4661, proof at tex lines 4673-4704).

* Section `DetectingLists` (tex 4689-4690): "A finite list of at most `dim V + dim W` evaluations
  already has that intersection. Choose and pad these lists at the finite stages".
* Section `KernelComputation` (tex 4686-4690): "take representatives `V` for `H^1` and coefficient
  space `W`. Evaluate `(c,w)` by `b_c(g)-(ρ(g)-1)w`. The intersection of all kernels is
  `(0,W^Γ)`."
* Section `FiniteStage` (tex 4674-4684): the identities (5.2)
  `e^1_g d = (ρ(g)-1) e^0`, `e^2_{g,h} d = ρ(g) e^1_h - e^1_{gh} + e^1_g`, and "A cycle therefore
  defines an abstract crossed homomorphism of the product group."
* Section `Sequences` (tex 4674-4683): evaluation at sequences `g = (g_i)` for the product group
  `∏_i G_i`, before any ultrafilter is applied.
* Section `Comparison` (tex 4690-4691): "The comparison to `[W → W^d]` is an isomorphism on `H^0`
  and injective on `H^1`", on Mathlib's `H0 A` and `H1 A`.
* Section `ConeContraction` (tex 4691-4695): the long exact sequence step, and its stability under
  every coefficient extension once a contraction of the cone in degree zero is retained.
* Sections `ComparisonCone` and `RetainedComparison` (tex 4686-4695): the same statements for the
  comparison of the global cochains, and of a retained model, with `[W → W^d]`.
* Section `Examples`: non-vacuity, including a concrete instance with `H^1 ≠ 0`.

Not formalized here (outside this file's scope): the ultrafilter quotient (tex 4681), the
cancellation of unit disks producing the retained cone contraction (tex 4692-4693, GLUE), and the
Selmer-complex discussion (tex 4695-4704).

Sign conventions. Mathlib's `groupCohomology.d₀₁ A` sends `w` to `g ↦ ρ(g) w - w`, and
`groupCohomology.d₁₂ A` sends `f` to `(g, h) ↦ ρ(g) (f h) - f (g * h) + f g`. These are exactly
the manuscript's formulas in (5.2) (and Mathlib's `comp_d₀₁_eq`, `comp_d₁₂_eq` identify them with
the differentials of `inhomogeneousCochains A`), so no sign departure arises anywhere below.

Global conventions (DEPARTUREs of form, recorded once here and in the docstrings):
* Elliot's group `Γ_K = ∏_i G_K` (with one simultaneous complex conjugation) is an arbitrary group
  `G` here; every statement is uniform in the group, so it applies to the product group.
* The coefficient space `W` is the underlying module of `A : Rep k G`.
* A list of `d` Galois elements is either a `List G` or, after padding, a tuple `Fin d → G`
  (this is the form in which padded lists pass to a common limit).
-/

universe u

namespace ZInQ.Manuscript.RC.Limits

open Module

/-! ## Detecting lists -/

section DetectingLists

/-- Intersection over a cons list (auxiliary). -/
theorem iInf_mem_cons {α ι : Type*} [CompleteLattice α] (p : ι → α) (a : ι) (L : List ι) :
    (⨅ x ∈ a :: L, p x) = p a ⊓ ⨅ x ∈ L, p x := by
  apply le_antisymm
  · exact le_inf (iInf₂_le a List.mem_cons_self)
      (le_iInf₂ fun x hx => iInf₂_le x (List.mem_cons_of_mem a hx))
  · refine le_iInf₂ fun x hx => ?_
    rcases List.mem_cons.1 hx with rfl | hx
    · exact inf_le_left
    · exact inf_le_right.trans (iInf₂_le x hx)

/-- A longer list has a smaller intersection (auxiliary). -/
theorem iInf_mem_anti {α ι : Type*} [CompleteLattice α] (p : ι → α) {L L' : List ι}
    (h : ∀ x ∈ L, x ∈ L') : (⨅ x ∈ L', p x) ≤ ⨅ x ∈ L, p x :=
  le_iInf₂ fun x hx => iInf₂_le x (h x hx)

/-- The full intersection is below every list intersection (auxiliary). -/
theorem iInf_le_iInf_mem {α ι : Type*} [CompleteLattice α] (p : ι → α) (L : List ι) :
    (⨅ x, p x) ≤ ⨅ x ∈ L, p x :=
  le_iInf₂ fun x _ => iInf_le p x

/-- The intersection over a list equals the intersection over its entries `L.get i`
(auxiliary; converts a list of length `d` into a tuple `Fin d → ι`). -/
theorem iInf_get_eq_iInf_mem {α ι : Type*} [CompleteLattice α] (p : ι → α) (L : List ι) :
    (⨅ i : Fin L.length, p (L.get i)) = ⨅ x ∈ L, p x := by
  apply le_antisymm
  · refine le_iInf₂ fun x hx => ?_
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hx
    exact iInf_le (fun i => p (L.get i)) i
  · exact le_iInf fun i => iInf₂_le (L.get i) (List.get_mem L i)

variable {F X Y Γ : Type*} [Field F] [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]

/-- **Detecting lists** (tex 4689-4690: "A finite list of at most `dim V + dim W` evaluations
already has that intersection"). Kind: PROVED.

For any family `f : Γ → (X →ₗ[F] Y)` of linear maps on a finite-dimensional `F`-vector space `X`
there is a list `L` of at most `dim X` indices whose kernels already cut out the intersection of
all the kernels. Proof: a strictly descending chain of subspaces of `X` has length at most
`dim X`; we add one index at a time, each time strictly shrinking the current intersection.

DEPARTURE (form only): stated for an arbitrary family of linear maps on an arbitrary
finite-dimensional space `X`; the manuscript's case is `X = V × W` with `dim X = dim V + dim W`,
see `exists_detecting_list_pairEvaluation`. -/
theorem exists_detecting_list [FiniteDimensional F X] (f : Γ → X →ₗ[F] Y) :
    ∃ L : List Γ, L.length ≤ finrank F X ∧
      (⨅ g ∈ L, LinearMap.ker (f g)) = ⨅ g, LinearMap.ker (f g) := by
  suffices H : ∀ m : ℕ, ∀ L : List Γ,
      finrank F ↥(⨅ g ∈ L, LinearMap.ker (f g)) = m → L.length + m ≤ finrank F X →
      ∃ L' : List Γ, L'.length ≤ finrank F X ∧
        (⨅ g ∈ L', LinearMap.ker (f g)) = ⨅ g, LinearMap.ker (f g) by
    have h0 : (⨅ g ∈ ([] : List Γ), LinearMap.ker (f g)) = ⊤ := by simp
    refine H _ [] rfl ?_
    rw [h0, finrank_top, List.length_nil, zero_add]
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro L hm hlen
    by_cases hle : (⨅ g ∈ L, LinearMap.ker (f g)) ≤ ⨅ g, LinearMap.ker (f g)
    · exact ⟨L, by omega, le_antisymm hle (iInf_le_iInf_mem _ L)⟩
    · obtain ⟨g, hg⟩ : ∃ g, ¬ (⨅ x ∈ L, LinearMap.ker (f x)) ≤ LinearMap.ker (f g) := by
        by_contra! h
        exact hle (le_iInf h)
      have hlt : (⨅ x ∈ g :: L, LinearMap.ker (f x)) < ⨅ x ∈ L, LinearMap.ker (f x) := by
        rw [iInf_mem_cons]
        refine lt_of_le_of_ne inf_le_right fun h => hg ?_
        rw [← h]
        exact inf_le_left
      have hrank := Submodule.finrank_lt_finrank_of_lt hlt
      rw [hm] at hrank
      exact ih _ hrank (g :: L) rfl (by rw [List.length_cons]; omega)

/-- **Padding a detecting list** (tex 4690: "Choose and pad these lists at the finite stages
before taking their common limit"). Kind: PROVED.

Appending copies of any index `g₀` to a detecting list keeps it detecting; this produces a
detecting list of any prescribed length `N ≥ L.length`. -/
theorem detecting_list_pad (f : Γ → X →ₗ[F] Y) {L : List Γ}
    (hL : (⨅ g ∈ L, LinearMap.ker (f g)) = ⨅ g, LinearMap.ker (f g)) (g₀ : Γ) {N : ℕ}
    (hN : L.length ≤ N) :
    (L ++ List.replicate (N - L.length) g₀).length = N ∧
      (⨅ g ∈ L ++ List.replicate (N - L.length) g₀, LinearMap.ker (f g)) =
        ⨅ g, LinearMap.ker (f g) := by
  refine ⟨by rw [List.length_append, List.length_replicate]; omega,
    le_antisymm ?_ (iInf_le_iInf_mem _ _)⟩
  rw [← hL]
  exact iInf_mem_anti _ fun x hx => List.mem_append_left _ hx

/-- **Detecting lists of prescribed length** (tex 4689-4690). Kind: PROVED.

For every `N ≥ dim X` (and `Γ` nonempty) there is a detecting list of length exactly `N`. -/
theorem exists_detecting_list_of_length [FiniteDimensional F X] [Nonempty Γ]
    (f : Γ → X →ₗ[F] Y) {N : ℕ} (hN : finrank F X ≤ N) :
    ∃ L : List Γ, L.length = N ∧
      (⨅ g ∈ L, LinearMap.ker (f g)) = ⨅ g, LinearMap.ker (f g) := by
  obtain ⟨L, hlen, hL⟩ := exists_detecting_list f
  exact ⟨_, detecting_list_pad f hL (Classical.arbitrary Γ) (hlen.trans hN)⟩

/-- **Padded detecting tuples** (tex 4689-4690). Kind: PROVED.

The padded list as a tuple `γ : Fin N → Γ`, the form in which the finite-stage lists of a common
length `N` are passed to their common limit. -/
theorem exists_detecting_tuple [FiniteDimensional F X] [Nonempty Γ]
    (f : Γ → X →ₗ[F] Y) {N : ℕ} (hN : finrank F X ≤ N) :
    ∃ γ : Fin N → Γ, (⨅ i, LinearMap.ker (f (γ i))) = ⨅ g, LinearMap.ker (f g) := by
  obtain ⟨L, rfl, hL⟩ := exists_detecting_list_of_length f hN
  exact ⟨L.get, (iInf_get_eq_iInf_mem (fun g => LinearMap.ker (f g)) L).trans hL⟩

end DetectingLists

/-! ## The kernel computation -/

section KernelComputation

open groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G)

/-- **The evaluation of a pair** `e_g : V × W → W`, `(c, w) ↦ b_c(g) - (ρ(g) - 1) w`
(tex 4687-4688: "Evaluate `(c,w)` by `b_c(g)-(ρ(g)-1)w`"). Kind: definition.

DEPARTURE (form only): the representatives `V` are a submodule of the 1-cochains `G → W`, so the
cocycle `b_c` attached to `c ∈ V` is `c` itself. -/
def pairEvaluation (V : Submodule k (G → A)) (g : G) : (V × A) →ₗ[k] A :=
  (LinearMap.proj g : (G → A) →ₗ[k] A) ∘ₗ V.subtype ∘ₗ LinearMap.fst k V A -
    (A.ρ g - 1) ∘ₗ LinearMap.snd k V A

theorem pairEvaluation_apply (V : Submodule k (G → A)) (g : G) (c : V) (w : A) :
    pairEvaluation A V g (c, w) = (c : G → A) g - (A.ρ g w - w) := rfl

/-- **The intersection of all kernels is `(0, W^Γ)`** (tex 4688-4689). Kind: PROVED.

If `V` meets the 1-coboundaries only in `0` (as representatives for `H^1` do), then
`⋂_g ker e_g = 0 × W^G`. Proof: `(c, w)` lies in every kernel iff `c = d₀₁ w` is a coboundary;
then `c ∈ V ∩ B^1 = 0` and `ρ(g) w = w` for all `g`.

DEPARTURE (weaker hypotheses): only `V ⊓ B^1 = 0` is used, not `V ≤ Z^1`, and `k` may be any
commutative ring. -/
theorem iInf_ker_pairEvaluation (V : Submodule k (G → A)) (hV : V ⊓ coboundaries₁ A = ⊥) :
    (⨅ g, LinearMap.ker (pairEvaluation A V g)) = (⊥ : Submodule k V).prod A.ρ.invariants := by
  ext ⟨c, w⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, pairEvaluation_apply, Submodule.mem_prod,
    Submodule.mem_bot, Representation.mem_invariants]
  constructor
  · intro h
    have hcw : ∀ g, (c : G → A) g = A.ρ g w - w := fun g => sub_eq_zero.1 (h g)
    have hcB : (c : G → A) ∈ V ⊓ coboundaries₁ A :=
      Submodule.mem_inf.2 ⟨c.2, LinearMap.mem_range.2 ⟨w, funext fun g => by
        rw [d₀₁_hom_apply, hcw g]⟩⟩
    rw [hV, Submodule.mem_bot] at hcB
    refine ⟨Submodule.coe_eq_zero.1 hcB, fun g => ?_⟩
    have := hcw g
    rw [hcB, Pi.zero_apply, eq_comm, sub_eq_zero] at this
    exact this
  · rintro ⟨rfl, hw⟩ g
    simp [hw g]

/-- **The kernel computation, membership form** (tex 4688-4689): `(c, w)` is killed by every
evaluation iff `c = 0` and `w ∈ W^G`. Kind: PROVED. -/
theorem mem_iInf_ker_pairEvaluation_iff (V : Submodule k (G → A))
    (hV : V ⊓ coboundaries₁ A = ⊥) (c : V) (w : A) :
    (c, w) ∈ (⨅ g, LinearMap.ker (pairEvaluation A V g)) ↔ c = 0 ∧ w ∈ A.ρ.invariants := by
  rw [iInf_ker_pairEvaluation A V hV, Submodule.mem_prod, Submodule.mem_bot]

end KernelComputation

section KernelDetection

open groupCohomology

variable {k G : Type u} [Field k] [Group G] (A : Rep.{u} k G)

/-- **A detecting list of at most `dim V + dim W` evaluations** (tex 4686-4690). Kind: PROVED.

Over a field, for finite-dimensional representatives `V` (meeting `B^1` only in `0`) and
finite-dimensional coefficient space `W`, some list of at most `dim V + dim W` group elements
already has kernel intersection `(0, W^G)`. -/
theorem exists_detecting_list_pairEvaluation (V : Submodule k (G → A))
    (hV : V ⊓ coboundaries₁ A = ⊥) [FiniteDimensional k V] [FiniteDimensional k A] :
    ∃ L : List G, L.length ≤ finrank k V + finrank k A ∧
      (⨅ g ∈ L, LinearMap.ker (pairEvaluation A V g)) =
        (⊥ : Submodule k V).prod A.ρ.invariants := by
  obtain ⟨L, hlen, hL⟩ := exists_detecting_list (pairEvaluation A V)
  exact ⟨L, by rwa [Module.finrank_prod] at hlen, hL.trans (iInf_ker_pairEvaluation A V hV)⟩

/-- **Chosen and padded detecting lists** (tex 4686-4690, "Choose and pad these lists").
Kind: PROVED.

For every `N ≥ dim V + dim W` there is a tuple of exactly `N` group elements whose evaluations
have kernel intersection `(0, W^G)`. -/
theorem exists_detecting_tuple_pairEvaluation (V : Submodule k (G → A))
    (hV : V ⊓ coboundaries₁ A = ⊥) [FiniteDimensional k V] [FiniteDimensional k A] {N : ℕ}
    (hN : finrank k V + finrank k A ≤ N) :
    ∃ γ : Fin N → G, (⨅ i, LinearMap.ker (pairEvaluation A V (γ i))) =
      (⊥ : Submodule k V).prod A.ρ.invariants := by
  obtain ⟨γ, hγ⟩ := exists_detecting_tuple (pairEvaluation A V) (N := N)
    (by rwa [Module.finrank_prod])
  exact ⟨γ, hγ.trans (iInf_ker_pairEvaluation A V hV)⟩

end KernelDetection

/-! ## The identities (5.2) at a finite stage -/

section FiniteStage

open CategoryTheory groupCohomology

variable {k G : Type u} [CommRing k] [Group G] {A : Rep.{u} k G}
variable {C₀ C₁ C₂ : Type*} [AddCommGroup C₀] [Module k C₀] [AddCommGroup C₁] [Module k C₁]
  [AddCommGroup C₂] [Module k C₂]

/-- The degree-zero evaluation `e^0 := ι^0` of a retained cochain map (tex 4675-4678).
Kind: definition. -/
def evalZero (ι₀ : C₀ →ₗ[k] A) : C₀ →ₗ[k] A := ι₀

/-- The degree-one evaluation `e^1_g := ev_g ∘ ι^1` at a group element `g` (tex 4675-4678).
Kind: definition. -/
def evalOne (ι₁ : C₁ →ₗ[k] (G → A)) (g : G) : C₁ →ₗ[k] A :=
  (LinearMap.proj g : (G → A) →ₗ[k] A) ∘ₗ ι₁

/-- The degree-two evaluation `e^2_{g,h} := ev_{(g,h)} ∘ ι^2` (tex 4675-4678).
Kind: definition. -/
def evalTwo (ι₂ : C₂ →ₗ[k] (G × G → A)) (g h : G) : C₂ →ₗ[k] A :=
  (LinearMap.proj (g, h) : (G × G → A) →ₗ[k] A) ∘ₗ ι₂

/-- **(5.2), first identity** `e^1_g d = (ρ(g) - 1) e^0` (tex 4677-4679). Kind: PROVED.

Hypothesis: `ι = (ι^0, ι^1)` commutes with the differentials, `d₀₁ ∘ ι^0 = ι^1 ∘ d`.
No sign departure: Mathlib's `d₀₁` is `w ↦ (g ↦ ρ(g) w - w)`. -/
theorem evalOne_comp_d (d₀ : C₀ →ₗ[k] C₁) {ι₀ : C₀ →ₗ[k] A} {ι₁ : C₁ →ₗ[k] (G → A)}
    (h₀ : (d₀₁ A).hom ∘ₗ ι₀ = ι₁ ∘ₗ d₀) (g : G) :
    evalOne ι₁ g ∘ₗ d₀ = (A.ρ g - 1) ∘ₗ evalZero ι₀ := by
  refine LinearMap.ext fun x => ?_
  change ι₁ (d₀ x) g = A.ρ g (ι₀ x) - ι₀ x
  rw [← LinearMap.comp_apply ι₁ d₀, ← h₀, LinearMap.comp_apply, d₀₁_hom_apply]

/-- **(5.2), second identity** `e^2_{g,h} d = ρ(g) e^1_h - e^1_{gh} + e^1_g`
(tex 4677-4679). Kind: PROVED.

Hypothesis: `ι = (ι^1, ι^2)` commutes with the differentials, `d₁₂ ∘ ι^1 = ι^2 ∘ d`.
No sign departure: Mathlib's `d₁₂` is `f ↦ ((g, h) ↦ ρ(g) (f h) - f (g h) + f g)`, which is
exactly Elliot's right-hand side. -/
theorem evalTwo_comp_d (d₁ : C₁ →ₗ[k] C₂) {ι₁ : C₁ →ₗ[k] (G → A)}
    {ι₂ : C₂ →ₗ[k] (G × G → A)} (h₁ : (d₁₂ A).hom ∘ₗ ι₁ = ι₂ ∘ₗ d₁) (g h : G) :
    evalTwo ι₂ g h ∘ₗ d₁ = A.ρ g ∘ₗ evalOne ι₁ h - evalOne ι₁ (g * h) + evalOne ι₁ g := by
  refine LinearMap.ext fun y => ?_
  change ι₂ (d₁ y) (g, h) = A.ρ g (ι₁ y h) - ι₁ y (g * h) + ι₁ y g
  rw [← LinearMap.comp_apply ι₂ d₁, ← h₁, LinearMap.comp_apply, d₁₂_hom_apply]

/-- **A cycle defines a crossed homomorphism** (tex 4682-4683: "A cycle therefore defines an
abstract crossed homomorphism of the product group"). Kind: PROVED.

If `d z = 0` then `g ↦ e^1_g z` lies in Mathlib's 1-cocycles `cocycles₁ A`. -/
theorem evalOne_mem_cocycles₁ {d₁ : C₁ →ₗ[k] C₂} {ι₁ : C₁ →ₗ[k] (G → A)}
    {ι₂ : C₂ →ₗ[k] (G × G → A)} (h₁ : (d₁₂ A).hom ∘ₗ ι₁ = ι₂ ∘ₗ d₁) {z : C₁}
    (hz : d₁ z = 0) : (fun g => evalOne ι₁ g z) ∈ cocycles₁ A := by
  have hfun : (fun g => evalOne ι₁ g z) = ι₁ z := rfl
  rw [hfun]
  exact LinearMap.mem_ker.2 (by rw [← LinearMap.comp_apply, h₁, LinearMap.comp_apply, hz,
    map_zero])

/-- **The crossed homomorphism identity** `e^1_{gh} z = ρ(g) e^1_h z + e^1_g z` for a cycle
`z` (tex 4682-4683). Kind: PROVED. -/
theorem evalOne_mul {d₁ : C₁ →ₗ[k] C₂} {ι₁ : C₁ →ₗ[k] (G → A)}
    {ι₂ : C₂ →ₗ[k] (G × G → A)} (h₁ : (d₁₂ A).hom ∘ₗ ι₁ = ι₂ ∘ₗ d₁) {z : C₁}
    (hz : d₁ z = 0) (g h : G) :
    evalOne ι₁ (g * h) z = A.ρ g (evalOne ι₁ h z) + evalOne ι₁ g z :=
  (mem_cocycles₁_iff _).1 (evalOne_mem_cocycles₁ h₁ hz) g h

/-- The crossed homomorphism of a cycle, as an element of `cocycles₁ A` (tex 4682-4683).
Kind: definition. -/
def cycleCrossedHom {d₁ : C₁ →ₗ[k] C₂} {ι₁ : C₁ →ₗ[k] (G → A)}
    {ι₂ : C₂ →ₗ[k] (G × G → A)} (h₁ : (d₁₂ A).hom ∘ₗ ι₁ = ι₂ ∘ₗ d₁) (z : C₁)
    (hz : d₁ z = 0) : cocycles₁ A :=
  ⟨fun g => evalOne ι₁ g z, evalOne_mem_cocycles₁ h₁ hz⟩

/-- **Representatives transported by a retained cochain map** (tex 4686-4687: "take
representatives `V` for `H^1`"). Kind: PROVED.

If `ι` induces an injection on `H^1` (a cycle `z` with `ι^1 z ∈ B^1` is a boundary) and `V₀` is a
space of cycles meeting the boundaries only in `0` (representatives for `H^1` of the model), then
its image `V = ι^1(V₀)` satisfies the two hypotheses `V ≤ Z^1`, `V ⊓ B^1 = 0` used above. -/
theorem map_representatives {d₀ : C₀ →ₗ[k] C₁} {d₁ : C₁ →ₗ[k] C₂} {ι₁ : C₁ →ₗ[k] (G → A)}
    {ι₂ : C₂ →ₗ[k] (G × G → A)} (h₁ : (d₁₂ A).hom ∘ₗ ι₁ = ι₂ ∘ₗ d₁)
    (hinj : ∀ z, d₁ z = 0 → ι₁ z ∈ coboundaries₁ A → z ∈ LinearMap.range d₀)
    (V₀ : Submodule k C₁) (hV₀ : V₀ ≤ LinearMap.ker d₁) (hV₀B : V₀ ⊓ LinearMap.range d₀ = ⊥) :
    V₀.map ι₁ ≤ cocycles₁ A ∧ V₀.map ι₁ ⊓ coboundaries₁ A = ⊥ := by
  constructor
  · rintro _ ⟨z, hz, rfl⟩
    exact evalOne_mem_cocycles₁ h₁ (LinearMap.mem_ker.1 (hV₀ hz))
  · rw [eq_bot_iff]
    rintro _ ⟨⟨z, hz, rfl⟩, hB⟩
    have hz0 : z ∈ V₀ ⊓ LinearMap.range d₀ :=
      ⟨hz, hinj z (LinearMap.mem_ker.1 (hV₀ hz)) hB⟩
    rw [hV₀B, Submodule.mem_bot] at hz0
    rw [Submodule.mem_bot, hz0, map_zero]

/-- **Injectivity on `H^1` of a cochain map onto in degree zero and injective in degree one**
(tex 4655-4656: "The induced map on `H^1` is injective"). Kind: PROVED.

If `ι^0` is surjective and `ι^1` is injective (as for an inclusion of cochains that is the
identity in degree zero), a cochain `z` with `ι^1 z ∈ B^1` is a boundary. -/
theorem mem_range_of_ι₁_mem_coboundaries₁ {d₀ : C₀ →ₗ[k] C₁} {ι₀ : C₀ →ₗ[k] A}
    {ι₁ : C₁ →ₗ[k] (G → A)} (h₀ : (d₀₁ A).hom ∘ₗ ι₀ = ι₁ ∘ₗ d₀)
    (hsurj : Function.Surjective ι₀) (hinj : Function.Injective ι₁) {z : C₁}
    (hz : ι₁ z ∈ coboundaries₁ A) : z ∈ LinearMap.range d₀ := by
  obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hz
  obtain ⟨x, rfl⟩ := hsurj w
  refine ⟨x, hinj ?_⟩
  rw [← hw, ← LinearMap.comp_apply ι₁ d₀, ← h₀, LinearMap.comp_apply]

variable (A) in
/-- **Retained cochain maps into Mathlib's inhomogeneous cochains** (tex 4674-4676). Kind: PROVED.

A morphism of cochain complexes `φ : C ⟶ inhomogeneousCochains A` gives, after Mathlib's
identifications `cochainsIso₀/₁/₂` of the low-degree cochains with `A`, `G → A`, `G × G → A`,
maps `ι^0, ι^1, ι^2` satisfying the two hypotheses of `evalOne_comp_d` and `evalTwo_comp_d`. -/
theorem chainMap_lowDegree_comm {C : CochainComplex (ModuleCat.{u} k) ℕ}
    (φ : C ⟶ inhomogeneousCochains A) :
    (d₀₁ A).hom ∘ₗ (φ.f 0 ≫ (cochainsIso₀ A).hom).hom =
        (φ.f 1 ≫ (cochainsIso₁ A).hom).hom ∘ₗ (C.d 0 1).hom ∧
      (d₁₂ A).hom ∘ₗ (φ.f 1 ≫ (cochainsIso₁ A).hom).hom =
        (φ.f 2 ≫ (cochainsIso₂ A).hom).hom ∘ₗ (C.d 1 2).hom := by
  constructor
  · rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp]
    congr 1
    rw [Category.assoc, comp_d₀₁_eq, ← Category.assoc, φ.comm,
      Category.assoc]
  · rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp]
    congr 1
    rw [Category.assoc, comp_d₁₂_eq, ← Category.assoc, φ.comm,
      Category.assoc]

end FiniteStage

/-! ## Evaluation at sequences: the product group -/

section Sequences

open groupCohomology

variable {k : Type u} [CommRing k] {I : Type u} {Gs : I → Type u} [∀ i, Group (Gs i)]

/-- The product group `∏_i G_i` acting componentwise on `∏_i W_i` (tex 4674-4676: "For fixed `K`
let `Γ_K = ∏_i G_K`"; there all `G_i = G_K`). Kind: definition. -/
def piRepresentation (As : ∀ i, Rep.{u} k (Gs i)) :
    Representation k (∀ i, Gs i) (∀ i, As i) where
  toFun g := LinearMap.pi fun i => (As i).ρ (g i) ∘ₗ LinearMap.proj i
  map_one' := LinearMap.ext fun a => funext fun i => by simp
  map_mul' g h := LinearMap.ext fun a => funext fun i => by simp

/-- The product representation as an object of `Rep`. -/
abbrev piRep (As : ∀ i, Rep.{u} k (Gs i)) : Rep.{u} k (∀ i, Gs i) := Rep.of (piRepresentation As)

theorem piRep_ρ_apply (As : ∀ i, Rep.{u} k (Gs i)) (g : ∀ i, Gs i) (a : ∀ i, As i) (i : I) :
    (piRep As).ρ g a i = (As i).ρ (g i) (a i) := rfl

variable {As : ∀ i, Rep.{u} k (Gs i)}
variable {C₀ C₁ C₂ : I → Type*} [∀ i, AddCommGroup (C₀ i)] [∀ i, Module k (C₀ i)]
  [∀ i, AddCommGroup (C₁ i)] [∀ i, Module k (C₁ i)] [∀ i, AddCommGroup (C₂ i)]
  [∀ i, Module k (C₂ i)]

/-- A sequence of differentials, acting componentwise (tex 4675). Kind: definition. -/
def seqDiff {M N : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)] (d : ∀ i, M i →ₗ[k] N i) :
    (∀ i, M i) →ₗ[k] (∀ i, N i) :=
  LinearMap.pi fun i => d i ∘ₗ LinearMap.proj i

/-- Degree-zero evaluation of a sequence of retained cochain maps (tex 4675-4676).
Kind: definition. -/
def seqι₀ (ι₀ : ∀ i, C₀ i →ₗ[k] As i) : (∀ i, C₀ i) →ₗ[k] piRep As :=
  LinearMap.pi fun i => ι₀ i ∘ₗ LinearMap.proj i

/-- Degree-one evaluation at sequences `g = (g_i)`: `z ↦ (g ↦ (ι^1_i(z_i)(g_i))_i)`
(tex 4675-4676). Kind: definition. -/
def seqι₁ (ι₁ : ∀ i, C₁ i →ₗ[k] (Gs i → As i)) :
    (∀ i, C₁ i) →ₗ[k] ((∀ i, Gs i) → piRep As) where
  toFun z g i := ι₁ i (z i) (g i)
  map_add' z z' := funext fun g => funext fun i => by simp
  map_smul' c z := funext fun g => funext fun i => by simp

/-- Degree-two evaluation at pairs of sequences `g = (g_i), h = (h_i)`:
`z ↦ ((g, h) ↦ (ι^2_i(z_i)(g_i, h_i))_i)` (tex 4675-4676). Kind: definition. -/
def seqι₂ (ι₂ : ∀ i, C₂ i →ₗ[k] (Gs i × Gs i → As i)) :
    (∀ i, C₂ i) →ₗ[k] ((∀ i, Gs i) × (∀ i, Gs i) → piRep As) where
  toFun z gh i := ι₂ i (z i) (gh.1 i, gh.2 i)
  map_add' z z' := funext fun gh => funext fun i => by simp
  map_smul' c z := funext fun gh => funext fun i => by simp

/-- **Evaluation at sequences is a retained cochain map, degree 0 → 1** (tex 4675-4679).
Kind: PROVED. -/
theorem seq_comm₀ (d₀ : ∀ i, C₀ i →ₗ[k] C₁ i) {ι₀ : ∀ i, C₀ i →ₗ[k] As i}
    {ι₁ : ∀ i, C₁ i →ₗ[k] (Gs i → As i)}
    (h₀ : ∀ i, (d₀₁ (As i)).hom ∘ₗ ι₀ i = ι₁ i ∘ₗ d₀ i) :
    (d₀₁ (piRep As)).hom ∘ₗ seqι₀ ι₀ = seqι₁ ι₁ ∘ₗ seqDiff d₀ := by
  refine LinearMap.ext fun z => funext fun g => funext fun i => ?_
  change (As i).ρ (g i) (ι₀ i (z i)) - ι₀ i (z i) = ι₁ i (d₀ i (z i)) (g i)
  rw [← LinearMap.comp_apply (ι₁ i) (d₀ i), ← h₀ i, LinearMap.comp_apply, d₀₁_hom_apply]

/-- **Evaluation at sequences is a retained cochain map, degree 1 → 2** (tex 4675-4679).
Kind: PROVED. -/
theorem seq_comm₁ (d₁ : ∀ i, C₁ i →ₗ[k] C₂ i) {ι₁ : ∀ i, C₁ i →ₗ[k] (Gs i → As i)}
    {ι₂ : ∀ i, C₂ i →ₗ[k] (Gs i × Gs i → As i)}
    (h₁ : ∀ i, (d₁₂ (As i)).hom ∘ₗ ι₁ i = ι₂ i ∘ₗ d₁ i) :
    (d₁₂ (piRep As)).hom ∘ₗ seqι₁ ι₁ = seqι₂ ι₂ ∘ₗ seqDiff d₁ := by
  refine LinearMap.ext fun z => funext fun gh => funext fun i => ?_
  change (As i).ρ (gh.1 i) (ι₁ i (z i) (gh.2 i)) - ι₁ i (z i) (gh.1 i * gh.2 i) +
      ι₁ i (z i) (gh.1 i) = ι₂ i (d₁ i (z i)) (gh.1 i, gh.2 i)
  rw [← LinearMap.comp_apply (ι₂ i) (d₁ i), ← h₁ i, LinearMap.comp_apply, d₁₂_hom_apply]

/-- **(5.2) at arbitrary sequences** `g = (g_i), h = (h_i)` (tex 4675-4679: "Evaluation of
retained cochain maps at arbitrary sequences `g=(g_i),h=(h_i)` gives (5.2)"). Kind: PROVED.

Before any ultrafilter is applied: the identities hold in `∏_i W_i` for the product group. -/
theorem seq_fiveTwo (d₀ : ∀ i, C₀ i →ₗ[k] C₁ i) (d₁ : ∀ i, C₁ i →ₗ[k] C₂ i)
    {ι₀ : ∀ i, C₀ i →ₗ[k] As i} {ι₁ : ∀ i, C₁ i →ₗ[k] (Gs i → As i)}
    {ι₂ : ∀ i, C₂ i →ₗ[k] (Gs i × Gs i → As i)}
    (h₀ : ∀ i, (d₀₁ (As i)).hom ∘ₗ ι₀ i = ι₁ i ∘ₗ d₀ i)
    (h₁ : ∀ i, (d₁₂ (As i)).hom ∘ₗ ι₁ i = ι₂ i ∘ₗ d₁ i) (g h : ∀ i, Gs i) :
    evalOne (seqι₁ ι₁) g ∘ₗ seqDiff d₀ = ((piRep As).ρ g - 1) ∘ₗ evalZero (seqι₀ ι₀) ∧
      evalTwo (seqι₂ ι₂) g h ∘ₗ seqDiff d₁ =
        (piRep As).ρ g ∘ₗ evalOne (seqι₁ ι₁) h - evalOne (seqι₁ ι₁) (g * h) +
          evalOne (seqι₁ ι₁) g :=
  ⟨evalOne_comp_d _ (seq_comm₀ d₀ h₀) g, evalTwo_comp_d _ (seq_comm₁ d₁ h₁) g h⟩

/-- **A sequence of cycles defines an abstract crossed homomorphism of the product group**
(tex 4682-4683). Kind: PROVED.

DEPARTURE (scope): this is the statement before the ultrafilter quotient of tex 4681 ("One fixed
ultrafilter supplies these identities for all sequences"), which is not formalized here; no
continuity on a single original Galois group is asserted (tex 4683-4684). -/
theorem seq_cycle_mem_cocycles₁ (d₁ : ∀ i, C₁ i →ₗ[k] C₂ i)
    {ι₁ : ∀ i, C₁ i →ₗ[k] (Gs i → As i)} {ι₂ : ∀ i, C₂ i →ₗ[k] (Gs i × Gs i → As i)}
    (h₁ : ∀ i, (d₁₂ (As i)).hom ∘ₗ ι₁ i = ι₂ i ∘ₗ d₁ i) {z : ∀ i, C₁ i}
    (hz : ∀ i, d₁ i (z i) = 0) :
    (fun g => evalOne (seqι₁ ι₁) g z) ∈ cocycles₁ (piRep As) :=
  evalOne_mem_cocycles₁ (seq_comm₁ d₁ h₁) (funext hz)

end Sequences

/-! ## The comparison to `[W → W^d]` -/

section Comparison

open groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G)

/-- The differential of the two-term complex `[W → W^d]` attached to `γ = (g_1, …, g_d)`:
`w ↦ (ρ(g_i) w - w)_i` (tex 4690). Kind: definition. -/
def listDifferential {d : ℕ} (γ : Fin d → G) : A →ₗ[k] (Fin d → A) :=
  LinearMap.pi fun i => A.ρ (γ i) - 1

/-- The degree-one component of the comparison from `[W → (G → W)]` to `[W → W^d]`:
`c ↦ (c(g_i))_i` (tex 4690). The degree-zero component is the identity of `W`.
Kind: definition. -/
def listEvaluation {d : ℕ} (γ : Fin d → G) : (G → A) →ₗ[k] (Fin d → A) :=
  LinearMap.funLeft k A γ

theorem listDifferential_apply {d : ℕ} (γ : Fin d → G) (w : A) (i : Fin d) :
    listDifferential A γ w i = A.ρ (γ i) w - w := rfl

theorem listEvaluation_apply {d : ℕ} (γ : Fin d → G) (c : G → A) (i : Fin d) :
    listEvaluation A γ c i = c (γ i) := rfl

/-- **The comparison is a map of complexes** (tex 4690). Kind: PROVED.

`(id_W, listEvaluation)` commutes with the differentials `d₀₁` and `listDifferential`. -/
theorem listEvaluation_comp_d₀₁ {d : ℕ} (γ : Fin d → G) :
    listEvaluation A γ ∘ₗ (d₀₁ A).hom = listDifferential A γ :=
  LinearMap.ext fun _ => funext fun _ => rfl

/-- **`H^0` of `[W → W^d]` for a detecting list** (tex 4690-4691: "The comparison to `[W → W^d]`
is an isomorphism on `H^0`"). Kind: PROVED.

If the tuple `γ` detects (kernel intersection `(0, W^G)` on `V × W`), then the degree-zero
cohomology `ker(w ↦ (ρ(g_i) w - w)_i)` of `[W → W^d]` is exactly `W^G`. -/
theorem ker_listDifferential (V : Submodule k (G → A)) {d : ℕ} (γ : Fin d → G)
    (hdet : (⨅ i, LinearMap.ker (pairEvaluation A V (γ i))) =
      (⊥ : Submodule k V).prod A.ρ.invariants) :
    LinearMap.ker (listDifferential A γ) = A.ρ.invariants := by
  ext w
  rw [LinearMap.mem_ker]
  constructor
  · intro hw
    have hmem : ((0 : V), w) ∈ ⨅ i, LinearMap.ker (pairEvaluation A V (γ i)) := by
      rw [Submodule.mem_iInf]
      intro i
      have hi : A.ρ (γ i) w - w = 0 := congrFun hw i
      rw [LinearMap.mem_ker, pairEvaluation_apply, hi, sub_zero]
      rfl
    rw [hdet, Submodule.mem_prod] at hmem
    exact hmem.2
  · intro hw
    funext i
    rw [listDifferential_apply, (Representation.mem_invariants A.ρ w).1 hw (γ i), sub_self]
    rfl

/-- **The comparison is an isomorphism on `H^0`** (tex 4690-4691). Kind: PROVED.

Since the degree-zero component of the comparison is the identity of `W`, the induced map on
`H^0` is the inclusion `ker d₀₁ ⊆ ker (listDifferential)`; for a detecting tuple both kernels are
`W^G`, so it is an isomorphism. -/
theorem ker_listDifferential_eq_ker_d₀₁ (V : Submodule k (G → A)) {d : ℕ} (γ : Fin d → G)
    (hdet : (⨅ i, LinearMap.ker (pairEvaluation A V (γ i))) =
      (⊥ : Submodule k V).prod A.ρ.invariants) :
    LinearMap.ker (listDifferential A γ) = LinearMap.ker (d₀₁ A).hom := by
  rw [ker_listDifferential A V γ hdet, d₀₁_ker_eq_invariants]

/-- **The comparison on Mathlib's `H0 A`** (tex 4690-4691). Kind: definition (an
isomorphism, for a detecting tuple).

`H^0(G, W) ≅ W^G = ker(listDifferential)`; by `H0Comparison_apply` it is induced by the identity
of `W`, the degree-zero component of the comparison. -/
noncomputable def H0Comparison (V : Submodule k (G → A)) {d : ℕ} (γ : Fin d → G)
    (hdet : (⨅ i, LinearMap.ker (pairEvaluation A V (γ i))) =
      (⊥ : Submodule k V).prod A.ρ.invariants) :
    H0 A ≃ₗ[k] LinearMap.ker (listDifferential A γ) :=
  (H0Iso A).toLinearEquiv.trans (LinearEquiv.ofEq _ _ (ker_listDifferential A V γ hdet).symm)

/-- `H0Comparison` is induced by the identity of `W`. Kind: PROVED. -/
theorem H0Comparison_apply (V : Submodule k (G → A)) {d : ℕ} (γ : Fin d → G)
    (hdet : (⨅ i, LinearMap.ker (pairEvaluation A V (γ i))) =
      (⊥ : Submodule k V).prod A.ρ.invariants) (x : H0 A) :
    (H0Comparison A V γ hdet x : A) = ((H0Iso A).hom.hom x : A) := rfl

/-- **Injectivity on the representatives `V`** (tex 4690-4691: "injective on `H^1`").
Kind: PROVED.

For a detecting tuple: if `c ∈ V` and `(c(g_i))_i = (ρ(g_i) w - w)_i` for some `w`, then
`c = 0`. -/
theorem eq_zero_of_listEvaluation_eq (V : Submodule k (G → A)) {d : ℕ} (γ : Fin d → G)
    (hdet : (⨅ i, LinearMap.ker (pairEvaluation A V (γ i))) =
      (⊥ : Submodule k V).prod A.ρ.invariants)
    {c : G → A} (hc : c ∈ V) {w : A} (h : listEvaluation A γ c = listDifferential A γ w) :
    c = 0 := by
  have hmem : ((⟨c, hc⟩ : V), w) ∈ ⨅ i, LinearMap.ker (pairEvaluation A V (γ i)) := by
    rw [Submodule.mem_iInf]
    intro i
    have hi : c (γ i) = A.ρ (γ i) w - w := congrFun h i
    rw [LinearMap.mem_ker, pairEvaluation_apply, sub_eq_zero]
    exact hi
  rw [hdet, Submodule.mem_prod, Submodule.mem_bot] at hmem
  exact congrArg Subtype.val hmem.1

/-- **Injectivity on `V`, submodule form** (tex 4690-4691). Kind: PROVED.

The composite `V → W^d → W^d / im(listDifferential)` has zero kernel. -/
theorem ker_comparison_restrict_eq_bot (V : Submodule k (G → A)) {d : ℕ} (γ : Fin d → G)
    (hdet : (⨅ i, LinearMap.ker (pairEvaluation A V (γ i))) =
      (⊥ : Submodule k V).prod A.ρ.invariants) :
    LinearMap.ker ((LinearMap.range (listDifferential A γ)).mkQ ∘ₗ listEvaluation A γ ∘ₗ
      V.subtype) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨c, hc⟩ hmem
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at hmem
  obtain ⟨w, hw⟩ := hmem
  rw [Submodule.mem_bot]
  exact Subtype.ext (eq_zero_of_listEvaluation_eq A V γ hdet hc hw.symm)

/-- **Injectivity on `H^1`, cocycle form** (tex 4690-4691). Kind: PROVED.

If `V` together with the coboundaries spans the cocycles (`V` represents all of `H^1`) and `γ`
detects, then a 1-cocycle `z` with `(z(g_i))_i ∈ im(listDifferential)` is a coboundary. -/
theorem mem_coboundaries₁_of_listEvaluation_mem_range (V : Submodule k (G → A)) {d : ℕ}
    (γ : Fin d → G)
    (hdet : (⨅ i, LinearMap.ker (pairEvaluation A V (γ i))) =
      (⊥ : Submodule k V).prod A.ρ.invariants)
    (hspan : cocycles₁ A ≤ V ⊔ coboundaries₁ A) {z : G → A} (hz : z ∈ cocycles₁ A)
    (h : listEvaluation A γ z ∈ LinearMap.range (listDifferential A γ)) :
    z ∈ coboundaries₁ A := by
  obtain ⟨c, hc, b, hb, rfl⟩ := Submodule.mem_sup.1 (hspan hz)
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hb
  obtain ⟨w, hw⟩ := LinearMap.mem_range.1 h
  have hc0 : c = 0 := by
    refine eq_zero_of_listEvaluation_eq A V γ hdet hc (w := w - u) ?_
    calc listEvaluation A γ c
        = listEvaluation A γ (c + (d₀₁ A).hom u) - listDifferential A γ u := by
          rw [map_add, ← listEvaluation_comp_d₀₁ A γ, LinearMap.comp_apply,
            add_sub_cancel_right]
      _ = listDifferential A γ w - listDifferential A γ u := by rw [← hw]
      _ = listDifferential A γ (w - u) := (map_sub _ _ _).symm
  rw [hc0, zero_add]
  exact LinearMap.mem_range_self _ u

/-- The comparison on 1-cocycles, `Z^1 → W^d ⧸ im(listDifferential)`, `c ↦ [(c(g_i))_i]`
(tex 4690). Kind: definition. -/
def cocycleComparison {d : ℕ} (γ : Fin d → G) :
    cocycles₁ A →ₗ[k] (Fin d → A) ⧸ LinearMap.range (listDifferential A γ) :=
  (LinearMap.range (listDifferential A γ)).mkQ ∘ₗ listEvaluation A γ ∘ₗ (cocycles₁ A).subtype

theorem cocycleComparison_apply {d : ℕ} (γ : Fin d → G) (x : cocycles₁ A) :
    cocycleComparison A γ x = Submodule.Quotient.mk (listEvaluation A γ (x : G → A)) := rfl

/-- Coboundaries go to zero under the comparison (it is a map of complexes). Kind: PROVED. -/
theorem cocycleComparison_eq_zero_of_mem {d : ℕ} (γ : Fin d → G) (x : cocycles₁ A)
    (hx : (x : G → A) ∈ coboundaries₁ A) : cocycleComparison A γ x = 0 := by
  obtain ⟨u, hu⟩ := LinearMap.mem_range.1 hx
  rw [cocycleComparison_apply, Submodule.Quotient.mk_eq_zero, ← hu]
  exact ⟨u, (LinearMap.congr_fun (listEvaluation_comp_d₀₁ A γ) u).symm⟩

/-- **The comparison detects exactly the coboundaries** (tex 4690-4691). Kind: PROVED.

For a detecting tuple and representatives `V` with `Z^1 ≤ V + B^1`, a cocycle goes to zero in
`H^1([W → W^d])` iff it is a coboundary, i.e. (Mathlib's `H1π_eq_zero_iff`) iff its class in
`H1 A` vanishes. This is injectivity on `H^1` in cocycle form. -/
theorem cocycleComparison_eq_zero_iff (V : Submodule k (G → A)) {d : ℕ} (γ : Fin d → G)
    (hdet : (⨅ i, LinearMap.ker (pairEvaluation A V (γ i))) =
      (⊥ : Submodule k V).prod A.ρ.invariants)
    (hspan : cocycles₁ A ≤ V ⊔ coboundaries₁ A) (x : cocycles₁ A) :
    cocycleComparison A γ x = 0 ↔ (H1π A).hom x = 0 := by
  rw [H1π_eq_zero_iff]
  refine ⟨fun h => ?_, cocycleComparison_eq_zero_of_mem A γ x⟩
  rw [cocycleComparison_apply, Submodule.Quotient.mk_eq_zero] at h
  exact mem_coboundaries₁_of_listEvaluation_mem_range A V γ hdet hspan x.2 h

/-- The forward direction of `cocycleComparison_eq_zero_iff`, as a coboundary statement
(auxiliary). Kind: PROVED. -/
theorem mem_coboundaries₁_of_cocycleComparison_eq_zero (V : Submodule k (G → A)) {d : ℕ}
    (γ : Fin d → G)
    (hdet : (⨅ i, LinearMap.ker (pairEvaluation A V (γ i))) =
      (⊥ : Submodule k V).prod A.ρ.invariants)
    (hspan : cocycles₁ A ≤ V ⊔ coboundaries₁ A) (x : cocycles₁ A)
    (h : cocycleComparison A γ x = 0) : (x : G → A) ∈ coboundaries₁ A :=
  (H1π_eq_zero_iff x).1 ((cocycleComparison_eq_zero_iff A V γ hdet hspan x).1 h)

/-- The comparison on Mathlib's explicit model of `H^1`, namely
`(shortComplexH1 A).moduleCatLeftHomologyData.H = Z^1 ⧸ im(d₀₁)`, with values in
`H^1([W → W^d]) = W^d ⧸ im(listDifferential)` (tex 4690). Kind: definition. -/
def H1ComparisonModel {d : ℕ} (γ : Fin d → G) :
    (shortComplexH1 A).moduleCatLeftHomologyData.H →ₗ[k]
      (Fin d → A) ⧸ LinearMap.range (listDifferential A γ) :=
  (LinearMap.range (shortComplexH1 A).moduleCatToCycles).liftQ (cocycleComparison A γ)
    (by
      rintro _ ⟨u, rfl⟩
      exact LinearMap.mem_ker.2
        (cocycleComparison_eq_zero_of_mem A γ _ (LinearMap.mem_range.2 ⟨u, rfl⟩)))

/-- The comparison `H^1(G, W) → H^1([W → W^d])` on Mathlib's group cohomology `H1 A`
(tex 4690-4691). Kind: definition. -/
noncomputable def H1Comparison {d : ℕ} (γ : Fin d → G) :
    H1 A →ₗ[k] (Fin d → A) ⧸ LinearMap.range (listDifferential A γ) :=
  H1ComparisonModel A γ ∘ₗ (H1Iso A).toLinearEquiv.toLinearMap

/-- `H1Comparison` is induced by `c ↦ [(c(g_i))_i]` on cocycles. Kind: PROVED. -/
theorem H1Comparison_H1π {d : ℕ} (γ : Fin d → G) (x : cocycles₁ A) :
    H1Comparison A γ ((H1π A).hom x) = cocycleComparison A γ x := by
  have hx : (H1Iso A).hom.hom ((H1π A).hom x) =
      Submodule.Quotient.mk (p := LinearMap.range (shortComplexH1 A).moduleCatToCycles) x := by
    simp [H1π]
    rfl
  change H1ComparisonModel A γ ((H1Iso A).hom.hom ((H1π A).hom x)) = _
  rw [hx]
  exact Submodule.liftQ_apply _ _ _

/-- **The comparison is injective on `H^1`** (tex 4690-4691: "The comparison to `[W → W^d]` is
an isomorphism on `H^0` and injective on `H^1`"). Kind: PROVED.

For a detecting tuple `γ` and representatives `V` with `Z^1 ≤ V + B^1`, the induced map
`H^1(G, W) → W^d ⧸ im(listDifferential)` on Mathlib's `H1 A` is injective. -/
theorem H1Comparison_injective (V : Submodule k (G → A)) {d : ℕ} (γ : Fin d → G)
    (hdet : (⨅ i, LinearMap.ker (pairEvaluation A V (γ i))) =
      (⊥ : Submodule k V).prod A.ρ.invariants)
    (hspan : cocycles₁ A ≤ V ⊔ coboundaries₁ A) :
    Function.Injective (H1Comparison A γ) := by
  have hker : LinearMap.ker (H1ComparisonModel A γ) = ⊥ := by
    refine Submodule.ker_liftQ_eq_bot _ _ _ fun x hx => ?_
    obtain ⟨u, hu⟩ := LinearMap.mem_range.1
      (mem_coboundaries₁_of_cocycleComparison_eq_zero A V γ hdet hspan x (LinearMap.mem_ker.1 hx))
    exact ⟨u, Subtype.ext hu⟩
  exact (LinearMap.ker_eq_bot.1 hker).comp (H1Iso A).toLinearEquiv.injective

end Comparison

/-! ## The cone and coefficient extension -/

section ConeContraction

open TensorProduct

variable {R : Type*} [CommRing R]
variable {C₀ C₁ C₂ D₀ D₁ : Type*} [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁] [Module R C₁]
  [AddCommGroup C₂] [Module R C₂] [AddCommGroup D₀] [Module R D₀] [AddCommGroup D₁]
  [Module R D₁]

/-- **The cone has no cohomology in degree zero** (tex 4691-4692: "Its cone has no residual
cohomology in degrees at most zero"). Kind: PROVED.

Let `(φ₀, φ₁)` be a map from `C₀ → C₁ → C₂` to `D₀ → D₁` (so `φ₁ ∘ d₀ = δ₀ ∘ φ₀`). Its mapping
cone has `Cone^0 = C₁ × D₀` with differential `(c, y) ↦ (-d₁ c, φ₁ c + δ₀ y)` and
`Cone^{-1} = C₀` with differential `x ↦ (-d₀ x, φ₀ x)`. If the map is surjective on `H^0` and
injective on `H^1`, every degree-zero cycle `(c, y)` of the cone is a boundary. -/
theorem cone_H0_eq_zero (d₀ : C₀ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] C₂) (δ₀ : D₀ →ₗ[R] D₁)
    (φ₀ : C₀ →ₗ[R] D₀) (φ₁ : C₁ →ₗ[R] D₁) (hφ : φ₁ ∘ₗ d₀ = δ₀ ∘ₗ φ₀)
    (hH0 : ∀ y, δ₀ y = 0 → ∃ x, d₀ x = 0 ∧ φ₀ x = y)
    (hH1 : ∀ z, d₁ z = 0 → φ₁ z ∈ LinearMap.range δ₀ → z ∈ LinearMap.range d₀)
    {c : C₁} {y : D₀} (hc : d₁ c = 0) (hcy : φ₁ c + δ₀ y = 0) :
    ∃ x : C₀, -d₀ x = c ∧ φ₀ x = y := by
  obtain ⟨x₁, hx₁⟩ := hH1 c hc ⟨-y, by rw [map_neg, eq_comm, ← add_eq_zero_iff_eq_neg]; exact hcy⟩
  have hδ : δ₀ (y + φ₀ x₁) = 0 := by
    rw [map_add, ← LinearMap.comp_apply δ₀ φ₀, ← hφ, LinearMap.comp_apply, hx₁, add_comm]
    exact hcy
  obtain ⟨x₂, hx₂, hx₂'⟩ := hH0 _ hδ
  refine ⟨x₂ - x₁, ?_, ?_⟩
  · rw [map_sub, hx₂, zero_sub, neg_neg, hx₁]
  · rw [map_sub, hx₂', add_sub_cancel_right]

/-- **The cone has no cohomology in degree `-1`** (tex 4691-4692). Kind: PROVED.

If the map is injective on `H^0`, the cone differential `x ↦ (-d₀ x, φ₀ x)` on `Cone^{-1} = C₀`
is injective. -/
theorem cone_Hneg1_eq_zero (d₀ : C₀ →ₗ[R] C₁) (φ₀ : C₀ →ₗ[R] D₀)
    (hH0 : ∀ x, d₀ x = 0 → φ₀ x = 0 → x = 0) {x : C₀} (h₁ : -d₀ x = 0) (h₂ : φ₀ x = 0) :
    x = 0 :=
  hH0 x (neg_eq_zero.1 h₁) h₂

/-- **The long exact sequence gives the injection** (tex 4692-4695). Kind: PROVED.

Suppose the cone `C₁ × D₀ → C₂ × D₁` (see `cone_H0_eq_zero`) has a contraction in degree zero,
`∂^{-1} ∘ h^0 + h^1 ∘ ∂^0 = id` on `Cone^0`, written in components; only the `C₁`-row is needed:
`h^0 = (h₁, h₂) : C₁ × D₀ → C₀` and the `C₁`-row `(a, b) : C₂ × D₁ → C₁` of `h^1` satisfy
`-d₀ h₁ - a d₁ + b φ₁ = id` and `-d₀ h₂ + b δ₀ = 0`. (This is what a homotopy equivalence of the
cone with a complex starting in degree one provides: if `f : Cone → P`, `g : P → Cone` with
`P^n = 0` for `n ≤ 0` and `id - g f = ∂ h + h ∂`, then `id = ∂ h + h ∂` on `Cone^0`.) Then the
map is injective on `H^1`: a cocycle `z` with `φ₁ z ∈ im δ₀` is a coboundary.

GLUE (not formalized): over the local coefficient ring, vanishing of the residual cohomology of
the finite free cone in degrees `≤ 0` allows one to "Cancel unit disks there so that the free cone
starts in degree one" (tex 4692-4693); this produces the contraction assumed here. -/
theorem mem_range_of_cone_contraction (d₀ : C₀ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] C₂)
    (δ₀ : D₀ →ₗ[R] D₁) (φ₁ : C₁ →ₗ[R] D₁) (h₁ : C₁ →ₗ[R] C₀) (h₂ : D₀ →ₗ[R] C₀)
    (a : C₂ →ₗ[R] C₁) (b : D₁ →ₗ[R] C₁)
    (hrow₁ : -(d₀ ∘ₗ h₁) - a ∘ₗ d₁ + b ∘ₗ φ₁ = LinearMap.id)
    (hrow₂ : -(d₀ ∘ₗ h₂) + b ∘ₗ δ₀ = 0)
    {z : C₁} (hz : d₁ z = 0) (hφz : φ₁ z ∈ LinearMap.range δ₀) : z ∈ LinearMap.range d₀ := by
  obtain ⟨y, hy⟩ := hφz
  have e₁ : -(d₀ (h₁ z)) - a (d₁ z) + b (φ₁ z) = z := LinearMap.congr_fun hrow₁ z
  have e₂ : -(d₀ (h₂ y)) + b (δ₀ y) = 0 := LinearMap.congr_fun hrow₂ y
  rw [hz, map_zero, sub_zero, ← hy] at e₁
  refine ⟨h₂ y - h₁ z, ?_⟩
  calc d₀ (h₂ y - h₁ z) = -(d₀ (h₁ z)) + d₀ (h₂ y) := by rw [map_sub]; abel
    _ = -(d₀ (h₁ z)) + b (δ₀ y) := by rw [neg_add_eq_zero.1 e₂]
    _ = z := e₁

/-- **Injectivity on `H^1` after every coefficient extension** (tex 4693-4695: "the same is true
after every coefficient extension. The long exact sequence gives the claimed injection").
Kind: PROVED.

The contraction identities of `mem_range_of_cone_contraction` are identities between linear
maps, so they survive base change along any `R`-algebra `S`; hence the base-changed comparison is
again injective on `H^1`. -/
theorem mem_range_baseChange_of_cone_contraction (S : Type*) [CommRing S] [Algebra R S]
    (d₀ : C₀ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] C₂) (δ₀ : D₀ →ₗ[R] D₁) (φ₁ : C₁ →ₗ[R] D₁)
    (h₁ : C₁ →ₗ[R] C₀) (h₂ : D₀ →ₗ[R] C₀) (a : C₂ →ₗ[R] C₁) (b : D₁ →ₗ[R] C₁)
    (hrow₁ : -(d₀ ∘ₗ h₁) - a ∘ₗ d₁ + b ∘ₗ φ₁ = LinearMap.id)
    (hrow₂ : -(d₀ ∘ₗ h₂) + b ∘ₗ δ₀ = 0)
    {z : S ⊗[R] C₁} (hz : d₁.baseChange S z = 0)
    (hφz : φ₁.baseChange S z ∈ LinearMap.range (δ₀.baseChange S)) :
    z ∈ LinearMap.range (d₀.baseChange S) := by
  refine mem_range_of_cone_contraction (d₀.baseChange S) (d₁.baseChange S) (δ₀.baseChange S)
    (φ₁.baseChange S) (h₁.baseChange S) (h₂.baseChange S) (a.baseChange S) (b.baseChange S)
    ?_ ?_ hz hφz
  · rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_neg, ← LinearMap.baseChange_sub, ← LinearMap.baseChange_add, hrow₁,
      LinearMap.baseChange_id]
  · rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_neg,
      ← LinearMap.baseChange_add, hrow₂, LinearMap.baseChange_zero]

end ConeContraction

section ComparisonCone

open groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G)

/-- **The cone of the comparison to `[W → W^d]` has no `H^0`** (tex 4691-4692: "Its cone has no
residual cohomology in degrees at most zero"). Kind: PROVED.

The comparison `(id_W, listEvaluation)` from `[W → (G → W) → (G × G → W)]` to `[W → W^d]`, for a
detecting tuple and representatives `V` with `Z^1 ≤ V + B^1`: every degree-zero cycle `(c, y)`
of its cone (`d₁₂ c = 0` and `(c(g_i))_i + (ρ(g_i) y - y)_i = 0`) is the boundary of some `x`,
i.e. `c = -d₀₁ x` and `y = x`. (In degree `-1` the cone differential `x ↦ (-d₀₁ x, x)` is
injective, see `cone_Hneg1_eq_zero`.) -/
theorem comparison_cone_H0_eq_zero (V : Submodule k (G → A)) {d : ℕ} (γ : Fin d → G)
    (hdet : (⨅ i, LinearMap.ker (pairEvaluation A V (γ i))) =
      (⊥ : Submodule k V).prod A.ρ.invariants)
    (hspan : cocycles₁ A ≤ V ⊔ coboundaries₁ A) {c : G → A} {y : A}
    (hc : (d₁₂ A).hom c = 0) (hcy : listEvaluation A γ c + listDifferential A γ y = 0) :
    ∃ x : A, -(d₀₁ A).hom x = c ∧ x = y := by
  refine cone_H0_eq_zero (d₀₁ A).hom (d₁₂ A).hom (listDifferential A γ) LinearMap.id
    (listEvaluation A γ) (by rw [LinearMap.comp_id, listEvaluation_comp_d₀₁]) ?_ ?_ hc hcy
  · intro y' hy'
    have hy'' : y' ∈ LinearMap.ker (d₀₁ A).hom := by
      rw [← ker_listDifferential_eq_ker_d₀₁ A V γ hdet]
      exact hy'
    exact ⟨y', hy'', rfl⟩
  · intro z hz hzr
    exact mem_coboundaries₁_of_listEvaluation_mem_range A V γ hdet hspan
      (LinearMap.mem_ker.2 hz) hzr

end ComparisonCone

section RetainedComparison

open groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G)
variable {C₀ C₁ C₂ : Type*} [AddCommGroup C₀] [Module k C₀] [AddCommGroup C₁] [Module k C₁]
  [AddCommGroup C₂] [Module k C₂]

/-- **The retained comparison is injective on `H^1`** (tex 4686-4691: "Evaluation remains
injective ... The comparison to `[W → W^d]` is ... injective on `H^1`"). Kind: PROVED.

For a retained cochain map `ι` injective on `H^1`, a detecting tuple `γ` and representatives `V`
with `Z^1 ≤ V + B^1`: if `z` is a cycle of the model whose evaluations `(e^1_{g_i} z)_i` lie in
`im(listDifferential)`, then `z` is a boundary. -/
theorem retained_comparison_H1 {d₀ : C₀ →ₗ[k] C₁} {d₁ : C₁ →ₗ[k] C₂} {ι₁ : C₁ →ₗ[k] (G → A)}
    {ι₂ : C₂ →ₗ[k] (G × G → A)} (h₁ : (d₁₂ A).hom ∘ₗ ι₁ = ι₂ ∘ₗ d₁)
    (hinj : ∀ z, d₁ z = 0 → ι₁ z ∈ coboundaries₁ A → z ∈ LinearMap.range d₀)
    (V : Submodule k (G → A)) {d : ℕ} (γ : Fin d → G)
    (hdet : (⨅ i, LinearMap.ker (pairEvaluation A V (γ i))) =
      (⊥ : Submodule k V).prod A.ρ.invariants)
    (hspan : cocycles₁ A ≤ V ⊔ coboundaries₁ A) {z : C₁} (hz : d₁ z = 0)
    (h : (listEvaluation A γ ∘ₗ ι₁) z ∈ LinearMap.range (listDifferential A γ)) :
    z ∈ LinearMap.range d₀ :=
  hinj z hz (mem_coboundaries₁_of_listEvaluation_mem_range A V γ hdet hspan
    (evalOne_mem_cocycles₁ h₁ hz) h)

/-- **The retained comparison is surjective on `H^0`** (tex 4690-4691). Kind: PROVED.

If `ι^0` maps the degree-zero cycles of the model onto `W^G` (as for a model with the correct
`H^0`) and `γ` detects, then every degree-zero cycle `y` of `[W → W^d]` is `ι^0 x` for a cycle `x`;
together with injectivity of `ι^0` on cycles this is the isomorphism on `H^0`. -/
theorem retained_comparison_H0 {d₀ : C₀ →ₗ[k] C₁} {ι₀ : C₀ →ₗ[k] A}
    (hH0 : ∀ y ∈ A.ρ.invariants, ∃ x, d₀ x = 0 ∧ ι₀ x = y)
    (V : Submodule k (G → A)) {d : ℕ} (γ : Fin d → G)
    (hdet : (⨅ i, LinearMap.ker (pairEvaluation A V (γ i))) =
      (⊥ : Submodule k V).prod A.ρ.invariants) {y : A} (hy : listDifferential A γ y = 0) :
    ∃ x, d₀ x = 0 ∧ ι₀ x = y := by
  have hy' : y ∈ LinearMap.ker (listDifferential A γ) := hy
  rw [ker_listDifferential A V γ hdet] at hy'
  exact hH0 y hy'

/-- **The cone of the retained comparison has no `H^0`** (tex 4691-4692). Kind: PROVED.

Combining `retained_comparison_H0`, `retained_comparison_H1` and `cone_H0_eq_zero` for the
comparison `(e^0, (e^1_{g_i})_i)` from a retained model to `[W → W^d]`. -/
theorem retained_comparison_cone_H0 {d₀ : C₀ →ₗ[k] C₁} {d₁ : C₁ →ₗ[k] C₂} {ι₀ : C₀ →ₗ[k] A}
    {ι₁ : C₁ →ₗ[k] (G → A)} {ι₂ : C₂ →ₗ[k] (G × G → A)} (h₀ : (d₀₁ A).hom ∘ₗ ι₀ = ι₁ ∘ₗ d₀)
    (h₁ : (d₁₂ A).hom ∘ₗ ι₁ = ι₂ ∘ₗ d₁)
    (hH0 : ∀ y ∈ A.ρ.invariants, ∃ x, d₀ x = 0 ∧ ι₀ x = y)
    (hinj : ∀ z, d₁ z = 0 → ι₁ z ∈ coboundaries₁ A → z ∈ LinearMap.range d₀)
    (V : Submodule k (G → A)) {d : ℕ} (γ : Fin d → G)
    (hdet : (⨅ i, LinearMap.ker (pairEvaluation A V (γ i))) =
      (⊥ : Submodule k V).prod A.ρ.invariants)
    (hspan : cocycles₁ A ≤ V ⊔ coboundaries₁ A) {c : C₁} {y : A} (hc : d₁ c = 0)
    (hcy : (listEvaluation A γ ∘ₗ ι₁) c + listDifferential A γ y = 0) :
    ∃ x : C₀, -d₀ x = c ∧ ι₀ x = y := by
  refine cone_H0_eq_zero d₀ d₁ (listDifferential A γ) ι₀ (listEvaluation A γ ∘ₗ ι₁) ?_
    (fun y' hy' => retained_comparison_H0 A hH0 V γ hdet hy')
    (fun z hz hzr => retained_comparison_H1 A h₁ hinj V γ hdet hspan hz hzr) hc hcy
  rw [LinearMap.comp_assoc, ← h₀, ← LinearMap.comp_assoc, listEvaluation_comp_d₀₁]

end RetainedComparison

/-! ## Non-vacuity examples -/

section Examples

open CategoryTheory groupCohomology

/-- Representatives `V = 0` always satisfy the hypotheses `V ≤ Z^1` and `V ⊓ B^1 = 0`. -/
example {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) :
    (⊥ : Submodule k (G → A)) ≤ cocycles₁ A ∧ (⊥ : Submodule k (G → A)) ⊓ coboundaries₁ A = ⊥ :=
  ⟨bot_le, bot_inf_eq _⟩

/-- The identity of the low-degree inhomogeneous cochains is a retained cochain map: the
hypotheses of `evalOne_comp_d` and `evalTwo_comp_d` hold, and (5.2) specializes to Mathlib's
cocycle identity. -/
example {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) {z : G → A}
    (hz : (d₁₂ A).hom z = 0) (g h : G) :
    evalOne (LinearMap.id : (G → A) →ₗ[k] (G → A)) (g * h) z =
      A.ρ g (evalOne LinearMap.id h z) + evalOne LinearMap.id g z :=
  evalOne_mul (d₁ := (d₁₂ A).hom) (ι₂ := LinearMap.id)
    (by rw [LinearMap.comp_id, LinearMap.id_comp]) hz g h

/-- The identity chain map of Mathlib's `inhomogeneousCochains A` satisfies the hypotheses of
`chainMap_lowDegree_comm`. -/
example {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) :
    (d₀₁ A).hom ∘ₗ ((𝟙 (inhomogeneousCochains A) : inhomogeneousCochains A ⟶ _).f 0 ≫
        (cochainsIso₀ A).hom).hom =
      ((𝟙 (inhomogeneousCochains A) : inhomogeneousCochains A ⟶ _).f 1 ≫
        (cochainsIso₁ A).hom).hom ∘ₗ ((inhomogeneousCochains A).d 0 1).hom :=
  (chainMap_lowDegree_comm A (𝟙 _)).1

/-- The identity retained map on the global cochains satisfies the hypotheses `hinj` and `hH0`
of `retained_comparison_H1`, `retained_comparison_H0` and `retained_comparison_cone_H0`. -/
example {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) :
    (∀ z : G → A, (d₁₂ A).hom z = 0 → (LinearMap.id : (G → A) →ₗ[k] (G → A)) z ∈
      coboundaries₁ A → z ∈ LinearMap.range (d₀₁ A).hom) ∧
    (∀ y ∈ A.ρ.invariants, ∃ x, (d₀₁ A).hom x = 0 ∧ (LinearMap.id : A →ₗ[k] A) x = y) :=
  ⟨fun _ _ hz => hz, fun y hy =>
    ⟨y, by rw [← LinearMap.mem_ker, d₀₁_ker_eq_invariants]; exact hy, rfl⟩⟩

/-- The cone of the identity map is contractible: the contraction hypotheses of
`mem_range_of_cone_contraction` are satisfiable for every complex `C₀ → C₁ → C₂`. -/
example {R C₀ C₁ C₂ : Type*} [CommRing R] [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁]
    [Module R C₁] [AddCommGroup C₂] [Module R C₂] (d₀ : C₀ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] C₂) :
    -(d₀ ∘ₗ (0 : C₁ →ₗ[R] C₀)) - (0 : C₂ →ₗ[R] C₁) ∘ₗ d₁ +
        (LinearMap.id : C₁ →ₗ[R] C₁) ∘ₗ LinearMap.id = LinearMap.id ∧
      -(d₀ ∘ₗ (LinearMap.id : C₀ →ₗ[R] C₀)) + (LinearMap.id : C₁ →ₗ[R] C₁) ∘ₗ d₀ = 0 := by
  simp

/-- Sequences: the constant family of identity retained maps on the global cochains of `A`
satisfies the hypotheses of `seq_cycle_mem_cocycles₁`, so a sequence of 1-cocycles of `G` gives
a crossed homomorphism of the product group `ℕ → G` (written as `∀ _ : ℕ, G`). -/
example {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (z : ℕ → G → A)
    (hz : ∀ i, (d₁₂ A).hom (z i) = 0) :
    (fun g => evalOne (seqι₁ (As := fun _ : ℕ => A) (fun _ => LinearMap.id)) g z) ∈
      cocycles₁ (piRep (fun _ : ℕ => A)) :=
  seq_cycle_mem_cocycles₁ (fun _ => (d₁₂ A).hom) (ι₂ := fun _ => LinearMap.id)
    (fun _ => by rw [LinearMap.comp_id, LinearMap.id_comp]) hz

namespace Examples

/-! A concrete non-degenerate instance: `G = ℤ` (written multiplicatively) acting trivially on
`W = ℚ`. Here `H^1(G, W) = Hom(ℤ, ℚ) ≠ 0` is represented by `V = ℚ · c₀` with
`c₀(g) = toAdd g`, and the single element `g₁ = ofAdd 1` is a detecting list. -/

/-- The trivial representation of `Multiplicative ℤ` on `ℚ`. -/
abbrev exA : Rep.{0} ℚ (Multiplicative ℤ) := Rep.trivial ℚ (Multiplicative ℤ) ℚ

/-- The crossed homomorphism `c₀(g) = toAdd g`. -/
def exCocycle : Multiplicative ℤ → exA := fun g => ((Multiplicative.toAdd g : ℤ) : ℚ)

/-- The representatives `V = ℚ · c₀`. -/
abbrev exV : Submodule ℚ (Multiplicative ℤ → exA) := Submodule.span ℚ {exCocycle}

/-- The detecting tuple `(ofAdd 1)`. -/
def exγ : Fin 1 → Multiplicative ℤ := fun _ => Multiplicative.ofAdd 1

/-- `c₀` is a 1-cocycle. -/
theorem exCocycle_mem : exCocycle ∈ cocycles₁ exA := by
  rw [mem_cocycles₁_iff]
  intro g h
  simp only [exCocycle, toAdd_mul, Int.cast_add, Representation.trivial_apply]
  exact add_comm _ _

/-- `c₀ ≠ 0`. -/
theorem exCocycle_ne_zero : exCocycle ≠ 0 := by
  intro h
  have := congrFun h (Multiplicative.ofAdd 1)
  simp [exCocycle] at this

/-- Non-vacuity of `V ≤ Z^1`. -/
theorem exV_le : exV ≤ cocycles₁ exA :=
  (Submodule.span_singleton_le_iff_mem _ _).2 exCocycle_mem

/-- The representatives are nonzero. -/
theorem exV_ne_bot : exV ≠ ⊥ :=
  fun h => exCocycle_ne_zero (Submodule.span_singleton_eq_bot.1 h)

/-- Non-vacuity of `V ⊓ B^1 = 0`. -/
theorem exV_inf : exV ⊓ coboundaries₁ exA = ⊥ := by
  rw [coboundaries₁_eq_bot_of_isTrivial, inf_bot_eq]

/-- Non-vacuity of the detection hypothesis: `(ofAdd 1)` detects. -/
theorem exDetect : (⨅ i, LinearMap.ker (pairEvaluation exA exV (exγ i))) =
    (⊥ : Submodule ℚ exV).prod exA.ρ.invariants := by
  ext ⟨c, w⟩
  rw [Submodule.mem_iInf, Submodule.mem_prod, Submodule.mem_bot]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 c.2
  have hval : (c : Multiplicative ℤ → exA) (Multiplicative.ofAdd 1) = a := by
    rw [← ha]
    simp [exCocycle]
  have hev : ∀ i, pairEvaluation exA exV (exγ i) (c, w) = a := by
    intro i
    rw [pairEvaluation_apply]
    change (c : Multiplicative ℤ → exA) (Multiplicative.ofAdd 1) - (w - w) = a
    rw [sub_self, sub_zero, hval]
  constructor
  · intro h
    have ha0 : a = 0 := by
      rw [← hev 0]
      exact LinearMap.mem_ker.1 (h 0)
    refine ⟨?_, (Representation.mem_invariants _ _).2 fun _ => rfl⟩
    change c = 0
    rw [← Submodule.coe_eq_zero, ← ha, ha0, zero_smul]
  · rintro ⟨hc, -⟩ i
    have hc' : c = 0 := hc
    rw [LinearMap.mem_ker, hev i, ← hval, hc']
    rfl

/-- Non-vacuity of `Z^1 ≤ V + B^1`: every cocycle is a multiple of `c₀`. -/
theorem exSpan : cocycles₁ exA ≤ exV ⊔ coboundaries₁ exA := by
  intro z hz
  apply Submodule.mem_sup_left
  rw [Submodule.mem_span_singleton]
  refine ⟨z (Multiplicative.ofAdd 1), ?_⟩
  let ψ : ℤ →+ ℚ :=
    { toFun := fun n => z (Multiplicative.ofAdd n)
      map_zero' := cocycles₁_map_one (⟨z, hz⟩ : cocycles₁ exA)
      map_add' := fun m n => by
        have := (mem_cocycles₁_iff z).1 hz (Multiplicative.ofAdd m) (Multiplicative.ofAdd n)
        rw [Representation.trivial_apply] at this
        change z (Multiplicative.ofAdd m * Multiplicative.ofAdd n) = _
        rw [this, add_comm] }
  let ψ' : ℤ →+ ℚ := (AddMonoidHom.mulLeft (z (Multiplicative.ofAdd 1))).comp (Int.castAddHom ℚ)
  have hψ : ψ = ψ' := AddMonoidHom.ext_int (by simp [ψ, ψ'])
  funext g
  have := congrArg (fun f : ℤ →+ ℚ => f (Multiplicative.toAdd g)) hψ
  simp only [ψ, ψ', AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.coe_comp,
    Function.comp_apply, Int.coe_castAddHom, AddMonoidHom.coe_mulLeft, ofAdd_toAdd] at this
  rw [Pi.smul_apply, this]
  rfl

/-- In the concrete instance, `H^1` is nonzero: the class of `c₀` does not vanish. -/
theorem exH1_ne_zero : (H1π exA).hom ⟨exCocycle, exCocycle_mem⟩ ≠ 0 := by
  rw [Ne, H1π_eq_zero_iff, coboundaries₁_eq_bot_of_isTrivial, Submodule.mem_bot]
  exact exCocycle_ne_zero

/-- In the concrete instance, the comparison to `[W → W^1]` is injective on the nonzero
`H^1(ℤ, ℚ)`, and `H^0` of `[W → W^1]` is `W^G`. -/
example : Function.Injective (H1Comparison exA exγ) ∧
    LinearMap.ker (listDifferential exA exγ) = exA.ρ.invariants :=
  ⟨H1Comparison_injective exA exV exγ exDetect exSpan,
    ker_listDifferential exA exV exγ exDetect⟩

/-- In the concrete instance, the existence theorem produces padded detecting tuples of length
`dim V + dim W = 2`. -/
example : ∃ γ : Fin 2 → Multiplicative ℤ,
    (⨅ i, LinearMap.ker (pairEvaluation exA exV (γ i))) =
      (⊥ : Submodule ℚ exV).prod exA.ρ.invariants := by
  refine exists_detecting_tuple_pairEvaluation exA exV exV_inf ?_
  have h1 : Module.finrank ℚ exV = 1 := finrank_span_singleton exCocycle_ne_zero
  have h2 : Module.finrank ℚ exA = 1 := Module.finrank_self ℚ
  omega

end Examples

end Examples

end ZInQ.Manuscript.RC.Limits

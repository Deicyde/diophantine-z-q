/-
glue-I3-linalg: the commutant argument of step C2 (N5 L731-734), as linear algebra over
Mathlib's `Representation`, `IsSemisimpleRepresentation` and `IsIrreducible`.

`isIrreducible_of_commutant_scalar`: a nonzero semisimple representation whose equivariant
endomorphisms are all scalars is irreducible.
-/
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace GlueI3

open Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- The projection onto a subrepresentation along an invariant complement is equivariant. -/
lemma projection_comm {ρ : Representation k G V} (W W' : Subrepresentation ρ)
    (h : IsCompl W.toSubmodule W'.toSubmodule) (g : G) :
    W.toSubmodule.projection W'.toSubmodule h ∘ₗ ρ g =
      ρ g ∘ₗ W.toSubmodule.projection W'.toSubmodule h := by
  apply LinearMap.ext
  intro v
  set p := W.toSubmodule.projection W'.toSubmodule h
  have hv := Submodule.projection_add_projection_eq_self h v
  set a := p v with ha
  set b := W'.toSubmodule.projection W.toSubmodule h.symm v
  have haW : a ∈ W.toSubmodule := by apply Submodule.projection_apply_mem
  have hbW : b ∈ W'.toSubmodule := by apply Submodule.projection_apply_mem
  simp only [LinearMap.coe_comp, Function.comp_apply]
  conv_lhs => rw [← hv, map_add, map_add]
  rw [Submodule.projection_apply_of_mem_right h (W'.apply_mem_toSubmodule g hbW), add_zero,
    Submodule.projection_apply_of_mem_left h (W.apply_mem_toSubmodule g haW)]

/-- **The commutant argument (GLUE, proved).** A semisimple representation on a nonzero space
whose `G`-equivariant endomorphisms are all scalars is irreducible. -/
theorem isIrreducible_of_commutant_scalar (ρ : Representation k G V) [Nontrivial V]
    (hss : ρ.IsSemisimpleRepresentation)
    (hcomm : ∀ φ : V →ₗ[k] V, (∀ g, φ ∘ₗ ρ g = ρ g ∘ₗ φ) → ∃ c : k, φ = c • LinearMap.id) :
    ρ.IsIrreducible := by
  refine { toNontrivial := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h] at this
    exact hx ((Submodule.mem_bot k).mp this)
  · intro W
    obtain ⟨W', hW'⟩ := hss.exists_isCompl W
    have h : IsCompl W.toSubmodule W'.toSubmodule := by
      constructor
      · rw [disjoint_iff]
        have := congrArg Subrepresentation.toSubmodule hW'.inf_eq_bot
        simp only [Subrepresentation.toSubmodule_inf] at this
        exact this
      · rw [codisjoint_iff]
        have := congrArg Subrepresentation.toSubmodule hW'.sup_eq_top
        simp only [Subrepresentation.toSubmodule_sup] at this
        exact this
    obtain ⟨c, hc⟩ := hcomm _ (projection_comm W W' h)
    by_cases hW : W = ⊥
    · exact Or.inl hW
    right
    -- some nonzero `w ∈ W` gives `c = 1`
    have hne : W.toSubmodule ≠ ⊥ := by
      intro h0; apply hW; apply Subrepresentation.toSubmodule_injective; rw [h0]; rfl
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have h1 := congrArg (fun f => f w) hc
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at h1
    rw [Submodule.projection_apply_of_mem_left h hwW] at h1
    have hc1 : c = 1 := by
      have : (c - 1) • w = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hw0)
    -- then `W' = 0`
    have hW'0 : W'.toSubmodule = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have h2 := congrArg (fun f => f y) hc
      simp only [LinearMap.id_apply, hc1, one_smul] at h2
      rw [Submodule.projection_apply_of_mem_right h hy] at h2
      exact (Submodule.mem_bot k).mpr h2.symm
    apply Subrepresentation.toSubmodule_injective
    have := h.sup_eq_top
    rw [hW'0, sup_bot_eq] at this
    exact this

/-- The commutant of a family of endomorphisms. -/
def commOf {W : Type*} [AddCommGroup W] [Module k W] (r : G → W →ₗ[k] W) :
    Submodule k (W →ₗ[k] W) where
  carrier := {φ | ∀ g, φ ∘ₗ r g = r g ∘ₗ φ}
  add_mem' := by
    intro φ ψ hφ hψ g
    simp only [Set.mem_ofPred_eq] at *
    rw [LinearMap.add_comp, LinearMap.comp_add, hφ g, hψ g]
  zero_mem' := by intro g; simp
  smul_mem' := by
    intro c φ hφ g
    simp only [Set.mem_ofPred_eq] at *
    rw [LinearMap.smul_comp, LinearMap.comp_smul, hφ g]

/-- `(a, b, c, d) ↦ [[a, b], [c, d]]`, an injective linear map
`End_G(V)⁴ → End_G(V ⊕ V)`. -/
def blockMap (ρ : Representation k G V) :
    (commOf (k := k) (fun g => ρ g)) × (commOf (k := k) (fun g => ρ g)) ×
      (commOf (k := k) (fun g => ρ g)) × (commOf (k := k) (fun g => ρ g)) →ₗ[k]
      commOf (k := k) (fun g => (ρ g).prodMap (ρ g)) where
  toFun t := ⟨((t.1 : V →ₗ[k] V).coprod (t.2.1 : V →ₗ[k] V)).prod
      ((t.2.2.1 : V →ₗ[k] V).coprod (t.2.2.2 : V →ₗ[k] V)), by
    intro g
    have ha : ∀ v, (t.1 : V →ₗ[k] V) (ρ g v) = ρ g ((t.1 : V →ₗ[k] V) v) :=
      fun v => congrArg (fun f => f v) (t.1.2 g)
    have hb : ∀ v, (t.2.1 : V →ₗ[k] V) (ρ g v) = ρ g ((t.2.1 : V →ₗ[k] V) v) :=
      fun v => congrArg (fun f => f v) (t.2.1.2 g)
    have hc : ∀ v, (t.2.2.1 : V →ₗ[k] V) (ρ g v) = ρ g ((t.2.2.1 : V →ₗ[k] V) v) :=
      fun v => congrArg (fun f => f v) (t.2.2.1.2 g)
    have hd : ∀ v, (t.2.2.2 : V →ₗ[k] V) (ρ g v) = ρ g ((t.2.2.2 : V →ₗ[k] V) v) :=
      fun v => congrArg (fun f => f v) (t.2.2.2.2 g)
    apply LinearMap.ext
    rintro ⟨x, y⟩
    simp [ha, hb, hc, hd]⟩
  map_add' s t := by
    apply Subtype.ext; apply LinearMap.ext; rintro ⟨x, y⟩
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]
    simp [add_add_add_comm]
  map_smul' c t := by
    apply Subtype.ext; apply LinearMap.ext; rintro ⟨x, y⟩
    simp

lemma blockMap_injective (ρ : Representation k G V) : Function.Injective (blockMap ρ) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  rintro ⟨a, b, c, d⟩ h
  have h' := congrArg Subtype.val h
  have hx : ∀ x, (blockMap ρ (a, b, c, d) : V × V →ₗ[k] V × V) (x, 0) = 0 :=
    fun x => by rw [h']; rfl
  have hy : ∀ y, (blockMap ρ (a, b, c, d) : V × V →ₗ[k] V × V) (0, y) = 0 :=
    fun y => by rw [h']; rfl
  simp only [blockMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.prod_apply, Function.prod,
    LinearMap.coprod_apply, map_zero, add_zero, zero_add, Prod.mk_eq_zero] at hx hy
  refine Prod.ext (Subtype.ext (LinearMap.ext fun x => (hx x).1))
    (Prod.ext (Subtype.ext (LinearMap.ext fun y => (hy y).1))
      (Prod.ext (Subtype.ext (LinearMap.ext fun x => (hx x).2))
        (Subtype.ext (LinearMap.ext fun y => (hy y).2))))

omit [Monoid G] in
lemma id_mem_commOf {W : Type*} [AddCommGroup W] [Module k W] (r : G → W →ₗ[k] W) :
    (LinearMap.id : W →ₗ[k] W) ∈ commOf r := by
  intro g; simp

omit [Monoid G] in
/-- A commutant of dimension `1` consists of the scalars. -/
lemma scalar_of_finrank_commOf_eq_one {W : Type*} [AddCommGroup W] [Module k W] [Nontrivial W]
    (r : G → W →ₗ[k] W) (h1 : Module.finrank k (commOf r) = 1) :
    ∀ φ ∈ commOf r, ∃ c : k, φ = c • LinearMap.id := by
  intro φ hφ
  have hid0 : (⟨LinearMap.id, id_mem_commOf r⟩ : commOf r) ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : W)
    exact hx (by simpa using congrArg (fun f : commOf r => (f : W →ₗ[k] W) x) h0)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hid0).mp h1 ⟨φ, hφ⟩
  exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩

/-- **The dimension count of C2 (GLUE, proved).** If `dim End_G(V ⊕ V) ≤ 4` and `V ≠ 0` is
finite-dimensional, then `dim End_G(V) = 1`. -/
theorem finrank_commOf_eq_one_of_prod_le_four (ρ : Representation k G V) [Nontrivial V]
    [FiniteDimensional k V]
    (h4 : Module.finrank k (commOf (k := k) (fun g => (ρ g).prodMap (ρ g))) ≤ 4) :
    Module.finrank k (commOf (k := k) (fun g => ρ g)) = 1 := by
  have hinj := blockMap_injective ρ
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_prod] at hle
  have hC1 : Module.finrank k (commOf (k := k) (fun g => ρ g)) ≤ 1 := by omega
  have hid0 : (⟨LinearMap.id, id_mem_commOf _⟩ : commOf (k := k) (fun g => ρ g)) ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have h0x := congrArg (fun f : commOf (k := k) (fun g => ρ g) => (f : V →ₗ[k] V) x) h0
    exact hx (by simpa using h0x)
  have hpos : 0 < Module.finrank k (commOf (k := k) (fun g => ρ g)) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hid0⟩
  omega

/-- **C2 over the splitting field (GLUE, proved).** N5 L731-734: over a field `E` splitting `B`,
`V_ℓ(A) ⊗ E ≅ r ⊕ r` and `dim_E End_G(V_ℓ A ⊗ E) = 4`. If the commutant of `r ⊕ r` has
dimension at most `4` and `r` is semisimple and nonzero, then `r` is irreducible, and its
commutant is the scalars. -/
theorem isIrreducible_of_finrank_commOf_prod_le_four (ρ : Representation k G V) [Nontrivial V]
    (hss : ρ.IsSemisimpleRepresentation)
    [FiniteDimensional k V]
    (h4 : Module.finrank k (commOf (k := k) (fun g => (ρ g).prodMap (ρ g))) ≤ 4) :
    ρ.IsIrreducible ∧ ∀ φ ∈ commOf (k := k) (fun g => ρ g), ∃ c : k, φ = c • LinearMap.id := by
  have hsc := scalar_of_finrank_commOf_eq_one _ (finrank_commOf_eq_one_of_prod_le_four ρ h4)
  exact ⟨isIrreducible_of_commutant_scalar ρ hss (fun φ hφ => hsc φ hφ), hsc⟩

/-- **Semisimplicity passes to equivariant quotients (GLUE, proved).** -/
theorem isSemisimple_of_surjective {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k G W) (hss : ρ.IsSemisimpleRepresentation)
    (f : V →ₗ[k] W) (hf : Function.Surjective f) (hfeq : ∀ g v, f (ρ g v) = σ g (f v)) :
    σ.IsSemisimpleRepresentation := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule] at hss ⊢
  exact IsSemisimpleModule.of_surjective
    (IntertwiningMap.equivLinearMapAsModule ρ σ (LinearMap.intertwiningMap_of_isIntertwiningMap ρ σ f hfeq)) hf

/-! ### Extension of the coefficient field -/

/-- Base change `ρ_E` of a representation along a field extension `E/k`. -/
def repBaseChange (E : Type*) [Field E] [Algebra k E] (ρ : Representation k G V) :
    Representation E G (TensorProduct k E V) where
  toFun g := (ρ g).baseChange E
  map_one' := by
    change (ρ 1).baseChange E = LinearMap.id
    rw [map_one, Module.End.one_eq_id, LinearMap.baseChange_id]
  map_mul' g h := by
    change (ρ (g * h)).baseChange E = (ρ g).baseChange E ∘ₗ (ρ h).baseChange E
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

/-- **GLUE, not proved here (linear algebra; STANDARD).** Invariants commute with extension of
the coefficient field: `dim_E End_G(V ⊗ E) = dim_k End_G(V)` for finite-dimensional `V`. (The
commutant of `ρ(G)` is the commutant of its finite-dimensional span, i.e. the kernel of a
`k`-linear map between finite-dimensional spaces, and kernels commute with flat base change.) -/
def InvariantsBaseChange : Prop :=
  ∀ (k E G V : Type) [Field k] [Field E] [Algebra k E] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V),
    Module.finrank E (commOf (k := E) (fun g => repBaseChange E ρ g)) =
      Module.finrank k (commOf (k := k) (fun g => ρ g))

/-- **GLUE, not proved here (algebra; STANDARD).** In characteristic `0`, semisimplicity of a
finite-dimensional representation survives extension of the coefficient field. (The span of
`ρ(G)` is a finite-dimensional algebra with a faithful semisimple module, hence semisimple, hence
separable since `k` is perfect, so its base change is semisimple.) -/
def SemisimpleBaseChange : Prop :=
  ∀ (k E G V : Type) [Field k] [CharZero k] [Field E] [Algebra k E] [Monoid G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k G V),
    ρ.IsSemisimpleRepresentation → (repBaseChange E ρ).IsSemisimpleRepresentation

/-- **C2, absolute irreducibility (GLUE, proved from the two linear-algebra statements above).**
If `r` is a nonzero semisimple representation over a field of characteristic `0` with
`dim End_G(r ⊕ r) ≤ 4`, then `r ⊗ F` is irreducible for every extension `F`, i.e. `r` is
absolutely irreducible. -/
theorem absolutelyIrreducible_of_finrank_commOf_prod_le_four
    (hInv : InvariantsBaseChange) (hSS : SemisimpleBaseChange)
    {k G V : Type} [Field k] [CharZero k] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] (ρ : Representation k G V)
    (hss : ρ.IsSemisimpleRepresentation)
    (h4 : Module.finrank k (commOf (k := k) (fun g => (ρ g).prodMap (ρ g))) ≤ 4)
    (F : Type) [Field F] [Algebra k F] : (repBaseChange F ρ).IsIrreducible := by
  have h1 := finrank_commOf_eq_one_of_prod_le_four ρ h4
  have hF1 : Module.finrank F (commOf (k := F) (fun g => repBaseChange F ρ g)) = 1 := by
    rw [hInv k F G V ρ, h1]
  have : Nontrivial (TensorProduct k F V) := by
    apply Module.nontrivial_of_finrank_pos (R := F)
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos
  exact isIrreducible_of_commutant_scalar _ (hSS k F G V ρ hss)
    (fun φ hφ => scalar_of_finrank_commOf_eq_one _ hF1 φ hφ)

/-! ### E1: a common constituent gives a nonzero equivariant map -/

/-- **E1, first arrow (GLUE, proved).** If `ρ` is semisimple and a nonzero subrepresentation `U`
of `ρ` is equivariantly isomorphic to a subrepresentation `U'` of `σ`, there is a nonzero
`G`-equivariant linear map `V → W`. (Project onto `U` along an invariant complement, transport,
include.) -/
theorem exists_equivariant_ne_zero_of_common {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k G W) (hss : ρ.IsSemisimpleRepresentation)
    (U : Subrepresentation ρ) (U' : Subrepresentation σ) (hU : U ≠ ⊥)
    (e : U.toSubmodule ≃ₗ[k] U'.toSubmodule)
    (he : ∀ g (u : U.toSubmodule), (e ⟨ρ g u, U.apply_mem_toSubmodule g u.2⟩ : W) = σ g (e u)) :
    ∃ φ : V →ₗ[k] W, φ ≠ 0 ∧ ∀ g, φ ∘ₗ ρ g = σ g ∘ₗ φ := by
  obtain ⟨U'', hU''⟩ := hss.exists_isCompl U
  have h : IsCompl U.toSubmodule U''.toSubmodule := by
    constructor
    · rw [disjoint_iff]
      have := congrArg Subrepresentation.toSubmodule hU''.inf_eq_bot
      simp only [Subrepresentation.toSubmodule_inf] at this
      exact this
    · rw [codisjoint_iff]
      have := congrArg Subrepresentation.toSubmodule hU''.sup_eq_top
      simp only [Subrepresentation.toSubmodule_sup] at this
      exact this
  let p := Submodule.projectionOnto U.toSubmodule U''.toSubmodule h
  refine ⟨U'.toSubmodule.subtype ∘ₗ e.toLinearMap ∘ₗ p, ?_, ?_⟩
  · intro h0
    apply hU
    apply Subrepresentation.toSubmodule_injective
    change U.toSubmodule = ⊥
    rw [eq_bot_iff]
    intro u hu
    have := congrArg (fun f => f u) h0
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply,
      Submodule.coe_subtype, LinearEquiv.coe_coe, p] at this
    rw [Submodule.projectionOnto_apply_left h ⟨u, hu⟩] at this
    have h2 : e ⟨u, hu⟩ = 0 := Subtype.ext this
    have h3 : (⟨u, hu⟩ : U.toSubmodule) = 0 := by simpa using h2
    exact (Submodule.mem_bot k).mpr (congrArg Subtype.val h3)
  · intro g
    apply LinearMap.ext
    intro v
    have hpv : (p (ρ g v)) = ⟨ρ g (p v), U.apply_mem_toSubmodule g (p v).2⟩ := by
      apply Subtype.ext
      exact congrArg (fun f => f v) (projection_comm U U'' h g)
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearEquiv.coe_coe]
    rw [hpv, he]

/-- **Equivariant descent (GLUE, proved).** A nonzero `G`-equivariant `E`-linear map
`E ⊗ V → E ⊗ W` gives a nonzero `G`-equivariant `k`-linear map `V → W`: expand in a `k`-basis of
`E` and take a nonzero coordinate. -/
theorem exists_equivariant_ne_zero_of_baseChange {W : Type*} [AddCommGroup W] [Module k W]
    (E : Type*) [Field E] [Algebra k E] (ρ : Representation k G V) (σ : Representation k G W)
    (φ : TensorProduct k E V →ₗ[E] TensorProduct k E W) (hφ0 : φ ≠ 0)
    (hφ : ∀ g, φ ∘ₗ repBaseChange E ρ g = repBaseChange E σ g ∘ₗ φ) :
    ∃ ψ : V →ₗ[k] W, ψ ≠ 0 ∧ ∀ g, ψ ∘ₗ ρ g = σ g ∘ₗ ψ := by
  classical
  let b := Module.Free.chooseBasis k E
  let c : TensorProduct k E W ≃ₗ[k] (Module.Free.ChooseBasisIndex k E →₀ W) :=
    (TensorProduct.congr b.repr (LinearEquiv.refl k W)).trans
      (TensorProduct.finsuppScalarLeft k W _)
  have hc : ∀ (x : TensorProduct k E W) g j, c (repBaseChange E σ g x) j = σ g (c x j) := by
    intro x g j
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a w =>
      simp [c, repBaseChange, LinearMap.baseChange_tmul]
    | add x y hx hy =>
      rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, map_add]
  let ψ : Module.Free.ChooseBasisIndex k E → V →ₗ[k] W := fun j =>
    (Finsupp.lapply j) ∘ₗ c.toLinearMap ∘ₗ (φ.restrictScalars k) ∘ₗ (TensorProduct.mk k E V 1)
  have hψ : ∀ j v, ψ j v = c (φ (1 ⊗ₜ[k] v)) j := fun j v => rfl
  have heq : ∀ j g, ψ j ∘ₗ ρ g = σ g ∘ₗ ψ j := by
    intro j g
    apply LinearMap.ext; intro v
    show c (φ ((1 : E) ⊗ₜ[k] ρ g v)) j = σ g (c (φ ((1 : E) ⊗ₜ[k] v)) j)
    have h1 : (1 : E) ⊗ₜ[k] ρ g v = repBaseChange E ρ g (1 ⊗ₜ v) := by
      simp [repBaseChange, LinearMap.baseChange_tmul]
    have h2 := congrArg (fun f => f ((1 : E) ⊗ₜ[k] v)) (hφ g)
    simp only [LinearMap.coe_comp, Function.comp_apply] at h2
    rw [h1, h2, hc]
  have hne : ∃ j, ψ j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hφ0
    have h1 : ∀ v, φ (1 ⊗ₜ[k] v) = 0 := fun v => by
      apply c.injective
      ext j
      rw [map_zero, Finsupp.zero_apply, ← hψ, h j, LinearMap.zero_apply]
    apply LinearMap.ext; intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      have : a ⊗ₜ[k] v = a • ((1 : E) ⊗ₜ[k] v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, h1, smul_zero, LinearMap.zero_apply]
    | add x y hx hy => rw [map_add, hx, hy]; simp
  obtain ⟨j, hj⟩ := hne
  exact ⟨ψ j, hj, heq j⟩

end GlueI3

#print axioms GlueI3.isIrreducible_of_commutant_scalar
#print axioms GlueI3.isIrreducible_of_finrank_commOf_prod_le_four
#print axioms GlueI3.absolutelyIrreducible_of_finrank_commOf_prod_le_four
#print axioms GlueI3.exists_equivariant_ne_zero_of_common
#print axioms GlueI3.isSemisimple_of_surjective
#print axioms GlueI3.exists_equivariant_ne_zero_of_baseChange

/- glue-I3-linalg: pkg-I3's `I3.lean` (verbatim) + the linear-algebra glue of `Commutant.lean` + C2 in the object layer (§5). -/
/-
pkg-I3: Faltings 1983 and Mumford's structure results, as Lean leaves.

Scratch file (task pkg-I3). Everything here is built on Mathlib v4.35.0 definitions:
schemes over `Spec K`, group objects in `Over (Spec K)`, `AlgebraicClosure`,
`Field.absoluteGaloisGroup`, `PadicInt`, `Representation`, `QuaternionAlgebra`.
No abstract structure is invented: the only new definitions are
* `AbVar K`         : an abelian variety (proper, smooth, geometrically integral group scheme),
* `AbVar.homGroup`  : the group `Hom_K(A, B)` of homomorphisms of group schemes,
* `AbVar.Pt`        : the group `A(K̄)` of `K̄`-points, with the Galois action,
* `Tate.T ℓ M`      : the `ℓ`-adic Tate module `lim M[ℓⁿ]` of an abelian group, as a `ℤ_ℓ`-module,
* `AbVar.T`, `AbVar.V` : `T_ℓ(A)`, `V_ℓ(A) = ℚ_ℓ ⊗ T_ℓ(A)` with the Galois representation.
Leaves are `def … : Prop`.
-/
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.AdjoinRoot

noncomputable section

/-! ## 0. Linear-algebra glue (copied from `scratch/glue-I3-linalg/Commutant.lean`) -/

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


/-- An equivariant linear isomorphism `V ≃ W` gives `dim End_G(V) ≤ dim End_G(W)`. -/
lemma finrank_commOf_le_of_equiv {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (r : G → V →ₗ[k] V) (s : G → W →ₗ[k] W) (e : V ≃ₗ[k] W)
    (he : ∀ g v, e (r g v) = s g (e v)) :
    Module.finrank k (commOf r) ≤ Module.finrank k (commOf s) := by
  have hmem : ∀ φ ∈ commOf r, e.conj φ ∈ commOf s := by
    intro φ hφ g
    apply LinearMap.ext; intro w
    have hφ' := congrArg (fun f => f (e.symm w)) (hφ g)
    simp only [LinearMap.coe_comp, Function.comp_apply] at hφ'
    have he' : e.symm (s g w) = r g (e.symm w) := by
      apply e.injective; rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.conj_apply,
      LinearEquiv.coe_coe]
    rw [he', hφ', he]
  let f : commOf r →ₗ[k] commOf s := e.conj.toLinearMap.restrict hmem
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact e.conj.injective (congrArg Subtype.val hxy)
  exact LinearMap.finrank_le_finrank_of_injective hf

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

end GlueI3


/-! ## 1. The `ℓ`-adic Tate module of an abelian group -/

namespace PkgI3.Tate

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (M : Type*) [AddCommGroup M]

/-- `T_ℓ(M) = lim_n M[ℓⁿ]` (transition maps: multiplication by `ℓ`), realized as the
sequences `(xₙ)` with `x₀ = 0` and `ℓ • xₙ₊₁ = xₙ`; then `xₙ ∈ M[ℓⁿ]`. -/
def T : AddSubgroup (ℕ → M) where
  carrier := {x | x 0 = 0 ∧ ∀ n, ℓ • x (n + 1) = x n}
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨by simp [hx0, hy0], fun n => ?_⟩
    simp [smul_add, hx n, hy n]
  zero_mem' := ⟨rfl, fun n => by simp⟩
  neg_mem' := by
    rintro x ⟨hx0, hx⟩
    refine ⟨by simp [hx0], fun n => ?_⟩
    simp [hx n]

variable {ℓ M}

omit hℓ in
lemma pow_smul_eq_zero {x : ℕ → M} (hx : x ∈ T ℓ M) (n : ℕ) : (ℓ ^ n) • x n = 0 := by
  induction n with
  | zero => simpa using hx.1
  | succ n ih => rw [pow_succ, mul_smul, hx.2 n, ih]

omit hℓ in
lemma nsmul_congr {y : M} {n : ℕ} (hy : (ℓ ^ n) • y = 0) {c d : ℕ}
    (h : (c : ZMod (ℓ ^ n)) = (d : ZMod (ℓ ^ n))) : c • y = d • y := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [← Nat.mod_add_div' c (ℓ ^ n), ← Nat.mod_add_div' d (ℓ ^ n), add_smul, add_smul,
    mul_smul, mul_smul, hy, smul_zero, smul_zero, h]

instance (n : ℕ) : NeZero (ℓ ^ n) := ⟨pow_ne_zero n hℓ.out.ne_zero⟩

lemma val_cast (a : ℤ_[ℓ]) (n : ℕ) :
    (((PadicInt.toZModPow (n + 1) a).val : ℕ) : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a := by
  rw [← PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) a, ZMod.natCast_val]

/-- The `ℤ_ℓ`-action: `(a • x)ₙ = (a mod ℓⁿ) • xₙ`. -/
def smulSeq (a : ℤ_[ℓ]) (x : ℕ → M) : ℕ → M :=
  fun n => (PadicInt.toZModPow n a).val • x n

lemma smulSeq_mem (a : ℤ_[ℓ]) {x : ℕ → M} (hx : x ∈ T ℓ M) : smulSeq a x ∈ T ℓ M := by
  refine ⟨by simp [smulSeq, hx.1], fun n => ?_⟩
  simp only [smulSeq]
  rw [smul_comm, hx.2 n]
  apply nsmul_congr (pow_smul_eq_zero hx n)
  rw [val_cast, ZMod.natCast_zmod_val]

lemma smulSeq_congr {x : ℕ → M} (hx : x ∈ T ℓ M) (n : ℕ) {a : ℤ_[ℓ]} {c : ℕ}
    (h : (c : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a) : smulSeq a x n = c • x n := by
  simp only [smulSeq]
  apply nsmul_congr (pow_smul_eq_zero hx n)
  rw [ZMod.natCast_zmod_val, h]

instance : Module ℤ_[ℓ] (T ℓ M) where
  smul a x := ⟨smulSeq a x.1, smulSeq_mem a x.2⟩
  one_smul x := Subtype.ext <| funext fun n => by
    change smulSeq 1 x.1 n = x.1 n
    rw [smulSeq_congr x.2 n (c := 1) (by simp), one_smul]
  mul_smul a b x := Subtype.ext <| funext fun n => by
    change smulSeq (a * b) x.1 n = smulSeq a (smulSeq b x.1) n
    rw [smulSeq_congr x.2 n (c := (PadicInt.toZModPow n a).val * (PadicInt.toZModPow n b).val)
      (by push_cast; simp), mul_smul]
    rfl
  smul_zero a := Subtype.ext <| funext fun n => by
    change smulSeq a 0 n = 0
    simp [smulSeq]
  smul_add a x y := Subtype.ext <| funext fun n => by
    change smulSeq a (x.1 + y.1) n = smulSeq a x.1 n + smulSeq a y.1 n
    simp [smulSeq, smul_add]
  add_smul a b x := Subtype.ext <| funext fun n => by
    change smulSeq (a + b) x.1 n = smulSeq a x.1 n + smulSeq b x.1 n
    rw [smulSeq_congr x.2 n (c := (PadicInt.toZModPow n a).val + (PadicInt.toZModPow n b).val)
      (by push_cast; simp), add_smul]
    rfl
  zero_smul x := Subtype.ext <| funext fun n => by
    change smulSeq 0 x.1 n = 0
    simp [smulSeq]

@[simp] lemma smul_apply (a : ℤ_[ℓ]) (x : T ℓ M) (n : ℕ) :
    (a • x).1 n = (PadicInt.toZModPow n a).val • x.1 n := rfl

variable {N : Type*} [AddCommGroup N]

/-- Functoriality: a group homomorphism `M → N` induces a `ℤ_ℓ`-linear map `T_ℓ M → T_ℓ N`. -/
def map (φ : M →+ N) : T ℓ M →ₗ[ℤ_[ℓ]] T ℓ N where
  toFun x := ⟨fun n => φ (x.1 n), by simp [x.2.1], fun n => by rw [← map_nsmul, x.2.2 n]⟩
  map_add' x y := Subtype.ext <| funext fun n => by simp
  map_smul' a x := Subtype.ext <| funext fun n => by simp [map_nsmul]

@[simp] lemma map_apply (φ : M →+ N) (x : T ℓ M) (n : ℕ) : (map φ x).1 n = φ (x.1 n) := rfl

end PkgI3.Tate

/-! ## 2. Abelian varieties, their Hom groups, points, Tate modules -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

/-- An abelian variety over a field `K`: a group object in schemes over `Spec K` whose structure
morphism is proper, smooth and geometrically integral (Mumford §4, Milne 1986 §1). -/
structure AbVar (K : Type u) [Field K] where
  /-- the underlying `K`-scheme -/
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

namespace AbVar

variable {K : Type u} [Field K]

/-- Commutativity is a Mathlib theorem (Stacks 0BFD), not an assumption. -/
instance (A : AbVar K) : IsCommMonObj A.X :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.X

/-- The dimension of `A` (Krull dimension of the underlying space). -/
def dim (A : AbVar K) : WithBot ℕ∞ := topologicalKrullDim A.X.left

/-- The homomorphisms `A → B` of group schemes over `K`, as a subgroup of the commutative group
of all `K`-morphisms `A → B` (pointwise product, `Hom.commGroup`). -/
def homGroup (A B : AbVar K) : Subgroup (A.X ⟶ B.X) where
  carrier := {f | IsMonHom f}
  one_mem' := by
    change IsMonHom (toUnit A.X ≫ η[B.X])
    infer_instance
  mul_mem' := by
    rintro f g (hf : IsMonHom f) (hg : IsMonHom g)
    change IsMonHom (lift f g ≫ μ[B.X])
    infer_instance
  inv_mem' := by
    rintro f (hf : IsMonHom f)
    change IsMonHom f⁻¹
    infer_instance

/-- `Hom_K(A, B)`, written additively (a `ℤ`-module). -/
abbrev Hom (A B : AbVar K) : Type u := Additive (homGroup A B)

/-- The underlying morphism of schemes. -/
def Hom.hom {A B : AbVar K} (f : Hom A B) : A.X ⟶ B.X := (Additive.toMul f).1

instance {A B : AbVar K} (f : Hom A B) : IsMonHom f.hom := (Additive.toMul f).2

lemma Hom.ext' {A B : AbVar K} {f g : Hom A B} (h : f.hom = g.hom) : f = g :=
  Additive.toMul.injective (Subtype.ext h)

/-- Package a homomorphism. -/
def Hom.mk' {A B : AbVar K} (f : A.X ⟶ B.X) [IsMonHom f] : Hom A B :=
  Additive.ofMul ⟨f, ‹_›⟩

@[simp] lemma Hom.hom_mk' {A B : AbVar K} (f : A.X ⟶ B.X) [IsMonHom f] :
    (Hom.mk' f).hom = f := rfl
@[simp] lemma Hom.hom_add {A B : AbVar K} (f g : Hom A B) : (f + g).hom = f.hom * g.hom := rfl
@[simp] lemma Hom.hom_zero {A B : AbVar K} : (0 : Hom A B).hom = 1 := rfl

/-- The endomorphism ring `End_K(A)`, with multiplication `f * g = f ∘ g`. -/
abbrev End (A : AbVar K) : Type u := Hom A A

instance (A : AbVar K) : Ring (End A) :=
  { (inferInstance : AddCommGroup (End A)) with
    mul := fun f g => Hom.mk' (g.hom ≫ f.hom)
    one := Hom.mk' (𝟙 _)
    mul_assoc := fun f g h => Hom.ext' (by simp [HMul.hMul, Mul.mul])
    one_mul := fun f => Hom.ext' (by simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one])
    mul_one := fun f => Hom.ext' (by simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one])
    left_distrib := fun f g h => Hom.ext' (by
      change (g + h).hom ≫ f.hom = g.hom ≫ f.hom * h.hom ≫ f.hom
      simp [MonObj.mul_comp])
    right_distrib := fun f g h => Hom.ext' (by
      change h.hom ≫ (f + g).hom = h.hom ≫ f.hom * h.hom ≫ g.hom
      simp [MonObj.comp_mul])
    zero_mul := fun f => Hom.ext' (by
      change f.hom ≫ (1 : A.X ⟶ A.X) = 1
      simp)
    mul_zero := fun f => Hom.ext' (by
      change (1 : A.X ⟶ A.X) ≫ f.hom = 1
      simp) }

/-- The endomorphism algebra `End⁰_K(A) = ℚ ⊗ End_K(A)`. -/
abbrev End0 (A : AbVar K) : Type u := TensorProduct ℤ ℚ (End A)

/-- A morphism of `K`-schemes is an isogeny-type map: finite and surjective. -/
def IsIsogenyMor {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y) : Prop :=
  IsFinite f.left ∧ Surjective f.left

/-! ### Points over a field extension and the Galois action -/

variable (L : Type u) [Field L] [Algebra K L]

/-- `Spec L` as a `K`-scheme. -/
def ptObj : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The group `A(L)` of `L`-points: `K`-morphisms `Spec L → A`. -/
abbrev Pt (A : AbVar K) : Type u := ptObj (K := K) L ⟶ A.X

variable {L}

/-- `σ ∈ Aut_K(L)` acting on `Spec L` over `K`. -/
def galHom (σ : L ≃ₐ[K] L) : ptObj (K := K) L ⟶ ptObj L :=
  Over.homMk (Spec.map (CommRingCat.ofHom (σ : L →+* L))) (by
    simp only [ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

lemma galHom_one : galHom (1 : L ≃ₐ[K] L) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((1 : L ≃ₐ[K] L) : L →+* L)) = 𝟙 (Spec (CommRingCat.of L))
  rw [show CommRingCat.ofHom ((1 : L ≃ₐ[K] L) : L →+* L) = 𝟙 _ from by ext; rfl]
  exact Spec.map_id _

lemma galHom_mul (σ τ : L ≃ₐ[K] L) : galHom (σ * τ) = galHom σ ≫ galHom τ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((σ * τ : L ≃ₐ[K] L) : L →+* L)) =
    Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L))
  rw [← Spec.map_comp]
  congr 1

/-- The Galois action on `A(L)`: `σ • P = P ∘ Spec(σ)`, i.e. `σ` applied to coordinates. -/
def galAct (A : AbVar K) (σ : L ≃ₐ[K] L) : A.Pt L →* A.Pt L where
  toFun P := galHom σ ≫ P
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

/-- A homomorphism `f : A → B` acting on `L`-points. -/
def ptMap {A B : AbVar K} (f : Hom A B) : A.Pt L →* B.Pt L := IsMonHom.monoidHom f.hom _

/-! ### `T_ℓ(A)`, `V_ℓ(A)` and the Galois representation -/

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `T_ℓ(A) = lim A(K̄)[ℓⁿ]`, a `ℤ_ℓ`-module. -/
abbrev T (A : AbVar K) : Type u := Tate.T ℓ (Additive (A.Pt (AlgebraicClosure K)))

/-- `V_ℓ(A) = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ(A)`. -/
abbrev V (A : AbVar K) : Type u := TensorProduct ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ)

variable {ℓ}

/-- Galois action on `T_ℓ(A)`. -/
def galT (A : AbVar K) (σ : Field.absoluteGaloisGroup K) : A.T ℓ →ₗ[ℤ_[ℓ]] A.T ℓ :=
  Tate.map (MonoidHom.toAdditive (A.galAct σ))

/-- A homomorphism acting on Tate modules. -/
def homT {A B : AbVar K} (f : Hom A B) : A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ :=
  Tate.map (MonoidHom.toAdditive (ptMap f))

/-- Galois-equivariance of a `ℤ_ℓ`-linear map of Tate modules. -/
def IsGalEquivariant {A B : AbVar K} (φ : A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) : Prop :=
  ∀ (σ : Field.absoluteGaloisGroup K) (x : A.T ℓ), φ (A.galT σ x) = B.galT σ (φ x)

variable (ℓ)

/-- The Galois representation `ρ_ℓ : G_K → GL(V_ℓ(A))`. -/
def galRep (A : AbVar K) : Representation ℚ_[ℓ] (Field.absoluteGaloisGroup K) (A.V ℓ) where
  toFun σ := (A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ]
  map_one' := by
    have : A.galT (ℓ := ℓ) 1 = LinearMap.id := by
      apply LinearMap.ext; intro x; apply Subtype.ext; funext n
      change Additive.ofMul (galHom (1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≫
        Additive.toMul (x.1 n)) = x.1 n
      rw [galHom_one, Category.id_comp]; rfl
    change (A.galT (ℓ := ℓ) 1).baseChange ℚ_[ℓ] = LinearMap.id
    rw [this, LinearMap.baseChange_id]
  map_mul' σ τ := by
    have : A.galT (ℓ := ℓ) (σ * τ) = A.galT σ ∘ₗ A.galT τ := by
      apply LinearMap.ext; intro x; apply Subtype.ext; funext n
      have h := galHom_mul (K := K) (L := AlgebraicClosure K) σ τ
      change Additive.ofMul (galHom (σ * τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≫
        Additive.toMul (x.1 n)) = Additive.ofMul (galHom σ ≫ galHom τ ≫ Additive.toMul (x.1 n))
      exact (congrArg (fun g => Additive.ofMul (g ≫ Additive.toMul (x.1 n))) h).trans
        (by rw [Category.assoc])
    change (A.galT (ℓ := ℓ) (σ * τ)).baseChange ℚ_[ℓ] =
      (A.galT σ).baseChange ℚ_[ℓ] ∘ₗ (A.galT τ).baseChange ℚ_[ℓ]
    rw [this, LinearMap.baseChange_comp]

/-- The action of `Hom(A, B)` on Tate modules, as a group homomorphism. -/
def tateHom (A B : AbVar K) : Hom A B →+ (A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) where
  toFun f := homT f
  map_zero' := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    simp [homT, ptMap, IsMonHom.monoidHom]
  map_add' f g := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    simp [homT, ptMap, IsMonHom.monoidHom, MonObj.comp_mul]

/-- The `ℤ_ℓ`-linear extension `ℤ_ℓ ⊗_ℤ Hom(A, B) → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)`, `a ⊗ f ↦ a · T_ℓ(f)`. -/
def tateHomZl (A B : AbVar K) :
    TensorProduct ℤ ℤ_[ℓ] (Hom A B) →ₗ[ℤ] (A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) :=
  TensorProduct.lift
    (LinearMap.mk₂ ℤ (fun (a : ℤ_[ℓ]) (f : Hom A B) => a • tateHom ℓ A B f)
      (fun a b f => add_smul a b _)
      (fun n a f => by rw [smul_assoc])
      (fun a f g => by rw [map_add, smul_add])
      (fun n a f => by rw [map_zsmul, smul_comm]))

end AbVar

end PkgI3

/-! ### Base change -/

namespace PkgI3.AbVar

open CategoryTheory AlgebraicGeometry Limits

variable {K : Type} [Field K]

/-- Base change `A_L` along a field extension `L/K` (Mathlib's `Over.pullback`; the group
structure is transported by the monoidal functor `Over.pullback`). -/
def baseChange (A : AbVar K) (L : Type) [Field L] [Algebra K L] : AbVar L :=
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  letI : GrpObj ((Over.pullback f).obj A.X) := Functor.grpObjObj
  haveI : IsProper ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : Smooth ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  { X := (Over.pullback f).obj A.X }

instance geometricallyIntegral_id_spec (K : Type) [Field K] :
    GeometricallyIntegral (𝟙 (Spec (CommRingCat.of K))) := by
  constructor
  intro L _ y Z fst snd h
  have : IsIso snd := h.isIso_snd_of_isIso
  have : Nonempty Z := ⟨(inv snd) (IsLocalRing.closedPoint L)⟩
  exact isIntegral_of_isOpenImmersion snd

open MonoidalCategory in
/-- Sanity check: `AbVar K` is inhabited (by `Spec K`, the zero abelian variety). No
nonzero abelian variety can be constructed in Mathlib v4.35.0: it has no projective group
scheme (Weierstrass curves exist only as point sets, not as `GrpObj`s in `Over (Spec K)`). -/
def zero (K : Type) [Field K] : AbVar K :=
  haveI : IsProper (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by dsimp; infer_instance
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by
    dsimp; infer_instance
  { X := 𝟙_ (Over (Spec (CommRingCat.of K))) }

end PkgI3.AbVar

/-! ## 3. The leaves of package I3

Each leaf is a `Prop` quantified over all fields (resp. number fields) and all abelian varieties
in the sense of `AbVar`; universe `0`. Locators: see `docs/research/pkg-I3.md`. -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AbVar Polynomial
open scoped Quaternion TensorProduct

/-- Every nonzero endomorphism is an isogeny (equivalently `End⁰(A)` is a division algebra);
in characteristic `0` this is equivalent to `A` being simple (Mumford §19, Thm 1 and Cor. 2). -/
def EndDivision {k : Type} [Field k] (A : AbVar k) : Prop :=
  ∀ f : End A, f ≠ 0 → IsIsogenyMor f.hom

/-- **I3.F1 — Faltings 1983, Satz 3 (semisimplicity).** For an abelian variety `A` over a number
field `K` and a prime `ℓ`, the representation of `G_K` on `V_ℓ(A)` is semisimple. -/
def FaltingsSemisimple : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime],
    (A.galRep ℓ).IsSemisimpleRepresentation

/-- **I3.F2 — Faltings 1983, Satz 4 (`A = B`) and Korollar 1 (Tate's conjecture).** For abelian
varieties `A, B` over a number field `K` and a prime `ℓ`, the natural map
`Hom_K(A, B) ⊗ ℤ_ℓ → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)` is injective with image the `G_K`-equivariant maps. -/
def FaltingsTate : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime],
    Function.Injective (tateHomZl ℓ A B) ∧
      Set.range (tateHomZl ℓ A B) = {φ | IsGalEquivariant φ}

/-- **I3.M0 — structure of the Tate module (Mumford §4, `A[n] ≅ (ℤ/n)^{2g}` for `char k ∤ n`;
§18-19).** For `ℓ ≠ char k`, `T_ℓ(A)` is free of rank `2 dim A` over `ℤ_ℓ`. -/
def TateModuleFree : Prop :=
  ∀ (k : Type) [Field k] (A : AbVar k) (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
    Module.Free ℤ_[ℓ] (A.T ℓ) ∧ Module.Finite ℤ_[ℓ] (A.T ℓ) ∧
      ((Module.finrank ℤ_[ℓ] (A.T ℓ) : ℕ∞) : WithBot ℕ∞) = 2 * A.dim

/-- **I3.M1 — Mumford §19, Thm 3.** `Hom(A, B)` is a free `ℤ`-module of finite rank
`≤ 4 dim A dim B`, and for `ℓ ≠ char k` the map `Hom(A, B) ⊗ ℤ_ℓ → Hom(T_ℓ A, T_ℓ B)` is injective. -/
def HomFreeFinite : Prop :=
  ∀ (k : Type) [Field k] (A B : AbVar k),
    Module.Free ℤ (Hom A B) ∧ Module.Finite ℤ (Hom A B) ∧
      ((Module.finrank ℤ (Hom A B) : ℕ∞) : WithBot ℕ∞) ≤ 4 * A.dim * B.dim ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 → Function.Injective (tateHomZl ℓ A B)

/-- **I3.M2 — Mumford §19, Thm 4 (independence of `ℓ`).** For `φ ∈ End(A)` there is a monic
`P ∈ ℤ[X]` that is the characteristic polynomial of `V_ℓ(φ)` for every prime `ℓ ≠ char k`
(computed in any finite basis). -/
def CharPolyIndepOfEll : Prop :=
  ∀ (k : Type) [Field k] (A : AbVar k) (φ : End A), ∃ P : ℤ[X], P.Monic ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        (LinearMap.toMatrix b b ((homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
          P.map (Int.castRingHom ℚ_[ℓ])

/-- **I3.M3 — Poincaré complete reducibility (Mumford §19, Thm 1), in the form used at E1.**
Over a field of characteristic `0`, if `End⁰(A)` is a division algebra and `f : A → J` is a
nonzero homomorphism, there are an abelian variety `Z` and a homomorphism `g : Z → J` such that
`(f, g) : A × Z → J`, `(a, z) ↦ f(a) + g(z)`, is an isogeny. -/
def PoincareReducibility : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A J : AbVar k), EndDivision A →
    ∀ f : Hom A J, f ≠ 0 → ∃ (Z : AbVar k) (g : Hom Z J),
      IsIsogenyMor (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom)

/-- **I3.Q — the QM dichotomy (step A9).** Over an algebraically closed field of characteristic
`0`, if a quaternion division algebra `B = (a, b)_ℚ` embeds in `End⁰(A)` for an abelian surface
`A`, then `End⁰(A) ≅ B` or `End⁰(A) ≅ M₂(ℚ(√d))` with `d < 0`. (Consequence of Mumford §19
Thm 1, Cor. 2, §21 (Albert, `[D:ℚ] ∣ 2g` in characteristic `0`) and §22; see the note.) -/
def QMDichotomy : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : AbVar k), A.dim = 2 →
    ∀ a b : ℚ, (∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x) →
      Nonempty (ℍ[ℚ, a, b] →ₐ[ℚ] End0 A) →
        Nonempty (End0 A ≃ₐ[ℚ] ℍ[ℚ, a, b]) ∨
          ∃ d : ℚ, d < 0 ∧
            Nonempty (End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)))

/-- The package as one hypothesis. -/
structure I3Leaves : Prop where
  faltingsSemisimple : FaltingsSemisimple
  faltingsTate : FaltingsTate
  tateModuleFree : TateModuleFree
  homFreeFinite : HomFreeFinite
  charPolyIndepOfEll : CharPolyIndepOfEll
  poincare : PoincareReducibility
  qmDichotomy : QMDichotomy

end PkgI3

/-! ## 4. Glue checks: the leaves are usable with these definitions -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry MonObj AbVar
open scoped TensorProduct

/-- The easy half of Faltings' statement holds outright: the image of `Hom(A, B) ⊗ ℤ_ℓ`
consists of Galois-equivariant maps. (So `FaltingsTate` asserts injectivity and the reverse
inclusion, as in the published statement.) -/
lemma homT_galT {K : Type} [Field K] {A B : AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (f : Hom A B)
    (σ : Field.absoluteGaloisGroup K) (x : A.T ℓ) :
    homT f (A.galT σ x) = B.galT σ (homT f x) := by
  apply Subtype.ext; funext n
  change Additive.ofMul ((galHom σ ≫ Additive.toMul (x.1 n)) ≫ f.hom) =
    Additive.ofMul (galHom σ ≫ (Additive.toMul (x.1 n) ≫ f.hom))
  rw [Category.assoc]

theorem range_tateHomZl_subset {K : Type} [Field K] (A B : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Set.range (tateHomZl ℓ A B) ⊆ {φ | IsGalEquivariant φ} := by
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.induction_on with
  | zero => intro σ x; simp
  | tmul a f =>
    intro σ x
    have e : tateHomZl ℓ A B (a ⊗ₜ f) = a • tateHom ℓ A B f := rfl
    rw [e, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
    exact congrArg (a • ·) (homT_galT f σ x)
  | add y z hy hz =>
    intro σ x
    simp only [map_add, LinearMap.add_apply, hy σ x, hz σ x]

/-- **Glue for E1.** From Faltings' theorem and the structure of `T_ℓ`: a nonzero
`G_K`-equivariant `ℚ_ℓ`-linear map `V_ℓ(A) → V_ℓ(B)` forces a nonzero homomorphism `A → B`. -/
theorem exists_hom_ne_zero_of_equivariant (hF : FaltingsTate) (hT : TateModuleFree)
    {K : Type} [Field K] [NumberField K] (A B : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (φ : A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ) (hφ : φ ≠ 0)
    (heq : ∀ σ, φ ∘ₗ A.galRep ℓ σ = B.galRep ℓ σ ∘ₗ φ) : ∃ f : Hom A B, f ≠ 0 := by
  classical
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨-, hfinA, -⟩ := hT K A ℓ hℓK
  obtain ⟨hfreeB, -, -⟩ := hT K B ℓ hℓK
  have : Module.FinitePresentation ℤ_[ℓ] (A.T ℓ) := Module.finitePresentation_of_finite _ _
  let ιA : A.T ℓ →ₗ[ℤ_[ℓ]] A.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ) 1
  let ιB : B.T ℓ →ₗ[ℤ_[ℓ]] B.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (B.T ℓ) 1
  have : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) ιB := inferInstance
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (nonZeroDivisors ℤ_[ℓ]) ιB ((φ.restrictScalars ℤ_[ℓ]) ∘ₗ ιA)
  have hs0 : (s : ℤ_[ℓ]) ≠ 0 := nonZeroDivisors.ne_zero s.2
  -- `ιB` is injective (`T_ℓ B` is free, hence torsion-free).
  have hιB : Function.Injective ιB := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[ℓ]) ιB).mp hy
    exact (smul_eq_zero.mp ht).resolve_left (nonZeroDivisors.ne_zero t.2)
  -- the Galois actions commute with `ι`
  have hιAσ : ∀ σ x, ιA (A.galT σ x) = A.galRep ℓ σ (ιA x) := fun σ x => by
    simp [ιA, galRep, LinearMap.baseChange_tmul]
  have hιBσ : ∀ σ x, ιB (B.galT σ x) = B.galRep ℓ σ (ιB x) := fun σ x => by
    simp [ιB, galRep, LinearMap.baseChange_tmul]
  have hsφ : ∀ x, ιB (h x) = (s : ℤ_[ℓ]) • φ (ιA x) := fun x => by
    have := congrArg (fun g => g x) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      LinearMap.coe_restrictScalars, Submonoid.smul_def] at this
    exact this
  -- `h` is equivariant
  have hheq : IsGalEquivariant h := by
    intro σ x
    apply hιB
    rw [hsφ, hιAσ, hιBσ, hsφ]
    have := congrArg (fun g => g (ιA x)) (heq σ)
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    rw [this, LinearMap.map_smul_of_tower]
  -- `h ≠ 0`
  have hh0 : h ≠ 0 := by
    intro h0
    apply hφ
    have hφι : ∀ x, φ (ιA x) = 0 := fun x => by
      have h1 : (s : ℤ_[ℓ]) • φ (ιA x) = 0 := by rw [← hsφ, h0]; simp
      rw [← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ])] at h1
      exact (smul_eq_zero.mp h1).resolve_left (by
        simpa using (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]).ne hs0)
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul q x =>
      have : (q ⊗ₜ[ℤ_[ℓ]] x : A.V ℓ) = q • ιA x := by simp [ιA, TensorProduct.smul_tmul']
      rw [this, map_smul, hφι, smul_zero, LinearMap.zero_apply]
    | add v w hv hw => simp [map_add, hv, hw]
  -- conclude with Faltings
  obtain ⟨z, hz⟩ : h ∈ Set.range (tateHomZl ℓ A B) := by
    rw [(hF K A B ℓ).2]; exact hheq
  by_contra hall
  simp only [ne_eq, not_exists, not_not] at hall
  have : Subsingleton (Hom A B) := ⟨fun f g => (hall f).trans (hall g).symm⟩
  have : z = 0 := Subsingleton.elim _ _
  exact hh0 (by rw [← hz, this, map_zero])

/-- The `G_K`-equivariant `ℚ_ℓ`-linear endomorphisms of `V_ℓ(A)`. -/
def equivEnd {K : Type} [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Submodule ℚ_[ℓ] (Module.End ℚ_[ℓ] (A.V ℓ)) where
  carrier := {φ | ∀ σ, φ ∘ₗ A.galRep ℓ σ = A.galRep ℓ σ ∘ₗ φ}
  add_mem' := by
    intro φ ψ hφ hψ σ
    simp only [Set.mem_setOf_eq] at *
    rw [LinearMap.add_comp, LinearMap.comp_add, hφ σ, hψ σ]
  zero_mem' := by intro σ; simp
  smul_mem' := by
    intro c φ hφ σ
    simp only [Set.mem_setOf_eq] at *
    rw [LinearMap.smul_comp, LinearMap.comp_smul, hφ σ]

/-- **Glue for C2 (GLUE, proved).** The `ℚ_ℓ`-form of Satz 4:
`dim_{ℚ_ℓ} End_{G_K}(V_ℓ A) = rank_ℤ End_K(A)`. With `FaltingsSemisimple` and
`End⁰_K(A) ≅ B` (A9, A10, and `L'` defining every geometric endomorphism), the commutant
argument of N5 L731-734 then gives absolute irreducibility of `r_ℓ`.
Proof: `T_ℓ A` is free of finite rank (`TateModuleFree`), so every `φ ∈ End(V_ℓ A)`
has `ℓᵏφ(T_ℓ A) ⊆ T_ℓ A`; equivariance passes to `T_ℓ A` because `T_ℓ A → V_ℓ A` is injective
(as in `exists_hom_ne_zero_of_equivariant`); so `End_G(V) = ℚ_ℓ ⊗ End_G(T)`, and
`End_G(T) ≅ ℤ_ℓ ⊗ End(A)` (`FaltingsTate`) is free of rank `rank_ℤ End(A)` (`HomFreeFinite`). -/
theorem finrank_equivEnd (hF : FaltingsTate) (hT : TateModuleFree) (hH : HomFreeFinite)
    {K : Type} [Field K] [NumberField K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.finrank ℚ_[ℓ] (equivEnd A ℓ) = Module.finrank ℤ (End A) := by
  classical
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨hfree, hfin, -⟩ := hT K A ℓ hℓK
  obtain ⟨hHfree, hHfin, -, -⟩ := hH K A A
  have : Module.FinitePresentation ℤ_[ℓ] (A.T ℓ) := Module.finitePresentation_of_finite _ _
  let jT : A.T ℓ →ₗ[ℤ_[ℓ]] A.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ) 1
  have : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) jT := inferInstance
  have hj : Function.Injective jT := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[ℓ]) jT).mp hy
    exact (smul_eq_zero.mp ht).resolve_left (nonZeroDivisors.ne_zero t.2)
  have hjσ : ∀ σ x, jT (A.galT σ x) = A.galRep ℓ σ (jT x) := fun σ x => by
    simp [jT, galRep, LinearMap.baseChange_tmul]
  have hjψ : ∀ (ψ : Module.End ℤ_[ℓ] (A.T ℓ)) x, jT (ψ x) = ψ.baseChange ℚ_[ℓ] (jT x) :=
    fun ψ x => by simp [jT, LinearMap.baseChange_tmul]
  -- the equivariant endomorphisms of `T_ℓ A`
  let ET : Submodule ℤ_[ℓ] (Module.End ℤ_[ℓ] (A.T ℓ)) :=
    { carrier := {ψ | IsGalEquivariant ψ}
      add_mem' := fun {ψ χ} hψ hχ σ x => by
        simp only [LinearMap.add_apply, map_add, hψ σ x, hχ σ x]
      zero_mem' := fun σ x => by simp
      smul_mem' := fun c ψ hψ σ x => by
        simp only [LinearMap.smul_apply, map_smul, hψ σ x] }
  -- Step 1: `ET ≅ ℤ_ℓ ⊗ End A` (Faltings), so `rank ET = rank End A`.
  have hsmul : ∀ (a : ℤ_[ℓ]) z, tateHomZl ℓ A A (a • z) = a • tateHomZl ℓ A A z := by
    intro a z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b f =>
      rw [TensorProduct.smul_tmul', smul_eq_mul,
        show tateHomZl ℓ A A ((a * b) ⊗ₜ f) = (a * b) • tateHom ℓ A A f from rfl,
        show tateHomZl ℓ A A (b ⊗ₜ f) = b • tateHom ℓ A A f from rfl, mul_smul]
    | add y z hy hz => rw [smul_add, map_add, map_add, hy, hz, smul_add]
  let L1 : TensorProduct ℤ ℤ_[ℓ] (End A) →ₗ[ℤ_[ℓ]] ET :=
    { toFun := fun z => ⟨tateHomZl ℓ A A z, range_tateHomZl_subset A A ℓ ⟨z, rfl⟩⟩
      map_add' := fun y z => Subtype.ext (map_add _ y z)
      map_smul' := fun a z => Subtype.ext (hsmul a z) }
  have hL1 : Function.Bijective L1 := by
    refine ⟨fun y z h => (hF K A A ℓ).1 (congrArg Subtype.val h), fun ψ => ?_⟩
    obtain ⟨z, hz⟩ : ψ.1 ∈ Set.range (tateHomZl ℓ A A) := by
      rw [(hF K A A ℓ).2]; exact ψ.2
    exact ⟨z, Subtype.ext hz⟩
  have h1 : Module.finrank ℤ_[ℓ] ET = Module.finrank ℤ (End A) := by
    rw [← (LinearEquiv.ofBijective L1 hL1).finrank_eq, Module.finrank_baseChange]
  -- Step 2: `equivEnd A ℓ` is the localization of `ET`.
  let Φ : ET →ₗ[ℤ_[ℓ]] equivEnd A ℓ :=
    { toFun := fun ψ => ⟨ψ.1.baseChange ℚ_[ℓ], fun σ => by
        change ψ.1.baseChange ℚ_[ℓ] ∘ₗ (A.galT σ).baseChange ℚ_[ℓ] =
          (A.galT σ).baseChange ℚ_[ℓ] ∘ₗ ψ.1.baseChange ℚ_[ℓ]
        rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
        congr 1
        exact LinearMap.ext fun x => ψ.2 σ x⟩
      map_add' := fun ψ χ => Subtype.ext (LinearMap.baseChange_add _ _)
      map_smul' := fun c ψ => Subtype.ext (LinearMap.baseChange_smul _ _) }
  have hΦ : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) Φ := by
    constructor
    · intro s
      have hc : algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]) ≠ 0 := by
        simpa using (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]).ne (nonZeroDivisors.ne_zero s.2)
      rw [Module.End.isUnit_iff]
      constructor
      · intro x y hxy
        simp only [Module.algebraMap_end_apply] at hxy
        rw [← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ]) x, ← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ]) y] at hxy
        exact smul_right_injective _ hc hxy
      · intro y
        refine ⟨(algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]))⁻¹ • y, ?_⟩
        simp only [Module.algebraMap_end_apply]
        rw [← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ]), smul_smul, mul_inv_cancel₀ hc, one_smul]
    · intro φ
      obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
        (nonZeroDivisors ℤ_[ℓ]) jT ((φ.1.restrictScalars ℤ_[ℓ]) ∘ₗ jT)
      have hsφ : ∀ x, jT (h x) = (s : ℤ_[ℓ]) • φ.1 (jT x) := fun x => by
        have := congrArg (fun g => g x) hs
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
          LinearMap.coe_restrictScalars, Submonoid.smul_def] at this
        exact this
      have hheq : IsGalEquivariant h := by
        intro σ x
        apply hj
        rw [hsφ, hjσ, hjσ, hsφ]
        have := congrArg (fun g => g (jT x)) (φ.2 σ)
        simp only [LinearMap.coe_comp, Function.comp_apply] at this
        rw [this, LinearMap.map_smul_of_tower]
      refine ⟨⟨⟨h, hheq⟩, s⟩, Subtype.ext ?_⟩
      apply TensorProduct.AlgebraTensorModule.curry_injective
      apply LinearMap.ext_ring
      apply LinearMap.ext
      intro x
      change (s : ℤ_[ℓ]) • φ.1 ((1 : ℚ_[ℓ]) ⊗ₜ x) = h.baseChange ℚ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ x)
      exact (hsφ x).symm.trans (hjψ h x)
    · intro ψ χ hψχ
      refine ⟨1, ?_⟩
      rw [one_smul, one_smul]
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      apply hj
      rw [hjψ, hjψ]
      exact congrArg (fun g => g (jT x)) (congrArg Subtype.val hψχ)
  have e1 := IsLocalization.finrank_eq (R := ℤ_[ℓ]) (N := equivEnd A ℓ) ℚ_[ℓ]
    (nonZeroDivisors ℤ_[ℓ]) le_rfl
  have e2 := IsLocalizedModule.finrank_eq (M := ET) (N := equivEnd A ℓ) (p := nonZeroDivisors ℤ_[ℓ]) (f := Φ) le_rfl
  rw [e1, e2, h1]

end PkgI3

/-! ## 5. C2 in the object layer of pkg-I3 -/

namespace PkgI3

open GlueI3 AbVar

lemma equivEnd_eq_commOf {K : Type} [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    equivEnd A ℓ = commOf (k := ℚ_[ℓ]) (fun σ => A.galRep ℓ σ) := rfl

/-- **C2 (GLUE, proved from I3's leaves, the two linear-algebra statements, and A9's output).**
`A` over a number field `K` with `rank_ℤ End_K(A) = 4` (`End⁰_K(A) = B`, from A9, A10, A8/B3);
`E ⊇ ℚ_ℓ` a field and `V_ℓ(A) ⊗ E ≅ r ⊕ r` as `G_K`-representations (from `B ⊗ E ≅ M₂(E)`), with `r`
semisimple (a quotient of `V_ℓ(A) ⊗ E`, semisimple by `FaltingsSemisimple` and
`SemisimpleBaseChange`; derived here). Then `r` is absolutely irreducible: `r ⊗ F` is irreducible
for every field `F ⊇ E`. -/
theorem C2_absolutelyIrreducible (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree) (hH : HomFreeFinite)
    (hInv : InvariantsBaseChange) (hSS : SemisimpleBaseChange)
    {K : Type} [Field K] [NumberField K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (hrank : Module.finrank ℤ (End A) = 4)
    (E : Type) [Field E] [CharZero E] [Algebra ℚ_[ℓ] E]
    {U : Type} [AddCommGroup U] [Module E U] [FiniteDimensional E U] [Nontrivial U]
    (r : Representation E (Field.absoluteGaloisGroup K) U)
    (e : TensorProduct ℚ_[ℓ] E (A.V ℓ) ≃ₗ[E] U × U)
    (he : ∀ σ v, e (repBaseChange E (A.galRep ℓ) σ v) = (r σ).prodMap (r σ) (e v))
    (F : Type) [Field F] [Algebra E F] : (repBaseChange F r).IsIrreducible := by
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨-, hfin, -⟩ := hT K A ℓ hℓK
  have : FiniteDimensional ℚ_[ℓ] (A.V ℓ) := inferInstance
  have h1 : Module.finrank E (commOf (k := E) (fun σ => repBaseChange E (A.galRep ℓ) σ)) = 4 := by
    rw [hInv ℚ_[ℓ] E _ _ (A.galRep ℓ), ← equivEnd_eq_commOf, finrank_equivEnd hF hT hH, hrank]
  have he' : ∀ σ w, e.symm ((r σ).prodMap (r σ) w) = repBaseChange E (A.galRep ℓ) σ (e.symm w) := by
    intro σ w
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have h4 := finrank_commOf_le_of_equiv (fun σ => (r σ).prodMap (r σ)) _ e.symm he'
  rw [h1] at h4
  have hVE := hSS ℚ_[ℓ] E _ _ (A.galRep ℓ) (hS K A ℓ)
  have hr : r.IsSemisimpleRepresentation := by
    refine isSemisimple_of_surjective (repBaseChange E (A.galRep ℓ)) r hVE
      (LinearMap.fst E U U ∘ₗ e.toLinearMap) ?_ ?_
    · intro u
      exact ⟨e.symm (u, 0), by simp⟩
    · intro σ v
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearMap.fst_apply]
      rw [he]
      rfl
  exact absolutelyIrreducible_of_finrank_commOf_prod_le_four hInv hSS r hr h4 F

end PkgI3

#print axioms PkgI3.C2_absolutelyIrreducible

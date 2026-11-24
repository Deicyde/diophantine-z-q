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
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.Dual.Lemmas
import ZInQKernel.HDecomp.Objects

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt2 from
`scratch/glue-ssbc/C2.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

/- glue-ssbc: glue-I3-linalg's C2.lean with `SemisimpleBaseChange` proved (§0) and C2, E1 restated
  without it (end).
   Original header: glue-I3-linalg: pkg-I3's `I3.lean` (verbatim) + the linear-algebra glue of
   `Commutant.lean` + C2 and E1 in the object layer (§5). -/

noncomputable section

/-! ## 0. Linear-algebra glue (copied from `scratch/glue-I3-linalg/Commutant.lean`, plus
`finrank_commOf_le_of_equiv` and `equivariantDescent`) -/

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
    (IntertwiningMap.equivLinearMapAsModule ρ σ (LinearMap.intertwiningMap_of_isIntertwiningMap ρ σ
        f hfeq)) hf

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

/-- **GLUE, not proved here (algebra; STANDARD).** In characteristic `0`, semisimplicity of a
finite-dimensional representation survives extension of the coefficient field. (The span of
`ρ(G)` is a finite-dimensional algebra with a faithful semisimple module, hence semisimple, hence
separable since `k` is perfect, so its base change is semisimple.) -/
def SemisimpleBaseChange : Prop :=
  ∀ (k E G V : Type) [Field k] [CharZero k] [Field E] [Algebra k E] [Monoid G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k G V),
    ρ.IsSemisimpleRepresentation → (repBaseChange E ρ).IsSemisimpleRepresentation

/-! ### `SemisimpleBaseChange`, proved (glue-ssbc; copied from `scratch/glue-ssbc/SSBC.lean`) -/

section General

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]

/-- The trace form `(x, y) ↦ tr_W (x y)` on a subalgebra `B ⊆ End_F W` is nondegenerate. -/
def TraceNondeg (B : Subalgebra F (Module.End F W)) : Prop :=
  ∀ x ∈ B, (∀ y ∈ B, LinearMap.trace F W (x * y) = 0) → x = 0

/-- A finite-dimensional subalgebra of `End W` with nondegenerate trace form is a semisimple
ring. -/
theorem isSemisimpleRing_of_traceNondeg (B : Subalgebra F (Module.End F W))
    (h : TraceNondeg B) : IsSemisimpleRing B := by
  have : IsArtinianRing B := IsArtinianRing.of_finite F B
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  intro x hx
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
  rw [Ideal.jacobson_bot] at hn
  have hnil : ∀ y : B, IsNilpotent ((x : Module.End F W) * y) := by
    intro y
    have hxy : x * y ∈ Ring.jacobson B := Ideal.mul_mem_right _ _ hx
    refine ⟨n, ?_⟩
    have : (x * y) ^ n ∈ Ring.jacobson B ^ n := Ideal.pow_mem_pow hxy n
    rw [hn] at this
    have h0 : (x * y) ^ n = 0 := (Submodule.mem_bot _).mp this
    have := congrArg (fun z : B => (z : Module.End F W)) h0
    simpa using this
  have : (x : Module.End F W) = 0 := by
    apply h _ x.2
    intro y hy
    exact (LinearMap.isNilpotent_trace_of_isNilpotent (hnil ⟨y, hy⟩)).eq_zero
  exact (Submodule.mem_bot _).mpr (Subtype.ext this)

set_option backward.isDefEq.respectTransparency false in
/-- A faithful finite-dimensional semisimple module makes the subalgebra a semisimple ring. -/
theorem isSemisimpleRing_of_isSemisimpleModule (B : Subalgebra F (Module.End F W))
    [IsSemisimpleModule B W] : IsSemisimpleRing B := by
  let bas := Module.finBasis F W
  let n := Module.finrank F W
  let f : B →ₗ[B] (Fin n →₀ W) :=
    (Finsupp.linearEquivFunOnFinite B W (Fin n)).symm.toLinearMap ∘ₗ
      LinearMap.pi (fun i => LinearMap.toSpanSingleton B W (bas i))
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro b hb
    rw [LinearMap.mem_ker] at hb
    rw [Submodule.mem_bot]
    apply Subtype.ext
    apply bas.ext
    intro i
    have := congrArg (fun φ : Fin n →₀ W => φ i) hb
    simpa [f, Subalgebra.smul_def, Module.End.smul_def] using this
  have : IsSemisimpleModule B (LinearMap.range f) := inferInstance
  refine IsSemisimpleModule.congr (R := B) (N := B) (M := ↥(LinearMap.range f)) ?_
  exact LinearEquiv.ofInjective f hf

/-- **Char 0:** a subalgebra of `End W` over which `W` is semisimple has nondegenerate trace
form. -/
theorem traceNondeg_of_isSemisimpleModule [CharZero F] (B : Subalgebra F (Module.End F W))
    [IsSemisimpleModule B W] : TraceNondeg B := by
  have := isSemisimpleRing_of_isSemisimpleModule B
  let I : Ideal B :=
    { carrier := {x | ∀ y : B, LinearMap.trace F W ((x : Module.End F W) * y) = 0}
      add_mem' := by
        intro a b ha hb y
        simp only [Set.mem_ofPred_eq, Subalgebra.coe_add, add_mul, map_add] at *
        rw [ha y, hb y, add_zero]
      zero_mem' := by intro y; simp
      smul_mem' := by
        intro c x hx y
        simp only [Set.mem_ofPred_eq, smul_eq_mul, Subalgebra.coe_mul] at *
        rw [mul_assoc, LinearMap.trace_mul_comm, mul_assoc]
        have := hx (y * c)
        simpa using this }
  obtain ⟨e, he, hIe⟩ := IsSemisimpleRing.ideal_eq_span_idempotent I
  have heI : e ∈ I := hIe ▸ Ideal.subset_span (Set.mem_singleton e)
  have he' : IsIdempotentElem (e : Module.End F W) := by
    have := congrArg (fun z : B => (z : Module.End F W)) he.eq
    simpa [IsIdempotentElem] using this
  have htr : LinearMap.trace F W (e : Module.End F W) = 0 := by
    have := heI e
    rwa [he'.eq] at this
  have he0 : e = 0 := Subtype.ext ((LinearMap.IsIdempotentElem.trace_eq_zero_iff he').mp htr)
  have hI : I = ⊥ := by rw [hIe, he0, Ideal.span_singleton_eq_bot]
  intro x hx hxy
  have : (⟨x, hx⟩ : B) ∈ I := fun y => hxy y y.2
  rw [hI] at this
  exact congrArg Subtype.val ((Submodule.mem_bot _).mp this)

end General

section SSBC

/-- `ρ` is semisimple iff `V` is a semisimple module over the span of `ρ(G)`. -/
theorem isSemisimpleRepresentation_iff_range (ρ : Representation k G V) :
    ρ.IsSemisimpleRepresentation ↔ IsSemisimpleModule (asAlgebraHom ρ).range V := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  let σ : MonoidAlgebra k G →+* (asAlgebraHom ρ).range := (asAlgebraHom ρ).rangeRestrict.toRingHom
  have : RingHomSurjective σ := ⟨AlgHom.rangeRestrict_surjective _⟩
  let l : ρ.asModule →ₛₗ[σ] V :=
    { toFun := ρ.asModuleEquiv
      map_add' := map_add _
      map_smul' := fun r x => asModuleEquiv_map_smul ρ r x }
  exact LinearMap.isSemisimpleModule_iff_of_bijective l ρ.asModuleEquiv.bijective

theorem mem_range_of (ρ : Representation k G V) (g : G) : ρ g ∈ (asAlgebraHom ρ).range :=
  ⟨MonoidAlgebra.of k G g, asAlgebraHom_of ρ g⟩

theorem asAlgebraHom_eq_sum (ρ : Representation k G V) (r : MonoidAlgebra k G) :
    asAlgebraHom ρ r = r.coeff.sum (fun g a => a • ρ g) := by
  rw [asAlgebraHom_def, MonoidAlgebra.lift_apply]

theorem baseChange_mem_range (E : Type*) [Field E] [Algebra k E] (ρ : Representation k G V)
    (y : Module.End k V) (hy : y ∈ (asAlgebraHom ρ).range) :
    y.baseChange E ∈ (asAlgebraHom (repBaseChange E ρ)).range := by
  obtain ⟨s, rfl⟩ := hy
  show (asAlgebraHom ρ s).baseChange E ∈ _
  induction s using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, LinearMap.baseChange_add]; exact Subalgebra.add_mem _ ha hb
  | single g a =>
    rw [asAlgebraHom_single, LinearMap.baseChange_smul, ← algebraMap_smul E a]
    exact Subalgebra.smul_mem _ (mem_range_of (repBaseChange E ρ) g) _

variable [FiniteDimensional k V]

/-- **Base change of the trace-form criterion.** -/
theorem traceNondeg_baseChange (E : Type*) [Field E] [Algebra k E] (ρ : Representation k G V)
    (hA : TraceNondeg (asAlgebraHom ρ).range) :
    TraceNondeg (asAlgebraHom (repBaseChange E ρ)).range := by
  intro x hx hxy
  obtain ⟨r, rfl⟩ := hx
  change (∀ y ∈ _, LinearMap.trace E _ (asAlgebraHom (repBaseChange E ρ) r * y) = 0) at hxy
  show asAlgebraHom (repBaseChange E ρ) r = 0
  rw [asAlgebraHom_eq_sum] at hxy ⊢
  set c := r.coeff
  have hρE : ∀ g, repBaseChange E ρ g = (ρ g).baseChange E := fun g => rfl
  -- every `k`-linear functional of the coefficients gives an element of the radical over `k`
  have key : ∀ f : Module.Dual k E, c.sum (fun g a => f a • ρ g) = 0 := by
    intro f
    apply hA _ (Subalgebra.sum_mem _ fun g _ => Subalgebra.smul_mem _ (mem_range_of ρ g) _)
    intro y hy
    have h0 := congrArg f (hxy _ (baseChange_mem_range E ρ y hy))
    simp only [Finsupp.sum, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, hρE,
      ← LinearMap.baseChange_mul, LinearMap.trace_baseChange, smul_eq_mul, map_zero] at h0 ⊢
    rw [← h0]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_comm (c g), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  let b := Module.finBasis k V
  have hv : ∀ v : V, (c.sum (fun g a => a • repBaseChange E ρ g)) (1 ⊗ₜ v) = 0 := by
    intro v
    apply (Algebra.TensorProduct.basis E b).repr.injective
    ext j
    rw [map_zero, Finsupp.zero_apply]
    rw [← Module.forall_dual_apply_eq_zero_iff k]
    intro f
    have hk := congrArg (fun φ : Module.End k V => b.repr (φ v) j) (key f)
    simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, hρE,
      LinearMap.baseChange_tmul, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply,
      smul_eq_mul, LinearMap.zero_apply, map_zero, Finsupp.zero_apply] at hk ⊢
    rw [← hk]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_comm (c g), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  apply (Algebra.TensorProduct.basis E b).ext
  intro i
  rw [Algebra.TensorProduct.basis_apply, hv, LinearMap.zero_apply]

/-- **`SemisimpleBaseChange`, proved.** In characteristic `0`, a semisimple finite-dimensional
representation stays semisimple after any extension of the coefficient field. -/
theorem isSemisimpleRepresentation_baseChange [CharZero k] (E : Type*) [Field E] [Algebra k E]
    (ρ : Representation k G V) (hρ : ρ.IsSemisimpleRepresentation) :
    (repBaseChange E ρ).IsSemisimpleRepresentation := by
  rw [isSemisimpleRepresentation_iff_range] at hρ ⊢
  have hA := traceNondeg_of_isSemisimpleModule (asAlgebraHom ρ).range
  have := isSemisimpleRing_of_traceNondeg _ (traceNondeg_baseChange E ρ hA)
  infer_instance


end SSBC

/-- **`SemisimpleBaseChange` (GLUE, proved by glue-ssbc).** -/
theorem semisimpleBaseChange : SemisimpleBaseChange :=
  fun _ E _ _ _ _ _ _ _ _ _ _ ρ hρ => isSemisimpleRepresentation_baseChange E ρ hρ

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

/-- `E ⊗_k End_G(V) → End_E(E ⊗ V)`, `e ⊗ ψ ↦ e • (ψ ⊗ E)`. -/
def commBaseChange (E : Type*) [Field E] [Algebra k E] (ρ : Representation k G V) :
    TensorProduct k E (commOf (k := k) (fun g => ρ g)) →ₗ[E]
      (TensorProduct k E V →ₗ[E] TensorProduct k E V) :=
  ((LinearMap.baseChangeHom k E V V) ∘ₗ (commOf (k := k) (fun g => ρ g)).subtype).liftBaseChange E

/-- **Every equivariant `E`-linear endomorphism of `E ⊗ V` comes from `E ⊗ End_G(V)` (GLUE,
proved).** Coordinates in a `k`-basis `(bⱼ)` of `E`: `φ = ∑ⱼ bⱼ • (ψⱼ ⊗ E)` with `ψⱼ ∈ End_G(V)`. -/
theorem commOf_baseChange_le_range (E : Type*) [Field E] [Algebra k E]
    (ρ : Representation k G V) [FiniteDimensional k V] :
    commOf (k := E) (fun g => repBaseChange E ρ g) ≤ LinearMap.range (commBaseChange E ρ) := by
  classical
  let C := commOf (k := k) (fun g => ρ g)
  let Φ := commBaseChange E ρ
  intro φ hφ
  have hmem : φ ∈ LinearMap.range Φ := by
    let b := Module.Free.chooseBasis k E
    let c : TensorProduct k E V ≃ₗ[k] (Module.Free.ChooseBasisIndex k E →₀ V) :=
      (TensorProduct.congr b.repr (LinearEquiv.refl k V)).trans
        (TensorProduct.finsuppScalarLeft k V _)
    have hc : ∀ (x : TensorProduct k E V) g j, c (repBaseChange E ρ g x) j = ρ g (c x j) := by
      intro x g j
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a w =>
        simp [c, repBaseChange, LinearMap.baseChange_tmul]
      | add x y hx hy =>
        rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, map_add]
    have hcb : ∀ j (w : V) j', c (b j ⊗ₜ[k] w) j' = if j = j' then w else 0 := by
      intro j w j'
      simp [c, Finsupp.single_apply]
    let ψ : Module.Free.ChooseBasisIndex k E → V →ₗ[k] V := fun j =>
      (Finsupp.lapply j) ∘ₗ c.toLinearMap ∘ₗ (φ.restrictScalars k) ∘ₗ (TensorProduct.mk k E V 1)
    have hψ : ∀ j v, ψ j v = c (φ (1 ⊗ₜ[k] v)) j := fun j v => rfl
    have hψC : ∀ j, ψ j ∈ C := by
      intro j g
      apply LinearMap.ext; intro v
      show c (φ ((1 : E) ⊗ₜ[k] ρ g v)) j = ρ g (c (φ ((1 : E) ⊗ₜ[k] v)) j)
      have h1 : (1 : E) ⊗ₜ[k] ρ g v = repBaseChange E ρ g (1 ⊗ₜ v) := by
        simp [repBaseChange, LinearMap.baseChange_tmul]
      have h2 := congrArg (fun f => f ((1 : E) ⊗ₜ[k] v)) (hφ g)
      simp only [LinearMap.coe_comp, Function.comp_apply] at h2
      rw [h1, h2, hc]
    let bV := Module.finBasis k V
    let S : Finset (Module.Free.ChooseBasisIndex k E) :=
      Finset.univ.biUnion (fun i => (c (φ (1 ⊗ₜ[k] bV i))).support)
    have hS : ∀ j, j ∉ S → ψ j = 0 := by
      intro j hj
      apply bV.ext; intro i
      rw [hψ, LinearMap.zero_apply]
      by_contra h
      apply hj
      simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and, Finsupp.mem_support_iff]
      exact ⟨i, h⟩
    refine ⟨∑ j ∈ S, b j ⊗ₜ[k] (⟨ψ j, hψC j⟩ : C), ?_⟩
    have key : ∀ v, (Φ (∑ j ∈ S, b j ⊗ₜ[k] (⟨ψ j, hψC j⟩ : C))) (1 ⊗ₜ[k] v) =
        ∑ j ∈ S, b j ⊗ₜ[k] ψ j v := by
      intro v
      simp [Φ, commBaseChange, map_sum, LinearMap.sum_apply, LinearMap.baseChange_tmul,
        TensorProduct.smul_tmul']
    apply LinearMap.ext; intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul a v =>
      have hav : a ⊗ₜ[k] v = a • ((1 : E) ⊗ₜ[k] v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hav, map_smul, map_smul, key]
      congr 1
      apply c.injective
      ext j'
      rw [map_sum, Finsupp.finsetSum_apply, ← hψ]
      simp only [hcb]
      rw [Finset.sum_ite_eq']
      split_ifs with hj'
      · rfl
      · rw [hS j' hj', LinearMap.zero_apply]
  exact hmem

/-- **Invariants under extension of coefficients, `≤` (GLUE, proved).**
`dim_E End_G(E ⊗ V) ≤ dim_k End_G(V)` for finite-dimensional `V`. -/
theorem finrank_commOf_baseChange_le (E : Type*) [Field E] [Algebra k E]
    (ρ : Representation k G V) [FiniteDimensional k V] :
    Module.finrank E (commOf (k := E) (fun g => repBaseChange E ρ g)) ≤
      Module.finrank k (commOf (k := k) (fun g => ρ g)) :=
  calc Module.finrank E (commOf (k := E) (fun g => repBaseChange E ρ g))
      ≤ Module.finrank E (LinearMap.range (commBaseChange E ρ)) :=
        Submodule.finrank_mono (commOf_baseChange_le_range E ρ)
    _ ≤ Module.finrank E (TensorProduct k E (commOf (k := k) (fun g => ρ g))) :=
        LinearMap.finrank_range_le _
    _ = Module.finrank k (commOf (k := k) (fun g => ρ g)) := Module.finrank_baseChange

/-- **Scalar commutants stay scalar under extension of coefficients (GLUE, proved).** -/
theorem scalar_commOf_baseChange (E : Type*) [Field E] [Algebra k E]
    (ρ : Representation k G V) [FiniteDimensional k V]
    (hsc : ∀ ψ ∈ commOf (k := k) (fun g => ρ g), ∃ c : k, ψ = c • LinearMap.id) :
    ∀ φ ∈ commOf (k := E) (fun g => repBaseChange E ρ g), ∃ μ : E, φ = μ • LinearMap.id := by
  intro φ hφ
  obtain ⟨t, rfl⟩ := commOf_baseChange_le_range E ρ hφ
  clear hφ
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul e ψ =>
    obtain ⟨c, hc⟩ := hsc ψ ψ.2
    refine ⟨e * algebraMap k E c, ?_⟩
    simp only [commBaseChange, LinearMap.liftBaseChange_tmul, LinearMap.coe_comp,
      Function.comp_apply, Submodule.coe_subtype, LinearMap.baseChangeHom_apply, hc]
    rw [LinearMap.baseChange_smul, LinearMap.baseChange_id]
    apply LinearMap.ext; intro x
    simp [mul_smul, algebraMap_smul]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hy
    exact ⟨a + a', by rw [map_add, ha, ha', add_smul]⟩

/-- **C2, absolute irreducibility (GLUE, proved from `SemisimpleBaseChange`).**
If `r` is a nonzero semisimple representation over a field of characteristic `0` with
`dim End_G(r ⊕ r) ≤ 4`, then `r ⊗ F` is irreducible for every extension `F`, i.e. `r` is
absolutely irreducible. -/
theorem absolutelyIrreducible_of_finrank_commOf_prod_le_four (hSS : SemisimpleBaseChange)
    {k G V : Type} [Field k] [CharZero k] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] (ρ : Representation k G V)
    (hss : ρ.IsSemisimpleRepresentation)
    (h4 : Module.finrank k (commOf (k := k) (fun g => (ρ g).prodMap (ρ g))) ≤ 4)
    (F : Type) [Field F] [Algebra k F] : (repBaseChange F ρ).IsIrreducible := by
  obtain ⟨-, hsc⟩ := isIrreducible_of_finrank_commOf_prod_le_four ρ hss h4
  have : Nontrivial (TensorProduct k F V) := by
    apply Module.nontrivial_of_finrank_pos (R := F)
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos
  exact isIrreducible_of_commutant_scalar _ (hSS k F G V ρ hss)
    (scalar_commOf_baseChange F ρ hsc)


/-- **GLUE (linear algebra; the `Hom` form of invariants under extension, weakened to what E1 uses;
proved below as `equivariantDescent`).** A nonzero `G`-equivariant `E`-linear map
`V ⊗ E → W ⊗ E` forces a nonzero `G`-equivariant `k`-linear map `V → W` (`V`, `W`
finite-dimensional): `Hom_G(V ⊗ E, W ⊗ E) = Hom_G(V, W) ⊗ E`. -/
def EquivariantDescent : Prop :=
  ∀ (k E G V W : Type) [Field k] [Field E] [Algebra k E] [Monoid G] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W),
    (∃ φ : TensorProduct k E V →ₗ[E] TensorProduct k E W, φ ≠ 0 ∧
      ∀ g, φ ∘ₗ repBaseChange E ρ g = repBaseChange E σ g ∘ₗ φ) →
    ∃ ψ : V →ₗ[k] W, ψ ≠ 0 ∧ ∀ g, ψ ∘ₗ ρ g = σ g ∘ₗ ψ

theorem equivariantDescent : EquivariantDescent := by
  intro k E G V W _ _ _ _ _ _ _ _ _ _ ρ σ ⟨φ, h0, h⟩
  exact exists_equivariant_ne_zero_of_baseChange E ρ σ φ h0 h

end GlueI3


/-! pkg-I3's object layer and leaves (§1-§4 of the draft, a verbatim copy of
`scratch/pkg-I3/I3.lean`) are imported from `ZInQKernel.HDecomp.Objects` (§A), whose
QM leaf is `PkgI3.QMDichotomyYu`. -/

/-! ## 5. C2 in the object layer of pkg-I3 -/

namespace PkgI3

open GlueI3 AbVar

lemma equivEnd_eq_commOf {K : Type} [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    equivEnd A ℓ = commOf (k := ℚ_[ℓ]) (fun σ => A.galRep ℓ σ) := rfl

/-- **C2 (GLUE, proved from I3's leaves, `SemisimpleBaseChange`, and A9's output).**
`A` over a number field `K` with `rank_ℤ End_K(A) = 4` (`End⁰_K(A) = B`, from A9, A10, A8/B3);
`E ⊇ ℚ_ℓ` a field and `V_ℓ(A) ⊗ E ≅ r ⊕ r` as `G_K`-representations (from `B ⊗ E ≅ M₂(E)`), with `r`
semisimple (a quotient of `V_ℓ(A) ⊗ E`, semisimple by `FaltingsSemisimple` and
`SemisimpleBaseChange`; derived here). Then `r` is absolutely irreducible: `r ⊗ F` is irreducible
for every field `F ⊇ E`. -/
theorem C2_absolutelyIrreducible (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree)
    (hH : HomFreeFinite)
    (hSS : SemisimpleBaseChange)
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
  have h1 : Module.finrank E (commOf (k := E) (fun σ => repBaseChange E (A.galRep ℓ) σ)) ≤ 4 := by
    have := finrank_commOf_baseChange_le E (A.galRep ℓ)
    rwa [← equivEnd_eq_commOf, finrank_equivEnd hF hT hH, hrank] at this
  have he' : ∀ σ w, e.symm ((r σ).prodMap (r σ) w) = repBaseChange E (A.galRep ℓ) σ (e.symm w) := by
    intro σ w
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have h4 := finrank_commOf_le_of_equiv (fun σ => (r σ).prodMap (r σ)) _ e.symm he'
  replace h4 := h4.trans h1
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
  exact absolutelyIrreducible_of_finrank_commOf_prod_le_four hSS r hr h4 F

/-- **E1, from a common constituent to a nonzero homomorphism (GLUE, proved from I3's leaves and
`SemisimpleBaseChange`).** N5 L861-867: if `V_ℓ(A) ⊗ E` and `V_ℓ(J) ⊗ E` have a common
constituent (a nonzero subrepresentation `U` of the first, equivariantly isomorphic to a
subrepresentation `U'` of the second), then there is a nonzero homomorphism `A → J` over `K`. -/
theorem E1_exists_hom_ne_zero (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree)
    (hSS : SemisimpleBaseChange)
    {K : Type} [Field K] [NumberField K] (A J : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E]
    (U : Subrepresentation (repBaseChange E (A.galRep ℓ)))
    (U' : Subrepresentation (repBaseChange E (J.galRep ℓ))) (hU : U ≠ ⊥)
    (e : U.toSubmodule ≃ₗ[E] U'.toSubmodule)
    (he : ∀ g (u : U.toSubmodule),
      (e ⟨repBaseChange E (A.galRep ℓ) g u, U.apply_mem_toSubmodule g u.2⟩ :
        TensorProduct ℚ_[ℓ] E (J.V ℓ)) = repBaseChange E (J.galRep ℓ) g (e u)) :
    ∃ f : Hom A J, f ≠ 0 := by
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨-, hfinA, -⟩ := hT K A ℓ hℓK
  obtain ⟨-, hfinJ, -⟩ := hT K J ℓ hℓK
  have : FiniteDimensional ℚ_[ℓ] (A.V ℓ) := inferInstance
  have : FiniteDimensional ℚ_[ℓ] (J.V ℓ) := inferInstance
  have hVE := hSS ℚ_[ℓ] E _ _ (A.galRep ℓ) (hS K A ℓ)
  obtain ⟨φ, hφ0, hφ⟩ := exists_equivariant_ne_zero_of_common _ _ hVE U U' hU e he
  obtain ⟨ψ, hψ0, hψ⟩ := equivariantDescent ℚ_[ℓ] E _ _ _ (A.galRep ℓ) (J.galRep ℓ) ⟨φ, hφ0, hφ⟩
  exact exists_hom_ne_zero_of_equivariant hF hT A J ℓ ψ hψ0 hψ

/-! ## glue-ssbc: C2 and E1 with `SemisimpleBaseChange` discharged -/

/-- **C2, unconditional in `SemisimpleBaseChange`.** -/
theorem C2_absolutelyIrreducible' (hS : FaltingsSemisimple) (hF : FaltingsTate)
    (hT : TateModuleFree) (hH : HomFreeFinite)
    {K : Type} [Field K] [NumberField K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (hrank : Module.finrank ℤ (End A) = 4)
    (E : Type) [Field E] [CharZero E] [Algebra ℚ_[ℓ] E]
    {U : Type} [AddCommGroup U] [Module E U] [FiniteDimensional E U] [Nontrivial U]
    (r : Representation E (Field.absoluteGaloisGroup K) U)
    (e : TensorProduct ℚ_[ℓ] E (A.V ℓ) ≃ₗ[E] U × U)
    (he : ∀ σ v, e (repBaseChange E (A.galRep ℓ) σ v) = (r σ).prodMap (r σ) (e v))
    (F : Type) [Field F] [Algebra E F] : (repBaseChange F r).IsIrreducible :=
  C2_absolutelyIrreducible hS hF hT hH semisimpleBaseChange A ℓ hrank E r e he F

/-- **E1, unconditional in `SemisimpleBaseChange`.** -/
theorem E1_exists_hom_ne_zero' (hS : FaltingsSemisimple) (hF : FaltingsTate)
    (hT : TateModuleFree)
    {K : Type} [Field K] [NumberField K] (A J : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E]
    (U : Subrepresentation (repBaseChange E (A.galRep ℓ)))
    (U' : Subrepresentation (repBaseChange E (J.galRep ℓ))) (hU : U ≠ ⊥)
    (e : U.toSubmodule ≃ₗ[E] U'.toSubmodule)
    (he : ∀ g (u : U.toSubmodule),
      (e ⟨repBaseChange E (A.galRep ℓ) g u, U.apply_mem_toSubmodule g u.2⟩ :
        TensorProduct ℚ_[ℓ] E (J.V ℓ)) = repBaseChange E (J.galRep ℓ) g (e u)) :
    ∃ f : Hom A J, f ≠ 0 :=
  E1_exists_hom_ne_zero hS hF hT semisimpleBaseChange A J ℓ E U U' hU e he

end PkgI3

/-- The absolute-irreducibility criterion, unconditional. -/
theorem GlueI3.absolutelyIrreducible_of_finrank_commOf_prod_le_four'
    {k G V : Type} [Field k] [CharZero k] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] (ρ : Representation k G V)
    (hss : ρ.IsSemisimpleRepresentation)
    (h4 : Module.finrank k (GlueI3.commOf (k := k) (fun g => (ρ g).prodMap (ρ g))) ≤ 4)
    (F : Type) [Field F] [Algebra k F] : (GlueI3.repBaseChange F ρ).IsIrreducible :=
  GlueI3.absolutelyIrreducible_of_finrank_commOf_prod_le_four GlueI3.semisimpleBaseChange ρ hss h4 F


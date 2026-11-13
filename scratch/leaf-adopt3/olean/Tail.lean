import HDPrefix

section GlueSSBCSec
/-! ### Copied from `scratch/glue-ssbc/SSBC.lean` (compiled there; imports covered by Mathlib). Inserted by leaf-adopt3 following g0-split's recipe. -/
noncomputable section

namespace GlueSSBC

open Module Representation

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

section Rep

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- Base change `ρ_E` of a representation along a field extension `E/k` (verbatim from
glue-I3-linalg). -/
def repBaseChange (E : Type*) [Field E] [Algebra k E] (ρ : Representation k G V) :
    Representation E G (TensorProduct k E V) where
  toFun g := (ρ g).baseChange E
  map_one' := by
    change (ρ 1).baseChange E = LinearMap.id
    rw [map_one, Module.End.one_eq_id, LinearMap.baseChange_id]
  map_mul' g h := by
    change (ρ (g * h)).baseChange E = (ρ g).baseChange E ∘ₗ (ρ h).baseChange E
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

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

end Rep

/-- glue-I3-linalg's Prop, verbatim (with `repBaseChange` from this file). -/
def SemisimpleBaseChange : Prop :=
  ∀ (k E G V : Type) [Field k] [CharZero k] [Field E] [Algebra k E] [Monoid G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k G V),
    ρ.IsSemisimpleRepresentation → (repBaseChange E ρ).IsSemisimpleRepresentation

theorem semisimpleBaseChange : SemisimpleBaseChange :=
  fun _ E _ _ _ _ _ _ _ _ _ _ ρ hρ => isSemisimpleRepresentation_baseChange E ρ hρ

end GlueSSBC
end
end GlueSSBCSec




noncomputable section

namespace HSyn

open scoped MatrixGroups ModularForm

/-! ## §0. Cheap definitions -/

/-- `ℚ̄`. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(ℚ̄/ℚ)`, with Mathlib's Krull topology. -/
abbrev GQ := Qbar ≃ₐ[ℚ] Qbar

/-- `v` is a place of `ℚ̄` above the prime `p`: a valuation subring of `ℚ̄` in which `p` is not a
unit. (Its restriction to `ℚ` is then `ℤ_(p)`.) -/
def LiesOver (v : ValuationSubring Qbar) (p : ℕ) : Prop := (p : Qbar) ∈ v.nonunits

/-- `σ` is an arithmetic Frobenius at the place `v` above `p`: it stabilizes `v` and acts as
`x ↦ x^p` on its residue field. -/
def IsArithFrob (σ : GQ) (v : ValuationSubring Qbar) (p : ℕ) : Prop :=
  σ ∈ v.decompositionSubgroup ℚ ∧ ∀ x ∈ v, σ x - x ^ p ∈ v.nonunits

/-- A continuous `n`-dimensional representation of `G_ℚ` over `ℚ̄_ℓ` (Mathlib's normed
`PadicAlgCl ℓ`). Continuity for the norm topology is equivalent to the usual notion (the image
lies in `GL_n` of a finite extension of `ℚ_ℓ`), by compactness and Baire. -/
structure GaloisRep (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) where
  toHom : GQ →* GL (Fin n) (PadicAlgCl ℓ)
  continuous_toHom : Continuous toHom

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-- `ρ` is unramified at `p`: every inertia group above `p` acts trivially. -/
def GaloisRep.UnramifiedAt (ρ : GaloisRep ℓ n) (p : ℕ) : Prop :=
  ∀ v : ValuationSubring Qbar, LiesOver v p →
    ∀ σ ∈ v.inertiaSubgroup ℚ, ρ.toHom ((σ : v.decompositionSubgroup ℚ) : GQ) = 1

/-- Every arithmetic Frobenius above `p` has trace `a` (meaningful at unramified `p`). -/
def GaloisRep.FrobTrace (ρ : GaloisRep ℓ n) (p : ℕ) (a : PadicAlgCl ℓ) : Prop :=
  ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
    Matrix.trace (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) = a

/-- `c` is a complex conjugation: it is induced by `z ↦ z̄` through some embedding `ℚ̄ → ℂ`. -/
def IsComplexConj (c : GQ) : Prop :=
  ∃ ι : Qbar →ₐ[ℚ] ℂ, ∀ x, ι (c x) = starRingEnd ℂ (ι x)

/-- `ρ` is odd: `det ρ(c) = −1` for every complex conjugation `c`. -/
def GaloisRep.IsOdd (ρ : GaloisRep ℓ 2) : Prop :=
  ∀ c, IsComplexConj c → Matrix.det (ρ.toHom c : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) = -1

/-- `ρ` is (absolutely) irreducible, in Burnside's form: its image spans `M_n(ℚ̄_ℓ)`. Over the
algebraically closed `ℚ̄_ℓ` this is equivalent to irreducibility. -/
def GaloisRep.IsIrreducible (ρ : GaloisRep ℓ n) : Prop :=
  Algebra.adjoin (PadicAlgCl ℓ)
    (Set.range fun σ => (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) = ⊤

/-- `ρ` is semisimple: every invariant subspace has an invariant complement. -/
def GaloisRep.IsSemisimple (ρ : GaloisRep ℓ n) : Prop :=
  ∀ W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ),
    (∀ σ, W.map (Matrix.toLin' (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) ≤ W) →
    ∃ W', IsCompl W W' ∧
      ∀ σ, W'.map (Matrix.toLin' (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) ≤ W'

/-- Cusp forms of weight `k` on `Γ₁(N)` (Mathlib). -/
abbrev CF (N : ℕ) (k : ℤ) := CuspForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k

/-- The `m`-th q-expansion coefficient `a_m(f)` (period 1). -/
def coeff {N : ℕ} {k : ℤ} (f : CF N k) (m : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 f).coeff m

/-- `f` has nebentypus `χ`: `f|_k γ = χ(d) f` for `γ = (a b; c d) ∈ Γ₀(N)`. -/
def HasNebentypus {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma0 N, (⇑f ∣[k] γ) = χ (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) • ⇑f

/-- `f` is a normalized eigenform of all Hecke operators with nebentypus `χ`, expressed through
its coefficients: `a₁ = 1` and `a_m a_n = Σ_{d ∣ (m,n)} χ(d) d^{k−1} a_{mn/d²}` (with `χ(d) = 0`
for `(d, N) > 1`). For a form with nebentypus `χ` this is equivalent to the Hecke definition
(Diamond–Shurman, Prop. 5.3.1; locator UNVERIFIED). -/
def IsNormalizedEigenform {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  HasNebentypus f χ ∧ coeff f 1 = 1 ∧
    ∀ m n : ℕ, 0 < m → 0 < n →
      coeff f m * coeff f n =
        ∑ d ∈ (Nat.gcd m n).divisors, χ (d : ZMod N) * (d : ℂ) ^ (k - 1) * coeff f (m * n / d ^ 2)

/-- `ρ` is attached to the eigenform `g` (through embeddings `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`): for
`p ∤ Nℓ`, `ρ` is unramified at `p` and its Frobenius trace is `ιL(α)` where `ιC(α) = a_p(g)`. -/
def GaloisRep.AttachedTo (ρ : GaloisRep ℓ 2) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    {N : ℕ} {k : ℤ} (g : CF N k) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
    ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff g p ∧ ρ.FrobTrace p (ιL α)

/-! ## §1. Leaves statable today over the cheap definitions (not proved here; copied from the
hdec-faithful draft). Numbering of the note: T13 Skolem–Noether, T14 HasseBrauerQ, T17
Kronecker–Weber, T18 FrobeniusDense, T19 Brauer–Nesbitt, R14 EigenformRepExists, R15
DeligneSerreConseq, T24 EigenformTwist. -/

/-- **L14. Skolem–Noether** (Reiner, *Maximal orders*, Thm 7.21; Tau Ceti `skolemNoether`).
Exact. -/
def SkolemNoether : Prop :=
  ∀ (K A B : Type) [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] [Ring B] [Algebra K B] [IsSimpleRing B] [FiniteDimensional K B]
    (f g : B →ₐ[K] A), ∃ x : Aˣ, ∀ b, g b = (x : A) * f b * ((x⁻¹ : Aˣ) : A)

/-- **L15(a). Hasse principle for `Br(ℚ)`, in the form used** (Albert–Brauer–Hasse–Noether with
the sum formula; Milne, *Arithmetic duality theorems*, Ch. I). A central simple `ℚ`-algebra that
splits over every `ℚ_p` splits over `ℚ`. Consequence (the real invariant is forced to 0). -/
def HasseBrauerQ : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℚ A] [Algebra.IsCentral ℚ A] [IsSimpleRing A]
    [FiniteDimensional ℚ A] (n : ℕ), Module.finrank ℚ A = n ^ 2 →
    (∀ p : ℕ, ∀ _ : Fact p.Prime,
      Nonempty (TensorProduct ℚ ℚ_[p] A ≃ₐ[ℚ_[p]] Matrix (Fin n) (Fin n) ℚ_[p])) →
    Nonempty (A ≃ₐ[ℚ] Matrix (Fin n) (Fin n) ℚ)

/-- **L17. Kronecker–Weber** (Washington, *Cyclotomic fields*, Thm 14.1; Tau Ceti
`kroneckerWeber`). Exact. -/
def KroneckerWeber : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
    (∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ) →
    ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)

/-- **L18. Chebotarev, in the density form used** (Neukirch VII.13.4; Tau Ceti). Frobenius
elements are dense in `G_ℚ`, avoiding any finite set of primes. Consequence. -/
def FrobeniusDense : Prop :=
  ∀ (U : Subgroup GQ), IsOpen (U : Set GQ) → ∀ (σ : GQ) (S : Finset ℕ),
    ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p ∧ IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U

/-- **L19. Brauer–Nesbitt** (Curtis–Reiner §30). Semisimple representations of a group over a
field of characteristic 0 with equal traces are isomorphic. Exact. -/
def BrauerNesbitt : Prop :=
  ∀ (G : Type) [Group G] (E : Type) [Field E] [CharZero E] (n : ℕ)
    (ρ₁ ρ₂ : G →* GL (Fin n) E),
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ g, Matrix.trace (ρ₁ g : Matrix (Fin n) (Fin n) E) =
      Matrix.trace (ρ₂ g : Matrix (Fin n) (Fin n) E)) →
    ∃ P : GL (Fin n) E, ∀ g, ρ₂ g = P * ρ₁ g * P⁻¹

/-- **L27(a). Galois representations of eigenforms** (Eichler–Shimura `k = 2`, Deligne 1971
`k ≥ 2`, Deligne–Serre 1974 `k = 1`). Consequence (the published statements also give the
determinant). -/
def EigenformRepExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k),
    0 < N → 1 ≤ k → IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g

/-- **L27(b). Deligne–Serre, in the form used** (Ann. Sci. ÉNS 7 (1974), Thm 4.1, with L18 and
L19). A semisimple representation attached to a weight-one eigenform has finite image.
Consequence. -/
def DeligneSerreConseq : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ρ : GaloisRep ℓ 2) (N : ℕ) (χ : DirichletCharacter ℂ N) (g : CF N 1),
    0 < N → IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    (Set.range ρ.toHom).Finite

/-- **L28(a). Twisting an eigenform** (Shimura 1971, Prop. 3.64; Atkin–Li 1978). The twist of a
normalized eigenform of level `N` by a character mod `m` is a normalized eigenform of level
`Nm²` with coefficients `ψ(p) a_p` at `p ∤ Nm`. Consequence. -/
def EigenformTwist : Prop :=
  ∀ (N m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ m) (g : CF N k),
    0 < N → 0 < m → IsNormalizedEigenform g χ →
    ∃ (χ' : DirichletCharacter ℂ (N * m ^ 2)) (g' : CF (N * m ^ 2) k),
      IsNormalizedEigenform g' χ' ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N * m → coeff g' p = ψ (p : ZMod m) * coeff g p


/-! ## §2. Leaves that need definitions Mathlib lacks: placeholders (no content)

Each docstring gives the statement in the form the proof uses, the reference (UNVERIFIED unless
the note says otherwise), and the missing definitions with their cost tier. -/

/-! leaf-adopt (2026-11-12): the placeholders `R01_ShimuraDeligne`, `R02_BabaGranath` and
`R05_GonzalezRotger` are replaced by leaf-qm-fp's concrete field-point statements (section
`LeafQMSec`), with rv-blueprints' repairs Q2, Q4, Q5 (section `LeafAdoptSec`): the bundle uses
`LeafAdopt.R1R2fpRep` (R1(a), (c), (d), R1 at level one, `π₀(X₆) = 1`, R2 with biconditional CM
clauses, R5 on points), `LeafQM.AV.R1rec` (R1(d), object form), `LeafQM.AV.R5fp` (= R5fpStrong,
`LeafAdopt.R5fp_iff_R5fpStrong`) and `LeafQM.AV.R5fpCount`. All of them rest on Lemma P of
rv-qm-polar (type `μ` fixed, characteristic 0, `𝒪` maximal; see `LeafAdopt.R1R2fpRep`;
leaf-adopt2). Part (b) of R1 stays a placeholder: -/

/-- **R1(b). Complex uniformization, in family form** (rv-blueprints Q3; R1an of bp-qmmoduli).
For `Y₃` and `π : Y₃ → P¹` of `LeafAdopt.R1R2fpRep`: (a) for every `P : QML3 ℂ` there is `τ ∈ ℍ`
with `P.A(ℂ) ≅ ℂ²/ι(𝒪)(τ, 1)ᵀ` compatibly with `ι`; (b) for every `τ ∈ ℍ` there are `P_τ : QML3 ℂ`
and such an isomorphism; (c) `τ ↦ π(Φ⁻¹[P_τ]) ∈ P¹(ℂ)` is holomorphic on `ℍ`. The Hauptmodul
comparison of F1 (`PkgI1.QMHauptmodul` against `π`) uses (b) and (c); a statement at each point
separately is too weak. Shimura, Ann. of Math. 85 (1967), Main Thm I; Deligne, Sém. Bourbaki 389
(1971), §4.15 (analytic families) (UNVERIFIED locators). Missing: analytification of `ℂ`-schemes
and of abelian varieties (large; bp-qmmoduli N14). Rests on Lemma P (rv-qm-polar) as R1R2fpRep.
Part (a) at a single point would follow from `ZInQ.LeafPush2.UniformizationExists` (T35) with
T11a (the `ℂ`-linear action of `ι(𝒪)` on the lattice), class number one of `𝒪` (Eichler) and the
QM lattice computation (bp-analytic Q1); that reduction is not carried out. (b) and (c) are the
family statements. -/
opaque R01b_ComplexUniformization : Prop

/-! leaf-adopt2 (2026-11-12): the placeholder `R03_LinYang` is replaced by leaf-push2's
`ZInQ.LeafPush2.R03_LinYang` (section `LeafPush2Sec`): over `ℂ`, every abelian surface with
`𝒪 ↪ End A` is `≅ Jac C` for a curve `C` with a sextic model on the Lin–Yang family at some
`j ≠ 0`, or a product of elliptic curves. A consequence of Lin–Yang Example 29 with Weil's
dichotomy and Lemma P (rv-qm-polar). The `J`/Igusa–Clebsch convention is tied to hdec-elementary's
`OnQMLocus` (`ZInQ.LeafPush2.linYangTuple_onQMLocus`, proved). The `ℚ̄`-form
`R03_LinYang_algClosed` is a glue target (Lefschetz principle). -/



/-! leaf-adopt (2026-11-12): the placeholder `R16_EichlerShimuraJ1` is replaced by
leaf-modcurves' `LeafModCurves.R16_EichlerShimuraJ1'` (section `LeafModCurvesSec`), stated for
every `K_N` model of `X₁(N)` (`IsJ1`), so bp-modcurves' leaf MC9 is not needed (rv-blueprints M1).
Its 2-dimensional constituent of `V_ℓ(J₁(N))` is derived (`LeafModCurves.g13_constituent`, from
the glue target `VSurjOfSurjective`). New textbook leaves from the same file:
`LeafModCurves.JacobianExists ℚ` (T33) and `LeafModCurves.DimJ1Genus` (T34). -/


/-- **R17. Carayol's local–global compatibility** (docstring repaired by rv-loc-leaves, adopted 2026-11-12 by loc-fix; the concrete statement is
`LadicCond.CarayolR17'` of scratch/def-ladic-cond, unchanged). For a weight-2 newform of level `N`,
any prime `ℓ` (including `ℓ = 2`) and any prime `p ≠ ℓ` (including `p ∣ N`), the Artin conductor
exponent of `ρ_{f,λ}|G_{ℚ_p}` is `v_p(N)`. Ann. Sci. ÉNS 19 (1986), Théorème (A), pp. 409-411,
§0.8 p. 411 (coverage of `p ∣ N` and `ℓ = 2` YES per the audit; the extra discrete-series
hypothesis concerns only totally real `F` of even degree, not `ℚ`), with the newform conductor
`a(π_p) = v_p(N)` (Casselman 1973; UNVERIFIED locator). Duals and unramified twists do not change
the conductor. Do not replace by Théorème (B) or by the `Γ₀` elliptic-curve corollary. -/
opaque R17_Carayol : Prop

/-! leaf-adopt2 (2026-11-12): the placeholder `R18_Javanpeykar` is replaced by leaf-push2's
`ZInQ.LeafPush2.R18_Javanpeykar` (section `LeafPush2Sec`): over a number field `K`, for a pointed
curve `X` with Jacobian `J` (`IsJacobian`), `g = dim J ≥ 1` and a Belyi function `t ∈ K(X)` of
degree `d > 0`, `stableFaltingsHeight J ≤ 13·10⁶ · g · d⁵` (in `EReal`). A consequence of ANT 8
(2014) Thm 1.1.1 with H5. Its height is leaf-push2's copy of def-faltings' height over
`PkgI3.AbVar`. -/

/-! leaf-adopt (2026-11-12): the placeholders `R19_GaudronRemond`, `R20_FaltingsHeightLemma`,
`R21_Bost` are replaced by def-faltings' `ZInQ.DefFaltings.R19_GaudronRemond`,
`R20_FaltingsLemma5`, `R21_Bost` over `stableFaltingsHeight` (section `DefFaltingsSec`), with H5
as an explicit leaf `LeafAdopt.H5` (rv-blueprints F2). **Not yet known to be non-vacuous**: the
three Props `AnalyticUniformizationExists`, `AnalyticUniformizationUnique`,
`HodgeLatticeTheorem` (node AN3 and the Hodge lattice) are open, and until they are proved the
index set of the infimum may be empty (`h = ⊤`): then R21 holds trivially and R19, R20 have no
instance. R19 is normalization-sensitive (a consequence only if Gaudron–Rémond's `h` is Faltings'
original normalization, rv-blueprints F4). -/


/-! leaf-adopt2 (2026-11-12): the placeholder `R22_Pazuki` is replaced by leaf-push2's
`ZInQ.LeafPush2.R22_Pazuki` (section `LeafPush2Sec`): the audit's upper half
`h([θ_m(0, Ω)]) ≤ X/2 + C₂ log(X + 2)` for `X ≥ max(1, h_F + log π)`, for every abelian surface
over a number field, every analytic uniformization at every complex place and every `Ω ∈ 𝔥₂`
that is a period matrix of its lattice (all principal polarizations, no polarization object).
Consequence of Bull. SMF 140 (2012) Cor. 1.3(2) with H5; the identification of Pazuki's level-2
coordinates (Def. 2.6) with `θ[a;b](0, Ω)` is UNVERIFIED (the main risk). The glue form with
`X = max(1, h_F + 3)` is `ZInQ.LeafPush2.R22_plus3` (proved). -/


/-- **T10. `V_ℓ(A) ≅ H¹_et(A_K̄, ℚ_ℓ)^∨`**, Galois-equivariantly (Milne in Cornell–Silverman 1986,
Thm 15.1(a), UNVERIFIED). Missing: ℓ-adic étale cohomology (large). -/
opaque T10_TateDuality : Prop

/-! leaf-adopt2 (2026-11-12): the placeholders `T11_RiemannGAGA` and `T12_ArtinComparison` are
removed. T11 is now the two concrete textbook leaves `ZInQ.LeafPush2.T11a_RiemannEnd`
(endomorphisms of `A/ℂ` = `ℂ`-linear maps preserving the lattice of a uniformization) and
`ZInQ.LeafPush2.T11b_Rigidity` (`Hom(A_L, B_L) = Hom(A, B)` over `k = k̄` of characteristic 0).
T12 is glue: its used form `ZInQ.LeafPush2.T12_ComplexConjEigen` (the `±1`-eigenspaces of complex
conjugation on `V_ℓ(A)` have dimension `dim A`) is a glue target from T35, T5, T26 and the
antiholomorphy of complex conjugation. The new textbook leaf T35 is
`ZInQ.LeafPush2.UniformizationExists` (AN3 for abelian varieties: Mumford §1 with GAGA); it is
kept instead of bp-analytic's `UniformizationLeaf` (docs/research/leaf-adopt2.md §2): its
predicate is the one R22 and T11a quantify over, it ties `g` to `dim A`, and it covers every
`K` with `σ : K → ℂ`. -/




/-! hsyn-fold: R8, T9, T23, T29 and T32 are no longer placeholders. Their concrete statements
(task leaf-push) are `PkgI2.GrothendieckMonodromy` (= `LeafPush.R08_GrothendieckMonodromy`,
consequence form), `LeafPush.T09_WeilPairing` (consequence, polarization hidden),
`PkgI4.T23_FontaineClosure` (exact, matrix form, `ℚ_p` coefficients),
`LeafPush.T29a_DivisionNormalizer` and `LeafPush.T29b_SplitNormalizer` (exact),
`LeafPush.T32a_TameQuadratic` and `LeafPush.T32b_QuadraticRamification` (consequences).
leaf-adopt (2026-11-12): T32 is now glue, proved (`HSyn.t32a_glue`, `HSyn.t32b_glue`, §3).
leaf-adopt2 (2026-11-12): T12 is now glue (target `ZInQ.LeafPush2.T12_ComplexConjEigen`,
unproved). -/

/-! ## §3. Glue -/

/-- **T32(a) is glue** (leaf-adopt, 2026-11-12): proved in scratch/glue-t32a (`GlueB3Unram.t32a`,
copied in section `GlueT32aSec`), with no leaf. -/
theorem t32a_glue : LeafPush.T32a_TameQuadratic := GlueB3Unram.t32a

/-- **T32(b) is glue** (leaf-adopt, 2026-11-12): proved in scratch/glue-b3b (`GlueB3Unram.t32b`,
copied with scratch/glue-t32a in section `GlueT32aSec`), with no leaf. -/
theorem t32b_glue : LeafPush.T32b_QuadraticRamification := GlueB3Unram.t32b

/-- **The two complex-conjugation predicates agree** (leaf-adopt2): leaf-push2's
`ZInQ.LeafPush2.IsComplexConj` (used by `T12_ComplexConjEigen`) is pkg-I4's
`PkgI4.IsComplexConj` (used by the oddness of `GaloisRep`s, G10), by definition. -/
theorem isComplexConj_leafPush2_iff (c : Field.absoluteGaloisGroup ℚ) :
    ZInQ.LeafPush2.IsComplexConj c ↔ PkgI4.IsComplexConj c :=
  Iff.rfl

/-- **Glue target (leaf-adopt2, unproved): the two copies of the stable Faltings height agree.**
R18 and R22 (leaf-push2) are stated over `ZInQ.LeafPush2.stableFaltingsHeight` on `PkgI3.AbVar`;
R19-R21 and H5 (def-faltings) over `ZInQ.DefFaltings.stableFaltingsHeight` on def-faltings' copy
of the structure. The two definitions are textual copies (leaf-push2 Part I = def-faltings §§1-18
with `AbVar` replaced), so this is pure transport along `LeafAdopt.abVarEquiv` (every structure of
the Arakelov layer is duplicated, so the proof needs an equivalence of `GroupModel`, `HodgeData`
and `MetrizedModel` and equality of model heights). It is what lets the glue apply H5 to R18 and
R22. Not a leaf. -/
def HeightCopiesAgree : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K),
    ZInQ.LeafPush2.stableFaltingsHeight A =
      ZInQ.DefFaltings.stableFaltingsHeight ((LeafAdopt.abVarEquiv K).symm A)

/-- **B3(v) with no leaf** (glue-t32a): `LeafB3a` of glue-b3-unram is proved. -/
theorem leafB3a_glue : GlueB3Unram.LeafB3a := GlueB3Unram.leafB3a

/-- **G12, weight arithmetic** (N5 L763-764, Tate normalization; from the hdec-faithful draft). -/
theorem weight_match (n k : ℤ) (hk : 1 ≤ k)
    (h : (n = 0 ∧ n + 1 - k = -1) ∨ (n = -1 ∧ n + 1 - k = 0)) : n = 0 ∧ k = 2 := by
  omega

/-- **G15 (D3), pkg-I6's `sq_principalUnits` proved** from glue-conductor's
`exists_sq_eq_one_add` (same statement as `PkgI6.sq_principalUnits`, which is `sorry` there). -/
theorem sq_principalUnits_proved (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B] (e : ℕ) (_he1 : 1 ≤ e)
    (he : Ideal.span {(2 : B)} = IsLocalRing.maximalIdeal B ^ e) (r : ℕ) (hr : e < r)
    (y : B) (hy : y ∈ IsLocalRing.maximalIdeal B ^ (r + e)) :
    ∃ x ∈ IsLocalRing.maximalIdeal B ^ r, (1 + x) ^ 2 = 1 + y := by
  obtain ⟨w, hw, h⟩ := GlueConductor.exists_sq_eq_one_add e (r - e) (by omega) he y
    (by rwa [show 2 * e + (r - e) = r + e by omega])
  exact ⟨w, by rwa [show e + (r - e) = r by omega] at hw, h⟩

/-- **D3 (GLUE, proved)**: pkg-I6's `sq_principalUnits`, from glue-conductor's Hensel argument. -/
theorem _root_.PkgI6.sq_principalUnits (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B] (e : ℕ) (he1 : 1 ≤ e)
    (he : Ideal.span {(2 : B)} = IsLocalRing.maximalIdeal B ^ e) (r : ℕ) (hr : e < r)
    (y : B) (hy : y ∈ IsLocalRing.maximalIdeal B ^ (r + e)) :
    ∃ x ∈ IsLocalRing.maximalIdeal B ^ r, (1 + x) ^ 2 = 1 + y :=
  sq_principalUnits_proved B e he1 he r hr y hy


end HSyn

end


noncomputable section

namespace HSyn

open scoped MatrixGroups ModularForm

/-- **The research-level leaves of route P** (note §2.1), bundled. Placeholders are
uninterpreted. Genuine statements: `R4` (pkg-I1), `R6`, `R7` (pkg-I2), `R9` (pkg-I3), `R10`,
`R11`+`R12`, `R13` (pkg-I4), `R14`, `R15` (§1 here); leaf-adopt (2026-11-12): R1 (a, c, d),
R2, R5 (leaf-qm-fp, repaired), R16 (leaf-modcurves), R19-R21 and H5 (def-faltings);
leaf-adopt2 (2026-11-12): R3, R18, R22 (leaf-push2). Remaining placeholders: R1(b), R17. -/
structure ResearchLeaves : Prop where
  /-- R1 (a), (c), (d), `π₀(X₆) = 1` (rv-blueprints Q4), R1 at level one, R2 with biconditional CM
  clauses (Q5) and R5 on points of `X₆`, on one `Y₃`, `X₆` (leaf-qm-fp, repaired by leaf-adopt).
  Premise Lemma P of rv-qm-polar (type-`μ` polarization exists and is unique), see the definition. -/
  r1r2 : LeafAdopt.R1R2fpRep
  /-- R1(b), complex uniformization in family form (Q3): still a placeholder. -/
  r1an : R01b_ComplexUniformization
  /-- R1(d), Shimura reciprocity, object form (leaf-qm-fp; premise Lemma P, rv-qm-polar). -/
  r1rec : LeafQM.AV.R1rec
  /-- R3, Lin–Yang over `ℂ`, existential and polarization-free (leaf-push2; premise Lemma P). -/
  r3 : ZInQ.LeafPush2.R03_LinYang
  r4 : PkgI1.ThetaModularity
  /-- R5(ii), González–Rotger Thm 5.12, fields of moduli (= rv-blueprints' R5fpStrong, Q2;
  premise Lemma P, rv-qm-polar). -/
  r5 : LeafQM.AV.R5fp
  /-- R5(i), González–Rotger Prop. 5.6, `#CM(R) = 2^b h(R)` (premise Lemma P, rv-qm-polar). -/
  r5count : LeafQM.AV.R5fpCount
  r6 : PkgI2.RaynaudCriterion.{0}
  r7a : PkgI2.NeronOggShafarevich.{0}
  r7b : PkgI2.SerreTatePotentialGood.{0}
  r8 : PkgI2.GrothendieckMonodromy.{0}
  r9a : PkgI3.FaltingsSemisimple
  r9b : PkgI3.FaltingsTate
  r10 : PkgI4.DeRhamComparison
  /-- R11 (Berger) and R12 (Pan) enter through their joint consequence: Pan's theorem with "de Rham
  at `p`" in place of "potentially semistable at `p`" (pkg-I4). `B_st` is not needed by the glue.
  Both theorems remain separate leaves in the count. -/
  r11r12 : PkgI4.PanBerger
  r13 : PkgI4.EigenformHT
  r14 : EigenformRepExists
  r15 : DeligneSerreConseq
  /-- R16, Eichler–Shimura in `J₁(N)`, existential form for every `K_N` model (leaf-modcurves). -/
  r16 : LeafModCurves.R16_EichlerShimuraJ1'
  r17 : R17_Carayol
  /-- R18, Javanpeykar, over leaf-push2's stable Faltings height on `PkgI3.AbVar` (with H5). -/
  r18 : ZInQ.LeafPush2.R18_Javanpeykar
  /-- R19-R21 over def-faltings' `stableFaltingsHeight` (not yet known non-vacuous: AN3 open). -/
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
  r20 : ZInQ.DefFaltings.R20_FaltingsLemma5
  r21 : ZInQ.DefFaltings.R21_Bost
  /-- R22, Pazuki's upper half, over all uniformizations and period matrices (leaf-push2). -/
  r22 : ZInQ.LeafPush2.R22_Pazuki
  /-- H5 (rv-blueprints F2): the stable height is finite and attained by Néron models. -/
  h5 : LeafAdopt.H5

/-- **The textbook foundations** (note §2.2), bundled. -/
structure TextbookLeaves : Prop where
  t1 : PkgI2.PurityBranchLocus.{0}
  t2 : PkgI2.AbhyankarDVR.{0}
  t3 : PkgI2.NeronMappingAbelianScheme.{0}
  t4 : PkgI2.ReductionTorsionBijective.{0}
  t5 : PkgI2.TorsionStructure.{0}
  t6 : PkgI3.HomFreeFinite
  t7 : PkgI3.CharPolyIndepOfEll
  t8 : PkgI3.PoincareReducibility
  t9 : LeafPush.T09_WeilPairing.{0}
  t10 : T10_TateDuality
  /-- T11(a), Riemann/GAGA for endomorphisms (leaf-push2). -/
  t11a : ZInQ.LeafPush2.T11a_RiemannEnd
  /-- T11(b), rigidity of homomorphisms under extension of an algebraically closed field
  (leaf-push2). -/
  t11b : ZInQ.LeafPush2.T11b_Rigidity
  -- leaf-adopt2: T12 is glue (`ZInQ.LeafPush2.T12_ComplexConjEigen`, a target), no longer a field.
  t13 : SkolemNoether
  -- hsyn-fix: the cochain forms I6.2a′-c′ (rv-leaves-b repair 3; Mathlib does not yet compare
  -- `continuousCohomology` with inhomogeneous cochains). `PkgI6.BrauerHasse2` etc. remain in the file.
  t14a : PkgI6.BrauerHasse2C
  t14b : PkgI6.BrauerReciprocity2C
  t15 : PkgI6.LocalH2CardC
  t16a : ∀ (p : ℕ) [Fact p.Prime], PkgI6.LocalKroneckerWeber p
  t16b : PkgI6.LocalReciprocityUpper
  t17 : KroneckerWeber
  t18 : FrobeniusDense
  t19 : BrauerNesbitt
  t20 : GlueConductor.HilbertDifferentFormula
  t21 : GlueConductor.SerreDifferentBound
  t22a : PkgI6.HerbrandQuotient
  t22b : PkgI6.HerbrandTransitivity
  t23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p
  t24 : EigenformTwist
  t25 : PkgI4.NewformOfEigenform
  t26 : PkgI3.TateModuleFree
  t27 : PkgI3.QMDichotomyYu
  t28 : PkgI1.IgusaClebschSeparation
  t29a : ∀ (p : ℕ) [Fact p.Prime], LeafPush.T29a_DivisionNormalizer p
  t29b : ∀ (p : ℕ) [Fact p.Prime], LeafPush.T29b_SplitNormalizer p
  t30 : GlueDescent.B2Q.LeafSqrtCrit
  t31 : GlueDescent.B2Q.LeafUnramified
  -- leaf-adopt: T32 is glue (`HSyn.t32a_glue`, `HSyn.t32b_glue`), no longer a field.
  /-- T33 (new, leaf-modcurves): existence of the Jacobian of a pointed curve (Weil; Milne 1986). -/
  t33 : LeafModCurves.JacobianExists ℚ
  /-- T34 (new, leaf-modcurves): `dim J₁(N)` is the genus of `Γ₁(N)` (Shimura 1971 Prop. 1.40 with
  §6.7 and `dim Jac = genus`). -/
  t34 : LeafModCurves.DimJ1Genus
  /-- T35 (new, leaf-push2): analytic uniformization of `A(ℂ)_σ` by `ℂ^{dim A}` with a full
  lattice (Mumford §1 with GAGA; AN3 for abelian varieties). -/
  t35 : ZInQ.LeafPush2.UniformizationExists


/-! ## §3′. g0-split: the glue G1-G17, G19 split into named pieces (task g0-split, 2026-11-12;
folded into this file by leaf-adopt3, 2026-11-13, following g0-split's recipe, doc §4)

`GlueAssembly.GlueOutputs Mult.S_mul` asks, for each `u ∉ 𝒞`, for a number field `K'`, a point
`z ∈ K'¹⁰`, a real `h_A`, and

* (o1) `Φ(z) = J(u)` (step F1, glue G19),
* (o2) Pazuki's bound `h(z) ≤ …(h_A)` (step F3, glue G19, leaf R22),
* (o3) `NonCMOutput Q M h_A`: a level `N` with `1 ≤ N ≤ QM²` (G13-G16), `h_F(J₁(N)) ≤ 1.3·10⁷N¹²`
  (G18/E2, leaf R18), `2 ≤ g ≤ N²` (G17 for `2 ≤ g`; E2 for `g ≤ N²`, proved from T34),
  `1 ≤ d = [L':ℚ] ≤ QM` (G7, B3), Gaudron-Rémond's `log deg φ` (E3, R19, on the isogeny of G17),
  Faltings' variation with additivity (E4, R20 + additivity) and Bost (R21); or the CM branch,
  which the route does not use (G6, NoCM).

Below, `h_A` is the stable Faltings height (def-faltings) of an abelian surface `A` over a number
field `L'` attached to `u` (`FibreOver`). Proved pieces applied: A4 (`exists_fibre_object`,
leaf-qm-fp), `model_dim`, H5's finiteness, E1 (`PkgI3.E1_exists_hom_ne_zero` with glue-ssbc's
`SemisimpleBaseChange`, copied in section `GlueSSBCSec`), T8 (Poincaré, a leaf), E2's
`dim J₁(N) ≤ N²` (`LeafModCurves.dim_J1_le`, from T34), `javanpeykarJ1` (from leaf-push2's
concrete R18), `thetaPazuki` (from leaf-push2's concrete R22) and the E3-E4 numerics
(`transfer_core`, from R19, R20, R21), `isogenousProduct`. leaf-adopt3: R18 and R22 are now the bundle
fields `r.r18`, `r.r22` (leaf-push2's statements over `ZInQ.LeafPush2.stableFaltingsHeight`);
g0-split's transported forms `R18_JavanpeykarConcrete`, `R22_PazukiConcrete` (over def-faltings'
height) are derived from them with the glue piece `HSyn.HeightCopiesAgree` (leaf-adopt2's glue
target, pure transport between the two textual copies of the height): `r18Concrete_of`,
`r22Concrete_of`. g0-split's copies of leaf-push2's R22 definitions and of `ffAlgebra`,
`javanpeykarBound` are replaced by the `ZInQ.LeafPush2` originals (identical text). The ten
missing glue pieces, smallest first (sizes SPECULATIVE), and `HeightCopiesAgree` form the bundle
`HSyn.GluePieces`:
1. `DimFinite` (an abelian variety has finite dimension),
2. `DimBaseChange` (dimension invariant under field extension),
3. `X1BelyiOnModel` (`BelyiX1` on the model of `IsJ1`),
4. `FibreSimple` (G5-G6 on `A`),
5. `HeightAdditivity` (E4),
6. `StableHeightBaseChange` (stable height invariant under base change),
7. `ProductExists` (G17: `A × Z` is an abelian variety),
8. `ReverseIsogeny` (G17: the isogeny `J → A × Z`),
9. `ThetaPointOfFibre` (G19, F1 on `A`),
10. `ModularConstituent` (G2, G4, G7-G16).
`glueOutputs_of_leaves` takes them as the bundle `HSyn.GluePieces`. -/

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

/-- `A`, an abelian variety over the number field `K` (def-faltings' `AbVar`), is (up to
isomorphism of `ℚ̄`-schemes, after some embedding `K → ℚ̄`) the abelian surface of an object
`(A, ι, η)` of `Y₃` at a `ℚ̄`-point `y` of `Y₃` lying over `J(u)` (for the moduli data
`(Y, Φ, π)` that R1-R2 provide). -/
def FibreOver (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K) : Prop :=
  ∃ (emb : K.K →+* Qbar) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P ∧ π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) ∧
    (letI : Algebra K.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X))

/-- `P ≅ A × Z` as group schemes: homomorphisms `p₁ : P → A`, `p₂ : P → Z` with
`(p₁, p₂) : P → A × Z` an isomorphism. -/
def IsProductOf {K : Type} [Field K] (P A Z : Over (Spec (CommRingCat.of K))) [MonObj P]
    [MonObj A] [MonObj Z] : Prop :=
  ∃ (p₁ : P ⟶ A) (p₂ : P ⟶ Z), IsMonHom p₁ ∧ IsMonHom p₂ ∧ IsIso (lift p₁ p₂)

/-- The hypotheses of E1 (`PkgI3.E1_exists_hom_ne_zero`): for some prime `ℓ` and field `E ⊇ ℚ_ℓ`,
`V_ℓ(A) ⊗ E` and `V_ℓ(J) ⊗ E` have a common nonzero constituent, as `G_K`-representations. -/
def CommonConstituent {K : Type} [Field K] [NumberField K] (A J : PkgI3.AbVar K) : Prop :=
  ∃ (ℓ : ℕ) (_ : Fact ℓ.Prime) (E : Type) (_ : Field E) (_ : Algebra ℚ_[ℓ] E)
    (U : Subrepresentation (GlueI3.repBaseChange E (A.galRep ℓ)))
    (U' : Subrepresentation (GlueI3.repBaseChange E (J.galRep ℓ)))
    (e : U.toSubmodule ≃ₗ[E] U'.toSubmodule), U ≠ ⊥ ∧
    ∀ g (u : U.toSubmodule),
      (e ⟨GlueI3.repBaseChange E (A.galRep ℓ) g u, U.apply_mem_toSubmodule g u.2⟩ :
        TensorProduct ℚ_[ℓ] E (J.V ℓ)) = GlueI3.repBaseChange E (J.galRep ℓ) g (e u)

/-! ### The missing pieces, smallest first -/

/-- **Missing piece 2 (definition-level glue; used by G18/E2 and G17).** The dimension of an
abelian variety is invariant under extension of the base field (Stacks, Tag 00P4 for finitely
generated algebras over a field; STANDARD). -/
def DimBaseChange : Prop :=
  ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A : ZInQ.DefFaltings.AbVar K),
    (A.baseChange L).dim = A.dim

/-- **Missing piece 6 (definition-level glue; used by E3-E4).** The *stable* Faltings
height is invariant under finite extension of the number field (Faltings 1983 §1; Deligne,
Sém. Bourbaki 616). For def-faltings' infimum this needs semistable reduction and the Néron
models of H5 (`NeronModelMinimal`); it is a property of the definition, not a literature leaf. -/
def StableHeightBaseChange : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    (A : ZInQ.DefFaltings.AbVar K),
    stableFaltingsHeight (A.baseChange L) = stableFaltingsHeight A

/-- **R18 (Javanpeykar, ANT 8 (2014), Thm 1.1.1), transported: leaf-push2's `R18_Javanpeykar`**
(`ResearchLeaves.r18`) on this file's copies (`LeafModCurves.IsCurve`, `IsJacobian`,
`IsBelyiFunction` are textual copies of leaf-push2's; the height is def-faltings'
`stableFaltingsHeight` through `LeafAdopt.abVarEquiv`). leaf-adopt3: no longer a hypothesis; it is
derived (`r18Concrete_of`) from `r.r18` and the glue piece `HSyn.HeightCopiesAgree`. -/
def R18_JavanpeykarConcrete : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : Over (Spec (CommRingCat.of K)))
    [LeafModCurves.IsCurve X] [IsIntegral X.left] (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X)
    (J : PkgI3.AbVar K) (aj : X ⟶ J.X), LeafModCurves.IsJacobian X P₀ J aj →
    ∀ g : ℕ, J.dim = (g : WithBot ℕ∞) → 1 ≤ g →
    ∀ t : X.left.functionField,
      letI := ZInQ.LeafPush2.ffAlgebra X
      LeafModCurves.IsBelyiFunction K X.left.functionField t →
      ∀ d : ℕ, Module.finrank (IntermediateField.adjoin K {t}) X.left.functionField = d → 0 < d →
        stableFaltingsHeight ((LeafAdopt.abVarEquiv K).symm J) ≤ ((ZInQ.LeafPush2.javanpeykarBound g d : ℝ) : EReal)

/-- **Missing piece 3 (glue E2, Belyi half: `LeafModCurves.BelyiX1` on the model of `IsJ1`).**
Every `J₁(N)` over `ℚ` (`IsJ1 N J`) is the Jacobian of a pointed curve `X` whose function field
carries a Belyi function `t` (`j/1728`) of degree `[ℚ(X) : ℚ(t)] ≤ N²`. From `BelyiX1` (a glue
target of leaf-modcurves: good reduction of `E_j` away from `j = 0, 1728, ∞`, and
`[K_N : ℚ(j)] ≤ N²`) by transport along `ℚ(X) ≅ K_N` (`IsX1Model`); the transport is not done
here. -/
def X1BelyiOnModel : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ J : PkgI3.AbVar ℚ, LeafModCurves.IsJ1 N J →
    ∃ (X : Over (Spec (CommRingCat.of ℚ))) (_ : LeafModCurves.IsCurve X) (_ : IsIntegral X.left)
      (P₀ : 𝟙_ (Over (Spec (CommRingCat.of ℚ))) ⟶ X) (aj : X ⟶ J.X),
      LeafModCurves.IsJacobian X P₀ J aj ∧ ∃ t : X.left.functionField,
        (letI := ZInQ.LeafPush2.ffAlgebra X; LeafModCurves.IsBelyiFunction ℚ X.left.functionField t) ∧
        ∃ d : ℕ,
          (letI := ZInQ.LeafPush2.ffAlgebra X
           Module.finrank (IntermediateField.adjoin ℚ {t}) X.left.functionField = d) ∧
          0 < d ∧ d ≤ N ^ 2

/-- **G18/E2: R18 applied to `X₁(N)` (proved below, `javanpeykarJ1`, from
`R18_JavanpeykarConcrete`, `X1BelyiOnModel` and T34).** For every `N ≥ 1` and every `J₁(N)` of
positive dimension over `ℚ`, `h_F(J₁(N)) ≤ 1.3·10⁷N¹²`. -/
def JavanpeykarJ1 : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ J : PkgI3.AbVar ℚ, LeafModCurves.IsJ1 N J →
    ∀ g : ℕ, J.dim = (g : WithBot ℕ∞) → 1 ≤ g →
    ∀ x : ℝ, stableFaltingsHeight ((LeafAdopt.abVarEquiv ℚ).symm J) = x →
      x ≤ 13000000 * (N : ℝ) ^ 12

/-- **Missing piece 5 (glue E4, the additivity half that the transfer uses).**
`h_F(A) + h_F(Z) ≤ h_F(A × Z)` for abelian varieties over a number field (equality holds;
Faltings 1983 §1; needs Néron models and H5, rv-blueprints F1). -/
def HeightAdditivity : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (P A Z : ZInQ.DefFaltings.AbVar L),
    IsProductOf P.X A.X Z.X → ∀ a z p : ℝ, stableFaltingsHeight A = a →
      stableFaltingsHeight Z = z → stableFaltingsHeight P = p → a + z ≤ p

/-- **Missing piece 1 (definition-level glue).** An abelian variety has finite dimension: its
Krull dimension is a natural number (a scheme of finite type over a field; STANDARD). -/
def DimFinite : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K), ∃ n : ℕ, A.dim = (n : WithBot ℕ∞)

/-- **Missing piece 7 (definition-level glue; G17).** The product `A × Z` of abelian varieties is an
abelian variety `P` (proper, smooth, geometrically integral group scheme), with
`dim P = dim A + dim Z` (Mumford §4; STANDARD; geometric integrality of products is not in
Mathlib). -/
def ProductExists : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A Z : PkgI3.AbVar L),
    ∃ P : ZInQ.DefFaltings.AbVar L, IsProductOf P.X A.X Z.X ∧ P.dim = A.dim + Z.dim

/-- **Missing piece 8 (glue G17, after Poincaré).** If `(f, g) : A × Z → J` is finite and surjective
(T8's output) and `P ≅ A × Z`, there is an isogeny `J → P` in the other direction, and
`dim J = dim P` (Mumford §8, Thm 4 / Remark, UNVERIFIED: an isogeny of degree `n` has a
quasi-inverse `ψ` with `φψ = [n]`). Needs finite group schemes and quotients, not in Mathlib. -/
def ReverseIsogeny : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A J Z : PkgI3.AbVar L) (P : ZInQ.DefFaltings.AbVar L)
    (f : PkgI3.AbVar.Hom A J) (g : PkgI3.AbVar.Hom Z J), IsProductOf P.X A.X Z.X →
    PkgI3.AbVar.IsIsogenyMor (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom) →
    ∃ φ : ((LeafAdopt.abVarEquiv L).symm J).X ⟶ P.X, ZInQ.DefFaltings.IsIsogeny φ ∧ J.dim = P.dim

/-- **G17 after Poincaré (proved below, `isogenousProduct`, from `DimFinite`, `ProductExists`,
`ReverseIsogeny`).** From T8's isogeny `(f, g) : A × Z → J` to Gaudron-Rémond's input: `P ≅ A × Z`,
an isogeny `J → P`, and `dim J = dim A + dim Z`. -/
def IsogenousProduct : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A J Z : PkgI3.AbVar L) (f : PkgI3.AbVar.Hom A J)
    (g : PkgI3.AbVar.Hom Z J),
    PkgI3.AbVar.IsIsogenyMor (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom) →
    ∃ (P : ZInQ.DefFaltings.AbVar L) (φ : ((LeafAdopt.abVarEquiv L).symm J).X ⟶ P.X),
      ZInQ.DefFaltings.IsIsogeny φ ∧ IsProductOf P.X A.X Z.X ∧
      ∀ a n : ℕ, A.dim = a → J.dim = n → ∃ m : ℕ, Z.dim = m ∧ a + m = n

/-- **Missing piece 4 (glue G5-G6 on the actual `A`: QM dichotomy and NoCM).** For `u ∉ 𝒞`, the
fibre surface `A` (any number-field model of it) is simple over its field: every nonzero
endomorphism is an isogeny (because `End⁰(A_ℚ̄) = B` is a division algebra). Proved parts: T27 at
`B = (2,-3)` (`PkgI3.qmDichotomy_B6`), the Elkies identities and the free `W`-orbit
(`GlueRepo.PR.fibre_free`), `cm_of_val`. Missing: the instantiation on `A` and the counting with
R5 (h-decomposition G6). -/
def FibreSimple : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
      PkgI3.EndDivision (LeafAdopt.abVarEquiv K.K A)

/-- **R22 (Pazuki, Bull. SMF 140 (2012), Cor. 1.3(2)), transported: leaf-push2's `R22_Pazuki`**
(`ResearchLeaves.r22`; same statement, the height is def-faltings' `stableFaltingsHeight` through
`LeafAdopt.abVarEquiv`). leaf-adopt3: no longer a hypothesis; it is derived (`r22Concrete_of`)
from `r.r22` and the glue piece `HSyn.HeightCopiesAgree`. -/
def R22_PazukiConcrete : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K), A.dim = (2 : WithBot ℕ∞) →
    ∀ x : ℝ, stableFaltingsHeight ((LeafAdopt.abVarEquiv K).symm A) = x →
    ∀ X : ℝ, max 1 (x + Real.log Real.pi) ≤ X →
    ∀ (σ : K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φ : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts A σ),
      ZInQ.LeafPush2.IsUniformization σ Λ Φ →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, ZInQ.LeafPush2.IsSiegel Ω → ZInQ.LeafPush2.IsPeriodMatrix Λ Ω →
    ∀ (L : Type) [Field L] [NumberField L] (emb : L →+* ℂ) (z : ZInQ.LeafPush2.Char2 → L) (c : ℂ), c ≠ 0 →
      (∀ m, emb (z m) = c * ZInQ.LeafPush2.thetaConst Ω m) →
      ZInQ.LeafPush2.absLogHeight z ≤ X / 2 + ZInQ.LeafPush2.pazukiC2 * Real.log (X + 2)

/-- **Missing piece 9 (glue G19, F1 on the actual `A`).** For `u ∉ 𝒞` and the fibre surface `A`
over `J(u)` (any number-field model): at some complex place `σ` there are an analytic
uniformization `Φ` of `A(ℂ)_σ` with kernel `Λ`, a period matrix `Ω ∈ 𝔥₂` of `Λ` (for the principal
polarization), and an algebraic representative `z ∈ L¹⁶` of the theta-null point `[θ_m(0, Ω)]`;
and its ten even coordinates `z'` (in a number field `K'`) satisfy `Φ(z') = J(u)` with
`h(z') ≤ h(z)` (the six odd theta nulls vanish). F1: Lin-Yang's Igusa invariants on the QM locus
(R3) with the theta expressions of `ψ₄`, `χ₁₀` (R4). Proved parts: F1's algebra
(`PkgI1.f1_algebra`), theta-structure independence (`PkgI1.thetaRatio_invariant`), leaf-push2's
`linYangTuple_onQMLocus` (not copied). Missing: the analytic side (R1(b), uniformization:
leaf-push2's `UniformizationExists`), R3 and R4 applied to `A`, algebraicity of the theta point,
the odd-zero height comparison. -/
def ThetaPointOfFibre : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
    ∃ (σ : K.K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
      (Φu : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts (LeafAdopt.abVarEquiv K.K A) σ), ZInQ.LeafPush2.IsUniformization σ Λ Φu ∧
    ∃ Ω : Matrix (Fin 2) (Fin 2) ℂ, ZInQ.LeafPush2.IsSiegel Ω ∧ ZInQ.LeafPush2.IsPeriodMatrix Λ Ω ∧
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* ℂ) (z : ZInQ.LeafPush2.Char2 → L.K) (c : ℂ), c ≠ 0 ∧
      (∀ m, emb (z m) = c * ZInQ.LeafPush2.thetaConst Ω m) ∧
    ∃ (K' : GlueAssembly.NF) (z' : Fin 10 → K'.K),
      3779136 * (∏ i, z' i) ^ 4 / (∑ i, z' i ^ 8) ^ 5 = algebraMap ℚ K'.K (Jmap u) ∧
      Height.logHeight z' / Module.finrank ℚ K'.K ≤ ZInQ.LeafPush2.absLogHeight z

/-- **G19: F1 and F3 on the actual `A` (proved below, `thetaPazuki`, from
`R22_PazukiConcrete` and `ThetaPointOfFibre`).** For `u ∉ 𝒞` and the fibre surface `A` over
`J(u)` with stable height `x`, a point `z ∈ K'¹⁰` with `Φ(z) = J(u)` and Pazuki's bound. -/
def ThetaPazuki : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
    A.dim = 2 → ∀ x : ℝ, stableFaltingsHeight A = x →
      ∃ (K' : GlueAssembly.NF) (z : Fin 10 → K'.K),
        3779136 * (∏ i, z i) ^ 4 / (∑ i, z i ^ 8) ^ 5 = algebraMap ℚ K'.K (Jmap u) ∧
        GlueAssembly.PazukiOutput (Height.logHeight z / Module.finrank ℚ K'.K) x

/-- **Missing piece 10 (glue G2, G4, G7-G16: fibre field, scalar descent, modularity, conductor).**
For `u ∉ 𝒞` and an object `P` of `Y₃` over `ℚ̄` at a point over `J(u)`: there are a number field
`L' ⊆ ℚ̄` with `[L':ℚ] ≤ QM` (G2, G4, G7: the fibre field, the Hom field and B3) and a model `A`
of `P`'s surface over `L'`, a level `1 ≤ N ≤ QM²` (G13-G16: the conductor of the newform `f`), a
`J₁(N)` over `ℚ`, and a common constituent of `V_ℓ(A)` and `V_ℓ(J₁(N)_{L'})` as
`G_{L'}`-representations (G8-G14: `r_ℓ`, its twist, Pan-Berger modularity, the newform and
Eichler-Shimura). Here `Q = Q_D`, `M = M_{S_mul}(u)`. The model and the field are produced
together because `[L':ℚ] ≤ QM` bounds the field of `A`: quantifying over all models would make the
piece false. Proved cores (not on the actual `A`): `GlueDescent.B3Q.b3_degree_le_QM` (B3),
`GlueConductor.level_le` (G16), `GlueConductor.D1_genuine` (D1), `PkgI2.D2_fixed_of_raynaud`,
`PkgI6.artinConductor_le_of_upper`, `PkgI3.C2_absolutelyIrreducible`, `HSyn.weight_match`,
`GlueAssembly.twist_finite`, `LeafModCurves.g13_constituent`, `GlueC10.c10`,
`PkgI2.goodReduction_of_QM_rational3` (G3), `PkgI2.inertiaTrivial_of_goodReduction` (G11).
Missing: the instantiation of all of these on `A`, the appendix lemma (G9), oddness (G10, needs
T11-T12, placeholders) and Carayol's conductor (R17, a placeholder). -/
def ModularConstituent : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) →
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* Qbar) (A : ZInQ.DefFaltings.AbVar L.K) (N : ℕ)
      (J : PkgI3.AbVar ℚ),
      (letI : Algebra L.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X)) ∧
      0 < N ∧ LeafModCurves.IsJ1 N J ∧
      (N : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      (Module.finrank ℚ L.K : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
      CommonConstituent (LeafAdopt.abVarEquiv L.K A)
        (LeafAdopt.abVarEquiv L.K (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K))

/-! ### Proved connective pieces -/

/-- **R18 transported (proved, leaf-adopt3)** from leaf-push2's `R18_Javanpeykar` (the bundle
field `r18`) and `HeightCopiesAgree`. The curve, Jacobian and Belyi predicates of
`LeafModCurves` and `ZInQ.LeafPush2` are textual copies, converted field by field. -/
theorem r18Concrete_of (h : ZInQ.LeafPush2.R18_Javanpeykar) (hH : HeightCopiesAgree) :
    R18_JavanpeykarConcrete := by
  intro K _ _ X hX _ P₀ J aj hJac g hg hg1 t ht d hd hd0
  haveI : ZInQ.LeafPush2.IsCurve X := ⟨hX.proper, hX.smooth, hX.geomConnected⟩
  rw [← hH K J]
  exact h K X P₀ J aj ⟨hJac.base, hJac.univ⟩ g hg hg1 t ht d hd hd0

/-- **R22 transported (proved, leaf-adopt3)** from leaf-push2's `R22_Pazuki` (the bundle field
`r22`) and `HeightCopiesAgree`. -/
theorem r22Concrete_of (h : ZInQ.LeafPush2.R22_Pazuki) (hH : HeightCopiesAgree) :
    R22_PazukiConcrete := by
  intro K _ _ A hA x hx
  rw [← hH K A] at hx
  exact h K A hA x hx

/-- Isomorphic schemes over `S` have the same Krull dimension. -/
theorem dim_eq_of_iso {S : Scheme} {X Y : Over S} (e : X ≅ Y) :
    topologicalKrullDim X.left = topologicalKrullDim Y.left :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso ((Over.forget S).mapIso e)).isHomeomorph

/-- **The model is a surface (proved from `DimBaseChange`).** A model over `L` of an abelian
surface over `ℚ̄` has dimension `2`. -/
theorem model_dim (hDim : DimBaseChange) {L : Type} [Field L] (emb : L →+* Qbar)
    (A : ZInQ.DefFaltings.AbVar L) (B : PkgI3.AbVar Qbar)
    (hiso : letI : Algebra L Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ B.X))
    (hB : B.dim = 2) : A.dim = 2 := by
  letI : Algebra L Qbar := emb.toAlgebra
  obtain ⟨e⟩ : Nonempty ((A.baseChange Qbar).X ≅ B.X) := hiso
  rw [← hDim L Qbar A, ← hB]
  exact dim_eq_of_iso e

/-- **G18/E2, Javanpeykar on `J₁(N)` (proved).** From the concrete R18, the Belyi data on the
model (`X1BelyiOnModel`) and E2's `dim J₁(N) ≤ N²` (`LeafModCurves.dim_J1_le`, from T34):
`13·10⁶·g·d⁵ ≤ 13·10⁶·N²·(N²)⁵`. -/
theorem javanpeykarJ1 (hR18 : R18_JavanpeykarConcrete) (hB : X1BelyiOnModel)
    (hT34 : LeafModCurves.DimJ1Genus) : JavanpeykarJ1 := by
  intro N hN J hJ g hg hg1 x hx
  obtain ⟨X, _, _, P₀, aj, hJac, t, ht, d, hd, hd0, hdN⟩ := hB N hN J hJ
  have h := hR18 ℚ X P₀ J aj hJac g hg hg1 t ht d hd hd0
  rw [hx] at h
  have hxb : x ≤ ZInQ.LeafPush2.javanpeykarBound g d := EReal.coe_le_coe_iff.mp h
  obtain ⟨g', hg', hgN⟩ := LeafModCurves.dim_J1_le hT34 N hN J hJ
  have hgg : g = g' := by
    have : (g : WithBot ℕ∞) = (g' : WithBot ℕ∞) := hg.symm.trans hg'
    exact_mod_cast this
  subst hgg
  have hgR : (g : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hgN
  have hdR : (d : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hdN
  calc x ≤ ZInQ.LeafPush2.javanpeykarBound g d := hxb
    _ = 13 * 10 ^ 6 * (g : ℝ) * (d : ℝ) ^ 5 := rfl
    _ ≤ 13 * 10 ^ 6 * ((N : ℝ) ^ 2) * ((N : ℝ) ^ 2) ^ 5 := by gcongr
    _ = 13000000 * (N : ℝ) ^ 12 := by ring

/-- **G19, F1 + F3 (proved)** from the concrete R22 at `X = max(1, h_F(A) + 3) ≥ max(1, h_F(A) +
log π)` (the hardened form of `PazukiOutput`, rv-leaves-a) and the
theta point of `ThetaPointOfFibre`. -/
theorem thetaPazuki (hR22 : R22_PazukiConcrete) (hT : ThetaPointOfFibre) : ThetaPazuki := by
  intro Y Φ π h1 h2 u hu K A hFib hA2 x hx
  obtain ⟨σ, Λ, Φu, hΦu, Ω, hΩ, hP, L, emb, z, c, hc, hz, K', z', hF1, hle⟩ :=
    hT Y Φ π h1 h2 u hu K A hFib
  refine ⟨K', z', hF1, ?_⟩
  have hx' : stableFaltingsHeight ((LeafAdopt.abVarEquiv K.K).symm
      (LeafAdopt.abVarEquiv K.K A)) = x := by
    rw [Equiv.symm_apply_apply]; exact hx
  have hpi : Real.log Real.pi ≤ 3 := by
    have h4 : Real.log Real.pi ≤ Real.log 4 :=
      Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_four])
    have h42 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  have h := hR22 K.K (LeafAdopt.abVarEquiv K.K A) hA2 x hx' (max 1 (x + 3))
    (max_le_max le_rfl (by linarith)) σ Λ Φu hΦu Ω hΩ hP L.K emb z c hc hz
  unfold GlueAssembly.PazukiOutput
  unfold ZInQ.LeafPush2.pazukiC2 at h
  linarith

/-- **G17 after Poincaré (proved)** from `DimFinite`, `ProductExists`, `ReverseIsogeny`. -/
theorem isogenousProduct (hF : DimFinite) (hP : ProductExists) (hR : ReverseIsogeny) :
    IsogenousProduct := by
  intro L _ _ A J Z f g hiso
  obtain ⟨P, hPA, hPd⟩ := hP L A Z
  obtain ⟨φ, hφ, hJd⟩ := hR L A J Z P f g hPA hiso
  refine ⟨P, φ, hφ, hPA, fun a n ha hn => ?_⟩
  obtain ⟨m, hm⟩ := hF L Z
  refine ⟨m, hm, ?_⟩
  have h : ((n : ℕ) : WithBot ℕ∞) = ((a + m : ℕ) : WithBot ℕ∞) := by
    rw [← hn, hJd, hPd, ha, hm, Nat.cast_add]
  exact_mod_cast h.symm

/-- `log κ` of Gaudron-Rémond, computed. -/
theorem log_grKappa (g d : ℕ) (x : ℝ) (hg : 1 ≤ g) (hd : 1 ≤ d) :
    Real.log (grKappa g d x) = 1024 * (g : ℝ) ^ 3 * (64 * (g : ℝ) ^ 2 * Real.log (14 * g) +
      Real.log d + 2 * Real.log (max x (max (Real.log d) 1))) := by
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h14 : (0 : ℝ) < 14 * g := by positivity
  have hm : (1 : ℝ) ≤ max (max x (Real.log d)) 1 := le_max_right _ _
  have ha : ((14 * g : ℝ) ^ (64 * g ^ 2)) ≠ 0 := (pow_pos h14 _).ne'
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hm2 : (max (max x (Real.log d)) 1) ^ 2 ≠ 0 := (pow_pos (by linarith) _).ne'
  unfold grKappa
  rw [Real.log_pow, Real.log_mul (mul_ne_zero ha hd0) hm2, Real.log_mul ha hd0, Real.log_pow,
    Real.log_pow, max_assoc]
  push_cast
  ring

theorem one_le_grKappa (g d : ℕ) (x : ℝ) (hg : 1 ≤ g) (hd : 1 ≤ d) : 1 ≤ grKappa g d x := by
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h14 : (1 : ℝ) ≤ 14 * g := by linarith
  have hm : (1 : ℝ) ≤ max (max x (Real.log d)) 1 := le_max_right _ _
  unfold grKappa
  apply one_le_pow₀
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ h14) hd')
    (one_le_pow₀ hm)

/-- **E3-E4 numerics on concrete objects (proved from R19, R20, R21).** Over a number field `L`,
for `J` of dimension `g ≥ 2` with an isogeny `J → P`, `h_F(A) + h_F(Z) ≤ h_F(P)`, `dim Z ≤ g`,
the bounds on `N`, `[L:ℚ]`, `h_F(J)` and `g ≤ N²` give glue-assembly's `NonCMOutput`. -/
theorem transfer_core (r19 : R19_GaudronRemond) (r20 : R20_FaltingsLemma5) (r21 : R21_Bost)
    {L : Type} [Field L] [NumberField L] (J P A Z : ZInQ.DefFaltings.AbVar L) (g gZ : ℕ)
    (hJd : J.dim = (g : WithBot ℕ∞)) (hZd : Z.dim = (gZ : WithBot ℕ∞)) (hgZ : gZ ≤ g)
    (hg2 : 2 ≤ g) (φ : J.X ⟶ P.X) (hφ : IsIsogeny φ) (x y a z : ℝ)
    (hx : stableFaltingsHeight J = x) (hy : stableFaltingsHeight P = y)
    (hz : stableFaltingsHeight Z = z) (hadd : a + z ≤ y) {Q M N : ℝ} (hN1 : 1 ≤ N)
    (hN : N ≤ Q * M ^ 2) (hJav : x ≤ 13000000 * N ^ 12) (hgN : (g : ℝ) ≤ N ^ 2)
    (hd : (Module.finrank ℚ L : ℝ) ≤ Q * M) :
    GlueAssembly.NonCMOutput Q M a := by
  obtain ⟨⟨ψ, hψ, hdeg⟩, -⟩ := r19 L J P g x hJd hx ⟨φ, hφ⟩
  have hvar := r20 L J P ψ hψ x y hx hy
  have hB := r21 L Z gZ hZd
  rw [hz] at hB
  have hB' : -(3 / 2) * (gZ : ℝ) ≤ z := EReal.coe_le_coe_iff.mp hB
  set d := Module.finrank ℚ L with hdd
  have hd1 : 1 ≤ d := Module.finrank_pos
  have hg1 : 1 ≤ g := by omega
  have hκ := log_grKappa g d x hg1 hd1
  have hκ1 := one_le_grKappa g d x hg1 hd1
  have hlogdeg : Real.log (isogDeg ψ) ≤ Real.log (grKappa g d x) := by
    rcases Nat.eq_zero_or_pos (isogDeg ψ) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg hκ1
    · exact Real.log_le_log (by exact_mod_cast hpos) hdeg
  refine ⟨N, g, d, x, Real.log (isogDeg ψ), z, hN1, hN, hJav, by exact_mod_cast hg2, hgN,
    by exact_mod_cast hd1, hd, ?_, ?_, ?_⟩
  · rw [hκ] at hlogdeg; exact hlogdeg
  · have := (abs_le.mp hvar).1
    linarith
  · have hgZr : (gZ : ℝ) ≤ g := by exact_mod_cast hgZ
    linarith

/-- glue-ssbc's theorem in `GlueI3`'s statement. -/
theorem semisimpleBaseChange : GlueI3.SemisimpleBaseChange :=
  fun k E G V _ _ _ _ _ _ _ _ ρ hρ => GlueSSBC.semisimpleBaseChange k E G V ρ hρ

/-- **E1 on a common constituent (proved)**: `PkgI3.E1_exists_hom_ne_zero` with R9 (Faltings),
T26 and glue-ssbc. -/
theorem hom_of_common (r : ResearchLeaves) (t : TextbookLeaves) {K : Type} [Field K]
    [NumberField K] (A J : PkgI3.AbVar K) (h : CommonConstituent A J) :
    ∃ f : PkgI3.AbVar.Hom A J, f ≠ 0 := by
  obtain ⟨ℓ, _, E, _, _, U, U', e, hU, he⟩ := h
  exact PkgI3.E1_exists_hom_ne_zero r.r9a r.r9b t.t26 semisimpleBaseChange A J ℓ E U U' hU e he

end G0Split

/-- **The glue pieces** (g0-split's ten missing pieces, smallest first, and leaf-adopt2's
`HeightCopiesAgree`), bundled (leaf-adopt3). Each is a `def … : Prop` whose docstring names its
glue step; none is a literature leaf, and each is to be proved in Lean by the project. -/
structure GluePieces : Prop where
  /-- 1. An abelian variety has finite dimension (definition level). -/
  dimFinite : G0Split.DimFinite
  /-- 2. Dimension is invariant under field extension (Stacks 00P4). -/
  dimBaseChange : G0Split.DimBaseChange
  /-- 3. E2, Belyi half: `BelyiX1` on the model of `IsJ1`. -/
  belyi : G0Split.X1BelyiOnModel
  /-- 4. G5-G6 on the fibre surface: simplicity. -/
  fibreSimple : G0Split.FibreSimple
  /-- 5. E4: additivity of the stable height on products. -/
  additivity : G0Split.HeightAdditivity
  /-- 6. Stable height invariant under base change. -/
  stableHeightBaseChange : G0Split.StableHeightBaseChange
  /-- 7. G17: products of abelian varieties exist. -/
  productExists : G0Split.ProductExists
  /-- 8. G17: the reverse isogeny `J → A × Z`. -/
  reverseIsogeny : G0Split.ReverseIsogeny
  /-- 9. G19, F1 on the fibre surface: the theta point. -/
  thetaPoint : G0Split.ThetaPointOfFibre
  /-- 10. G2, G4, G7-G16: field, model, level and common constituent. -/
  modularConstituent : G0Split.ModularConstituent
  /-- 11. The two textual copies of the stable Faltings height agree (leaf-adopt2's target). -/
  heightCopies : HeightCopiesAgree

open G0Split in
/-- **The glue G1-G17 and G19 (non-Arakelov part), split (g0-split).** The leaves and the ten
missing glue pieces (each a `def … : Prop` in `G0Split` whose docstring names its glue step) give
glue-assembly's interface `GlueOutputs` at `S = Mult.S_mul`. Applied proved pieces: A4
(`LeafQM.AV.exists_fibre_object`, from R1-R2), `model_dim`, H5's finiteness
(`faltingsHeight_coe`), E1 (`hom_of_common`: R9, T26, glue-ssbc), T8 (Poincaré, a leaf), E2's
`dim J₁(N) ≤ N²` (`LeafModCurves.dim_J1_le`, from T34), `javanpeykarJ1` (concrete R18),
`thetaPazuki` (concrete R22), `isogenousProduct`, and the E3-E4 numerics (`transfer_core`, from
R19-R21). The non-CM disjunct is used (G6, NoCM). -/
theorem glueOutputs_of_leaves (r : ResearchLeaves) (t : TextbookLeaves) (gp : GluePieces) :
    GlueAssembly.GlueOutputs ZInQ.Mult.S_mul := by
  obtain ⟨hDimF, hDim, hBelyi, hSimp, hAdd, hBC, hProdE, hRev, hThetaPt, hMod, hCopies⟩ := gp
  have hR18 : R18_JavanpeykarConcrete := r18Concrete_of r.r18 hCopies
  have hR22 : R22_PazukiConcrete := r22Concrete_of r.r22 hCopies
  -- A4: the moduli data and an object over every value
  obtain ⟨Y, Φ, π, h1, h2, hfib⟩ :=
    LeafQM.AV.exists_fibre_object (LeafAdopt.R1R2fp_of_rep r.r1r2)
  intro u hu
  obtain ⟨y, P, hP, hy⟩ := hfib (OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)))
  -- G2-G16 (missing piece 10, `ModularConstituent`): the field `L'`, the model `A`, the level `N`, `J₁(N)`
  obtain ⟨L, emb, A, N, J, hiso, hN0, hJ1, hNQ, hdQ, hCC⟩ := hMod Y Φ π h1 h2 u hu y P hP hy
  have hFib : FibreOver Y Φ π u L A := ⟨emb, y, P, hP, hy, hiso⟩
  have hA2 : A.dim = 2 := model_dim hDim emb A P.A hiso P.surface
  -- H5: the stable height of `A` is real
  have hfin := r.h5.1
  have hx : ZInQ.DefFaltings.stableFaltingsHeight A = ZInQ.DefFaltings.faltingsHeight A :=
    (ZInQ.DefFaltings.faltingsHeight_coe hfin A).symm
  -- G19: the theta point (missing piece 9, `ThetaPointOfFibre`) and Pazuki (R22)
  obtain ⟨K', z, hF1, hPaz⟩ := thetaPazuki hR22 hThetaPt Y Φ π h1 h2 u hu L A hFib hA2 _ hx
  refine ⟨K', z, ZInQ.DefFaltings.faltingsHeight A, hF1, hPaz, Or.inl ?_⟩
  -- E1: a nonzero homomorphism `A → J₁(N)_{L'}`
  obtain ⟨f, hf⟩ := hom_of_common r t _ _ hCC
  -- G5-G6 (missing piece 4, `FibreSimple`): `A` simple; T8: Poincaré
  obtain ⟨Z, g, hisoZ⟩ := t.t8 L.K _ _ (hSimp Y Φ π h1 h2 u hu L A hFib) f hf
  -- G17 after Poincaré (`isogenousProduct`, from missing pieces 1, 7, 8): `A × Z`, the isogeny `J₁(N)_{L'} → A × Z`
  obtain ⟨Pr, φ, hφ, hPprod, hdims⟩ :=
    isogenousProduct hDimF hProdE hRev L.K _ _ _ f g hisoZ
  -- E2: `dim J₁(N) ≤ N²`
  obtain ⟨gJ, hgJ, hgN⟩ := LeafModCurves.dim_J1_le t.t34 N hN0 J hJ1
  have hJLd : (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K).dim = (gJ : WithBot ℕ∞) :=
    (hDim ℚ L.K ((LeafAdopt.abVarEquiv ℚ).symm J)).trans hgJ
  have hALd : A.dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [hA2]; rfl
  obtain ⟨gZ, hZd, hsum⟩ := hdims 2 gJ hALd hJLd
  -- heights (H5; missing pieces 5, 6; R18 with missing pieces 2, 3)
  have hxJ : ZInQ.DefFaltings.stableFaltingsHeight
      (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K) =
      ZInQ.DefFaltings.faltingsHeight ((LeafAdopt.abVarEquiv ℚ).symm J) := by
    rw [hBC ℚ L.K ((LeafAdopt.abVarEquiv ℚ).symm J)]
    exact (ZInQ.DefFaltings.faltingsHeight_coe hfin _).symm
  have hyP := (ZInQ.DefFaltings.faltingsHeight_coe hfin Pr).symm
  have hzZ := (ZInQ.DefFaltings.faltingsHeight_coe hfin ((LeafAdopt.abVarEquiv L.K).symm Z)).symm
  have hadd := hAdd L.K Pr A ((LeafAdopt.abVarEquiv L.K).symm Z) hPprod _ _ _ hx hzZ hyP
  have hJb := javanpeykarJ1 hR18 hBelyi t.t34 N hN0 J hJ1 gJ hgJ (by omega) _
    (ZInQ.DefFaltings.faltingsHeight_coe hfin _).symm
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  have hgN' : (gJ : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hgN
  -- E3-E4 (proved from R19-R21)
  exact transfer_core r.r19 r.r20 r.r21 (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K) Pr A
    ((LeafAdopt.abVarEquiv L.K).symm Z) gJ gZ hJLd hZd (by omega) (by omega) φ hφ _ _ _ _ hxJ hyP
    hzZ hadd hN1 hNQ hJb hgN' hdQ

/-- **G18-G20, proved** (glue-assembly): `GlueOutputs Mult.S_mul → SixContactMin`, through F2
over Mathlib's Weil heights, the E2-E4 and F3 arithmetic, the final constant, and F4.
`GlueAssembly.SixContactMinAt Mult.S_mul` is `ZInQ.SixContactMin` by definition. -/
theorem sixContactMin_of_glueOutputs (h : GlueAssembly.GlueOutputs ZInQ.Mult.S_mul) :
    ZInQ.SixContactMin :=
  GlueAssembly.sixContactMinAt_of_glueOutputs h

/-- The scratch copy of `JHeightBound` in glue-assembly is the repository's. -/
theorem jHeightBound_copy_iff :
    GlueAssembly.JHeightBound ZInQ.Mult.S_mul ↔ ZInQ.JHeight.JHeightBound ZInQ.Mult.S_mul :=
  Iff.rfl

/-- **G0. The leaves and the glue pieces imply `SixContactMin`** (no `sorry`). Hypotheses: exactly
the three bundles `ResearchLeaves`, `TextbookLeaves`, `GluePieces`. -/
theorem sixContactMin_of_leaves (r : ResearchLeaves) (t : TextbookLeaves) (gp : GluePieces) :
    ZInQ.SixContactMin :=
  sixContactMin_of_glueOutputs (glueOutputs_of_leaves r t gp)

/-- **G20 alone** (the existing proof in `ZInQKernel`), for reference. -/
example (h : ZInQ.JHeight.JHeightBound ZInQ.Mult.S_mul) : ZInQ.SixContactMin :=
  ZInQ.JHeight.sixContactMin_of_jHeightBound h

end HSyn


end

#print axioms HSyn.weight_match
#print axioms PkgI2.inertiaTrivial_of_goodReduction
#print axioms PkgI2.D2_fixed_of_raynaud
#print axioms GlueConductor.D1_genuine
#print axioms GlueConductor.level_le
#print axioms GlueConductor.fourth_pow_mem
#print axioms HSyn.sixContactMin_of_glueOutputs
#print axioms PkgI1.f1_algebra
#print axioms PkgI1.equiv_of_lyVec
#print axioms PkgI3.exists_hom_ne_zero_of_equivariant
#print axioms PkgI3.finrank_equivEnd
#print axioms PkgI6.eq_of_same_finite_support
#print axioms GlueAssembly.twist_finite
#print axioms GlueAssembly.index_Gamma1_le
#print axioms GlueAssembly.mulHeight_le_mulHeightL2
#print axioms GlueAssembly.invariants_ne_bot_of_baseChange
#print axioms GlueDescent.B3Q.b3_degree_le_QM
#print axioms GlueRepo.PR.inertia_orders_eq_one_iff
#print axioms GlueRepo.PR.fibre_free
#print axioms HSyn.sq_principalUnits_proved
#print axioms HSyn.sixContactMin_of_leaves
-- hsyn-fix: theorems adopted from rv-a6-route, glue-I6-rest and glue-I3-linalg
#print axioms PkgI2.goodReduction_of_QM_rational3
#print axioms PkgI6.artinConductor_le_of_upper
#print axioms PkgI6.sq_principalUnits
#print axioms PkgI3.C2_absolutelyIrreducible
#print axioms PkgI3.E1_exists_hom_ne_zero
#print axioms GlueI3.equivariantDescent
#print axioms GlueI3.absolutelyIrreducible_of_finrank_commOf_prod_le_four
-- hsyn-fix: further theorems the note calls proved (rv-hsyn §B checked them in a copy)
#print axioms PkgI1.gram_det
#print axioms PkgI1.cm4
#print axioms PkgI1.cm24
#print axioms PkgI1.G6_sub_F2
#print axioms PkgI1.Ju_ne_branch
#print axioms PkgI1.elkies_t
#print axioms PkgI1.elkies_t_sub_one
#print axioms PkgI1.thetaRatio_invariant
#print axioms GlueAssembly.logHeight_Phi_le
#print axioms GlueAssembly.transfer_of_level
#print axioms GlueAssembly.weight_match_coh
#print axioms GlueAssembly.sixContactMinAt_of_glueOutputs
#print axioms GlueAssembly.pazuki_numerics
#print axioms PkgI3.range_tateHomZl_subset
#print axioms GlueDescent.B2Q.b2_of_leaves
#print axioms GlueConductor.exists_sq_eq_one_add
#print axioms PkgI6.cob_of_same_finite_support
-- hsyn-fold: theorems adopted from glue-a6-alg, glue-c10 and glue-d1-local
#print axioms GlueA6Alg.Alg.core
#print axioms GlueA6Alg.Alg.exists_valuationSubring_comap_eq
#print axioms PkgI2.quatUnipotentTrivial
#print axioms PkgI2.goodReduction_of_QM_rational3_of_alg
#print axioms PkgI2.goodReduction_of_QM_rational3'
#print axioms PkgI3.trace_indep_of_ell
#print axioms PkgI3.trace_eq_trace_of_ell
#print axioms GlueC10.iso_of_trace_eq_frob_finite
#print axioms GlueC10.frobDense_of_chebotarev
#print axioms GlueC10.eq_of_eq_on_frob
#print axioms GlueC10.iso_of_trace_eq_on_frob
#print axioms GlueC10.iso_three_of_five
#print axioms GlueC10.semisimple_of_le
#print axioms GlueC10.trace_half
#print axioms GlueC10.frobLift
#print axioms GlueC10.frobDense
#print axioms GlueC10.c10
#print axioms GlueD1Local.ramificationIdx_le_factorial_local
#print axioms GlueD1Local.D1_local
#print axioms GlueD1Local.index_localSub
#print axioms GlueD1Local.D1_local'
#print axioms GlueD1Local.ramificationIdx_le_factorial_of_unique
#print axioms GlueD1Local.D1_krasner
#print axioms GlueD1Local.D1_krasner'
-- hsyn-fold: obj-bridge
#print axioms ObjBridge.homEquiv
#print axioms ObjBridge.endMulEquiv
#print axioms ObjBridge.homRankBound_iff
#print axioms ObjBridge.charpolyIndependentOfEll_iff
#print axioms ObjBridge.neronOggShafarevich_iff
#print axioms ObjBridge.i3Leaves_iff
#print axioms ObjBridge.charPolyIndepOfEll_iff_grp
#print axioms ObjBridge.exists_hom_ne_one_of_equivariant
#print axioms ObjBridge.finrank_equivEnd
#print axioms ObjBridge.ofGrp_baseChange
#print axioms ObjBridge.homT_comp
#print axioms ObjBridge.homT_id
-- leaf-adopt: theorems adopted from glue-t32a, leaf-qm-fp, leaf-modcurves, def-faltings, and new
#print axioms HSyn.t32a_glue
#print axioms HSyn.t32b_glue
#print axioms HSyn.leafB3a_glue
#print axioms GlueB3Unram.unramified_outside_noLeaf
#print axioms LeafQM.AV.R1fp_of_R1R2fp
#print axioms LeafQM.AV.R5fpWeak_of_R5fp
#print axioms LeafQM.AV.conj_iso_of_rational
#print axioms LeafQM.AV.cm_of_val
#print axioms LeafQM.AV.Level3.onto
#print axioms LeafQM.AV.Level3.torsor
#print axioms LeafQM.AV.QML3.goodReduction
#print axioms LeafQM.AV.residue_unramified_over_branch
#print axioms LeafQM.AV.exists_fibre_object
#print axioms LeafQM.AV.fibre_conjugates_isomorphic
#print axioms LeafQM.AV.leaves_on_one_witness
#print axioms LeafModCurves.genus_Gamma1_le
#print axioms LeafModCurves.IsJacobian.unique
#print axioms LeafModCurves.dim_J1_le
#print axioms LeafModCurves.exists_J1_dim_le
#print axioms LeafModCurves.exists_J1_quotient
#print axioms LeafModCurves.rhoF_traces
#print axioms LeafModCurves.g13_constituent
#print axioms LeafModCurves.rhoF_attached
#print axioms ZInQ.DefFaltings.stableFaltingsHeight
#print axioms ZInQ.DefFaltings.MetrizedModel.modelHeight_eq_of_model_eq
#print axioms ZInQ.DefFaltings.stableFaltingsHeight_eq_iInf_height
#print axioms ZInQ.DefFaltings.stableFaltingsHeightDeligne_eq
#print axioms ZInQ.DefFaltings.stableFaltingsHeight_ne_bot_of_R21
#print axioms LeafAdopt.r2X6PropsIff_of
#print axioms LeafAdopt.cmExists_of_iff
#print axioms LeafAdopt.R1R2fp_of_rep
#print axioms LeafAdopt.R5fp_iff_R5fpStrong
#print axioms HSyn.sixContactMin_of_leaves
#print axioms LeafAdopt.abVarEquiv_dim
#print axioms ZInQ.LeafPush2.stableFaltingsHeight
#print axioms ZInQ.LeafPush2.R18_real
#print axioms ZInQ.LeafPush2.javanpeykarBound_pos
#print axioms ZInQ.LeafPush2.javanpeykarBound_mono
#print axioms ZInQ.LeafPush2.R22_plus3
#print axioms ZInQ.LeafPush2.isSiegel_I
#print axioms ZInQ.LeafPush2.linYangTuple_onQMLocus
#print axioms ZInQ.LeafPush2.onQMLocus_of_linYangTuple
#print axioms ZInQ.LeafPush2.linYang_j_eq
#print axioms ZInQ.LeafPush2.R03_of_algClosed
#print axioms ZInQ.LeafPush2.exists_isComplexConj
#print axioms ZInQ.LeafPush2.T10_groupIso
#print axioms ZInQ.LeafPush2.R03_LinYang
#print axioms ZInQ.LeafPush2.R22_Pazuki
#print axioms ZInQ.LeafPush2.R18_Javanpeykar
#print axioms HSyn.isComplexConj_leafPush2_iff
-- leaf-adopt3: g0-split's proof of glueOutputs_of_leaves
#print axioms HSyn.glueOutputs_of_leaves
#print axioms HSyn.G0Split.transfer_core
#print axioms HSyn.G0Split.javanpeykarJ1
#print axioms HSyn.G0Split.thetaPazuki
#print axioms HSyn.G0Split.isogenousProduct
#print axioms HSyn.G0Split.semisimpleBaseChange

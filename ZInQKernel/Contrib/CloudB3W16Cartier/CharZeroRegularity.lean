/-
Adapted from AxiomMath/Stacks, c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/RingTheory/Smooth/RegularLocalRing/CharZeroRegularity.lean,
lines 106–456. Source SHA256: 2ea401af814ca2c9942aa83aadb6f1d0f73e2c2f44a82b80dd8118cfd3308ee2.
Apache-2.0; see LICENSE and NOTICE.md in this directory.
Changes: retain only the 00TX induction; use Mathlib's formal-smooth conormal
injection and perfect-field residue smoothness, drop citation attributes,
and isolate new declarations. No change to the mathematical induction.
-/
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.Kaehler.TensorProduct
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.RingTheory.Smooth.RegularLocalRing

noncomputable section
universe u v w
namespace ZInQ.Contrib.CloudB3W16Cartier
open Module IsLocalRing KaehlerDifferential TensorProduct

/-- The structure map onto a quotient ring is surjective. -/
private lemma Ideal.Quotient.algebraMap_surjective {R : Type*} [CommRing R] (I : Ideal R) :
    Function.Surjective (algebraMap R (R ⧸ I)) := by
  rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective

/-- Characteristic zero, in the form the argument uses it: every `n + 1` is invertible in an
algebra over a field of characteristic zero. -/
private lemma isUnit_natCast_add_one (k R : Type*) [Field k] [CharZero k] [CommRing R]
    [Algebra k R] (n : ℕ) : IsUnit ((n : R) + 1) := by
  have h : ((n : R) + 1) = algebraMap k R ((n : k) + 1) := by push_cast; ring
  rw [h]
  exact IsUnit.map _ (Ne.isUnit (Nat.cast_add_one_ne_zero n : ((n : k) + 1) ≠ 0))

/-- **The cancellation at the heart of Stacks 00TW (2).** Let `θ` be a derivation over a field of
characteristic zero taking the value `1` at `f`. Differentiating `f ^ (n + 1) * b = 0` gives
`(n + 1) * b * f ^ n = -f ^ (n + 1) * θ b`, so dividing by the unit `n + 1` shows that `b * f ^ n`
is again divisible by `f ^ (n + 1)`. -/
private lemma mem_span_singleton_pow_succ_of_derivation_apply_eq_one {k R : Type*} [Field k]
    [CharZero k] [CommRing R] [Algebra k R] (θ : Derivation k R R) {f b : R} {n : ℕ}
    (hθ : θ f = 1) (h : f ^ (n + 1) * b = 0) : b * f ^ n ∈ Ideal.span {f ^ (n + 1)} := by
  have hd : θ (f ^ (n + 1) * b) = 0 := by rw [h, map_zero]
  rw [Derivation.leibniz, Derivation.leibniz_pow] at hd
  simp only [hθ, smul_eq_mul, Nat.add_sub_cancel, mul_one, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at hd
  obtain ⟨u, hu⟩ := isUnit_natCast_add_one k R n
  have hkey : (u : R) * (b * f ^ n) = f ^ (n + 1) * (-(θ b)) := by
    rw [hu]; linear_combination hd
  refine Ideal.mem_span_singleton'.mpr ⟨(↑u⁻¹ : R) * (-(θ b)), ?_⟩
  calc (↑u⁻¹ : R) * (-(θ b)) * f ^ (n + 1)
      = (↑u⁻¹ : R) * ((u : R) * (b * f ^ n)) := by rw [hkey]; ring
    _ = b * f ^ n := by rw [← mul_assoc, u.inv_mul, one_mul]

/-- **Stacks 00TW (2).** Let `R` be a Noetherian local algebra over a field of characteristic zero.
If some `k`-derivation of `R` takes the value `1` at `f`, then `f` is a nonzerodivisor: an `a` with
`a * f = 0` lies in every power of `(f)`, hence in `⋂ (f) ^ n = 0`. -/
private lemma mem_nonZeroDivisors_of_derivation_apply_eq_one
    {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra k R] (θ : Derivation k R R) {f : R} (hθ : θ f = 1) :
    f ∈ nonZeroDivisors R := by
  have key : ∀ a : R, a * f = 0 → a = 0 := by
    intro a ha
    by_cases hu : IsUnit f
    · exact hu.mul_left_eq_zero.mp ha
    have hpow : ∀ n : ℕ, a ∈ Ideal.span ({f} : Set R) ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Ideal.span_singleton_pow] at ih ⊢
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ih
        exact mem_span_singleton_pow_succ_of_derivation_apply_eq_one θ hθ (by rw [← ha]; ring)
    have hmem : a ∈ (⨅ i, Ideal.span ({f} : Set R) ^ i) := Ideal.mem_iInf.mpr hpow
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _
      (fun h => hu (Ideal.span_singleton_eq_top.mp h))] at hmem
    simpa using hmem
  exact mem_nonZeroDivisors_iff.mpr ⟨fun a ha => key a (by rwa [mul_comm]), key⟩

/-- **Nakayama, Stacks 00DV.** In a Noetherian local ring with nonzero maximal ideal `𝔪 ≠ 𝔪²`: some
element of `𝔪` has nonzero class in `𝔪/𝔪²`. -/
private lemma exists_mem_maximalIdeal_notMem_sq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (hm : maximalIdeal R ≠ ⊥) :
    ∃ f ∈ maximalIdeal R, f ∉ maximalIdeal R ^ 2 := by
  by_contra hc
  push Not at hc
  exact hm (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
    (IsNoetherian.noetherian _) (fun a ha => by simpa [Ideal.smul_eq_mul, pow_two] using hc a ha)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge)

/-- A functional taking the value `1` at `x` splits `R ∙ x` off as a direct summand, with
complement its kernel. -/
private lemma isCompl_span_singleton_ker {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {φ : M →ₗ[R] R} {x : M} (hx : φ x = 1) : IsCompl (R ∙ x) (LinearMap.ker φ) := by
  constructor
  · rw [disjoint_iff, Submodule.eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy1
    have hc : c = 0 := by simpa [hx] using hy2
    simp [hc]
  · rw [codisjoint_iff, eq_top_iff]
    intro y _
    refine Submodule.mem_sup.mpr ⟨φ y • x, Submodule.mem_span_singleton.mpr ⟨_, rfl⟩,
      y - φ y • x, ?_, by abel⟩
    simp [LinearMap.mem_ker, hx]

/-- If a functional on a finite free module over a local ring takes the value `1` at `x`, then
`M ⧸ R ∙ x` is free of rank one less: it is the kernel of the functional, a direct summand of `M`
and hence projective, and a projective module over a local ring is free. -/
private lemma free_and_finrank_quotient_span_singleton_of_apply_eq_one
    {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] {φ : M →ₗ[R] R} {x : M} (hx : φ x = 1) :
    Module.Free R (M ⧸ R ∙ x) ∧ finrank R (M ⧸ R ∙ x) + 1 = finrank R M := by
  have hcompl := isCompl_span_singleton_ker hx
  have e : (M ⧸ R ∙ x) ≃ₗ[R] LinearMap.ker φ := Submodule.quotientEquivOfIsCompl _ _ hcompl
  have : Module.Finite R (LinearMap.ker φ) := Module.Finite.equiv e
  have : Module.Projective R (LinearMap.ker φ) :=
    Module.Projective.of_split (LinearMap.ker φ).subtype
      (Submodule.projectionOnto _ _ hcompl.symm)
      (by ext y; simp [Submodule.projectionOnto_apply_left])
  have : Module.Free R (LinearMap.ker φ) := Module.free_of_flat_of_isLocalRing
  -- `R ∙ x` is free of rank one, `φ` witnessing that `x` generates it freely
  have hinj : Function.Injective (LinearMap.toSpanSingleton R M x) := fun a c hac => by
    simpa [LinearMap.toSpanSingleton_apply, hx] using congrArg φ hac
  have espan : R ≃ₗ[R] (R ∙ x) := (LinearEquiv.ofInjective _ hinj).trans
    (LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range R M x).symm)
  have : Module.Free R (R ∙ x) := Module.Free.of_equiv espan
  have : Module.Finite R (R ∙ x) := Module.Finite.equiv espan
  have hone : finrank R (R ∙ x) = 1 := by rw [← espan.finrank_eq]; simp
  have hrk : finrank R (R ∙ x) + finrank R (LinearMap.ker φ) = finrank R M := by
    rw [← Module.finrank_prod]
    exact LinearEquiv.finrank_eq (Submodule.prodEquivOfIsCompl _ _ hcompl)
  refine ⟨Module.Free.of_equiv e.symm, ?_⟩
  rw [e.finrank_eq, ← hrk, hone]
  ring

/-- **Nakayama, Stacks 00DV.** In a finite free module over a local ring, an element whose image in
the fibre `κ ⊗ M` is nonzero is the value `1` of some functional: otherwise every functional is a
nonunit at it, so all of its coordinates lie in the maximal ideal. -/
private lemma exists_apply_eq_one_of_tmul_ne_zero
    {R κ M : Type*} [CommRing R] [IsLocalRing R] [Field κ] [Algebra R κ]
    (hsurj : Function.Surjective (algebraMap R κ))
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] {x : M}
    (hx : (1 : κ) ⊗ₜ[R] x ≠ 0) : ∃ φ : M →ₗ[R] R, φ x = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hnu : ∀ φ : M →ₗ[R] R, ¬ IsUnit (φ x) := by
    rintro φ ⟨v, hv⟩
    refine hcon ((↑v⁻¹ : R) • φ) ?_
    rw [LinearMap.smul_apply, smul_eq_mul, ← hv]
    exact v.inv_mul
  have hker := IsLocalRing.ker_eq_maximalIdeal _ hsurj
  set b := Module.Free.chooseBasis R M with hb
  refine hx ?_
  rw [← b.sum_repr x, TensorProduct.tmul_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hcoord : algebraMap R κ (b.repr x i) = 0 :=
    RingHom.mem_ker.mp (hker.ge ((mem_maximalIdeal _).mpr
      (by simpa using hnu ((Finsupp.lapply i).comp b.repr.toLinearMap))))
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, hcoord,
    TensorProduct.zero_tmul]

/-- The conormal module `I/I²` of a principal ideal `I = (f)` is generated by the class of `f`. -/
private lemma Ideal.span_toCotangent_eq_top {R : Type*} [CommRing R] {I : Ideal R} {f : R}
    (hI : I = Ideal.span {f}) (hf : f ∈ I) :
    Submodule.span R {I.toCotangent ⟨f, hf⟩} = ⊤ := by
  subst hI
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨⟨a, ha⟩, rfl⟩ := Ideal.toCotangent_surjective _ y
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
  rw [← LinearMap.map_smul]
  congr 1

/-- **The conormal sequence for a principal quotient** (Stacks 00RU). Let `R` be a `k`-algebra and
`I = (f)` a principal ideal. Then the kernel of the base change map
`R/I ⊗_R Ω_{R/k} → Ω_{(R/I)/k}` is the line spanned by `1 ⊗ df`: by Stacks 00RU that kernel is the
image of `I/I²`, and `I/I²` is generated by the class of `f`. -/
private lemma KaehlerDifferential.ker_mapBaseChange_quotient (k R : Type*) [Field k] [CommRing R]
    [Algebra k R] (I : Ideal R) {f : R} (hI : I = Ideal.span {f}) :
    LinearMap.ker (mapBaseChange k R (R ⧸ I)) =
      Submodule.span (R ⧸ I) {(1 : R ⧸ I) ⊗ₜ[R] D k R f} := by
  have hsurj := Ideal.Quotient.algebraMap_surjective I
  have hker : RingHom.ker (algebraMap R (R ⧸ I)) = I := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  have hfk : f ∈ RingHom.ker (algebraMap R (R ⧸ I)) := by
    rw [hker, hI]; exact Ideal.mem_span_singleton_self f
  refine Submodule.restrictScalars_injective R _ _ ?_
  rw [Submodule.restrictScalars_span R (R ⧸ I) hsurj,
    ← range_kerCotangentToTensor k R (R ⧸ I) hsurj, ← Submodule.map_top,
    ← Ideal.span_toCotangent_eq_top (hker.trans hI) hfk, Submodule.map_span, Set.image_singleton,
    kerCotangentToTensor_toCotangent]

/-- The quotient of a local ring by the principal ideal of a nonunit is local. -/
private lemma isLocalRing_quotient_span_singleton {R : Type*} [CommRing R] [IsLocalRing R] {f : R}
    (hf : ¬ IsUnit f) : IsLocalRing (R ⧸ Ideal.span ({f} : Set R)) :=
  have : Nontrivial (R ⧸ Ideal.span ({f} : Set R)) := Ideal.Quotient.nontrivial_iff.mpr
    (fun hc => hf (Ideal.span_singleton_eq_top.mp hc))
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The differentials of a quotient are finite whenever those of the ring are: the base change map
of Stacks 00RU is surjective. -/
private lemma KaehlerDifferential.finite_quotient (k R : Type*) [Field k] [CommRing R] [Algebra k R]
    [Module.Finite R Ω[R⁄k]] (I : Ideal R) : Module.Finite (R ⧸ I) Ω[R ⧸ I⁄k] :=
  have : Module.Finite (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k]) := Module.Finite.base_change _ _ _
  Module.Finite.of_surjective _
    (mapBaseChange_surjective k R (R ⧸ I) (Ideal.Quotient.algebraMap_surjective I))

/-- **The differentials of a principal quotient are free of rank one less.** Let `R` be a local
`k`-algebra whose module of differentials is finite free, and let `f : R` be a nonunit on which
some functional takes the differential `d f` to `1`. By
`KaehlerDifferential.ker_mapBaseChange_quotient`, `Ω_{(R/fR)/k}` is the fibre `R/fR ⊗_R Ω_{R/k}`
modulo the line spanned by `1 ⊗ d f`, and the base change of the functional splits that line
off. -/
private lemma free_and_finrank_kaehlerDifferential_quotient_span_singleton (k R : Type*) [Field k]
    [CommRing R] [Algebra k R] [IsLocalRing R] [Module.Free R Ω[R⁄k]] [Module.Finite R Ω[R⁄k]]
    {f : R} (hf : ¬ IsUnit f) (φ : Ω[R⁄k] →ₗ[R] R) (hφ : φ (D k R f) = 1) :
    Module.Free (R ⧸ Ideal.span ({f} : Set R)) Ω[R ⧸ Ideal.span ({f} : Set R)⁄k] ∧
      finrank (R ⧸ Ideal.span ({f} : Set R)) Ω[R ⧸ Ideal.span ({f} : Set R)⁄k] + 1
        = finrank R Ω[R⁄k] := by
  have : IsLocalRing (R ⧸ Ideal.span ({f} : Set R)) := isLocalRing_quotient_span_singleton hf
  have : Module.Finite (R ⧸ Ideal.span ({f} : Set R))
      ((R ⧸ Ideal.span ({f} : Set R)) ⊗[R] Ω[R⁄k]) := Module.Finite.base_change _ _ _
  obtain ⟨hfree, hrank⟩ := free_and_finrank_quotient_span_singleton_of_apply_eq_one
    (φ := (AlgebraTensorModule.rid R (R ⧸ Ideal.span ({f} : Set R))
        (R ⧸ Ideal.span ({f} : Set R))).toLinearMap ∘ₗ
      LinearMap.baseChange (R ⧸ Ideal.span ({f} : Set R)) φ)
    (x := (1 : R ⧸ Ideal.span ({f} : Set R)) ⊗ₜ[R] D k R f)
    (by simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.baseChange_tmul, hφ, AlgebraTensorModule.rid_tmul, one_smul])
  have e : Ω[R ⧸ Ideal.span ({f} : Set R)⁄k] ≃ₗ[R ⧸ Ideal.span ({f} : Set R)]
      ((R ⧸ Ideal.span ({f} : Set R)) ⊗[R] Ω[R⁄k]) ⧸
        ((R ⧸ Ideal.span ({f} : Set R)) ∙ (1 : R ⧸ Ideal.span ({f} : Set R)) ⊗ₜ[R] D k R f) :=
    ((Submodule.quotEquivOfEq _ _
      (KaehlerDifferential.ker_mapBaseChange_quotient k R _ (f := f) rfl).symm).trans
      (LinearMap.quotKerEquivOfSurjective _ (mapBaseChange_surjective k R _
        (Ideal.Quotient.algebraMap_surjective _)))).symm
  refine ⟨Module.Free.of_equiv e.symm, ?_⟩
  rw [e.finrank_eq, hrank]
  exact Module.finrank_baseChange ..

/-- Conormal injectivity for a formally smooth quotient, with no
formal-smoothness assumption on the source algebra. Adapted from Stacks
`RingTheory/Smooth/Conormal.lean`, lines 1110–1120 (06A6/06A8). -/
private theorem conormal_injective_of_formallySmooth (R P S : Type*)
    [CommRing R] [CommRing P] [CommRing S] [Algebra R P] [Algebra P S] [Algebra R S]
    [IsScalarTower R P S] [Algebra.FormallySmooth R S]
    (hf : Function.Surjective (algebraMap P S)) :
    Function.Injective (kerCotangentToTensor R P S) := by
  let f : P →ₐ[R] S := IsScalarTower.toAlgHom R P S
  have hs : Function.Surjective f.kerSquareLift :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hf
  have hn : IsNilpotent (RingHom.ker f.kerSquareLift) :=
    f.ker_kerSquareLift ▸ ⟨2, Ideal.cotangentIdeal_square _⟩
  let g := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R S) f.kerSquareLift hs hn
  have hg : f.kerSquareLift.comp g = AlgHom.id R S :=
    Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id R S) f.kerSquareLift hs hn
  let p := (retractionKerCotangentToTensorEquivSection hf).symm ⟨g, hg⟩
  exact Function.LeftInverse.injective (g := p.1) (LinearMap.congr_fun p.2)

/-- **Stacks 00TU**, in the form the induction uses. Let `R` be a local `k`-algebra with a
surjection onto a field `κ` which is a finitely generated separable extension of `k`. If `f ∈ 𝔪`
has nonzero class in `𝔪/𝔪²`, then `1 ⊗ d f` is nonzero in the fibre `κ ⊗_R Ω_{R/k}`. -/
private lemma one_tmul_D_ne_zero_of_notMem_sq (k R κ : Type*) [Field k] [CommRing R] [Algebra k R]
    [IsLocalRing R] [Field κ] [Algebra R κ] [Algebra k κ] [IsScalarTower k R κ]
    [Algebra.FormallySmooth k κ]
    (hsurj : Function.Surjective (algebraMap R κ)) {f : R} (hfm : f ∈ maximalIdeal R)
    (hfm2 : f ∉ maximalIdeal R ^ 2) : (1 : κ) ⊗ₜ[R] D k R f ≠ 0 := by
  have hker := IsLocalRing.ker_eq_maximalIdeal _ hsurj
  have hfk : f ∈ RingHom.ker (algebraMap R κ) := hker ▸ hfm
  intro hc
  have h0 : (RingHom.ker (algebraMap R κ)).toCotangent ⟨f, hfk⟩ = 0 := by
    refine (conormal_injective_of_formallySmooth k R κ hsurj) ?_
    rw [map_zero, kerCotangentToTensor_toCotangent]
    exact hc
  have h1 : f ∈ RingHom.ker (algebraMap R κ) ^ 2 := (Ideal.toCotangent_eq_zero _ _).mp h0
  exact hfm2 (hker ▸ h1)

/-- Two ideals containing `I` with the same image in `R ⧸ I` are equal. -/
private lemma Ideal.eq_of_map_quotientMk_eq {R : Type*} [CommRing R] {I J K : Ideal R}
    (hJ : I ≤ J) (hK : I ≤ K)
    (h : J.map (Ideal.Quotient.mk I) = K.map (Ideal.Quotient.mk I)) : J = K := by
  have h' := congrArg (Ideal.comap (Ideal.Quotient.mk I)) h
  rwa [Ideal.comap_map_quotientMk, Ideal.comap_map_quotientMk, sup_eq_right.mpr hJ,
    sup_eq_right.mpr hK] at h'

/-- An element `f` of an ideal `J` of a Noetherian ring, together with lifts of a minimal system of
generators of `J/(f)`, generates `J`; so `J` needs at most one generator more than its image in
`R/(f)`. -/
private lemma Ideal.spanFinrank_le_spanFinrank_map_quotient_add_one
    {R : Type*} [CommRing R] [IsNoetherianRing R] {f : R} {J : Ideal R} (hf : f ∈ J) :
    J.spanFinrank ≤ (J.map (Ideal.Quotient.mk (Ideal.span {f}))).spanFinrank + 1 := by
  classical
  obtain ⟨t, hcard, hspan⟩ := (IsNoetherian.noetherian (J.map
    (Ideal.Quotient.mk (Ideal.span ({f} : Set R))))).exists_span_finset_card_eq_spanFinrank
  set g : R ⧸ Ideal.span ({f} : Set R) → R :=
    Function.surjInv Ideal.Quotient.mk_surjective with hg
  have hgspec : ∀ y, Ideal.Quotient.mk (Ideal.span ({f} : Set R)) (g y) = y :=
    Function.surjInv_eq Ideal.Quotient.mk_surjective
  have hf0 : Ideal.Quotient.mk (Ideal.span ({f} : Set R)) f = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
  set u : Set R := insert f (g '' (t : Set (R ⧸ Ideal.span ({f} : Set R)))) with hu
  have hIJ : Ideal.span ({f} : Set R) ≤ J := by simpa [Ideal.span_le] using hf
  have hIu : Ideal.span ({f} : Set R) ≤ Ideal.span u := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hspanu : Ideal.span u = J := by
    refine Ideal.eq_of_map_quotientMk_eq hIu hIJ ?_
    rw [hu, Ideal.map_span, ← hspan, Set.image_insert_eq, Set.image_image]
    simp only [hgspec, Set.image_id', hf0]
    change Submodule.span (R ⧸ Ideal.span ({f} : Set R))
        (insert 0 (t : Set (R ⧸ Ideal.span ({f} : Set R))))
      = Submodule.span (R ⧸ Ideal.span ({f} : Set R))
        (t : Set (R ⧸ Ideal.span ({f} : Set R)))
    rw [Submodule.span_insert_zero]
  calc J.spanFinrank = (Ideal.span u).spanFinrank := by rw [hspanu]
    _ ≤ u.ncard := Submodule.spanFinrank_span_le_ncard_of_finite
        (Set.Finite.insert f (t.finite_toSet.image g))
    _ ≤ (g '' (t : Set (R ⧸ Ideal.span ({f} : Set R)))).ncard + 1 := Set.ncard_insert_le _ _
    _ ≤ t.card + 1 := by
        gcongr
        exact (Set.ncard_image_le t.finite_toSet).trans (by simp)
    _ = _ := by rw [hcard]

/-- **Stacks 00NU.** If `f` is a nonzerodivisor in the maximal ideal of a Noetherian local ring `R`
and `R/fR` is a regular local ring, then so is `R`: the maximal ideal of `R` needs at most one
generator more than that of `R/fR`, and the Krull dimension drops by exactly one. -/
private lemma isRegularLocalRing_of_isRegularLocalRing_quotient_span_singleton
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {f : R}
    (hreg : f ∈ nonZeroDivisors R) (hfm : f ∈ maximalIdeal R)
    (h : IsRegularLocalRing (R ⧸ Ideal.span {f})) : IsRegularLocalRing R := by
  have := h
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  have h1 := Ideal.spanFinrank_le_spanFinrank_map_quotient_add_one (f := f) hfm
  rw [IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at h1
  calc ((maximalIdeal R).spanFinrank : WithBot ℕ∞)
      ≤ (((maximalIdeal (R ⧸ Ideal.span ({f} : Set R))).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast h1
    _ = ringKrullDim (R ⧸ Ideal.span ({f} : Set R)) + 1 := by
        push_cast [← h.spanFinrank_maximalIdeal]; rfl
    _ = ringKrullDim R :=
        ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hreg hfm

/-- **Stacks 00TX, (2) ⇒ (3).** Let `k` be a field of characteristic zero and `κ` a field which is
essentially of finite type over `k`. A Noetherian local `k`-algebra with residue field `κ` whose
module of differentials over `k` is finite free is a regular local ring. The proof is the source's
induction on the rank of the differentials. -/
theorem isRegularLocalRing_of_free_kaehlerDifferential
    (k : Type u) [Field k] [CharZero k] (κ : Type v) [Field κ] [Algebra k κ]
    [Algebra.EssFiniteType k κ] (n : ℕ) :
    ∀ (R : Type w) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra k R] [Algebra R κ]
      [IsScalarTower k R κ] [Module.Free R Ω[R⁄k]] [Module.Finite R Ω[R⁄k]],
      Function.Surjective (algebraMap R κ) → finrank R Ω[R⁄k] = n → IsRegularLocalRing R := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R _ _ _ _ _ _ _ _ hsurj hn
  by_cases hm : maximalIdeal R = ⊥
  · have hfield : IsField R := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm
    let _ := hfield.toField
    exact IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (by simp [hm])
  -- pick `f ∈ 𝔪` with nonzero class in `𝔪/𝔪²`, and a functional taking `d f` to `1`
  obtain ⟨f, hfm, hfm2⟩ := exists_mem_maximalIdeal_notMem_sq (R := R) hm
  have hfnu : ¬ IsUnit f := (mem_maximalIdeal f).mp hfm
  obtain ⟨φ, hφ⟩ := exists_apply_eq_one_of_tmul_ne_zero (κ := κ) hsurj
    (one_tmul_D_ne_zero_of_notMem_sq k R κ hsurj hfm hfm2)
  have hfreg : f ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_of_derivation_apply_eq_one (φ.compDer (D k R)) (by simpa using hφ)
  obtain ⟨hfree, hrank⟩ :=
    free_and_finrank_kaehlerDifferential_quotient_span_singleton k R hfnu φ hφ
  refine isRegularLocalRing_of_isRegularLocalRing_quotient_span_singleton hfreg hfm ?_
  -- the residue field of `R/fR` is again `κ`, so the induction hypothesis applies to it
  set I := Ideal.span ({f} : Set R) with hI
  have : IsLocalRing (R ⧸ I) := isLocalRing_quotient_span_singleton hfnu
  have : Module.Finite (R ⧸ I) Ω[R ⧸ I⁄k] := KaehlerDifferential.finite_quotient k R I
  have hIker : I ≤ RingHom.ker (algebraMap R κ) := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact (IsLocalRing.ker_eq_maximalIdeal _ hsurj).ge hfm
  let _ : Algebra (R ⧸ I) κ :=
    (Ideal.Quotient.lift I (algebraMap R κ) fun a ha => RingHom.mem_ker.mp (hIker ha)).toAlgebra
  have halg : ∀ a : R, algebraMap (R ⧸ I) κ (Ideal.Quotient.mk I a) = algebraMap R κ a :=
    fun _ => rfl
  have hsurj' : Function.Surjective (algebraMap (R ⧸ I) κ) := by
    intro y
    obtain ⟨a, rfl⟩ := hsurj y
    exact ⟨Ideal.Quotient.mk I a, halg a⟩
  have : IsScalarTower k (R ⧸ I) κ := IsScalarTower.of_algebraMap_eq fun c => by
    rw [← Ideal.Quotient.mk_algebraMap k I c, halg, IsScalarTower.algebraMap_apply k R κ]
  exact ih (finrank (R ⧸ I) Ω[R ⧸ I⁄k]) (by omega) (R ⧸ I) hsurj' rfl

/-- The characteristic-zero local smoothness criterion, with the hard 00TX
induction above and the existing Jacobian 00TV proof as the final edge. -/
theorem isSmoothAt_of_free_kaehlerDifferential
    {k S : Type*} [Field k] [CharZero k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (q : Ideal S) [q.IsPrime] (Sq : Type*) [CommRing Sq] [Algebra k Sq] [Algebra S Sq]
    [IsScalarTower k S Sq] [IsLocalization.AtPrime Sq q]
    [Module.Free Sq Ω[Sq⁄k]] : Algebra.IsSmoothAt k q := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have : IsLocalRing Sq := IsLocalization.AtPrime.isLocalRing Sq q
  have : IsNoetherianRing Sq := IsLocalization.isNoetherianRing q.primeCompl Sq inferInstance
  have : Module.Finite Sq Ω[Sq⁄k] :=
    Module.Finite.of_isLocalizedModule (S := q.primeCompl) (KaehlerDifferential.map k k S Sq)
  have : Algebra.EssFiniteType S Sq := Algebra.EssFiniteType.of_isLocalization Sq q.primeCompl
  have : Algebra.EssFiniteType k Sq := Algebra.EssFiniteType.comp k S Sq
  have : Algebra.EssFiniteType k (ResidueField Sq) :=
    Algebra.EssFiniteType.comp k Sq (ResidueField Sq)
  have hreg : IsRegularLocalRing Sq :=
    isRegularLocalRing_of_free_kaehlerDifferential k (ResidueField Sq)
      (finrank Sq Ω[Sq⁄k]) Sq Ideal.Quotient.mk_surjective rfl
  have : IsRegularLocalRing (Localization.AtPrime q) :=
    hreg.of_ringEquiv (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) Sq).symm.toRingEquiv
  have : Algebra.EssFiniteType S (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_isLocalization (Localization.AtPrime q) q.primeCompl
  have : Algebra.EssFiniteType k (Localization.AtPrime q) :=
    Algebra.EssFiniteType.comp k S (Localization.AtPrime q)
  have : Algebra.EssFiniteType k (ResidueField (Localization.AtPrime q)) :=
    Algebra.EssFiniteType.comp k (Localization.AtPrime q) (ResidueField (Localization.AtPrime q))
  exact _root_.Algebra.FormallySmooth.localization_of_isRegularLocalRing q

end ZInQ.Contrib.CloudB3W16Cartier

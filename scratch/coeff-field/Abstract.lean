import Mathlib

/-! Abstract glue: eigenvalues of operators preserving a spanning `F`-structure are algebraic of
bounded degree, jointly. -/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CoeffField

open Submodule

variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {ι : Type*}

/-- `v` has all coordinates `c i v` in `F`. -/
def IsRat (c : ι → V →ₗ[K] K) (v : V) : Prop := ∀ i, c i v ∈ Set.range (algebraMap F K)

section Inner

variable [Module F V] [IsScalarTower F K V]

variable (F) in
/-- The `F`-structure `W = {v | c_i v ∈ F ∀ i}`. -/
def ratPart (c : ι → V →ₗ[K] K) : Submodule F V where
  carrier := {v | IsRat (F := F) c v}
  zero_mem' := fun i => ⟨0, by simp⟩
  add_mem' := by
    rintro a b ha hb i
    obtain ⟨x, hx⟩ := ha i
    obtain ⟨y, hy⟩ := hb i
    exact ⟨x + y, by simp [hx, hy]⟩
  smul_mem' := by
    rintro r a ha i
    obtain ⟨x, hx⟩ := ha i
    refine ⟨r * x, ?_⟩
    rw [← algebraMap_smul K r a, map_smul, map_mul, hx, smul_eq_mul]

theorem exists_finset (c : ι → V →ₗ[K] K) (hc : ∀ v, (∀ i, c i v = 0) → v = 0) :
    ∃ s : Finset (Module.Dual K V), (↑s ⊆ Set.range c) ∧ ∀ v, (∀ φ ∈ s, φ v = 0) → v = 0 := by
  have hfg : (span K (Set.range c)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan⟩ := (fg_span_iff_fg_span_finset_subset _).1 hfg
  refine ⟨s, hs, fun v hv => hc v fun i => ?_⟩
  have hi : c i ∈ span K (s : Set (Module.Dual K V)) := hspan ▸ subset_span ⟨i, rfl⟩
  refine span_induction (p := fun φ _ => φ v = 0) (fun φ hφ => hv φ hφ) (by simp)
    (fun φ ψ _ _ h1 h2 => by simp [h1, h2]) (fun a φ _ h => by simp [h]) hi

theorem finiteDimensional_ratPart (c : ι → V →ₗ[K] K) (hc : ∀ v, (∀ i, c i v = 0) → v = 0) :
    FiniteDimensional F (ratPart F c) := by
  obtain ⟨s, hs, hinj⟩ := exists_finset c hc
  let P : (s → F) →ₗ[F] (s → K) := LinearMap.pi fun φ => (Algebra.linearMap F K).comp (LinearMap.proj φ)
  let E : ratPart F c →ₗ[F] (s → K) :=
    { toFun := fun w φ => (φ : Module.Dual K V) (w : V)
      map_add' := fun a b => by funext φ; simp
      map_smul' := fun r a => by
        funext φ
        simp only [SetLike.val_smul, Pi.smul_apply, RingHom.id_apply]
        rw [← algebraMap_smul K r (a : V), map_smul, smul_eq_mul, Algebra.smul_def] }
  have hE : ∀ w, E w ∈ LinearMap.range P := by
    intro w
    have h : ∀ φ : s, ∃ x : F, algebraMap F K x = (φ : Module.Dual K V) (w : V) := by
      intro φ
      obtain ⟨i, hi⟩ := hs φ.2
      rw [← hi]
      exact w.2 i
    choose x hx using h
    exact ⟨x, by funext φ; simp [P, E, hx]⟩
  let E' : ratPart F c →ₗ[F] LinearMap.range P := E.codRestrict _ hE
  have hinj' : Function.Injective E' := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h0 : ∀ φ ∈ s, φ (w : V) = 0 := fun φ hφ => by
      have := congrArg (fun z : LinearMap.range P => (z : s → K) ⟨φ, hφ⟩) hw
      simpa [E', E] using this
    exact Subtype.ext (hinj _ h0)
  exact Module.Finite.of_injective E' hinj'

/-- The stabilizer algebra: operators preserving `W` and having `f` as an eigenvector. -/
def stab (c : ι → V →ₗ[K] K) (f : V) : Subalgebra F (Module.End K V) where
  carrier := {T | (∀ w ∈ ratPart F c, T w ∈ ratPart F c) ∧ ∃ μ : K, T f = μ • f}
  mul_mem' := by
    rintro S T ⟨hS, μ, hμ⟩ ⟨hT, ν, hν⟩
    refine ⟨fun w hw => hS _ (hT w hw), μ * ν, ?_⟩
    rw [Module.End.mul_apply, hν, map_smul, hμ, smul_smul, mul_comm]
  add_mem' := by
    rintro S T ⟨hS, μ, hμ⟩ ⟨hT, ν, hν⟩
    exact ⟨fun w hw => add_mem (hS w hw) (hT w hw), μ + ν, by
      rw [LinearMap.add_apply, hμ, hν, add_smul]⟩
  algebraMap_mem' := by
    intro r
    refine ⟨fun w hw => ?_, algebraMap F K r, ?_⟩
    · rw [Module.algebraMap_end_apply]
      exact (ratPart F c).smul_mem r hw
    · rw [Module.algebraMap_end_apply, algebraMap_smul]

variable (c : ι → V →ₗ[K] K) {f : V}

theorem eigen_exists (T : stab (F := F) c f) : ∃ μ : K, (T : Module.End K V) f = μ • f := T.2.2

/-- The eigenvalue. -/
def lamFun (T : stab (F := F) c f) : K := (eigen_exists c T).choose

theorem lamFun_spec (T : stab (F := F) c f) : (T : Module.End K V) f = lamFun c T • f :=
  (eigen_exists c T).choose_spec

theorem lamFun_eq (hf : f ≠ 0) {T : stab (F := F) c f} {μ : K} (h : (T : Module.End K V) f = μ • f) :
    lamFun c T = μ :=
  smul_left_injective K hf ((lamFun_spec c T).symm.trans h)

/-- The eigencharacter `stab → K`. -/
def lam (hf : f ≠ 0) : stab (F := F) c f →ₐ[F] K where
  toFun := lamFun c
  map_one' := lamFun_eq c hf (by simp)
  map_mul' S T := lamFun_eq c hf (by
    change (S : Module.End K V) ((T : Module.End K V) f) = _
    rw [lamFun_spec c T, map_smul, lamFun_spec c S, smul_smul, mul_comm])
  map_zero' := lamFun_eq c hf (by simp)
  map_add' S T := lamFun_eq c hf (by
    change (S : Module.End K V) f + (T : Module.End K V) f = _
    rw [lamFun_spec c S, lamFun_spec c T, add_smul])
  commutes' r := lamFun_eq c hf (by
    change (algebraMap F (Module.End K V) r) f = _
    rw [Module.algebraMap_end_apply, algebraMap_smul])

theorem finiteDimensional_stab (hc : ∀ v, (∀ i, c i v = 0) → v = 0)
    (hspan : span K (ratPart F c : Set V) = ⊤) : FiniteDimensional F (stab (F := F) c f) := by
  haveI := finiteDimensional_ratPart (F := F) c hc
  let R : stab (F := F) c f →ₗ[F] Module.End F (ratPart F c) :=
    { toFun := fun T => ((T : Module.End K V).restrictScalars F).restrict T.2.1
      map_add' := fun S T => by ext w; rfl
      map_smul' := fun r T => by ext w; rfl }
  refine Module.Finite.of_injective R ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro T hT
  have hT0 : (T : Module.End K V) = 0 := by
    apply LinearMap.ext
    intro v
    have hv : v ∈ span K (ratPart F c : Set V) := hspan ▸ mem_top
    refine span_induction (p := fun v _ => (T : Module.End K V) v = (0 : Module.End K V) v)
      (fun w hw => ?_) (by simp) (fun a b _ _ h1 h2 => by simp_all) (fun a b _ h => by simp_all) hv
    have := LinearMap.congr_fun hT ⟨w, hw⟩
    exact congrArg Subtype.val this
  exact Subtype.ext (by simpa using hT0)

theorem finiteDimensional_range_lam (hf : f ≠ 0) (hc : ∀ v, (∀ i, c i v = 0) → v = 0)
    (hspan : span K (ratPart F c : Set V) = ⊤) : FiniteDimensional F (lam (F := F) c hf).range := by
  haveI := finiteDimensional_stab (F := F) (f := f) c hc hspan
  exact Module.Finite.of_surjective (lam (F := F) c hf).rangeRestrict.toLinearMap
    (AlgHom.rangeRestrict_surjective _)

end Inner

/-- **Main abstract glue.** -/
theorem finiteDimensional_adjoin_eigenvalues (c : ι → V →ₗ[K] K)
    (hc : ∀ v, (∀ i, c i v = 0) → v = 0)
    (hspan : span K {v | IsRat (F := F) c v} = ⊤) {f : V} (hf : f ≠ 0) (s : Set K)
    (hs : ∀ μ ∈ s, ∃ T : Module.End K V,
      (∀ v, IsRat (F := F) c v → IsRat (F := F) c (T v)) ∧ T f = μ • f) :
    FiniteDimensional F (Algebra.adjoin F s) := by
  letI : Module F V := Module.compHom V (algebraMap F K)
  haveI : IsScalarTower F K V := ⟨fun a b v => by
    change (a • b) • v = algebraMap F K a • b • v
    rw [Algebra.smul_def, mul_smul]⟩
  have hle : Algebra.adjoin F s ≤ (lam (F := F) c hf).range := by
    rw [Algebra.adjoin_le_iff]
    intro μ hμ
    obtain ⟨T, hT, hTf⟩ := hs μ hμ
    exact ⟨⟨T, fun w hw => hT w hw, μ, hTf⟩, lamFun_eq c hf hTf⟩
  haveI := finiteDimensional_range_lam (F := F) c hf hc hspan
  exact Submodule.finiteDimensional_of_le (show Subalgebra.toSubmodule (Algebra.adjoin F s) ≤
    Subalgebra.toSubmodule (lam (F := F) c hf).range from hle)

end CoeffField

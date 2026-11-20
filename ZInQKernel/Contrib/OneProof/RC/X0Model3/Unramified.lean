import Mathlib.RingTheory.RingHom.Etale
import Mathlib.Analysis.Complex.Basic

/-! Local uniqueness of complex evaluations over an unramified algebra
coordinate (tex 2915–2919, on the spot, provenance (c)). -/

noncomputable section

open Algebra Filter Topology
open scoped TensorProduct

namespace ZInQ.Manuscript.RC.X0Model3

private def pairEval {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (f g : A →+* ℂ) (h : f.comp (algebraMap R A) = g.comp (algebraMap R A)) :
    A ⊗[R] A →+* ℂ :=
  letI := (f.comp (algebraMap R A)).toAlgebra
  (Algebra.TensorProduct.lift (S := R)
    (⟨f, fun _ => rfl⟩ : A →ₐ[R] ℂ)
    (⟨g, fun r => (DFunLike.congr_fun h r).symm⟩ : A →ₐ[R] ℂ)
    (fun _ _ => Commute.all _ _)).toRingHom

@[simp] private theorem pairEval_tmul {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (f g : A →+* ℂ) (h : f.comp (algebraMap R A) = g.comp (algebraMap R A)) (a b : A) :
    pairEval f g h (a ⊗ₜ[R] b) = f a * g b := rfl

private theorem pairEval_self {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (f : A →+* ℂ) (d : A ⊗[R] A) :
    pairEval f f rfl d = f (Algebra.TensorProduct.lmul' R d) := by
  refine TensorProduct.inductionOn d (fun a b => ?_) (fun a b ha hb => ?_)
  · simp
  · simp [ha, hb]

private theorem continuousPairTest {R A P Q : Type} [CommRing R] [CommRing A]
    [Algebra R A] [TopologicalSpace P] [TopologicalSpace Q]
    (f : P → A →+* ℂ) (g : Q → A →+* ℂ) (p : P) (q : Q)
    (hf : ∀ a, ContinuousAt (fun x => f x a) p)
    (hg : ∀ a, ContinuousAt (fun y => g y a) q) (d : A ⊗[R] A) :
    ∃ v : P × Q → ℂ, ContinuousAt v (p, q) ∧
      ∀ x y (h : (f x).comp (algebraMap R A) = (g y).comp (algebraMap R A)),
        v (x, y) = pairEval (f x) (g y) h d := by
  refine TensorProduct.inductionOn d (fun a b => ?_) (fun a b ha hb => ?_)
  · have h₁ : ContinuousAt (fun z : P × Q => f z.1 a) (p, q) :=
      by
        change ContinuousAt ((fun x : P => f x a) ∘ Prod.fst) (p, q)
        exact ContinuousAt.comp (x := (p, q)) (hf a) continuousAt_fst
    have h₂ : ContinuousAt (fun z : P × Q => g z.2 b) (p, q) :=
      by
        change ContinuousAt ((fun y : Q => g y b) ∘ Prod.snd) (p, q)
        exact ContinuousAt.comp (x := (p, q)) (hg b) continuousAt_snd
    exact ⟨fun z => f z.1 a * g z.2 b, h₁.mul h₂, fun _ _ _ => rfl⟩
  ·
    obtain ⟨va, hca, hva⟩ := ha
    obtain ⟨vb, hcb, hvb⟩ := hb
    exact ⟨fun z => va z + vb z, hca.add hcb, fun x y h => by
      simpa only [map_add] using congrArg₂ (· + ·) (hva x y h) (hvb x y h)⟩

/-- Near a common complex evaluation, two continuous families of evaluations of an
unramified algebra coincide whenever they agree on the base algebra. Continuity is
needed only at the centers and for the values of regular functions. -/
theorem eventually_eq_of_unramified {R A P Q : Type} [CommRing R] [CommRing A]
    [Algebra R A] [EssFiniteType R A] [FormallyUnramified R A]
    [TopologicalSpace P] [TopologicalSpace Q]
    (f : P → A →+* ℂ) (g : Q → A →+* ℂ) (p : P) (q : Q)
    (hf : ∀ a, ContinuousAt (fun x => f x a) p)
    (hg : ∀ a, ContinuousAt (fun y => g y a) q) (h₀ : f p = g q) :
    ∃ U ∈ 𝓝 p, ∃ V ∈ 𝓝 q, ∀ x ∈ U, ∀ y ∈ V,
      (f x).comp (algebraMap R A) = (g y).comp (algebraMap R A) → f x = g y := by
  obtain ⟨e, he, hspan⟩ :
      ∃ e : A ⊗[R] A, IsIdempotentElem e ∧
        KaehlerDifferential.ideal R A = Ideal.span {e} :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg R A)).mp
      ((Ideal.cotangent_subsingleton_iff _).mp
        (inferInstanceAs (Subsingleton Ω[A⁄R])))
  have hem : Algebra.TensorProduct.lmul' R e = 0 :=
    RingHom.mem_ker.mp (show e ∈ KaehlerDifferential.ideal R A by
      rw [hspan]
      exact Ideal.mem_span_singleton_self e)
  obtain ⟨v, hv, hval⟩ := continuousPairTest f g p q hf hg (1 - e)
  have hcenter : v (p, q) = 1 := by
    rw [hval p q (congrArg (fun k : A →+* ℂ => k.comp (algebraMap R A)) h₀)]
    simp only [← h₀, pairEval_self, map_sub, map_one, hem, map_zero, sub_zero]
  have hnear : ∀ᶠ z in 𝓝 (p, q), v z ≠ 0 :=
    hv.eventually (eventually_ne_nhds (hcenter ▸ one_ne_zero))
  rw [nhds_prod_eq] at hnear
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp hnear
  refine ⟨U, hU, V, hV, fun x hx y hy h => ?_⟩
  let k := pairEval (f x) (g y) h
  have hk : k (1 - e) ≠ 0 := (hval x y h) ▸ hUV (show (x, y) ∈ U ×ˢ V from ⟨hx, hy⟩)
  have he0 : k e = 0 := by
    have hm : k ((1 - e) * e) = 0 := by
      rw [sub_mul, one_mul, he.eq, sub_self, map_zero]
    rw [map_mul] at hm
    exact (mul_eq_zero.mp hm).resolve_left hk
  ext a
  have ha : (1 : A) ⊗ₜ[R] a - a ⊗ₜ[R] (1 : A) ∈ Ideal.span {e} :=
    hspan ▸ KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R a
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
  have hzero := congrArg k hb
  change k _ = k _ at hzero
  rw [map_mul, he0, zero_mul] at hzero
  exact (sub_eq_zero.mp (by simpa [k] using hzero)).symm


end ZInQ.Manuscript.RC.X0Model3

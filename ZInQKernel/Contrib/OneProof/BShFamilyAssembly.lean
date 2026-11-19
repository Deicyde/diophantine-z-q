import ZInQKernel.Contrib.OneProof.BShTraces
import ZInQKernel.Contrib.OneProof.BShFamilyKernels

/-! ON THE SPOT (provenance (c)): simultaneous local matches of the
algebraic Vélu pairs give model embeddings, and automorphisms permute
the embeddings via their action on kernels. -/

noncomputable section

namespace BShFamily

open BShTraces BShStandard ShimuraPointDict AfTateLam LeafModCurves PkgI3 PkgI3.AbVar
open AlgebraicGeometry CategoryTheory UpperHalfPlane Filter WeierstrassCurve
open scoped MatrixGroups Topology

variable {X : Over SpecQ} [IsIntegral X.left] {J : AbVar ℚ}
variable {N p : ℕ} {jX tX : X.left.functionField}
local notation "K" => X.left.functionField

/-- The same puncture-preserving comparison identifies both components
of an algebraic pair with the coordinates of a branch. -/
def PairedGerms {L : Type*} [Field L] (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX)
    (τ s : ℍ) (u : L →+* MeromorphicGerm (τ : ℂ)) (r : L × L) : Prop :=
  ∃ (f : ℂ → ℂ) (hf : Tendsto f (𝓝[≠] (τ : ℂ)) (𝓝[≠] (s : ℂ))),
    meromorphicIncl _ (u r.1) = pullGerm f hf (fieldGerm hN hG s jX) ∧
    meromorphicIncl _ (u r.2) = pullGerm f hf (fieldGerm hN hG s tX)

/-- A simultaneous germ comparison gives both implications between the
polynomial relations, hence an embedding of the fixed model field. -/
theorem exists_embedding_of_pairedGerms {L : Type*} [Field L]
    (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX)
    {τ s : ℍ} {u : L →+* MeromorphicGerm (τ : ℂ)} {r : L × L}
    (h : PairedGerms hN hG τ s u r) :
    ∃ b : K →+* L, b jX = r.1 ∧ b tX = r.2 := by
  obtain ⟨f,hf,hj,ht⟩ := h
  let v := (pullGerm f hf).comp (fieldGerm hN hG s)
  let m := (meromorphicIncl _).comp u
  apply exists_ringHom_of_pair_relations hG.1
  intro P
  have hej : m r.1 = v jX := hj
  have het : m r.2 = v tX := ht
  have he : m (AfTateOr.ev2 P r.1 r.2) = v (AfTateOr.ev2 P jX tX) := by
    rw [AfTateOr.map_ev2, AfTateOr.map_ev2, hej, het]
  constructor
  · intro hp
    apply m.injective
    rw [he, hp, map_zero, map_zero]
  · intro hp
    apply v.injective
    rw [← he, hp, map_zero, map_zero]

/-- If the surviving multiset kernels of the normalized model can be
matched at each parameter, then their algebraic Vélu pairs provide the
entire Galois family required by the prime trace theorem. -/
theorem primeTrace_of_kernel_profiles
    (hN : 2 ≤ N) (hp : p.Prime) (hC : IsCurve X) (hG : IsX1Gen N X jX tX) (aj : X ⟶ J.X)
    {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (W : WeierstrassCurve K) (x : K)
    (h : let U := Kernel (W.map (algebraMap K L)) p N (algebraMap K L x)
      let r (i : U) := veluPair (algebraMap K L W.a₄) (algebraMap K L W.a₆)
        (algebraMap K L x) i.val
      ∀ τ : ℍ, ∃ (u : L →+* MeromorphicGerm (τ : ℂ)) (e : PrimeBranch N p ≃ U),
        ((meromorphicIncl _).comp u).comp (algebraMap K L) = fieldGerm hN hG τ ∧
        (∀ i : Fin p, PairedGerms hN hG τ (shiftDiv p i τ) u (r (e (.inl i)))) ∧
        (∀ (i : {u : Unit // ¬ p ∣ N}) (g : SL(2, ℤ)), (N : ℤ) ∣ g 1 0 →
          (g 1 1 : ZMod N) = (p : ZMod N) →
          PairedGerms hN hG τ (g • mulNat p τ) u (r (e (.inr i))))) :
    ∃ F : X ⟶ J.X, IsPrimeTrace jX tX aj N p F := by
  classical
  let U := Kernel (W.map (algebraMap K L)) p N (algebraMap K L x)
  let r (i : U) := veluPair (algebraMap K L W.a₄) (algebraMap K L W.a₆)
    (algebraMap K L x) i.val
  obtain ⟨u₀, e₀, _, ht₀, hh₀⟩ := h UpperHalfPlane.I
  have ex (i : PrimeBranch N p) :
      ∃ b : K →+* L, b jX = (r (e₀ i)).1 ∧ b tX = (r (e₀ i)).2 := by
    cases i with
    | inl i => exact exists_embedding_of_pairedGerms hN hG (ht₀ i)
    | inr i =>
      obtain ⟨g,hg,hd⟩ := HeckePin.exists_gamma_prime N ⟨p,hp⟩ i.property
      exact exists_embedding_of_pairedGerms hN hG (hh₀ i g hg hd)
  choose b hb using ex
  refine exists_primeTrace_of_coordinate_germs hN hC hG aj b ?_ ?_
  · intro σ
    let P := kernelPerm σ W p N x
    let π := (e₀.trans P).trans e₀.symm
    have hπ (i : PrimeBranch N p) : e₀ (π i) = P (e₀ i) := e₀.apply_symm_apply _
    refine ⟨π, fun i => ringHom_eq_of_generators hG.1 _ _ ?_ ?_⟩
    · have he := congrArg Prod.fst (map_veluPair_kernelPerm σ W p N x (e₀ i))
      simp only [RingHom.comp_apply, hb, hπ]
      exact he
    · have he := congrArg Prod.snd (map_veluPair_kernelPerm σ W p N x (e₀ i))
      simp only [RingHom.comp_apply, hb, hπ]
      exact he
  · intro τ
    obtain ⟨u,e,hu,ht,hh⟩ := h τ
    let π := e.trans e₀.symm
    have hp' (i : PrimeBranch N p) : e₀ (π i) = e i := e₀.apply_symm_apply _
    refine ⟨u, π, hu, ?_, ?_⟩
    · intro i
      simp only [(hb _).1, (hb _).2, hp']
      exact ht i
    · intro i g hg hd
      simp only [(hb _).1, (hb _).2, hp']
      exact hh i g hg hd

#print axioms exists_embedding_of_pairedGerms
#print axioms primeTrace_of_kernel_profiles

end BShFamily

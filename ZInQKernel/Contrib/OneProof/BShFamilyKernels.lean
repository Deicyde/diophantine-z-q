import ZInQKernel.Contrib.OneProof.BShTracesVelu
import ZInQKernel.Contrib.OneProof.BShFamilyTorsion

/-! ON THE SPOT (provenance (c)): encode a prime kernel by the multiset
of x-coordinates of its nonzero elements. This is the correct weight
for the short Vélu sums and works for the prime two. -/

noncomputable section

namespace BShFamily

open BShTraces WeierstrassCurve Polynomial

/-- Every nonzero element is counted once, so opposite pairs may have equal
x-coordinates, but a nonzero element of order two is counted only once. -/
def cluster {F : Type*} [Field F] (E : WeierstrassCurve F) (p : ℕ) (r : F) :
    Multiset F :=
  (Finset.univ : Finset (Multiple p)).val.map (fun k => mulX E k.val.val r)

theorem map_cluster {F E : Type*} [Field F] [Field E] (f : F →+* E)
    (W : WeierstrassCurve F) (p : ℕ) (r : F) :
    (cluster W p r).map f = cluster (W.map f) p (f r) := by
  simp only [cluster, Multiset.map_map, Function.comp_def, map_mulX]

/-- A surviving cluster is the cluster of some division root, with the
marked order-p point excluded when the prime divides the level. -/
def Survives {F : Type*} [Field F] (E : WeierstrassCurve F)
    (p N : ℕ) (x : F) (S : Multiset F) : Prop :=
  (∃ r : F, (E.ΨSq p).eval r = 0 ∧ S = cluster E p r) ∧
    (¬ p ∣ N ∨ mulX E (N / p : ℕ) x ∉ S)

/-- The branch index remembers the kernel even when two pairs of target
coordinates agree. -/
def Kernel {F : Type*} [Field F] (E : WeierstrassCurve F)
    (p N : ℕ) (x : F) :=
  {S : Multiset F // Survives E p N x S}

/-- Functoriality of the mark test and cluster for an automorphism over the
short coefficients and marked coordinate. -/
theorem survives_map {F E : Type*} [Field F] [Field E] (f : F →+* E)
    {W : WeierstrassCurve F} {p N : ℕ} {x : F} {S : Multiset F}
    (h : Survives W p N x S) : Survives (W.map f) p N (f x) (S.map f) := by
  obtain ⟨⟨r, hr, rfl⟩, h⟩ := h
  refine ⟨⟨f r, ?_, map_cluster f W p r⟩, ?_⟩
  · rw [map_ΨSq, eval_map, eval₂_at_apply, hr, map_zero]
  · refine h.imp_right fun h hmem => h ?_
    rw [← map_mulX, Multiset.mem_map] at hmem
    obtain ⟨y, hy, he⟩ := hmem
    exact (f.injective he) ▸ hy

/-- The automorphism action on surviving kernels is a permutation, before
any evaluation of quotient coordinates. -/
def kernelPerm {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (W : WeierstrassCurve K) (p N : ℕ) (x : K) :
    Equiv.Perm (Kernel (W.map (algebraMap K F)) p N (algebraMap K F x)) where
  toFun S := ⟨S.val.map σ, by
    have h := survives_map (σ : F →+* F) S.property
    have hx : (σ : F →+* F) (algebraMap K F x) = algebraMap K F x := σ.commutes x
    rwa [WeierstrassCurve.map_map, show (σ : F →+* F).comp (algebraMap K F) =
      algebraMap K F from RingHom.ext σ.commutes, hx] at h⟩
  invFun S := ⟨S.val.map σ.symm, by
    have h := survives_map (σ.symm : F →+* F) S.property
    have hx : (σ.symm : F →+* F) (algebraMap K F x) = algebraMap K F x := σ.symm.commutes x
    rwa [WeierstrassCurve.map_map, show (σ.symm : F →+* F).comp (algebraMap K F) =
      algebraMap K F from RingHom.ext σ.symm.commutes, hx] at h⟩
  left_inv S := Subtype.ext (by simp [Multiset.map_map, Function.comp_def])
  right_inv S := Subtype.ext (by simp [Multiset.map_map, Function.comp_def])

/-- The simultaneous algebraic Vélu pair from the cluster of a surviving
kernel and the source mark. -/
def veluPair {F : Type*} [Field F] (a b x : F) (S : Multiset F) : F × F :=
  shortCoordinates (a - 5 * (S.map (shortT a)).sum)
    (b - 7 * (S.map (shortW a b)).sum)
    (x + (S.map (shortShift a b x)).sum)

theorem map_veluPair {F E : Type*} [Field F] [Field E] (f : F →+* E)
    (a b x : F) (S : Multiset F) :
    Prod.map f f (veluPair a b x S) = veluPair (f a) (f b) (f x) (S.map f) := by
  have hT (t : F) : f (shortT a t) = shortT (f a) (f t) := by
    simp only [shortT, map_add, map_mul, map_pow, map_ofNat]
  have hW (t : F) : f (shortW a b t) = shortW (f a) (f b) (f t) := by
    simp only [shortW, map_add, map_mul, map_pow, map_ofNat]
  have hS (t : F) : f (shortShift a b x t) = shortShift (f a) (f b) (f x) (f t) := by
    simp only [shortShift, hT, map_add, map_sub, map_mul, map_pow, map_div₀, map_ofNat]
  apply Prod.ext <;>
    simp only [veluPair, shortCoordinates, Prod.map_fst, Prod.map_snd, map_div₀, map_mul,
      map_add, map_sub, map_neg, map_pow, map_ofNat, map_multiset_sum, Multiset.map_map,
      Function.comp_def, hT, hW, hS]

theorem map_veluPair_kernelPerm {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (W : WeierstrassCurve K) (p N : ℕ) (x : K)
    (S : Kernel (W.map (algebraMap K F)) p N (algebraMap K F x)) :
    let a := algebraMap K F W.a₄
    let b := algebraMap K F W.a₆
    let y := algebraMap K F x
    Prod.map σ σ (veluPair a b y S.val) =
      veluPair a b y (kernelPerm σ W p N x S).val := by
  have hh (a : K) : (σ : F →+* F) (algebraMap K F a) = algebraMap K F a := σ.commutes a
  have h := map_veluPair (σ : F →+* F) (algebraMap K F W.a₄) (algebraMap K F W.a₆)
    (algebraMap K F x) S.val
  simp only [hh] at h
  exact h

#print axioms map_cluster
#print axioms survives_map
#print axioms map_veluPair
#print axioms map_veluPair_kernelPerm

end BShFamily

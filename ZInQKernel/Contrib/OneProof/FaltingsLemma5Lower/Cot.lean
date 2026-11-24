import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower.CotPts

/-! faltings5-lower, part 9: `IsogCotBijective` from Milne's quasi-inverse.

If `f^* : ω_B → ω_A` (cotangent spaces at the origin of the generic fibres) were not onto, a nonzero
functional vanishing on its image gives a derivation `D` of `𝒪_{𝒢,ξ}` at the origin, killing `𝓞_K`
and `f^*(𝒪_{𝒩,ξ})`: a tangent vector `v` of `A` (`Spec K[ε] → A`, through `Spec 𝒪_{𝒢,ξ}` and `theta`)
with `v ≫ φ = 1`. With Milne's `ψ`, `φ ≫ ψ = [d]`, `v ≫ [d] = 1`, so `v = 1` in characteristic `0`
(`ZInQ.Contrib.AbVarBC.Tangent.eq_one_of_comp_intCast`) and `D = 0`. Both cotangent spaces have
dimension `dim A = dim B` (kernel `TangentDim`), so `f^*` is bijective. -/

set_option linter.style.haveILetI false

namespace GapHeight

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Contrib.AbVarBC.Tangent TrivSqZeroExt

section Sec

variable {K : Type} [Field K] [NumberField K] {A B : PkgI3.AbVar K}

/-- `K → 𝒪_{𝒢,ξ}` extending the structure map (nonzero elements of `𝓞_K` are units at `ξ`). -/
noncomputable def jA (𝒢 : GroupModel A K) : K →+* 𝒢.genStalk :=
  IsLocalization.lift (M := nonZeroDivisors (𝓞 K)) (S := K) (g := 𝒢.structMap)
    (fun y => ZInQ.DefFaltings.HodgeLattice.isUnit_structMap 𝒢 (nonZeroDivisors.ne_zero y.2))

theorem jA_alg (𝒢 : GroupModel A K) (c : 𝓞 K) :
    jA 𝒢 (algebraMap (𝓞 K) K c) = 𝒢.structMap c :=
  IsLocalization.lift_eq _ _

theorem εMap_structMap (𝒢 : GroupModel A K) (c : 𝓞 K) :
    (εMap 𝒢).hom (𝒢.structMap c) = algebraMap (𝓞 K) K c := by
  have := congrArg (fun g => g.hom c) (structMap_εMap 𝒢)
  exact this

theorem εMap_jA (𝒢 : GroupModel A K) (k : K) : (εMap 𝒢).hom (jA 𝒢 k) = k := by
  have h : (εMap 𝒢).hom.comp (jA 𝒢) = RingHom.id K := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K))
    ext c
    simp only [RingHom.comp_apply, jA_alg, RingHom.id_apply]
    exact εMap_structMap 𝒢 c
  exact RingHom.congr_fun h k

theorem genMap_jA (𝒢 : GroupModel A K) (𝒩 : GroupModel B K) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (k : K) : (genMap 𝒢 𝒩 f).hom (jA 𝒩 k) = jA 𝒢 k := by
  have h : (genMap 𝒢 𝒩 f).hom.comp (jA 𝒩) = jA 𝒢 := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K))
    ext c
    simp only [RingHom.comp_apply, jA_alg]
    exact genMap_structMap 𝒢 𝒩 f c
  exact RingHom.congr_fun h k

theorem mem_max_of_εMap (𝒢 : GroupModel A K) {r : 𝒢.genStalk} (h : (εMap 𝒢).hom r = 0) :
    r ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := hu.map (εMap 𝒢).hom
  rw [h] at this
  exact not_isUnit_zero this

theorem sub_mem_max (𝒢 : GroupModel A K) (r : 𝒢.genStalk) :
    r - jA 𝒢 ((εMap 𝒢).hom r) ∈ IsLocalRing.maximalIdeal 𝒢.genStalk :=
  mem_max_of_εMap 𝒢 (by rw [map_sub, εMap_jA, sub_self])

/-- The cotangent space as a `K`-vector space (through `jA`). -/
def cotK (𝒢 : GroupModel A K) : Type := 𝒢.cotangent

noncomputable instance (𝒢 : GroupModel A K) : AddCommGroup (cotK 𝒢) :=
  inferInstanceAs (AddCommGroup 𝒢.cotangent)

noncomputable instance (𝒢 : GroupModel A K) : Module K (cotK 𝒢) :=
  Module.compHom 𝒢.cotangent (jA 𝒢)

theorem cotK_smul (𝒢 : GroupModel A K) (k : K) (x : cotK 𝒢) :
    k • x = (show 𝒢.cotangent from (jA 𝒢 k • (show 𝒢.cotangent from x))) := rfl

/-- `f^*` is semilinear along `genMap`. -/
theorem cotMap_smul (𝒢 : GroupModel A K) (𝒩 : GroupModel B K) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (r : 𝒩.genStalk) (x : 𝒩.cotangent) :
    cotMap 𝒢 𝒩 f (r • x) = (genMap 𝒢 𝒩 f).hom r • cotMap 𝒢 𝒩 f x := by
  obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ x
  have hsm : r • (Ideal.toCotangent (IsLocalRing.maximalIdeal 𝒩.genStalk) m : 𝒩.cotangent) =
      Ideal.toCotangent _ (r • m) :=
    ((Ideal.toCotangent (IsLocalRing.maximalIdeal 𝒩.genStalk)).map_smul r m).symm
  erw [hsm]
  let ψ := (genMap 𝒢 𝒩 f).hom.toIntAlgHom
  have h : IsLocalRing.maximalIdeal 𝒩.genStalk ≤
      (IsLocalRing.maximalIdeal 𝒢.genStalk).comap ψ :=
    fun t ht => genMap_mem_maximalIdeal 𝒢 𝒩 f t ht
  change Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒩.genStalk)
      (IsLocalRing.maximalIdeal 𝒢.genStalk) ψ h (Ideal.toCotangent _ (r • m)) =
    (genMap 𝒢 𝒩 f).hom r • Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒩.genStalk)
      (IsLocalRing.maximalIdeal 𝒢.genStalk) ψ h (Ideal.toCotangent _ m)
  rw [Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent,
    ← (Ideal.toCotangent _).map_smul]
  congr 1
  apply Subtype.ext
  simp only [SetLike.val_smul, smul_eq_mul, map_mul, ψ, RingHom.toIntAlgHom_apply]

/-- `f^*` as a `K`-linear map. -/
noncomputable def cotMapK (𝒢 : GroupModel A K) (𝒩 : GroupModel B K) (f : 𝒢.G ⟶ 𝒩.G)
    [IsMonHom f] : cotK 𝒩 →ₗ[K] cotK 𝒢 where
  toFun x := cotMap 𝒢 𝒩 f x
  map_add' x y := map_add (cotMap 𝒢 𝒩 f) x y
  map_smul' k x := by
    show cotMap 𝒢 𝒩 f (jA 𝒩 k • (show 𝒩.cotangent from x)) =
      jA 𝒢 k • (show 𝒢.cotangent from cotMap 𝒢 𝒩 f x)
    rw [cotMap_smul, genMap_jA]

end Sec

end GapHeight

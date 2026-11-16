/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_PDivisibleGroup_cotangentBaseChange_bijective
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_PDivisibleGroup_cotangentBaseChange_bijective

set_option autoImplicit false

open scoped TensorProduct
open Coalgebra

namespace PDivCotBC

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
  (S : Type) [CommRing S] [Algebra R S] (v : ℕ)

open PDivisibleGroup

-- [port T8] local notation "A" expanded in place
-- [port T8] local notation "I" expanded in place
-- [port T8] local notation "B" expanded in place
-- [port T8] local notation "IS" expanded in place

theorem sub_mem (a : (G.level v)) : a - algebraMap R (G.level v) (counit (R := R) a) ∈ (G.augIdeal v) :=
  Hopf.sub_algebraMap_counit_mem_augIdeal R _ a

noncomputable def θ : (G.level v) →ₗ[R] G.Cotangent v where
  toFun a := ((G.augIdeal v)).toCotangent ⟨a - algebraMap R (G.level v) (counit (R := R) a), sub_mem G v a⟩
  map_add' a b := by
    rw [← map_add]
    congr 1
    ext
    change a + b - algebraMap R (G.level v) (counit (R := R) (a + b)) = (a - _) + (b - _)
    rw [map_add, map_add]; abel
  map_smul' r a := by
    rw [RingHom.id_apply, ← LinearMap.map_smul_of_tower]
    congr 1
    ext
    change r • a - algebraMap R (G.level v) (counit (R := R) (r • a)) = r • (a - algebraMap R (G.level v) (counit (R := R) a))
    rw [map_smul, smul_eq_mul, map_mul, smul_sub, Algebra.smul_def, Algebra.smul_def]

theorem θ_apply (a : (G.level v)) :
    θ G v a = ((G.augIdeal v)).toCotangent ⟨a - algebraMap R (G.level v) (counit (R := R) a), sub_mem G v a⟩ := rfl

theorem θ_of_mem {a : (G.level v)} (ha : a ∈ (G.augIdeal v)) : θ G v a = ((G.augIdeal v)).toCotangent ⟨a, ha⟩ := by
  rw [θ_apply]
  congr 1
  ext
  change a - algebraMap R (G.level v) (counit (R := R) a) = a
  rw [(G.mem_augIdeal_iff v a).1 ha, map_zero, sub_zero]

theorem θ_eq_zero_of_mem_sq {a : (G.level v)} (ha : a ∈ (G.augIdeal v) ^ 2) : θ G v a = 0 := by
  rw [θ_of_mem G v (Ideal.pow_le_self two_ne_zero ha), Ideal.toCotangent_eq_zero]
  exact ha

noncomputable def Ψ : (S ⊗[R] G.level v) →ₗ[S] S ⊗[R] G.Cotangent v := (θ G v).baseChange S

theorem Ψ_tmul (s : S) (a : (G.level v)) : Ψ G S v (s ⊗ₜ[R] a) = s ⊗ₜ[R] θ G v a := by
  rw [Ψ, LinearMap.baseChange_tmul]

theorem Ψ_mul_tmul_of_mem_sq (c : (S ⊗[R] G.level v)) {z : (G.level v)} (hz : z ∈ (G.augIdeal v) ^ 2) :
    Ψ G S v (c * ((1 : S) ⊗ₜ[R] z)) = 0 := by
  induction c using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero]
  | tmul s a =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Ψ_tmul,
      θ_eq_zero_of_mem_sq G v (Ideal.mul_mem_left _ a hz), TensorProduct.tmul_zero]
  | add x y hx hy => rw [add_mul, map_add, hx, hy, add_zero]

theorem augIdeal_eq_span :
    ((PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))) = Ideal.span ((fun y : (G.level v) => (1 : S) ⊗ₜ[R] y) '' ((G.augIdeal v) : Set (G.level v))) := by
  rw [Hopf.augIdeal_baseChange R S (G.level v), Ideal.map, Set.image]
  rfl

theorem Ψ_mul_mul_tmul_eq_zero {u : (S ⊗[R] G.level v)} (hu : u ∈ (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))) {y : (G.level v)} (hy : y ∈ (G.augIdeal v)) (c : (S ⊗[R] G.level v)) :
    Ψ G S v (c * u * ((1 : S) ⊗ₜ[R] y)) = 0 := by
  rw [augIdeal_eq_span] at hu
  induction hu using Submodule.span_induction generalizing c with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    exact Ψ_mul_tmul_of_mem_sq G S v c (by rw [pow_two]; exact Ideal.mul_mem_mul hz hy)
  | zero => rw [mul_zero, zero_mul, map_zero]
  | add x x' _ _ hx hx' => rw [mul_add, add_mul, map_add, hx, hx', add_zero]
  | smul b x _ hx => rw [smul_eq_mul, ← mul_assoc c b x]; exact hx (c * b)

theorem Ψ_mul_eq_zero {u w : (S ⊗[R] G.level v)} (hu : u ∈ (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))) (hw : w ∈ (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))) : Ψ G S v (u * w) = 0 := by
  rw [augIdeal_eq_span] at hw
  induction hw using Submodule.span_induction generalizing u with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    have := Ψ_mul_mul_tmul_eq_zero G S v hu hy 1
    rwa [one_mul] at this
  | zero => rw [mul_zero, map_zero]
  | add x x' _ _ hx hx' => rw [mul_add, map_add, hx hu, hx' hu, add_zero]
  | smul b x _ hx =>
    rw [smul_eq_mul, ← mul_assoc, mul_comm u b, mul_assoc]
    have hbu : b * u ∈ (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v)) := Ideal.mul_mem_left _ b hu
    rw [← mul_assoc]
    exact hx hbu

theorem Ψ_eq_zero_of_mem_sq {z : (S ⊗[R] G.level v)} (hz : z ∈ ((PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))) ^ 2) : Ψ G S v z = 0 := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz (fun u hu w hw => Ψ_mul_eq_zero G S v hu hw) ?_
  intro x y hx hy
  rw [map_add, hx, hy, add_zero]

noncomputable def ΨI : ((PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))) →ₗ[S] S ⊗[R] G.Cotangent v :=
  (Ψ G S v).comp ((Submodule.subtype ((PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v)))).restrictScalars S)

theorem ΨI_apply (u : (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))) : ΨI G S v u = Ψ G S v (u : (S ⊗[R] G.level v)) := rfl

noncomputable def Ψbar : ((PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))).Cotangent →ₗ[S] S ⊗[R] G.Cotangent v :=
  Ideal.Cotangent.lift (ΨI G S v) fun x y => by
    rw [ΨI_apply]
    exact Ψ_mul_eq_zero G S v x.2 y.2

theorem Ψbar_toCotangent (u : (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))) : Ψbar G S v (((PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))).toCotangent u) = Ψ G S v (u : (S ⊗[R] G.level v)) := by
  rw [Ψbar, Ideal.Cotangent.lift_toCotangent]
  rfl

theorem Ψbar_comp_cotangentBaseChange :
    (Ψbar G S v).comp (G.cotangentBaseChange S v) = LinearMap.id := by
  refine TensorProduct.AlgebraTensorModule.ext fun s y => ?_
  rw [LinearMap.comp_apply, LinearMap.id_apply, cotangentBaseChange_tmul, map_smul]
  obtain ⟨x, rfl⟩ := ((G.augIdeal v)).toCotangent_surjective y
  rw [cotangentToBaseChange_toCotangent, Ψbar_toCotangent]
  change s • Ψ G S v ((1 : S) ⊗ₜ[R] (x : (G.level v))) = _
  rw [Ψ_tmul, θ_of_mem G v x.2, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem injective : Function.Injective (G.cotangentBaseChange S v) := by
  intro a b hab
  have h1 := congrArg (Ψbar G S v) hab
  have h2 := LinearMap.congr_fun (Ψbar_comp_cotangentBaseChange G S v)
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, h2, h2] at h1
  exact h1

theorem toCotangent_smul (s : S) (x : (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))) :
    ((PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))).toCotangent (s • x) = s • ((PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))).toCotangent x := rfl

theorem toCotangent_mul_tmul_mem_range (c : (S ⊗[R] G.level v)) {y : (G.level v)} (hy : y ∈ (G.augIdeal v))
    (hcy : c * ((1 : S) ⊗ₜ[R] y) ∈ (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))) :
    ((PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))).toCotangent ⟨c * ((1 : S) ⊗ₜ[R] y), hcy⟩ ∈ LinearMap.range (G.cotangentBaseChange S v) := by
  induction c using TensorProduct.induction_on with
  | zero =>
    have : (⟨0 * ((1 : S) ⊗ₜ[R] y), hcy⟩ : (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))) = 0 := by ext; exact zero_mul _
    rw [this, map_zero]
    exact zero_mem _
  | tmul s a =>
    refine ⟨s ⊗ₜ[R] ((G.augIdeal v)).toCotangent ⟨a * y, Ideal.mul_mem_left _ a hy⟩, ?_⟩
    rw [cotangentBaseChange_tmul, cotangentToBaseChange_toCotangent, ← toCotangent_smul]
    congr 1
    ext
    change s • ((1 : S) ⊗ₜ[R] (a * y)) = (s ⊗ₜ[R] a) * ((1 : S) ⊗ₜ[R] y)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add c c' hc hc' =>
    have hcm : c * ((1 : S) ⊗ₜ[R] y) ∈ (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v)) :=
      Ideal.mul_mem_left _ c (G.augIdeal_le_comap_includeRight S v hy)
    have hcm' : c' * ((1 : S) ⊗ₜ[R] y) ∈ (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v)) :=
      Ideal.mul_mem_left _ c' (G.augIdeal_le_comap_includeRight S v hy)
    have : (⟨(c + c') * ((1 : S) ⊗ₜ[R] y), hcy⟩ : (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))) = ⟨_, hcm⟩ + ⟨_, hcm'⟩ := by
      ext; exact add_mul _ _ _
    rw [this, map_add]
    exact add_mem (hc hcm) (hc' hcm')

theorem toCotangent_mul_mem_range {u : (S ⊗[R] G.level v)}
    (hu : u ∈ Ideal.span ((fun y : (G.level v) => (1 : S) ⊗ₜ[R] y) '' ((G.augIdeal v) : Set (G.level v)))) :
    ∀ (c : (S ⊗[R] G.level v)) (hcu : c * u ∈ (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))),
      ((PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))).toCotangent ⟨c * u, hcu⟩ ∈ LinearMap.range (G.cotangentBaseChange S v) := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    intro c hcu
    exact toCotangent_mul_tmul_mem_range G S v c hy hcu
  | zero =>
    intro c hcu
    have : (⟨c * 0, hcu⟩ : (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))) = 0 := by ext; exact mul_zero _
    rw [this, map_zero]; exact zero_mem _
  | add x x' hx hx' ihx ihx' =>
    intro c hcu
    have hxm : x ∈ (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v)) := by rw [augIdeal_eq_span]; exact hx
    have hxm' : x' ∈ (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v)) := by rw [augIdeal_eq_span]; exact hx'
    have : (⟨c * (x + x'), hcu⟩ : (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))) =
        ⟨c * x, Ideal.mul_mem_left _ c hxm⟩ + ⟨c * x', Ideal.mul_mem_left _ c hxm'⟩ := by
      ext; exact mul_add _ _ _
    rw [this, map_add]
    exact add_mem (ihx _ _) (ihx' _ _)
  | smul b x hx ihx =>
    intro c hcu
    have hxm : x ∈ (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v)) := by rw [augIdeal_eq_span]; exact hx
    have : (⟨c * (b • x), hcu⟩ : (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))) = ⟨(c * b) * x, Ideal.mul_mem_left _ _ hxm⟩ := by
      ext; change c * (b * x) = c * b * x; rw [mul_assoc]
    rw [this]
    exact ihx _ _

theorem surjective : Function.Surjective (G.cotangentBaseChange S v) := by
  intro z
  obtain ⟨⟨u, hu⟩, rfl⟩ := ((PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v))).toCotangent_surjective z
  have hu' : u ∈ Ideal.span ((fun y : (G.level v) => (1 : S) ⊗ₜ[R] y) '' ((G.augIdeal v) : Set (G.level v))) := by
    rw [← augIdeal_eq_span]; exact hu
  have h1 : (1 : (S ⊗[R] G.level v)) * u ∈ (PDivisibleGroup.Hopf.augIdeal S (S ⊗[R] G.level v)) := by rw [one_mul]; exact hu
  obtain ⟨t, ht⟩ := toCotangent_mul_mem_range G S v hu' 1 h1
  refine ⟨t, ?_⟩
  rw [ht]
  congr 1
  ext
  exact one_mul u

end PDivCotBC

theorem solution
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (S : Type) [CommRing S] [Algebra R S] [Nontrivial S] (v : ℕ) :
    Function.Bijective (G.cotangentBaseChange S v) :=
  ⟨PDivCotBC.injective G S v, PDivCotBC.surjective G S v⟩

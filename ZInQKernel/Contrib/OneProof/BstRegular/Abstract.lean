import ZInQKernel.Contrib.OneProof.PanBergerFontaine

/-!
# bst-regular (a), (b): Fontaine's regularity formalism for subrings of `B_dR`

For a `ℚ_p`-subalgebra `B ⊆ B_dR` and a subgroup `H ⊆ G_{ℚ_p}`, `B` is **`H`-regular** (Fontaine, Astérisque 223
(1994), Exp. III §1.4; the notion as in Brinon–Conrad, CMI notes, §5.1; locators UNVERIFIED) when

* `B` is a domain: automatic, `B` being a subring of the field `B_dR` (`isDomain_sub`, step (b));
* `(Frac B)^H = B^H`: in fraction-free form, for `x, y ∈ B`, `y ≠ 0`, with `σ(x) y = x σ(y)` for every `σ ∈ H`
  (i.e. `x / y` is `H`-fixed), `x = c y` for some `c ∈ B^H` (`IsRegularB.frac`); this makes `B^H` a field
  (`IsRegularB.inv_fixed`);
* every nonzero `b ∈ B` spanning an `H`-stable `ℚ_p`-line is a unit of `B` (`IsRegularB.line`).

The abstract step (`isAdmissibleT_of_isAdmissible_of_regular`): for `H`-regular `B` and `V = E^n`, Fontaine's
dimension form `dim_{B^H} (B ⊗ V)^H = dim_{ℚ_p} V` (`IsAdmissible`) implies the basis form (`IsAdmissibleT`):
`B ⊗ V` has a `B`-basis of `H`-invariant vectors.

Proof: take `N = dim_{ℚ_p} V` elements `d_j` of `D = (B ⊗ V)^H` independent over `B^H`, and let `M ∈ M_N(B)` be their
coordinates in the basis `1 ⊗ e_i`. A minimal-support relation `M v = 0` has `σ(v_{j₀}) v - v_{j₀} σ(v)` as a smaller
relation, hence proportional to an `H`-invariant relation, which contradicts independence over `B^H`; so `det M ≠ 0`.
`M = R(σ) σ(M)` with `R(σ)` the `ℚ_p`-matrix of `ρ(σ)`, so `det M` spans an `H`-stable line, hence is a unit, and
the `d_j` are a `B`-basis.
-/

noncomputable section

namespace HDec
namespace PkgI4
namespace BstRegular

open Module BergerBst BmaxOne PanBergerSplit
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

/-- **`B` is `H`-regular** (Fontaine's notion), for a `ℚ_p`-subalgebra `B ⊆ B_dR` stable under `H`. `B` is a domain
automatically (a subring of the field `B_dR`, `isDomain_sub`). `frac` is `(Frac B)^H = B^H` with fractions cleared;
`line` is: a nonzero `b ∈ B` with `σ(b) ∈ ℚ_p b` for all `σ ∈ H` is a unit of `B`. -/
structure IsRegularB (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) : Prop where
  stable : ∀ σ ∈ H, ∀ x ∈ B, bdrAct p σ x ∈ B
  frac : ∀ x ∈ B, ∀ y ∈ B, y ≠ 0 → (∀ σ ∈ H, bdrAct p σ x * y = x * bdrAct p σ y) →
    ∃ c ∈ B, (∀ σ ∈ H, bdrAct p σ c = c) ∧ x = c * y
  line : ∀ b ∈ B, b ≠ 0 → (∀ σ ∈ H, ∃ c : ℚ_[p], bdrAct p σ b = algebraMap ℚ_[p] (BdR p) c * b) →
    ∃ b' ∈ B, b * b' = 1

/-! ## (b) `B` is a domain -/

theorem isDomain_BdR : IsDomain (BdR p) := (ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p).isDomain

/-- **(b)** Every `ℚ_p`-subalgebra of `B_dR` (in particular `B_st`) is a domain. -/
theorem isDomain_sub (B : Subalgebra ℚ_[p] (BdR p)) : IsDomain B := by
  have := isDomain_BdR p
  infer_instance

/-- For `H`-regular `B`, `B^H` is a field: a nonzero `H`-fixed `b ∈ B` has an `H`-fixed inverse in `B`. -/
theorem IsRegularB.inv_fixed {B : Subalgebra ℚ_[p] (BdR p)} {H : Subgroup (GQp p)} (hR : IsRegularB p B H)
    {b : BdR p} (hb : b ∈ B) (hb0 : b ≠ 0) (hfix : ∀ σ ∈ H, bdrAct p σ b = b) :
    ∃ c ∈ B, (∀ σ ∈ H, bdrAct p σ c = c) ∧ c * b = 1 := by
  obtain ⟨c, hc, hcf, h1⟩ := hR.frac 1 B.one_mem b hb hb0 (fun σ hσ => by rw [map_one, hfix σ hσ])
  exact ⟨c, hc, hcf, h1.symm⟩

/-! ## (a) The abstract step: dimension form ⇒ basis form -/

section Abstract

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

omit [FiniteDimensional ℚ_[p] E] in
/-- Coordinates in `B_dR ⊗ V` of the image of `x ∈ B ⊗ V`, for the bases `1 ⊗ e_i`. -/
theorem repr_inclT (B : Subalgebra ℚ_[p] (BdR p)) {ι : Type*} [DecidableEq ι]
    (bV : Basis ι ℚ_[p] (Fin n → E)) (x : B ⊗[ℚ_[p]] (Fin n → E)) (i : ι) :
    (Algebra.TensorProduct.basis (BdR p) bV).repr (inclT p B x) i =
      ((Algebra.TensorProduct.basis B bV).repr x i : BdR p) := by
  induction x using TensorProduct.inductionOn with
  | tmul c v =>
    rw [inclT, TensorProduct.map_tmul, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, Subalgebra.coe_mul,
      Subalgebra.coe_algebraMap, AlgHom.toLinearMap_apply, Subalgebra.coe_val, LinearMap.id_coe, id_eq]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, Subalgebra.coe_add]

omit [FiniteDimensional ℚ_[p] E] in
/-- Coordinates of `σ ⊗ ρ(σ)` on `B_dR ⊗ V`: `y_i ↦ Σ_k R_{ik} σ(y_k)`, `R = [ρ(σ)]_{bV}`. -/
theorem repr_tensorAct {ι : Type*} [Fintype ι] [DecidableEq ι] (bV : Basis ι ℚ_[p] (Fin n → E))
    (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) (y : BdR p ⊗[ℚ_[p]] (Fin n → E)) (i : ι) :
    (Algebra.TensorProduct.basis (BdR p) bV).repr (TensorProduct.map (bdrLin p σ) (vAct p ρ σ) y) i =
      ∑ k, algebraMap ℚ_[p] (BdR p) (LinearMap.toMatrix bV bV (vAct p ρ σ) i k) *
        bdrAct p σ ((Algebra.TensorProduct.basis (BdR p) bV).repr y k) := by
  induction y using TensorProduct.inductionOn with
  | tmul c v =>
    rw [TensorProduct.map_tmul, Algebra.TensorProduct.basis_repr_tmul]
    simp only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, map_mul]
    have hA : ∀ c : ℚ_[p], bdrAct p σ (algebraMap ℚ_[p] (BdR p) c) = algebraMap ℚ_[p] (BdR p) c :=
      fun c => bdrAct_qpToBdR p σ c
    simp only [hA]
    have hmv := LinearMap.toMatrix_mulVec_repr bV bV (vAct p ρ σ) v
    have hi := congrFun hmv i
    rw [← hi]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ = _ * (bdrLin p σ c * _)
    rw [show bdrLin p σ c = bdrAct p σ c from rfl]
    ring
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, Finset.sum_add_distrib, mul_add]

omit [FiniteDimensional ℚ_[p] E] in
theorem toMatrix_vAct_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (bV : Basis ι ℚ_[p] (Fin n → E))
    (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) : (LinearMap.toMatrix bV bV (vAct p ρ σ)).det ≠ 0 := by
  have h1 : LinearMap.toMatrix bV bV (vAct p ρ σ) * LinearMap.toMatrix bV bV (vAct p ρ σ⁻¹) = 1 := by
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id bV]
    congr 1
    apply LinearMap.ext
    intro v
    exact vAct_mul_inv p ρ σ v
  intro h0
  have := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **(a) Fontaine's abstract step.** For an `H`-regular `B ⊆ B_dR`, the dimension form of `B`-admissibility
implies the basis form: `B ⊗_{ℚ_p} V` has a `B`-basis of `H`-invariant vectors. -/
theorem isAdmissibleT_of_isAdmissible_of_regular (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p))
    (hR : IsRegularB p B H) (ρ : GQp p →* GL (Fin n) E) (hadm : IsAdmissible p B H ρ) :
    IsAdmissibleT p B H ρ := by
  have := isDomain_BdR p
  have := isDomain_sub p B
  have : Module.Free ℚ_[p] (Fin n → E) := Module.Free.of_divisionRing _ _
  have : Module.Finite ℚ_[p] (Fin n → E) := Module.Finite.pi
  set N := finrank ℚ_[p] (Fin n → E) with hN
  let bV : Basis (Fin N) ℚ_[p] (Fin n → E) := Module.finBasis ℚ_[p] (Fin n → E)
  let bB := Algebra.TensorProduct.basis B bV
  let bL := Algebra.TensorProduct.basis (BdR p) bV
  -- `N` elements of `D` independent over `B^H`
  obtain ⟨d, hd⟩ := exists_linearIndependent_of_le_finrank (R := fixedSub p B H) (M := dB p B H ρ)
    (n := N) hadm.ge
  let M : Matrix (Fin N) (Fin N) B := fun i j => bB.repr (d j : B ⊗[ℚ_[p]] (Fin n → E)) i
  let R : GQp p → Matrix (Fin N) (Fin N) ℚ_[p] := fun σ => LinearMap.toMatrix bV bV (vAct p ρ σ)
  -- the coordinate relation `M = R(σ) σ(M)` in `B_dR`
  have hrel : ∀ σ ∈ H, ∀ i j, ((M i j : B) : BdR p) =
      ∑ k, algebraMap ℚ_[p] (BdR p) (R σ i k) * bdrAct p σ ((M k j : B) : BdR p) := by
    intro σ hσ i j
    have hfix : TensorProduct.map (bdrLin p σ) (vAct p ρ σ) (inclT p B (d j : B ⊗[ℚ_[p]] (Fin n → E))) =
        inclT p B (d j : B ⊗[ℚ_[p]] (Fin n → E)) := (d j).2 σ hσ
    have h1 := repr_tensorAct p bV ρ σ (inclT p B (d j : B ⊗[ℚ_[p]] (Fin n → E))) i
    rw [hfix, repr_inclT] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [repr_inclT]
  -- coordinates of a combination
  have hcomb : ∀ (v : Fin N → B) i,
      bB.repr (∑ j, v j • (d j : B ⊗[ℚ_[p]] (Fin n → E))) i = (M.mulVec v) i := by
    intro v i
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct, M]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  -- σ on `B`
  have hσB : ∀ σ ∈ H, ∀ x : B, bdrAct p σ (x : BdR p) ∈ B := fun σ hσ x => hR.stable σ hσ x x.2
  let sB : ∀ σ ∈ H, B → B := fun σ hσ x => ⟨bdrAct p σ x, hσB σ hσ x⟩
  -- σ maps relations to relations
  have hσrel : ∀ σ (hσ : σ ∈ H) (v : Fin N → B), M.mulVec v = 0 → M.mulVec (fun j => sB σ hσ (v j)) = 0 := by
    intro σ hσ v hv
    have hs : ∀ f : Fin N → B, ((∑ j, f j : B) : BdR p) = ∑ j, (f j : BdR p) := fun f => map_sum B.val f _
    have hk : ∀ k, ∑ j, bdrAct p σ ((M k j : B) : BdR p) * bdrAct p σ ((v j : B) : BdR p) = 0 := by
      intro k
      have h1 : ((M.mulVec v k : B) : BdR p) = 0 := by rw [hv]; rfl
      have h2 : ((M.mulVec v k : B) : BdR p) = ∑ j, ((M k j : B) : BdR p) * ((v j : B) : BdR p) :=
        hs (fun j => M k j * v j)
      rw [h2] at h1
      have h3 := congrArg (bdrAct p σ) h1
      rw [map_sum, map_zero] at h3
      simpa only [map_mul] using h3
    funext i
    apply Subtype.val_injective
    have h2 : ((M.mulVec (fun j => sB σ hσ (v j)) i : B) : BdR p) =
        ∑ j, ((M i j : B) : BdR p) * bdrAct p σ ((v j : B) : BdR p) :=
      hs (fun j => M i j * sB σ hσ (v j))
    rw [h2]
    change _ = (0 : BdR p)
    calc ∑ j, ((M i j : B) : BdR p) * bdrAct p σ ((v j : B) : BdR p)
        = ∑ j, (∑ k, algebraMap ℚ_[p] (BdR p) (R σ i k) * bdrAct p σ ((M k j : B) : BdR p)) *
            bdrAct p σ ((v j : B) : BdR p) :=
          Finset.sum_congr rfl fun j _ => by rw [← hrel σ hσ i j]
      _ = ∑ k, algebraMap ℚ_[p] (BdR p) (R σ i k) *
            ∑ j, bdrAct p σ ((M k j : B) : BdR p) * bdrAct p σ ((v j : B) : BdR p) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          simp_rw [mul_assoc]
      _ = 0 := by simp only [hk, mul_zero, Finset.sum_const_zero]
  -- `det M ≠ 0`
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v₀, hv₀, hMv₀⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    classical
    let P : ℕ → Prop := fun k => ∃ v : Fin N → B, v ≠ 0 ∧ M.mulVec v = 0 ∧
      (Finset.univ.filter fun j => v j ≠ 0).card = k
    have hP : ∃ k, P k := ⟨_, v₀, hv₀, hMv₀, rfl⟩
    obtain ⟨v, hv0, hMv, hcard⟩ := Nat.find_spec hP
    have hmin : ∀ w : Fin N → B, w ≠ 0 → M.mulVec w = 0 →
        Nat.find hP ≤ (Finset.univ.filter fun j => w j ≠ 0).card :=
      fun w hw hMw => Nat.find_min' hP ⟨w, hw, hMw, rfl⟩
    obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hv0
    -- every `σ ∈ H` fixes the ratios `v_j / v_{j₀}`
    have hratio : ∀ σ (hσ : σ ∈ H) j, sB σ hσ (v j₀) * v j = v j₀ * sB σ hσ (v j) := by
      intro σ hσ
      let w : Fin N → B := fun j => sB σ hσ (v j₀) * v j - v j₀ * sB σ hσ (v j)
      have hMw : M.mulVec w = 0 := by
        have e : w = sB σ hσ (v j₀) • v - v j₀ • (fun j => sB σ hσ (v j)) := by
          funext j; simp [w]
        rw [e, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hMv, hσrel σ hσ v hMv,
          smul_zero, smul_zero, sub_zero]
      by_contra hne
      have hw0 : w ≠ 0 := by
        intro hw
        apply hne
        intro j
        have := congrFun hw j
        simpa [w, sub_eq_zero] using this
      have hsub : (Finset.univ.filter fun j => w j ≠ 0) ⊂ (Finset.univ.filter fun j => v j ≠ 0) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨j₀, by simpa using hj₀, ?_⟩
          simp [w, mul_comm]
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          intro hvj
          apply hj
          simp only [w, hvj, mul_zero, sub_eq_zero]
          have : sB σ hσ 0 = 0 := Subtype.ext (by simp [sB])
          rw [this, mul_zero]
      have := Finset.card_lt_card hsub
      have := hmin w hw0 hMw
      omega
    -- the ratios are in `B^H`
    have hc : ∀ j, ∃ c ∈ B, (∀ σ ∈ H, bdrAct p σ c = c) ∧ ((v j : B) : BdR p) = c * (v j₀ : BdR p) := by
      intro j
      refine hR.frac _ (v j).2 _ (v j₀).2 (fun h => hj₀ (Subtype.ext h)) fun σ hσ => ?_
      have := congrArg (fun z : B => (z : BdR p)) (hratio σ hσ j)
      simp only [Subalgebra.coe_mul, sB] at this
      rw [mul_comm] at this
      rw [this, mul_comm]
    choose c hcB hcfix hcv using hc
    let cH : Fin N → fixedSub p B H := fun j => ⟨⟨c j, hcB j⟩, hcfix j⟩
    have hsum : ∑ j, cH j • d j = 0 := by
      apply Subtype.val_injective
      apply bB.repr.injective
      ext i
      have hi := congrFun hMv i
      rw [← hcomb] at hi
      have e : (v j₀ : B) • ∑ j, ((cH j : B) • (d j : B ⊗[ℚ_[p]] (Fin n → E))) =
          ∑ j, v j • (d j : B ⊗[ℚ_[p]] (Fin n → E)) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul]
        congr 1
        apply Subtype.val_injective
        rw [Subalgebra.coe_mul, hcv j]
        exact mul_comm _ _
      have h2 : (v j₀ : B) * bB.repr (∑ j, ((cH j : B) • (d j : B ⊗[ℚ_[p]] (Fin n → E)))) i = 0 := by
        rw [← smul_eq_mul, ← Finsupp.smul_apply, ← map_smul, e, hi]
        rfl
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hj₀
      · have hcoe : ((∑ j, cH j • d j : dB p B H ρ) : B ⊗[ℚ_[p]] (Fin n → E)) =
            ∑ j, ((cH j : B) • (d j : B ⊗[ℚ_[p]] (Fin n → E))) := by
          rw [Submodule.coe_sum]
          exact Finset.sum_congr rfl fun j _ => Subalgebra.smul_def _ _
        rw [hcoe, h]
        simp
    have hsum' : ∑ j, cH j • d j = ∑ j, (0 : Fin N → fixedSub p B H) j • d j := by
      rw [hsum]
      exact (Finset.sum_eq_zero fun j _ => zero_smul _ _).symm
    have := Fintype.linearIndependent_iffₛ.mp hd cH 0 hsum' j₀
    apply hj₀
    apply Subtype.val_injective
    have h' := hcv j₀
    have hc0 : c j₀ = 0 := congrArg (fun z : fixedSub p B H => ((z : B) : BdR p)) this
    rw [hc0, zero_mul] at h'
    exact h'
  -- `det M` spans an `H`-stable line, hence is a unit
  have hdetL : ∀ σ ∈ H, ∃ c : ℚ_[p], bdrAct p σ ((M.det : B) : BdR p) =
      algebraMap ℚ_[p] (BdR p) c * ((M.det : B) : BdR p) := by
    intro σ hσ
    refine ⟨((R σ).det)⁻¹, ?_⟩
    let Mc : Matrix (Fin N) (Fin N) (BdR p) := (B.val : B →+* BdR p).mapMatrix M
    have hMc : ((M.det : B) : BdR p) = Mc.det := RingHom.map_det (B.val : B →+* BdR p) M
    have hmat : Mc = ((algebraMap ℚ_[p] (BdR p)).mapMatrix (R σ)) * (bdrAct p σ).mapMatrix Mc := by
      ext i j
      simp only [Mc, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply]
      exact hrel σ hσ i j
    have hd2 : Mc.det = algebraMap ℚ_[p] (BdR p) (R σ).det * bdrAct p σ Mc.det := by
      conv_lhs => rw [hmat]
      rw [Matrix.det_mul, ← RingHom.map_det, ← RingHom.map_det]
    have hne : (R σ).det ≠ 0 := toMatrix_vAct_det_ne_zero p bV ρ σ
    have h1 : algebraMap ℚ_[p] (BdR p) ((R σ).det)⁻¹ * algebraMap ℚ_[p] (BdR p) (R σ).det = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hne, map_one]
    rw [hMc]
    calc bdrAct p σ Mc.det = (algebraMap ℚ_[p] (BdR p) ((R σ).det)⁻¹ * algebraMap ℚ_[p] (BdR p) (R σ).det) *
          bdrAct p σ Mc.det := by rw [h1, one_mul]
      _ = algebraMap ℚ_[p] (BdR p) ((R σ).det)⁻¹ * Mc.det := by rw [mul_assoc, ← hd2]
  obtain ⟨b', hb'B, hbb'⟩ := hR.line _ (M.det).2 (fun h => hdet (Subtype.ext h)) hdetL
  have hunit : IsUnit M.det :=
    IsUnit.of_mul_eq_one (⟨b', hb'B⟩ : B) (Subtype.ext hbb')
  let inst : Invertible M := M.invertibleOfIsUnitDet hunit
  let e : (Fin N → B) ≃ₗ[B] (B ⊗[ℚ_[p]] (Fin n → E)) := (Matrix.toLinearEquiv' M inst).trans bB.equivFun.symm
  let bas : Basis (Fin N) B (B ⊗[ℚ_[p]] (Fin n → E)) := (Pi.basisFun B (Fin N)).map e
  have hbas : ∀ j, bas j = (d j : B ⊗[ℚ_[p]] (Fin n → E)) := by
    intro j
    simp only [bas, Basis.map_apply, e, LinearEquiv.trans_apply, Pi.basisFun_apply, Basis.equivFun_symm_apply]
    conv_rhs => rw [← bB.sum_repr (d j : B ⊗[ℚ_[p]] (Fin n → E))]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    change (M.mulVec (Pi.single j 1)) i = M i j
    rw [Matrix.mulVec_single_one]
    rfl
  exact ⟨Fin N, bas, fun j => by rw [hbas j]; exact (d j).2⟩

end Abstract

end BstRegular
end PkgI4
end HDec

import ZInQKernel.HDecomp.LeafPush2.UnifBridge
import ZInQKernel.HDecomp.Objects

/-!
# av-split, row H-38 (T35) without a new leaf

`T35.lean` proves the row `ZInQ.LeafPush2.UniformizationExists` from its case over `ℂ`,
`MumfordUniformizationC`. Here that case is derived from two leaves that are already needed:

* bp-analytic's AN3 leaf `BPAnalytic.Uniformization.UniformizationLeafAll` (kernel,
  `ZInQKernel/HDecomp/Analytic/Uniformization.lean`: `A(ℂ) ≅ ℂ^g/Λ` as complex Lie groups, for some
  `g`, in coordinate form);
* the H-25 leaf `MumfordTorsionAlgClosed` (Mumford §4, Application 2 (iv)), used at `k = ℂ` to
  identify `g = dim A`: `#(ℂ^g/Λ)[2] = 2^{2g}` (proved here, `card_torsion_torus`) and
  `#A(ℂ)[2] = 2^{2 dim A}` (the leaf).

The definitions `MumfordTorsionAlgClosed` and `MumfordUniformizationC` are copied verbatim from
`T5Isog.lean` and `T35.lean` (scratch files cannot import each other).
-/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AvSplit

open PkgI2 (IsAbelianVariety Pts torsion)

/-- (Verbatim copy from `T5Isog.lean`.) **LEAF (H-25; published form).** Mumford, *Abelian
varieties* (1970), §4, Application 2, (iv) (UNVERIFIED locator). -/
def MumfordTorsionAlgClosed : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Grp (Over (Spec (.of k)))) [IsAbelianVariety A]
    (g n : ℕ), topologicalKrullDim A.X.left = (g : WithBot ℕ∞) → 0 < n → (n : k) ≠ 0 →
      ∃ e : torsion A k n ≃ (Fin (2 * g) → ZMod n),
        ∀ x y : torsion A k n,
          ∀ h : x.1 * y.1 ∈ torsion A k n, e ⟨x.1 * y.1, h⟩ = e x + e y

open PkgI3
open ZInQ.LeafPush2 (CPts IsUniformization)

/-- (Verbatim copy from `T35.lean`.) The row H-38 at `K = ℂ`, `σ = id`. -/
def MumfordUniformizationC : Prop :=
  ∀ (A : AbVar ℂ) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ IsUniformization (RingHom.id ℂ) Λ Φ

namespace AN3

open BPAnalytic (Torus proj)

/-! ## The `n`-torsion of a complex torus -/

section Count

variable {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem finrank_lattice : Module.finrank ℤ Λ = 2 * g := by
  rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

/-- **`#(ℂ^g/Λ)[n] = n^{2g}`** for a full lattice `Λ` (proved). -/
theorem card_torsion_torus (n : ℕ) (hn : 0 < n) :
    Nat.card {q : Torus Λ // n • q = 0} = n ^ (2 * g) := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  haveI : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  set r := Module.finrank ℤ Λ with hr
  let b : Module.Basis (Fin r) ℤ Λ := Module.finBasis ℤ Λ
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  let θ : Λ → Torus Λ := fun l => proj Λ (((n : ℂ)⁻¹) • (l : Fin g → ℂ))
  have hθmem : ∀ l, n • θ l = 0 := by
    intro l
    show n • (QuotientAddGroup.mk _ : Torus Λ) = 0
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    have : n • ((n : ℂ)⁻¹ • (l : Fin g → ℂ)) = (l : Fin g → ℂ) := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hn0, one_smul]
    rw [this]; exact l.2
  -- `θ l = θ l'` iff `l - l' ∈ nΛ`
  have hθeq : ∀ l l' : Λ, θ l = θ l' ↔ ∀ i, (n : ℤ) ∣ b.repr (l - l') i := by
    intro l l'
    constructor
    · intro h
      have h1 : ((n : ℂ)⁻¹ • (l : Fin g → ℂ)) - (n : ℂ)⁻¹ • (l' : Fin g → ℂ) ∈ Λ :=
        (BPAnalytic.proj_eq_iff Λ).mp h
      rw [← smul_sub] at h1
      set mu : Λ := ⟨_, h1⟩
      have hmu : l - l' = n • mu := by
        apply Subtype.ext
        show (l : Fin g → ℂ) - l' = n • (((n : ℂ)⁻¹) • ((l : Fin g → ℂ) - l'))
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hn0, one_smul]
      intro i
      rw [hmu, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
      exact Dvd.intro _ rfl
    · intro h
      choose k hk using h
      let mu : Λ := ∑ i, k i • b i
      have hmu : l - l' = n • mu := by
        apply b.repr.injective
        ext i
        rw [hk i, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
        simp [mu, Finsupp.single_apply]
      apply (BPAnalytic.proj_eq_iff Λ).mpr
      rw [← smul_sub]
      have : ((l : Fin g → ℂ) - (l' : Fin g → ℂ)) = n • (mu : Fin g → ℂ) := by
        rw [← Submodule.coe_sub, hmu]; rfl
      rw [this, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn0, one_smul]
      exact mu.2
  -- the parametrization
  let lift : (Fin r → ZMod n) → Λ := fun c => ∑ i, ((c i).val : ℤ) • b i
  have hrepr : ∀ c i, b.repr (lift c) i = ((c i).val : ℤ) := by
    intro c i
    simp [lift, Finsupp.single_apply]
  let G : (Fin r → ZMod n) → {q : Torus Λ // n • q = 0} := fun c => ⟨θ (lift c), hθmem _⟩
  have hG : Function.Bijective G := by
    constructor
    · intro c c' h
      have h1 := (hθeq (lift c) (lift c')).mp (congrArg Subtype.val h)
      funext i
      have h2 := h1 i
      rw [map_sub, Finsupp.sub_apply, hrepr, hrepr] at h2
      have h3 : (((c i).val : ℤ) : ZMod n) = (((c' i).val : ℤ) : ZMod n) := by
        rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact h2
      simpa [ZMod.natCast_zmod_val] using h3
    · rintro ⟨q, hq⟩
      obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective q
      have hv : n • v ∈ Λ := by
        rw [← QuotientAddGroup.mk_nsmul] at hq
        exact (QuotientAddGroup.eq_zero_iff _).mp hq
      let l : Λ := ⟨n • v, hv⟩
      have hl : θ l = QuotientAddGroup.mk v := by
        show proj Λ ((n : ℂ)⁻¹ • (n • v)) = _
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn0, one_smul]
      let c : Fin r → ZMod n := fun i => ((b.repr l i : ℤ) : ZMod n)
      refine ⟨c, Subtype.ext ?_⟩
      show θ (lift c) = (QuotientAddGroup.mk v : Torus Λ)
      rw [← hl]
      apply (hθeq _ _).mpr
      intro i
      rw [map_sub, Finsupp.sub_apply, hrepr, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub]
      simp [c, ZMod.natCast_zmod_val]
  rw [← Nat.card_eq_of_bijective G hG, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
    Fintype.card_fin, hr, finrank_lattice]

end Count

/-! ## `g = dim A` from Mumford's torsion count -/

/-- For a uniformization `φ : ℂ^g'/Λ ≃+ A(ℂ)` of a complex abelian variety of dimension `g`
(bp-analytic's form), `g' = g`, by counting `2`-torsion (proved, from the H-25 leaf). -/
theorem eq_dim_of_uniformization (hT : MumfordTorsionAlgClosed) (A : AbVar ℂ) (g : ℕ)
    (hg : A.dim = (g : WithBot ℕ∞)) {g' : ℕ} (Λ : Submodule ℤ (Fin g' → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (φ : Torus Λ ≃+ Additive (A.Pt ℂ)) : g' = g := by
  obtain ⟨e, -⟩ := hT ℂ (ObjBridge.toGrp A) g 2 hg (by norm_num) (by norm_num)
  have h1 : Nat.card (torsion (ObjBridge.toGrp A) ℂ 2) = 2 ^ (2 * g) := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
  let e2 : {q : Torus Λ // 2 • q = 0} ≃ torsion (ObjBridge.toGrp A) ℂ 2 :=
    { toFun := fun q => ⟨Additive.toMul (φ q.1), by
        have h : φ q.1 + φ q.1 = 0 := by rw [← two_nsmul, ← map_nsmul, q.2, map_zero]
        show (Additive.toMul (φ q.1) : Pts (ObjBridge.toGrp A) ℂ) ^ 2 = 1
        rw [pow_two]
        exact congrArg Additive.toMul h⟩
      invFun := fun x => ⟨φ.symm (Additive.ofMul x.1), by
        have hx : (x.1 : Pts (ObjBridge.toGrp A) ℂ) * x.1 = 1 := by
          have := x.2
          change (x.1 : Pts (ObjBridge.toGrp A) ℂ) ^ 2 = 1 at this
          rwa [pow_two] at this
        have h2 : Additive.ofMul (x.1 : A.Pt ℂ) + Additive.ofMul x.1 = 0 := by
          exact congrArg Additive.ofMul hx
        rw [two_nsmul, ← map_add]
        exact (congrArg φ.symm h2).trans (map_zero _)⟩
      left_inv := fun q => Subtype.ext (by
        show φ.symm (φ q.1) = q.1
        exact φ.symm_apply_apply q.1)
      right_inv := fun x => Subtype.ext (by
        show Additive.toMul (φ (φ.symm (Additive.ofMul x.1))) = x.1
        rw [φ.apply_symm_apply]; rfl) }
  have h2 := card_torsion_torus Λ 2 (by norm_num)
  rw [Nat.card_congr e2, h1] at h2
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

/-- **`MumfordUniformizationC` from the AN3 leaf and the H-25 leaf (proved).** -/
theorem mumfordUniformizationC_of (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hT : MumfordTorsionAlgClosed) : MumfordUniformizationC := by
  intro A g hg
  obtain ⟨g', Λ, hd, hz, φ, hφ⟩ := HL A
  have hweak := ZInQ.LeafPush2.isUniformization_of_bp A hφ
  have hgg : g' = g := eq_dim_of_uniformization hT A g hg Λ φ
  subst hgg
  exact ⟨Λ, _, hd, hz, hweak⟩

end AN3

end AvSplit

#print axioms AvSplit.AN3.card_torsion_torus
#print axioms AvSplit.AN3.eq_dim_of_uniformization
#print axioms AvSplit.AN3.mumfordUniformizationC_of

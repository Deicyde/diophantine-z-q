import TailK

/-!
# qm-split, row H-86: `STQM` from the Shimura–Taniyama descent theorem in published form

The row `STQM` (leafq-check, `scratch/leafq-check/CMDescendsGlue.lean` l.40 @ w54; not in the chain, so its
definition and `bcC` are copied verbatim below, in the same namespace context and with the same `open`s)
says: a QM surface over `ℂ` with CM by `ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]` is `A₀ ×_{ℚ̄,ιe} ℂ` for some `A₀/ℚ̄`.

The published theorem (`ShimuraTaniyamaQbar`, below): an abelian variety over `ℂ` whose `End⁰` contains a
field of degree `2 dim A` (complex multiplication) has a model over `ℚ̄`. The glue proved here: the CM
element `φ` (or `2φ − 1`) and `ι(i)` commute, square to `d ∈ {−1, −3, −6}` and `2`, and generate a copy of
the field `E_d = ℚ(√2)(√d)` of degree 4 inside `End⁰(A)`; `End⁰(A) = ℚ ⊗ End(A)` is nonzero because
`n ↦ n·1 = ι(n)` is injective and `ℚ` is flat over `ℤ`.

Check: `scratch/qm-split/chk.sh scratch/qm-split/STQM.lean`.
-/

set_option linter.all false

noncomputable section

namespace HDec.HSyn.G0Split.FibreQM.PeriodMapH
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM

namespace QMSplitSTQM

/-! ## The row, copied verbatim (leafq-check `CMDescendsGlue.lean` l.26-43) -/

/-- `A₀ ×_{ℚ̄, ιe} ℂ`. -/
noncomputable abbrev bcC (ιe : Qbar →+* ℂ) (A₀ : PkgI3.AbVar Qbar) : PkgI3.AbVar ℂ :=
  @PkgI3.AbVar.baseChange Qbar _ A₀ ℂ _ ιe.toAlgebra

/-- **LEAF (Shimura–Taniyama, QM form).** A QM abelian surface over `ℂ` with CM by `ℤ[i]`, `ℤ[ζ₃]` or
`ℤ[√−6]` (an endomorphism `φ` commuting with `ι(𝒪)` with `φ² = −1`, `φ² − φ + 1 = 0` or `φ² = −6`) is
isomorphic, as an abelian variety, to `A₀ ×_{ℚ̄,ιe} ℂ` for some abelian variety `A₀/ℚ̄` and some
`ιe : ℚ̄ → ℂ`.

Published: an abelian variety over `ℂ` of CM type is isomorphic to the base change of an abelian variety
over a number field (Shimura–Taniyama, *Complex multiplication of abelian varieties*, 1961, §12.4;
Shimura, *Abelian varieties with complex multiplication and modular functions*, 1998, §12.4, Prop. 26;
UNVERIFIED numbers). It applies: `ι(i)` and `φ` commute, `ι(i)² = 2`, so `End⁰(A) ⊇ ℚ(√2, φ)`, a CM
field of degree `4 = 2 dim A`. A consequence of the published statement. -/
def STQM : Prop :=
  ∀ (A : PkgI3.AbVar ℂ) (q : QMStr A), A.dim = 2 → (HasCM4 q ∨ HasCM3 q ∨ HasCM24 q) →
    ∃ (ιe : Qbar →+* ℂ) (A₀ : PkgI3.AbVar Qbar) (e : PkgI3.AbVar.Hom (bcC ιe A₀) A)
      (e' : PkgI3.AbVar.Hom A (bcC ιe A₀)), e.hom ≫ e'.hom = 𝟙 _ ∧ e'.hom ≫ e.hom = 𝟙 _

/-! ## The published theorem -/

/-- **LEAF (Shimura–Taniyama: abelian varieties with complex multiplication are defined over `ℚ̄`).**
Let `A` be an abelian variety over `ℂ` (here of dimension 2) such that `End⁰(A) = ℚ ⊗ End(A)` contains a
field `E` with `[E : ℚ] = 2 dim A` (an injective `ℚ`-algebra map `E → End⁰(A)`). Then `A` is isomorphic to
`A₀ ×_{ℚ̄, ιe} ℂ` for an abelian variety `A₀` over `ℚ̄` and an embedding `ιe : ℚ̄ → ℂ`.

Sources: G. Shimura and Y. Taniyama, *Complex multiplication of abelian varieties and its applications to
number theory*, Publ. Math. Soc. Japan 6 (1961), §12.4, Prop. 26; G. Shimura, *Abelian varieties with
complex multiplication and modular functions*, Princeton 1998, §12.4, Prop. 26; J. S. Milne, *Complex
multiplication* (notes), §7 ("abelian varieties with CM over `ℂ` are defined over `ℚ^al`"); all numbers
UNVERIFIED (no network). Form: the printed statement with "CM" specialized to "a field of degree `2g` in
`End⁰`" and `g = 2`; the printed conclusion is a model over a number field `L ⊂ ℂ`, and the `ℚ̄`-form is
that model base-changed to the algebraic closure of `L` in `ℂ` (Milne prints the `ℚ^al` form). -/
def ShimuraTaniyamaQbar : Prop :=
  ∀ (A : PkgI3.AbVar ℂ), A.dim = 2 → ∀ (E : Type) [Field E] [Algebra ℚ E], Module.finrank ℚ E = 4 →
    (∃ f : E →ₐ[ℚ] PkgI3.AbVar.End0 A, Function.Injective f) →
    ∃ (ιe : Qbar →+* ℂ) (A₀ : PkgI3.AbVar Qbar) (e : PkgI3.AbVar.Hom (bcC ιe A₀) A)
      (e' : PkgI3.AbVar.Hom A (bcC ιe A₀)), e.hom ≫ e'.hom = 𝟙 _ ∧ e'.hom ≫ e.hom = 𝟙 _

/-! ## The fields `E_d = ℚ(√2)(√d)` -/

open Polynomial

abbrev K1 := AdjoinRoot (X ^ 2 - C (2 : ℚ))

instance factK1 : Fact (Irreducible (X ^ 2 - C (2 : ℚ))) := ⟨by
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro b hb
  have : IsSquare (2 : ℚ) := ⟨b, by rw [← hb]; ring⟩
  rw [Rat.isSquare_iff] at this; norm_num at this⟩

theorem K1_finrank : Module.finrank ℚ K1 = 2 := by
  rw [(AdjoinRoot.powerBasis (X_pow_sub_C_ne_zero (by norm_num) _)).finrank]
  simp [AdjoinRoot.powerBasis_dim]

/-- The real embedding `√2 ↦ √2`. -/
def sig : K1 →+* ℝ := AdjoinRoot.lift (algebraMap ℚ ℝ) (Real.sqrt 2) (by simp [Real.sq_sqrt])

theorem K1_no_neg_sq (d : ℚ) (hd : d < 0) (b : K1) : b ^ 2 ≠ algebraMap ℚ K1 d := by
  intro h
  have := congrArg sig h
  rw [map_pow, eq_ratCast (algebraMap ℚ K1) d, map_ratCast] at this
  have : (0 : ℝ) ≤ (sig b) ^ 2 := sq_nonneg _
  have : (d : ℝ) < 0 := by exact_mod_cast hd
  linarith

abbrev Ed (d : ℚ) := AdjoinRoot (X ^ 2 - C (algebraMap ℚ K1 d))

theorem irr_d (d : ℚ) (hd : d < 0) : Irreducible (X ^ 2 - C (algebraMap ℚ K1 d)) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two (K1_no_neg_sq d hd)

theorem Ed_finrank (d : ℚ) [Fact (Irreducible (X ^ 2 - C (algebraMap ℚ K1 d)))] :
    Module.finrank ℚ (Ed d) = 4 := by
  rw [← Module.finrank_mul_finrank ℚ K1 (Ed d), K1_finrank,
    (AdjoinRoot.powerBasis (X_pow_sub_C_ne_zero (by norm_num) _)).finrank]
  simp [AdjoinRoot.powerBasis_dim]


/-! ## `End⁰(A)` is nonzero; the embedding `E_d → End⁰(A)` -/

section End0

open scoped TensorProduct IsMulCommutative

variable {A : PkgI3.AbVar ℂ}

theorem end0_nontrivial (q : QMStr A) : Nontrivial (PkgI3.AbVar.End0 A) := by
  let j : ℤ →ₗ[ℤ] PkgI3.AbVar.End A := LinearMap.toSpanSingleton ℤ _ 1
  have hj : Function.Injective j := by
    intro m n h
    have hO : (m : LeafQM.O) = (n : LeafQM.O) := by
      apply q.injective
      simp only [j, LinearMap.toSpanSingleton_apply] at h
      rw [map_intCast, map_intCast, ← zsmul_one, ← zsmul_one, h]
    have h' : ((m : LeafQM.O) : LeafQM.B) = ((n : LeafQM.O) : LeafQM.B) := congrArg Subtype.val hO
    have := congrArg QuaternionAlgebra.re h'
    simpa using this
  haveI : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := ℚ) j hj
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h1 : j.lTensor ℚ ((1 : ℚ) ⊗ₜ[ℤ] (1 : ℤ)) = 1 := by
    simp [j, LinearMap.lTensor_tmul]; rfl
  have h2 : (1 : ℚ) ⊗ₜ[ℤ] (1 : ℤ) = 0 := hinj (by rw [h1, map_zero]; exact h.symm)
  have := congrArg (TensorProduct.rid ℤ ℚ) h2
  simp at this


/-- **The field `E_d` inside `End⁰(A)`**: for `ψ ∈ End_𝒪(A)` with `ψ² = d < 0`, the map `√2 ↦ 1 ⊗ ι(i)`,
`√d ↦ 1 ⊗ ψ` is an injective `ℚ`-algebra map `E_d → End⁰(A)`. -/
theorem embed_Ed (q : QMStr A) (d : ℤ) (hd : d < 0) (ψ : PkgI3.AbVar.End A) (hψ : ψ ∈ com q)
    (hψψ : ψ * ψ = (d : PkgI3.AbVar.End A))
    [Fact (Irreducible (X ^ 2 - C (algebraMap ℚ K1 (d : ℚ))))] :
    ∃ f : Ed (d : ℚ) →ₐ[ℚ] PkgI3.AbVar.End0 A, Function.Injective f := by
  set α : PkgI3.AbVar.End0 A := (1 : ℚ) ⊗ₜ[ℤ] q.iota oI
  set β : PkgI3.AbVar.End0 A := (1 : ℚ) ⊗ₜ[ℤ] ψ
  have hαα : α * α = algebraMap ℚ (PkgI3.AbVar.End0 A) 2 := by
    simp only [α, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, ← map_mul, oI_sq, map_add, map_one,
      TensorProduct.tmul_add, ← Algebra.TensorProduct.one_def, map_ofNat]
    exact one_add_one_eq_two
  have hββ : β * β = algebraMap ℚ (PkgI3.AbVar.End0 A) (d : ℚ) := by
    simp only [β, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, hψψ,
      Algebra.TensorProduct.algebraMap_apply]
    rw [← zsmul_one, ← TensorProduct.smul_tmul]
    simp [zsmul_eq_mul]
  have hαβ : α * β = β * α := by
    have hc : q.iota oI * ψ = ψ * q.iota oI := by
      rw [com, Subring.mem_centralizer_iff] at hψ
      exact hψ _ ⟨oI, rfl⟩
    simp only [α, β, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, hc]
  set S := Algebra.adjoin ℚ ({α, β} : Set (PkgI3.AbVar.End0 A))
  haveI hS : IsMulCommutative S := by
    apply Algebra.isMulCommutative_adjoin
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hαβ
    · exact hαβ.symm
    · exact Commute.refl _
  letI cS : CommRing S := { (inferInstance : Ring S) with mul_comm := fun x y => hS.is_comm.comm x y }
  let αS : S := ⟨α, Algebra.subset_adjoin (by simp)⟩
  let βS : S := ⟨β, Algebra.subset_adjoin (by simp)⟩
  have hα2 : αS ^ 2 = algebraMap ℚ S 2 := Subtype.ext (by
    change α ^ 2 = algebraMap ℚ (PkgI3.AbVar.End0 A) 2; rw [sq, hαα])
  have hβ2 : βS ^ 2 = algebraMap ℚ S (d : ℚ) := Subtype.ext (by
    change β ^ 2 = algebraMap ℚ (PkgI3.AbVar.End0 A) (d : ℚ); rw [sq, hββ])
  let i₁ : K1 →+* S := AdjoinRoot.lift (algebraMap ℚ S) αS (by
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, hα2, sub_self])
  have hi : i₁ (algebraMap ℚ K1 (d : ℚ)) = algebraMap ℚ S (d : ℚ) :=
    RingHom.congr_fun (RingHom.ext_rat (i₁.comp (algebraMap ℚ K1)) (algebraMap ℚ S)) _
  let f₀ : Ed (d : ℚ) →+* S := AdjoinRoot.lift i₁ βS (by
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, hi, hβ2, sub_self])
  let f : Ed (d : ℚ) →+* PkgI3.AbVar.End0 A := S.val.toRingHom.comp f₀
  haveI := end0_nontrivial q
  exact ⟨f.toRatAlgHom, f.injective⟩

/-- **Row H-86 from the published theorem.** -/
theorem stqm_of (h : ShimuraTaniyamaQbar) : STQM := by
  intro A q hA hCM
  obtain ⟨d, hd, ψ, hψ, hψψ⟩ :
      ∃ d : ℤ, d < 0 ∧ ∃ ψ ∈ com q, ψ * ψ = (d : PkgI3.AbVar.End A) := by
    rcases hCM with ⟨φ, hφ, h4⟩ | ⟨φ, hφ, h3⟩ | ⟨φ, hφ, h24⟩
    · exact ⟨-1, by norm_num, φ, hφ, by rw [h4]; simp⟩
    · refine ⟨-3, by norm_num, φ + φ - 1, (com q).sub_mem ((com q).add_mem hφ hφ) (com q).one_mem, ?_⟩
      have hφφ : φ * φ = φ - 1 := by
        rw [← sub_eq_zero, ← h3]; abel
      have e : (φ + φ - 1) * (φ + φ - 1) = -(1 + 1 + 1) := by
        simp only [add_mul, mul_add, sub_mul, mul_sub, _root_.one_mul, _root_.mul_one, hφφ]
        abel
      rw [e]; push_cast; norm_num
    · exact ⟨-6, by norm_num, φ, hφ, by rw [h24]; simp⟩
  haveI : Fact (Irreducible (X ^ 2 - C (algebraMap ℚ K1 (d : ℚ)))) := ⟨irr_d d (by exact_mod_cast hd)⟩
  obtain ⟨f, hf⟩ := embed_Ed q d hd ψ hψ hψψ
  exact h A hA (Ed (d : ℚ)) (Ed_finrank (d : ℚ)) ⟨f, hf⟩

end End0

end QMSplitSTQM

end HDec.HSyn.G0Split.FibreQM.PeriodMapH

#print axioms HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.stqm_of

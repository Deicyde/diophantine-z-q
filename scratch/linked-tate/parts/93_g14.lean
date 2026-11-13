/-! ## g14-trace copy: scratch/g14-trace/part_g14.lean, verbatim lines 26-31 (header), 110-163 (§2 and
`FrobTraceLink`), 194-293 (§4-§5); §1 (the twist obstruction), `FrobSquaresLink` and §6 are omitted. -/
section G14TraceSec
noncomputable section

namespace G14Trace

open PkgI4 (Qbar GQ LiesOver IsArithFrob GaloisRep)
open PkgI3 G0ModNewform GlueC10Link

/-! ## §2. Traces through G8's intertwining (proved) -/

/-- If `e : V ≃ ℚ̄_ℓ² × ℚ̄_ℓ²` intertwines `f g` with `m g ⊕ m g`, then `tr f(g) = 2 tr m(g)`. -/
theorem trace_of_intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] (f : G → Module.End (PadicAlgCl ℓ) V)
    (m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (h : Intertwines f m e) (g : G) :
    LinearMap.trace (PadicAlgCl ℓ) V (f g) = 2 * (m g).trace := by
  haveI : Module.Finite (PadicAlgCl ℓ) V := Module.Finite.equiv e.symm
  have hconj : e.conj (f g) = LinearMap.prodMap (Matrix.toLin' (m g)) (Matrix.toLin' (m g)) := by
    apply LinearMap.ext
    intro x
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h g, LinearEquiv.apply_symm_apply,
      LinearMap.prodMap_apply, Matrix.toLin'_apply]
  rw [← LinearMap.trace_conj' (f g) e, hconj, LinearMap.trace_prodMap', Matrix.trace_toLin'_eq]
  ring

/-- One coefficient prime: if `N·tr T = t` and `tr(β⁻¹ a T) = 2 tr m` (images of
`a, β ∈ ℚ̄` under `j`), then `tr m = j(½ β⁻¹ a t/N)`. -/
theorem trace_eq_image {ℓ : ℕ} [Fact ℓ.Prime] (j : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {V : Type*}
    [AddCommGroup V] [Module (PadicAlgCl ℓ) V] (T : Module.End (PadicAlgCl ℓ) V) (a β : Qbar)
    (N : ℕ) (hN : N ≠ 0) (t : ℤ) (hNT : (N : PadicAlgCl ℓ) * LinearMap.trace _ V T = t)
    (m : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (h2 : LinearMap.trace _ V (((j β)⁻¹ * j a) • T) = 2 * m.trace) :
    m.trace = j ((β)⁻¹ * a * ((t : Qbar) / N) / 2) := by
  have hNE : (N : PadicAlgCl ℓ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hT : LinearMap.trace _ V T = (t : PadicAlgCl ℓ) / N := by
    rw [eq_div_iff hNE, mul_comm, hNT]
  rw [map_smul, smul_eq_mul, hT] at h2
  rw [map_div₀, map_mul, map_mul, map_inv₀, map_div₀, map_intCast, map_natCast, map_ofNat]
  linear_combination (-1 / 2 : PadicAlgCl ℓ) * h2

/-! ## §3. The AV-side glue Props -/

/-- **The Frobenius trace link (GLUE, AV side; N5 L781-786).** There is a finite set `S` of
primes such that at every arithmetic Frobenius `τ` above `p ∉ S` there are an abelian variety
`Ā` over a field `k` of characteristic `p`, an endomorphism `α'` of `Ā` and `N ≠ 0` with
`FrobCompare` (kernel, `GlueC10Link`) at `ℓ = 3` and at `ℓ = 5`: some isomorphism
`ℚ̄_ℓ ⊗ V_ℓ(A) ≃ ℚ̄_ℓ ⊗ V_ℓ(Ā)` carries `N·Tm_ℓ(τ)` to `V_ℓ(α')`. In N5, `S = T ∪ {3, 5}`
(`T` = bad primes of `A/L'`), `Ā` is the reduction of `A` at the place `v ∩ L'`, `α' = N·(μ̄_τ ∘ F)`
(relative `p`-Frobenius `F`, reduction `μ̄_τ` of the isogeny `μ_τ : {}^τA → A`, defined over
`L ⊆ L'` by N5 L638-640), and the
isomorphism is the Serre–Tate reduction isomorphism. It concerns the operators `Tm_ℓ` that
g0-mod-field's `TateBridge` builds from the points-level `m_σ = μ_σ ∘ σ` (one `m_σ` for all `ℓ`). -/
def FrobTraceLink {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
    LiesOver v p → IsArithFrob τ v p →
    ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k) (α : PkgI3.AbVar.End Ab)
      (N : ℕ), N ≠ 0 ∧ FrobCompare 3 (Tm3 τ) α N ∧ FrobCompare 5 (Tm5 τ) α N

/-! ## §4. One algebraic number for both traces (proved from T7) -/

/-- **The common trace (GLUE, proved from T7, `FrobTraceLink` and the scalar link).** With
`ρ_ℓ = β_ℓ⁻¹ a_ℓ Tm_ℓ`, `a_ℓ = j_ℓ ∘ a`, `β_ℓ = j_ℓ ∘ β`, and G8's intertwining of `ρ_ℓ` with
`r_ℓ ⊕ r_ℓ` at `ℓ = 3, 5`: outside a finite set, at every arithmetic Frobenius `τ`, the traces of
`r₅(τ)` and `r₃(τ)` are `j₅(x)` and `j₃(x)` for one `x = ½ β(τ)⁻¹ a(τ) tr(α')/N ∈ ℚ̄`. -/
theorem common_trace (hM : CharPolyIndepOfEll) {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3)
    (a β : GQ → Qbar)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (r5 : GaloisRep 5 2) (r3 : GaloisRep 3 2)
    (h5 : GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) r5)
    (h3 : GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) r3)
    (hF : FrobTraceLink A Tm5 Tm3) :
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p → IsArithFrob τ v p →
        ∃ x : Qbar, (r5.mat τ).trace = j5 x ∧ (r3.mat τ).trace = j3 x := by
  obtain ⟨S, hS⟩ := hF
  obtain ⟨-, e5, he5, -⟩ := h5
  obtain ⟨-, e3, he3, -⟩ := h3
  haveI : Module.Finite (PadicAlgCl 5) (Vb A 5) := Module.Finite.equiv e5.symm
  haveI : Module.Finite (PadicAlgCl 3) (Vb A 3) := Module.Finite.equiv e3.symm
  refine ⟨S ∪ {3, 5}, fun p hp hpS v τ hv hτ => ?_⟩
  have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
  have hp3 : p ≠ 3 := fun h => hpS (Finset.mem_union_right _ (by simp [h]))
  have hp5 : p ≠ 5 := fun h => hpS (Finset.mem_union_right _ (by simp [h]))
  obtain ⟨k, _, hk, Ab, α, N, hN, hc3, hc5⟩ := hS p hp hpS1 v τ hv hτ
  obtain ⟨t, ht⟩ := trace_T_of_frobCompare hM Ab α
  have hk3 : ((3 : ℕ) : k) ≠ 0 := cast_ne_zero_of_charP hp Nat.prime_three hp3
  have hk5 : ((5 : ℕ) : k) ≠ 0 := cast_ne_zero_of_charP hp (by norm_num) hp5
  have t5 := ht 5 hk5 (Tm5 τ) N hc5
  have t3 := ht 3 hk3 (Tm3 τ) N hc3
  refine ⟨(β τ)⁻¹ * a τ * ((t : Qbar) / N) / 2, ?_, ?_⟩
  · refine trace_eq_image j5 (Tm5 τ) (a τ) (β τ) N hN t t5 (r5.mat τ) ?_
    exact trace_of_intertwines _ r5.mat e5 he5 τ
  · refine trace_eq_image j3 (Tm3 τ) (a τ) (β τ) N hN t t3 (r3.mat τ) ?_
    exact trace_of_intertwines _ r3.mat e3 he3 τ

/-! ## §5. Choosing `ι₃` compatibly with Pan's `ι₅` (proved) -/

/-- Any two `ℚ`-embeddings of `ℚ̄` into a field differ by an endomorphism of `ℚ̄`:
`ι = j ∘ γ` (`ι(x)` is a root of the minimal polynomial of `x`, which splits in `j(ℚ̄)`). -/
theorem exists_comp_eq {F : Type*} [Field F] [Algebra ℚ F] (ι j : Qbar →ₐ[ℚ] F) :
    ∃ γ : Qbar →ₐ[ℚ] Qbar, ι = j.comp γ := by
  have hmem : ∀ x : Qbar, ∃ y : Qbar, j y = ι x := by
    intro x
    have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    set P := minpoly ℚ x with hP
    have hP0 : P.map (algebraMap ℚ Qbar) ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero hint)
    have hroot : ((P.map (algebraMap ℚ Qbar)).map (j : Qbar →+* F)).IsRoot (ι x) := by
      rw [Polynomial.map_map, j.comp_algebraMap, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    obtain ⟨y, hy⟩ := (IsAlgClosed.splits (P.map (algebraMap ℚ Qbar))).mem_range_of_isRoot hP0 hroot
    exact ⟨y, hy⟩
  choose γf hγf using hmem
  have hj : Function.Injective j := j.toRingHom.injective
  refine ⟨{ toFun := γf
            map_one' := hj (by rw [hγf, map_one, map_one])
            map_mul' := fun x y => hj (by rw [hγf, map_mul, map_mul, hγf, hγf])
            map_zero' := hj (by rw [hγf, map_zero, map_zero])
            map_add' := fun x y => hj (by rw [hγf, map_add, map_add, hγf, hγf])
            commutes' := fun q => hj (by rw [hγf, AlgHom.commutes, AlgHom.commutes]) }, ?_⟩
  ext x
  exact (hγf x).symm

/-- **`G14TraceCompat` from the common trace (GLUE, proved).** If the traces of `r₅`, `r₃` at
Frobenius are `j₅(x)`, `j₃(x)`, and `ι₅ = j₅ ∘ γ`, `ι₃ = j₃ ∘ γ`, then `G14TraceCompat` holds for
any data with these `ι₅, ι₃, r₅, r₃`. -/
theorem g14TraceCompat_of_common {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    (D : ModData K A) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3)
    (γ : Qbar →ₐ[ℚ] Qbar) (h5 : D.ι5 = j5.comp γ) (h3 : D.ι3 = j3.comp γ)
    (h : ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p → IsArithFrob τ v p →
        ∃ x : Qbar, (D.r5.mat τ).trace = j5 x ∧ (D.r3.mat τ).trace = j3 x) :
    G14TraceCompat D := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun p hp hpS v τ hv hτ c hc => ?_⟩
  obtain ⟨x, hx5, hx3⟩ := hS p hp hpS v τ hv hτ
  have hxc : x = γ c := by
    apply j5.toRingHom.injective
    change j5 x = j5 (γ c)
    rw [← hx5, hc, h5, AlgHom.comp_apply]
  rw [hx3, hxc, h3, AlgHom.comp_apply]

/-- **G14TraceCompat on G8's construction (GLUE, proved from T7, `FrobTraceLink` and the scalar
link).** For data `D` whose `r₅`, `r₃` are G8's outputs on `ρ_ℓ = β_ℓ⁻¹ a_ℓ Tm_ℓ` with
`a_ℓ = j_ℓ ∘ a`, `β_ℓ = j_ℓ ∘ β`, and whose embeddings are `ι₅ = j₅ ∘ γ`, `ι₃ = j₃ ∘ γ`. -/
theorem g14TraceCompat_of_link (hM : CharPolyIndepOfEll) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} (D : ModData K A) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5)
    (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3) (γ : Qbar →ₐ[ℚ] Qbar) (hι5 : D.ι5 = j5.comp γ)
    (hι3 : D.ι3 = j3.comp γ) (a β : GQ → Qbar)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3))
    (h5 : GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) D.r5)
    (h3 : GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) D.r3)
    (hF : FrobTraceLink A Tm5 Tm3) : G14TraceCompat D :=
  g14TraceCompat_of_common D j5 j3 γ hι5 hι3
    (common_trace hM A j5 j3 a β Tm5 Tm3 D.r5 D.r3 h5 h3 hF)

end G14Trace
end
end G14TraceSec

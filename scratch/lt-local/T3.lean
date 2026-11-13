import Base
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.FieldTheory.IsAlgClosed.Classification

/-! # lt-local, part 1: a field isomorphism `ℂ ≃ ℚ̄_ℓ` extending two given embeddings of `ℚ̄`

`exists_equiv_extending ιC j`: for embeddings `ιC : ℚ̄ → ℂ` and `j : ℚ̄ → ℚ̄_ℓ` there is a ring
isomorphism `Φ : ℂ ≃+* ℚ̄_ℓ` with `Φ ∘ ιC = j` (both fields are algebraically closed over `ℚ̄`
with transcendence bases of cardinality `𝔠`; Mathlib's `IsAlgClosure.equivOfEquiv` applied to the
`ℚ̄`-algebra isomorphism of the two polynomial rings on the bases). It transports `G7Data`'s
`ℂ^×`-valued cochain `β = ιC ∘ β_ℚ̄` to `j ∘ β_ℚ̄`, as `G7Clauses` asks.

`padic_card_le` and `padicAlgCl_card` are copied verbatim from g8-tate's `part_tools.lean`
(namespace `G8Tate`, renamed here to `LTLocal` to avoid a clash at integration). -/

noncomputable section

namespace LTLocal

open Cardinal LadicCond

/-- (copied from g8-tate) `#ℚ_p ≤ 𝔠`. -/
theorem padic_card_le (p : ℕ) [Fact p.Prime] : #ℚ_[p] ≤ 𝔠 := by
  have hex : ∀ x : ℚ_[p], ∀ n : ℕ, ∃ r : ℚ, ‖x - r‖ < 1 / ((n : ℝ) + 1) :=
    fun x n => Padic.rat_dense p x (by positivity)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hpos)
    have h1 := hf x n
    have h2 := hf y n
    rw [hxy] at h1
    have h3 : ‖x - y‖ ≤ ‖x - (f y n : ℚ_[p])‖ + ‖y - (f y n : ℚ_[p])‖ := by
      calc ‖x - y‖ = ‖(x - (f y n : ℚ_[p])) - (y - (f y n : ℚ_[p]))‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  calc #ℚ_[p] ≤ #(ℕ → ℚ) := mk_le_of_injective hinj
    _ = 𝔠 := by
      rw [← power_def, Cardinal.mkRat, mk_nat, aleph0_power_aleph0]

/-- (copied from g8-tate) `#ℚ̄_ℓ = 𝔠`. -/
theorem padicAlgCl_card (ℓ : ℕ) [Fact ℓ.Prime] : #(PadicAlgCl ℓ) = 𝔠 := by
  apply le_antisymm
  · calc #(PadicAlgCl ℓ) ≤ max #ℚ_[ℓ] ℵ₀ :=
          Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[ℓ] (PadicAlgCl ℓ)
      _ ≤ 𝔠 := max_le (padic_card_le ℓ) aleph0_le_continuum
  · calc 𝔠 ≤ #ℚ_[ℓ] := continuum_le_cardinal_of_nontriviallyNormedField _
      _ ≤ #(PadicAlgCl ℓ) := mk_le_of_injective (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).injective

/-- `ℚ̄` is countable. -/
theorem qbar_card_le : #PkgI4.Qbar ≤ ℵ₀ := by
  calc #PkgI4.Qbar ≤ max #ℚ ℵ₀ := Algebra.IsAlgebraic.cardinalMk_le_max ℚ PkgI4.Qbar
    _ = ℵ₀ := by rw [Cardinal.mkRat, max_self]

/-- **Two algebraically closed fields of cardinality `𝔠` containing `ℚ̄` are isomorphic over
`ℚ̄` (proved).** Stated for the `ℚ̄`-algebra structures given by `ι` and `j`. -/
theorem exists_equiv_extending_aux {K M : Type} [Field K] [Field M] [IsAlgClosed K]
    [IsAlgClosed M] (ι : PkgI4.Qbar →+* K) (j : PkgI4.Qbar →+* M) (hK : #K = 𝔠) (hM : #M = 𝔠) :
    ∃ Φ : K ≃+* M, ∀ x, Φ (ι x) = j x := by
  letI : Algebra PkgI4.Qbar K := ι.toAlgebra
  letI : Algebra PkgI4.Qbar M := j.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis PkgI4.Qbar K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis PkgI4.Qbar M
  have hc : ℵ₀ < 𝔠 := aleph0_lt_continuum
  have hs' : #K = #s :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs qbar_card_le
      (hK ▸ hc)
  have ht' : #M = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht qbar_card_le
      (hM ▸ hc)
  obtain ⟨e⟩ : Nonempty (s ≃ t) := Cardinal.eq.mp (by rw [← hs', ← ht', hK, hM])
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let e' : Algebra.adjoin PkgI4.Qbar (Set.range ((↑) : s → K)) ≃ₐ[PkgI4.Qbar]
      Algebra.adjoin PkgI4.Qbar (Set.range ((↑) : t → M)) :=
    (hs.1.aevalEquiv.symm.trans (MvPolynomial.renameEquiv PkgI4.Qbar e)).trans ht.1.aevalEquiv
  refine ⟨IsAlgClosure.equivOfEquiv K M e'.toRingEquiv, fun x => ?_⟩
  have h1 : ι x = algebraMap (Algebra.adjoin PkgI4.Qbar (Set.range ((↑) : s → K))) K
      (algebraMap PkgI4.Qbar _ x) := rfl
  rw [h1, IsAlgClosure.equivOfEquiv_algebraMap]
  show algebraMap _ M (e' (algebraMap PkgI4.Qbar _ x)) = j x
  rw [AlgEquiv.commutes]
  rfl

/-- **`ℂ ≃+* ℚ̄_ℓ` extending given embeddings of `ℚ̄` (proved).** -/
theorem exists_equiv_extending {ℓ : ℕ} [Fact ℓ.Prime] (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) :
    ∃ Φ : ℂ ≃+* PadicAlgCl ℓ, ∀ x, Φ (ιC x) = j x :=
  exists_equiv_extending_aux ιC.toRingHom j.toRingHom mk_complex (padicAlgCl_card ℓ)

end LTLocal

end

/-! # lt-local, part 2: `G7Clauses` and `dim A_{L'} = 2` for `TateBridge35`'s transported data

* `g7Clauses_of_transport`: local-data's `G7Clauses (j ∘ β_ℚ̄) ε' L` from `G7Data`, the bound
  `[L:ℚ] ≤ D` (local-data's finding F3: `G7Data` does not carry it), `ιC ∘ β_ℚ̄ = β` and
  `∂(j ∘ β_ℚ̄) = ε'` (both in `TateBridge35`'s output). The `ℂ^×`-valued clauses are carried to
  `ℚ̄_ℓ` by a field isomorphism `Φ : ℂ ≃ ℚ̄_ℓ` with `Φ ∘ ιC = j` (part 1), so that
  `j ∘ β_ℚ̄ = Φ ∘ β`; `ε' = 1` on `G_L × G_L` because `ε = 1` there (`DescentDatum`) and
  `j ∘ β_ℚ̄` has no zero. The proof of the clauses for `Φ ∘ β` follows g8-tate's
  `g7Clauses_of_g7Data` (copied, with `ε'` in place of `Φ ∘ ε`).
* `dim_bc_of_g7Data`: `dim A_{L'} = 2` from `G7Data`'s last clause `IsModelOver L' A_{L'} P`,
  `P.surface` and g0-dim's `pkgI3_dim_baseChange` (the proof of g0-split's `model_dim`). -/

noncomputable section

namespace LTLocal

open PkgI4 (GQ GQp decomp)
open LadicCond G0ModField
open ZInQ LeafQM.AV GlueDescent.B2
open CategoryTheory AlgebraicGeometry

/-- (copied from g8-tate) `T u` consists of primes. -/
theorem T_prime (u : ℚ) : ∀ q ∈ T u, q.Prime := by
  obtain ⟨hS, -, -⟩ := admissible_S_mul
  intro q hq
  rcases Finset.mem_union.mp hq with h | h
  · exact hS q h
  · exact Nat.prime_of_mem_primeFactors h

/-- **`G7Clauses` for the transported cochain `j ∘ β_ℚ̄` (proved).** -/
theorem g7Clauses_of_transport {ℓ : ℕ} [Fact ℓ.Prime] {u : ℚ}
    {P : QML3 Qbar} {L : IF} [FiniteDimensional ℚ L] {A : PkgI3.AbVar L}
    {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF}
    {hLL' : L ≤ L'} (h : G7Data u P L A ε N χ β L' hLL')
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (βQ : PkgI4.GQ → PkgI4.Qbar)
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
    (hC : ∀ g, ιC (βQ g) = (β g : ℂ)) {ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ}
    (hε' : ∀ g h, j (βQ g) * j (βQ h) = ε' g h * j (βQ (g * h))) :
    G15Ram.G7Clauses (fun g => j (βQ g)) ε' L := by
  obtain ⟨Φ, hΦ⟩ := exists_equiv_extending ιC j
  have hjβ : ∀ g, j (βQ g) = Φ (β g : ℂ) := fun g => by rw [← hC, hΦ]
  have hne : ∀ g, Φ (β g : ℂ) ≠ 0 := fun g => (map_ne_zero Φ).mpr (Units.ne_zero _)
  obtain ⟨-, hDD, -, -, ⟨Tm, hTmT, hN⟩, hβlc, hβsq, hβε, -⟩ := h
  have hfun : (fun g => j (βQ g)) = fun g => Φ (β g : ℂ) := funext hjβ
  refine ⟨inferInstance, hLD, hε', fun g => by simp only [hjβ]; exact hne g, ?_, ?_, ?_⟩
  · rw [hfun]
    exact hβlc.comp (fun z : ℂˣ => Φ (z : ℂ))
  · have hT : ∀ q ∈ Tm, q.Prime := fun q hq => T_prime u q (hTmT hq)
    subst hN
    refine ⟨Tm, hT, inferInstance, χ, Units.map Φ.toRingHom.toMonoidHom, fun g => ?_⟩
    show j (βQ g) ^ 2 = Φ ((GlueDescent.B2Q.galChar χ g : ℂˣ) : ℂ)
    rw [hjβ, ← map_pow, ← Units.val_pow_eq_pow_val, hβsq g]
  · intro g h hg _
    obtain ⟨hε, hinf, h11, -⟩ := hDD
    have h1 := GlueDescent.B3Q.inflatedNormalized_of L ε hε hinf h11 g h
      (Or.inl (GlueDescent.B3Q.mem_GQL.mpr hg))
    have h2 := hβε g h
    rw [h1, one_mul] at h2
    have h3 := hε' g h
    rw [hjβ, hjβ, hjβ, ← map_mul, ← Units.val_mul, h2] at h3
    exact mul_right_cancel₀ (hne (g * h)) (h3.symm.trans (one_mul _).symm)

/-- **`dim A_{L'} = 2` on G7's data (proved)**: G7Data's clause `IsModelOver L' A_{L'} P`,
`P.surface` and g0-dim's `pkgI3_dim_baseChange` (as g0-split's `model_dim`). -/
theorem dim_bc_of_g7Data {u : ℚ} {P : QML3 Qbar} {L : IF} {A : PkgI3.AbVar L}
    {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF}
    {hLL' : L ≤ L'} (h : G7Data u P L A ε N χ β L' hLL') :
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 := by
  obtain ⟨e⟩ := h.2.2.2.2.2.2.2.2.2.2.2
  rw [← G0Dim.pkgI3_dim_baseChange Qbar (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')),
    ← P.surface]
  exact IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.homeoOfIso ((Over.forget _).mapIso e)).isHomeomorph

end LTLocal

end

/-! # lt-local, part 3: verbatim copies from `scratch/g0-assemble2/G0Assemble2.lean`

* `G0ModNewform.Vb` (G0Assemble2.lean l.41358-41360, g0-mod-newform §9's copy of g0-mod-galois'
  `Vb`; the base environment has `G0Galois.Vb` and `GaloisCopy.Vb`, the same `abbrev`);
* g14-trace's `G14Trace.FrobTraceLink` with its namespace header (l.62238-62242, l.62356-62373);
* g0-assemble2's `HSyn.G0AssembleMod.LinkedTateLocal` with its namespace header
  (l.63903-63947; GLUE field 39 of `GluePieces3`).
The rest of what these depend on (`G0Galois.G7Out`, `G0Galois.G8Out`, `G0Galois.Vb`,
`GlueDescent.rho`, `G15Ram.LocalData`, `G0ModField.G7Data`, `FibreCtx`, `incAlg`,
`numberField_of_fd`, `GlueC10Link.FrobCompare`) is in the base environment (lg-kerwild's
`KerWild.lean`, itself verbatim copies of the same sources). -/

noncomputable section

namespace G0ModNewform

/-- (copied from g0-mod-galois) `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

end G0ModNewform

namespace G14Trace

open PkgI4 (Qbar GQ LiesOver IsArithFrob GaloisRep)
open PkgI3 G0ModNewform GlueC10Link


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


end G14Trace

end

noncomputable section

-- Name resolution of `Qbar`, `GQ` in `LinkedTateLocal`: here through the section-level opens of
-- G0Assemble2.lean's `section G0A2_a85_linked` (l.61787-61789, which open `GlueC10`); every
-- candidate (`GlueC10.Qbar`, `PkgI4.Qbar`, ... ) is a reducible `abbrev` of `AlgebraicClosure ℚ`,
-- and `GQ` of `Qbar ≃ₐ[ℚ] Qbar`, so the statement is the same term up to reducible unfolding.
open CategoryTheory.MonObj
open GlueDescent GlueC10 PkgI3
open scoped TensorProduct

namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry
open G0ModField

/-- **Glue: linked Tate data with the Frobenius link and the local data** (g0-assemble2; replaces
g0-assemble's `LinkedTateData`, which asked for `G14TraceCompat` and `G15RamWild` themselves).
For every fibre context and G7 data: one pair `a, β : G_ℚ → ℚ̄` and embeddings `j₅, j₃` (the scalar
link, N5 L719-722), operator data at `ℓ = 5, 3` with g0-mod-galois' `G7Out` for the scalars
`j_ℓ ∘ a`, `j_ℓ ∘ β`, g14-trace's `FrobTraceLink` (N5 L781-786), and, for every `r₅`, `r₃` that G8
attaches to these data, g15-ram's `LocalData` (N5 L819-852: the local Galois closure and twist at
each `p`). `G14TraceCompat` then follows from T7 (g14-trace) and `G15RamWild` from the local
ramification theory (g15-ram, with T20, T21 proved in the kernel). -/
def LinkedTateLocal : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm₅ : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c₅ ε₅ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u₅ : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm₃ : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c₃ ε₃ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u₃ : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 Tm₅ c₅ ε₅
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u₃ ∧
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm₅ Tm₃ ∧
      ∀ (r₅ : PkgI4.GaloisRep 5 2) (r₃ : PkgI4.GaloisRep 3 2),
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5
          (GlueDescent.rho Tm₅ (fun g => j5 (aQ g)) (fun g => j5 (βQ g))) r₅ →
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3
          (GlueDescent.rho Tm₃ (fun g => j3 (aQ g)) (fun g => j3 (βQ g))) r₃ →
        (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @G15Ram.LocalData p ⟨hp⟩ 5 _ r₅) ∧
          G15Ram.LocalData 5 r₃

end HSyn.G0AssembleMod

end

/-! # lt-local, part 4: `LinkedTateLocal` on `TateBridge35`'s data

* `LinkedTateLocalD` (the corrected statement): g0-assemble2's `LinkedTateLocal` with the premise
  `[L:ℚ] ≤ D` added (as g8-object's `LinkedTateDataD` adds it to `LinkedTateData`).
* `ModelEndRank4` (GLUE, named here): `rank_ℤ End(A_{L'}) = 4` on G7's model. It is
  `TateBridge35`'s second hypothesis, and a consequence of `LinkedTateLocal` itself (its `G7Out`
  contains it), so it costs no truth.
* `localGlue_at`: lg-kerwild's `localGlue_of_transport`, with `UnramRoots p ℓ` needed only at
  `p = 2` (its proof, through local-glue's `localGlue_of_descent`).
* **`linkedTateLocalD_of_tateBridge35`**: R6 + I2-Tors + `UnramRoots 2 5` + `UnramRoots 2 3` +
  `TateBridge35` + `ModelEndRank4` ⟹ `LinkedTateLocalD`.
* `linkedTateLocal_of_D`: `LinkedTateLocalD` + `G7DegreeBound` ⟹ `LinkedTateLocal` (trivial;
  shows what the unrestricted statement would need). -/

noncomputable section

-- the section-level opens of G0Assemble2.lean's `section G0A2_a85_linked`, as for the copy
open CategoryTheory.MonObj
open GlueDescent GlueC10 PkgI3
open scoped TensorProduct

namespace LTLocal

open CategoryTheory AlgebraicGeometry
open G0ModField

/-- **Glue (G5-G6 on G7's model, N5 L528-563): the endomorphism ring of `A_{L'}` has rank 4.**
For every fibre context and G7 data, `rank_ℤ End(A_{L'}) = 4`. Proof plan (not formalized):
`≥ 4` from the QM structure `ι : 𝒪 → End(PK.A)` of `IsQMModel`, base-changed to `L'` (unram-tate's
`endBaseChange`; `𝒪` has rank 4 and `ι` is injective because `[n] ≠ 0`, cf. g0-assemble2's
`modelNoncomm_of_mulIsogeny`); `≤ 4` from `End(A_{L'})` a division-ring order (g0-split's
`FibreSimple`, already in `GluePieces3` through FS5) and Albert's bound `[End⁰(A):ℚ] ≤ 2g` for a
simple abelian variety in characteristic `0` (Mumford, *Abelian Varieties*, §21; locator
UNVERIFIED). This is `TateBridge35`'s (and g0-mod-field's `TateBridge`'s) second hypothesis. -/
def ModelEndRank4 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4

/-- **G4's degree bound on G7's data (GLUE, N5 L532-563).** `[L:ℚ] ≤ D` for every G7 datum in a
fibre context. g0-mod-field's `G4Out` carries this bound but its `G7Data` does not (local-data's
finding F3); `G7Data` admits fields `L` larger than G4's Hom field, so this Prop is not expected to
hold as stated (SPECULATIVE). It is named only to record what the unrestricted
`LinkedTateLocal` would need on this route; the fix is to add the bound to `G7Data`
(`LinkedTateLocalD`). -/
def G7DegreeBound : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' → Module.finrank ℚ L ≤ ZInQ.heightD

/-- **Glue (corrected `LinkedTateLocal`, for `GluePieces4`):** the text of g0-assemble2's
`HSyn.G0AssembleMod.LinkedTateLocal` (GLUE field 39 of `GluePieces3`) with the premise
`Module.finrank ℚ L ≤ ZInQ.heightD` added after `G7Data`. The local data at `p > D` (tame
closure of `L_v`) and the `G7Clauses` used at every `p` need this bound (N5 L848-851:
`[L_v:ℚ_p] ≤ D < p`). Proved from `TateBridge35`, `ModelEndRank4` and leaves
(`linkedTateLocalD_of_tateBridge35`). -/
def LinkedTateLocalD : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    Module.finrank ℚ L ≤ ZInQ.heightD →
    letI : NumberField L' := numberField_of_fd L'
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm₅ : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c₅ ε₅ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u₅ : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm₃ : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c₃ ε₃ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u₃ : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 Tm₅ c₅ ε₅
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u₃ ∧
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm₅ Tm₃ ∧
      ∀ (r₅ : PkgI4.GaloisRep 5 2) (r₃ : PkgI4.GaloisRep 3 2),
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5
          (GlueDescent.rho Tm₅ (fun g => j5 (aQ g)) (fun g => j5 (βQ g))) r₅ →
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3
          (GlueDescent.rho Tm₃ (fun g => j3 (aQ g)) (fun g => j3 (βQ g))) r₃ →
        (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @G15Ram.LocalData p ⟨hp⟩ 5 _ r₅) ∧
          G15Ram.LocalData 5 r₃

/-- **lg-kerwild's `localGlue_of_transport` with `UnramRoots` only at `p = 2` (proved; its proof,
through local-glue's `localGlue_of_descent`).** -/
theorem localGlue_at (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
    (hU : p = 2 → G15Ram.UnramRoots p ℓ) (hpℓ : p ≠ ℓ) {u : ℚ} {P : LeafQM.AV.QML3 Qbar} {L : IF}
    [FiniteDimensional ℚ L] [IsGalois ℚ L] {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] {hLL' : L ≤ L'} (hD : G7Data u P L A ε N χ β L' hLL')
    {Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    {c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ} {a : PkgI4.GQ → PadicAlgCl ℓ}
    {uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (hC : ∀ g, ιC (βQ g) = (β g : ℂ))
    (h7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a
        (fun g => j (βQ g)) uu)
    (hCl : G15Ram.G7Clauses (fun g => j (βQ g)) ε' L) :
    @G15Ram.LocalGlue p _ ℓ _ _ _ _ Tm a (fun g => j (βQ g)) L := by
  haveI : NumberField L' := numberField_of_fd L'
  have hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 := h7.1
  exact G15Ram.localGlue_of_descent hR6 hTors hpℓ h7 hCl
    (LGKerWild.kerWild_of_g7Data_alg hD βQ j ιC hC)
    (fun _ => LGKerWild.descentPts_of_g7 hLL' A hdim)
    (fun h2 => G15Ram.betaTwist2_of_unramRoots h2 hCl (hU h2))

/-- **`LinkedTateLocalD` from `TateBridge35` (proved).** Inputs: the leaves R6
(`ObjBridge.RaynaudCriterion`) and I2-Tors (`ObjBridge.TorsionStructure`); local-glue's textbook
Prop `UnramRoots` at `p = 2` for `ℓ = 5, 3`; g14-trace's glue `TateBridge35`; the glue
`ModelEndRank4`. Steps: `dim A_{L'} = 2` (`dim_bc_of_g7Data`) and `ModelEndRank4` feed
`TateBridge35`; its output gives `G7Out` at 5 and 3, `FrobTraceLink` and `ιC ∘ βQ = β`;
`G7Clauses` for `j_ℓ ∘ βQ` (`g7Clauses_of_transport`, with `[L:ℚ] ≤ D`); `LocalGlue` at `p ≠ ℓ`
(`localGlue_at`: lg-kerwild's `KerWild` and `DescentPts` discharges); `LocalData` for every `r_ℓ`
with G8's output (local-data's `localData_of_g7`). -/
theorem linkedTateLocalD_of_tateBridge35 (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU5 : G15Ram.UnramRoots 2 5)
    (hU3 : G15Ram.UnramRoots 2 3) (hB : G14Bridge.TateBridge35) (hRk : ModelEndRank4) :
    LinkedTateLocalD := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD hLD
  letI : NumberField L' := numberField_of_fd L'
  have hdim := dim_bc_of_g7Data hD
  have hrk := hRk Y Φ π u P hctx L A ε N χ β L' hLL' hD
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF, ιC, hC⟩ :=
    hB u P L A ε N χ β L' hLL' hD hdim hrk
  have hCl5 := g7Clauses_of_transport hD hLD βQ j5 ιC hC h5.2.2.2.2.1
  have hCl3 := g7Clauses_of_transport hD hLD βQ j3 ιC hC h3.2.2.2.2.1
  refine ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF,
    fun r5 r3 h85 h83 => ⟨fun p hp hp5 => ?_, ?_⟩⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    exact G15Ram.localData_of_g7 h85 hCl5
      (localGlue_at hR6 hTors (fun h2 => by subst h2; exact hU5) hp5 hD βQ j5 ιC hC h5 hCl5)
  · exact G15Ram.localData_of_g7 h83 hCl3
      (localGlue_at hR6 hTors (fun h2 => absurd h2 (by norm_num)) (by norm_num) hD βQ j3 ιC hC
        h3 hCl3)

/-- `LinkedTateLocalD` and `G7DegreeBound` give g0-assemble2's `LinkedTateLocal` (proved,
trivially). -/
theorem linkedTateLocal_of_D (h : LinkedTateLocalD) (hB : G7DegreeBound) :
    HSyn.G0AssembleMod.LinkedTateLocal :=
  fun Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD =>
    h Y Φ π u P hctx L A ε N χ β L' hLL' hD (hB Y Φ π u P hctx L A ε N χ β L' hLL' hD)

/-- The unrestricted Prop gives the restricted one (proved, trivially). -/
theorem linkedTateLocalD_of_local (h : HSyn.G0AssembleMod.LinkedTateLocal) : LinkedTateLocalD :=
  fun Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD _ =>
    h Y Φ π u P hctx L A ε N χ β L' hLL' hD

/-- `ModelEndRank4` follows from `LinkedTateLocal` (its `G7Out` at `5` contains the rank), so
naming it costs no truth (proved). -/
theorem modelEndRank4_of_localD (h : LinkedTateLocalD) (hB : G7DegreeBound) :
    ModelEndRank4 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, -⟩ :=
    h Y Φ π u P hctx L A ε N χ β L' hLL' hD (hB Y Φ π u P hctx L A ε N χ β L' hLL' hD)
  exact h5.2.1

end LTLocal

end

/-! # lt-local, part 5: `ModelEndRank4` from `FibreSimple` and linked-tate's `QMEndRank`

Verbatim copies from `scratch/linked-tate/LinkedTate.lean` (with their namespace headers and opens):
* def-faltings' `ZInQ.DefFaltings.AbVar`, `AbVar.baseChange` (l.17119, l.18210-18236);
* leaf-adopt's `LeafAdopt.abVarEquiv` (l.19042-19045, l.19196-19201);
* g0-split's `HSyn.G0Split.FibreOver` and `FibreSimple` (l.33338-33340, l.33577-33590,
  l.33712-33722; `FibreSimple` is the existing `GluePieces` piece, supplied in `GluePieces3`
  through FS5);
* linked-tate's `HSyn.LinkedTate.QMEndRank` (l.42841-42844, l.43121-43135; GLUE, literature-backed:
  Mumford §19 Thm 3 and Albert's classification, §21, numbering UNVERIFIED).
New: `endDivision_of_fibreSimple` (linked-tate's proof, copied) and `modelEndRank4_of_qmEndRank`
(the argument of linked-tate's `linkedTateCore_of`). -/

noncomputable section

namespace ZInQ.DefFaltings

section ModelsSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ExteriorAlgebra

/-- (copied from `ZInQKernel/HDecomp/Objects.lean`) An abelian variety over a field `K`: a group
object in schemes over `Spec K`, proper, smooth and geometrically integral. -/
structure AbVar (K : Type) [Field K] where
  /-- the underlying `K`-scheme -/
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

/-- (copied) Base change `A_L`. -/
noncomputable def AbVar.baseChange {K : Type} [Field K] (A : AbVar K) (L : Type) [Field L]
    [Algebra K L] : AbVar L :=
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  letI : GrpObj ((Over.pullback f).obj A.X) := Functor.grpObjObj
  haveI : IsProper ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : Smooth ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  { X := (Over.pullback f).obj A.X }

end ModelsSec

end ZInQ.DefFaltings

namespace LeafAdopt

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Bridge (proved)**: def-faltings' copy of the abelian-variety structure and this file's
`PkgI3.AbVar` (= the kernel's) are the same data (for `K : Type`), so R19-R21 and H5 transfer to
`PkgI3.AbVar` along this equivalence; unifying the two declarations is WP1 work. -/
def abVarEquiv (K : Type) [Field K] : ZInQ.DefFaltings.AbVar K ≃ PkgI3.AbVar K where
  toFun A := { X := A.X }
  invFun A := { X := A.X }

end LeafAdopt

namespace HSyn

open scoped MatrixGroups ModularForm

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

/-- `A`, an abelian variety over the number field `K` (def-faltings' `AbVar`), is (up to
isomorphism of `ℚ̄`-schemes, after some embedding `K → ℚ̄`) the abelian surface of an object
`(A, ι, η)` of `Y₃` at a `ℚ̄`-point `y` of `Y₃` lying over `J(u)` (for the moduli data
`(Y, Φ, π)` that R1-R2 provide). -/
def FibreOver (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K) : Prop :=
  ∃ (emb : K.K →+* Qbar) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P ∧ π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) ∧
    (letI : Algebra K.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X))

/-- **Missing piece 4 (glue G5-G6 on the actual `A`: QM dichotomy and NoCM).** For `u ∉ 𝒞`, the
fibre surface `A` (any number-field model of it) is simple over its field: every nonzero
endomorphism is an isogeny (because `End⁰(A_ℚ̄) = B` is a division algebra). Proved parts: T27 at
`B = (2,-3)` (`PkgI3.qmDichotomy_B6`), the Elkies identities and the free `W`-orbit
(`GlueRepo.PR.fibre_free`), `cm_of_val`. Missing: the instantiation on `A` and the counting with
R5 (h-decomposition G6). -/
def FibreSimple : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
      PkgI3.EndDivision (LeafAdopt.abVarEquiv K.K A)

end G0Split

end HSyn

namespace HSyn.LinkedTate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-- **Glue: the endomorphism ring of the QM model has rank 4** (linked-tate; G5-G6 + A9, N5
L564-577). For a `QML3` object `PK` over `K ⊆ ℚ̄` and a tower `K ≤ L ≤ L'` (`L'/ℚ` finite), if every
nonzero endomorphism of `A' = (PK.A)_{L,L'}` is an isogeny (`EndDivision`, which `FibreSimple`
supplies for the fibre), then `End_{L'}(A')` is a free `ℤ`-module of rank 4. Route (STANDARD,
UNVERIFIED numbering): `End(A')` is finitely generated and torsion-free (Mumford §19 Thm 3:
`End ⊗ ℤ_ℓ ↪ End T_ℓ`), so free; `End⁰(A')` is a division algebra containing `ι(B)`, `B = (2,−3)`
of dimension 4, and by Albert's classification for simple abelian surfaces in characteristic 0
(Mumford §21) it is `ℚ`, real quadratic, CM quartic or an indefinite quaternion algebra over `ℚ`;
only the last contains `B`, so `End⁰(A') = B`. GLUE (literature-backed). -/
def QMEndRank : Prop :=
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L') (PK : LeafQM.AV.QML3 K),
    PkgI3.EndDivision (@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL'))) = 4

end HSyn.LinkedTate

namespace LTLocal

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-- (copied from linked-tate; `Qbar` written `PkgI4.Qbar`) **`EndDivision` for every number-field model of the fibre, from the
glue piece `FibreSimple`** (proved). -/
theorem endDivision_of_fibreSimple (hFS : HSyn.G0Split.FibreSimple)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : LeafQM.AV.PtEquiv Y} {π : LeafQM.AV.ToP1 Y.left} {u : ℚ}
    {P : LeafQM.AV.QML3 PkgI4.Qbar} (hctx : FibreCtx Y Φ π u P) (L' : IF)
    [FiniteDimensional ℚ L'] (A' : PkgI3.AbVar L') (hA' : IsModelOver L' A' P) :
    PkgI3.EndDivision A' := by
  obtain ⟨h1, h2, hu, y, hy, hπ⟩ := hctx
  haveI : NumberField L' := numberField_of_fd L'
  exact hFS Y Φ π h1 h2 u hu ⟨L'⟩ ((LeafAdopt.abVarEquiv L').symm A')
    ⟨algebraMap L' PkgI4.Qbar, y, P, hy, hπ, hA'⟩

/-- **`ModelEndRank4` from `FibreSimple` and `QMEndRank` (proved;** the argument of linked-tate's
`linkedTateCore_of`): G7Data's `IsQMModel` writes `A = (PK.A)_L`, its last clause gives
`EndDivision A_{L'}` through `FibreSimple`, and `QMEndRank` gives the rank. -/
theorem modelEndRank4_of_qmEndRank (hFS : HSyn.G0Split.FibreSimple)
    (hR : HSyn.LinkedTate.QMEndRank) : ModelEndRank4 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  have hmod := hdata.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨K, hKL, PK, -, rfl⟩ := hdata.1
  exact hR K L L' hKL hLL' PK (endDivision_of_fibreSimple hFS hctx L' _ hmod)

/-- **`LinkedTateLocalD` from `TateBridge35`, `FibreSimple` and `QMEndRank` (proved).** -/
theorem linkedTateLocalD_of_tateBridge35' (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU5 : G15Ram.UnramRoots 2 5)
    (hU3 : G15Ram.UnramRoots 2 3) (hB : G14Bridge.TateBridge35)
    (hFS : HSyn.G0Split.FibreSimple) (hR : HSyn.LinkedTate.QMEndRank) : LinkedTateLocalD :=
  linkedTateLocalD_of_tateBridge35 hR6 hTors hU5 hU3 hB (modelEndRank4_of_qmEndRank hFS hR)

end LTLocal

end

#print axioms LTLocal.exists_equiv_extending
#print axioms LTLocal.g7Clauses_of_transport
#print axioms LTLocal.dim_bc_of_g7Data
#print axioms LTLocal.localGlue_at
#print axioms LTLocal.linkedTateLocalD_of_tateBridge35
#print axioms LTLocal.linkedTateLocal_of_D
#print axioms LTLocal.linkedTateLocalD_of_local
#print axioms LTLocal.modelEndRank4_of_localD
#print axioms LTLocal.endDivision_of_fibreSimple
#print axioms LTLocal.modelEndRank4_of_qmEndRank
#print axioms LTLocal.linkedTateLocalD_of_tateBridge35'

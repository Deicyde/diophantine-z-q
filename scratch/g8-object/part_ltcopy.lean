
/-! Copied verbatim from linked-tate's `scratch/linked-tate/parts/95_linked.lean` at its commit
dae5b706 (saved as `scratch/g8-object/lt_95_dae5b706.lean`): L218-228 (`RhoRamWild`), L266-309
(`LinkedTateCore`), L327-361 (`LinkedTateCoreDR`), in their namespace, with ModField's file-level
opens re-issued (active in their flat file). -/
section LinkedTateCopy

noncomputable section

namespace HSyn.LinkedTate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
open G0ModField

/-- **Glazer's wild-ramification clauses (i)-(ii) for an operator family `ρ` on `V`** (the form of
`LocalRamWild` on the descended `ρ_ℓ = β_ℓ⁻¹ a_ℓ Tm_ℓ` instead of on G8's `r_ℓ`; N5 L819-852,
D1-D4): for `p ≤ D` the absolute upper ramification groups `G_{ℚ_p}^t`, `t > U₀`, act trivially
through `decomp p`; for `p > D` wild inertia does. -/
def RhoRamWild (p : ℕ) (hp : p.Prime) {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) V) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) →
      ∀ t : ℝ, G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs p t, ρ (PkgI4.decomp p σ) = 1) ∧
    ((ZInQ.heightD : ℝ) < p → ∀ σ ∈ (LadicCond.wildSet : Set (PkgI4.GQp p)),
      ρ (PkgI4.decomp p σ) = 1)

/-- **Glue: linked Tate data on G7's model, at the level of the descended operators**
(linked-tate; the content of g0-assemble's `LinkedTateData` minus what is proved here). For every
fibre context and G7 data: one pair of scalar functions `a, β : G_ℚ → ℚ̄` and embeddings
`j₅ : ℚ̄ → ℚ̄₅`, `j₃ : ℚ̄ → ℚ̄₃` (N5 L719-722: the scalars `a_σ = deg(μ_σ)^{-1/4}`, `β_σ` lie in one
number field and are mapped to `ℚ̄_ℓ` by embeddings), and operator data at `ℓ = 5` and `ℓ = 3`
with
* g0-mod-galois' `G7Out` at each `ℓ` for the scalars `j_ℓ ∘ a`, `j_ℓ ∘ β` (the Tate functor applied
  to one family `m_σ = μ_σ ∘ σ`; g0-mod-field's `TateBridge`, which unram-tate proved for each `ℓ`
  separately from I3.M0, plus `dim A_{L'} = 2` and `rank_ℤ End(A_{L'}) = 4`);
* g14-trace's `FrobTraceLink` for the two operator families (N5 L777-786: reduction at a
  Frobenius, the relative Frobenius composed with `μ̄_τ`);
* Glazer's wild-ramification clauses (i)-(ii) for the descended operators `ρ₅` at `p ≠ 5` and
  `ρ₃` at `p = 5` (`RhoRamWild`; N5 L819-852, D1-D4).
GLUE. -/
def LinkedTateCore : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∃ (a b : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
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
        (fun g => j5 (a g)) (fun g => j5 (b g)) u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃
        (fun g => j3 (a g)) (fun g => j3 (b g)) u₃ ∧
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm₅ Tm₃ ∧
      ∀ p : ℕ, ∀ hp : p.Prime,
        (p ≠ 5 → RhoRamWild p hp
          (GlueDescent.rho Tm₅ (fun g => j5 (a g)) (fun g => j5 (b g)))) ∧
        (p = 5 → RhoRamWild p hp
          (GlueDescent.rho Tm₃ (fun g => j3 (a g)) (fun g => j3 (b g))))

/-- **Glue: `LinkedTateCore` given `dim A_{L'} = 2` and `rank End(A_{L'}) = 4`** (linked-tate; the
same conclusion as `LinkedTateCore`, under the two hypotheses that g0-mod-field's `TateBridge`
also assumes). GLUE. -/
def LinkedTateCoreDR : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    letI : NumberField L' := numberField_of_fd L'
    ∃ (a b : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
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
        (fun g => j5 (a g)) (fun g => j5 (b g)) u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃
        (fun g => j3 (a g)) (fun g => j3 (b g)) u₃ ∧
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm₅ Tm₃ ∧
      ∀ p : ℕ, ∀ hp : p.Prime,
        (p ≠ 5 → RhoRamWild p hp
          (GlueDescent.rho Tm₅ (fun g => j5 (a g)) (fun g => j5 (b g)))) ∧
        (p = 5 → RhoRamWild p hp
          (GlueDescent.rho Tm₃ (fun g => j3 (a g)) (fun g => j3 (b g))))

end HSyn.LinkedTate

end

end LinkedTateCopy

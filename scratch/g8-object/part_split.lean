
/-! ## g8-object, part 3: `TmWild` split into a closed lemma, a `G_L`-clause on G7's operators,
and a statement about `A/L` alone

`TmWild p Tm a F` (`a = 1`, `Tm = 1` on `G_F ∩ P_p` through `decomp`) is the one clause of
`LocalDataC` that mixes the `ℓ`-adic operators with the local field. It is split here into
* `ContainsL p L F`: `F` contains `j(L)` for an embedding `j : ℚ̄ → ℚ̄_p` compatible with `decomp`;
  then `decomp(G_F) ⊆ G_L` (`decomp_mem_fixing`, proved);
* `OnL`: on `G_L` (through `resQ L`), `a = 1` and `Tm` is the Tate action of `A/L`, transported by
  an isomorphism `ψ`. A `p`-independent clause on G7's data, the `G_L`-clause of g0-mod-field's
  `DescentDatum` (`a = 1`, `m_σ = σ` on `G_L`) after the Tate functor;
* `WildTateTrivial p L A ℓ F`: wild inertia of `G_F` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)` for the
  model `A/L` itself (R6 + D2 at `p ≤ D`; potential good reduction at `p > D`).
The restated local data `LocalDataS` then mention only `L`, `A/L`, `G7Data`'s `β` and local fields:
no `ℓ`-adic operator. -/

noncomputable section

namespace G8Object

open PkgI4 (GQ GQp GaloisRep decomp)
open LadicCond

section Split

open G0ModField

variable (p : ℕ) [Fact p.Prime]

/-- `F ⊆ ℚ̄_p` contains `j(L)` for an embedding `j : ℚ̄ → ℚ̄_p` that intertwines `decomp p σ` with
`σ` (the embedding underlying `PkgI4.decomp`; part 1 of g0-mod-newform's `decomp_spec`). -/
def ContainsL (L : IF) (F : Fld p) : Prop :=
  ∃ j : PkgI4.Qbar →+* PadicAlgCl p, (∀ (σ : GQp p) (x : PkgI4.Qbar), j (decomp p σ x) = σ (j x)) ∧
    ∀ x ∈ L, j x ∈ F

/-- **`decomp(G_F) ⊆ G_L` when `F ⊇ j(L)` (proved).** -/
theorem decomp_mem_fixing (L : IF) {F : Fld p} (hL : ContainsL p L F) {σ : GQp p}
    (hσ : σ ∈ fixSet F) : decomp p σ ∈ L.fixingSubgroup := by
  obtain ⟨j, hj, hjL⟩ := hL
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  apply j.injective
  rw [hj]
  exact hσ _ (hjL x hx)

variable {p}

/-- **Glue on G7's data, the `G_L`-clause (p-independent; N5 L638-647, L831).** Through
`resQ L : G_L → G_ℚ`, `a = 1` and `Tm` is the Tate action of the model `A/L`, transported to `V` by
an isomorphism `ψ`. For Glazer's data: `a_σ = 1` and `μ_σ = 1` on `G_L` (g0-mod-field's
`DescentDatum`), so `Tm(σ) = ℚ̄_ℓ ⊗ V_ℓ(m_σ)` is the Galois action, and `ψ` is the identification of
`V_ℓ(A_{L'})` with `V_ℓ(A)`. -/
def OnL (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L) {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*}
    [AddCommGroup V] [Module (PadicAlgCl ℓ) V] (Tm : GQ → Module.End (PadicAlgCl ℓ) V)
    (a : GQ → PadicAlgCl ℓ) (ψ : V ≃ₗ[PadicAlgCl ℓ] G0Galois.Vb A ℓ) : Prop :=
  ∀ σL : Field.absoluteGaloisGroup L,
    a (@G0Galois.resQ L _ (numberField_of_fd L) σL) = 1 ∧
    Tm (@G0Galois.resQ L _ (numberField_of_fd L) σL) =
      ψ.symm.toLinearMap ∘ₗ G0Galois.tate A ℓ σL ∘ₗ ψ.toLinearMap

variable (p)

/-- **Glue on the model `A/L` (R6 + D2 at `p ≤ D`, N5 L814-821; potential good reduction at
`p > D`, N5 L848-850).** Every `σ ∈ G_F ∩ P_p` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)` through any
`σ_L ∈ G_L` with `resQ L σ_L = decomp p σ`. For `F ⊇ L_v(A[3])` (`A[5]` if `p = 3`), Raynaud's
criterion (`PkgI2.RaynaudCriterion`) makes `A` semistable over `F`, and wild inertia then acts
trivially for `ℓ ≠ p` (`PkgI2.D2_fixed_of_raynaud`). For `p > D` (`F` the Galois closure of
`L_v`): QM surfaces have potentially good reduction everywhere, and the finite inertia image has
order divisible only by primes `≤ 5` (Serre–Tate). A statement about `A/L` and `F` alone. -/
def WildTateTrivial (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L) (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, ∀ σL : Field.absoluteGaloisGroup L,
    @G0Galois.resQ L _ (numberField_of_fd L) σL = decomp p σ → G0Galois.tate A ℓ σL = 1

variable {p}

/-- **`TmWild` from the split (proved).** -/
theorem tmWild_of_split {L : IF} [FiniteDimensional ℚ L] [IsGalois ℚ L] {A : PkgI3.AbVar L}
    {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a : GQ → PadicAlgCl ℓ}
    {ψ : V ≃ₗ[PadicAlgCl ℓ] G0Galois.Vb A ℓ} (hOn : OnL L A Tm a ψ) {F : Fld p}
    (hL : ContainsL p L F) (hW : WildTateTrivial p L A ℓ F) : TmWild p Tm a F := by
  intro σ hσ
  have hmem := decomp_mem_fixing p L hL hσ.1
  rw [← resQ_range L] at hmem
  obtain ⟨σL, hσL⟩ := hmem
  have hσL' : @G0Galois.resQ L _ (numberField_of_fd L) σL = decomp p σ := hσL
  obtain ⟨ha, hT⟩ := hOn σL
  rw [hσL'] at ha hT
  refine ⟨ha, ?_⟩
  rw [hT, hW σ hσ σL hσL']
  ext v
  simp

variable (p)

/-- **G15's local data on G7Data's objects only** (`L`, the model `A/L`, the cochain `β`): the
restated `LocalDataC` with `TmWild` replaced by `ContainsL ∧ WildTateTrivial`. No `ℓ`-adic
operator occurs. -/
def LocalDataS (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L) (ℓ : ℕ) [Fact ℓ.Prime]
    (βC : GQ → ℂˣ) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ F : Fld p, IsFinGal F ∧
      ramCard F 0 ≤ (ZInQ.heightD * ZInQ.heightG0).factorial ∧
      ContainsL p L F ∧ WildTateTrivial p L A ℓ F ∧ BetaUpperC p βC F G0ModNewform.U0) ∧
    ((ZInQ.heightD : ℝ) < p → ∃ F : Fld p, IsFinGal F ∧ ¬ p ∣ ramCard F 0 ∧
      ContainsL p L F ∧ WildTateTrivial p L A ℓ F ∧ BetaTameC p βC F)

variable {p}

/-- **`LocalDataC` from `OnL` and `LocalDataS` (proved).** -/
theorem localDataC_of_S {L : IF} [FiniteDimensional ℚ L] [IsGalois ℚ L] {A : PkgI3.AbVar L}
    {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a : GQ → PadicAlgCl ℓ}
    {ψ : V ≃ₗ[PadicAlgCl ℓ] G0Galois.Vb A ℓ} (hOn : OnL L A Tm a ψ) {βC : GQ → ℂˣ}
    (h : LocalDataS p L A ℓ βC) : LocalDataC p Tm a βC := by
  refine ⟨fun hpD => ?_, fun hpD => ?_⟩
  · obtain ⟨F, hF, he, hL, hW, hb⟩ := h.1 hpD
    exact ⟨F, hF, he, tmWild_of_split hOn hL hW, hb⟩
  · obtain ⟨F, hF, he, hL, hW, hb⟩ := h.2 hpD
    exact ⟨F, hF, he, tmWild_of_split hOn hL hW, hb⟩

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent.B2

/-- **The restated `GluePieces2` field, split form (GLUE).** g14-trace's `TateBridge35` data, the
`G_L`-clause `OnL` for `Tm₅`, `Tm₃` (with isomorphisms `ψ₅`, `ψ₃` to the Tate modules of the model
`A/L`), and G15's local data `LocalDataS` on `G7Data`'s `L`, `A`, `β` (`ℓ = 5` at `p ≠ 5`, `ℓ = 3`
at `p = 5`). -/
def LinkedTateObjS : Prop :=
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
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (ψ₅ : G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 ≃ₗ[PadicAlgCl 5]
        G0Galois.Vb A 5)
      (ψ₃ : G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 ≃ₗ[PadicAlgCl 3]
        G0Galois.Vb A 3),
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 Tm₅ c₅ ε₅
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u₃ ∧
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm₅ Tm₃ ∧
      (∃ ιC : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = (β g : ℂ)) ∧
      OnL L A Tm₅ (fun g => j5 (aQ g)) ψ₅ ∧ OnL L A Tm₃ (fun g => j3 (aQ g)) ψ₃ ∧
      (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalDataS p ⟨hp⟩ L _ A 5 _ β) ∧
      LocalDataS 5 L A 3 β

/-- **`LinkedTateObj` from the split form (GLUE, proved).** -/
theorem linkedTateObj_of_S (hS : LinkedTateObjS) : LinkedTateObj := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨aQ, βQ, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, ψ₅, ψ₃, h75, h73, hF, hι, hOn5, hOn3,
    hl5, hl3⟩ := hS Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  exact ⟨aQ, βQ, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, h75, h73, hF, hι,
    fun p hp hp5 => @localDataC_of_S p ⟨hp⟩ L _ _ A 5 _ _ _ _ _ _ _ hOn5 β (hl5 p hp hp5),
    localDataC_of_S hOn3 hl3⟩

/-- **g0-assemble's `LinkedTateData` from the split form and T7 (proved).** -/
theorem linkedTateData_of_S (hM : PkgI3.CharPolyIndepOfEll) (hS : LinkedTateObjS) :
    HSyn.G0AssembleMod.LinkedTateData :=
  linkedTateData_of_obj hM (linkedTateObj_of_S hS)

end Split

end G8Object

end

#print axioms G8Object.decomp_mem_fixing
#print axioms G8Object.tmWild_of_split
#print axioms G8Object.localDataC_of_S
#print axioms G8Object.linkedTateObj_of_S
#print axioms G8Object.linkedTateData_of_S

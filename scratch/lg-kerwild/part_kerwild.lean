/-! ## lg-kerwild: `KerWild` from G7Data through the Tate bridge, `DescentPts` on G7Data's model

Task lg-kerwild (2026-11-13). local-glue (`G15Ram.localGlue_of_unramRoots`) left two glue Props:
`G15Ram.KerWild K β L` (G7Data's kernel-field clause, dropped by `G7Out` and by g0-mod-field's
`TateBridge`, local-glue finding G8) and `G15Ram.DescentPts A L` (used at `p ≤ 5`).

This part:
* `kerWild_of_ker`: `KerWild L' β L` from G7Data's clause `G_{L'} = G_L ∩ ker β_ℂ` and any
  transport with `β(g) = 1 → β_ℂ(g) = 1`; `kerWild_of_alg` for the transport of g14-trace's
  `TateBridge35` (`β = j ∘ β_ℚ̄`, `β_ℂ = ι_ℂ ∘ β_ℚ̄`, `j`, `ι_ℂ` field embeddings, so injective);
  `kerWild_of_g7Data_alg` reads the clause off `G7Data`.
* `TateBridgeK`: g0-mod-field's `TateBridge` with `KerWild` added to its output (the correction of
  finding G8); `TateBridgeT`: `TateBridge` with the scalar transport added to its output (as
  `TateBridge35` has it); `tateBridgeK_of_T`, `tateBridge_of_K` (proved).
* `TateBridge35K`: g14-trace's `TateBridge35` with `KerWild` at `ℓ = 5, 3` added;
  `tateBridge35K_of_35 : TateBridge35 → TateBridge35K` (proved: the clause is transported from
  `G7Data`, nothing new is assumed); `tateBridgeK_five_three_of_35` (the `ℓ = 5, 3` conclusions
  of `TateBridgeK` from `TateBridge35`).
* `dim_model_of_bc`: `dim A = 2` from `dim A_{L'} = 2` (g0-dim's `pkgI3_dim_baseChange`);
  `descentPts_of_g7` : `DescentPts (A_{L'}) L` for G7Data's model `A/L`.
* `localGlue_of_tateBridge35`: local-glue's `LocalGlue` on `TateBridge35`'s data at `ℓ = 5, 3`
  from R6, I2-Tors, `UnramRoots` and `G7Clauses`, with no `KerWild` or `DescentPts` hypothesis.
-/

section LGKerWildSec

noncomputable section

namespace LGKerWild

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent G0ModField

/-! ### §1. `KerWild` from the kernel-field clause -/

/-- **`KerWild` from G7Data's kernel-field clause and a transport that detects `β = 1`
(proved).** `G_{L'} = G_L ∩ ker β_ℂ` (G7Data, `GQL L = L.fixingSubgroup`), `L'` finite Galois, and
`β_ℓ(g) = 1 ⇒ β_ℂ(g) = 1` give `KerWild L' β_ℓ L` for `G7Out`'s model field `K = L'`. -/
theorem kerWild_of_ker {ℓ : ℕ} [Fact ℓ.Prime] {L L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] (βC : PkgI4.GQ → ℂˣ)
    (hker : ∀ σ : PkgI4.GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1)
    {β : PkgI4.GQ → PadicAlgCl ℓ} (hβ : ∀ g, β g = 1 → βC g = 1) :
    @G15Ram.KerWild ℓ _ L' _ (RQ.numberField_of_fd L') β L := by
  intro g hgL hg1
  have h3 : g ∈ L'.fixingSubgroup :=
    (hker g).mpr ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).mpr hgL, hβ g hg1⟩
  rw [RQ.resQ_range L']
  exact h3

/-- **The algebraic transport detects `β = 1` (proved).** If `β_ℓ = j ∘ β_ℚ̄` and
`β_ℂ = ι_ℂ ∘ β_ℚ̄` for `ℚ`-algebra maps `j : ℚ̄ → ℚ̄_ℓ`, `ι_ℂ : ℚ̄ → ℂ` (injective, `ℚ̄` a field),
then `β_ℓ(g) = 1 ⇒ β_ℂ(g) = 1`. -/
theorem transport_one {ℓ : ℕ} [Fact ℓ.Prime] (βQ : PkgI4.GQ → PkgI4.Qbar)
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (βC : PkgI4.GQ → ℂˣ)
    (hC : ∀ g, ιC (βQ g) = (βC g : ℂ)) (g : PkgI4.GQ) (h1 : j (βQ g) = 1) : βC g = 1 := by
  have hQ : βQ g = 1 := j.toRingHom.injective (by rw [h1, map_one])
  apply Units.ext
  rw [← hC g, hQ, map_one, Units.val_one]

/-- **`KerWild` for the algebraic transport (proved).** -/
theorem kerWild_of_alg {ℓ : ℕ} [Fact ℓ.Prime] {L L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] (βC : PkgI4.GQ → ℂˣ)
    (hker : ∀ σ : PkgI4.GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1)
    (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (hC : ∀ g, ιC (βQ g) = (βC g : ℂ)) :
    @G15Ram.KerWild ℓ _ L' _ (RQ.numberField_of_fd L') (fun g => j (βQ g)) L :=
  kerWild_of_ker βC hker (fun g h1 => transport_one βQ j ιC βC hC g h1)

/-- G7Data's kernel-field clause (clause 9), as an equality of fixing subgroups. -/
theorem g7Data_ker {u : ℚ} {P : QML3 Qbar} {L : IF} {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ}
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} {hLL' : L ≤ L'}
    (h : G7Data u P L A ε N χ β L' hLL') :
    ∀ σ : PkgI4.GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ β σ = 1 :=
  h.2.2.2.2.2.2.2.2.1

/-- **`KerWild` transported from `G7Data` (proved).** For G7's data and an algebraic form `β_ℚ̄`
of its `β` (`ι_ℂ ∘ β_ℚ̄ = β`), every `j : ℚ̄ → ℚ̄_ℓ` gives `KerWild L' (j ∘ β_ℚ̄) L`. -/
theorem kerWild_of_g7Data_alg {ℓ : ℕ} [Fact ℓ.Prime] {u : ℚ} {P : QML3 Qbar} {L : IF}
    {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L'] [IsGalois ℚ L'] {hLL' : L ≤ L'}
    (h : G7Data u P L A ε N χ β L' hLL') (βQ : PkgI4.GQ → PkgI4.Qbar)
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
    (hC : ∀ g, ιC (βQ g) = (β g : ℂ)) :
    @G15Ram.KerWild ℓ _ L' _ (RQ.numberField_of_fd L') (fun g => j (βQ g)) L :=
  kerWild_of_alg β (g7Data_ker h) βQ j ιC hC

/-! ### §2. The corrected bridges -/

/-- **Bridge 2 with the kernel-field clause (GLUE; correction of g0-mod-field's `TateBridge`,
local-glue finding G8).** `TateBridge`'s statement, with `KerWild L' β' L` (G7Data's clause
`G_{L'} = G_L ∩ ker β`, for the `ℚ̄_ℓ`-valued `β'`: `g ∈ G_L`, `β'(g) = 1` ⟹ `g ∈ G_{L'}`) added
to its output. Source: N5 L702-716 (`L'` is the kernel field of `β|G_L`). -/
def TateBridgeK : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') β' L

/-- **Bridge 2 with the scalar transport (GLUE; the form in which `TateBridge35` states it).**
`TateBridge`'s statement with, in its output, an algebraic form `β_ℚ̄ : G_ℚ → ℚ̄` of G7Data's
`β` (`ι_ℂ ∘ β_ℚ̄ = β`) and an embedding `j : ℚ̄ → ℚ̄_ℓ` with `β' = j ∘ β_ℚ̄` (N5 L719-722: the
values of `β` are algebraic and are mapped into `ℚ̄_ℓ` by one embedding). -/
def TateBridgeT : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      ∃ (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
        (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ), (∀ g, β' g = j (βQ g)) ∧ ∀ g, ιC (βQ g) = (β g : ℂ)

/-- **`TateBridgeK` contains `TateBridge` (proved).** -/
theorem tateBridge_of_K (h : TateBridgeK) : TateBridge := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrk ℓ _
  obtain ⟨Tm, c, ε', a, β', uu, h7, -⟩ := h u P L A ε N χ β L' hLL' hD hdim hrk ℓ
  exact ⟨Tm, c, ε', a, β', uu, h7⟩

/-- **The transport form gives the kernel-field form (proved)**: `KerWild` is transported from
`G7Data` (`kerWild_of_g7Data_alg`). -/
theorem tateBridgeK_of_T (h : TateBridgeT) : TateBridgeK := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrk ℓ _
  obtain ⟨Tm, c, ε', a, β', uu, h7, βQ, j, ιC, hj, hC⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk ℓ
  refine ⟨Tm, c, ε', a, β', uu, h7, ?_⟩
  have hβ' : β' = fun g => j (βQ g) := funext hj
  subst hβ'
  exact kerWild_of_g7Data_alg hD βQ j ιC hC

/-- **g14-trace's `TateBridge35` with the kernel-field clause at `ℓ = 5, 3` (GLUE).**
`TateBridge35`'s statement with `KerWild L' (j_ℓ ∘ β_ℚ̄) L` for `ℓ = 5, 3` added to the output.
It follows from `TateBridge35` (`tateBridge35K_of_35`). -/
def TateBridge35K : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c5 ε5 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u5 : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c3 ε3 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u3 : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm5 c5 ε5
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u5 ∧
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm3 c3 ε3
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u3 ∧
      @G14Bridge.FrobTraceLink L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm5 Tm3 ∧
      (∃ ιC : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = (β g : ℂ)) ∧
      @G15Ram.KerWild 5 _ L' _ (numberField_of_fd L') (fun g => j5 (βQ g)) L ∧
      @G15Ram.KerWild 3 _ L' _ (numberField_of_fd L') (fun g => j3 (βQ g)) L

/-- **`TateBridge35` gives `TateBridge35K` (proved)**: the kernel-field clause at `ℓ = 5, 3` is
transported from `G7Data` through `TateBridge35`'s own clause `ι_ℂ ∘ β_ℚ̄ = β`. -/
theorem tateBridge35K_of_35 (h : G14Bridge.TateBridge35) : TateBridge35K := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrk
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF, ιC, hC⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk
  exact ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF, ⟨ιC, hC⟩,
    kerWild_of_g7Data_alg hD βQ j5 ιC hC, kerWild_of_g7Data_alg hD βQ j3 ιC hC⟩

/-- **`TateBridge35` gives the `ℓ = 5` and `ℓ = 3` conclusions of `TateBridgeT` (proved).** -/
theorem tateBridgeT_at_of_35 (h : G14Bridge.TateBridge35) (u : ℚ) (P : QML3 Qbar)
    (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4) :
    ∀ ℓ, (ℓ = 5 ∨ ℓ = 3) → ∀ [Fact ℓ.Prime],
    ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      ∃ (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
        (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ), (∀ g, β' g = j (βQ g)) ∧ ∀ g, ιC (βQ g) = (β g : ℂ) := by
  intro ℓ hℓ _
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, -, ιC, hC⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk
  rcases hℓ with rfl | rfl
  · exact ⟨Tm5, c5, ε5, _, _, u5, h5, βQ, j5, ιC, fun _ => rfl, hC⟩
  · exact ⟨Tm3, c3, ε3, _, _, u3, h3, βQ, j3, ιC, fun _ => rfl, hC⟩

/-- **`TateBridge35` gives the `ℓ = 5` and `ℓ = 3` conclusions of `TateBridgeK` (proved).** -/
theorem tateBridgeK_at_of_35 (h : G14Bridge.TateBridge35) (u : ℚ) (P : QML3 Qbar)
    (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4) :
    ∀ ℓ, (ℓ = 5 ∨ ℓ = 3) → ∀ [Fact ℓ.Prime],
    ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') β' L := by
  intro ℓ hℓ _
  obtain ⟨Tm, c, ε', a, β', uu, h7, βQ, j, ιC, hj, hC⟩ :=
    tateBridgeT_at_of_35 h u P L A ε N χ β L' hLL' hD hdim hrk ℓ hℓ
  refine ⟨Tm, c, ε', a, β', uu, h7, ?_⟩
  have hβ' : β' = fun g => j (βQ g) := funext hj
  subst hβ'
  exact kerWild_of_g7Data_alg hD βQ j ιC hC

/-! ### §3. `DescentPts` on G7Data's model -/

/-- **`dim A = 2` for the model `A/L` from `dim A_{L'} = 2` (proved)**, by g0-dim's
`pkgI3_dim_baseChange` (dimension is invariant under field base change, Stacks 00P4). -/
theorem dim_model_of_bc {L L' : IF} (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2) : A.dim = 2 :=
  (@G0Dim.pkgI3_dim_baseChange L _ L' _ (incAlg hLL') A).symm.trans hdim

/-- **`DescentPts` for `A_{L'}` and G7's model field `L` (proved)**: `TateBridge`'s abelian
variety is the base change `A_{L'}` of the model `A/L` (`G7Data`), so local-glue's
`descentPts_baseChange` (with the conjugate model when Mathlib's embeddings differ, finding G9)
applies; `dim A = 2` comes from `dim A_{L'} = 2` (`dim_model_of_bc`). -/
theorem descentPts_of_g7 {L L' : IF} [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [FiniteDimensional ℚ L'] (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2) :
    @G15Ram.DescentPts L' _ (numberField_of_fd L')
      (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) L _ :=
  G15Ram.descentPts_baseChange hLL' A (dim_model_of_bc hLL' A hdim)

/-! ### §4. `LocalGlue` on the Tate bridge's data, with no local glue Prop -/

/-- **`LocalGlue` on the data of the transport form of the Tate bridge (proved).** For G7's
data, `dim A_{L'} = 2`, `G7Out` at `ℓ` for `A_{L'}` with `β' = j ∘ β_ℚ̄` where `ι_ℂ ∘ β_ℚ̄ = β`
(the output of `TateBridgeT`, or of `TateBridge35` at `ℓ = 5, 3`), and G7's clauses
(`G7Clauses`): `LocalGlue p Tm a β' L` at every `p ≠ ℓ`, from the leaves R6 and I2-Tors and the
textbook Prop `UnramRoots` (used at `p = 2`). -/
theorem localGlue_of_transport (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
    (hU : G15Ram.UnramRoots p ℓ) (hpℓ : p ≠ ℓ) {u : ℚ} {P : QML3 Qbar} {L : IF}
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
  exact G15Ram.localGlue_of_unramRoots hR6 hTors hU hpℓ h7 hCl
    (kerWild_of_g7Data_alg hD βQ j ιC hC) (fun _ => descentPts_of_g7 hLL' A hdim)

/-- **`LocalGlue` on `TateBridge35`'s data at `ℓ = 5` and `ℓ = 3` (proved).** For G7's data and the
output of g14-trace's `TateBridge35`, with G7's clauses for `j_ℓ ∘ β_ℚ̄`: `LocalGlue` at every
`p ≠ 5` for `Tm₅` and at every `p ≠ 3` for `Tm₃`, from R6, I2-Tors and `UnramRoots`. -/
theorem localGlue_of_tateBridge35 (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ)
    {u : ℚ} {P : QML3 Qbar} {L : IF}
    [FiniteDimensional ℚ L] [IsGalois ℚ L] {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] {hLL' : L ≤ L'} (hD : G7Data u P L A ε N χ β L' hLL')
    (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
    (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
    (c5 ε5 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
    (u5 : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
    (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
    (c3 ε3 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
    (u3 : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
    (h5 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm5 c5 ε5
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u5)
    (h3 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm3 c3 ε3
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u3)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (hC : ∀ g, ιC (βQ g) = (β g : ℂ))
    (hCl5 : G15Ram.G7Clauses (fun g => j5 (βQ g)) ε5 L)
    (hCl3 : G15Ram.G7Clauses (fun g => j3 (βQ g)) ε3 L) :
    (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 →
      @G15Ram.LocalGlue p ⟨hp⟩ 5 _ _ _ _ Tm5 (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) L) ∧
    (∀ (p : ℕ) (hp : p.Prime), p ≠ 3 →
      @G15Ram.LocalGlue p ⟨hp⟩ 3 _ _ _ _ Tm3 (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) L) := by
  refine ⟨fun p hp hp5 => ?_, fun p hp hp3 => ?_⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    exact localGlue_of_transport hR6 hTors (hU p 5) hp5 hD βQ j5 ιC hC h5 hCl5
  · haveI : Fact p.Prime := ⟨hp⟩
    exact localGlue_of_transport hR6 hTors (hU p 3) hp3 hD βQ j3 ιC hC h3 hCl3

end LGKerWild

end

end LGKerWildSec

#print axioms LGKerWild.kerWild_of_ker
#print axioms LGKerWild.transport_one
#print axioms LGKerWild.kerWild_of_alg
#print axioms LGKerWild.g7Data_ker
#print axioms LGKerWild.kerWild_of_g7Data_alg
#print axioms LGKerWild.tateBridge_of_K
#print axioms LGKerWild.tateBridgeK_of_T
#print axioms LGKerWild.tateBridge35K_of_35
#print axioms LGKerWild.tateBridgeT_at_of_35
#print axioms LGKerWild.tateBridgeK_at_of_35
#print axioms LGKerWild.dim_model_of_bc
#print axioms LGKerWild.descentPts_of_g7
#print axioms LGKerWild.localGlue_of_transport
#print axioms LGKerWild.localGlue_of_tateBridge35

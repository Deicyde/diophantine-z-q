
/-! ## g8-object, part 2: the full G12-G16 interface on the object; the restated `GluePieces2`
field (`LinkedTateObj`) checked against g0-assemble's `LinkedTateData`

Appended after verbatim copies of g0-mod-field (`ModField.lean`), g14-trace (`G14Trace.lean`,
`part_bridge.lean`), g15-ram (`G15Ram.lean` §1-§3), g0-mod-galois' definitions, part 1
(`part_obj.lean`) and g0-assemble's `87_afterg7.lean` L27-123 (`ModelG3G6`, `LocalRamWild`,
`G15RamWild`, `g15RamG_of_wild`, `LinkedTateData`). -/

noncomputable section

namespace G8Object

open PkgI4 (GQ GQp GaloisRep decomp)
open LadicCond

/-! ### §E. Linked objects: `G12Spec ∧ G14TraceCompat ∧ G15RamG` on the constructed `r_ℓ` -/

section Linked

variable {K : Type} [Field K] [NumberField K]

/-- **The linked object at `ℓ = 5, 3`** (N5 L719-722): the descent data at `5` and `3` (each with
its constructed `r_ℓ`), whose scalars are the images `j_ℓ ∘ aQ`, `j_ℓ ∘ βQ` of one pair
`aQ, βQ : G_ℚ → ℚ̄` (the scalar link of g14-trace), with g14-trace's Frobenius link
`FrobTraceLink` for `Tm₅`, `Tm₃`. -/
structure LinkedObj (A : PkgI3.AbVar K) where
  D5 : DescData A 5
  D3 : DescData A 3
  aQ : GQ → PkgI4.Qbar
  βQ : GQ → PkgI4.Qbar
  j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5
  j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3
  ha5 : D5.a = fun g => j5 (aQ g)
  hb5 : D5.β = fun g => j5 (βQ g)
  ha3 : D3.a = fun g => j3 (aQ g)
  hb3 : D3.β = fun g => j3 (βQ g)
  frob : G14Trace.FrobTraceLink A D5.Tm D3.Tm

/-- G8's output for the constructed `r_ℓ`, in the form g14-trace consumes (scalars written
through the link). -/
theorem LinkedObj.galG8Out5 {A : PkgI3.AbVar K} (Lk : LinkedObj A) (hS : PkgI3.FaltingsSemisimple)
    (hF : PkgI3.FaltingsTate) (hT : PkgI3.TateModuleFree) (hH : PkgI3.HomFreeFinite)
    (hSS : GlueI3.SemisimpleBaseChange) (hB : G0Galois.BurnsideAbsIrred) :
    G0ModNewform.GalG8Out A 5
      (GlueDescent.rho Lk.D5.Tm (fun g => Lk.j5 (Lk.aQ g)) (fun g => Lk.j5 (Lk.βQ g))) Lk.D5.r := by
  have h := Lk.D5.g8Out hS hF hT hH hSS hB
  rw [Lk.ha5, Lk.hb5] at h
  exact h

theorem LinkedObj.galG8Out3 {A : PkgI3.AbVar K} (Lk : LinkedObj A) (hS : PkgI3.FaltingsSemisimple)
    (hF : PkgI3.FaltingsTate) (hT : PkgI3.TateModuleFree) (hH : PkgI3.HomFreeFinite)
    (hSS : GlueI3.SemisimpleBaseChange) (hB : G0Galois.BurnsideAbsIrred) :
    G0ModNewform.GalG8Out A 3
      (GlueDescent.rho Lk.D3.Tm (fun g => Lk.j3 (Lk.aQ g)) (fun g => Lk.j3 (Lk.βQ g))) Lk.D3.r := by
  have h := Lk.D3.g8Out hS hF hT hH hSS hB
  rw [Lk.ha3, Lk.hb3] at h
  exact h

/-- **The restated G12-G15 interface holds on the object (GLUE, proved).** For a linked object,
G12's output for the constructed `r₅` (`GalG12Out`, which g0-mod-galois' `g12` proves for any `r`
with G8's output), the restated local data `LocalDataG` on the descent data, and G2, G3: there is
`M : ModObj A` carrying the two descent data, with g0-mod-newform's `G12Spec`,
`G14TraceCompat` and `G15RamG` on `M.toModData`. Inputs: C2's leaves (R9a, R9b, T26, T6),
glue-ssbc's `SemisimpleBaseChange`, Burnside, T7 (`CharPolyIndepOfEll`) and g0-mod-newform's
`DirichletOfFinite`. -/
theorem interface_obj (hDF : G0ModNewform.DirichletOfFinite) (hM : PkgI3.CharPolyIndepOfEll)
    (hS : PkgI3.FaltingsSemisimple) (hF : PkgI3.FaltingsTate) (hT : PkgI3.TateModuleFree)
    (hH : PkgI3.HomFreeFinite) (hSS : GlueI3.SemisimpleBaseChange)
    (hB : G0Galois.BurnsideAbsIrred) {A : PkgI3.AbVar K} (Lk : LinkedObj A) (u : ℚ)
    (h12 : G0ModNewform.GalG12Out Lk.D5.r)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalDataG p ⟨hp⟩ 5 _ _ _ _ Lk.D5.Tm Lk.D5.a Lk.D5.β)
    (h3 : LocalDataG 5 Lk.D3.Tm Lk.D3.a Lk.D3.β)
    (h2 : G0Galois.G2Out K (GlueDescent.ramSet ZInQ.Mult.S_mul u))
    (h35 : G0Galois.G3Out A 5 (GlueDescent.ramSet ZInQ.Mult.S_mul u))
    (h33 : G0Galois.G3Out A 3 (GlueDescent.ramSet ZInQ.Mult.S_mul u)) :
    ∃ M : ModObj A, M.D5 = Lk.D5 ∧ M.D3 = Lk.D3 ∧ G0ModNewform.G12Spec M.toModData ∧
      G0ModNewform.G14TraceCompat M.toModData ∧ G0ModNewform.G15RamG M.toModData u := by
  obtain ⟨⟨i, ιC, ι5, ι3, r5, r3⟩, hD5, hD3, hs, hc⟩ :=
    G14Trace.g12Spec_g14_of_galois hDF hM A Lk.j5 Lk.j3 Lk.aQ Lk.βQ Lk.D5.Tm Lk.D3.Tm Lk.D5.r
      Lk.D3.r (Lk.galG8Out5 hS hF hT hH hSS hB) (Lk.galG8Out3 hS hF hT hH hSS hB) h12 Lk.frob
  dsimp only at hD5 hD3
  subst hD5 hD3
  let M : ModObj A := ⟨i, ιC, ι5, ι3, Lk.D5, Lk.D3⟩
  exact ⟨M, rfl, rfl, hs, hc, g15RamG_obj M u h5 h3 h2 h35 h33⟩

open PkgI3 PkgI3.AbVar LeafModCurves C9Rhof in
/-- **G13-G16 on the object (GLUE, proved).** g0-mod-newform's `modularConstituent_tail_G`, with
its hypothesis `∃ D, G12Spec D ∧ G14TraceCompat D ∧ G15RamG D u` discharged by `interface_obj`:
the open inputs are now Props on G7's data (`LocalDataG`, `FrobTraceLink`, the scalar link),
G12's output and the leaves. -/
theorem modularConstituent_tail_obj (lv : G0ModNewform.NewformLeaves) (hJac : LeafModCurves.JacobianExists ℚ)
    (hX : LeafModCurves.X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hDF : G0ModNewform.DirichletOfFinite) (hM : PkgI3.CharPolyIndepOfEll)
    (hS : PkgI3.FaltingsSemisimple) (hF : PkgI3.FaltingsTate) (hT : PkgI3.TateModuleFree)
    (hH : PkgI3.HomFreeFinite) (hSS : GlueI3.SemisimpleBaseChange)
    (hB : G0Galois.BurnsideAbsIrred) {A : PkgI3.AbVar K} (Lk : LinkedObj A) (u : ℚ)
    (h12 : G0ModNewform.GalG12Out Lk.D5.r)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalDataG p ⟨hp⟩ 5 _ _ _ _ Lk.D5.Tm Lk.D5.a Lk.D5.β)
    (h3 : LocalDataG 5 Lk.D3.Tm Lk.D3.a Lk.D3.β)
    (h2 : G0Galois.G2Out K (GlueDescent.ramSet ZInQ.Mult.S_mul u))
    (h35 : G0Galois.G3Out A 5 (GlueDescent.ramSet ZInQ.Mult.S_mul u))
    (h33 : G0Galois.G3Out A 3 (GlueDescent.ramSet ZInQ.Mult.S_mul u)) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ LeafModCurves.IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      G0ModNewform.CommonConstituent A (J.baseChange K) := by
  obtain ⟨M, -, -, hs, hc, hr⟩ := interface_obj hDF hM hS hF hT hH hSS hB Lk u h12 h5 h3 h2 h35 h33
  exact G0ModNewform.modularConstituent_tail_G lv hJac hX hSw hL8 hAd A u ⟨M.toModData, hs, hc, hr⟩

end Linked

/-! ### §F. The β-clauses on G7's own `β`, and the restated `GluePieces2` field -/

section Restated

variable (p : ℕ) [Fact p.Prime]

/-- **Glue on G7Data's cochain `β : G_ℚ → ℂ^×` (D3 + T16; N5 L832-844).** `β` is trivial on
`G_{ℚ_p}^t ∩ G_F` for `t > U` (through `decomp`). A Prop on `G7Data`'s `β` and the local field
`F` only. -/
def BetaUpperC (βC : GQ → ℂˣ) (F : Fld p) (U : ℝ) : Prop :=
  ∀ t : ℝ, U < t → ∀ σ ∈ upperAbs p t ∩ fixSet F, βC (decomp p σ) = 1

/-- **Glue on G7Data's `β` at tame primes (N5 L848-851).** `β` is trivial on `G_F ∩ P_p`. -/
def BetaTameC (βC : GQ → ℂˣ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, βC (decomp p σ) = 1

/-- **`LocalDataG` with its `β`-clauses on G7Data's own `β`** (`ℂ^×`-valued). The `Tm`, `a` clause
(`TmWild`) is on the `ℓ`-adic data. -/
def LocalDataC {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a : GQ → PadicAlgCl ℓ) (βC : GQ → ℂˣ) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ F : Fld p, IsFinGal F ∧
      ramCard F 0 ≤ (ZInQ.heightD * ZInQ.heightG0).factorial ∧
      TmWild p Tm a F ∧ BetaUpperC p βC F G0ModNewform.U0) ∧
    ((ZInQ.heightD : ℝ) < p → ∃ F : Fld p, IsFinGal F ∧ ¬ p ∣ ramCard F 0 ∧
      TmWild p Tm a F ∧ BetaTameC p βC F)

variable {p}

theorem eq_one_of_C {ℓ : ℕ} [Fact ℓ.Prime] {βC : GQ → ℂˣ} {βQ : GQ → PkgI4.Qbar}
    {ιC : PkgI4.Qbar →ₐ[ℚ] ℂ} (hι : ∀ g, ιC (βQ g) = (βC g : ℂ))
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) {g : GQ} (h : βC g = 1) : j (βQ g) = 1 := by
  have h1 : ιC (βQ g) = ιC 1 := by rw [hι, h, Units.val_one, map_one]
  rw [ιC.toRingHom.injective h1, map_one]

/-- **`LocalDataC` gives `LocalDataG` for `j_ℓ ∘ βQ` when `ιC ∘ βQ = β` (proved).** -/
theorem localDataG_of_C {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a : GQ → PadicAlgCl ℓ}
    {βC : GQ → ℂˣ} {βQ : GQ → PkgI4.Qbar} {ιC : PkgI4.Qbar →ₐ[ℚ] ℂ}
    (hι : ∀ g, ιC (βQ g) = (βC g : ℂ)) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (h : LocalDataC p Tm a βC) : LocalDataG p Tm a (fun g => j (βQ g)) := by
  refine ⟨fun hpD => ?_, fun hpD => ?_⟩
  · obtain ⟨F, hF, he, hw, hb⟩ := h.1 hpD
    exact ⟨F, hF, he, hw, fun t ht σ hσ => eq_one_of_C hι j (hb t ht σ hσ)⟩
  · obtain ⟨F, hF, he, hw, hb⟩ := h.2 hpD
    exact ⟨F, hF, he, hw, fun σ hσ => eq_one_of_C hι j (hb σ hσ)⟩

/-- **`LocalDataG` on the data implies the wild clauses for `ρ = β⁻¹ a Tm` (proved, with
g15-ram's local-field theorems).** For `p ≤ D`, `σ ∈ G_{ℚ_p}^t` with `t > U₀` fixes `F`
(`UpperBreakFix`, from T20/T21) and is wild (`upperWild`), so `a = Tm = 1` (`TmWild`) and
`β = 1` (`BetaUpper`); for `p > D`, wild inertia fixes the tame `F` (`wildFixTame`). So
`LocalDataG` implies the `ρ`-level form (it is the logically stronger hypothesis); what it
leaves out is the ramification theory, which is proved. -/
theorem rhoRamWild_of_localDataG (p : ℕ) (hp : p.Prime) {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*}
    [AddCommGroup V] [Module (PadicAlgCl ℓ) V] {Tm : GQ → Module.End (PadicAlgCl ℓ) V}
    {a β : GQ → PadicAlgCl ℓ} (h : @LocalDataG p ⟨hp⟩ ℓ _ V _ _ Tm a β) :
    HSyn.LinkedTate.RhoRamWild p hp (GlueDescent.rho Tm a β) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hUB : G15Ram.UpperBreakFix p := G15Ram.upperBreakFix_of_hilbertSerre
    (G15Ram.hilbertSerre_of_model (G15Ram.ladicDVRModel_of_Zp G15Ram.ladicDVRModelZp))
  refine ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_⟩
  · obtain ⟨F, hF, he, hw, hup⟩ := h.1 hpD
    have ha : 1 ≤ ZInQ.heightD * ZInQ.heightG0 :=
      Nat.mul_pos GlueDescent.heightD_pos (by unfold ZInQ.heightG0; norm_num)
    have hU0 : (0 : ℝ) ≤ G0ModNewform.U0 := by unfold G0ModNewform.U0; positivity
    have hfix : σ ∈ fixSet F := hUB F hF _ ha he t (by unfold G0ModNewform.U0 at ht; exact ht) hσ
    have hwild : σ ∈ wildSet := G15Ram.upperWild t (by linarith) hσ
    obtain ⟨h1, h2⟩ := hw σ ⟨hfix, hwild⟩
    have h3 := hup t ht σ ⟨hσ, hfix⟩
    simp [GlueDescent.rho, h1, h2, h3]
  · obtain ⟨F, hF, he, hw, htame⟩ := h.2 hpD
    have hfix := G15Ram.wildFixTame F hF he hσ
    obtain ⟨h1, h2⟩ := hw σ ⟨hfix, hσ⟩
    have h3 := htame σ ⟨hfix, hσ⟩
    simp [GlueDescent.rho, h1, h2, h3]

theorem toHom_eq_one_of_rho {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] {ρ : GQ → Module.End (PadicAlgCl ℓ) V} {r : GaloisRep ℓ 2}
    {e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines ρ r.mat e) {g : GQ} (hg : ρ g = 1) : r.toHom g = 1 :=
  toHom_eq_one_of_intertwines h hg

/-- `LocalRamWild` (g0-assemble) for every `r` intertwined with `ρ`, from `RhoRamWild` (proved). -/
theorem localRamWild_of_rhoRamWild (p : ℕ) (hp : p.Prime) {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*}
    [AddCommGroup V] [Module (PadicAlgCl ℓ) V] {ρ : GQ → Module.End (PadicAlgCl ℓ) V}
    {r : GaloisRep ℓ 2} {e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines ρ r.mat e) (hR : HSyn.LinkedTate.RhoRamWild p hp ρ) :
    @HSyn.G0AssembleMod.LocalRamWild p ⟨hp⟩ ℓ _ r := by
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨fun hp' t ht σ hσ => toHom_eq_one_of_rho h (hR.1 hp' t ht σ hσ),
    fun hp' σ hσ => toHom_eq_one_of_rho h (hR.2 hp' σ hσ)⟩

/-- `e(ℚ_p/ℚ_p) = 1` (the argument of g15-ram's `localData_trivRep`). -/
theorem ramCard_bot_zero : ramCard (⊥ : Fld p) 0 = 1 := by
  have hF : IsFinGal (⊥ : Fld p) := ⟨inferInstance, inferInstance⟩
  have h1 := G15Ram.one_le_ramCard hF 0
  have h2 : ramCard (⊥ : Fld p) 0 ≤ 1 := by
    unfold ramCard
    have hfin := (finite_restr hF (ramSet (⊥ : Fld p) 0)).to_subtype
    refine Finite.card_le_one_iff_subsingleton.mpr ⟨fun a b => ?_⟩
    apply Subtype.ext
    obtain ⟨σ, -, hσ⟩ := a.2
    obtain ⟨τ, -, hτ⟩ := b.2
    rw [← hσ, ← hτ]
    funext x
    obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp x.2
    simp only [restr, ← hq, AlgEquiv.commutes]
  omega

/-- **Non-vacuity (proved).** `LocalDataG` holds for the trivial data `Tm = 1`, `a = β = 1` (with
`F = ℚ_p`), so the restated hypotheses are consistent. -/
theorem localDataG_triv {ℓ : ℕ} [Fact ℓ.Prime] (V : Type*) [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] :
    LocalDataG p (fun _ => (1 : Module.End (PadicAlgCl ℓ) V)) (fun _ => 1) (fun _ => 1) := by
  have hF : IsFinGal (⊥ : Fld p) := ⟨inferInstance, inferInstance⟩
  refine ⟨fun _ => ⟨⊥, hF, ?_, fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => rfl⟩,
    fun _ => ⟨⊥, hF, ?_, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩⟩
  · rw [ramCard_bot_zero]; exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  · rw [ramCard_bot_zero]; exact (Nat.Prime.one_lt Fact.out).ne' ∘ Nat.dvd_one.mp

end Restated

section Field

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent.B2 G0ModField

/-- **The restated `GluePieces2` field (replaces g0-assemble's `LinkedTateData`; GLUE).** For every
fibre context and G7 data: g14-trace's `TateBridge35` conclusion (one pair `aQ, βQ : G_ℚ → ℚ̄`,
embeddings `j₅`, `j₃`, `G7Out` at `ℓ = 5, 3` for the scalars `j_ℓ ∘ aQ`, `j_ℓ ∘ βQ`,
`FrobTraceLink` for `Tm₅`, `Tm₃`, and `ιC ∘ βQ = G7Data's β`), together with the local data of
G15 on these data (`LocalDataC`: `TmWild` on `(Tm_ℓ, j_ℓ ∘ aQ)` and the `β`-clauses on
`G7Data`'s `β`) for `ℓ = 5` at every `p ≠ 5` and for `ℓ = 3` at `p = 5`. Unlike `LinkedTateData`,
it does not mention `r₅`, `r₃`, `G14TraceCompat` or `G15RamG`: those are proved from it
(`linkedTateData_of_obj`). -/
def LinkedTateObj : Prop :=
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
      (∃ ιC : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = (β g : ℂ)) ∧
      (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 →
        @LocalDataC p ⟨hp⟩ 5 _ _ _ _ Tm₅ (fun g => j5 (aQ g)) β) ∧
      LocalDataC 5 Tm₃ (fun g => j3 (aQ g)) β

/-- **g0-assemble's `LinkedTateData`, proved from the restated field (GLUE, proved).** Inputs: the
leaf T7 (`PkgI3.CharPolyIndepOfEll`, Mumford §19 Thm 4) and `LinkedTateObj`. For any `r₅`, `r₃`
with G8's output on the linked data and any `ι₅ = j₅ ∘ γ` (`exists_comp_eq`), `ι₃ := j₃ ∘ γ`
gives `G14TraceCompat` (g14-trace's `g14TraceCompat_of_link`), and `G15RamWild` holds by
`rhoRamWild_of_localDataG` (g15-ram's local-field theorems) carried to `r_ℓ` by G8's
intertwiner. -/
theorem linkedTateData_of_obj (hM : PkgI3.CharPolyIndepOfEll) (hO : LinkedTateObj) :
    HSyn.G0AssembleMod.LinkedTateData := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨aQ, βQ, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, h75, h73, hF, ⟨ιC0, hι⟩, hl5, hl3⟩ :=
    hO Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  refine ⟨Tm₅, c₅, ε₅, fun g => j5 (aQ g), fun g => j5 (βQ g), u₅,
    Tm₃, c₃, ε₃, fun g => j3 (aQ g), fun g => j3 (βQ g), u₃, h75, h73, ?_⟩
  intro r₅ r₃ h8₅ h8₃ i ιC ι5
  obtain ⟨γ, hγ⟩ := G14Trace.exists_comp_eq ι5 j5
  refine ⟨j3.comp γ, ?_, ?_⟩
  · exact G14Trace.g14TraceCompat_of_link hM ⟨i, ιC, ι5, j3.comp γ, r₅, r₃⟩ j5 j3 γ hγ rfl aQ βQ
      Tm₅ Tm₃ h8₅ h8₃ hF
  · obtain ⟨-, e5, he5, -⟩ := h8₅
    obtain ⟨-, e3, he3, -⟩ := h8₃
    intro p hp
    refine ⟨fun hp5 => ?_, fun hp5 => ?_⟩
    · exact localRamWild_of_rhoRamWild p hp he5
        (rhoRamWild_of_localDataG p hp (@localDataG_of_C p ⟨hp⟩ 5 _ _ _ _ _ _ _ _ _ hι j5
          (hl5 p hp hp5)))
    · subst hp5
      exact localRamWild_of_rhoRamWild 5 hp he3
        (rhoRamWild_of_localDataG 5 hp (localDataG_of_C hι j3 hl3))

/-- **linked-tate's `LinkedTateCore` from the restated field (GLUE, proved).** The existential data
are the same; `RhoRamWild` (linked-tate's wild clauses on `ρ_ℓ`, the conclusion form) follows from
`LocalDataC` by `rhoRamWild_of_localDataG`. As a hypothesis `LinkedTateObj` is logically stronger (it implies `LinkedTateCore`), but its
local content is more primitive: g15-ram's local-field theorems (T20, T21, `upperWild`,
`wildFixTame`) are proved, and what remains is `TmWild` on G7's operators and the `β`-clauses on
G7Data's own `β`. -/
theorem linkedTateCore_of_obj (hO : LinkedTateObj) : HSyn.LinkedTate.LinkedTateCore := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨aQ, βQ, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, h75, h73, hF, ⟨ιC0, hι⟩, hl5, hl3⟩ :=
    hO Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  refine ⟨aQ, βQ, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, h75, h73, hF, fun p hp => ⟨fun hp5 => ?_,
    fun hp5 => ?_⟩⟩
  · exact rhoRamWild_of_localDataG p hp
      (@localDataG_of_C p ⟨hp⟩ 5 _ _ _ _ _ _ _ _ _ hι j5 (hl5 p hp hp5))
  · subst hp5
    exact rhoRamWild_of_localDataG 5 hp (localDataG_of_C hι j3 hl3)

/-- **The restated field under `dim A_{L'} = 2` and `rank End(A_{L'}) = 4`** (the form matching
linked-tate's `LinkedTateCoreDR` and g14-trace's `TateBridge35`, which take these two hypotheses;
linked-tate proves `LinkedTateCore` from the `DR` form, `FibreSimple` and `QMEndRank`). GLUE. -/
def LinkedTateObjDR : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
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
      (∃ ιC : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = (β g : ℂ)) ∧
      (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 →
        @LocalDataC p ⟨hp⟩ 5 _ _ _ _ Tm₅ (fun g => j5 (aQ g)) β) ∧
      LocalDataC 5 Tm₃ (fun g => j3 (aQ g)) β

/-- **linked-tate's `LinkedTateCoreDR` from `LinkedTateObjDR` (GLUE, proved).** -/
theorem linkedTateCoreDR_of_objDR (hO : LinkedTateObjDR) : HSyn.LinkedTate.LinkedTateCoreDR := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata hdim hrk
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨aQ, βQ, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, h75, h73, hF, ⟨ιC0, hι⟩, hl5, hl3⟩ :=
    hO Y Φ π u P hctx L A ε N χ β L' hLL' hdata hdim hrk
  refine ⟨aQ, βQ, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, h75, h73, hF, fun p hp => ⟨fun hp5 => ?_,
    fun hp5 => ?_⟩⟩
  · exact rhoRamWild_of_localDataG p hp
      (@localDataG_of_C p ⟨hp⟩ 5 _ _ _ _ _ _ _ _ _ hι j5 (hl5 p hp hp5))
  · subst hp5
    exact rhoRamWild_of_localDataG 5 hp (localDataG_of_C hι j3 hl3)

/-- **`LinkedTateObjDR` contains g14-trace's `TateBridge35` conclusion (proved).** On a fibre
context, the existential data of `LinkedTateObjDR` (dropping the two `LocalDataC` clauses) are a
witness for `TateBridge35`'s conclusion, stated over g0-mod-field's copies `GaloisCopy.G7Out` and
`G14Bridge.FrobTraceLink` (accepted by definitional unfolding of the verbatim copies). So
`LinkedTateObjDR` = `TateBridge35` (on fibre contexts) + G15's local data. -/
theorem tateBridge35_of_objDR (hO : LinkedTateObjDR)
    (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar) (hctx : FibreCtx Y Φ π u P)
    (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4) :
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
      ∃ ιC : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = (β g : ℂ) := by
  obtain ⟨aQ, βQ, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, h75, h73, hF, hι, -, -⟩ :=
    hO Y Φ π u P hctx L A ε N χ β L' hLL' hD hdim hrk
  exact ⟨aQ, βQ, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, h75, h73, hF, hι⟩


end Field

end G8Object

end

#print axioms G8Object.LinkedObj.galG8Out5
#print axioms G8Object.interface_obj
#print axioms G8Object.modularConstituent_tail_obj
#print axioms G8Object.localDataG_of_C
#print axioms G8Object.rhoRamWild_of_localDataG
#print axioms G8Object.localRamWild_of_rhoRamWild
#print axioms G8Object.linkedTateData_of_obj
#print axioms G8Object.linkedTateCore_of_obj
#print axioms G8Object.linkedTateCoreDR_of_objDR
#print axioms G8Object.tateBridge35_of_objDR
#print axioms G8Object.localDataG_triv

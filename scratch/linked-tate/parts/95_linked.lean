/-! ## linked-tate: g0-assemble's joint glue Props `ModelG3G6` and `LinkedTateData`, reduced

Task linked-tate (2026-11-13). Both Props are g0-assemble's (`scratch/g0-assemble/parts/87_afterg7.lean`,
copied verbatim above with `LocalRamWild`, `G15RamWild`, `g15RamG_of_wild`, `afterG7_of`). Nothing
in them is changed. Over the pin-applied `Leaves.lean` (`R1fpProps` with `R1famProps`,
`R1univProps`).

* `ModelG3G6` is proved (`modelG3G6_of`) from
  - `HSyn.G0Split.FibreSimple` (an existing `GluePieces` field, G5-G6 on any number-field model of
    the fibre; g0-fibresimple reduced it to leaves, FS1b and FS5), for the `EndDivision` half of
    `G6Out`;
  - the new named glue Prop `QMModelG3` (G3: inertia at `p ∉ {3, ℓ}` acts trivially on
    `ℚ̄_ℓ ⊗ V_ℓ` of a base change of a `QML3` object), for the two `G3Out`;
  - and a proof (no input) of the noncommutativity half of `G6Out`: the QM structure `ι` of the
    `QML3` object and base change on endomorphisms are injective ring maps, and `𝒪` is not
    commutative (`oI_oH_ne`).
* `LinkedTateData` is proved (`linkedTateData_of`) from the leaf T7 (`PkgI3.CharPolyIndepOfEll`,
  Mumford §19 Thm 4; `TextbookLeaves.t7`) and the new named glue Prop `LinkedTateCore`:
  `G7Out` data at `ℓ = 5` and `ℓ = 3` whose scalars are the images `j_ℓ ∘ a`, `j_ℓ ∘ β` of one pair
  `a, β : G_ℚ → ℚ̄` (the scalar link), with g14-trace's `FrobTraceLink` for the two operator
  families and the wild-ramification clauses for the descended operators `ρ_ℓ` themselves
  (`RhoRamWild`). `G14TraceCompat` is then g14-trace's `g14TraceCompat_of_link` (T7), and
  `G15RamWild` for every `r_ℓ` with G8's output is transported from `ρ_ℓ` through G8's
  intertwiner (`localRamWild_of_rho`).
-/

section LinkedTateSec

noncomputable section

namespace HSyn.LinkedTate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-! ### §1 Base change on endomorphisms (copied from `scratch/bp-qmmoduli/QMAbVar.lean` L533-575:
`endBC` as unram-tate copied it, `specMap_flat`, `specMap_surjective`, `endBC_injective`) -/

section BaseChangeEnd

variable {K : Type} [Field K]

open scoped CategoryTheory.Obj in
/-- **Base change on endomorphisms** (copied verbatim from bp-qmmoduli's `endBC`):
`End_K(A) → End_L(A_L)`, `f ↦ (Over.pullback (Spec L → Spec K)).map f`, a ring homomorphism
(functoriality, and `Functor.map_mul` for the monoidal functor `Over.pullback`). -/
noncomputable def endBC (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
    PkgI3.AbVar.End A →+* PkgI3.AbVar.End (A.baseChange L) where
  toFun f := @PkgI3.AbVar.Hom.mk' L _ (A.baseChange L) (A.baseChange L)
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map f.hom)
    (Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      (f := f.hom))
  map_one' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (𝟙 A.X) = 𝟙 _
    exact (Over.pullback _).map_id _
  map_mul' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (g.hom ≫ f.hom) = _
    rw [Functor.map_comp]; rfl
  map_zero' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (1 : A.X ⟶ A.X) = 1
    exact Functor.map_one _
  map_add' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (f.hom * g.hom) = _
    rw [Functor.map_mul]; rfl

/-- `Spec L → Spec K` is flat, surjective and quasi-compact, so `Over.pullback` along it is
faithful (Mathlib, `Morphisms/FlatDescent.lean`). -/
instance specMap_flat (L : Type) [Field L] [Algebra K L] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

instance specMap_surjective (L : Type) [Field L] [Algebra K L] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  ⟨fun _ => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩

/-- Base change on endomorphisms is injective. -/
theorem endBC_injective (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
    Function.Injective (endBC A L) := by
  intro f g h
  apply PkgI3.AbVar.Hom.ext'
  exact (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map_injective
    (congrArg PkgI3.AbVar.Hom.hom h)

end BaseChangeEnd

/-! ### §2 The noncommutativity half of `G6Out` (proved) -/

/-- `i = ofInt ![0,1,0,0] ∈ 𝒪`. -/
def oI : LeafQM.O := ⟨LeafQM.ofInt ![0, 1, 0, 0], ⟨_, rfl⟩⟩

/-- `(1 + j)/2 = ofInt ![0,0,1,0] ∈ 𝒪`. -/
def oH : LeafQM.O := ⟨LeafQM.ofInt ![0, 0, 1, 0], ⟨_, rfl⟩⟩

/-- `𝒪` is not commutative: `i · (1+j)/2 = (i+k)/2 ≠ (i−k)/2 = (1+j)/2 · i`. -/
theorem oI_oH_ne : oI * oH ≠ oH * oI := by
  intro h
  have h1 : ((oI * oH : LeafQM.O) : LeafQM.B) =
      LeafQM.ofInt (LeafQM.mulCoord ![0, 1, 0, 0] ![0, 0, 1, 0]) := LeafQM.ofInt_mul _ _
  have h2 : ((oH * oI : LeafQM.O) : LeafQM.B) =
      LeafQM.ofInt (LeafQM.mulCoord ![0, 0, 1, 0] ![0, 1, 0, 0]) := LeafQM.ofInt_mul _ _
  have h0 : ((oI * oH : LeafQM.O) : LeafQM.B) = ((oH * oI : LeafQM.O) : LeafQM.B) :=
    congrArg Subtype.val h
  rw [h1, h2] at h0
  have h3 := congrArg QuaternionAlgebra.imK h0
  have e1 : LeafQM.mulCoord ![0, 1, 0, 0] ![0, 0, 1, 0] 3 = 1 := by decide
  have e2 : LeafQM.mulCoord ![0, 0, 1, 0] ![0, 1, 0, 0] 3 = -1 := by decide
  have h4 : ((LeafQM.mulCoord ![0, 1, 0, 0] ![0, 0, 1, 0] 3 : ℤ) : ℚ) / 2 =
      ((LeafQM.mulCoord ![0, 0, 1, 0] ![0, 1, 0, 0] 3 : ℤ) : ℚ) / 2 := h3
  rw [e1, e2] at h4
  norm_num at h4

/-- **`End` of a twice base-changed `QML3` surface is not commutative** (proved): the images of
`i` and `(1+j)/2` under `endBC ∘ endBC ∘ ι` do not commute (both base changes and `ι` are
injective ring maps). -/
theorem noncomm_baseChange2 {K : Type} [Field K] (PK : LeafQM.AV.QML3 K) (L : Type) [Field L] [Algebra K L]
    (L' : Type) [Field L'] [Algebra L L'] :
    ∃ x y : PkgI3.AbVar.End ((PK.A.baseChange L).baseChange L'), x * y ≠ y * x := by
  let f := (endBC (PK.A.baseChange L) L').comp ((endBC PK.A L).comp PK.q.iota)
  have hf : Function.Injective f :=
    (endBC_injective _ L').comp ((endBC_injective _ L).comp PK.q.injective)
  refine ⟨f oI, f oH, fun h => oI_oH_ne (hf ?_)⟩
  rw [map_mul, map_mul]
  exact h

/-! ### §3 The `EndDivision` half of `G6Out`, from `FibreSimple` (proved) -/

/-- **`EndDivision` for every number-field model of the fibre, from the glue piece
`FibreSimple`** (proved): a model `A'/L'` of `P`'s surface (`IsModelOver`) at a fibre context
gives `FibreOver` for `(abVarEquiv L').symm A'` with the inclusion `L' ⊆ ℚ̄`. -/
theorem endDivision_of_fibreSimple (hFS : HSyn.G0Split.FibreSimple)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : LeafQM.AV.PtEquiv Y} {π : LeafQM.AV.ToP1 Y.left} {u : ℚ}
    {P : LeafQM.AV.QML3 Qbar} (hctx : FibreCtx Y Φ π u P) (L' : IF) [FiniteDimensional ℚ L']
    (A' : PkgI3.AbVar L') (hA' : IsModelOver L' A' P) : PkgI3.EndDivision A' := by
  obtain ⟨h1, h2, hu, y, hy, hπ⟩ := hctx
  haveI : NumberField L' := numberField_of_fd L'
  exact hFS Y Φ π h1 h2 u hu ⟨L'⟩ ((LeafAdopt.abVarEquiv L').symm A')
    ⟨algebraMap L' Qbar, y, P, hy, hπ, hA'⟩

/-! ### §4 G3 on the model: the named glue Prop `QMModelG3` -/

/-- **Glue G3 on base changes of `QML3` objects** (linked-tate; G3 = Lemma PR(ii), h-decomposition
§3 G3, with R7a; N5 L524-529 and h-trust A6, C6). For a `QML3` object `PK` over `K ⊆ ℚ̄` and a
tower `K ≤ L ≤ L'` with `L'/ℚ` finite, every inertia element of `G_{L'}` at a place above a prime
`p ∉ {3, ℓ}` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ((PK.A)_{L,L'})` (`G0Galois.G3Out … ℓ {3}`). Route
(STANDARD; the Lean parts SPECULATIVE): `PK.A` has good reduction at every DVR with `3` a unit
(`LeafQM.AV.QML3.goodReduction`, proved in `Leaves.lean` from NOS, Raynaud and
`TorsionStructure`), good reduction is preserved by base change, and Néron–Ogg–Shafarevich
(R7a, (a) ⇒ (b), `PkgI2.inertiaTrivial_of_goodReduction`) makes inertia trivial on `A[ℓⁿ]`; the
open part is the transport from PkgI2's points and valuation rings of `\bar{L'}` to `ℚ̄_ℓ ⊗ V_ℓ`
and to places of `ℚ̄` (`resQ`). GLUE. -/
def QMModelG3 : Prop :=
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L') (PK : LeafQM.AV.QML3 K)
    (ℓ : ℕ) [Fact ℓ.Prime],
    letI : NumberField L' := numberField_of_fd L'
    G0Galois.G3Out (@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) ℓ {3}

/-- **Glue: good reduction away from `3` gives `G3Out` on base changes** (linked-tate; the
transport half of G3/G11, given the leaf R7a = Néron–Ogg–Shafarevich, Serre–Tate 1968 Thm 1,
`PkgI2.NeronOggShafarevich`). If `A/K` (`K ⊆ ℚ̄`) has good reduction (PkgI2's
`HasGoodReduction`, an abelian scheme over the DVR) at every discrete valuation ring of `K` in
which `3` is a unit, then for every tower `K ≤ L ≤ L'` with `L'/ℚ` finite and every prime `ℓ`,
inertia of `G_{L'}` at places above `p ∉ {3, ℓ}` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A_{L,L'})`.
Proof route (STANDARD): `v ∩ K` is such a DVR; NOS (a) ⇒ (b) over `K` makes inertia at `v`
trivial on every `A[ℓⁿ](K̄)`; inertia of `G_{L'}` restricts into it; triviality on all `A[ℓⁿ]`
is triviality on `T_ℓ`, hence on `ℚ̄_ℓ ⊗ V_ℓ`; base change does not change the points over
`\bar K = \bar{L'}` (`bcPt`, unram-tate). Only definitions are transported; no new literature
input. GLUE. -/
def GoodRedG3Bridge : Prop :=
  PkgI2.NeronOggShafarevich.{0} →
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L') (A : PkgI3.AbVar K),
    (∀ (Ov : ValuationSubring K) [IsDiscreteValuationRing Ov], IsUnit (3 : Ov) →
      PkgI2.HasGoodReduction (ObjBridge.toGrp A) Ov) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      letI : NumberField L' := numberField_of_fd L'
      G0Galois.G3Out (@PkgI3.AbVar.baseChange L _
        (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')) ℓ {3}

/-- **`QMModelG3`, proved** from the leaves R6 (Raynaud), R7a (NOS), T5 (`TorsionStructure`)
through `LeafQM.AV.QML3.goodReduction` (proved in `Leaves.lean`: a `QML3` object has good
reduction at every DVR with `3` a unit) and the glue `GoodRedG3Bridge`. -/
theorem qmModelG3_of (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (hB : GoodRedG3Bridge) : QMModelG3 :=
  fun K L L' _ hKL hLL' PK ℓ _ => hB hNOS K L L' hKL hLL' PK.A
    (fun Ov _ h3 => LeafQM.AV.QML3.goodReduction (P := PK) hNOS hRay hTors Ov h3) ℓ

/-- `3 ∈ T(u)` (`3 ∈ S_mul`). -/
theorem three_mem_T (u : ℚ) : 3 ∈ T u :=
  Finset.mem_union_left _ (ZInQ.Mult.mem_S_mul_of_le Nat.prime_three (by norm_num))

/-- `G3Out` is monotone in `T`. -/
theorem g3Out_mono {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K} {ℓ : ℕ}
    [Fact ℓ.Prime] {T₁ T₂ : Finset ℕ} (hT : T₁ ⊆ T₂) (h : G0Galois.G3Out A ℓ T₁) :
    G0Galois.G3Out A ℓ T₂ :=
  fun p hp hpT hpl v hv σ' hσ => h p hp (fun h' => hpT (hT h')) hpl v hv σ' hσ

/-- **`ModelG3G6`, proved** from the glue pieces `FibreSimple` (EndDivision) and `QMModelG3`
(G3); the noncommutativity of `End(A_{L'})` is proved (`noncomm_baseChange2`). -/
theorem modelG3G6_of (hFS : HSyn.G0Split.FibreSimple) (hG3 : QMModelG3) :
    HSyn.G0AssembleMod.ModelG3G6 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  have hmod := hdata.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨K, hKL, PK, -, rfl⟩ := hdata.1
  have hT : ({3} : Finset ℕ) ⊆ T u := Finset.singleton_subset_iff.mpr (three_mem_T u)
  refine ⟨⟨endDivision_of_fibreSimple hFS hctx L' _ hmod, ?_⟩, ?_, ?_⟩
  · exact @noncomm_baseChange2 K _ PK L _ (incAlg hKL) L' _ (incAlg hLL')
  · exact g3Out_mono hT (hG3 K L L' hKL hLL' PK 5)
  · exact g3Out_mono hT (hG3 K L L' hKL hLL' PK 3)

/-! ### §5 `G15RamWild` from the descended operators (proved) -/

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

/-- If `e` intertwines `ρ` with `r ⊕ r` and `ρ(g) = 1`, then `r(g) = 1` (proved). -/
theorem toHom_eq_one_of_intertwines {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) V)
    (r : PkgI4.GaloisRep ℓ 2)
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (h : G0Galois.Intertwines ρ r.mat e) (g : PkgI4.GQ) (hg : ρ g = 1) : r.toHom g = 1 := by
  have hmv : ∀ x : Fin 2 → PadicAlgCl ℓ, (r.mat g).mulVec x = x := by
    intro x
    have hx := h g (e.symm (x, 0))
    rw [hg] at hx
    change e (e.symm (x, 0)) = _ at hx
    rw [LinearEquiv.apply_symm_apply] at hx
    exact (congrArg Prod.fst hx).symm
  apply Units.ext
  rw [Units.val_one]
  change r.mat g = 1
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, hmv x, Matrix.toLin'_one, LinearMap.id_apply]

/-- **`LocalRamWild` for `r` from `RhoRamWild` for `ρ`** (proved), when G8's `e` intertwines `ρ`
with `r ⊕ r`. -/
theorem localRamWild_of_rho (p : ℕ) (hp : p.Prime) {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*}
    [AddCommGroup V] [Module (PadicAlgCl ℓ) V] (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) V)
    (r : PkgI4.GaloisRep ℓ 2)
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (h : G0Galois.Intertwines ρ r.mat e) (hR : RhoRamWild p hp ρ) :
    @HSyn.G0AssembleMod.LocalRamWild p ⟨hp⟩ ℓ _ r := by
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨fun hp' t ht σ hσ => ?_, fun hp' σ hσ => ?_⟩
  · exact toHom_eq_one_of_intertwines ρ r e h _ (hR.1 hp' t ht σ hσ)
  · exact toHom_eq_one_of_intertwines ρ r e h _ (hR.2 hp' σ hσ)

/-! ### §6 `LinkedTateData` from T7 and the named glue Prop `LinkedTateCore` -/

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

/-- **`LinkedTateCore`, proved** from `FibreSimple` (EndDivision of the model), `QMEndRank` and
`LinkedTateCoreDR`; `dim A_{L'} = 2` is proved (`QML3.surface` and g0-dim's
`pkgI3_dim_baseChange`, twice). -/
theorem linkedTateCore_of (hFS : HSyn.G0Split.FibreSimple) (hR : QMEndRank)
    (hDR : LinkedTateCoreDR) : LinkedTateCore := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  have hmod := hdata.2.2.2.2.2.2.2.2.2.2.2
  have hdata' := hdata
  obtain ⟨K, hKL, PK, -, rfl⟩ := hdata.1
  have hdim : (@PkgI3.AbVar.baseChange L _ (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))
      L' _ (incAlg hLL')).dim = 2 := by
    rw [@G0Dim.pkgI3_dim_baseChange L _ L' _ (incAlg hLL'),
      @G0Dim.pkgI3_dim_baseChange K _ L _ (incAlg hKL)]
    exact PK.surface
  exact hDR Y Φ π u P hctx L _ ε N χ β L' hLL' hdata' hdim
    (hR K L L' hKL hLL' PK (endDivision_of_fibreSimple hFS hctx L' _ hmod))

/-- **`LinkedTateData`, proved** from the leaf T7 (`PkgI3.CharPolyIndepOfEll`) and the glue Prop
`LinkedTateCore`: for G8's `r₅`, `r₃` on the linked data and any `ι₅ = j₅ ∘ γ` (`exists_comp_eq`),
`ι₃ := j₃ ∘ γ` makes the traces compatible (g14-trace's `g14TraceCompat_of_link`), and
`G15RamWild` holds because G8's intertwiner carries `RhoRamWild` from `ρ_ℓ` to `r_ℓ`. -/
theorem linkedTateData_of (hM : PkgI3.CharPolyIndepOfEll) (hC : LinkedTateCore) :
    HSyn.G0AssembleMod.LinkedTateData := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨a, b, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, h5, h3, hF, hR⟩ :=
    hC Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  refine ⟨Tm₅, c₅, ε₅, fun g => j5 (a g), fun g => j5 (b g), u₅,
    Tm₃, c₃, ε₃, fun g => j3 (a g), fun g => j3 (b g), u₃, h5, h3, ?_⟩
  intro r₅ r₃ h8₅ h8₃ i ιC ι5
  obtain ⟨gm, hgm⟩ := G14Trace.exists_comp_eq ι5 j5
  refine ⟨j3.comp gm, ?_, ?_⟩
  · exact G14Trace.g14TraceCompat_of_link hM ⟨i, ιC, ι5, j3.comp gm, r₅, r₃⟩ j5 j3 gm hgm rfl a b
      Tm₅ Tm₃ h8₅ h8₃ hF
  · obtain ⟨-, e5, he5, -⟩ := h8₅
    obtain ⟨-, e3, he3, -⟩ := h8₃
    intro p hp
    exact ⟨fun h => localRamWild_of_rho p hp _ r₅ e5 he5 ((hR p hp).1 h),
      fun h => localRamWild_of_rho p hp _ r₃ e3 he3 ((hR p hp).2 h)⟩

/-! ### §7 `AfterG7` with the two joint Props replaced (proved) -/

/-- **`AfterG7` (G8-G16)** from g0-assemble's inputs of `afterG7_of` with `ModelG3G6` replaced by
`FibreSimple` and `QMModelG3`, and `LinkedTateData` by `LinkedTateCore` (T7 is `t.t7`). -/
theorem afterG7_of_linked (r : HSyn.ResearchLeaves) (t : HSyn.TextbookLeaves)
    (m : G0Galois.GaloisPieces) (hDF : G0ModNewform.DirichletOfFinite)
    (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hFS : HSyn.G0Split.FibreSimple) (hG3 : QMModelG3) (hC : LinkedTateCore) : AfterG7 :=
  HSyn.G0AssembleMod.afterG7_of r t m hDF hCar hSw hL8 hAd (modelG3G6_of hFS hG3)
    (linkedTateData_of t.t7 hC)

/-- **`AfterG7` with G3 reduced to the bundle's R6, R7a, T5 and `GoodRedG3Bridge`, and
`LinkedTateCore` to `QMEndRank` and `LinkedTateCoreDR`.** -/
theorem afterG7_of_linked' (r : HSyn.ResearchLeaves) (t : HSyn.TextbookLeaves)
    (m : G0Galois.GaloisPieces) (hDF : G0ModNewform.DirichletOfFinite)
    (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hFS : HSyn.G0Split.FibreSimple) (hB : GoodRedG3Bridge) (hR : QMEndRank)
    (hDR : LinkedTateCoreDR) : AfterG7 :=
  afterG7_of_linked r t m hDF hCar hSw hL8 hAd hFS (qmModelG3_of r.r7a r.r6 t.t5 hB)
    (linkedTateCore_of hFS hR hDR)

end HSyn.LinkedTate

end

end LinkedTateSec

#print axioms HSyn.LinkedTate.oI_oH_ne
#print axioms HSyn.LinkedTate.noncomm_baseChange2
#print axioms HSyn.LinkedTate.endDivision_of_fibreSimple
#print axioms HSyn.LinkedTate.qmModelG3_of
#print axioms HSyn.LinkedTate.modelG3G6_of
#print axioms HSyn.LinkedTate.toHom_eq_one_of_intertwines
#print axioms HSyn.LinkedTate.localRamWild_of_rho
#print axioms HSyn.LinkedTate.linkedTateCore_of
#print axioms HSyn.LinkedTate.linkedTateData_of
#print axioms HSyn.LinkedTate.afterG7_of_linked
#print axioms HSyn.LinkedTate.afterG7_of_linked'

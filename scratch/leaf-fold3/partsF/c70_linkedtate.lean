-- (leaf-fold3) scratch/g0-assemble3/parts/c10-c15 verbatim (linked-tate parts 95, 97, 98b, 98c, 98d, 98)
-- (g0-assemble3: scratch/linked-tate/parts/95_linked.lean, verbatim except `hdata.2.….2` (11×) → `….2.1` twice, for G7Data's added last clause)
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
  have hmod := hdata.2.2.2.2.2.2.2.2.2.2.2.1
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
  have hmod := hdata.2.2.2.2.2.2.2.2.2.2.2.1
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



-- (g0-assemble3: scratch/linked-tate/parts/97_linkeddata.lean, verbatim)
/-! ## linked-tate: the linked Tate data are constructed; `LinkedTateCoreDR` reduced to `LinkedFrobRam`

unram-tate proved g0-mod-field's `TateBridge` (copied above, `UnramTate.tateBridge_of_tateModuleFree`)
by applying the Tate functor `opV` to the points-level descent datum `m_σ = μ_σ ∘ σ`:
`Tm g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)`, `a = 1`, `β' g = γ(hgh⁻¹)`, separately for each `ℓ`.
Here the same construction is run once for `ℓ = 5` and `ℓ = 3` with **one** scalar function
`γ₀ : G_ℚ → ℚ̄` (`scalarTransferQ`, unram-tate's `scalarTransfer` with target `ℚ̄`), mapped to
`ℚ̄_ℓ` by embeddings `j_ℓ : ℚ̄ → ℚ̄_ℓ`. So the scalar link of g14-trace (finding F1) holds by
construction, and the existence half of `LinkedTateCoreDR` is proved (from the leaf I3.M0
through `TateCont`). What is left is the named glue Prop `LinkedFrobRam`: `FrobTraceLink` and
`RhoRamWild` for these canonical operators (`tmOf`), for every choice of the data that the
construction uses.
-/

section LinkedDataSec

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace UnramTate

open G0ModField

/-- **`ScalarTransfer` with target `ℚ̄`, tied to `β/a`** (proved; unram-tate's `scalarTransfer`
with `PadicAlgCl ℓ` replaced by `ℚ̄`): `γ_ℂ = β/a` takes algebraic values (unram-tate's argument),
so for an embedding `κ : ℚ̄ → ℂ` every value has a preimage `γ₀(σ)`; injectivity of `κ` transfers
`∂γ_ℂ = n/d` to `γ₀`. -/
theorem scalarTransferQ (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (a : GQ → ℝ)
    (β : GQ → ℂˣ) (ε : GQ → GQ → ℂˣ) (n d : GQ → GQ → ℤ)
    (hd : ∀ σ τ, d σ τ ≠ 0)
    (hna : ∀ σ τ, (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) =
      (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ))
    (hβe : ∀ σ τ, β σ * β τ = ε σ τ * β (σ * τ))
    (ha0 : ∀ σ, 0 < a σ)
    (hcos : ∀ σ, ∀ k ∈ GQL L', a (σ * k) = a σ ∧ β (σ * k) = β σ)
    (hone : ∀ k ∈ GQL L', a k = 1 ∧ β k = 1) :
    ∃ (gam : GQ → PkgI4.Qbar) (κ : PkgI4.Qbar →ₐ[ℚ] ℂ),
      (∀ σ, κ (gam σ) = (β σ : ℂ) / ((a σ : ℝ) : ℂ)) ∧ (∀ σ, gam σ ≠ 0) ∧
      (∀ σ τ, gam σ * gam τ = ((n σ τ : PkgI4.Qbar) / (d σ τ : PkgI4.Qbar)) * gam (σ * τ)) ∧
      (∀ σ, ∀ k ∈ GQL L', gam (σ * k) = gam σ) ∧ (∀ k ∈ GQL L', gam k = 1) := by
  let gC : GQ → ℂ := fun σ => (β σ : ℂ) / ((a σ : ℝ) : ℂ)
  let q : GQ → GQ → ℚ := fun σ τ => (n σ τ : ℚ) / d σ τ
  have ha0' : ∀ σ, ((a σ : ℝ) : ℂ) ≠ 0 := fun σ => Complex.ofReal_ne_zero.mpr (ha0 σ).ne'
  have hq : ∀ σ τ, gC σ * gC τ = (q σ τ : ℂ) * gC (σ * τ) := by
    intro σ τ
    have h1 := hna σ τ
    have h2 : (β σ : ℂ) * β τ = ε σ τ * β (σ * τ) := by
      rw [← Units.val_mul, hβe σ τ, Units.val_mul]
    have hdC : (d σ τ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (hd σ τ)
    have hε : (ε σ τ : ℂ) = (((a σ * a τ * ((n σ τ : ℝ) / d σ τ)) : ℝ) : ℂ) / ((a (σ * τ) : ℝ) : ℂ) := by
      rw [h1, mul_div_cancel_right₀ _ (ha0' _)]
    have hA := ha0' σ
    have hB := ha0' τ
    have hAB := ha0' (σ * τ)
    simp only [gC, q]
    rw [div_mul_div_comm, h2, hε]
    push_cast
    field_simp
  have hgcos : ∀ σ, ∀ k ∈ GQL L', gC (σ * k) = gC σ := by
    intro σ k hk; simp only [gC]; rw [(hcos σ k hk).1, (hcos σ k hk).2]
  have hg1 : ∀ k ∈ GQL L', gC k = 1 := by
    intro k hk; simp only [gC]; rw [(hone k hk).1, (hone k hk).2]; simp
  have hg0 : ∀ σ, gC σ ≠ 0 := fun σ => div_ne_zero (Units.ne_zero _) (ha0' σ)
  have hpow : ∀ (σ : GQ) (k : ℕ), ∃ r : ℚ, gC σ ^ k = (r : ℂ) * gC (σ ^ k) := by
    intro σ k
    induction k with
    | zero => exact ⟨1, by rw [pow_zero, pow_zero, hg1 1 (one_mem _)]; simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * q (σ ^ k) σ, ?_⟩
      rw [pow_succ, hr, _root_.mul_assoc, hq, pow_succ]
      push_cast; ring
  have hfin : ∀ σ : GQ, ∃ r : ℕ, 0 < r ∧ σ ^ r ∈ GQL L' := by
    intro σ
    let σ' : Qbar ≃ₐ[ℚ] Qbar := σ
    let s := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' σ'
    have hs : IsOfFinOrder s := isOfFinOrder_of_finite s
    refine ⟨orderOf s, hs.orderOf_pos, ?_⟩
    have h1 : AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' (σ' ^ orderOf s) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    rw [mem_GQL]
    intro x hx
    exact (AlgEquiv.restrictNormal_eq_one_iff L' _).mp h1 x hx
  have halg : ∀ σ, IsIntegral ℚ (gC σ) := by
    intro σ
    obtain ⟨r, hr0, hr⟩ := hfin σ
    obtain ⟨t, ht⟩ := hpow σ r
    rw [hg1 _ hr, _root_.mul_one] at ht
    refine ⟨Polynomial.X ^ r - Polynomial.C t, Polynomial.monic_X_pow_sub_C t hr0.ne', ?_⟩
    simp [Polynomial.eval₂_sub, ht]
  let κ : PkgI4.Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hpre : ∀ σ, ∃ y : PkgI4.Qbar, κ y = gC σ := by
    intro σ
    have hint := halg σ
    set P := minpoly ℚ (gC σ) with hP
    have hP0 : P.map (algebraMap ℚ PkgI4.Qbar) ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero hint)
    have hroot : ((P.map (algebraMap ℚ PkgI4.Qbar)).map (κ : PkgI4.Qbar →+* ℂ)).IsRoot (gC σ) := by
      rw [Polynomial.map_map, κ.comp_algebraMap, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
        minpoly.aeval]
    obtain ⟨y, hy⟩ :=
      (IsAlgClosed.splits (P.map (algebraMap ℚ PkgI4.Qbar))).mem_range_of_isRoot hP0 hroot
    exact ⟨y, hy⟩
  choose gam hgam using hpre
  have hκ : Function.Injective κ := κ.toRingHom.injective
  refine ⟨gam, κ, hgam, ?_, ?_, ?_, ?_⟩
  · intro σ h0
    apply hg0 σ
    rw [← hgam, h0, map_zero]
  · intro σ τ
    apply hκ
    rw [map_mul, map_mul, hgam, hgam, map_div₀, map_intCast, map_intCast, hgam, hq]
    simp only [q]
    push_cast
    ring
  · intro σ k hk
    apply hκ
    rw [hgam, hgam, hgcos σ k hk]
  · intro k hk
    apply hκ
    rw [hgam, map_one, hg1 k hk]

/-- **The canonical operators** `Tm g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` on `ℚ̄_ℓ ⊗ V_ℓ(A_{L'})`
(unram-tate's construction, for the points-level maps `m`, the transport `Θ : A(ℚ̄) ≅ A_{L'}(\bar{L'})`
and `h ∈ G_ℚ`). -/
def tmOf {L L' : IF} (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ)
    (m : GQ → (PtQ L A →+ PtQ L A)) (ℓ : ℕ) [Fact ℓ.Prime] :
    PkgI4.GQ → Module.End (PadicAlgCl ℓ)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
  fun g => ((opVHom (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ).comp (conjE Θ))
    (m (h * g * h⁻¹))

/-- **Glue: the Frobenius trace link and Glazer's wild ramification for the canonical
operators** (linked-tate; the remaining content of `LinkedTateCoreDR`). For every fibre context
and G7 data, every transport `(Θ, h)` with unram-tate's `TatePoints` property, every
points-level descent datum `(m, a, n, d)` of `A` for `ε` (the clauses of g0-mod-field's
`DescentDatum`, with the rational discrepancy `n/d` as functions), every `γ₀ : G_ℚ → ℚ̄` with
`∂γ₀ = n/d`, constant on `G_{L'}`-cosets and `1` on `G_{L'}`, and all embeddings `j₅`, `j₃`:
* g14-trace's `FrobTraceLink` for `tmOf … 5`, `tmOf … 3` (N5 L777-786: at a Frobenius `τ` above
  `p ∉ S`, `N·Tm_ℓ(τ)` is `V_ℓ` of `N·μ̄ ∘ F` on the reduction, at `ℓ = 3` and `ℓ = 5`);
* `RhoRamWild` for `ρ₅ = (j₅∘β')⁻¹ Tm₅` at `p ≠ 5` and `ρ₃` at `p = 5` (`β' g = γ₀(hgh⁻¹)`,
  `a = 1`; N5 L819-852, D1-D4).
GLUE (AV reduction theory, Néron/Serre–Tate, and the conductor bounds of G15). -/
def LinkedFrobRam : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∀ (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ),
      (∀ (σ : Field.absoluteGaloisGroup L') (σ' : Qbar ≃ₐ[L] Qbar),
        (∀ x, σ' x = (h * (@GaloisCopy.resQ L' _ (numberField_of_fd L') σ) * h⁻¹) x) →
        ∀ x, Θ (MonoidHom.toAdditive (A.galAct σ') x) =
          MonoidHom.toAdditive ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).galAct σ)
            (Θ x)) →
    ∀ (m : GQ → (PtQ L A →+ PtQ L A)) (a : GQ → ℝ) (n d : GQ → GQ → ℤ),
      (∀ σ, 0 < a σ) →
      (∀ σ k : GQ, k ∈ GQL L → a k = 1 ∧ a (σ * k) = a σ ∧ a (k * σ) = a σ) →
      (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ')) →
      (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) →
      (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
        (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
          (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) →
      (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) →
      (∀ σ τ, n σ τ ≠ 0 ∧ d σ τ ≠ 0 ∧ d σ τ • (m σ).comp (m τ) = n σ τ • m (σ * τ) ∧
        (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) = (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) →
      (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
        ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F σ) →
    ∀ (gam : GQ → PkgI4.Qbar),
      (∃ κ : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ σ, κ (gam σ) = (β σ : ℂ) / ((a σ : ℝ) : ℂ)) →
      (∀ σ, gam σ ≠ 0) →
      (∀ σ τ, gam σ * gam τ = ((n σ τ : PkgI4.Qbar) / (d σ τ : PkgI4.Qbar)) * gam (σ * τ)) →
      (∀ σ, ∀ k ∈ GQL L', gam (σ * k) = gam σ) → (∀ k ∈ GQL L', gam k = 1) →
    ∀ (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3),
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))
        (tmOf hLL' A Θ h m 5) (tmOf hLL' A Θ h m 3) ∧
      ∀ p : ℕ, ∀ hp : p.Prime,
        (p ≠ 5 → HSyn.LinkedTate.RhoRamWild p hp
          (GlueDescent.rho (tmOf hLL' A Θ h m 5) (fun _ => j5 1)
            (fun g => j5 (gam (h * g * h⁻¹))))) ∧
        (p = 5 → HSyn.LinkedTate.RhoRamWild p hp
          (GlueDescent.rho (tmOf hLL' A Θ h m 3) (fun _ => j3 1)
            (fun g => j3 (gam (h * g * h⁻¹)))))

/-- **Glue: the Frobenius trace link for the canonical operators** (linked-tate; N5 L777-786).
For every fibre context and G7 data, every transport `(Θ, h)` with unram-tate's `TatePoints`
property and every points-level descent datum `(m, a, n, d)` of `A` for `ε` (the clauses of
g0-mod-field's `DescentDatum`, the discrepancy `n/d` as functions): g14-trace's `FrobTraceLink`
holds for `tmOf … 5` and `tmOf … 3`: outside a finite set of primes, at every arithmetic Frobenius
`τ` there are an abelian variety `Ā` over a field of characteristic `p`, `α' ∈ End(Ā)` and
`N ≠ 0` with `N·Tm_ℓ(τ)` conjugate to `V_ℓ(α')` at `ℓ = 3` and `ℓ = 5` (Glazer: `Ā` the
reduction of `A_{L'}`, `α' = N·μ̄ ∘ F`; Néron mapping property and Serre–Tate). GLUE. -/
def LinkedFrob : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∀ (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ),
      (∀ (σ : Field.absoluteGaloisGroup L') (σ' : Qbar ≃ₐ[L] Qbar),
        (∀ x, σ' x = (h * (@GaloisCopy.resQ L' _ (numberField_of_fd L') σ) * h⁻¹) x) →
        ∀ x, Θ (MonoidHom.toAdditive (A.galAct σ') x) =
          MonoidHom.toAdditive ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).galAct σ)
            (Θ x)) →
    ∀ (m : GQ → (PtQ L A →+ PtQ L A)) (a : GQ → ℝ) (n d : GQ → GQ → ℤ),
      (∀ σ, 0 < a σ) →
      (∀ σ k : GQ, k ∈ GQL L → a k = 1 ∧ a (σ * k) = a σ ∧ a (k * σ) = a σ) →
      (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ')) →
      (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) →
      (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
        (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
          (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) →
      (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) →
      (∀ σ τ, n σ τ ≠ 0 ∧ d σ τ ≠ 0 ∧ d σ τ • (m σ).comp (m τ) = n σ τ • m (σ * τ) ∧
        (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) = (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) →
      (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
        ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F σ) →
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))
        (tmOf hLL' A Θ h m 5) (tmOf hLL' A Θ h m 3)

/-- **Glue: Glazer's wild ramification for the canonical descended operators** (linked-tate;
N5 L819-852, D1-D4). Same data as `LinkedFrob`, and every `γ₀ : G_ℚ → ℚ̄` that is `β/a` under some embedding `ℚ̄ → ℂ` (the
scalars of G7, N5 L719-722), with `∂γ₀ = n/d`, constant on `G_{L'}`-cosets and `1` on `G_{L'}`, and
all embeddings `j₅`, `j₃`: `RhoRamWild` for
`ρ₅ = (j₅∘β')⁻¹ Tm₅` at `p ≠ 5` and for `ρ₃` at `p = 5` (`β' g = γ₀(hgh⁻¹)`, `a = 1`). GLUE. -/
def LinkedRam : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∀ (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ),
      (∀ (σ : Field.absoluteGaloisGroup L') (σ' : Qbar ≃ₐ[L] Qbar),
        (∀ x, σ' x = (h * (@GaloisCopy.resQ L' _ (numberField_of_fd L') σ) * h⁻¹) x) →
        ∀ x, Θ (MonoidHom.toAdditive (A.galAct σ') x) =
          MonoidHom.toAdditive ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).galAct σ)
            (Θ x)) →
    ∀ (m : GQ → (PtQ L A →+ PtQ L A)) (a : GQ → ℝ) (n d : GQ → GQ → ℤ),
      (∀ σ, 0 < a σ) →
      (∀ σ k : GQ, k ∈ GQL L → a k = 1 ∧ a (σ * k) = a σ ∧ a (k * σ) = a σ) →
      (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ')) →
      (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) →
      (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
        (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
          (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) →
      (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) →
      (∀ σ τ, n σ τ ≠ 0 ∧ d σ τ ≠ 0 ∧ d σ τ • (m σ).comp (m τ) = n σ τ • m (σ * τ) ∧
        (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) = (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) →
      (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
        ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F σ) →
    ∀ (gam : GQ → PkgI4.Qbar),
      (∃ κ : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ σ, κ (gam σ) = (β σ : ℂ) / ((a σ : ℝ) : ℂ)) →
      (∀ σ, gam σ ≠ 0) →
      (∀ σ τ, gam σ * gam τ = ((n σ τ : PkgI4.Qbar) / (d σ τ : PkgI4.Qbar)) * gam (σ * τ)) →
      (∀ σ, ∀ k ∈ GQL L', gam (σ * k) = gam σ) → (∀ k ∈ GQL L', gam k = 1) →
    ∀ (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3),
      ∀ p : ℕ, ∀ hp : p.Prime,
        (p ≠ 5 → HSyn.LinkedTate.RhoRamWild p hp
          (GlueDescent.rho (tmOf hLL' A Θ h m 5) (fun _ => j5 1)
            (fun g => j5 (gam (h * g * h⁻¹))))) ∧
        (p = 5 → HSyn.LinkedTate.RhoRamWild p hp
          (GlueDescent.rho (tmOf hLL' A Θ h m 3) (fun _ => j3 1)
            (fun g => j3 (gam (h * g * h⁻¹)))))

/-- `LinkedFrobRam` is the conjunction of `LinkedFrob` and `LinkedRam` (proved). -/
theorem linkedFrobRam_of (hF : LinkedFrob) (hR : LinkedRam) : LinkedFrobRam := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD Θ h hΘ m a n d h1 h2 h3 h4 h5 h6 h7 h8
    gam g0 g1 g2 g3 g4 j5 j3
  exact ⟨hF Y Φ π u P hctx L A ε N χ β L' hLL' hD Θ h hΘ m a n d h1 h2 h3 h4 h5 h6 h7 h8,
    hR Y Φ π u P hctx L A ε N χ β L' hLL' hD Θ h hΘ m a n d h1 h2 h3 h4 h5 h6 h7 h8 gam g0 g1 g2 g3 g4
      j5 j3⟩

set_option maxHeartbeats 1000000 in
/-- **`LinkedTateCoreDR`, proved** from the leaf I3.M0 (`PkgI3.TateModuleFree`, through
unram-tate's `tateCont_of_tateModuleFree`) and the glue `LinkedFrobRam`. The data: unram-tate's
`Θ, h` (`tatePoints`), the descent datum of `G7Data`, `γ₀` from `scalarTransferQ`, `a = 1`,
`β' g = γ₀(hgh⁻¹)`, `j_ℓ = IsAlgClosed.lift : ℚ̄ → ℚ̄_ℓ`; `G7Out` at each `ℓ` by unram-tate's
assembly (`tateBridge_of_pieces`) run with the scalars `j_ℓ ∘ 1`, `j_ℓ ∘ β'`. -/
theorem linkedTateCoreDR_of (hT : PkgI3.TateModuleFree) (hFR : LinkedFrobRam) :
    HSyn.LinkedTate.LinkedTateCoreDR := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrank
  haveI hNF : NumberField L' := numberField_of_fd L'
  have hD' := hD
  obtain ⟨hQM, hDD, -, -, -, -, -, hβe, hL', -, -, -⟩ := hD
  obtain ⟨hεc, hinf, h11, m, a, ha0, haL, hmL, hmLL, hmEnd, hmsf, hmc, hmF⟩ := hDD
  choose n d hn hd hnd hna using hmc
  obtain ⟨iot⟩ : Nonempty (LeafQM.O →+* PkgI3.AbVar.End A) := by
    obtain ⟨K, hKL, PK, -, rfl⟩ := hQM
    exact ⟨(endBaseChange K L hKL PK.A).some.comp PK.q.iota⟩
  obtain ⟨Θ, h, hΘ⟩ := tatePoints L L' hLL' A
  have hLL'G : ∀ k, k ∈ GQL L' → k ∈ GQL L := fun k hk => ((hL' k).mp hk).1
  have hβL' : ∀ k, k ∈ GQL L' → β k = 1 := fun k hk => ((hL' k).mp hk).2
  obtain ⟨gam, κ, hκgam, hgam0, hgamc, hgamcos, hgam1⟩ := scalarTransferQ L' a β ε n d hd hna hβe ha0
    (fun σ k hk => ⟨(haL σ k (hLL'G k hk)).2.1, by
      have := hβe σ k
      rw [hβL' k hk, _root_.mul_one, eps_right_one L ε hεc hinf h11 σ k (hLL'G k hk),
        _root_.one_mul] at this
      exact this.symm⟩)
    (fun k hk => ⟨(haL 1 k (hLL'G k hk)).1, hβL' k hk⟩)
  have hC := tateCont_of_tateModuleFree hT
  have hR := resQEmbedding
  let cj : PkgI4.GQ → GQ := fun g => h * g * h⁻¹
  have hcj : ∀ g g₂, cj (g * g₂) = cj g * cj g₂ := fun g g₂ => by
    show h * (g * g₂) * h⁻¹ = (h * g * h⁻¹) * (h * g₂ * h⁻¹)
    group
  -- `G_{L'}` is normal
  have hnorm : (L'.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
  have hres : ∀ σ : Field.absoluteGaloisGroup L',
      cj (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
    intro σ
    have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
      rw [← resQRange L']; exact ⟨σ, rfl⟩
    exact hnorm.conj_mem _ this h
  -- one coefficient prime, with the scalars `j ∘ 1`, `j ∘ γ₀ ∘ cj`
  have key : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ),
      ∃ (c : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ)
        (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
          (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
        G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ
          (tmOf hLL' A Θ h m ℓ) c c (fun _ => j 1) (fun g => j (gam (h * g * h⁻¹))) uu := by
    intro ℓ _ j
    let R : AddMonoid.End (PtQ L A) →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
      (opVHom (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ).comp (conjE Θ)
    let m' : GQ → AddMonoid.End (PtQ L A) := m
    let Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) := fun g => R (m' (cj g))
    let c' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ := fun g g₂ =>
      ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ))
    let a' : PkgI4.GQ → PadicAlgCl ℓ := fun _ => j 1
    let β' : PkgI4.GQ → PadicAlgCl ℓ := fun g => j (gam (cj g))
    -- matrix units
    let QM : LeafQM.O →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
      R.comp ((LeafQM.AV.endPt A Qbar).comp iot)
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (2 : PadicAlgCl ℓ) (by norm_num : 0 < 2)
    have hI : QM iO * QM iO = (2 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
      rw [← map_mul, iO_sq, map_add, map_one, two_smul]
    have hJ : QM jO * QM jO = (-3 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
      rw [← map_mul, jO_sq, map_neg, map_add, map_add, map_one]
      module
    have hIJ : QM iO * QM jO = -(QM jO * QM iO) := by
      rw [← map_mul, iO_jO, map_neg, map_mul]
    obtain ⟨uu, huu⟩ := matrixUnits_of_quat s hs two_ne_zero three_ne_zero _ _ hI hJ hIJ
    have hcomm : ∀ (g : PkgI4.GQ) (o : LeafQM.O), Commute (Tm g) (QM o) := by
      intro g o
      apply Commute.map _ R
      exact hmEnd (cj g) (iot o)
    -- the relations
    have hT : ∀ g g₂, Tm g * Tm g₂ = c' g g₂ • Tm (g * g₂) := by
      intro g g₂
      have h0 : d (cj g) (cj g₂) • (m' (cj g) * m' (cj g₂)) = n (cj g) (cj g₂) • m' (cj g * cj g₂) :=
        hnd (cj g) (cj g₂)
      have h1 := congrArg R h0
      rw [map_zsmul, map_zsmul, ← hcj] at h1
      have h1' : d (cj g) (cj g₂) • (Tm g * Tm g₂) = n (cj g) (cj g₂) • Tm (g * g₂) := by
        show d (cj g) (cj g₂) • (R (m' (cj g)) * R (m' (cj g₂))) = _
        rw [← map_mul]; exact h1
      have h2 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) • (Tm g * Tm g₂) =
          (n (cj g) (cj g₂) : PadicAlgCl ℓ) • Tm (g * g₂) :=
        (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).trans
          (h1'.trans (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).symm)
      have hd0 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) ≠ 0 := Int.cast_ne_zero.mpr (hd _ _)
      show _ = ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ)) • _
      rw [div_eq_inv_mul, ← smul_smul, ← h2, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    have ha : ∀ g g₂, a' g * a' g₂ * c' g g₂ = c' g g₂ * a' (g * g₂) := by
      intro g g₂; simp only [a', map_one, _root_.one_mul, _root_.mul_one]
    have hβ : ∀ g g₂, β' g * β' g₂ = c' g g₂ * β' (g * g₂) := by
      intro g g₂
      show j (gam (cj g)) * j (gam (cj g₂)) =
        ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ)) *
          j (gam (cj (g * g₂)))
      rw [← map_mul, hgamc, map_mul, map_div₀, map_intCast, map_intCast, hcj]
    have hβ0 : ∀ g, β' g ≠ 0 := fun g => (map_ne_zero j).mpr (hgam0 _)
    have hTres : ∀ σ : Field.absoluteGaloisGroup L',
        Tm (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
      intro σ
      have hτ := hres σ
      let σ' : Qbar ≃ₐ[L] Qbar :=
        AlgEquiv.ofRingEquiv (f := (act (cj (@GaloisCopy.resQ L' _ hNF σ))).toRingEquiv)
          (fun x => (mem_GQL.mp (hLL'G _ hτ)) x x.2)
      have hm := hmL (cj (@GaloisCopy.resQ L' _ hNF σ)) σ' (fun x => rfl)
      rw [tate_eq_opV]
      show opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ (conjE Θ (m' (cj _))) = _
      congr 1
      refine DFunLike.ext _ _ fun x => ?_
      show Θ (m (cj (@GaloisCopy.resQ L' _ hNF σ)) (Θ.symm x)) = _
      rw [hm]
      show Θ (MonoidHom.toAdditive (A.galAct σ') (Θ.symm x)) = _
      rw [hΘ σ σ' (fun x => rfl) (Θ.symm x), AddEquiv.apply_symm_apply]
    have hrho1 : ∀ σ : Field.absoluteGaloisGroup L',
        GlueDescent.rho Tm a' β' (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
      intro σ
      unfold GlueDescent.rho
      rw [hTres σ]
      simp only [β', a', hgam1 _ (hres σ), map_one, inv_one, _root_.mul_one, one_smul]
    refine ⟨c', uu, hdim, hrank, hT, ha, hβ, hβ0,
      fun σ => ⟨hTres σ, map_one j, by
        show j (gam (cj (@GaloisCopy.resQ L' _ hNF σ))) = 1
        rw [hgam1 _ (hres σ), map_one]⟩,
      fun g i j => huu i j (Tm g) (hcomm g iO) (hcomm g jO), ?_⟩
    -- continuity
    intro f v
    rw [continuous_iff_continuousAt]
    intro g₀
    let e₀ : Field.absoluteGaloisGroup L' → PkgI4.GQ := fun σ => g₀ * @GaloisCopy.resQ L' _ hNF σ
    have he₀ : Topology.IsOpenEmbedding e₀ :=
      (Homeomorph.mulLeft g₀).isOpenEmbedding.comp (hR L')
    have he₀1 : e₀ 1 = g₀ := by simp only [e₀, map_one, _root_.mul_one]
    have hcomp : (fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀ =
        fun σ => (f ∘ₗ GlueDescent.rho Tm a' β' g₀) (GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ v) := by
      funext σ
      simp only [Function.comp_apply, e₀, LinearMap.comp_apply]
      rw [← GlueDescent.rho_map_mul Tm c' c' a' β' hT ha hβ hβ0, hrho1, Module.End.mul_apply]
    have hc : ContinuousAt ((fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀) 1 := by
      rw [hcomp]; exact (hC L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ v).continuousAt
    rw [he₀.continuousAt_iff, he₀1] at hc
    exact hc
  let j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5 := IsAlgClosed.lift
  let j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3 := IsAlgClosed.lift
  obtain ⟨c5, u5, h5⟩ := key 5 j5
  obtain ⟨c3, u3, h3⟩ := key 3 j3
  obtain ⟨hF, hRam⟩ := hFR Y Φ π u P hctx L A ε N χ β L' hLL' hD' Θ h hΘ m a n d ha0 haL hmL
    hmLL hmEnd hmsf (fun σ τ => ⟨hn σ τ, hd σ τ, hnd σ τ, hna σ τ⟩) hmF gam ⟨κ, hκgam⟩ hgam0 hgamc hgamcos
    hgam1 j5 j3
  exact ⟨fun _ => 1, fun g => gam (h * g * h⁻¹), j5, j3, tmOf hLL' A Θ h m 5, c5, c5, u5,
    tmOf hLL' A Θ h m 3, c3, c3, u3, h5, h3, hF, hRam⟩

end UnramTate

/-- **`LinkedTateData`, proved** from the leaves T7 (`PkgI3.CharPolyIndepOfEll`) and I3.M0
(`PkgI3.TateModuleFree`) and the glue Props `FibreSimple`, `QMEndRank`, `LinkedFrobRam`. -/
theorem HSyn.LinkedTate.linkedTateData_of_frobRam (hM : PkgI3.CharPolyIndepOfEll)
    (hT : PkgI3.TateModuleFree) (hFS : HSyn.G0Split.FibreSimple)
    (hR : HSyn.LinkedTate.QMEndRank) (hFR : UnramTate.LinkedFrobRam) :
    HSyn.G0AssembleMod.LinkedTateData :=
  HSyn.LinkedTate.linkedTateData_of hM
    (HSyn.LinkedTate.linkedTateCore_of hFS hR (UnramTate.linkedTateCoreDR_of hT hFR))

/-- **`AfterG7` (G8-G16) with both joint Props of g0-assemble reduced** (proved): g0-assemble's
inputs of `afterG7_of` (leaf bundles, `GaloisPieces`, `DirichletOfFinite`, `CarayolR17'`, the
three LadicCond glue Props) with `ModelG3G6` and `LinkedTateData` replaced by the glue Props
`FibreSimple` (already a `GluePieces` field), `GoodRedG3Bridge`, `QMEndRank`, `LinkedFrob`,
`LinkedRam`; the leaves used are the bundles' R6, R7a, T5 (G3), T7 (G14) and T26 = I3.M0. -/
theorem HSyn.LinkedTate.afterG7_of_final (r : HSyn.ResearchLeaves) (t : HSyn.TextbookLeaves)
    (m : G0Galois.GaloisPieces) (hDF : G0ModNewform.DirichletOfFinite)
    (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hFS : HSyn.G0Split.FibreSimple) (hB : HSyn.LinkedTate.GoodRedG3Bridge)
    (hR : HSyn.LinkedTate.QMEndRank) (hF : UnramTate.LinkedFrob) (hRam : UnramTate.LinkedRam) :
    G0ModField.AfterG7 :=
  HSyn.G0AssembleMod.afterG7_of r t m hDF hCar hSw hL8 hAd
    (HSyn.LinkedTate.modelG3G6_of hFS (HSyn.LinkedTate.qmModelG3_of r.r7a r.r6 t.t5 hB))
    (HSyn.LinkedTate.linkedTateData_of_frobRam t.t7 t.t26 hFS hR
      (UnramTate.linkedFrobRam_of hF hRam))

end

end LinkedDataSec



-- (g0-assemble3: scratch/linked-tate/parts/98b_ram.lean, verbatim)
/-! ## linked-tate: `LinkedRam` reduced to a field statement about `L'`, G3, and the prime `3`

For the canonical data, `ρ_ℓ(g) = β'(g)⁻¹ Tm(g)` is the Tate action on `G_{L'}` (`β' = 1` there,
`tmOf_resQ`). So clauses (i)-(ii) of `RhoRamWild` follow once the relevant local elements land in
`G_{L'}` (`KernelFieldBreaks`, a statement about the field `L'` alone) and act trivially through
the Tate module: away from `3` this is G3 (`QMModelG3`, already reduced), with local inertia
landing in a global inertia group (`LocalInertiaGlobal`, `UpperAbsInertia`, definitions only);
at `p = 3` (only for `ρ₅`) it is `TateRamAtThree`.

**Caveat (linked-tate finding).** g0-mod-field's `G7Data` does not record `[L:ℚ] ≤ D` (its `G4Out`
does). For `G7Data` with an oversized `L` (e.g. `L ⊇ ℚ(ζ_{2^k})` with `k > U₀ + 1`, allowed when
`M_{S_mul}(u)` is large), `KernelFieldBreaks` (i) fails: `G_{ℚ_2}^t ⊄ G_L ⊇ G_{L'}` for `U₀ < t <
k − 1`; `TateRamAtThree` is likewise only justified for small `K`. `linkedRam_of` is a valid
implication, but its premises are expected to hold only under `[L:ℚ] ≤ D`; `GluePieces3` therefore
keeps `LinkedRam` itself as the field. -/

section LinkedRamSec

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace UnramTate

open G0ModField

/-- **The canonical operators are the Tate action on `G_{L'}`** (proved; the step `hTres` of
unram-tate's assembly, for any `(Θ, h)` with the `TatePoints` property and any `m` equal to the
Galois action on `G_L`). -/
theorem tmOf_resQ {L L' : IF} [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (A : PkgI3.AbVar L)
    (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ)
    (hΘ : ∀ (σ : Field.absoluteGaloisGroup L') (σ' : Qbar ≃ₐ[L] Qbar),
        (∀ x, σ' x = (h * (@GaloisCopy.resQ L' _ (numberField_of_fd L') σ) * h⁻¹) x) →
        ∀ x, Θ (MonoidHom.toAdditive (A.galAct σ') x) =
          MonoidHom.toAdditive ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).galAct σ)
            (Θ x))
    (m : GQ → (PtQ L A →+ PtQ L A))
    (hmL : ∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ'))
    (ℓ : ℕ) [Fact ℓ.Prime] (σ : Field.absoluteGaloisGroup L') :
    tmOf hLL' A Θ h m ℓ (@GaloisCopy.resQ L' _ (numberField_of_fd L') σ) =
      GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
  haveI hNF : NumberField L' := numberField_of_fd L'
  have hnorm : (L'.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
  have hτ : h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹ ∈ GQL L' := by
    have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
      rw [← resQRange L']; exact ⟨σ, rfl⟩
    exact hnorm.conj_mem _ this h
  have hτL : h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹ ∈ GQL L :=
    mem_GQL.mpr (fun x hx => mem_GQL.mp hτ x (hLL' hx))
  let σ' : Qbar ≃ₐ[L] Qbar :=
    AlgEquiv.ofRingEquiv (f := (act (h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹)).toRingEquiv)
      (fun x => (mem_GQL.mp hτL) x x.2)
  have hm := hmL (h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹) σ' (fun x => rfl)
  rw [tate_eq_opV]
  show opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ
    (conjE Θ (m (h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹))) = _
  congr 1
  refine DFunLike.ext _ _ fun x => ?_
  show Θ (m (h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹) (Θ.symm x)) = _
  rw [hm]
  show Θ (MonoidHom.toAdditive (A.galAct σ') (Θ.symm x)) = _
  rw [hΘ σ σ' (fun x => rfl) (Θ.symm x), AddEquiv.apply_symm_apply]

/-- **Glue: the ramification of the kernel field `L'`** (linked-tate; the field half of N5
L819-852, D1 and D3). For every G7 data: for `p ≤ D`, every element of an absolute upper
ramification group `G_{ℚ_p}^t`, `t > U₀`, maps into `G_{L'}` (the upper breaks of `L'` at `p` are
`≤ U₀`); for `p > D`, wild inertia maps into `G_{L'}` (`L'` is tame at `p`: `[L:ℚ] ≤ D < p`, and
`L'/L` is cut out by `β|_{G_L}` with `β² = χ` of order prime to `p` at `p`). GLUE. -/
def KernelFieldBreaks : Prop :=
  ∀ (u : ℚ) (P : LeafQM.AV.QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∀ t : ℝ, G0ModNewform.U0 < t →
          ∀ σ ∈ LadicCond.upperAbs p t, PkgI4.decomp p σ ∈ GQL L') ∧
        ((ZInQ.heightD : ℝ) < p → ∀ σ ∈ (LadicCond.wildSet : Set (PkgI4.GQp p)),
          PkgI4.decomp p σ ∈ GQL L')

/-- **Glue (definitions): local inertia lands in a global inertia group.** For `σ` in the
inertia set of `G_{ℚ_p}`, `decomp p σ` lies in the inertia group of the place `v` of `ℚ̄` induced
by the embedding `ℚ̄ → ℚ̄_p` that `decomp` uses (`v` lies over `p`). GLUE (Mathlib-level). -/
def LocalInertiaGlobal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : PkgI4.GQp p), σ ∈ (LadicCond.inertiaSet : Set (PkgI4.GQp p)) →
    ∃ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p ∧
      ∃ τ ∈ v.inertiaSubgroup ℚ, ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = PkgI4.decomp p σ

/-- **Glue (definitions): upper ramification groups of positive index lie in inertia.** For
`t > 0`, `upperAbs p t ⊆ inertiaSet` (`G^t(L) ⊆ G_0(L)` for each finite Galois `L/ℚ_p`, and every
integral `x ∈ ℚ̄_p` lies in such an `L`). GLUE (Mathlib-level). -/
def UpperAbsInertia : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (t : ℝ), 0 < t →
    LadicCond.upperAbs p t ⊆ (LadicCond.inertiaSet : Set (PkgI4.GQp p))

/-- **Glue: the Tate module of the QM model at `p = 3`** (linked-tate; N5 L819-852, D1-D2 at the
prime `3`, where the model may have bad reduction). For a `QML3` object `PK` over `K ≤ L ≤ L'`
(`L'/ℚ` finite Galois) and `t > U₀`, every `σ' ∈ G_{L'}` whose image is an element of
`G_{ℚ_3}^t` acts trivially on `ℚ̄₅ ⊗ V₅((PK.A)_{L,L'})` (QM surfaces have potentially good
reduction; the inertia image is finite, cut out by a field whose upper breaks at `3` are `≤ U₀`).
GLUE. -/
def TateRamAtThree : Prop :=
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L')
    (PK : LeafQM.AV.QML3 K),
    letI : NumberField L' := numberField_of_fd L'
    ∀ t : ℝ, G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs 3 t,
      ∀ σ' : Field.absoluteGaloisGroup L', G0Galois.resQ L' σ' = PkgI4.decomp 3 σ →
        G0Galois.tate (@PkgI3.AbVar.baseChange L _
          (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) 5 σ' = 1

/-- G3 at a local inertia element (proved from `LocalInertiaGlobal`). -/
theorem tate_trivial_of_g3 (hLI : LocalInertiaGlobal) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (h : G0Galois.G3Out A ℓ {3}) (p : ℕ)
    [Fact p.Prime] (hp3 : p ≠ 3) (hpl : p ≠ ℓ) (σ : PkgI4.GQp p)
    (hσ : σ ∈ (LadicCond.inertiaSet : Set (PkgI4.GQp p))) (σ'' : Field.absoluteGaloisGroup K)
    (hσ'' : G0Galois.resQ K σ'' = PkgI4.decomp p σ) : G0Galois.tate A ℓ σ'' = 1 := by
  obtain ⟨v, hv, τ, hτ, hτeq⟩ := hLI p σ hσ
  exact h p Fact.out (by simpa using hp3) hpl v hv σ'' ⟨τ, hτ, hτeq.trans hσ''.symm⟩

/-- `0 ≤ U₀`. -/
theorem U0_nonneg : 0 ≤ G0ModNewform.U0 := by
  unfold G0ModNewform.U0; positivity

/-- `3 ≤ D`. -/
theorem three_le_heightD : (3 : ℝ) ≤ (ZInQ.heightD : ℝ) := by
  exact_mod_cast G0ModField.le_heightD_of_mem_S_mul
    (ZInQ.Mult.mem_S_mul_of_le Nat.prime_three (by norm_num))

/-- **`LinkedRam`, proved** from `QMModelG3` (G3), `KernelFieldBreaks`, `LocalInertiaGlobal`,
`UpperAbsInertia` and `TateRamAtThree`. -/
theorem linkedRam_of (hG3 : HSyn.LinkedTate.QMModelG3) (hK : KernelFieldBreaks)
    (hLI : LocalInertiaGlobal) (hUI : UpperAbsInertia) (h3 : TateRamAtThree) : LinkedRam := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD Θ h hΘ m a n d h1 h2 hmL h4 h5 h6 h7 h8
    gam g0 g1 g2 g3 hgam1 j5 j3
  haveI hNF : NumberField L' := numberField_of_fd L'
  have hK' := hK u P L A ε N χ β L' hLL' hD
  obtain ⟨K, hKL, PK, -, rfl⟩ := hD.1
  have hnorm : (L'.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
  -- on `G_{L'}`, `ρ` is the Tate action
  have hρ : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (g : PkgI4.GQ),
      g ∈ GQL L' →
      (∀ σ'' : Field.absoluteGaloisGroup L', G0Galois.resQ L' σ'' = g →
        G0Galois.tate (@PkgI3.AbVar.baseChange L _
          (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) ℓ σ'' = 1) →
      GlueDescent.rho (tmOf hLL' _ Θ h m ℓ) (fun _ => j 1) (fun g => j (gam (h * g * h⁻¹))) g
        = 1 := by
    intro ℓ _ j g hg ht
    obtain ⟨σ'', hσ''⟩ : g ∈ (@GaloisCopy.resQ L' _ hNF).range := by
      rw [resQRange L']; exact hg
    subst hσ''
    have hcj : h * (@GaloisCopy.resQ L' _ hNF σ'') * h⁻¹ ∈ GQL L' := hnorm.conj_mem _ hg h
    unfold GlueDescent.rho
    rw [tmOf_resQ hLL' _ Θ h hΘ m hmL ℓ σ'']
    have ht' : GaloisCopy.tate (@PkgI3.AbVar.baseChange L _
        (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) ℓ σ'' = 1 :=
      ht σ'' rfl
    have hγ : gam (h * (@GaloisCopy.resQ L' _ hNF σ'') * h⁻¹) = 1 := hgam1 _ hcj
    rw [ht']
    show ((j (gam (h * (@GaloisCopy.resQ L' _ hNF σ'') * h⁻¹)))⁻¹ * j 1) • (1 : Module.End _ _) = 1
    rw [hγ, map_one, inv_one, _root_.one_mul, one_smul]
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hG5 := hG3 K L L' hKL hLL' PK 5
  have hG3' := hG3 K L L' hKL hLL' PK 3
  refine ⟨fun hp5 => ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_⟩,
    fun hp5 => ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_⟩⟩
  · -- `ρ₅`, `p ≠ 5`, `p ≤ D`
    have hσI := hUI p t (lt_of_le_of_lt U0_nonneg ht) hσ
    refine hρ 5 j5 _ ((hK' p hp).1 hpD t ht σ hσ) (fun σ'' hσ'' => ?_)
    by_cases hp3 : p = 3
    · subst hp3
      exact h3 K L L' hKL hLL' PK t ht σ hσ σ'' hσ''
    · exact tate_trivial_of_g3 hLI hG5 p hp3 hp5 σ hσI σ'' hσ''
  · -- `ρ₅`, `p ≠ 5`, `p > D`
    have hσI := LadicCond.wildSet_subset_inertiaSet hσ
    have hp3 : p ≠ 3 := by
      intro h3'
      subst h3'
      have := three_le_heightD
      push_cast at hpD
      linarith
    exact hρ 5 j5 _ ((hK' p hp).2 hpD σ hσ)
      (fun σ'' hσ'' => tate_trivial_of_g3 hLI hG5 p hp3 hp5 σ hσI σ'' hσ'')
  · -- `ρ₃`, `p = 5`, `p ≤ D`
    have hσI := hUI p t (lt_of_le_of_lt U0_nonneg ht) hσ
    have hp3 : p ≠ 3 := by omega
    exact hρ 3 j3 _ ((hK' p hp).1 hpD t ht σ hσ)
      (fun σ'' hσ'' => tate_trivial_of_g3 hLI hG3' p hp3 hp3 σ hσI σ'' hσ'')
  · -- `ρ₃`, `p = 5`, `p > D`
    have hσI := LadicCond.wildSet_subset_inertiaSet hσ
    have hp3 : p ≠ 3 := by omega
    exact hρ 3 j3 _ ((hK' p hp).2 hpD σ hσ)
      (fun σ'' hσ'' => tate_trivial_of_g3 hLI hG3' p hp3 hp3 σ hσI σ'' hσ'')

end UnramTate

end

end LinkedRamSec



-- (g0-assemble3: scratch/linked-tate/parts/98c_inertia.lean, verbatim)
/-! ## linked-tate: `LocalInertiaGlobal` proved (Mathlib)

The place is the comap `v` of the valuation `‖·‖` of `ℚ̄_p` along the embedding `ℚ̄ → ℚ̄_p` that
`decomp` uses (`embP`, with `embP ∘ decomp σ = σ ∘ embP`, Mathlib's `restrictNormal_commutes`):
`decomp σ` preserves `v` (`σ` is an isometry, `PkgI4.norm_gqp_apply`), `p ∈ v.nonunits`
(`‖p‖ = p⁻¹`), and for `σ` in the inertia set `decomp σ` acts trivially on the residue field of
`v` (`‖σx − x‖ < 1` for `‖x‖ ≤ 1`). First compiled standalone over Mathlib
(`scratch/linked-tate/test/LocalInertia.lean`). -/

section LocalInertiaSec

noncomputable section

open scoped Pointwise

namespace UnramTate

variable (p : ℕ) [Fact p.Prime]

/-- The embedding `ℚ̄ → ℚ̄_p` that `decomp` uses. -/
def embP : PkgI4.Qbar →+* PadicAlgCl p :=
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom

theorem embP_decomp (σ : PkgI4.GQp p) (x : PkgI4.Qbar) : embP p (PkgI4.decomp p σ x) = σ (embP p x) := by
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[p]) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

theorem localInertiaGlobal_at (σ : PkgI4.GQp p) (hσ : σ ∈ (LadicCond.inertiaSet : Set (PkgI4.GQp p))) :
    ∃ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p ∧
      ∃ τ ∈ v.inertiaSubgroup ℚ, ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = PkgI4.decomp p σ := by
  let w : Valuation PkgI4.Qbar NNReal := (Valued.v : Valuation (PadicAlgCl p) NNReal).comap (embP p)
  let v := w.valuationSubring
  have hmem : ∀ x, x ∈ v ↔ ‖embP p x‖ ≤ 1 := by
    intro x
    show Valued.v (embP p x) ≤ 1 ↔ _
    rw [← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  have hnorm : ∀ (g : PkgI4.GQp p) (x : PkgI4.Qbar), ‖embP p (PkgI4.decomp p g x)‖ = ‖embP p x‖ := by
    intro g x; rw [embP_decomp, PkgI4.norm_gqp_apply]
  have hτv : PkgI4.decomp p σ ∈ v.decompositionSubgroup ℚ := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hmem, hmem, ← map_inv]
    exact iff_of_eq (congrArg (· ≤ (1 : ℝ)) (hnorm σ⁻¹ x))
  have hnu : ∀ x : PkgI4.Qbar, ‖embP p x‖ < 1 → x ∈ v.nonunits := by
    intro x hx
    rw [ValuationSubring.mem_nonunits_iff_or]
    by_cases h0 : x = 0
    · exact Or.inl h0
    · right
      rw [hmem, map_inv₀, norm_inv]
      have hpos : 0 < ‖embP p x‖ := norm_pos_iff.mpr ((map_ne_zero _).mpr h0)
      intro h
      have := (inv_le_one₀ hpos).mp h
      linarith
  refine ⟨v, ?_, ⟨⟨PkgI4.decomp p σ, hτv⟩, ?_, rfl⟩⟩
  · apply hnu
    rw [map_natCast]
    have : ‖((p : ℚ_[p]) : PadicAlgCl p)‖ = ‖(p : ℚ_[p])‖ := PadicAlgCl.norm_extends p _
    rw [map_natCast] at this
    rw [this, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  · rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    ext r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    change (⟨PkgI4.decomp p σ, hτv⟩ : v.decompositionSubgroup ℚ) • IsLocalRing.residue v a =
      IsLocalRing.residue v a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
    apply hnu
    show ‖embP p (PkgI4.decomp p σ (a : PkgI4.Qbar) - a)‖ < 1
    rw [map_sub, embP_decomp]
    exact hσ _ ((hmem a).mp a.2)

/-- **`LocalInertiaGlobal`, proved.** -/
theorem localInertiaGlobal : LocalInertiaGlobal := fun p _ σ hσ => localInertiaGlobal_at p σ hσ

end UnramTate

end

end LocalInertiaSec



-- (g0-assemble3: scratch/linked-tate/parts/98d_upperabs.lean, verbatim)
/-! ## linked-tate: `UpperAbsInertia` proved (Mathlib)

For `t > 0`, the lower index `sInf {u ≥ −1 | t ≤ φ_L(u)}` is `≥ 0` (`φ_L ≤ 0` on `u ≤ 0`, an
integral of a nonnegative function), so `G^t(L) ⊆ G_0(L)`: `‖σx − x‖ ≤ ‖ϖ‖^{n+1} < 1` on the unit
ball of `L`. Every `x ∈ ℚ̄_p` lies in the finite Galois normal closure of `ℚ_p(x)`. First compiled
standalone over Mathlib (`scratch/linked-tate/test/UpperAbs.lean`). -/

section UpperAbsSec

noncomputable section

namespace UnramTate

variable {p : ℕ} [Fact p.Prime]

theorem phiAt_nonpos (L : LadicCond.Fld p) {u : ℝ} (hu : u ≤ 0) : LadicCond.phiAt L u ≤ 0 := by
  unfold LadicCond.phiAt
  rw [intervalIntegral.integral_symm]
  have : 0 ≤ ∫ t in u..(0 : ℝ), (LadicCond.ramCardR L t : ℝ) / (LadicCond.ramCard L 0 : ℝ) :=
    intervalIntegral.integral_nonneg hu (fun _ _ => by positivity)
  linarith

theorem sInf_nonneg_of_pos (L : LadicCond.Fld p) {t : ℝ} (ht : 0 < t) :
    0 ≤ sInf {u : ℝ | -1 ≤ u ∧ t ≤ LadicCond.phiAt L u} := by
  rcases Set.eq_empty_or_nonempty {u : ℝ | -1 ≤ u ∧ t ≤ LadicCond.phiAt L u} with h | h
  · rw [h, Real.sInf_empty]
  · apply le_csInf h
    rintro u ⟨-, hu⟩
    by_contra hneg
    push Not at hneg
    have := phiAt_nonpos L hneg.le
    linarith

theorem upperSet_sub (L : LadicCond.Fld p) {t : ℝ} (ht : 0 < t) (σ : PkgI4.GQp p) (hσ : σ ∈ LadicCond.upperSet L t) :
    ∀ x ∈ L, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1 := by
  have h0 := sInf_nonneg_of_pos L ht
  unfold LadicCond.upperSet LadicCond.ramSetR at hσ
  rw [if_neg (show ¬ _ ≤ (-1 : ℝ) by linarith)] at hσ
  obtain ⟨ϖ, hϖ, hle⟩ := hσ
  intro x hx hx1
  refine lt_of_le_of_lt (hle x hx hx1) ?_
  exact pow_lt_one₀ (norm_nonneg _) hϖ.2.1 (Nat.succ_ne_zero _)

theorem upperAbs_subset_inertiaSet' (t : ℝ) (ht : 0 < t) :
    LadicCond.upperAbs p t ⊆ (LadicCond.inertiaSet : Set (PkgI4.GQp p)) := by
  intro σ hσ x hx
  let K : LadicCond.Fld p := IntermediateField.adjoin ℚ_[p] {x}
  haveI hKfin : FiniteDimensional ℚ_[p] K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  let L : LadicCond.Fld p := IntermediateField.normalClosure ℚ_[p] K (LadicCond.Kbar p)
  have hL : LadicCond.IsFinGal L := ⟨inferInstance, inferInstance⟩
  have hxL : x ∈ L := IntermediateField.le_normalClosure K (IntermediateField.mem_adjoin_simple_self ℚ_[p] x)
  exact upperSet_sub L ht σ (hσ L hL) x hxL hx

/-- **`UpperAbsInertia`, proved.** -/
theorem upperAbsInertia : UpperAbsInertia := fun _ _ t ht => upperAbs_subset_inertiaSet' t ht

end UnramTate

end

end UpperAbsSec



-- (g0-assemble3: scratch/linked-tate/parts/98_g3tate.lean, verbatim)
/-! ## linked-tate: `GoodRedG3Bridge` reduced to its torsion-point form `GoodRedTorsion`

`G3Out` asks that inertia act trivially on `ℚ̄_ℓ ⊗ V_ℓ`. Triviality on every `A[ℓⁿ](K̄)` implies
it, because `T_ℓ(A)` consists of compatible sequences of `ℓⁿ`-torsion points
(`tate_eq_one_of_torsion`, proved). What remains of G3's transport is the statement at the level
of points, where NOS itself speaks (`PkgI2.InertiaTrivialOn`). -/

section LinkedTateG3Sec

noncomputable section

namespace HSyn.LinkedTate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-- **Inertia acting trivially on all `ℓ`-power torsion acts trivially on `ℚ̄_ℓ ⊗ V_ℓ`**
(proved): each coordinate `xₙ` of `x ∈ T_ℓ(A)` is `ℓⁿ`-torsion. -/
theorem tate_eq_one_of_torsion {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (σ : Field.absoluteGaloisGroup K)
    (h : ∀ (n : ℕ) (x : A.Pt (AlgebraicClosure K)), x ^ (ℓ ^ n) = 1 → A.galAct σ x = x) :
    G0Galois.tate A ℓ σ = 1 := by
  have hT : A.galT (ℓ := ℓ) σ = LinearMap.id := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    have hx : (ℓ ^ n) • x.1 n = 0 := PkgI3.Tate.pow_smul_eq_zero x.2 n
    have hx' : (Additive.toMul (x.1 n)) ^ (ℓ ^ n) = 1 := by
      rw [← toMul_nsmul, hx]; rfl
    show Additive.ofMul (A.galAct σ (Additive.toMul (x.1 n))) = x.1 n
    rw [h n _ hx']; rfl
  have hR : A.galRep ℓ σ = 1 := by
    change (A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ] = LinearMap.id
    rw [hT, LinearMap.baseChange_id]
  change (A.galRep ℓ σ).baseChange (PadicAlgCl ℓ) = LinearMap.id
  rw [hR, Module.End.one_eq_id, LinearMap.baseChange_id]

/-- **Glue: good reduction away from `3` makes inertia trivial on torsion points of the base
change** (linked-tate; the point-level transport half of G3, given the leaf R7a). Same hypotheses
as `GoodRedG3Bridge`. Conclusion: for `p ∉ {3}`, `p ≠ ℓ`, and an element `σ'` of `G_{L'}` whose
image `resQ σ'` lies in the inertia group of a place `v` of `ℚ̄` above `p`, `σ'` fixes every
`ℓⁿ`-torsion point of `A_{L,L'}(\bar{L'})`. Route (STANDARD): `v ∩ K` is a DVR of `K` with `3` a
unit; NOS (a) ⇒ (b) over `K` (PkgI2's `InertiaTrivialOn` on `A(K̄)[ℓⁿ]` at a valuation ring of
`K̄` over `v ∩ K`); transport along `\bar{L'} ≅ K̄` over `K` (`resQ`'s embedding `ℚ̄ → \bar{L'}`) and
`A_{L,L'}(\bar{L'}) = A(\bar{L'})` (unram-tate's `bcPt`). GLUE (definitions only; no new
literature). -/
def GoodRedTorsion : Prop :=
  PkgI2.NeronOggShafarevich.{0} →
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L') (A : PkgI3.AbVar K),
    (∀ (Ov : ValuationSubring K) [IsDiscreteValuationRing Ov], IsUnit (3 : Ov) →
      PkgI2.HasGoodReduction (ObjBridge.toGrp A) Ov) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      letI : NumberField L' := numberField_of_fd L'
      ∀ p : ℕ, p.Prime → p ∉ ({3} : Finset ℕ) → p ≠ ℓ →
        ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
        ∀ σ' : Field.absoluteGaloisGroup L',
          (∃ σ ∈ v.inertiaSubgroup ℚ,
            ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = G0Galois.resQ L' σ') →
          ∀ (n : ℕ) (x : (@PkgI3.AbVar.baseChange L _
              (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).Pt
              (AlgebraicClosure L')),
            x ^ (ℓ ^ n) = 1 →
            (@PkgI3.AbVar.baseChange L _
              (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).galAct σ' x = x

/-- **`GoodRedG3Bridge`, proved** from `GoodRedTorsion` (`tate_eq_one_of_torsion`). -/
theorem goodRedG3Bridge_of_torsion (h : GoodRedTorsion) : GoodRedG3Bridge := by
  intro hNOS K L L' _ hKL hLL' A hA ℓ _
  letI : NumberField L' := numberField_of_fd L'
  intro p hp hpT hpl v hv σ' hσ
  exact tate_eq_one_of_torsion _ ℓ σ' (h hNOS K L L' hKL hLL' A hA ℓ p hp hpT hpl v hv σ' hσ)

end HSyn.LinkedTate

end

end LinkedTateG3Sec



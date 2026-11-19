import ZInQKernel.Contrib.CloudB3E2Norm.RingClassKS
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Kummer

/-!
# Strictness at the old places: the strict-lift hypotheses from the local Kummer conditions

Manuscript `diophantine_zq.tex`, tex 3262–3270 ("Thus the old Kummer conditions proved in paragraph
5 survive (H20)") and tex 4157–4170 (the norm identity). The strict-lift hypotheses `hRloc`, `hPloc`
of `hzR_genuine_of_strictLifts` (`LocalComponents.lean`) ask that the localization `res a_T` of a
global class lies in the image of the local conditions. This file reduces them, for the genuine
Selmer data, to one membership statement per old place, in the local Kummer conditions of lanes
RC28/RC29 (`kummerConditionIn`, `actualKummerAt`, `actualKummerAtS`):

* `mem_range_cocycleConditionι_iff` (PROVED): a degree-one local cochain `c` lies in the image of a
  cocycle condition `U¹ = Z ⊔ B¹ → C¹_cont(G_v, M)` iff `c ∈ Z ⊔ B¹`;
  `mem_kummer_of_eq_add_d0`, `mem_kummer_of_eq_sum_add_d0` (PROVED): for the Kummer condition,
  `c = ∑_j ι ∘ κ(a_j, P_j) + d⁰ b` (extended local Kummer cocycles of local points `P_j ∈ B(K_v)`
  plus a coboundary) suffices.
* `exists_lift_selData` (PROVED): for the genuine Selmer data `selData Δ` of any local conditions
  `Δ`, a global cochain `a` has a lift `u` with `ι u = res a` as soon as its localization at every
  place lies in the image of that place's condition.
* `exists_lift_relaxedAt` (PROVED): for the relaxed data `relaxedAt D res_w` (full condition at the
  new place), only the old places matter; `exists_lift_addPlace` (PROVED): for the primitive data
  `addPlace D res_w ι_w`, the old places and the new place `w` (in the image of `ι_w`).
* `exists_hPloc_primToRel` (PROVED): the primitive hypothesis `hPloc` through `primToRel`, from the
  old places and the new place.
* **`exists_hRloc_genuine`** (PROVED): `hRloc` of `hzR_genuine_of_strictLifts` at the genuine
  relaxed data from one membership per old place.
* `restrictPlaces Δ hS` (definition): local conditions indexed by `Places K S` (lanes RC28/RC29)
  restricted to the old places `Places K S₀ ⊆ Places K S`, with the same global group `G_{K,S}` and
  the same local complexes (definitional), in the format of RC32's `genuineOld`.
* Non-vacuity: `nonVacuity_oldStrict`.

**What remains** (the arithmetic input, tex 3251–3270): at every old place `v`, the localization of
the transferred Kummer cochain `𝒯_θ(κ(Q_T))` restricted to `G_{K_v}` is of the form
`∑_j ι_v ∘ κ(a_j, P_j) + d⁰ b` for local points `P_j ∈ B(K_v)` of the local twist. Its group-theoretic
part is in the tree: the local Mackey formula (each decomposition-group orbit term of the transfer
is a local corestriction plus a coboundary, `HeegnerCohomology/MackeyCor.lean`,
`orbitTerm_eq_cor_add_coboundary`) and the corestriction of a Kummer cocycle is the Kummer cocycle
of the transversal norm (`CochainNorm.lean`, `cor_kummer`). Its arithmetic part is not: the
identification of the local coefficient module through the local twist (`E^{(h)}[2^i] ≅ E[2^i](χ_h)`
over `K̄_v` and the embedding `K_S → K̄_v`, the GLUE input of `KummerAt.lean`), and the local
points of the twist over `K_v` obtained as local norms. **Coefficient mismatch**: lanes RC28/RC29's
conditions live over the stage ring `Acoef i` (module `Mcoef`/`MinS`), while RC32's abbrevs
`genuineOld`/`genuineRelaxed` are declared over a topological field `k`. The generic reductions
here and in `LocalComponents.lean` (`exists_lift_selData`, `exists_lift_relaxedAt`,
`exists_lift_addPlace`, `exists_hPloc_primToRel`, `hU_hL_of_strictLifts`, `hzR_of_strictLifts`) are
stated for any commutative ring and any `selData Δ`, so they apply to `Acoef i` directly; the
genuine wrappers `exists_hRloc_genuine` and `hzR_genuine_of_strictLifts` carry `[Field k]` and
would be generalized together with the genuine abbrevs.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules

universe u

/-! ### Membership in a cocycle condition -/

section Cocycle

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- **The image of a cocycle condition in degree one is `Z ⊔ B¹`** (PROVED). -/
theorem mem_range_cocycleConditionι_iff (Z : Submodule k (contCochain k G M 1))
    (hZ : ∀ z ∈ Z, contD k G M 1 z = 0) (c : (natCx (contCochains k G M)).X 1) :
    (∃ u, (cocycleConditionι Z hZ).f 1 1 rfl u = c) ↔
      ((contSubCx k G M).el c : contCochain k G M 1) ∈ Z ⊔ contB1 k G M := by
  constructor
  · rintro ⟨u, rfl⟩
    exact u.2
  · intro h
    exact ⟨(⟨(contSubCx k G M).el c, h⟩ : (condSubCx Z hZ).P 1), rfl⟩

end Cocycle

section Kummer

variable {F : Type} [Field F] [CharZero F] [DecidableEq F] {B : WeierstrassCurve F} [B.IsElliptic]
  {m : ℕ} [NeZero m] {k : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M] [SMulCommClass (Field.absoluteGaloisGroup F) k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M]
  (ι : TorsAlg F B m →+ M)
  (hι : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (σ • t) = σ • ι t)

/-- **A local Kummer cocycle plus a coboundary lies in the Kummer condition** (PROVED): if
`c = ι ∘ κ(a, P) + d⁰ b` for a local point `P ∈ B(F)`, then `c` is in the image of the extended
Kummer condition `kummerConditionIn` in degree one. -/
theorem mem_kummer_of_eq_add_d0 (c : (natCx (contCochains k (Field.absoluteGaloisGroup F) M)).X 1)
    (a : k) (P : B.toAffine.Point) (b : contCochain k (Field.absoluteGaloisGroup F) M 0)
    (hc : (show contCochain k (Field.absoluteGaloisGroup F) M 1 from c) =
      kummerCocycleIn ι a P + contD k (Field.absoluteGaloisGroup F) M 0 b) :
    ∃ u, (kummerConditionInι k ι hι).f 1 1 rfl u = c := by
  rw [kummerConditionInι, mem_range_cocycleConditionι_iff]
  change (show contCochain k (Field.absoluteGaloisGroup F) M 1 from c) ∈ _
  rw [hc]
  exact Submodule.add_mem_sup (kummerCocycleIn_mem ι a P) (LinearMap.mem_range.2 ⟨b, rfl⟩)

/-- **A finite combination of local Kummer cocycles plus a coboundary lies in the Kummer
condition** (PROVED): if `c = ∑_j ι ∘ κ(a_j, P_j) + d⁰ b`, then `c` is in the image of the extended
Kummer condition in degree one (the form of the arithmetic input stated in the module docstring). -/
theorem mem_kummer_of_eq_sum_add_d0
    (c : (natCx (contCochains k (Field.absoluteGaloisGroup F) M)).X 1)
    {J : Type} (s : Finset J) (a : J → k) (P : J → B.toAffine.Point)
    (b : contCochain k (Field.absoluteGaloisGroup F) M 0)
    (hc : (show contCochain k (Field.absoluteGaloisGroup F) M 1 from c) =
      ∑ j ∈ s, kummerCocycleIn ι (a j) (P j) + contD k (Field.absoluteGaloisGroup F) M 0 b) :
    ∃ u, (kummerConditionInι k ι hι).f 1 1 rfl u = c := by
  rw [kummerConditionInι, mem_range_cocycleConditionι_iff]
  change (show contCochain k (Field.absoluteGaloisGroup F) M 1 from c) ∈ _
  rw [hc]
  exact Submodule.add_mem_sup (Submodule.sum_mem _ fun j _ => kummerCocycleIn_mem ι (a j) (P j))
    (LinearMap.mem_range.2 ⟨b, rfl⟩)

end Kummer

/-! ### Lifts for the genuine Selmer data -/

section SelData

variable {k : Type u} [CommRing k] {GS : Type u} [Group GS] [TopologicalSpace GS]
  [IsTopologicalGroup GS] {ι : Type u} {Gv : ι → Type u} [∀ v, Group (Gv v)]
  [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* GS}
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]

/-- **A lift through the genuine local conditions, place by place** (PROVED): if the localization
of `a` at every place lies in the image of that place's condition in degree one, then
`ι u = res a` for some `u`. -/
theorem exists_lift_selData (Δ : LocalConditions k GS Gv loc M) (a : (selData k GS Gv loc M Δ).G.X 1)
    (h : ∀ v, ∃ u : (Δ.U v).X 1,
      (Δ.i v).f 1 1 rfl u = (selData k GS Gv loc M Δ).res.f 1 1 rfl a v) :
    ∃ u : (selData k GS Gv loc M Δ).U.X 1,
      (selData k GS Gv loc M Δ).ι.f 1 1 rfl u = (selData k GS Gv loc M Δ).res.f 1 1 rfl a := by
  choose u hu using h
  exact ⟨u, funext hu⟩

end SelData

section AddPlace

variable {S : Type} [CommRing S] (D : SelData S) {Lq : GCx S} (resq : GHom D.G Lq)

/-- **Lifts for the relaxed data: only the old places matter** (PROVED). -/
theorem exists_lift_relaxedAt (a : D.G.X 1)
    (h : ∃ u : D.U.X 1, D.ι.f 1 1 rfl u = D.res.f 1 1 rfl a) :
    ∃ u : (relaxedAt D resq).U.X 1,
      (relaxedAt D resq).ι.f 1 1 rfl u = (relaxedAt D resq).res.f 1 1 rfl a := by
  obtain ⟨u, hu⟩ := h
  exact ⟨((u, resq.f 1 1 rfl a) : D.U.X 1 × Lq.X 1), Prod.ext hu rfl⟩

/-- **Lifts for the primitive data: the old places and the new place** (PROVED). -/
theorem exists_lift_addPlace {Uq : GCx S} (ιq : GHom Uq Lq) (a : D.G.X 1)
    (h : ∃ u : D.U.X 1, D.ι.f 1 1 rfl u = D.res.f 1 1 rfl a)
    (hq : ∃ y : Uq.X 1, ιq.f 1 1 rfl y = resq.f 1 1 rfl a) :
    ∃ u : (addPlace D resq ιq).U.X 1,
      (addPlace D resq ιq).ι.f 1 1 rfl u = (addPlace D resq ιq).res.f 1 1 rfl a := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨y, hy⟩ := hq
  exact ⟨((u, y) : D.U.X 1 × Uq.X 1), Prod.ext hu hy⟩

/-- **The primitive strict-lift hypothesis through `primToRel`** (PROVED): for
`f = primToRel D res_w ι_w` (identity on the old conditions, `ι_w` at the new place), a lift `u_P`
with `ι(f u_P) = res a_P` exists as soon as `a_P` lifts at the old places and its localization at
`w` lies in the image of `ι_w`. -/
theorem exists_hPloc_primToRel {Uq : GCx S} (ιq : GHom Uq Lq) (a : D.G.X 1)
    (h : ∃ u : D.U.X 1, D.ι.f 1 1 rfl u = D.res.f 1 1 rfl a)
    (hq : ∃ y : Uq.X 1, ιq.f 1 1 rfl y = resq.f 1 1 rfl a) :
    ∃ uP : (prodCx D.U Uq).X 1,
      (relaxedAt D resq).ι.f 1 1 rfl ((primToRel D resq ιq).f 1 1 rfl uP) =
        (relaxedAt D resq).res.f 1 1 rfl a := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨y, hy⟩ := hq
  exact ⟨((u, y) : D.U.X 1 × Uq.X 1), Prod.ext hu hy⟩

end AddPlace

/-! ### At the genuine relaxed Selmer data -/

section GenuineTriangle

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [Field k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- **`hRloc` of `hzR_genuine_of_strictLifts` from the old places** (PROVED): at the genuine
relaxed data, a lift `u_R` with `ι u_R = res a_R` exists as soon as, at every old place `v ∈ S₀`,
the localization of `a_R` lies in the image of the old condition `Δ_v` (for a Kummer condition:
`mem_kummer_of_eq_add_d0`). -/
theorem exists_hRloc_genuine
    (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M) (w : Places K S) (aR : (globalCx k (GKS K S) M).X 1)
    (hold : ∀ v : Places K S₀, ∃ u : (Δ.U v).X 1,
      (Δ.i v).f 1 1 rfl u = (genuineOld K S₀ S k M Δ).res.f 1 1 rfl aR v) :
    ∃ uR : (genuineRelaxed K S₀ S k M Δ w).U.X 1,
      (genuineRelaxed K S₀ S k M Δ w).ι.f 1 1 rfl uR =
        (genuineRelaxed K S₀ S k M Δ w).res.f 1 1 rfl aR :=
  exists_lift_relaxedAt (genuineOld K S₀ S k M Δ) (genuineRes K S k M w) aR
    (exists_lift_selData Δ aR hold)

end GenuineTriangle

/-! ### Restriction of local conditions to the old places -/

section Restrict

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]

/-- **Local conditions at all places of `S`, restricted to the old places `S₀ ⊆ S`**, with the
same global group `G_{K,S}` and the same local complexes (definitional): the format of RC32's
`genuineOld` for the conditions of lanes RC28/RC29. Kind: definition. -/
def restrictPlaces (Δ : LocalConditions k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) M) (hS : S₀ ⊆ S) :
    LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1) (fun v => locMap K S v.1) M where
  U v := Δ.U ⟨v.1, hS v.2⟩
  i v := Δ.i ⟨v.1, hS v.2⟩

/-- The restricted conditions at an old place are the original ones. Kind: PROVED. -/
theorem restrictPlaces_U (Δ : LocalConditions k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) M) (hS : S₀ ⊆ S) (v : Places K S₀) :
    (restrictPlaces Δ hS).U v = Δ.U ⟨v.1, hS v.2⟩ :=
  rfl

end Restrict

/-! ### Non-vacuity -/

/-- **Non-vacuity of the hypotheses of `exists_lift_relaxedAt` and `exists_lift_addPlace`**: the
zero cochain lifts through any conditions. Kind: PROVED. -/
theorem nonVacuity_oldStrict {S : Type} [CommRing S] (D : SelData S) {Lq Uq : GCx S}
    (resq : GHom D.G Lq) (ιq : GHom Uq Lq) :
    (∃ u : D.U.X 1, D.ι.f 1 1 rfl u = D.res.f 1 1 rfl 0) ∧
      ∃ y : Uq.X 1, ιq.f 1 1 rfl y = resq.f 1 1 rfl 0 :=
  ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩

end ZInQ.Contrib.CloudB3E2.NormCochain

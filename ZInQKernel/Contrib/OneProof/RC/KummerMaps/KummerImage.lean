import ZInQKernel.Contrib.OneProof.RC.KummerMaps.Iota

/-!
# Lane RC29 (Kummer maps), part 4: the actual Kummer condition in cohomology

Manuscript `diophantine_zq.tex` (11/5), Lemma `ex:arith-local-kummer` (tex 3413–3438): "the
condition `U_F = B(F)^∧_2[−1] → RΓ(F, T_2B)` includes the finite two-primary torsion. Its
reduction modulo `2^a` has `B(F)[2^a]` in degree zero and `B(F)/2^aB(F)` in degree one. … At
`v ∣ 2N`, … derived coefficient extension defines the scalar `A_i` condition for this actual
twist."

How lane RC28's finite-level Kummer subcomplex, with the genuine coefficient map `ι_v` of
`Iota.lean`, realizes the actual Kummer local condition at `v` — **as the image of the local
Kummer map `E^{(h)}(K_v)/2^i → H¹(K_v, M_i)`** (extended `A_i`-linearly):

* `cocycleCondition_range_homologyMap_one` (generic, PROVED): for lane RC28's cocycle condition
  `U⁰ = C⁰`, `U¹ = Z ⊔ B¹`, `Uⁿ = 0` cut out by a submodule `Z` of `1`-cocycles, **the image of
  `H¹(U) → H¹(C^•_cont(G, M))` is exactly the set of classes of cocycles lying in `Z ⊔ B¹`**.
* `kummerCocycleIn_apply_eq` (PROVED): the generators `g ↦ a • ι(κ_P(g))` of lane RC28's
  `kummerZ'` are the push-forwards along `ι` of lane RC28's genuine Kummer cocycles
  `κ_P(σ) = σQ − Q` (`m Q = P`), scaled by `a ∈ A_i`.
* **The local Kummer map with coefficients in `M`** (generic, for any equivariant `ι`):
  `kummerCocycleIn_add`, `kummerCocycleIn_nsmul_mem` (the push-forwards of lane RC28's
  `kummerCocycle_add` and of the coboundary criterion), `kummerMapIn : B(F) →+ H¹(G_F, M)`,
  `P ↦ ι_*[κ_P]`; `kummerMapIn_nsmul`: it kills `m B(F)`, i.e. it is defined on `B(F)/mB(F)`;
  **`range_homologyMap_kummerConditionIn`: the image of `H¹(U) → H¹(G_F, M)` is the `k`-span of
  the image of `kummerMapIn`** (PROVED).
* For the actual Kummer condition `actualKummerAt` (lane RC28's `kummerAt` with the genuine
  `ι_v`):
  - `actualKummerAt_isIso_H0`: `H⁰(U_v) ≅ H⁰(K_v, M_i)` (the degree-zero torsion is all of
    `H⁰`);
  - `actualKummerAt_mono_H1`: `H¹(U_v) → H¹(K_v, M_i)` is injective;
  - `actualKummerMap : E^{(h)}(K_v) →+ H¹(K_v, M_i)`, the actual local Kummer map,
    `actualKummerMap_nsmul` (it factors through `E^{(h)}(K_v)/2^i`);
  - **`actualKummerAt_range_eq_span`: the actual Kummer condition at `v` is the image of the local
    Kummer map `E^{(h)}(K_v)/2^i → H¹(K_v, M_i)`, extended `A_i`-linearly** (the `A_i`-span of
    its image), and `actualKummerAt_range_H1` the same on cocycles: the image consists of the
    classes of cocycles in `span_{A_i}{ι_v ∘ κ_P : P ∈ B(K_v)} + B¹`.

How this relates to the text's derived object (DEPARTURE, as in lane RC28): the text's condition
is `U_F ⊗^L A_i` with `U_F = B(F)^∧_2[−1]`; since `A_i` is free over `ℤ/2^i`, its `H¹` is
`(B(F)/2^i) ⊗ A_i`, which the Kummer map (injective, lane RC28's `kummerMapH1_injective`) carries
isomorphically onto the `A_i`-span of the Kummer classes in
`H¹(K_v, B[2^i]) ⊗ A_i = H¹(K_v, M_i)`, and its `H⁰` is `B(F)[2^i] ⊗ A_i = H⁰(K_v, M_i)`. The
finite-level subcomplex has the same `H⁰` and the same image in `H¹` (the theorems here), and no
cohomology above degree one. The two identifications used in this comparison — `H^j(K_v,
B[2^i] ⊗ A_i) = H^j(K_v, B[2^i]) ⊗ A_i` and the injectivity of `(B(F)/2^i) ⊗ A_i → H¹(K_v,
B[2^i]) ⊗ A_i` — both follow from `A_i ≅ (ℤ/2^i)^i` as a `ℤ/2^i`-module (basis `1, t, …, t^{i−1}`)
and the additivity of cohomology in finite direct sums; they are not formalized here and no
statement of this file depends on them.

Kinds: PROVED (the comparison with the derived object is commentary, not a hypothesis).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open CategoryTheory NumberField IsDedekindDomain ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

/-! ### The image of `H¹` of a cocycle condition -/

section Generic

universe u

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M]
  [SMulCommClass G k M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M]
  [ContinuousSMul G M]
  (Z : Submodule k (contCochain k G M 1)) (hZ : ∀ z ∈ Z, contD k G M 1 z = 0)

/-- PROVED (tex 3417–3418: "Its Kummer image"). **The image of `H¹(U) → H¹(C^•_cont(G, M))`** for
lane RC28's cocycle condition `U = [C⁰ → Z ⊔ B¹]`: a class lies in the image iff it is the class
of a cocycle lying in `Z ⊔ B¹`. -/
theorem cocycleCondition_range_homologyMap_one
    (x : (natCx (contCochains k G M)).toCC.homology 1) :
    x ∈ Set.range (HomologicalComplex.homologyMap (GHom.toCC (cocycleConditionι Z hZ)) 1).hom ↔
      ∃ c : (natCx (contCochains k G M)).toCC.cycles 1,
        ((natCx (contCochains k G M)).toCC.iCycles 1).hom c ∈ Z ⊔ contB1 k G M ∧
        ((natCx (contCochains k G M)).toCC.homologyπ 1).hom c = x := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨y', rfl⟩ := (ModuleCat.epi_iff_surjective _).1
      (inferInstance : Epi (cocycleConditionH1Iso Z hZ).inv) y
    obtain ⟨x', rfl⟩ := Submodule.Quotient.mk_surjective (condB1 Z hZ) y'
    obtain ⟨c, hc1, hc2⟩ := cocycleCondition_homologyMap_inv_mk Z hZ x'
    exact ⟨c, hc1 ▸ (condOne Z hZ x').2, hc2.symm⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨c', hc1, hc2⟩ := cocycleCondition_homologyMap_inv_mk Z hZ
      (ofCondOne Z hZ ⟨_, hc⟩)
    have hcc : c' = c := by
      apply (ModuleCat.mono_iff_injective
        ((natCx (contCochains k G M)).toCC.iCycles 1)).1 inferInstance
      exact hc1
    exact ⟨_, hc2.trans (congrArg _ hcc)⟩

end Generic

/-! ### The extended Kummer cocycles are push-forwards of Kummer cocycles -/

/-- PROVED (tex 3417–3418, 3430–3432). The generator `g ↦ a • ι(κ_P(g))` of lane RC28's extended
Kummer submodule is `a` times the push-forward along `ι` of lane RC28's genuine Kummer cocycle
`κ_P` (`σ ↦ σQ − Q`, `m Q = P`). -/
theorem kummerCocycleIn_apply_eq {F : Type} [Field F] [CharZero F] [DecidableEq F]
    {B : WeierstrassCurve F} [B.IsElliptic] {m : ℕ} [NeZero m] {k : Type} [CommRing k]
    {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (Field.absoluteGaloisGroup F) M]
    [SMulCommClass (Field.absoluteGaloisGroup F) k M] [TopologicalSpace M] [DiscreteTopology M]
    (ι : TorsAlg F B m →+ M) (a : k) (P : B.toAffine.Point)
    (g : Fin 1 → Field.absoluteGaloisGroup F) :
    cfun (kummerCocycleIn ι a P) g = a • ι (cfun (kummerCocycle F B m P) g) :=
  rfl

/-! ### The local Kummer map with coefficients in `M` -/

section KummerMap

variable {F : Type} [Field F] [CharZero F] [DecidableEq F] {B : WeierstrassCurve F} [B.IsElliptic]
  {m : ℕ} [NeZero m] {k : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (Field.absoluteGaloisGroup F) M]
  (ι : TorsAlg F B m →+ M)
  (hι : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (σ • t) = σ • ι t)

include hι in
/-- PROVED (tex 3417–3418, pushed forward along `ι`). The extended Kummer cocycles are additive up
to a continuous coboundary: `ι∘κ_{P+P'} − ι∘κ_P − ι∘κ_{P'} = d⁰(ι T)`. -/
theorem kummerCocycleIn_add (P P' : B.toAffine.Point) :
    kummerCocycleIn ι (1 : k) (P + P') - kummerCocycleIn ι 1 P - kummerCocycleIn ι 1 P' ∈
      contB1 k (Field.absoluteGaloisGroup F) M := by
  have hT : divPt F B m (P + P') - divPt F B m P - divPt F B m P' ∈
      AddSubgroup.torsionBy (PtAlg F B) (m : ℤ) := by
    rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, nsmul_sub, nsmul_divPt, nsmul_divPt,
      nsmul_divPt, map_add, sub_sub, sub_self]
  refine (mem_contB1_iff _).2 ⟨constCochain (ι ⟨_, hT⟩), ?_⟩
  apply Subtype.ext
  funext g
  refine (cfun_contD_constCochain (k := k) (G := Field.absoluteGaloisGroup F) (M := M) _ g).trans ?_
  change _ = (1 : k) • ι (kummerFun F B m (P + P') (g 0)) - (1 : k) • ι (kummerFun F B m P (g 0)) -
    (1 : k) • ι (kummerFun F B m P' (g 0))
  rw [one_smul, one_smul, one_smul, ← hι, ← map_sub, ← map_sub, ← map_sub]
  congr 1
  apply Subtype.ext
  simp only [AddSubgroup.coe_sub, coe_smul_torsAlg, coe_kummerFun, smul_sub]
  abel

include hι in
/-- PROVED (tex 3417–3418, pushed forward along `ι`). The extended Kummer cocycle of a point of
`m B(F)` is a continuous coboundary. -/
theorem kummerCocycleIn_nsmul_mem (P' : B.toAffine.Point) :
    kummerCocycleIn ι (1 : k) (m • P') ∈ contB1 k (Field.absoluteGaloisGroup F) M := by
  have hT : divPt F B m (m • P') - basePt F B P' ∈ AddSubgroup.torsionBy (PtAlg F B) (m : ℤ) := by
    rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, nsmul_divPt, map_nsmul, sub_self]
  refine (mem_contB1_iff _).2 ⟨constCochain (ι ⟨_, hT⟩), ?_⟩
  apply Subtype.ext
  funext g
  refine (cfun_contD_constCochain (k := k) (G := Field.absoluteGaloisGroup F) (M := M) _ g).trans ?_
  change _ = (1 : k) • ι (kummerFun F B m (m • P') (g 0))
  rw [one_smul, ← hι, ← map_sub]
  congr 1
  apply Subtype.ext
  simp only [AddSubgroup.coe_sub, coe_smul_torsAlg, coe_kummerFun, smul_sub, smul_basePt]
  abel

variable (k)

/-- Definition (tex 3417–3418). The extended Kummer cocycle `ι∘κ_P` as an element of the
degree-one term `U¹ = kummerZ' ⊔ B¹` of the extended Kummer condition. -/
def kummerEltIn (P : B.toAffine.Point) : (kummerConditionIn k ι hι).X 1 :=
  ofCondOne (kummerZ' k ι) (kummerZ'_cocycle k ι hι)
    ⟨kummerCocycleIn ι 1 P, Submodule.mem_sup_left (kummerCocycleIn_mem ι 1 P)⟩

/-- Definition (tex 3417–3418, 3442–3445). **The Kummer map into `H¹` of the condition**,
`B(F) → U¹ ⧸ B¹`, `P ↦ [ι∘κ_P]`; additive by `kummerCocycleIn_add`. -/
def kummerQuotIn :
    B.toAffine.Point →+
      ((kummerConditionIn k ι hι).X 1 ⧸ condB1 (kummerZ' k ι) (kummerZ'_cocycle k ι hι)) :=
  AddMonoidHom.mk' (fun P => Submodule.Quotient.mk (kummerEltIn k ι hι P)) fun P P' => by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq, mem_condB1]
    have h := kummerCocycleIn_add (k := k) ι hι P P'
    rw [sub_sub] at h
    exact h

/-- Definition (tex 3417–3418, 3442–3445). **The local Kummer map with coefficients in `M`**,
`B(F) → H¹(C^•_cont(G_F, M))`, `P ↦ ι_*[κ_P]`: the class of the extended Kummer cocycle, through
`H¹` of the condition. -/
def kummerMapIn : B.toAffine.Point →+ (natCx (contCochains k (Field.absoluteGaloisGroup F) M)).toCC.homology 1 :=
  ((HomologicalComplex.homologyMap (GHom.toCC (kummerConditionInι k ι hι)) 1).hom.toAddMonoidHom.comp
    (kummerConditionInH1Iso k ι hι).inv.hom.toAddMonoidHom).comp (kummerQuotIn k ι hι)

/-- PROVED (tex 3415–3418). **The local Kummer map factors through `B(F)/mB(F)`**: it kills
`m B(F)`. -/
theorem kummerMapIn_nsmul (P' : B.toAffine.Point) : kummerMapIn k ι hι (m • P') = 0 := by
  have h : kummerQuotIn k ι hι (m • P') = 0 := by
    change Submodule.Quotient.mk (kummerEltIn k ι hι (m • P')) = 0
    rw [Submodule.Quotient.mk_eq_zero, mem_condB1]
    exact kummerCocycleIn_nsmul_mem ι hι P'
  change ((HomologicalComplex.homologyMap (GHom.toCC (kummerConditionInι k ι hι)) 1).hom
    ((kummerConditionInH1Iso k ι hι).inv.hom (kummerQuotIn k ι hι (m • P')))) = 0
  rw [h, map_zero, map_zero]

/-- PROVED (tex 3415–3418, 3430–3432). **The image of `H¹` of the extended Kummer condition is the
`k`-span of the image of the local Kummer map**: `range(H¹(U) → H¹(G_F, M)) =
span_k {ι_*[κ_P] : P ∈ B(F)}`. -/
theorem range_homologyMap_kummerConditionIn :
    LinearMap.range (HomologicalComplex.homologyMap (GHom.toCC (kummerConditionInι k ι hι)) 1).hom =
      Submodule.span k (Set.range (kummerMapIn k ι hι)) := by
  set Φ : (kummerConditionIn k ι hι).X 1 →ₗ[k]
      (natCx (contCochains k (Field.absoluteGaloisGroup F) M)).toCC.homology 1 :=
    (HomologicalComplex.homologyMap (GHom.toCC (kummerConditionInι k ι hι)) 1).hom ∘ₗ
      (kummerConditionInH1Iso k ι hι).inv.hom ∘ₗ
        (condB1 (kummerZ' k ι) (kummerZ'_cocycle k ι hι)).mkQ with hΦ
  have hΦP : ∀ P, Φ (kummerEltIn k ι hι P) = kummerMapIn k ι hι P := fun P => rfl
  have key : ∀ (z : contCochain k (Field.absoluteGaloisGroup F) M 1) (hz : z ∈ kummerZ' k ι),
      Φ (ofCondOne (kummerZ' k ι) (kummerZ'_cocycle k ι hι) ⟨z, Submodule.mem_sup_left hz⟩) ∈
        Submodule.span k (Set.range (kummerMapIn k ι hι)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨a, P⟩, rfl⟩ := hw
      have h1 : (ofCondOne (kummerZ' k ι) (kummerZ'_cocycle k ι hι)
          ⟨kummerCocycleIn ι a P, Submodule.mem_sup_left (Submodule.subset_span ⟨(a, P), rfl⟩)⟩) =
          a • kummerEltIn k ι hι P := by
        apply Subtype.ext
        exact kummerCocycleIn_eq_smul ι a P
      rw [h1, map_smul, hΦP]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨P, rfl⟩)
    | zero =>
      have h0 : (ofCondOne (kummerZ' k ι) (kummerZ'_cocycle k ι hι)
          ⟨0, Submodule.mem_sup_left (zero_mem _)⟩) = 0 := rfl
      rw [h0, map_zero]
      exact zero_mem _
    | add w w' hw hw' ihw ihw' =>
      have h2 : (ofCondOne (kummerZ' k ι) (kummerZ'_cocycle k ι hι)
          ⟨w + w', Submodule.mem_sup_left (add_mem hw hw')⟩) =
          ofCondOne (kummerZ' k ι) (kummerZ'_cocycle k ι hι) ⟨w, Submodule.mem_sup_left hw⟩ +
            ofCondOne (kummerZ' k ι) (kummerZ'_cocycle k ι hι) ⟨w', Submodule.mem_sup_left hw'⟩ :=
        rfl
      rw [h2, map_add]
      exact add_mem ihw ihw'
    | smul a w hw ihw =>
      have h3 : (ofCondOne (kummerZ' k ι) (kummerZ'_cocycle k ι hι)
          ⟨a • w, Submodule.mem_sup_left (Submodule.smul_mem _ a hw)⟩) =
          a • ofCondOne (kummerZ' k ι) (kummerZ'_cocycle k ι hι) ⟨w, Submodule.mem_sup_left hw⟩ :=
        rfl
      rw [h3, map_smul]
      exact Submodule.smul_mem _ a ihw
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    obtain ⟨y', rfl⟩ := (ModuleCat.epi_iff_surjective _).1
      (inferInstance : Epi (kummerConditionInH1Iso k ι hι).inv) y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y'
    change Φ x ∈ _
    obtain ⟨z, hz, b, hb, hzb⟩ := Submodule.mem_sup.1 (condOne (kummerZ' k ι)
      (kummerZ'_cocycle k ι hι) x).2
    have hx : Φ x = Φ (ofCondOne (kummerZ' k ι) (kummerZ'_cocycle k ι hι)
        ⟨z, Submodule.mem_sup_left hz⟩) := by
      simp only [hΦ, LinearMap.comp_apply, Submodule.mkQ_apply]
      congr 2
      rw [Submodule.Quotient.eq, mem_condB1]
      change (condOne (kummerZ' k ι) (kummerZ'_cocycle k ι hι) x :
          contCochain k (Field.absoluteGaloisGroup F) M 1) -
            (z : contCochain k (Field.absoluteGaloisGroup F) M 1) ∈
          contB1 k (Field.absoluteGaloisGroup F) M
      rw [← hzb, add_sub_cancel_left]
      exact hb
    rw [hx]
    exact key z hz
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨P, rfl⟩
    exact ⟨_, rfl⟩

end KummerMap

/-! ### The actual Kummer condition -/

section Actual

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α]
  (hFull : FullTorsion K S W (2 ^ i)) (v : Places K S)
  (hα : IsLocallyQuadAt i α (quadChar s hs hs0) v.1)

open scoped Classical in
/-- PROVED (tex 3415–3417, degree zero: "`B(F)[2^a]` in degree zero"). **The actual Kummer
condition has all of `H⁰(K_v, M_i)`**: the inclusion induces an isomorphism on `H⁰`. -/
theorem actualKummerAt_isIso_H0 :
    IsIso (HomologicalComplex.homologyMap
      (GHom.toCC (actualKummerAt W i s hs hs0 α hFull v hα).i) 0) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact kummerConditionIn_isIso_homologyMap_zero (Acoef i) (kummerIota W i s hs hs0 α hFull v.1)
    (kummerIota_smul W i s hs hs0 α hFull v.1 hα)

open scoped Classical in
/-- PROVED (tex 3415–3418, degree one). **The actual Kummer condition injects into
`H¹(K_v, M_i)`**. -/
theorem actualKummerAt_mono_H1 :
    Mono (HomologicalComplex.homologyMap
      (GHom.toCC (actualKummerAt W i s hs hs0 α hFull v hα).i) 1) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact cocycleCondition_mono_homologyMap_one _ _

open scoped Classical in
/-- PROVED (tex 3415–3418, 3430–3432: "`B(F)/2^aB(F)` in degree one", "derived coefficient
extension"). **The actual Kummer condition at `v`, in `H¹(K_v, M_i)`, is the image of the local
Kummer map of `B = E^{(h)}`, extended `A_i`-linearly**: a class `x ∈ H¹(K_v, M_i)` comes from
`H¹(U_v)` iff it is the class of a cocycle in
`span_{A_i}{g ↦ a • ι_v(κ_P(g)) : a ∈ A_i, P ∈ B(K_v)} + B¹`. -/
theorem actualKummerAt_range_H1
    (x : (locAt K S (Acoef i) (Mcoef K S W i α) v).toCC.homology 1) :
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    x ∈ Set.range (HomologicalComplex.homologyMap
      (GHom.toCC (actualKummerAt W i s hs hs0 α hFull v hα).i) 1).hom ↔
      ∃ c : (locAt K S (Acoef i) (Mcoef K S W i α) v).toCC.cycles 1,
        ((locAt K S (Acoef i) (Mcoef K S W i α) v).toCC.iCycles 1).hom c ∈
          Submodule.span (Acoef i) (Set.range fun p : Acoef i × (localTwist W h v.1).toAffine.Point =>
            kummerCocycleIn (kummerIota W i s hs hs0 α hFull v.1) p.1 p.2) ⊔
          contB1 (Acoef i) (Gloc K v.1) (ResMod (locMap K S v.1) (Mcoef K S W i α)) ∧
        ((locAt K S (Acoef i) (Mcoef K S W i α) v).toCC.homologyπ 1).hom c = x := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact cocycleCondition_range_homologyMap_one _ _ x

open scoped Classical in
/-- Definition (tex 3413–3418, 3430–3432, 3442–3445). **The local Kummer map of the actual twist
`B = E^{(h)}` over `K_v`, with coefficients in `M_i`**: `B(K_v) → H¹(K_v, M_i)`,
`P ↦ ι_{v,*}[κ_P]` (`kummerMapIn` for the genuine `ι_v`). -/
def actualKummerMap :
    (localTwist W h v.1).toAffine.Point →+
      (locAt K S (Acoef i) (Mcoef K S W i α) v).toCC.homology 1 :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  kummerMapIn (Acoef i) (kummerIota W i s hs hs0 α hFull v.1)
    (kummerIota_smul W i s hs hs0 α hFull v.1 hα)

open scoped Classical in
/-- PROVED (tex 3415–3418). **The actual local Kummer map factors through `B(K_v)/2^iB(K_v)`**:
it kills `2^i B(K_v)`. -/
theorem actualKummerMap_nsmul (P' : (localTwist W h v.1).toAffine.Point) :
    actualKummerMap W i s hs hs0 α hFull v hα ((2 ^ i : ℕ) • P') = 0 := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact kummerMapIn_nsmul (Acoef i) (kummerIota W i s hs hs0 α hFull v.1)
    (kummerIota_smul W i s hs hs0 α hFull v.1 hα) P'

open scoped Classical in
/-- PROVED (tex 3415–3418, 3430–3432: "`B(F)/2^aB(F)` in degree one", "derived coefficient
extension defines the scalar `A_i` condition"). **The actual Kummer local condition at `v` is the
image of the local Kummer map `E^{(h)}(K_v)/2^i → H¹(K_v, M_i)`, extended `A_i`-linearly**: the
image of `H¹(U_v) → H¹(K_v, M_i)` is the `A_i`-span of `{ι_{v,*}[κ_P] : P ∈ B(K_v)}` (and the map
is injective, `actualKummerAt_mono_H1`). -/
theorem actualKummerAt_range_eq_span :
    LinearMap.range (HomologicalComplex.homologyMap
      (GHom.toCC (actualKummerAt W i s hs hs0 α hFull v hα).i) 1).hom =
      Submodule.span (Acoef i) (Set.range (actualKummerMap W i s hs hs0 α hFull v hα)) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact range_homologyMap_kummerConditionIn (Acoef i) (kummerIota W i s hs hs0 α hFull v.1)
    (kummerIota_smul W i s hs hs0 α hFull v.1 hα)

end Actual

end ZInQ.Manuscript.RC.KummerMaps

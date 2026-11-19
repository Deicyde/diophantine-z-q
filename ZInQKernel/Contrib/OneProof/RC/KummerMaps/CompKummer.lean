import ZInQKernel.Contrib.OneProof.RC.KummerMaps.CompSep
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TauCetiComparison
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.CupOne

/-!
# Lane RC29, round 2 (comparison, part 2): the Kummer image is its exact local annihilator

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-local-kummer` (tex 3413–3468): "Its Kummer image
is its exact local annihilator" (tex 3423), proved at tex 3442–3445:

> The local finite dualities [Milne, I.2.3, I.3.2–I.3.5] make the Kummer map adjoint to
> `H¹(F, B[2^a]) → H¹(F, B)[2^a]`. The latter has Kummer image as kernel, so the Kummer image is
> its exact annihilator.

The other group proved this (`kummerAnnihilatorNodeCharZero_of_print`) from its PRINT
`MilneLocalTateDualityKummerCharZero` (Milne, *Arithmetic Duality Theorems*, 2nd ed., Ch. I,
Cor. 2.3, Thm. 3.2 and its proof, Cor. 3.4, Rem. 3.5), in the cohomology of `Gal(Fˢ/F)` with
coefficients over the separable closure, for the pairing `⟨x, y⟩ = inv_F(x ∪_{e_m} y)` with values
in `ℚ/ℤ`. This file derives from the same print the statement in the genuine continuous cochains
of lanes RC26 and RC28 (`contCochains`, `TorsAlg`, `kummerCocycle`, `contCup`), over
`G_F = Gal(F̄/F)`, and **without the trace** `inv_F ∘ (H²(F, μ_m) → Br F)`:

* `compKummerAnnihilator`: for a continuous `1`-cocycle `y ∈ C¹_cont(G_F, B(F̄)[m])`,
  `y` is a Kummer cocycle `κ_P` modulo coboundaries **iff** for every `P ∈ B(F)` the local cup
  product `κ_P ∪_{e_m} y ∈ C²_cont(G_F, μ_m(F̄))` (lane RC26's `contCup` for the Weil pairing
  `compWeil`) is a coboundary.
* `compKummerAnnihilator_adicCompletion`: the same for `F = K_v` (a finite place of a number field
  `K`), any elliptic curve `B` over `K_v` and `m = 2^i`.
* `compKummerIsotropic`: the Kummer cocycles are pairwise isotropic.

Steps (each PROVED):
* transport of `B¹` and `B²` along an isomorphism of a group and an equivariant isomorphism of
  coefficients (`compMem_B1_iff`, `compMem_B2_iff`), and between the cochains of lane RC26 and the
  explicit `B¹`, `B²` of the other group (`compMem_contB1_iff`, `compMem_range_d12_iff`);
* the cocycle `compCocycle y` of `Gal(Fˢ/F)` attached to `y`, and the other group's Kummer
  cocycle for the division point `compDivPt P = e⁻¹(divPt P)` (`compSepTors_kummerCocycle`: it is
  lane RC28's `kummerFun` after transport);
* `compKummerToBr_injective`: **`H²(F, μ_m) → Br F` is injective** (the long exact sequence of
  `1 → μ_m → (Fˢ)ˣ → (Fˢ)ˣ → 1` at `H²(F, μ_m)`, the other group's `explicitLongExact_H2A`, and
  Hilbert 90, `subsingleton_H1_unitsCoeff`), so `inv_F(x ∪ y) = 0 ↔ x ∪ y = 0`
  (`compLocalTatePairing_eq_zero_iff`).

DEPARTURE (form): the text works with `H¹(F, B[2^a])`; here a class is a continuous cocycle of
`C^•_cont(G_F, B(F̄)[m])` up to coboundaries, the Kummer image is the set of Kummer cocycles
`κ_P` (lane RC28's `kummerCocycle`, `σ ↦ σQ − Q`) up to coboundaries, and "orthogonal to the
Kummer image" is "the cup product with every `κ_P` is a coboundary", the pairing being taken in
`H²(F, μ_m)` instead of `ℚ/ℤ`; the two forms agree because `inv_F` is an isomorphism and
`H²(F, μ_m) → Br F` is injective (proved here). `m` is any positive integer (the text: `m = 2^a`).
The only hypothesis beyond the field data is the PRINT of the other group, unchanged.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory ZInQ.Manuscript.RC.CoefModules
  ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.Duality (MilneLocalTateDualityKummerCharZero
  kummerAnnihilatorNodeCharZero_of_print localTatePairing localWeilCup kummerToBr cupH cupZ
  cupH_mk coe_cupZ)

/-! ### Transport of coboundaries along isomorphisms -/

section Transport

variable {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  {M N : Type} [AddCommGroup M] [AddCommGroup N] [DistribMulAction G M] [DistribMulAction H N]

omit [TopologicalSpace G] [TopologicalSpace H] in
/-- PROVED. Membership in the other group's `B¹`: `a = d⁰ t` for some `t`. -/
theorem compMem_B1_iff_exists {a : G → M} : a ∈ B1 G M ↔ ∃ t : M, ∀ g : G, g • t - t = a g := by
  rw [B1, AddMonoidHom.mem_range]
  exact exists_congr fun t => funext_iff

/-- PROVED. **`B¹` transports along an isomorphism of groups `φ : H ≃ G` and an equivariant
isomorphism of coefficients `f : M ≃ N`** (`f (φ h • x) = h • f x`). -/
theorem compMem_B1_iff (φ : H ≃ₜ* G) (f : M ≃+ N) (hf : ∀ (h : H) (x : M), f (φ h • x) = h • f x)
    (a : G → M) : a ∈ B1 G M ↔ (fun h : H => f (a (φ h))) ∈ B1 H N := by
  rw [compMem_B1_iff_exists, compMem_B1_iff_exists]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨f t, fun h => by rw [← hf, ← map_sub, ht]⟩
  · rintro ⟨s, hs⟩
    refine ⟨f.symm s, fun g => ?_⟩
    have h1 := hs (φ.symm g)
    rw [ContinuousMulEquiv.apply_symm_apply] at h1
    have h2 := hf (φ.symm g) (f.symm s)
    rw [ContinuousMulEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h2
    apply f.injective
    rw [map_sub, h2, AddEquiv.apply_symm_apply, h1]

variable [TopologicalSpace M] [TopologicalSpace N] [DiscreteTopology M] [DiscreteTopology N]
  [IsTopologicalAddGroup M] [IsTopologicalAddGroup N]

/-- PROVED. **`B²` transports along an isomorphism of topological groups `φ : H ≃ G` and an
equivariant isomorphism of discrete coefficients `f : M ≃ N`.** -/
theorem compMem_B2_iff (φ : H ≃ₜ* G) (f : M ≃+ N)
    (hf : ∀ (h : H) (x : M), f (φ h • x) = h • f x) (c : G × G → M) :
    c ∈ B2 G M ↔ (fun p : H × H => f (c (φ p.1, φ p.2))) ∈ B2 H N := by
  rw [mem_B2_iff', mem_B2_iff']
  constructor
  · rintro ⟨u, hu, huc⟩
    refine ⟨fun h => f (u (φ h)),
      continuous_of_discreteTopology.comp (hu.comp φ.continuous_toFun), fun g h => ?_⟩
    rw [← hf, ← map_sub, ← map_add, map_mul, huc]
  · rintro ⟨v, hv, hvc⟩
    refine ⟨fun g => f.symm (v (φ.symm g)),
      continuous_of_discreteTopology.comp (hv.comp φ.symm.continuous_toFun), fun g h => ?_⟩
    have h1 := hvc (φ.symm g) (φ.symm h)
    rw [ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply] at h1
    have h2 := hf (φ.symm g) (f.symm (v (φ.symm h)))
    rw [ContinuousMulEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h2
    apply f.injective
    rw [map_add, map_sub, h2, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, map_mul, h1]

end Transport

/-! ### The cochains of lane RC26 against the explicit `B¹`, `B²` -/

section Cochains

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [DistribMulAction G M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M]

/-- PROVED. **A continuous `1`-cochain lies in `B¹_cont` (lane RC28's `contB1`) iff, read on `G`,
it lies in the other group's `B¹`.** -/
theorem compMem_contB1_iff (b : contCochain ℤ G M 1) :
    b ∈ contB1 ℤ G M ↔ (fun g : G => cfun b (fun _ => g)) ∈ B1 G M := by
  rw [compMem_B1_iff_exists, mem_contB1_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨cfun c default, fun g => (contD_zero_apply c (fun _ => g)).symm⟩
  · rintro ⟨t, ht⟩
    refine ⟨constCochain t, Subtype.ext (funext fun v => ?_)⟩
    have hv : v = fun _ => v 0 := funext fun i => congrArg v (Subsingleton.elim (α := Fin 1) i 0)
    change cfun (contD ℤ G M 0 (constCochain t)) v = cfun b v
    rw [cfun_contD_constCochain, ht (v 0), ← hv]

/-- PROVED. **A continuous `2`-cochain is the image of a continuous `1`-cochain under the degree-one
differential of `C^•_cont(G, M)` iff, read on `G × G`, it lies in the other group's `B²`.** -/
theorem compMem_range_d12_iff (b : (contCochains ℤ G M).X 2) :
    b ∈ LinearMap.range ((contCochains ℤ G M).d 1 2).hom ↔
      (fun p : G × G => contFun b ![p.1, p.2]) ∈ B2 G M := by
  rw [mem_B2_iff', LinearMap.mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun g => contFun c (fun _ => g), continuous_contFun_one c,
      fun g h => (contFun_d12 c g h).symm⟩
  · rintro ⟨u, hu, hub⟩
    refine ⟨mkCochain1 u hu, contCochains_ext fun v => ?_⟩
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv, contFun_d12]
    simp only [contFun_mkCochain1]
    exact hub (v 0) (v 1)

/-- PROVED. **The local cup product of two `1`-cochains** (lane RC26's `contCup`, the formula
`(a ∪ b)(g, h) = β(a(g), g • b(h))`). -/
theorem compContFun_contCup {A A' T : Type} [AddCommGroup A] [DistribMulAction G A]
    [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul G A]
    [AddCommGroup A'] [DistribMulAction G A'] [TopologicalSpace A'] [DiscreteTopology A']
    [ContinuousSMul G A'] [AddCommGroup T] [DistribMulAction G T] [TopologicalSpace T]
    [DiscreteTopology T] [ContinuousSMul G T] (β : A →ₗ[ℤ] A' →ₗ[ℤ] T)
    (hβc : Continuous fun x : A × A' => β x.1 x.2) (a : (contCochains ℤ G A).X 1)
    (b : (contCochains ℤ G A').X 1) (g h : G) :
    contFun (contCup β hβc 1 1 2 rfl a b) ![g, h] =
      β (contFun a (fun _ => g)) (g • contFun b (fun _ => h)) :=
  cupFun_one_one_apply β _ _ ![g, h]

end Cochains

/-! ### The Kummer cocycles and the transported cocycle -/

section Cocycle

variable (F : Type) [Field F]

/-- Definition. `compGal⁻¹ : Gal(Fˢ/F) → G_F` as a continuous homomorphism. -/
def compGalSymmHom : AbsoluteGaloisGroup F →ₜ* Field.absoluteGaloisGroup F :=
  { toMonoidHom := (compGal F).symm.toMulEquiv.toMonoidHom
    continuous_toFun := (compGal F).symm.continuous_toFun }

/-- PROVED. `compGalSymmHom` is `compGal⁻¹`. -/
theorem compGalSymmHom_apply (τ : AbsoluteGaloisGroup F) :
    compGalSymmHom F τ = (compGal F).symm τ :=
  rfl

variable [CharZero F] (B : WeierstrassCurve F) (m : ℕ)

/-- Definition. **The cocycle of `Gal(Fˢ/F)` attached to a continuous `1`-cocycle `y` of `G_F`
with values in `B(F̄)[m]`**: `τ ↦ e⁻¹(y(compGal⁻¹ τ))`, the other group's pullback `cocyclesMap1`
along `(compGal⁻¹, compSepTors⁻¹)`. -/
def compCocycle (y : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1)
    (hy : contD ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 y = 0) :
    Z1 (AbsoluteGaloisGroup F) (B.TorsionCoeff m) :=
  cocyclesMap1 (Field.absoluteGaloisGroup F) (TorsAlg F B m) (AbsoluteGaloisGroup F)
    (B.TorsionCoeff m) (compGalSymmHom F) (compSepTors F B m).symm.toAddMonoidHom
    continuous_of_discreteTopology (compSepTors_symm_smul_symm F B m)
    ⟨fun g => cfun y (fun _ => g), mem_Z1_of_d_eq_zero y hy⟩

/-- PROVED. The values of `compCocycle y`. -/
theorem compCocycle_apply (y : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1)
    (hy : contD ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 y = 0)
    (τ : AbsoluteGaloisGroup F) :
    (compCocycle F B m y hy : AbsoluteGaloisGroup F → B.TorsionCoeff m) τ =
      (compSepTors F B m).symm (cfun y (fun _ => (compGal F).symm τ)) :=
  rfl

end Cocycle

section Kummer

variable (F : Type) [Field F] [DecidableEq F] [CharZero F] (B : WeierstrassCurve F)
  [B.IsElliptic] (m : ℕ) [NeZero m]

/-- Definition. The division point `e⁻¹(Q) ∈ B(Fˢ)` of `P`, for lane RC28's chosen division point
`Q = divPt P ∈ B(F̄)`. -/
def compDivPt (P : B.toAffine.Point) : B.PointCoeff :=
  (compSepPt F B).symm (divPt F B m P)

/-- PROVED. `m • e⁻¹(Q) = P` in `B(Fˢ)`. -/
theorem nsmul_compDivPt (P : B.toAffine.Point) : m • compDivPt F B m P = B.basePointCoeff P := by
  apply (compSepPt F B).injective
  rw [map_nsmul, compDivPt, AddEquiv.apply_symm_apply, nsmul_divPt, compSepPt_apply,
    compSepPtHom_basePointCoeff]

/-- PROVED. **The other group's Kummer cocycle `τ ↦ τ e⁻¹(Q) − e⁻¹(Q)`, transported to `G_F` and
`B(F̄)[m]`, is lane RC28's Kummer function `σ ↦ σ Q − Q`.** -/
theorem compSepTors_kummerCocycle (P : B.toAffine.Point) (σ : Field.absoluteGaloisGroup F) :
    compSepTors F B m (WeierstrassCurve.kummerCocycle (nsmul_compDivPt F B m P) (compGal F σ)) =
      kummerFun F B m P σ := by
  apply Subtype.ext
  rw [coe_compSepTors, coe_kummerFun, WeierstrassCurve.coe_kummerCocycle, map_sub, compSepPt_smul,
    compDivPt, AddEquiv.apply_symm_apply]

/-- PROVED. The other group's Kummer class of `P` (`WeierstrassCurve.kummerMap`) is the class of
its Kummer cocycle for the division point `e⁻¹(Q)` (the other group's `kummerMap_eq_H1pi`). -/
theorem compKummerMap_eq (hm : IsUnit (m : F)) (P : B.toAffine.Point) :
    B.kummerMap m hm P = H1pi (AbsoluteGaloisGroup F) (B.TorsionCoeff m)
      ⟨WeierstrassCurve.kummerCocycle (nsmul_compDivPt F B m P),
        WeierstrassCurve.kummerCocycle_mem_Z1 (nsmul_compDivPt F B m P)⟩ :=
  WeierstrassCurve.kummerMap_eq_H1pi hm (nsmul_compDivPt F B m P)

/-- PROVED. **`y − κ_P` is a continuous coboundary iff the transported class of `y` is the other
group's Kummer class of `P`.** -/
theorem compKummer_sub_mem_iff (hm : IsUnit (m : F))
    (y : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1)
    (hy : contD ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 y = 0) (P : B.toAffine.Point) :
    y - kummerCocycle F B m P ∈ contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) ↔
      B.kummerMap m hm P = H1pi (AbsoluteGaloisGroup F) (B.TorsionCoeff m)
        (compCocycle F B m y hy) := by
  rw [compKummerMap_eq F B m hm P, eq_comm, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.mk'_apply, H1pi_eq_iff, compMem_contB1_iff,
    compMem_B1_iff (compGal F) (compSepTors F B m) (compSepTors_smul F B m)]
  refine Iff.of_eq (congrArg (· ∈ B1 (Field.absoluteGaloisGroup F) (TorsAlg F B m))
    (funext fun g => ?_))
  rw [Pi.sub_apply, map_sub, compCocycle_apply, ContinuousMulEquiv.symm_apply_apply,
    AddEquiv.apply_symm_apply]
  change cfun y (fun _ => g) - kummerFun F B m P g = cfun y (fun _ => g) -
    compSepTors F B m (WeierstrassCurve.kummerCocycle (nsmul_compDivPt F B m P) (compGal F g))
  rw [compSepTors_kummerCocycle]

end Kummer

/-! ### `H²(F, μ_m) → Br F` is injective: the pairing without the trace -/

section Trace

variable (F : Type) [Field F] (m : ℕ)

/-- PROVED. **`H²(F, μ_m) → H²(F, (Fˢ)ˣ) = Br F` is injective** for `m` invertible in `F`: by
the long exact sequence of the Kummer sequence `1 → μ_m → (Fˢ)ˣ → (Fˢ)ˣ → 1` its kernel is the
image of `H¹(F, (Fˢ)ˣ)`, which vanishes by Hilbert 90 (the other group's `explicitLongExact_H2A`,
`kummerShortExact_inclDistribMulActionHom` and `subsingleton_H1_unitsCoeff`). -/
theorem compKummerToBr_injective (hm : IsUnit (m : F)) :
    Function.Injective (kummerToBr (F := F) m) := by
  have h1 : Function.Injective (explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F m)
      (kummerCoeffInclHom F m) continuous_of_discreteTopology) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hseq := (TauCeti.kummerShortExact F m hm).explicitLongExact_H2A
    rw [TauCeti.kummerShortExact_inclDistribMulActionHom] at hseq
    have hmem : x ∈ (TauCeti.kummerShortExact F m hm).explicitDelta1.range := by
      rw [hseq]
      exact hx
    obtain ⟨z, rfl⟩ := hmem
    rw [Subsingleton.elim z 0, map_zero]
  exact (unitsRepH2Equiv F).injective.comp h1

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (B : WeierstrassCurve F) [B.IsElliptic]

/-- PROVED. **The local Tate pairing vanishes iff the cup product does**:
`inv_F(x ∪_{e_m} y) = 0 ↔ x ∪_{e_m} y = 0` in `H²(F, μ_m)` (`inv_F` is an isomorphism and
`H²(F, μ_m) → Br F` is injective). -/
theorem compLocalTatePairing_eq_zero_iff (hm : IsUnit (m : F))
    (x y : H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff m)) :
    localTatePairing B m hm x y = 0 ↔ localWeilCup B m hm x y = 0 := by
  change invMap F (kummerToBr m (localWeilCup B m hm x y)) = 0 ↔ _
  rw [AddEquiv.map_eq_zero_iff]
  exact (injective_iff_map_eq_zero' _).1 (compKummerToBr_injective F m hm) _

end Trace

/-! ### The cup product with a Kummer cocycle -/

section Cup

variable (F : Type) [Field F] [DecidableEq F] [CharZero F] (B : WeierstrassCurve F)
  [B.IsElliptic] (m : ℕ) [NeZero m]

/-- PROVED. **The local cup product `κ_P ∪_{e_m} y` is a continuous coboundary iff the other
group's cup product of the Kummer class of `P` with the transported class of `y` vanishes in
`H²(F, μ_m)`.** -/
theorem compCup_mem_range_iff (hm : IsUnit (m : F))
    (y : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1)
    (hy : contD ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 y = 0) (P : B.toAffine.Point) :
    contCup (compWeil F B m) (compWeil_continuous F B m) 1 1 2 rfl (kummerCocycle F B m P) y ∈
        LinearMap.range ((contCochains ℤ (Field.absoluteGaloisGroup F) (MuAlg F m)).d 1 2).hom ↔
      localWeilCup B m hm (B.kummerMap m hm P)
        (H1pi (AbsoluteGaloisGroup F) (B.TorsionCoeff m) (compCocycle F B m y hy)) = 0 := by
  rw [compKummerMap_eq F B m hm P, localWeilCup, cupH_mk, QuotientAddGroup.mk'_apply,
    H2pi_eq_zero_iff, coe_cupZ, compMem_range_d12_iff,
    compMem_B2_iff (compGal F) (compMu F m) (compMu_smul F m)]
  refine Iff.of_eq (congrArg (· ∈ B2 (Field.absoluteGaloisGroup F) (MuAlg F m))
    (funext fun p => ?_))
  refine (compContFun_contCup (compWeil F B m) (compWeil_continuous F B m)
    (kummerCocycle F B m P) y p.1 p.2).trans ?_
  change compWeil F B m (kummerFun F B m P p.1) (p.1 • cfun y (fun _ => p.2)) =
    compMu F m (B.torsionCoeffWeilPairing m hm
      (WeierstrassCurve.kummerCocycle (nsmul_compDivPt F B m P) (compGal F p.1))
      (compGal F p.1 • (compCocycle F B m y hy : AbsoluteGaloisGroup F → B.TorsionCoeff m)
        (compGal F p.2)))
  rw [← compWeil_compTors F B m hm, compSepTors_kummerCocycle, compSepTors_smul, compCocycle_apply,
    ContinuousMulEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]

end Cup

/-! ### The exact local annihilator -/

/-- PROVED from the PRINT `MilneLocalTateDualityKummerCharZero` (the other group's; J. S. Milne,
*Arithmetic Duality Theorems*, 2nd ed., 2006, Ch. I: Cor. 2.3, p. 28; Thm. 3.2, p. 41, with the
commutative diagram of its proof, pp. 41–42; Cor. 3.4, p. 43; Rem. 3.5, p. 44; original hypotheses:
`K` a nonarchimedean local field with finite residue field, of characteristic zero, `A` an abelian
variety over `K`; read in the author's text, it matches the print up to `A^t = A` for an elliptic
curve and sign conventions, which the print's existential absorbs).
**The Kummer image is its exact local annihilator** (Lemma `ex:arith-local-kummer`, tex 3423,
3442–3445), in the genuine continuous cochains of lanes RC26 and RC28 and without the trace: for a
nonarchimedean local field `F` of characteristic zero, an elliptic curve `B/F`, `m ≥ 1` and a
continuous `1`-cocycle `y ∈ C¹_cont(G_F, B(F̄)[m])`, `y ≡ κ_P` modulo continuous coboundaries for
some `P ∈ B(F)` iff for every `P ∈ B(F)` the local cup product `κ_P ∪_{e_m} y` (lane RC26's
`contCup` for the Weil pairing over `F̄`) is a coboundary in `C²_cont(G_F, μ_m(F̄))`. -/
theorem compKummerAnnihilator (hM : MilneLocalTateDualityKummerCharZero)
    (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic] (m : ℕ) [NeZero m]
    (y : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1)
    (hy : contD ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 y = 0) :
    (∃ P : B.toAffine.Point,
        y - kummerCocycle F B m P ∈ contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m)) ↔
      ∀ P : B.toAffine.Point,
        contCup (compWeil F B m) (compWeil_continuous F B m) 1 1 2 rfl (kummerCocycle F B m P) y ∈
          LinearMap.range
            ((contCochains ℤ (Field.absoluteGaloisGroup F) (MuAlg F m)).d 1 2).hom := by
  have hm : IsUnit (m : F) := isUnit_iff_ne_zero.2 (natCast_ne_zero_of_charZero F m)
  have key := kummerAnnihilatorNodeCharZero_of_print hM F B m hm
    (H1pi (AbsoluteGaloisGroup F) (B.TorsionCoeff m) (compCocycle F B m y hy))
  rw [AddMonoidHom.mem_range] at key
  simp only [AddMonoidHom.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at key
  simp only [compKummer_sub_mem_iff F B m hm y hy, compCup_mem_range_iff F B m hm y hy,
    ← compLocalTatePairing_eq_zero_iff F m B hm]
  exact key

/-- PROVED from the PRINT. **The Kummer cocycles are pairwise isotropic**: `κ_P ∪_{e_m} κ_{P'}` is
a continuous coboundary for all `P, P' ∈ B(F)` (the case `y = κ_{P'}` of
`compKummerAnnihilator`; tex 3423, 3443–3448 "finite isotropy"). -/
theorem compKummerIsotropic (hM : MilneLocalTateDualityKummerCharZero)
    (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic] (m : ℕ) [NeZero m]
    (P P' : B.toAffine.Point) :
    contCup (compWeil F B m) (compWeil_continuous F B m) 1 1 2 rfl (kummerCocycle F B m P)
        (kummerCocycle F B m P') ∈
      LinearMap.range ((contCochains ℤ (Field.absoluteGaloisGroup F) (MuAlg F m)).d 1 2).hom :=
  (compKummerAnnihilator hM F B m (kummerCocycle F B m P') (kummerCocycle_isCocycle F B m P')).1
    ⟨P', by rw [sub_self]; exact zero_mem _⟩ P

/-- PROVED from the PRINT. **The exact local annihilator at a finite place of a number field**
(Lemma `ex:arith-local-kummer` for `F = K_v`, `m = 2^i`): for a number field `K`, a finite place
`v`, any elliptic curve `B` over `K_v` (in the text the actual local twist `E^{(h)}`) and
`i ∈ ℕ`, a continuous `1`-cocycle `y ∈ C¹_cont(G_{K_v}, B(K̄_v)[2^i])` is a Kummer cocycle modulo
coboundaries iff its cup products with all Kummer cocycles are coboundaries. `K_v` is a
nonarchimedean local field (the other group's `isNonarchimedeanLocalField_adicCompletion`, the
residue field of `v` being finite) of characteristic zero. -/
theorem compKummerAnnihilator_adicCompletion (hM : MilneLocalTateDualityKummerCharZero)
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [DecidableEq (v.adicCompletion K)] (B : WeierstrassCurve (v.adicCompletion K)) [B.IsElliptic]
    (i : ℕ)
    (y : contCochain ℤ (Field.absoluteGaloisGroup (v.adicCompletion K))
      (TorsAlg (v.adicCompletion K) B (2 ^ i)) 1)
    (hy : contD ℤ (Field.absoluteGaloisGroup (v.adicCompletion K))
      (TorsAlg (v.adicCompletion K) B (2 ^ i)) 1 y = 0) :
    (∃ P : B.toAffine.Point, y - kummerCocycle (v.adicCompletion K) B (2 ^ i) P ∈
        contB1 ℤ (Field.absoluteGaloisGroup (v.adicCompletion K))
          (TorsAlg (v.adicCompletion K) B (2 ^ i))) ↔
      ∀ P : B.toAffine.Point,
        contCup (compWeil (v.adicCompletion K) B (2 ^ i))
            (compWeil_continuous (v.adicCompletion K) B (2 ^ i)) 1 1 2 rfl
            (kummerCocycle (v.adicCompletion K) B (2 ^ i) P) y ∈
          LinearMap.range ((contCochains ℤ (Field.absoluteGaloisGroup (v.adicCompletion K))
            (MuAlg (v.adicCompletion K) (2 ^ i))).d 1 2).hom := by
  have : Finite (NumberField.RingOfIntegers K ⧸ v.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  exact compKummerAnnihilator hM (v.adicCompletion K) B (2 ^ i) y hy

end ZInQ.Manuscript.RC.KummerMaps

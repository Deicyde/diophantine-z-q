import ZInQKernel.Contrib.OneProof.RC.KummerMaps.CompKummer

/-!
# Lane RC29, round 2 (comparison, part 3): the Kummer condition is its own exact annihilator

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-local-kummer` (tex 3413–3468): "Its Kummer image
is its exact local annihilator, and the comparison has integral isotropy homotopies" (tex 3423),
with the proof at tex 3442–3448. Lane RC28's finite-level Kummer condition
`kummerCondition F B m` has degree-one term `U¹ = kummerZ F B m ⊔ B¹_cont`
(`cocycleCondition_X_one`), where `kummerZ F B m` is the `ℤ`-span of the Kummer cocycles `κ_P`.
This file restates `compKummerAnnihilator` (`CompKummer.lean`) for `U¹`:

* `compCup_coboundary_left`: `(d⁰ c) ∪ y = d¹(c ∪ y)` for a continuous `1`-cocycle `y` (lane RC26's
  Leibniz rule `contNatPair`), so a coboundary cupped with a cocycle is a coboundary;
* `compMem_kummerCondition_iff`: `y ∈ U¹` iff `y ≡ κ_P` modulo `B¹_cont` for some `P ∈ B(F)`
  (lane RC28's `exists_kummerToQuot_eq`);
* `compKummerCondition_annihilator`: **a continuous `1`-cocycle `y` lies in `U¹` iff `u ∪_{e_m} y`
  is a coboundary for every `u ∈ U¹`** (`U¹` is its own exact annihilator);
* `compKummerCondition_isotropic`: `u ∪_{e_m} u'` is a coboundary for all `u, u' ∈ U¹`.

Kinds: definitions and PROVED; the last two from the PRINT `MilneLocalTateDualityKummerCharZero`
of the other group (through `compKummerAnnihilator`), the first two unconditionally.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open TauCeti TauCeti.ContCohomology ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.Duality (MilneLocalTateDualityKummerCharZero)

section Cup

variable (F : Type) [Field F] [CharZero F] (B : WeierstrassCurve F) [B.IsElliptic] (m : ℕ)
  [NeZero m]

/-- Definition. The local cup product through the Weil pairing `e_m` over `F̄`, lane RC26's
`contCup (compWeil F B m) _ 1 1 2 rfl`, read as a bilinear map on `C¹_cont(G_F, B(F̄)[m])`. -/
def compCup : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 →ₗ[ℤ]
    contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 →ₗ[ℤ]
      (contCochains ℤ (Field.absoluteGaloisGroup F) (MuAlg F m)).X 2 :=
  contCup (compWeil F B m) (compWeil_continuous F B m) 1 1 2 rfl

/-- PROVED. `compCup` is lane RC26's `contCup`. -/
theorem compCup_apply (u y : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1) :
    compCup F B m u y = contCup (compWeil F B m) (compWeil_continuous F B m) 1 1 2 rfl u y :=
  rfl

/-- PROVED. **A coboundary cupped with a cocycle is a coboundary**: `(d⁰ c) ∪ y = d¹(c ∪ y)` for a
continuous `1`-cocycle `y` (lane RC26's Leibniz rule for `contCup`, `contNatPair`, with the
equivariance `compWeil_smul`). -/
theorem compCup_coboundary_left
    (c : (contCochains ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m)).X 0)
    (y : (contCochains ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m)).X 1)
    (hy : ((contCochains ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m)).d 1 2).hom y = 0) :
    contCup (compWeil F B m) (compWeil_continuous F B m) 1 1 2 rfl
        (((contCochains ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m)).d 0 1).hom c) y ∈
      LinearMap.range ((contCochains ℤ (Field.absoluteGaloisGroup F) (MuAlg F m)).d 1 2).hom := by
  refine ⟨contCup (compWeil F B m) (compWeil_continuous F B m) 0 1 1 rfl c y, ?_⟩
  have h := (contNatPair (compWeil F B m) (compWeil_smul F B m)
    (compWeil_continuous F B m)).leib 0 1 1 rfl c y
  have hy' : ((contCochains ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m)).d 1 (1 + 1)).hom y =
      0 := hy
  rw [hy', map_zero] at h
  simp only [zsmul_zero, add_zero] at h
  exact h

variable [DecidableEq F]

/-- PROVED. **`y ∈ U¹ = kummerZ ⊔ B¹_cont` iff `y ≡ κ_P` modulo `B¹_cont` for some `P ∈ B(F)`**
(lane RC28's `exists_kummerToQuot_eq`: every element of `kummerZ` is congruent to one `κ_P`). -/
theorem compMem_kummerCondition_iff
    (y : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1) :
    y ∈ kummerZ F B m ⊔ contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) ↔
      ∃ P : B.toAffine.Point,
        y - kummerCocycle F B m P ∈ contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) := by
  constructor
  · intro hy
    obtain ⟨z, hz, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨P, hP⟩ := exists_kummerToQuot_eq F B m z hz
    rw [kummerToQuot_apply, Submodule.Quotient.eq] at hP
    refine ⟨P, ?_⟩
    have e : z + b - kummerCocycle F B m P = b - (kummerCocycle F B m P - z) := by abel
    rw [e]
    exact sub_mem hb hP
  · rintro ⟨P, hP⟩
    have e : y = kummerCocycle F B m P + (y - kummerCocycle F B m P) := by abel
    rw [e]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨P, rfl⟩) hP

end Cup

/-- PROVED from the PRINT `MilneLocalTateDualityKummerCharZero` (through `compKummerAnnihilator`).
**Lane RC28's Kummer condition is its own exact local annihilator** (Lemma `ex:arith-local-kummer`,
tex 3423): for a nonarchimedean local field `F` of characteristic zero, an elliptic curve `B/F`,
`m ≥ 1`, and a continuous `1`-cocycle `y ∈ C¹_cont(G_F, B(F̄)[m])`, `y` lies in
`U¹ = kummerZ ⊔ B¹_cont` iff `u ∪_{e_m} y` is a coboundary in `C²_cont(G_F, μ_m(F̄))` for every
`u ∈ U¹`. -/
theorem compKummerCondition_annihilator (hM : MilneLocalTateDualityKummerCharZero)
    (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic] (m : ℕ) [NeZero m]
    (y : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1)
    (hy : contD ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 y = 0) :
    y ∈ kummerZ F B m ⊔ contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) ↔
      ∀ u ∈ kummerZ F B m ⊔ contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m),
        contCup (compWeil F B m) (compWeil_continuous F B m) 1 1 2 rfl u y ∈
          LinearMap.range
            ((contCochains ℤ (Field.absoluteGaloisGroup F) (MuAlg F m)).d 1 2).hom := by
  rw [compMem_kummerCondition_iff F B m y, compKummerAnnihilator hM F B m y hy]
  constructor
  · intro h u hu
    change compCup F B m u y ∈ _
    obtain ⟨z, hz, b, hb, rfl⟩ := Submodule.mem_sup.1 hu
    clear hu
    rw [map_add, LinearMap.add_apply]
    refine add_mem ?_ ?_
    · induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨P, rfl⟩ := hx
        exact h P
      | zero =>
        rw [map_zero, LinearMap.zero_apply]
        exact zero_mem _
      | add x x' _ _ hx hx' =>
        rw [map_add, LinearMap.add_apply]
        exact add_mem hx hx'
      | smul a x _ hx =>
        rw [map_smul]
        exact Submodule.smul_mem _ a hx
    · obtain ⟨c, rfl⟩ := (mem_contB1_iff b).1 hb
      exact compCup_coboundary_left F B m c y hy
  · intro h P
    exact h _ (Submodule.mem_sup_left (Submodule.subset_span ⟨P, rfl⟩))

/-- PROVED from the PRINT (through `compKummerCondition_annihilator`). **Isotropy of the Kummer
condition**: `u ∪_{e_m} u'` is a coboundary in `C²_cont(G_F, μ_m(F̄))` for all `u, u' ∈ U¹`
(tex 3423, 3443–3448: "finite isotropy"). -/
theorem compKummerCondition_isotropic (hM : MilneLocalTateDualityKummerCharZero)
    (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic] (m : ℕ) [NeZero m]
    (u u' : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1)
    (hu : u ∈ kummerZ F B m ⊔ contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m))
    (hu' : u' ∈ kummerZ F B m ⊔ contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m)) :
    contCup (compWeil F B m) (compWeil_continuous F B m) 1 1 2 rfl u u' ∈
      LinearMap.range ((contCochains ℤ (Field.absoluteGaloisGroup F) (MuAlg F m)).d 1 2).hom := by
  have hcoc : contD ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 u' = 0 := by
    obtain ⟨z, hz, b, hb, rfl⟩ := Submodule.mem_sup.1 hu'
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.1 hb
    rw [map_add, kummerZ_cocycle F B m z hz, contD_contD 0 c, add_zero]
  exact (compKummerCondition_annihilator hM F B m u' hcoc).1 hu' u hu

end ZInQ.Manuscript.RC.KummerMaps

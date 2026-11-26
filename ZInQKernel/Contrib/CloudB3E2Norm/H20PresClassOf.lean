import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClass
import ZInQKernel.Contrib.CloudB3E2Norm.DivisionPointsF

/-!
# Actual points from points over a finite extension

Manuscript `diophantine_zq.tex`, tex 3080–3084, 3203–3215, 3251–3290, 3293–3295, 3471–3487.

`H20PresClass.ActualPoint` packages, for a support `T`, the transfer subgroup, the point and a
division point, and the local inputs. This file **constructs** it from a point over a finite
normal extension:

* `ptCoordField` (definition): the field generated over `L` by the coordinates of a point;
  `divV` (definition): the fixing subgroup of its normal closure, pulled back to `G_{K,S}` — an
  open normal subgroup fixing the point (`divV_isOpen`, `divV_fixes`, PROVED).
* `fixH L` (definition): the kernel of `G_{K,S} → Gal(L/K)` for a finite normal `L ⊆ K_{S''}`
  (the transfer subgroup `G_L`); `mem_fixH` (PROVED).
* **`ActualPoint.ofField`** (definition): the actual point `1 ⊗ P` of a support `T`, for `P`, `Q`
  points of `E(K_{S''})` with `2^i Q = P`, `P` fixed by `G_L`, `S'' ⊆ S₁` not containing the places
  off `T`: the transfer subgroup `G_L` (its finite index from `Gal(L/K)`), the open normal
  subgroup `divV`, the old-place inputs from `PsiTrivialAt2N` (`hin_of_point`), `hunr` from the
  inflation to `G_{K,S''}` (`infl_inertiaImage`) and `hQin` from `inertiaFixes_of_support`. The one
  remaining input is `hα`: `χ_h [π]` is trivial on `G_L` (for the text: the field of the character
  `χ_h Ψ` lies in `L = H_{d_T}`).
* `heegnerL d` (definition): `H_d` inside `K_{S''}` (normal, finite); `mem_heegnerL_iff`
  (PROVED, from the full anchor): `z ∈ H_d ↔ κ⁻¹ z ∈ D.H d`; `coords_realize_mem`,
  `realize_fixed` (PROVED): the realized Heegner point `P_d ∈ E(K_{S''})` has coordinates in `H_d`
  and is fixed by `G_{H_d}`; `exists_div_realize` (PROVED): a `2^i`-division point of `P_d` in
  `E(K_{S''})` (`DivisionPointsF.exists_supportPoint_ringClassField`: good reduction outside
  `S''`, `S''` containing the places above `2` and the primes of `d`); `ptMap_realize` (PROVED):
  the realization is compatible with `S'' ⊆ S₁`; `mem_fixH_heegnerL` (PROVED): `G_{H_d}` described
  through `K_{S₁}`.
* **`heegnerActual`** (definition): the actual Heegner point of conductor `d` on a support, built
  with `ActualPoint.ofField` from the anchored datum.
* **`gx_step_heegner`** gives the step identity `g_R = pointFactor a_q z z⁻¹ · g_T + d b` for the
  classes of the constructed actual Heegner points `heegnerActual … d`, `heegnerActual … (dq)` at the place over the anchor's prime
  `𝔮 ∣ q`. The other inputs are the support sets (`S_T, S_R ⊆ S₁`, primes of `d`/`dq` and of
  `2`, good reduction outside, no place off the support) and the triviality `hα` of
  `χ_h [π]` on `G_{H_d}`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps ZInQ.Manuscript.RC.Limits
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.Central (pointFactor)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open NumberField IsDedekindDomain TensorProduct WeierstrassCurve

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass groupRingTop ptSAction

set_option linter.unusedSectionVars false

/-! ### Fixing subgroups pulled back to `G_{K,S}` -/

section Fix

variable {K : Type} [Field K] [NumberField K] {S S'' : Set (HeightOneSpectrum (𝓞 K))}
  (h2 : S'' ⊆ S)

/-- **The transfer subgroup `G_L`**: the kernel of `G_{K,S} → G_{K,S''} → Gal(L/K)` for a normal
`L ⊆ K_{S''}`. Kind: definition. -/
def fixH (L : IntermediateField K (KS K S'')) [Normal K L] : Subgroup (GKS K S) :=
  ((AlgEquiv.restrictNormalHom L).comp
    (show GKS K S →* (KS K S'' ≃ₐ[K] KS K S'') from (inflMap K h2).toMonoidHom)).ker

instance (L : IntermediateField K (KS K S'')) [Normal K L] : (fixH h2 L).Normal :=
  MonoidHom.normal_ker _

theorem mem_fixH (L : IntermediateField K (KS K S'')) [Normal K L] (g : GKS K S) :
    g ∈ fixH h2 L ↔ ∀ x ∈ L, galS K S'' (inflMap K h2 g) x = x := by
  rw [fixH, MonoidHom.mem_ker, MonoidHom.comp_apply]
  change (inflMap K h2 g : KS K S'' ≃ₐ[K] KS K S'') ∈ (AlgEquiv.restrictNormalHom L).ker ↔ _
  rw [IntermediateField.restrictNormalHom_ker]
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x.1 x.2⟩

/-- `G_{K,S} ⧸ G_L ≅ Gal(L/K)` is finite. Kind: PROVED. -/
theorem finite_quotient_fixH (L : IntermediateField K (KS K S'')) [Normal K L]
    [FiniteDimensional K L] : Finite (GKS K S ⧸ fixH h2 L) := by
  have hs : Function.Surjective ((AlgEquiv.restrictNormalHom L).comp
      (show GKS K S →* (KS K S'' ≃ₐ[K] KS K S'') from (inflMap K h2).toMonoidHom)) :=
    (AlgEquiv.restrictNormalHom_surjective (KS K S'')).comp (resUnr_surjective K h2)
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivOfSurjective _ hs).symm.toEquiv

/-- The transfer subgroup is open. Kind: PROVED. -/
theorem fixH_isOpen (L : IntermediateField K (KS K S'')) [Normal K L] [FiniteDimensional K L] :
    IsOpen (fixH h2 L : Set (GKS K S)) := by
  have he : (fixH h2 L : Set (GKS K S)) = (fun g : GKS K S =>
      (show KS K S'' ≃ₐ[K] KS K S'' from inflMap K h2 g)) ⁻¹'
        (L.fixingSubgroup : Set (KS K S'' ≃ₐ[K] KS K S'')) := by
    ext g
    rw [SetLike.mem_coe, mem_fixH]
    exact ⟨fun h x => h x.1 x.2, fun h x hx => h ⟨x, hx⟩⟩
  rw [he]
  exact (IntermediateField.fixingSubgroup_isOpen L).preimage (inflMap K h2).continuous

end Fix

/-! ### The open normal subgroup fixing a point -/

section DivV

variable {K : Type} [Field K] [NumberField K] {S S'' : Set (HeightOneSpectrum (𝓞 K))}
  (h2 : S'' ⊆ S) (W : WeierstrassCurve K)

/-- The field generated over `L` by the coordinates of `Q`. Kind: definition. -/
def ptCoordField (L : IntermediateField K (KS K S'')) (Q : PtS K S'' W) :
    IntermediateField K (KS K S'') :=
  L ⊔ IntermediateField.adjoin K {Affine.Point.xCoord Q, Affine.Point.yCoord Q}

instance (L : IntermediateField K (KS K S'')) [FiniteDimensional K L] (Q : PtS K S'' W) :
    FiniteDimensional K (ptCoordField W L Q) := by
  have : FiniteDimensional K (IntermediateField.adjoin K
      ({Affine.Point.xCoord Q, Affine.Point.yCoord Q} : Set (KS K S''))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  exact IntermediateField.finiteDimensional_sup _ _

/-- The normal closure of `ptCoordField`. Kind: definition. -/
abbrev ptNormalField (L : IntermediateField K (KS K S'')) (Q : PtS K S'' W) :
    IntermediateField K (KS K S'') :=
  IntermediateField.normalClosure K (ptCoordField W L Q) (KS K S'')

instance (L : IntermediateField K (KS K S'')) [FiniteDimensional K L] (Q : PtS K S'' W) :
    FiniteDimensional K (ptNormalField W L Q) :=
  normalClosure.is_finiteDimensional K (ptCoordField W L Q) (KS K S'')

instance (L : IntermediateField K (KS K S'')) (Q : PtS K S'' W) :
    Normal K (ptNormalField W L Q) :=
  normalClosure.normal K (ptCoordField W L Q) (KS K S'')

theorem le_ptNormalField (L : IntermediateField K (KS K S'')) (Q : PtS K S'' W) :
    L ≤ ptNormalField W L Q :=
  le_sup_left.trans (IntermediateField.le_normalClosure (ptCoordField W L Q))

theorem coords_mem_ptNormalField (L : IntermediateField K (KS K S'')) (Q : PtS K S'' W) :
    Affine.Point.xCoord Q ∈ ptNormalField W L Q ∧ Affine.Point.yCoord Q ∈ ptNormalField W L Q :=
  ⟨IntermediateField.le_normalClosure (ptCoordField W L Q)
      (le_sup_right (a := L) (IntermediateField.subset_adjoin K _ (by simp))),
    IntermediateField.le_normalClosure (ptCoordField W L Q)
      (le_sup_right (a := L) (IntermediateField.subset_adjoin K _ (by simp)))⟩

/-- **The open normal subgroup fixing `Q`** (and `L`). Kind: definition. -/
abbrev divV (L : IntermediateField K (KS K S'')) (Q : PtS K S'' W) : Subgroup (GKS K S) :=
  fixH h2 (ptNormalField W L Q)

/-- `divV` fixes `Q`. Kind: PROVED. -/
theorem divV_fixes (L : IntermediateField K (KS K S'')) (Q : PtS K S'' W) (g : GKS K S)
    (hg : g ∈ divV h2 W L Q) : inflMap K h2 g • Q = Q := by
  rw [mem_fixH] at hg
  rw [ptS_smul_def, Affine.Point.map_eq_self_iff]
  exact ⟨hg _ (coords_mem_ptNormalField W L Q).1, hg _ (coords_mem_ptNormalField W L Q).2⟩

/-- `divV ≤ G_L`. Kind: PROVED. -/
theorem divV_le (L : IntermediateField K (KS K S'')) [Normal K L] (Q : PtS K S'' W) :
    divV h2 W L Q ≤ fixH h2 L := fun g hg => by
  rw [mem_fixH] at hg ⊢
  exact fun x hx => hg x (le_ptNormalField W L Q hx)

end DivV

/-! ### The constructor -/

section Of

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ S'' : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) (h'' : S'' ⊆ S₁) (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) [IsOpenKer (alphaShap s hs hs0 π)]
  (ψ : Δ →* (Acoef i)ˣ) (P : Set (HeightOneSpectrum (𝓞 K))) (hψ : Function.Injective ψ)
  (hΨ : PsiTrivialAt2N i π ψ P) {ι : Type} (place : ι × Bool → Places K S)

/-- `ρ₀(g)(1 ⊗ ptMap R) = 1 ⊗ ptMap(infl(g) R)`. Kind: PROVED. -/
theorem ambRho_ptMap (g : GKS K S) (R : PtS K S'' W) :
    ambRhoU h1 W Δ g ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ ptMap h'' W R :
      MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W) =
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ ptMap h'' W (inflMap K (h''.trans h1) g • R) :
        MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W) := by
  let := Fintype.ofFinite Δ
  rw [ambRhoU_oneTmul' h1 W (ptMap h'' W R) g, inflMap_trans h'' h1 g, ptMap_smul]

/-- **The actual point of a support from a point over a finite normal extension** (tex 3080–3084,
3203–3215, 3251–3290, 3471–3487). Kind: definition. -/
def ActualPoint.ofField {Tp : Finset ι} (L : IntermediateField K (KS K S'')) [Normal K L]
    [FiniteDimensional K L]
    (hα : fixH (h''.trans h1) L ≤ (alphaInfl hS s hs hs0 π).ker)
    (R Q : PtS K S'' W) (hQR : ((2 ^ i : ℕ) : ℤ) • Q = R)
    (hR : ∀ g ∈ fixH (h''.trans h1) L, inflMap K (h''.trans h1) g • R = R)
    (hplace : ∀ j, j.1 ∉ Tp → (place j).1 ∉ S'') :
    ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp :=
  have := finite_quotient_fixH (h''.trans h1) L
  letI := Fintype.ofFinite (GKS K S ⧸ fixH (h''.trans h1) L)
  { H := fixH (h''.trans h1) L
    hH := hα
    r := fun δ => Quotient.out δ
    hr := fun δ => Quotient.out_eq' δ
    y := ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ ptMap h'' W R : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W)
    Q := ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ ptMap h'' W Q : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W)
    hQ := by
      change ((2 ^ i : ℕ) : ℤ) • ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ ptMap h'' W Q :
        MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W) = _
      rw [← TensorProduct.tmul_smul, ← map_zsmul, hQR]
    hfix := fun x hx => by
      rw [ambRho_ptMap h1 h'' W x R, hR x hx]
    V := divV (h''.trans h1) W L Q
    hVopen := fixH_isOpen (h''.trans h1) _
    hVH := divV_le (h''.trans h1) W L Q
    hVQ := fun x hx => by
      rw [ambRho_ptMap h1 h'' W x Q, divV_fixes (h''.trans h1) W L Q x hx]
    hin := hin_of_point (hS := hS) (h01 := h01) (h1 := h1) (W := W) (i := i) (s := s) (hs := hs)
      (hs0 := hs0) (hFull := hFull) (π := π) (P := P) ψ hψ hΨ (fixH (h''.trans h1) L) hα
      (fun δ => Quotient.out δ) (fun δ => Quotient.out_eq' δ) (ptMap h'' W R) fun x hx => by
        rw [← ptMap_smul h'' W (inflMap K h1 x) R, ← inflMap_trans h'' h1 x, hR x hx]
    hunr := fun j hj t ht => by
      rw [SetLike.mem_coe, mem_fixH, infl_inertiaImage (h''.trans h1) (place j) (hplace j hj) ht]
      exact fun x _ => rfl
    hQin := fun j hj =>
      inertiaFixes_of_support h1 h'' W Δ (place j) (hplace j hj)
        ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ Q : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S'' W) }

end Of

/-! ### The ring class field inside `K_{S''}` and the realized Heegner point -/

section HeegnerField

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Contrib.CloudB3RC53.CST
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open scoped WeierstrassCurve

variable {K : Type} [Field K] [NumberField K] {S'' : Set (HeightOneSpectrum (𝓞 K))}

/-- The primes of the conductor of `ℤ + d𝒪_K` lie over `d`. Kind: PROVED. -/
theorem cond_primes (d : ℕ) [NeZero d]
    (hSd : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S'') :
    ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ (conductorOrder K d).conductor → v ∈ S'' :=
  fun v hv => hSd v ((Ideal.le_of_dvd hv) (natCast_mem_conductor d))

/-- **`H_d` inside `K_{S''}`**. Kind: definition. -/
abbrev heegnerL (d : ℕ) [NeZero d]
    (hSd : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S'') :
    IntermediateField K (KS K S'') :=
  ringClassFieldS (conductorOrder K d) S'' (cond_primes d hSd)

theorem mem_heegnerL (d : ℕ) [NeZero d]
    (hSd : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S'') (z : KS K S'') :
    z ∈ heegnerL d hSd ↔
      (z : AlgebraicClosure K) ∈ toAlgClosure (ringClassField (conductorOrder K d)) :=
  IntermediateField.mem_restrict _ _

instance (d : ℕ) [NeZero d]
    (hSd : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S'') :
    Normal K (heegnerL d hSd) :=
  Normal.of_algEquiv ((IntermediateField.restrictAlgEquiv (ringClassField_le_KS _ S''
      (cond_primes d hSd))).symm.trans
    (IntermediateField.equivMap (ringClassField (conductorOrder K d))
      (separableClosure K (AlgebraicClosure K)).val).symm).symm

variable {E : WeierstrassCurve ℚ} {cp : CSTParam E} {emb : Qbar →ₐ[ℚ] ℂ}
  {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K} {D : HeegnerPointData E}

/-- `κ(D.H d)` is `H_d` in `K_{S''}`. Kind: PROVED. -/
theorem mem_heegnerL_iff (hA : FullAnchor E K cp emb κ D) (d : ℕ) [NeZero d]
    (hcop : Nat.Coprime d (D.N * D.DK.natAbs))
    (hSd : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S'') (z : KS K S'') :
    z ∈ heegnerL d hSd ↔ κ.symm z ∈ D.H d := by
  rw [mem_heegnerL, hA.field d hcop, AlgEquiv.apply_symm_apply]

/-- The coordinates of the realized point lie in `H_d`. Kind: PROVED. -/
theorem coords_realize_mem (hA : FullAnchor E K cp emb κ D) (d : ℕ) [NeZero d]
    (hcop : Nat.Coprime d (D.N * D.DK.natAbs))
    (hSd : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S'')
    (hκ : ∀ x ∈ D.H d, κ x ∈ unramifiedOutside K S'')
    (hy : ∃ Y' : (E.baseChange (D.H d)).toAffine.Point,
      Affine.Point.map (W' := E) (D.H d).val Y' = D.y d) :
    Affine.Point.xCoord (realize E S'' κ.toAlgHom (D.H d) hκ (D.y d) hy) ∈ heegnerL d hSd ∧
      Affine.Point.yCoord (realize E S'' κ.toAlgHom (D.H d) hκ (D.y d) hy) ∈ heegnerL d hSd := by
  classical
  have hP := compQ_realize E S'' κ.toAlgHom (D.H d) hκ (D.y d) hy
  set R := realize E S'' κ.toAlgHom (D.H d) hκ (D.y d) hy
  obtain ⟨Y', hY'⟩ := hy
  rw [← hY'] at hP
  rcases Y' with _ | ⟨x, y, h⟩
  · have hR0 : R = 0 := by
      apply incS_injective S'' (E.baseChange K)
      rw [← hP, ← Affine.Point.zero_def, map_zero, map_zero, map_zero]
    rw [hR0]
    exact ⟨zero_mem _, zero_mem _⟩
  · rw [Affine.Point.map_some] at hP
    obtain ⟨h₁, hc₁⟩ := compQ_some E κ.toAlgHom
      ((E.toAffine.baseChange_nonsingular (D.H d).val.injective x y).2 h)
    rw [hc₁] at hP
    rcases hRc : R with _ | ⟨px, py, hp⟩
    · rw [hRc, ← Affine.Point.zero_def, map_zero] at hP
      exact absurd hP (by simp)
    · rw [hRc, Affine.Point.map_some] at hP
      simp only [Affine.Point.some.injEq] at hP
      obtain ⟨hx, hy⟩ := hP
      refine ⟨?_, ?_⟩
      · change px ∈ heegnerL d hSd
        rw [mem_heegnerL_iff hA d hcop hSd]
        have : κ.symm (px : AlgebraicClosure K) = (x : Qbar) := by
          rw [show (px : AlgebraicClosure K) = κ x from hx.symm, AlgEquiv.symm_apply_apply]
        rw [this]
        exact x.2
      · change py ∈ heegnerL d hSd
        rw [mem_heegnerL_iff hA d hcop hSd]
        have : κ.symm (py : AlgebraicClosure K) = (y : Qbar) := by
          rw [show (py : AlgebraicClosure K) = κ y from hy.symm, AlgEquiv.symm_apply_apply]
        rw [this]
        exact y.2

end HeegnerField

/-! ### The actual Heegner point of a support -/

section HeegnerPoint

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Contrib.CloudB3RC53.CST
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open scoped WeierstrassCurve

variable {K : Type} [Field K] [NumberField K] {E : WeierstrassCurve ℚ}
  {S S₁ S'' : Set (HeightOneSpectrum (𝓞 K))} (h'' : S'' ⊆ S₁) (h1 : S₁ ⊆ S)
  {cp : CSTParam E} {emb : Qbar →ₐ[ℚ] ℂ}
  {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K} {D : HeegnerPointData E}

omit h1 in
/-- `E(K_{S''}) → E(K_{S₁}) → E(K̄)` is `E(K_{S''}) → E(K̄)`. Kind: PROVED. -/
theorem incS_ptMap (P : PtS K S'' (E.baseChange K)) :
    incS S₁ (E.baseChange K) (ptMap h'' (E.baseChange K) P) = incS S'' (E.baseChange K) P := by
  rcases P with _ | ⟨x, y, hxy⟩
  · rw [← Affine.Point.zero_def, map_zero, map_zero, map_zero]
  · obtain ⟨h', e⟩ := ptMap_some h'' (E.baseChange K) hxy
    rw [e]
    simp only [incS, Affine.Point.map_some, Affine.Point.some.injEq]
    exact ⟨coe_ksIncl h'' x, coe_ksIncl h'' y⟩

omit h1 in
/-- `ptMap` carries the realization over `S''` to the realization over `S₁`. Kind: PROVED. -/
theorem ptMap_realize (L : IntermediateField ℚ Qbar) (hκ : ∀ x ∈ L, κ x ∈ unramifiedOutside K S'')
    (hκ₁ : ∀ x ∈ L, κ x ∈ unramifiedOutside K S₁) (Y : (E⁄Qbar).toAffine.Point)
    (hY : ∃ Y' : (E.baseChange L).toAffine.Point, Affine.Point.map (W' := E) L.val Y' = Y) :
    ptMap h'' (E.baseChange K) (realize E S'' κ.toAlgHom L hκ Y hY) =
      realize E S₁ κ.toAlgHom L hκ₁ Y hY := by
  apply incS_injective S₁ (E.baseChange K)
  refine Eq.trans ?_ (compQ_realize E S₁ κ.toAlgHom L hκ₁ Y hY)
  rw [compQ_realize E S'' κ.toAlgHom L hκ Y hY]
  exact incS_ptMap h'' _

variable (hA : FullAnchor E K cp emb κ D) (d : ℕ) [NeZero d]
  (hcop : Nat.Coprime d (D.N * D.DK.natAbs))
  (hSd : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S'')
  (hy : ∃ Y' : (E.baseChange (D.H d)).toAffine.Point,
    Affine.Point.map (W' := E) (D.H d).val Y' = D.y d)

include hA hcop in
/-- **The realized Heegner point is fixed by `G_{H_d}`** (PROVED). -/
theorem realize_fixed (g : GKS K S) (hg : g ∈ fixH (h''.trans h1) (heegnerL d hSd)) :
    inflMap K (h''.trans h1) g • realize E S'' κ.toAlgHom (D.H d)
        (field_ii hA d hcop S'' hSd) (D.y d) hy =
      realize E S'' κ.toAlgHom (D.H d) (field_ii hA d hcop S'' hSd) (D.y d) hy := by
  rw [mem_fixH] at hg
  have hag : ∀ x (hx : x ∈ D.H d), κ.toAlgHom ((1 : GalQ) x) =
      (galS K S'' (inflMap K (h''.trans h1) g) ⟨κ x, field_ii hA d hcop S'' hSd x hx⟩ :
        AlgebraicClosure K) := by
    intro x hx
    have hm : (⟨κ x, field_ii hA d hcop S'' hSd x hx⟩ : KS K S'') ∈ heegnerL d hSd := by
      rw [mem_heegnerL_iff hA d hcop hSd]
      simpa using hx
    rw [hg _ hm]
    rfl
  have h := compQ_map_of_agree E S'' κ.toAlgHom (D.H d) (field_ii hA d hcop S'' hSd) (D.y d) hy 1
    (inflMap K (h''.trans h1) g) hag
  have h1' : Affine.Point.map (W' := E) (1 : GalQ).toAlgHom (D.y d) = D.y d := by
    rcases D.y d with _ | ⟨x, y, hxy⟩
    · rfl
    · rfl
  rw [h1', compQ_realize E S'' κ.toAlgHom (D.H d) (field_ii hA d hcop S'' hSd) (D.y d) hy] at h
  exact (incS_injective S'' (E.baseChange K) h).symm

include hA hcop in
/-- **A `2^i`-division point of the realized Heegner point in `E(K_{S''})`** (PROVED;
`DivisionPointsF.exists_supportPoint_ringClassField`, Silverman VIII.1.5(b) over `H_d`). -/
theorem exists_div_realize [(E.baseChange K).IsElliptic] (m : ℕ) (hm : m ≠ 0)
    (hmS : ∀ v : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ v.asIdeal → v ∈ S'')
    (hgood : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S'' →
      ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt (E.baseChange K) v) :
    ∃ Q : PtS K S'' (E.baseChange K), (m : ℤ) • Q =
      realize E S'' κ.toAlgHom (D.H d) (field_ii hA d hcop S'' hSd) (D.y d) hy := by
  set R := realize E S'' κ.toAlgHom (D.H d) (field_ii hA d hcop S'' hSd) (D.y d) hy
  have hc := coords_realize_mem hA d hcop hSd (field_ii hA d hcop S'' hSd) hy
  obtain ⟨P₀, hP₀⟩ := (Affine.Point.exists_map_eq_iff (incS S'' (E.baseChange K) R)
    (toAlgClosure (ringClassField (conductorOrder K d))).val).2
    ⟨⟨⟨_, (mem_heegnerL d hSd _).1 hc.1⟩, by rw [Affine.Point.xCoord_map]; rfl⟩,
      ⟨⟨_, (mem_heegnerL d hSd _).1 hc.2⟩, by rw [Affine.Point.yCoord_map]; rfl⟩⟩
  have hm' : (m : AlgebraicClosure K) ≠ 0 := Nat.cast_ne_zero.2 hm
  obtain ⟨X, hX⟩ := ((E.baseChange K).baseChange (AlgebraicClosure K)).toAffine.nsmul_surjective
    hm' (incS S'' (E.baseChange K) R)
  obtain ⟨Q, hQ⟩ := DivisionPointsF.exists_supportPoint_ringClassField (E.baseChange K)
    (conductorOrder K d) (cond_primes d hSd) hm hmS hgood P₀ X (by
      change m • X = _
      rw [show m • X = _ from hX, ← hP₀]; rfl)
  refine ⟨Q, incS_injective S'' (E.baseChange K) ?_⟩
  rw [map_zsmul, natCast_zsmul, hQ]
  exact hX

end HeegnerPoint

/-! ### The step identity for the actual Heegner points -/

section HeegnerStep

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Contrib.CloudB3RC53.CST
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open scoped WeierstrassCurve

attribute [local instance] mcoefModuleK

variable {K : Type} [Field K] [NumberField K] (E : WeierstrassCurve ℚ)
  {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) [(E.baseChange K).IsElliptic] (i : ℕ)
  [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hFull : FullTorsion K S₀ (E.baseChange K) (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) [IsOpenKer (alphaShap s hs hs0 π)]
  (ψ : Δ →* (Acoef i)ˣ) (P : Set (HeightOneSpectrum (𝓞 K))) (hψ : Function.Injective ψ)
  (hΨ : PsiTrivialAt2N i π ψ P) {ι : Type} (place : ι × Bool → Places K S)
  {cp : CSTParam E} {emb : Qbar →ₐ[ℚ] ℂ} {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K}
  {D : HeegnerPointData E}

/-- **The actual Heegner point of conductor `d` on the support `Tp`** (tex 3080–3084,
3203–3215, 3293–3295): `1 ⊗ P_d` with `P_d ∈ E(K_{S''})` the realized Heegner point, the transfer
subgroup `G_{H_d}`, a `2^i`-division point in `E(K_{S''})`, for `S'' ⊆ S₁` containing the primes
of `d` and of `2`, outside of which `E` has good reduction, and containing no place off `Tp`.
The input `hα` is that `χ_h [π]` is trivial on `G_{H_d}`. Kind: definition. -/
def heegnerActual (hA : FullAnchor E K cp emb κ D) {Tp : Finset ι}
    {S'' : Set (HeightOneSpectrum (𝓞 K))}
    (h'' : S'' ⊆ S₁) (d : ℕ) [NeZero d] (hcop : Nat.Coprime d (D.N * D.DK.natAbs))
    (hSd : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S'')
    (hmS : ∀ v : HeightOneSpectrum (𝓞 K), ((2 ^ i : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S'')
    (hgood : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S'' →
      ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt (E.baseChange K) v)
    (hα : fixH (h''.trans h1) (heegnerL d hSd) ≤ (alphaInfl hS s hs hs0 π).ker)
    (hplace : ∀ j, j.1 ∉ Tp → (place j).1 ∉ S'') :
    ActualPoint hS h01 h1 (E.baseChange K) i s hs hs0 hFull π P place Tp :=
  ActualPoint.ofField hS h01 h1 h'' (E.baseChange K) i s hs hs0 hFull π ψ P hψ hΨ place
    (heegnerL d hSd) hα
    (realize E S'' κ.toAlgHom (D.H d) (field_ii hA d hcop S'' hSd) (D.y d)
      (anchor_coords hA.anchor (Nat.pos_of_ne_zero (NeZero.ne d)) hcop))
    (Classical.choose (exists_div_realize hA d hcop hSd
      (anchor_coords hA.anchor (Nat.pos_of_ne_zero (NeZero.ne d)) hcop) (2 ^ i)
      (pow_ne_zero _ two_ne_zero) hmS hgood))
    (Classical.choose_spec (exists_div_realize hA d hcop hSd
      (anchor_coords hA.anchor (Nat.pos_of_ne_zero (NeZero.ne d)) hcop) (2 ^ i)
      (pow_ne_zero _ two_ne_zero) hmS hgood))
    (realize_fixed h'' h1 hA d hcop hSd _) hplace

omit [(E.baseChange K).IsElliptic] in
/-- The transfer subgroup `G_{H_d}` described through `K_{S₁}` (PROVED). -/
theorem mem_fixH_heegnerL (hA : FullAnchor E K cp emb κ D) {S'' : Set (HeightOneSpectrum (𝓞 K))}
    (h'' : S'' ⊆ S₁) (d : ℕ) [NeZero d] (hcop : Nat.Coprime d (D.N * D.DK.natAbs))
    (hSd : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S'')
    (hκ : ∀ x ∈ D.H d, κ x ∈ unramifiedOutside K S₁) (g : GKS K S) :
    g ∈ fixH (h''.trans h1) (heegnerL d hSd) ↔ ∀ x (hx : x ∈ D.H d),
      ((galS K S₁ (inflMap K h1 g) ⟨κ x, hκ x hx⟩ : unramifiedOutside K S₁) :
        AlgebraicClosure K) = κ x := by
  rw [mem_fixH, inflMap_trans h'' h1 g]
  constructor
  · intro hg x hx
    have hm : (⟨κ x, field_ii hA d hcop S'' hSd x hx⟩ : KS K S'') ∈ heegnerL d hSd := by
      rw [mem_heegnerL_iff hA d hcop hSd]
      simpa using hx
    have := congrArg (fun z : KS K S₁ => (z : AlgebraicClosure K))
      (ksIncl_infl h'' (inflMap K h1 g) ⟨κ x, field_ii hA d hcop S'' hSd x hx⟩)
    simp only [hg _ hm, coe_ksIncl] at this
    exact this.symm
  · intro hg z hz
    rw [mem_heegnerL_iff hA d hcop hSd] at hz
    have hx := hg _ hz
    apply Subtype.ext
    have := congrArg (fun z : KS K S₁ => (z : AlgebraicClosure K))
      (ksIncl_infl h'' (inflMap K h1 g) z)
    simp only [coe_ksIncl] at this
    rw [this]
    have hz' : (ksIncl h'' z : KS K S₁) = ⟨κ (κ.symm z), hκ _ hz⟩ := by
      apply Subtype.ext
      exact (coe_ksIncl h'' z).trans (AlgEquiv.apply_symm_apply κ _).symm
    rw [hz', hx]
    exact AlgEquiv.apply_symm_apply κ _

end HeegnerStep

/-! ### The step identity for the constructed Heegner points -/

section HeegnerFinal

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Contrib.CloudB3RC53.CST
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open scoped WeierstrassCurve

attribute [local instance] mcoefModuleK

theorem admissible_coprime_d {E : WeierstrassCurve ℚ} {D : HeegnerPointData E} {d q : ℕ}
    (hadm : D.Admissible d q) : Nat.Coprime d (D.N * D.DK.natAbs) :=
  Nat.Coprime.coprime_dvd_right (Dvd.intro_left 2 (by ring)) hadm.2.1

theorem admissible_coprime_dq {E : WeierstrassCurve ℚ} {D : HeegnerPointData E} {d q : ℕ}
    (hadm : D.Admissible d q) : Nat.Coprime (d * q) (D.N * D.DK.natAbs) := by
  refine Nat.Coprime.mul_left (admissible_coprime_d hadm) ?_
  obtain ⟨-, -, hq, hqd⟩ := hadm
  exact (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqd (h.trans ⟨6 * d, by ring⟩)

variable {K : Type} [Field K] [NumberField K] (E : WeierstrassCurve ℚ)
  {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) [(E.baseChange K).IsElliptic] (i : ℕ)
  [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hFull : FullTorsion K S₀ (E.baseChange K) (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)
  [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
  (P : Set (HeightOneSpectrum (𝓞 K))) (hψ : Function.Injective ψ) (hΨ : PsiTrivialAt2N i π ψ P)
  (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k] [StageIsoA k i]
  [DecidableEq (Places K S₀)] {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)

/-- **The step identity for the actual Heegner points** (PROVED from the anchored norm relations,
tex 2914–2936, 3080–3084, 3915, 4157–4172). For an anchored datum `D`, admissible `(d, q)`
with `q` split, and consecutive supports `Tp`, `Tp ∪ {p}` with sets `S_T, S_R ⊆ S₁` as in `heegnerActual` (primes of `d`, resp. `dq`, and
of `2`; good reduction outside; no place off the support), the classes of the actual Heegner
points `A_T = heegnerActual … d`, `A_R = heegnerActual … (dq)` satisfy, at every new place `w`
over the anchor's prime `𝔮 ∣ q` (with `w ∤ d`, prime to the conductors), lane RC32's step
identity `g_R = pointFactor a_q z z⁻¹ · g_T + d b`, `z = α(Frob_w)`. The character assumptions
`hα_T` and `hα_R` make `χ_h [π]` trivial on `G_{H_d}` and `G_{H_{dq}}`. -/
theorem gx_step_heegner {cp : CSTParam E} {emb : Qbar →ₐ[ℚ] ℂ}
    {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K}
    (hnorm : ∃ D : HeegnerPointData E, D.NormRelations ∧ FullAnchor E K cp emb κ D) :
    ∃ D : HeegnerPointData E, ∃ hA : FullAnchor E K cp emb κ D, D.NormRelations ∧
      ∀ {d q : ℕ} [NeZero d] [NeZero q] (hadm : D.Admissible d q) (_ : jacobiSym D.DK q = 1)
        {Tp : Finset ι} {p : ι} {ST SR : Set (HeightOneSpectrum (𝓞 K))}
        (hT : ST ⊆ S₁) (hR : SR ⊆ S₁)
        (hSdT : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ ST)
        (hSdR : ∀ v : HeightOneSpectrum (𝓞 K), ((d * q : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ SR)
        (hmT : ∀ v : HeightOneSpectrum (𝓞 K), ((2 ^ i : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ ST)
        (hmR : ∀ v : HeightOneSpectrum (𝓞 K), ((2 ^ i : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ SR)
        (hgoodT : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ ST →
          ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt (E.baseChange K) v)
        (hgoodR : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SR →
          ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt (E.baseChange K) v)
        (hαT : fixH (hT.trans h1) (heegnerL d hSdT) ≤ (alphaInfl hS s hs hs0 π).ker)
        (hαR : fixH (hR.trans h1) (heegnerL (d * q) hSdR) ≤ (alphaInfl hS s hs hs0 π).ker)
        (hplT : ∀ j, j.1 ∉ Tp → (place j).1 ∉ ST)
        (hplR : ∀ j, j.1 ∉ insert p Tp → (place j).1 ∉ SR),
        ∃ 𝔮 : HeightOneSpectrum (𝓞 K), (q : 𝓞 K) ∈ 𝔮.asIdeal ∧
          ∀ (w : NewPlaces K S₀ S) (_ : w.1 = 𝔮) (_ : (d : 𝓞 K) ∉ w.1.asIdeal)
            (_ : w.1.asIdeal ∈ TauCeti.GlobalNumberFields.integralIdealsPrimeTo
              (ZInQ.Contrib.CloudB3RC53.CST.conductorOrder K d).conductorModulus)
            (_ : w.1.asIdeal ∈ TauCeti.GlobalNumberFields.integralIdealsPrimeTo
              (ZInQ.Contrib.CloudB3E1RingClass.ringClassOrder (K := K) d
                (NeZero.ne d)).conductorModulus),
            ∃ bG : (globalCx k (GKS K S) (MinS hS (E.baseChange K) i
                (alphaStage i s hs hs0 π ψ))).X 0,
              gx hS h01 h1 (E.baseChange K) i s hs hs0 hFull π ψ P k place
                  (heegnerActual E hS h01 h1 i s hs hs0 hFull π ψ P hψ hΨ place hA hR (d * q)
                    (admissible_coprime_dq hadm) hSdR hmR hgoodR hαR hplR) =
                pointFactor ((E.LFunction q : ℤ) : k)
                    ((eK k i).symm (alphaStage i s hs hs0 π ψ (urFrobElt K w) : Acoef i))
                    ((eK k i).symm (((alphaStage i s hs hs0 π ψ (urFrobElt K w))⁻¹ :
                      (Acoef i)ˣ) : Acoef i)) •
                  gx hS h01 h1 (E.baseChange K) i s hs hs0 hFull π ψ P k place
                    (heegnerActual E hS h01 h1 i s hs hs0 hFull π ψ P hψ hΨ place hA hT d
                      (admissible_coprime_d hadm) hSdT hmT hgoodT hαT hplT) +
                (globalCx k (GKS K S) (MinS hS (E.baseChange K) i
                  (alphaStage i s hs hs0 π ψ))).d 0 1 rfl bG := by
  obtain ⟨D, hA, hD, hall⟩ := gx_step_anchored E hS h01 h1 i s hs hs0 hFull π ψ P k place hnorm
  refine ⟨D, hA, hD, fun {d q} _ _ hadm hsplit Tp p ST SR hT hR hSdT hSdR hmT hmR hgoodT hgoodR
    hαT hαR hplT hplR => ?_⟩
  have hcopP := admissible_coprime_d hadm
  have hcopR := admissible_coprime_dq hadm
  have hSd₁ : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S₁ :=
    fun v hv => hT (hSdT v hv)
  have hSdq₁ : ∀ v : HeightOneSpectrum (𝓞 K), ((d * q : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S₁ :=
    fun v hv => hR (hSdR v hv)
  have hκP := field_ii hA d hcopP S₁ hSd₁
  have hκR := field_ii hA (d * q) hcopR S₁ hSdq₁
  set AT := heegnerActual E hS h01 h1 i s hs hs0 hFull π ψ P hψ hΨ place hA hT d hcopP hSdT hmT
    hgoodT hαT hplT
  set AR := heegnerActual E hS h01 h1 i s hs hs0 hFull π ψ P hψ hΨ place hA hR (d * q) hcopR
    hSdR hmR hgoodR hαR hplR
  have : AR.H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let U : Subgroup AT.H := AR.H.subgroupOf AT.H
  let : Fintype (AT.H ⧸ U) := Subgroup.fintypeQuotientOfFiniteIndex
  obtain ⟨𝔮, hq, hw⟩ := hall hadm hsplit hSd₁ hκP hκR AT AR
    (mem_fixH_heegnerL E h1 hA hT d hcopP hSdT hκP)
    (mem_fixH_heegnerL E h1 hA hR (d * q) hcopR hSdR hκR) U
    (fun x => Subgroup.mem_subgroupOf) (fun τ => Quotient.out τ) (fun τ => Quotient.out_eq' τ)
    (anchor_coords hA.anchor (Nat.pos_of_ne_zero (NeZero.ne d)) hcopP)
    (anchor_coords hA.anchor (Nat.pos_of_ne_zero (NeZero.ne (d * q))) hcopR)
    (congrArg (fun Y => ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ Y :
      MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ (E.baseChange K))) (ptMap_realize hT _ _ hκP _ _))
    (congrArg (fun Y => ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ Y :
      MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ (E.baseChange K))) (ptMap_realize hR _ _ hκR _ _))
  exact ⟨𝔮, hq, hw⟩

end HeegnerFinal

end ZInQ.Contrib.CloudB3E2.NormCochain

import ZInQKernel.Contrib.OneProof.CMHeight62Full.TreeH4
import ZInQKernel.Contrib.OneProof.JDescent4Genus
import ZInQKernel.Contrib.AbVarBC.Dim
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Dominant

/-!
# cmHeight62 (finite place): the N11-inst instance on the tree (item H3)

Let `E/K` be an elliptic curve with its short datum `D` (`ShortModel.ShortData`: `x, y` regular
off the identity, with poles of orders `2, 3` at the identity place `P` and `y² = x³ + a x + b`),
and `L/K` a number field. The projection `E_L → E` (`bcProj`) is dominant (a base change of the
surjection `Spec L → Spec K`), so it pulls back rational functions: `ι : K(E) → K(E_L)`
(`treeH3Iota`). Let `P_L` be the identity place of `K(E_L)` (its valuation ring is the image of the
stalk at the identity). With `X' = ι(x)` and `Y' = ι(y)`:

* `treeH3_equation`: `(X', Y')` satisfies the Weierstrass equation of `W_L = D.W ⊗ L`;
* `treeH3_valuation`: `v_{P_L}(X') = exp 2` and `v_{P_L}(Y') = exp 3`. Here `η_W ≠ 0` enters
  (item H4): it gives `ord_{P_L}(−X'/Y') = 1`, and `X'·(X'/Y')² = ι(x³/y²)` has order `0`;
* `treeH3_regularAway`: `X', Y'` are regular at every place `Q ≠ P_L`. The centre `c` of `Q` is a
  closed point of `E_L`. If `c` lies over the identity of `E`, then `c` is the identity of `E_L`
  (`tree34_eq_of_fst_eq`: the fibre of a base change over a rational point is one point), so
  `Q = P_L`. Otherwise `x, y` are regular at the image of `c`;
* `treeH3_param`: the image of `tG` in `K(E_L)` is `−X'/Y'`;
* `treeH3_poleSpaces`: the pole-space ladder of `P_L` (from `abVar_identityPoleSpaces`);
* `treeH3_exists_variableChange`: **the N11-inst instance.** A second Weierstrass pair
  `(x₀, y₀)` of a curve `W₀/L`, regular off `P_L` with pole orders `2, 3`, is
  `x₀ = u²X' + r`, `y₀ = u³Y' + su²X' + t` for one change of variables `C`, and
  `C⁻¹ • W_L = W₀` (`exists_variableChange_of_riemannRoch`).

`treeH3_n11Inst` collects the inputs `X', Y'` of the per-place assembly.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open CategoryTheory AlgebraicGeometry Limits IsLocalRing
open ZInQ.DefFaltings

/-! ## 1. The fibre of a base change over a rational point -/

section Fibre

theorem tree34_injective_of_isIso {A B : Scheme} (f : A ⟶ B) [IsIso f] :
    Function.Injective f := by
  intro a b h
  have h' := congrArg (inv f) h
  rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id] at h'

/-- Over the image `e(s)` of a section `e` of `p : X → S`, with `S` a point, the base change
`X ×_S Y → X` has at most one point when `Y` has one point. -/
theorem tree34_eq_of_fst_eq {X Y S : Scheme} [Subsingleton S] [Subsingleton Y] (p : X ⟶ S)
    (g : Y ⟶ S) (e : S ⟶ X) (he : e ≫ p = 𝟙 S) (s : S) {c₁ c₂ : ↑(pullback p g)}
    (h₁ : pullback.fst p g c₁ = e s) (h₂ : pullback.fst p g c₂ = e s) : c₁ = c₂ := by
  obtain ⟨z₁, hz₁, hz₁'⟩ := Scheme.Pullback.exists_preimage_pullback (f := e)
    (g := pullback.fst p g) s c₁ h₁.symm
  obtain ⟨z₂, hz₂, hz₂'⟩ := Scheme.Pullback.exists_preimage_pullback (f := e)
    (g := pullback.fst p g) s c₂ h₂.symm
  have : IsIso (e ≫ p) := by rw [he]; infer_instance
  have hsub : ∀ w₁ w₂ : ↑(pullback (e ≫ p) g), w₁ = w₂ := by
    intro w₁ w₂
    apply tree34_injective_of_isIso (pullback.snd (e ≫ p) g)
    exact Subsingleton.elim _ _
  have hz : z₁ = z₂ := tree34_injective_of_isIso (pullbackRightPullbackFstIso p g e).hom
    (hsub _ _)
  rw [← hz₁', ← hz₂', hz]

end Fibre

/-! ## 2. Constants under the pullback of rational functions -/

section Constants

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem tree34_functionFieldMap_const {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
    (p : X ⟶ Spec (CommRingCat.of K)) (p' : X' ⟶ Spec (CommRingCat.of L)) (f : X' ⟶ X)
    [IsDominant f] (hf : f ≫ p = p' ≫ Spec.map (CommRingCat.ofHom (algebraMap K L))) (a : K) :
    haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
    haveI : Nonempty (⊤ : X'.Opens) := ⟨⟨genericPoint X', trivial⟩⟩
    f.functionFieldMap.hom (X.germToFunctionField ⊤
        (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))) =
      X'.germToFunctionField ⊤
        (p'.appTop ((Scheme.ΓSpecIso (CommRingCat.of L)).inv (algebraMap K L a))) := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  have : Nonempty (⊤ : X'.Opens) := ⟨⟨genericPoint X', trivial⟩⟩
  have h := congrArg (fun φ => CommRingCat.Hom.hom φ
    (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)))
    (f.germToFunctionField_functionFieldMap (⊤ : X.Opens))
  simp only [CommRingCat.comp_apply] at h
  rw [h]
  change X'.germToFunctionField ⊤ (f.appTop (p.appTop _)) = _
  have hc : f.appTop (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) =
      p'.appTop ((Spec.map (CommRingCat.ofHom (algebraMap K L))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hf, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply]
  rw [hc]
  congr 2
  have hn := congrArg (fun φ => CommRingCat.Hom.hom φ a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K L)))
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hn
  exact hn.symm

end Constants

/-! ## 3. The tree: the pullback `ι : K(E) → K(E_L)` -/

section Tree

open HDec.CMBranch.CMjBridges (abVar_isIntegral abVarFunctionFieldAlgebra AbVarFunctionField
  abVarIdentity abVarPunctured abVar_exists_placeCenter abVar_identityPoleSpaces
  abVar_isFunctionField germToFunctionField_abVarSectionConst)
open ZInQ.Contrib.CMHeight62 (ShortData bcProj bcProj_identity)
open ZInQ.Contrib.RC53Assist.HodgeLineBinding (originStalkEquiv stalkMapAt algebraMap_stalkMapAt)
open MonObj

attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra

/-- The projection `E_L → E` is dominant: it is a base change of the surjection
`Spec L → Spec K`. -/
theorem treeH3_bcProj_isDominant {K : Type} [Field K] (E : PkgI3.AbVar K) (L : Type) [Field L]
    [Algebra K L] : IsDominant (bcProj E L) := by
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    ⟨fun _ => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  have : Surjective (pullback.fst E.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :=
    inferInstance
  unfold bcProj
  exact ⟨(Scheme.Hom.surjective
    (pullback.fst E.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))))).denseRange⟩

/-- `ι : K(E) → K(E_L)`, the pullback of rational functions along `E_L → E`. -/
def treeH3Iota {K : Type} [Field K] (E : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
    AbVarFunctionField E →+* AbVarFunctionField (E.baseChange L) :=
  haveI := treeH3_bcProj_isDominant E L
  (bcProj E L).functionFieldMap.hom

theorem treeH3Iota_algebraMap_stalk {K : Type} [Field K] (E : PkgI3.AbVar K) (L : Type)
    [Field L] [Algebra K L] (c : (E.baseChange L).X.left) {y : E.X.left}
    (h : bcProj E L c = y) (g : E.X.left.presheaf.stalk y) :
    treeH3Iota E L (algebraMap _ (AbVarFunctionField E) g) =
      algebraMap _ (AbVarFunctionField (E.baseChange L)) ((stalkMapAt (bcProj E L) h).hom g) := by
  haveI := treeH3_bcProj_isDominant E L
  exact (algebraMap_stalkMapAt (bcProj E L) h g).symm

/-- `ι` is the identity on the constants `K ⊆ L`. -/
theorem treeH3Iota_algebraMap {K : Type} [Field K] (E : PkgI3.AbVar K) (L : Type) [Field L]
    [Algebra K L] (a : K) :
    treeH3Iota E L (algebraMap K (AbVarFunctionField E) a) =
      algebraMap L (AbVarFunctionField (E.baseChange L)) (algebraMap K L a) := by
  haveI := treeH3_bcProj_isDominant E L
  exact tree34_functionFieldMap_const E.X.hom (E.baseChange L).X.hom (bcProj E L)
    pullback.condition a

theorem treeH3Iota_ne_zero {K : Type} [Field K] (E : PkgI3.AbVar K) (L : Type) [Field L]
    [Algebra K L] {f : AbVarFunctionField E} (hf : f ≠ 0) : treeH3Iota E L f ≠ 0 :=
  (map_ne_zero _).2 hf

/-- `ι` carries the valuation ring of the identity place of `K(E)` into that of `K(E_L)`. -/
theorem treeH3Iota_integers {K : Type} [Field K] (E : PkgI3.AbVar K) (L : Type) [Field L]
    [Algebra K L] (P : TauCeti.Place K (AbVarFunctionField E))
    (hp : (algebraMap (E.X.left.presheaf.stalk (abVarIdentity E)) (AbVarFunctionField E)).range =
      P.integers.toSubring)
    (PL : TauCeti.Place L (AbVarFunctionField (E.baseChange L)))
    (hpL : (algebraMap ((E.baseChange L).X.left.presheaf.stalk
        (abVarIdentity (E.baseChange L))) (AbVarFunctionField (E.baseChange L))).range =
      PL.integers.toSubring)
    (f : AbVarFunctionField E) (hf : P.valuation f ≤ 1) :
    PL.valuation (treeH3Iota E L f) ≤ 1 := by
  have hf' : f ∈ (algebraMap (E.X.left.presheaf.stalk (abVarIdentity E))
      (AbVarFunctionField E)).range := by
    rw [hp]
    exact P.mem_integers_iff.2 hf
  obtain ⟨g, rfl⟩ := hf'
  rw [treeH3Iota_algebraMap_stalk E L _ (bcProj_identity E L) g]
  have hm : algebraMap _ (AbVarFunctionField (E.baseChange L))
      ((stalkMapAt (bcProj E L) (bcProj_identity E L)).hom g) ∈
      (algebraMap ((E.baseChange L).X.left.presheaf.stalk (abVarIdentity (E.baseChange L)))
        (AbVarFunctionField (E.baseChange L))).range := ⟨_, rfl⟩
  rw [hpL] at hm
  exact PL.mem_integers_iff.1 hm

/-- `ι(−x/y)` is the image of `t_L`. -/
theorem treeH3Iota_fXY {K : Type} [Field K] {E : PkgI3.AbVar K} (L : Type) [Field L]
    [NumberField L] [Algebra K L] (D : ShortData E) :
    treeH3Iota E L D.fXY = algebraMap ((E.baseChange L).X.left.presheaf.stalk
      (abVarIdentity (E.baseChange L))) (AbVarFunctionField (E.baseChange L)) (D.tL (L := L)) := by
  rw [← D.algebraMap_tE]
  exact treeH3Iota_algebraMap_stalk E L _ (bcProj_identity E L) D.tE

/-! ## 4. The tree: the Weierstrass pair `(X', Y')` on `E_L` -/

/-- `y² = x³ + a x + b` in `K(E)`. -/
theorem treeH3_Y_sq {K : Type} [Field K] {E : PkgI3.AbVar K} (D : ShortData E) :
    D.Y ^ 2 = D.X ^ 3 + algebraMap K (AbVarFunctionField E) D.a * D.X +
      algebraMap K (AbVarFunctionField E) D.b := by
  haveI := D.nonempty_punctured
  have h := congrArg (fun z => E.X.left.germToFunctionField (abVarPunctured E) z) D.heq
  simp only [map_pow, map_add, map_mul, germToFunctionField_abVarSectionConst] at h
  exact h

/-- **`(X', Y')` satisfies the Weierstrass equation of `W_L`.** -/
theorem treeH3_equation {K : Type} [Field K] {E : PkgI3.AbVar K} (L : Type) [Field L]
    [Algebra K L] (D : ShortData E) :
    ((D.W.map (algebraMap K L)).baseChange
      (AbVarFunctionField (E.baseChange L))).toAffine.Equation
        (treeH3Iota E L D.X) (treeH3Iota E L D.Y) := by
  rw [genCmp_equation_baseChange_iff]
  have h := congrArg (treeH3Iota E L) (treeH3_Y_sq D)
  simp only [map_pow, map_add, map_mul, treeH3Iota_algebraMap] at h
  simp only [ZInQ.Contrib.CMHeight62.ShortData.W, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, map_zero]
  linear_combination h

/-- `ord_{P_L}(X') = −2` and `ord_{P_L}(Y') = −3`. -/
theorem treeH3_ord {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] (D : ShortData E) (𝒢 : GroupModel E L)
    (hη : D.etaW 𝒢 ≠ 0) (PL : TauCeti.Place L (AbVarFunctionField (E.baseChange L)))
    (hpL : (algebraMap ((E.baseChange L).X.left.presheaf.stalk
        (abVarIdentity (E.baseChange L))) (AbVarFunctionField (E.baseChange L))).range =
      PL.integers.toSubring) :
    PL.ord (treeH3Iota E L D.X) = -2 ∧ PL.ord (treeH3Iota E L D.Y) = -3 := by
  have hX := treeH3Iota_ne_zero E L D.X_ne_zero
  have hY := treeH3Iota_ne_zero E L D.Y_ne_zero
  have h1 : PL.ord (-treeH3Iota E L D.X / treeH3Iota E L D.Y) = 1 := by
    have e := congrArg PL.ord (treeH3Iota_fXY L D)
    rw [ZInQ.Contrib.CMHeight62.ShortData.fXY, map_div₀, map_neg] at e
    exact e.trans (treeH4_ord_tL D 𝒢 hη PL hpL)
  have h0 : PL.ord (treeH3Iota E L D.X ^ 3 / treeH3Iota E L D.Y ^ 2) = 0 := by
    have hP0 : D.P.ord (D.X ^ 3 / D.Y ^ 2) = 0 := by
      rw [D.P.ord_div (pow_ne_zero 3 D.X_ne_zero) (pow_ne_zero 2 D.Y_ne_zero), D.P.ord_pow,
        D.P.ord_pow, D.ord_X, D.ord_Y]
      norm_num
    have h := tree34_ord_map_eq_zero D.P PL (treeH3Iota E L)
      (treeH3Iota_integers E L D.P D.hp PL hpL) hP0
    rwa [map_div₀, map_pow, map_pow] at h
  exact tree34_ord_xy PL hX hY h1 h0

/-- **`v_{P_L}(X') = exp 2` and `v_{P_L}(Y') = exp 3`.** -/
theorem treeH3_valuation {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] (D : ShortData E) (𝒢 : GroupModel E L)
    (hη : D.etaW 𝒢 ≠ 0) (PL : TauCeti.Place L (AbVarFunctionField (E.baseChange L)))
    (hpL : (algebraMap ((E.baseChange L).X.left.presheaf.stalk
        (abVarIdentity (E.baseChange L))) (AbVarFunctionField (E.baseChange L))).range =
      PL.integers.toSubring) :
    PL.valuation (treeH3Iota E L D.X) = WithZero.exp (1 : ℤ) ^ 2 ∧
      PL.valuation (treeH3Iota E L D.Y) = WithZero.exp (1 : ℤ) ^ 3 := by
  obtain ⟨hx, hy⟩ := treeH3_ord D 𝒢 hη PL hpL
  exact ⟨tree34_valuation_of_ord PL (treeH3Iota_ne_zero E L D.X_ne_zero) (n := 2)
      (by rw [hx]; norm_num),
    tree34_valuation_of_ord PL (treeH3Iota_ne_zero E L D.Y_ne_zero) (n := 3)
      (by rw [hy]; norm_num)⟩

/-- **`X', Y'` are regular at every place `Q ≠ P_L`.** -/
theorem treeH3_regularAway {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L]
    [Algebra K L] (hdim : E.dim = 1) (D : ShortData E)
    (PL : TauCeti.Place L (AbVarFunctionField (E.baseChange L)))
    (hpL : (algebraMap ((E.baseChange L).X.left.presheaf.stalk
        (abVarIdentity (E.baseChange L))) (AbVarFunctionField (E.baseChange L))).range =
      PL.integers.toSubring) :
    treeH3Iota E L D.X ∈ regularAway PL ∧ treeH3Iota E L D.Y ∈ regularAway PL := by
  have hdimL : (E.baseChange L).dim = 1 := (PkgI3.AbVar.dim_baseChange E L).trans hdim
  haveI := D.nonempty_punctured
  have key : ∀ (s : Γ(E.X.left, abVarPunctured E))
      (Q : TauCeti.Place L (AbVarFunctionField (E.baseChange L))), Q ≠ PL →
      Q.valuation (treeH3Iota E L (E.X.left.germToFunctionField (abVarPunctured E) s)) ≤ 1 := by
    intro s Q hQ
    obtain ⟨c, -, hcQ⟩ := abVar_exists_placeCenter (E.baseChange L) hdimL Q
    by_cases h0 : bcProj E L c = abVarIdentity E
    · exfalso
      have hc : c = abVarIdentity (E.baseChange L) :=
        tree34_eq_of_fst_eq E.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))
          (η[E.X]).left (Over.w η[E.X]) (IsLocalRing.closedPoint K) h0 (bcProj_identity E L)
      subst hc
      exact hQ (TauCeti.Place.integers_injective
        (ValuationSubring.toSubring_injective (hcQ.symm.trans hpL)))
    · have hc' : bcProj E L c ∈ abVarPunctured E := h0
      rw [← E.X.left.algebraMap_germ_eq_germToFunctionField hc' s,
        treeH3Iota_algebraMap_stalk E L c rfl]
      have hm : algebraMap _ (AbVarFunctionField (E.baseChange L))
          ((stalkMapAt (bcProj E L) (rfl : bcProj E L c = bcProj E L c)).hom
            (E.X.left.presheaf.germ (abVarPunctured E) (bcProj E L c) hc' s)) ∈
          (algebraMap ((E.baseChange L).X.left.presheaf.stalk c)
            (AbVarFunctionField (E.baseChange L))).range := ⟨_, rfl⟩
      rw [hcQ] at hm
      exact Q.mem_integers_iff.1 hm
  exact ⟨fun Q hQ => key D.x Q hQ, fun Q hQ => key D.y Q hQ⟩

/-- **The image of `tG` in `K(E_L)` is `−X'/Y'`.** -/
theorem treeH3_param {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] (D : ShortData E) (𝒢 : GroupModel E L) :
    algebraMap ((E.baseChange L).X.left.presheaf.stalk (abVarIdentity (E.baseChange L)))
        (AbVarFunctionField (E.baseChange L)) (originStalkEquiv 𝒢 (D.tG 𝒢 : 𝒢.genStalk)) =
      -treeH3Iota E L D.X / treeH3Iota E L D.Y := by
  rw [treeH4_originStalkEquiv_tG]
  have h1 : treeH3Iota E L D.fXY = -treeH3Iota E L D.X / treeH3Iota E L D.Y := by
    rw [ZInQ.Contrib.CMHeight62.ShortData.fXY, map_div₀, map_neg]
  exact (treeH3Iota_fXY L D).symm.trans h1

/-- **The pole-space ladder of `P_L`**: `L(nP_L)` is finite-dimensional, of dimension `n` for
`n ≥ 1` (`abVar_identityPoleSpaces` for `E_L`; its place is `P_L`, the place with the same
valuation ring). -/
theorem treeH3_poleSpaces {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] (hdim : E.dim = 1)
    (PL : TauCeti.Place L (AbVarFunctionField (E.baseChange L)))
    (hpL : (algebraMap ((E.baseChange L).X.left.presheaf.stalk
        (abVarIdentity (E.baseChange L))) (AbVarFunctionField (E.baseChange L))).range =
      PL.integers.toSubring) :
    (∀ n : ℕ, FiniteDimensional L (poleSpace PL n)) ∧
      ∀ n : ℕ, 1 ≤ n → TauCeti.Divisor.dim (Finsupp.single PL (n : ℤ) :
        TauCeti.Divisor L (AbVarFunctionField (E.baseChange L))) = n := by
  have hdimL : (E.baseChange L).dim = 1 := (PkgI3.AbVar.dim_baseChange E L).trans hdim
  obtain ⟨P', -, hp', hdim', -⟩ := abVar_identityPoleSpaces (E.baseChange L) hdimL
  have hP : P' = PL := TauCeti.Place.integers_injective
    (ValuationSubring.toSubring_injective (hp'.symm.trans hpL))
  subst hP
  exact ⟨fun n => TauCeti.finiteDimensional_riemannRochSpace (abVar_isFunctionField _ hdimL) _,
    hdim'⟩

/-- **The inputs `X', Y'` of the per-place assembly** (the N11-inst data): the Weierstrass
equation of `W_L`, the pole orders `2, 3` at `P_L`, regularity off `P_L`, and `tG ↦ −X'/Y'`. -/
theorem treeH3_n11Inst {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] (hdim : E.dim = 1) (D : ShortData E) (𝒢 : GroupModel E L)
    (hη : D.etaW 𝒢 ≠ 0) (PL : TauCeti.Place L (AbVarFunctionField (E.baseChange L)))
    (hpL : (algebraMap ((E.baseChange L).X.left.presheaf.stalk
        (abVarIdentity (E.baseChange L))) (AbVarFunctionField (E.baseChange L))).range =
      PL.integers.toSubring) :
    ((D.W.map (algebraMap K L)).baseChange
        (AbVarFunctionField (E.baseChange L))).toAffine.Equation
        (treeH3Iota E L D.X) (treeH3Iota E L D.Y) ∧
      PL.valuation (treeH3Iota E L D.X) = WithZero.exp (1 : ℤ) ^ 2 ∧
      PL.valuation (treeH3Iota E L D.Y) = WithZero.exp (1 : ℤ) ^ 3 ∧
      treeH3Iota E L D.X ∈ regularAway PL ∧ treeH3Iota E L D.Y ∈ regularAway PL ∧
      algebraMap ((E.baseChange L).X.left.presheaf.stalk (abVarIdentity (E.baseChange L)))
          (AbVarFunctionField (E.baseChange L)) (originStalkEquiv 𝒢 (D.tG 𝒢 : 𝒢.genStalk)) =
        -treeH3Iota E L D.X / treeH3Iota E L D.Y := by
  obtain ⟨hx, hy⟩ := treeH3_valuation D 𝒢 hη PL hpL
  obtain ⟨hxS, hyS⟩ := treeH3_regularAway hdim D PL hpL
  exact ⟨treeH3_equation L D, hx, hy, hxS, hyS, treeH3_param D 𝒢⟩

/-- **The N11-inst instance.** A second Weierstrass pair `(x₀, y₀)` of `W₀/L` in `K(E_L)`,
regular off `P_L` with pole orders `2, 3` at `P_L`, differs from `(X', Y')` by one change of
variables `C`, and `C⁻¹ • W_L = W₀`. -/
theorem treeH3_exists_variableChange {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type}
    [Field L] [NumberField L] [Algebra K L] (hdim : E.dim = 1) (D : ShortData E)
    (𝒢 : GroupModel E L) (hη : D.etaW 𝒢 ≠ 0)
    (PL : TauCeti.Place L (AbVarFunctionField (E.baseChange L)))
    (hpL : (algebraMap ((E.baseChange L).X.left.presheaf.stalk
        (abVarIdentity (E.baseChange L))) (AbVarFunctionField (E.baseChange L))).range =
      PL.integers.toSubring)
    (W₀ : WeierstrassCurve L) {x₀ y₀ : AbVarFunctionField (E.baseChange L)}
    (hW₀ : (W₀.baseChange (AbVarFunctionField (E.baseChange L))).toAffine.Equation x₀ y₀)
    (hx₀ : PL.valuation x₀ = WithZero.exp (1 : ℤ) ^ 2)
    (hy₀ : PL.valuation y₀ = WithZero.exp (1 : ℤ) ^ 3) (hx₀S : x₀ ∈ regularAway PL)
    (hy₀S : y₀ ∈ regularAway PL) :
    ∃ C : WeierstrassCurve.VariableChange L, C • W₀ = D.W.map (algebraMap K L) ∧
      C⁻¹ • D.W.map (algebraMap K L) = W₀ ∧
      x₀ = algebraMap L (AbVarFunctionField (E.baseChange L)) (↑C.u ^ 2) * treeH3Iota E L D.X +
        algebraMap L (AbVarFunctionField (E.baseChange L)) C.r ∧
      y₀ = algebraMap L (AbVarFunctionField (E.baseChange L)) (↑C.u ^ 3) * treeH3Iota E L D.Y +
        algebraMap L (AbVarFunctionField (E.baseChange L)) (C.s * ↑C.u ^ 2) *
          treeH3Iota E L D.X + algebraMap L (AbVarFunctionField (E.baseChange L)) C.t := by
  obtain ⟨hfd, hdimP⟩ := treeH3_poleSpaces hdim PL hpL
  obtain ⟨hW, hx, hy, hxS, hyS, -⟩ := treeH3_n11Inst hdim D 𝒢 hη PL hpL
  exact exists_variableChange_of_riemannRoch PL hfd hdimP _ W₀ hW hW₀ hx hy hx₀ hy₀ hxS hyS
    hx₀S hy₀S

end Tree

end ZInQ.Contrib.CMHeight62Full

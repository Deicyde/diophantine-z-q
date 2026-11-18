import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Cochains
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality

/-!
# Lane RC26: the all-degree continuous cochain complex in degrees `≤ 2`

The complex `C^•_cont(G, M)` of continuous inhomogeneous cochains (`contCochains k G M`, the
subcomplex of Mathlib's `groupCohomology.inhomogeneousCochains (Rep.ofDistribMulAction k G M)`
formed by the continuous cochains `Gⁿ → M`) has cohomology `Hⁿ_cont(G, M) = contCohomology k G M n`
in every degree. In degrees `0, 1, 2` the inhomogeneous description of Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, 2nd ed., Ch. I §2, reads

```text
H⁰(G, M) = M^G,   H¹(G, M) = Z¹/B¹,   H²(G, M) = Z²/B²,
```

with `Zⁱ` the continuous `i`-cocycles `Gⁱ → M` and `Bⁱ` the differentials of continuous
`(i-1)`-cochains. Tau Ceti's explicit low-degree complex (`TauCeti.ContCohomology.H0`, `H1`, `H2`)
is exactly this description. This file identifies the two, for a topological group `G` and a
discrete `G`-module `M` which is a module over an arbitrary commutative ring `k`.

## Main definitions and statements

* `homologyAddEquivOfSurjective`: a recognition principle — the homology of a cochain complex of
  `k`-modules in degree `j` is any additive group `Q` receiving a surjective additive map from the
  `j`-cocycles `ker d` whose kernel is the image of the incoming differential (imitating Mathlib's
  `groupCohomology.isoH1`, through `ShortComplex.moduleCatHomologyIso` and
  `HomologicalComplex.homologyIsoSc'`); `homologyAddEquivOfSurjective_homologyπ` computes it on the
  class of a cycle.
* `contFun_d01`, `contFun_d12`, `contFun_d23`: the differentials of `C^•_cont(G, M)` in degrees
  `0, 1, 2`, in the usual inhomogeneous form.
* `contH0AddEquiv : contCohomology k G M 0 ≃+ H0 G M` (invariants), with
  `contH0AddEquiv_homologyπ`.
* `contH1AddEquiv : contCohomology k G M 1 ≃+ H1 G M`, with `contH1AddEquiv_homologyπ`: the class of
  a continuous cocycle `c` goes to the class of `g ↦ c (fun _ => g)`.
* `contH2AddEquiv : contCohomology k G M 2 ≃+ H2 G M`, with `contH2AddEquiv_homologyπ`: the class of
  `c` goes to the class of `(g, h) ↦ c ![g, h]`.
* `contH1AddEquiv_naturality`, `contH2AddEquiv_naturality`: compatibility with the cochain maps of
  compatible pairs (`contCochainsMap`) against Tau Ceti's pullbacks `explicitMap1`,
  `explicitMap2`; `contH1AddEquiv_res`, `contH2AddEquiv_res` for restriction (`resCochains`).
* For `k = ℤ`: `contH1AddEquivContinuousCohomology` and (for locally compact `G`)
  `contH2AddEquivContinuousCohomology`, identifying `Hⁱ_cont(G, M)` for `i = 1, 2` with Mathlib's
  `continuousCohomology i (TauCeti.ofDiscreteModule ℤ G M)`, by composing with Tau Ceti's
  comparison isomorphisms.

All declarations are definitions or proved statements.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory

/-! ### Recognising homology of complexes of modules -/

section Recognition

variable {k : Type} [CommRing k]

/-- A cycle of a short complex `S` of `k`-modules, read as an element of the kernel of `S.g`. -/
def cyclesToKer (S : ShortComplex (ModuleCat.{0} k)) (c : S.cycles) : LinearMap.ker S.g.hom :=
  ⟨S.iCycles.hom c, by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, S.iCycles_g]
    rfl⟩

/-- The underlying element of `cyclesToKer`. -/
@[simp]
theorem cyclesToKer_coe (S : ShortComplex (ModuleCat.{0} k)) (c : S.cycles) :
    (cyclesToKer S c : S.X₂) = S.iCycles.hom c :=
  rfl

/-- If `ψ : ker S.g → Q` is a surjective additive map whose kernel is the image of `S.f`, then
`ker S.g ⧸ im S.f`, the concrete homology of `S`, is additively isomorphic to `Q`. -/
def kerQuotAddEquivOfSurjective (S : ShortComplex (ModuleCat.{0} k)) {Q : Type*}
    [AddCommGroup Q] (ψ : LinearMap.ker S.g.hom →+ Q) (hψ : Function.Surjective ψ)
    (hker : ∀ x, ψ x = 0 ↔ ∃ y : S.X₁, S.f.hom y = (x : S.X₂)) :
    (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) ≃+ Q :=
  QuotientAddGroup.liftEquiv (LinearMap.range S.moduleCatToCycles).toAddSubgroup hψ (by
      ext x
      rw [Submodule.mem_toAddSubgroup, LinearMap.mem_range, AddMonoidHom.mem_ker, hker]
      exact exists_congr fun y => Subtype.ext_iff)

/-- `kerQuotAddEquivOfSurjective` sends the class of `x` to `ψ x`. -/
theorem kerQuotAddEquivOfSurjective_mk (S : ShortComplex (ModuleCat.{0} k)) {Q : Type*}
    [AddCommGroup Q] (ψ : LinearMap.ker S.g.hom →+ Q) (hψ : Function.Surjective ψ)
    (hker : ∀ x, ψ x = 0 ↔ ∃ y : S.X₁, S.f.hom y = (x : S.X₂)) (x : LinearMap.ker S.g.hom) :
    kerQuotAddEquivOfSurjective S ψ hψ hker (Submodule.Quotient.mk x) = ψ x :=
  rfl

/-- **Recognition of the homology of a short complex of modules.** If `ψ : ker S.g → Q` is a
surjective additive map whose kernel is the image of `S.f`, then `S.homology ≃+ Q`. -/
def shortComplexHomologyAddEquiv (S : ShortComplex (ModuleCat.{0} k)) {Q : Type*}
    [AddCommGroup Q] (ψ : LinearMap.ker S.g.hom →+ Q) (hψ : Function.Surjective ψ)
    (hker : ∀ x, ψ x = 0 ↔ ∃ y : S.X₁, S.f.hom y = (x : S.X₂)) : S.homology ≃+ Q :=
  S.moduleCatHomologyIso.toLinearEquiv.toAddEquiv.trans (kerQuotAddEquivOfSurjective S ψ hψ hker)

/-- `shortComplexHomologyAddEquiv` sends the class of a cycle `c` to `ψ c`. -/
theorem shortComplexHomologyAddEquiv_homologyπ (S : ShortComplex (ModuleCat.{0} k)) {Q : Type*}
    [AddCommGroup Q] (ψ : LinearMap.ker S.g.hom →+ Q) (hψ : Function.Surjective ψ)
    (hker : ∀ x, ψ x = 0 ↔ ∃ y : S.X₁, S.f.hom y = (x : S.X₂)) (c : S.cycles) :
    shortComplexHomologyAddEquiv S ψ hψ hker (S.homologyπ.hom c) = ψ (cyclesToKer S c) := by
  have h1 := congr($(S.π_moduleCatCyclesIso_hom).hom c)
  have h2 := congr($(S.moduleCatCyclesIso_hom_i).hom c)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  have h3 : S.moduleCatCyclesIso.hom.hom c = cyclesToKer S c := Subtype.ext h2
  change kerQuotAddEquivOfSurjective S ψ hψ hker
    (S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom c)) = _
  rw [h1, h3]
  rfl

/-- **Recognition of the homology of a cochain complex of modules in degree `j`.** Let `i → j → l`
be the incoming and outgoing indices at `j`. If `ψ : ker d^{j,l} → Q` is a surjective additive map
whose kernel is the image of `d^{i,j}`, then `K.homology j ≃+ Q`. -/
def homologyAddEquivOfSurjective (K : CochainComplex (ModuleCat.{0} k) ℕ) (i j l : ℕ)
    (hi : (ComplexShape.up ℕ).prev j = i) (hl : (ComplexShape.up ℕ).next j = l)
    {Q : Type*} [AddCommGroup Q]
    (ψ : LinearMap.ker (K.d j l).hom →+ Q) (hψ : Function.Surjective ψ)
    (hker : ∀ x, ψ x = 0 ↔ ∃ y : K.X i, (K.d i j).hom y = (x : K.X j)) : K.homology j ≃+ Q :=
  (K.homologyIsoSc' i j l hi hl).toLinearEquiv.toAddEquiv.trans
    (shortComplexHomologyAddEquiv (K.sc' i j l) ψ hψ hker)

/-- `homologyAddEquivOfSurjective` sends the class of a cycle `c` to `ψ` of its underlying
cocycle. -/
theorem homologyAddEquivOfSurjective_homologyπ (K : CochainComplex (ModuleCat.{0} k) ℕ)
    (i j l : ℕ) (hi : (ComplexShape.up ℕ).prev j = i) (hl : (ComplexShape.up ℕ).next j = l)
    {Q : Type*} [AddCommGroup Q]
    (ψ : LinearMap.ker (K.d j l).hom →+ Q) (hψ : Function.Surjective ψ)
    (hker : ∀ x, ψ x = 0 ↔ ∃ y : K.X i, (K.d i j).hom y = (x : K.X j)) (c : K.cycles j) :
    homologyAddEquivOfSurjective K i j l hi hl ψ hψ hker ((K.homologyπ j).hom c) =
      ψ ⟨(K.iCycles j).hom c, by
        rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.iCycles_d]
        rfl⟩ := by
  have h1 := congr($(K.π_homologyIsoSc'_hom i j l hi hl).hom c)
  have h2 := congr($(K.cyclesIsoSc'_hom_iCycles i j l hi hl).hom c)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  change shortComplexHomologyAddEquiv (K.sc' i j l) ψ hψ hker
    ((K.homologyIsoSc' i j l hi hl).hom.hom ((K.homologyπ j).hom c)) = _
  rw [h1, shortComplexHomologyAddEquiv_homologyπ]
  congr 1
  exact Subtype.ext h2

/-- In the category of modules, the projection from cycles to homology is surjective. -/
theorem homologyπ_surjective_moduleCat (K : CochainComplex (ModuleCat.{0} k) ℕ) (n : ℕ) :
    Function.Surjective (K.homologyπ n).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

end Recognition

/-! ### Small vectors -/

section Vectors

variable {G : Type}

/-- A point of `G¹` is the constant family at its only coordinate. -/
private theorem fin1_eq_const (v : Fin 1 → G) : v = fun _ => v 0 := by
  funext i; rw [Subsingleton.elim i 0]

/-- A point of `G²` is the vector of its two coordinates. -/
private theorem fin2_eq_vec (v : Fin 2 → G) : v = ![v 0, v 1] := by
  funext i; fin_cases i <;> rfl

/-- A point of `G³` is the vector of its three coordinates. -/
private theorem fin3_eq_vec (v : Fin 3 → G) : v = ![v 0, v 1, v 2] := by
  funext i; fin_cases i <;> rfl

/-- The map `G × G → G²`, `(g, h) ↦ ![g, h]`, is continuous. -/
private theorem continuous_vec2 [TopologicalSpace G] :
    Continuous (fun p : G × G => ![p.1, p.2]) :=
  continuous_pi fun i => by fin_cases i; exacts [continuous_fst, continuous_snd]

end Vectors

/-! ### The explicit description in degrees `0, 1, 2` -/

section Explicit

open TauCeti.ContCohomology

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- A continuous `n`-cochain, read as a function `Gⁿ → M`. -/
abbrev contFun {n : ℕ} (x : (contCochains k G M).X n) : (Fin n → G) → M :=
  asFun k G M ((contSubCx k G M).el x : (groupCohomology.inhomogeneousCochains (rep k G M)).X n)

/-- Continuous cochains are determined by their values. -/
theorem contCochains_ext {n : ℕ} {x y : (contCochains k G M).X n}
    (h : ∀ v, contFun x v = contFun y v) : x = y :=
  Subtype.ext (funext h)

/-- The zero cochain is the zero function. -/
theorem contFun_zero_apply {n : ℕ} (v : Fin n → G) :
    contFun (0 : (contCochains k G M).X n) v = 0 :=
  rfl

/-- The differential `C⁰_cont → C¹_cont`: `(d m)(g) = g • m - m`, a `0`-cochain being a single
value (Neukirch–Schmidt–Wingberg I §2). -/
theorem contFun_d01 (x : (contCochains k G M).X 0) (g : G) :
    contFun (((contCochains k G M).d 0 1).hom x) (fun _ => g) =
      g • contFun x Fin.elim0 - contFun x Fin.elim0 := by
  rw [show contFun (((contCochains k G M).d 0 1).hom x) (fun _ => g) = _ from
    contCochains_d_apply 0 x (fun _ => g)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, zero_add, pow_one,
    neg_smul, one_smul, sub_eq_add_neg]
  rw [Subsingleton.elim (α := Fin 0 → G) (Fin.contractNth 0 _ _) Fin.elim0,
    Subsingleton.elim (α := Fin 0 → G) (fun i => g) Fin.elim0]

/-- The differential `C¹_cont → C²_cont`: `(d f)(g, h) = g • f(h) - f(gh) + f(g)`
(Neukirch–Schmidt–Wingberg I §2). -/
theorem contFun_d12 (x : (contCochains k G M).X 1) (g h : G) :
    contFun (((contCochains k G M).d 1 2).hom x) ![g, h] =
      g • contFun x (fun _ => h) - contFun x (fun _ => g * h) + contFun x (fun _ => g) := by
  rw [show contFun (((contCochains k G M).d 1 2).hom x) ![g, h] = _ from
    contCochains_d_apply 1 x ![g, h]]
  have e0 : (fun i : Fin 1 => ![g, h] i.succ) = fun _ => h := by
    funext i; fin_cases i; rfl
  have e1 : Fin.contractNth 0 (fun x1 x2 : G => x1 * x2) ![g, h] = fun _ => g * h := by
    funext i; fin_cases i; rfl
  have e2 : Fin.contractNth 1 (fun x1 x2 : G => x1 * x2) ![g, h] = fun _ => g := by
    funext i; fin_cases i; rfl
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, zero_add, pow_one, neg_smul, one_smul,
    e0, e1, e2, Nat.reduceAdd, neg_one_sq, sub_eq_add_neg, add_assoc, Matrix.cons_val_zero]

/-- The differential `C²_cont → C³_cont`:
`(d f)(g, h, j) = g • f(h, j) - f(gh, j) + f(g, hj) - f(g, h)` (Neukirch–Schmidt–Wingberg I §2). -/
theorem contFun_d23 (x : (contCochains k G M).X 2) (g h j : G) :
    contFun (((contCochains k G M).d 2 3).hom x) ![g, h, j] =
      g • contFun x ![h, j] - contFun x ![g * h, j] + contFun x ![g, h * j] -
        contFun x ![g, h] := by
  rw [show contFun (((contCochains k G M).d 2 3).hom x) ![g, h, j] = _ from
    contCochains_d_apply 2 x ![g, h, j]]
  have e0 : (fun i : Fin 2 => ![g, h, j] i.succ) = ![h, j] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth 0 (fun x1 x2 : G => x1 * x2) ![g, h, j] = ![g * h, j] := by
    funext i; fin_cases i <;> rfl
  have e2 : Fin.contractNth 1 (fun x1 x2 : G => x1 * x2) ![g, h, j] = ![g, h * j] := by
    funext i; fin_cases i <;> rfl
  have e3 : Fin.contractNth 2 (fun x1 x2 : G => x1 * x2) ![g, h, j] = ![g, h] := by
    funext i; fin_cases i <;> rfl
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, zero_add, pow_one,
    neg_smul, one_smul, e0, e1, e2, e3, Nat.reduceAdd, neg_one_sq, sub_eq_add_neg, add_assoc,
    Matrix.cons_val_zero]
  rw [show ((-1 : k) ^ 3) = -1 by ring, neg_smul, one_smul]

/-- A continuous `1`-cochain, read on `G`, is continuous. -/
theorem continuous_contFun_one (x : (contCochains k G M).X 1) :
    Continuous (fun g : G => contFun x (fun _ => g)) :=
  ((contSubCx k G M).el x).2.comp (continuous_pi fun _ => continuous_id)

/-- A continuous `2`-cochain, read on `G × G`, is continuous. -/
theorem continuous_contFun_two (x : (contCochains k G M).X 2) :
    Continuous (fun p : G × G => contFun x ![p.1, p.2]) :=
  ((contSubCx k G M).el x).2.comp continuous_vec2

/-- A continuous `1`-cochain killed by the differential is a continuous `1`-cocycle in the
explicit sense. -/
theorem mem_Z1_of_d_eq_zero (x : (contCochains k G M).X 1)
    (hx : ((contCochains k G M).d 1 2).hom x = 0) :
    (fun g : G => contFun x (fun _ => g)) ∈ Z1 G M := by
  refine mem_Z1_iff.2 ⟨continuous_contFun_one x, d1_apply_eq_zero_iff.1 ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  rw [d1_apply, ← contFun_d12, hx]
  rfl

/-- A continuous `2`-cochain killed by the differential is a continuous `2`-cocycle in the
explicit sense. -/
theorem mem_Z2_of_d_eq_zero (x : (contCochains k G M).X 2)
    (hx : ((contCochains k G M).d 2 3).hom x = 0) :
    (fun p : G × G => contFun x ![p.1, p.2]) ∈ Z2 G M := by
  refine mem_Z2_iff.2 ⟨continuous_contFun_two x, d2_apply_eq_zero_iff.1 ?_⟩
  funext p
  obtain ⟨g, h, j⟩ := p
  rw [d2_apply, ← contFun_d23, hx]
  rfl

/-- The constant `0`-cochain with value `m`. -/
def mkCochain0 (m : M) : (contCochains k G M).X 0 :=
  (⟨fun _ : Fin 0 → G => m, continuous_const⟩ : contCochain k G M 0)

/-- The value of `mkCochain0`. -/
theorem contFun_mkCochain0 (m : M) (v : Fin 0 → G) :
    contFun (mkCochain0 (k := k) (G := G) m) v = m :=
  rfl

/-- The continuous `1`-cochain `(g) ↦ c g` attached to a continuous function `c : G → M`. -/
def mkCochain1 (c : G → M) (hc : Continuous c) : (contCochains k G M).X 1 :=
  (⟨fun v : Fin 1 → G => c (v 0), hc.comp (continuous_apply 0)⟩ : contCochain k G M 1)

/-- The value of `mkCochain1`. -/
theorem contFun_mkCochain1 (c : G → M) (hc : Continuous c) (v : Fin 1 → G) :
    contFun (mkCochain1 (k := k) c hc) v = c (v 0) :=
  rfl

/-- The continuous `2`-cochain `(g, h) ↦ c (g, h)` attached to a continuous function
`c : G × G → M`. -/
def mkCochain2 (c : G × G → M) (hc : Continuous c) : (contCochains k G M).X 2 :=
  (⟨fun v : Fin 2 → G => c (v 0, v 1),
    hc.comp ((continuous_apply 0).prodMk (continuous_apply 1))⟩ : contCochain k G M 2)

/-- The value of `mkCochain2`. -/
theorem contFun_mkCochain2 (c : G × G → M) (hc : Continuous c) (v : Fin 2 → G) :
    contFun (mkCochain2 (k := k) c hc) v = c (v 0, v 1) :=
  rfl

/-! #### Degree `0` -/

/-- A continuous `0`-cocycle is an invariant: the map `ker d⁰ → M^G`, `x ↦ x()`. -/
def kerToH0 : LinearMap.ker ((contCochains k G M).d 0 1).hom →+ H0 G M where
  toFun x := ⟨contFun (x : (contCochains k G M).X 0) Fin.elim0,
    (FixedPoints.mem_addSubgroup G M _).2 fun g => by
      have h := congrArg (fun y => contFun y (fun _ => g)) x.2
      simp only [contFun_d01] at h
      exact sub_eq_zero.1 h⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Every invariant is the value of a continuous `0`-cocycle. -/
theorem kerToH0_surjective : Function.Surjective (kerToH0 (k := k) (G := G) (M := M)) := by
  intro m
  have hd : ((contCochains k G M).d 0 1).hom (mkCochain0 (k := k) (G := G) (m : M)) = 0 := by
    refine contCochains_ext fun v => ?_
    rw [fin1_eq_const v, contFun_d01, contFun_zero_apply, contFun_mkCochain0,
      (FixedPoints.mem_addSubgroup G M _).1 m.2, sub_self]
  exact ⟨⟨_, hd⟩, rfl⟩

/-- `kerToH0` is injective, matching the vanishing of the incoming differential in degree `0`. -/
theorem kerToH0_eq_zero_iff (x : LinearMap.ker ((contCochains k G M).d 0 1).hom) :
    kerToH0 x = 0 ↔ ∃ y : (contCochains k G M).X 0,
      ((contCochains k G M).d 0 0).hom y = (x : (contCochains k G M).X 0) := by
  rw [(contCochains k G M).shape 0 0 (by simp)]
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply, exists_const]
  constructor
  · intro h
    refine contCochains_ext fun v => ?_
    rw [Subsingleton.elim v Fin.elim0]
    exact (congrArg Subtype.val h).symm
  · intro h
    exact Subtype.ext (congrArg (fun y => contFun y Fin.elim0) h.symm)

variable (k G M) in
/-- **Degree `0`:** `H⁰_cont(G, M) = M^G`, the invariants (Neukirch–Schmidt–Wingberg I §2). -/
def contH0AddEquiv : contCohomology k G M 0 ≃+ H0 G M :=
  homologyAddEquivOfSurjective (contCochains k G M) 0 0 1 (by simp) (by simp) kerToH0
    kerToH0_surjective kerToH0_eq_zero_iff

/-- The class of a continuous `0`-cocycle `c` goes to its value `c()`. -/
theorem contH0AddEquiv_homologyπ (c : (contCochains k G M).cycles 0) :
    (contH0AddEquiv k G M (((contCochains k G M).homologyπ 0).hom c) : M) =
      asFun k G M ((contSubCx k G M).el (((contCochains k G M).iCycles 0).hom c) :
          (groupCohomology.inhomogeneousCochains (rep k G M)).X 0) Fin.elim0 := by
  rw [contH0AddEquiv, homologyAddEquivOfSurjective_homologyπ]
  rfl

/-! #### Degree `1` -/

/-- The class map `ker d¹ → Z¹/B¹`, `x ↦ [g ↦ x(g)]`. -/
def kerToH1 : LinearMap.ker ((contCochains k G M).d 1 2).hom →+ H1 G M :=
  (H1pi G M).comp
    { toFun := fun x => ⟨fun g => contFun (x : (contCochains k G M).X 1) (fun _ => g),
        mem_Z1_of_d_eq_zero _ x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- The defining formula for `kerToH1`. -/
theorem kerToH1_apply (x : LinearMap.ker ((contCochains k G M).d 1 2).hom) :
    kerToH1 x = H1pi G M ⟨fun g => contFun (x : (contCochains k G M).X 1) (fun _ => g),
        mem_Z1_of_d_eq_zero _ x.2⟩ :=
  rfl

/-- Every class in `Z¹/B¹` comes from a continuous inhomogeneous `1`-cocycle. -/
theorem kerToH1_surjective : Function.Surjective (kerToH1 (k := k) (G := G) (M := M)) := by
  intro z
  induction z using QuotientAddGroup.induction_on with
  | H z =>
  obtain ⟨hcont, hcoc⟩ := mem_Z1_iff.1 z.2
  have hd : ((contCochains k G M).d 1 2).hom (mkCochain1 (k := k) _ hcont) = 0 := by
    refine contCochains_ext fun v => ?_
    rw [fin2_eq_vec v, contFun_d12, contFun_zero_apply, contFun_mkCochain1, contFun_mkCochain1,
      contFun_mkCochain1]
    have := congr_fun (d1_apply_eq_zero_iff.2 hcoc) (v 0, v 1)
    rwa [d1_apply] at this
  exact ⟨⟨_, hd⟩, congrArg (H1pi G M) (Subtype.ext rfl)⟩

/-- A continuous `1`-cocycle has trivial explicit class exactly when it is the differential of a
(continuous) `0`-cochain. -/
theorem kerToH1_eq_zero_iff (x : LinearMap.ker ((contCochains k G M).d 1 2).hom) :
    kerToH1 x = 0 ↔ ∃ y : (contCochains k G M).X 0,
      ((contCochains k G M).d 0 1).hom y = (x : (contCochains k G M).X 1) := by
  rw [kerToH1_apply]
  erw [H1pi_eq_zero_iff]
  simp only [B1, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨mkCochain0 m, contCochains_ext fun v => ?_⟩
    rw [fin1_eq_const v, contFun_d01, contFun_mkCochain0]
    exact congr_fun hm (v 0)
  · rintro ⟨y, hy⟩
    refine ⟨contFun y Fin.elim0, funext fun g => ?_⟩
    rw [d0_apply, ← contFun_d01, hy]

variable (k G M) in
/-- **Degree `1`:** `H¹_cont(G, M) = Z¹/B¹`, continuous crossed homomorphisms modulo principal
ones (Neukirch–Schmidt–Wingberg I §2). -/
def contH1AddEquiv : contCohomology k G M 1 ≃+ H1 G M :=
  homologyAddEquivOfSurjective (contCochains k G M) 0 1 2 (by simp) (by simp) kerToH1
    kerToH1_surjective kerToH1_eq_zero_iff

/-- The function `g ↦ c (fun _ => g)` attached to a cycle `c` of `C^•_cont(G, M)` in degree `1`
is a continuous `1`-cocycle. -/
theorem mem_Z1_of_cycles (c : (contCochains k G M).cycles 1) :
    (fun g : G => asFun k G M ((contSubCx k G M).el (((contCochains k G M).iCycles 1).hom c) :
      (groupCohomology.inhomogeneousCochains (rep k G M)).X 1) (fun _ => g)) ∈ Z1 G M :=
  mem_Z1_of_d_eq_zero _ (by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.iCycles_d]
    rfl)

/-- `contH1AddEquiv` sends the class of a continuous inhomogeneous `1`-cocycle `c` to the class of
the crossed homomorphism `g ↦ c (fun _ => g)`. -/
theorem contH1AddEquiv_homologyπ (c : (contCochains k G M).cycles 1) :
    contH1AddEquiv k G M (((contCochains k G M).homologyπ 1).hom c) =
      H1pi G M ⟨fun g : G => asFun k G M ((contSubCx k G M).el
        (((contCochains k G M).iCycles 1).hom c) :
          (groupCohomology.inhomogeneousCochains (rep k G M)).X 1) (fun _ => g),
        mem_Z1_of_cycles c⟩ :=
  homologyAddEquivOfSurjective_homologyπ _ _ _ _ _ _ _ _ _ c

/-! #### Degree `2` -/

/-- The class map `ker d² → Z²/B²`, `x ↦ [(g, h) ↦ x(g, h)]`. -/
def kerToH2 : LinearMap.ker ((contCochains k G M).d 2 3).hom →+ H2 G M :=
  (H2pi G M).comp
    { toFun := fun x => ⟨fun p => contFun (x : (contCochains k G M).X 2) ![p.1, p.2],
        mem_Z2_of_d_eq_zero _ x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- The defining formula for `kerToH2`. -/
theorem kerToH2_apply (x : LinearMap.ker ((contCochains k G M).d 2 3).hom) :
    kerToH2 x = H2pi G M ⟨fun p => contFun (x : (contCochains k G M).X 2) ![p.1, p.2],
        mem_Z2_of_d_eq_zero _ x.2⟩ :=
  rfl

/-- Every class in `Z²/B²` comes from a continuous inhomogeneous `2`-cocycle. -/
theorem kerToH2_surjective : Function.Surjective (kerToH2 (k := k) (G := G) (M := M)) := by
  intro z
  induction z using QuotientAddGroup.induction_on with
  | H z =>
  obtain ⟨hcont, hcoc⟩ := mem_Z2_iff.1 z.2
  have hd : ((contCochains k G M).d 2 3).hom (mkCochain2 (k := k) _ hcont) = 0 := by
    refine contCochains_ext fun v => ?_
    rw [fin3_eq_vec v, contFun_d23, contFun_zero_apply, contFun_mkCochain2, contFun_mkCochain2,
      contFun_mkCochain2, contFun_mkCochain2]
    have := congr_fun (d2_apply_eq_zero_iff.2 hcoc) (v 0, v 1, v 2)
    rwa [d2_apply] at this
  exact ⟨⟨_, hd⟩, congrArg (H2pi G M) (Subtype.ext rfl)⟩

/-- A continuous `2`-cocycle has trivial explicit class exactly when it is the differential of a
continuous `1`-cochain. -/
theorem kerToH2_eq_zero_iff (x : LinearMap.ker ((contCochains k G M).d 2 3).hom) :
    kerToH2 x = 0 ↔ ∃ y : (contCochains k G M).X 1,
      ((contCochains k G M).d 1 2).hom y = (x : (contCochains k G M).X 2) := by
  rw [kerToH2_apply]
  erw [H2pi_eq_zero_iff]
  rw [mem_B2_iff]
  constructor
  · rintro ⟨c, hc, hcx⟩
    refine ⟨mkCochain1 c hc, contCochains_ext fun v => ?_⟩
    rw [fin2_eq_vec v, contFun_d12, contFun_mkCochain1, contFun_mkCochain1, contFun_mkCochain1]
    exact congr_fun hcx (v 0, v 1)
  · rintro ⟨y, hy⟩
    refine ⟨fun g => contFun y (fun _ => g), continuous_contFun_one y, funext fun p => ?_⟩
    obtain ⟨g, h⟩ := p
    rw [d1_apply]
    change _ = contFun (x : (contCochains k G M).X 2) ![g, h]
    rw [← hy, contFun_d12]

variable (k G M) in
/-- **Degree `2`:** `H²_cont(G, M) = Z²/B²`, continuous inhomogeneous `2`-cocycles modulo
differentials of continuous `1`-cochains (Neukirch–Schmidt–Wingberg I §2). -/
def contH2AddEquiv : contCohomology k G M 2 ≃+ H2 G M :=
  homologyAddEquivOfSurjective (contCochains k G M) 1 2 3 (by simp) (by simp) kerToH2
    kerToH2_surjective kerToH2_eq_zero_iff

/-- The function `(g, h) ↦ c ![g, h]` attached to a cycle `c` of `C^•_cont(G, M)` in degree `2`
is a continuous `2`-cocycle. -/
theorem mem_Z2_of_cycles (c : (contCochains k G M).cycles 2) :
    (fun p : G × G => asFun k G M ((contSubCx k G M).el (((contCochains k G M).iCycles 2).hom c) :
      (groupCohomology.inhomogeneousCochains (rep k G M)).X 2) ![p.1, p.2]) ∈ Z2 G M :=
  mem_Z2_of_d_eq_zero _ (by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.iCycles_d]
    rfl)

/-- `contH2AddEquiv` sends the class of a continuous inhomogeneous `2`-cocycle `c` to the class of
`(g, h) ↦ c ![g, h]`. -/
theorem contH2AddEquiv_homologyπ (c : (contCochains k G M).cycles 2) :
    contH2AddEquiv k G M (((contCochains k G M).homologyπ 2).hom c) =
      H2pi G M ⟨fun p : G × G => asFun k G M ((contSubCx k G M).el
        (((contCochains k G M).iCycles 2).hom c) :
          (groupCohomology.inhomogeneousCochains (rep k G M)).X 2) ![p.1, p.2],
        mem_Z2_of_cycles c⟩ :=
  homologyAddEquivOfSurjective_homologyπ _ _ _ _ _ _ _ _ _ c

end Explicit

/-! ### Naturality in compatible pairs -/

section Naturality

open TauCeti.ContCohomology

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {N : Type} [AddCommGroup N] [Module k N] [DistribMulAction H N] [SMulCommClass H k N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul H N]

/-- **Naturality of `contH1AddEquiv`.** For a compatible pair `(φ, f)` (a continuous homomorphism
`φ : H →ₜ* G` and a continuous `k`-linear `f : M → N` with `f (φ h • m) = h • f m`), the map
induced on `H¹_cont` by `c ↦ f ∘ c ∘ φ` corresponds to Tau Ceti's explicit pullback
`explicitMap1` on `Z¹/B¹` (Neukirch–Schmidt–Wingberg I §5). -/
theorem contH1AddEquiv_naturality (φ : H →ₜ* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (x : contCohomology k G M 1) :
    contH1AddEquiv k H N ((contCohomologyMap φ f hfc hf 1).hom x) =
      explicitMap1 G M H N φ f.toAddMonoidHom hfc hf (contH1AddEquiv k G M x) := by
  obtain ⟨c, rfl⟩ := homologyπ_surjective_moduleCat _ 1 x
  have h1 := congr($(HomologicalComplex.homologyπ_naturality (contCochainsMap φ f hfc hf) 1).hom c)
  have h2 := congr($(HomologicalComplex.cyclesMap_i (contCochainsMap φ f hfc hf) 1).hom c)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [contCohomologyMap, h1, contH1AddEquiv_homologyπ, contH1AddEquiv_homologyπ]
  erw [explicitMap1_mk]
  change H1pi H N _ = H1pi H N _
  congr 1
  apply Subtype.ext
  funext h
  erw [cocyclesMap1_apply]
  simp only
  rw [h2]
  rfl

/-- **Naturality of `contH2AddEquiv`** for a compatible pair `(φ, f)`, against Tau Ceti's explicit
pullback `explicitMap2` on `Z²/B²`. -/
theorem contH2AddEquiv_naturality (φ : H →ₜ* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (x : contCohomology k G M 2) :
    contH2AddEquiv k H N ((contCohomologyMap φ f hfc hf 2).hom x) =
      explicitMap2 G M H N φ f.toAddMonoidHom hfc hf (contH2AddEquiv k G M x) := by
  obtain ⟨c, rfl⟩ := homologyπ_surjective_moduleCat _ 2 x
  have h1 := congr($(HomologicalComplex.homologyπ_naturality (contCochainsMap φ f hfc hf) 2).hom c)
  have h2 := congr($(HomologicalComplex.cyclesMap_i (contCochainsMap φ f hfc hf) 2).hom c)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [contCohomologyMap, h1, contH2AddEquiv_homologyπ, contH2AddEquiv_homologyπ]
  erw [explicitMap2_mk]
  change H2pi H N _ = H2pi H N _
  congr 1
  apply Subtype.ext
  funext p
  obtain ⟨g, h⟩ := p
  erw [cocyclesMap2_apply]
  simp only
  rw [h2]
  have e : (φ : H → G) ∘ ![g, h] = ![φ g, φ h] := by
    funext i; fin_cases i <;> rfl
  exact congrArg (fun v => f (asFun k G M ((contSubCx k G M).el
    (((contCochains k G M).iCycles 2).hom c) :
      (groupCohomology.inhomogeneousCochains (rep k G M)).X 2) v)) e

omit [IsTopologicalGroup G] [DistribMulAction G M] [SMulCommClass G k M] [DiscreteTopology M]
  [ContinuousSMul G M] [IsTopologicalGroup H] in
/-- The identity `M → ResMod φ M` is continuous. -/
theorem continuous_toResMod (φ : H →ₜ* G) : Continuous (toResMod (k := k) (M := M) φ) :=
  continuous_id

/-- **Restriction in degree `1`.** Restriction `resCochains φ` along a continuous homomorphism
`φ : H →ₜ* G` corresponds, on `Z¹/B¹`, to Tau Ceti's pullback `explicitMap1` along `φ` with the
identity on coefficients. -/
theorem contH1AddEquiv_res (φ : H →ₜ* G) (x : contCohomology k G M 1) :
    contH1AddEquiv k H (ResMod φ M)
        ((HomologicalComplex.homologyMap (resCochains (k := k) (M := M) φ) 1).hom x) =
      explicitMap1 G M H (ResMod φ M) φ (toResMod (k := k) (M := M) φ).toAddMonoidHom
        (continuous_toResMod (k := k) (M := M) φ) (toResMod_compat (k := k) (M := M) φ) (contH1AddEquiv k G M x) :=
  contH1AddEquiv_naturality φ (toResMod (k := k) (M := M) φ) (continuous_toResMod (k := k) (M := M) φ)
    (toResMod_compat (k := k) (M := M) φ) x

/-- **Restriction in degree `2`**, against Tau Ceti's pullback `explicitMap2`. -/
theorem contH2AddEquiv_res (φ : H →ₜ* G) (x : contCohomology k G M 2) :
    contH2AddEquiv k H (ResMod φ M)
        ((HomologicalComplex.homologyMap (resCochains (k := k) (M := M) φ) 2).hom x) =
      explicitMap2 G M H (ResMod φ M) φ (toResMod (k := k) (M := M) φ).toAddMonoidHom
        (continuous_toResMod (k := k) (M := M) φ) (toResMod_compat (k := k) (M := M) φ) (contH2AddEquiv k G M x) :=
  contH2AddEquiv_naturality φ (toResMod (k := k) (M := M) φ) (continuous_toResMod (k := k) (M := M) φ)
    (toResMod_compat (k := k) (M := M) φ) x

end Naturality

/-! ### Comparison with Mathlib's continuous cohomology (`k = ℤ`) -/

section Comparison

open TauCeti.ContCohomology

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [DistribMulAction G M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

variable (G M) in
/-- **`H¹_cont(G, M)` is Mathlib's `continuousCohomology 1`** of the topological representation
`TauCeti.ofDiscreteModule ℤ G M` attached to the discrete module `M`: `contH1AddEquiv` followed by
Tau Ceti's comparison `explicitH1AddEquivContinuousCohomology` (inhomogeneous versus homogeneous
continuous cochains, Neukirch–Schmidt–Wingberg I §2). -/
def contH1AddEquivContinuousCohomology :
    contCohomology ℤ G M 1 ≃+ continuousCohomology 1 (TauCeti.ofDiscreteModule ℤ G M) :=
  (contH1AddEquiv ℤ G M).trans (explicitH1AddEquivContinuousCohomology G M)

/-- `contH1AddEquivContinuousCohomology` on the class of a continuous inhomogeneous `1`-cocycle. -/
theorem contH1AddEquivContinuousCohomology_homologyπ (c : (contCochains ℤ G M).cycles 1) :
    contH1AddEquivContinuousCohomology G M (((contCochains ℤ G M).homologyπ 1).hom c) =
      explicitH1AddEquivContinuousCohomology G M (H1pi G M ⟨_, mem_Z1_of_cycles c⟩) := by
  rw [contH1AddEquivContinuousCohomology, AddEquiv.trans_apply, contH1AddEquiv_homologyπ]

variable (G M) in
/-- **`H²_cont(G, M)` is Mathlib's `continuousCohomology 2`** of `TauCeti.ofDiscreteModule ℤ G M`,
for a locally compact group `G` (for instance a profinite group): `contH2AddEquiv` followed by Tau
Ceti's comparison `explicitH2AddEquivContinuousCohomology`. -/
def contH2AddEquivContinuousCohomology [LocallyCompactSpace G] :
    contCohomology ℤ G M 2 ≃+ continuousCohomology 2 (TauCeti.ofDiscreteModule ℤ G M) :=
  (contH2AddEquiv ℤ G M).trans (explicitH2AddEquivContinuousCohomology G M)

/-- `contH2AddEquivContinuousCohomology` on the class of a continuous inhomogeneous `2`-cocycle. -/
theorem contH2AddEquivContinuousCohomology_homologyπ [LocallyCompactSpace G]
    (c : (contCochains ℤ G M).cycles 2) :
    contH2AddEquivContinuousCohomology G M (((contCochains ℤ G M).homologyπ 2).hom c) =
      explicitH2AddEquivContinuousCohomology G M (H2pi G M ⟨_, mem_Z2_of_cycles c⟩) := by
  rw [contH2AddEquivContinuousCohomology, AddEquiv.trans_apply, contH2AddEquiv_homologyπ]

end Comparison

end ZInQ.Manuscript.RC.SelmerComplex

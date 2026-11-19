import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.DerivativeCoords

/-!
# RC53 SwitchInputs: the derivative sides over an arbitrary coefficient field

Manuscript `diophantine_zq.tex`, tex L5027–5083 (the derivative conditions at an inert derivative
prime: strict `D⁰`, finite `D⁰ ⊕ F[−1]`, singular `D⁰ ⊕ S[−1]`, relaxed `D⁰ ⊕ (F ⊕ S)[−1]`).

The earlier files `DerivativeSides.lean`, `DerivativeAssembly.lean` state the genuine sides over the
residue field `𝔽₂ = ZMod 2`. The switching runs at height-one primes `𝔭 ≠ (2)` of `Λ`, whose residue
fields have characteristic `0`, and there is no ring map `Λ_𝔭 → ZMod 2`
(`isEmpty_ringHom_zmod_two_heightOne`). This file restates the same constructions over an arbitrary
field `k`, with coefficients `M` any topological `k`-module with a continuous action of `G` (no
finiteness or discreteness of `M`: the fibres `V_𝔭` have neither), on the genuine continuous
cochains `C^•_cont(G, M)` over `k` of the
other team's Selmer-complex lane. Nothing here uses the characteristic of `k`; the hypothesis
`(2 : k) ≠ 0` enters only downstream (the quadratic steps, `GaloisWiringQuad.lean`).

Nodes (all PROVED, except the named GLUE input `TameCoordinatesTrivialK`):
* `Z0K`, `Z1K`, `relaxedDK` (the cocycles and `d⁰ : C⁰ → Z¹` over `k`);
* `SideCondK` (a side condition `Z⁰ ⊆ A_F`, `B_F ⊆ Z¹`, `d A_F ⊆ B_F`, inertia property `hcob`) and
  the explicit model `H1WrelK = Z¹ ⧸ d⁰C⁰` of `H¹(W_rel)`;
* `ev0K`, `ev1K`, `relaxedDK_ev` (`(d⁰a)(g) = g • a − a`);
* `sideOfSetK T` (`A = M^T`, `B = {z ∈ Z¹ | z(h) = 0, h ∈ T}`), `finiteSideK I`, `singularSideK φ`;
* `ev1K_mul_of_trivial`, `mem_Z1K_of_additive` (with the trivial action, cocycles = additive maps);
* `coordQK` (`[z] ↦ (z(φ), z(σ))`), the GLUE input `TameCoordinatesTrivialK` (bijectivity of the
  coordinates and the inertia clause; the tame structure of an inert local Galois group, to be
  discharged by the tame-model work or the Λ-adic fibres), and `coordEquivK : H1WrelK ≃ k² × k²`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory ZInQ.Contrib.CloudB3RC53.GenuineInst ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.Uniform

section Core

variable (k : Type) [Field k]
  (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction G M]
  [SMulCommClass G k M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M]
      [ContinuousSMul G M]

/-- The `0`-cocycles `Z⁰ = ker d⁰` of the genuine continuous cochains over `k`. -/
abbrev Z0K : Submodule k ((contCochains k G M).X 0) :=
  LinearMap.ker ((contCochains k G M).d 0 1).hom

/-- The `1`-cocycles `Z¹ = ker d¹` over `k`. -/
abbrev Z1K : Submodule k ((contCochains k G M).X 1) :=
  LinearMap.ker ((contCochains k G M).d 1 2).hom

/-- `d⁰ : C⁰ → Z¹` over `k`. -/
def relaxedDK : (contCochains k G M).X 0 →ₗ[k] Z1K k G M :=
  ((contCochains k G M).d 0 1).hom.codRestrict (Z1K k G M) fun x => LinearMap.mem_ker.mpr (by
    have h := congrArg (fun φ => ModuleCat.Hom.hom φ x) ((contCochains k G M).d_comp_d 0 1 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
        at h
    exact h)

/-- A side condition `[A_F → B_F]` inside the relaxed one over `k` (tex L5060–5061):
`Z⁰ ⊆ A_F ⊆ C⁰`,
`B_F ⊆ Z¹`, `d(A_F) ⊆ B_F`, and the inertia property `d a ∈ B_F → a ∈ A_F`. -/
structure SideCondK where
  AF : Submodule k ((contCochains k G M).X 0)
  BF : Submodule k (Z1K k G M)
  hZ0 : Z0K k G M ≤ AF
  hd : AF ≤ BF.comap (relaxedDK k G M)
  hcob : ∀ a, relaxedDK k G M a ∈ BF → a ∈ AF

/-- The explicit `H¹` model of `W_rel` over `k`: `Z¹ ⧸ d(C⁰)`. -/
abbrev H1WrelK : Type := Z1K k G M ⧸ LinearMap.range (relaxedDK k G M)

end Core

section Sides

variable {k : Type} [Field k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M]
  [SMulCommClass G k M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M]
      [ContinuousSMul G M]

/-- A `0`-cochain read as an element of `M`. -/
def ev0K (a : (contCochains k G M).X 0) : M :=
  asFun k G M (((contSubCx k G M).el a : contCochain k G M 0) :
    (groupCohomology.inhomogeneousCochains (rep k G M)).X 0) Fin.elim0

/-- A `1`-cochain evaluated at `g`. -/
def ev1K (z : (contCochains k G M).X 1) (g : G) : M :=
  asFun k G M (((contSubCx k G M).el z : contCochain k G M 1) :
    (groupCohomology.inhomogeneousCochains (rep k G M)).X 1) (fun _ => g)

/-- `ev0K` as a linear map. -/
def ev0LK : (contCochains k G M).X 0 →ₗ[k] M where
  toFun := ev0K
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `ev1K · g` as a linear map. -/
def ev1LK (g : G) : (contCochains k G M).X 1 →ₗ[k] M where
  toFun z := ev1K z g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **`(d⁰a)(g) = g • a − a`** over `k`. PROVED. -/
theorem relaxedDK_ev (a : (contCochains k G M).X 0) (g : G) :
    ev1K ((relaxedDK k G M a : Z1K k G M) : (contCochains k G M).X 1) g = g • ev0K a - ev0K a := by
  have h := contCochains_d_apply (k := k) (G := G) (M := M) 0 a (fun _ => g)
  have e1 : (fun i : Fin 0 => (fun _ : Fin (0 + 1) => g) i.succ) = Fin.elim0 :=
    Subsingleton.elim _ _
  have e2 : ∀ j : Fin (0 + 1), Fin.contractNth j (· * ·) (fun _ : Fin (0 + 1) => g) = Fin.elim0 :=
    fun _ => Subsingleton.elim _ _
  rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  simp only [e1, e2, Fin.val_zero, zero_add, pow_one, neg_smul, one_smul] at h
  rw [sub_eq_add_neg]
  exact h

variable (k M) in
/-- **The side condition of a set `T ⊆ G`** over `k`: `A = M^T`, `B = {z ∈ Z¹ | z(h) = 0, h ∈ T}`
(tex L5060–5082). `hcob` holds since `(d⁰a)(h) = h • a − a`. PROVED. -/
def sideOfSetK (T : Set G) : SideCondK k G M where
  AF := ⨅ h : T, LinearMap.ker ((DistribSMul.toLinearMap k M (h : G) - LinearMap.id) ∘ₗ ev0LK)
  BF := ⨅ h : T, LinearMap.ker (ev1LK (h : G) ∘ₗ (Z1K k G M).subtype)
  hZ0 := by
    intro a ha
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply,
      DistribSMul.toLinearMap_apply, LinearMap.id_apply]
    intro h
    have h0 : relaxedDK k G M a = 0 := Subtype.ext ha
    have := relaxedDK_ev a (h : G)
    rw [h0, Submodule.coe_zero] at this
    exact this.symm.trans (map_zero (ev1LK (k := k) (M := M) (h : G)))
  hd := by
    intro a ha
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply,
      DistribSMul.toLinearMap_apply, LinearMap.id_apply, Submodule.mem_comap,
      Submodule.coe_subtype] at ha ⊢
    intro h
    exact (relaxedDK_ev a (h : G)).trans (ha h)
  hcob := by
    intro a ha
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply,
      DistribSMul.toLinearMap_apply, LinearMap.id_apply, Submodule.coe_subtype] at ha ⊢
    intro h
    exact (relaxedDK_ev a (h : G)).symm.trans (ha h)

theorem mem_sideOfSetK_BF (T : Set G) (z : Z1K k G M) :
    z ∈ (sideOfSetK k M T).BF ↔ ∀ h ∈ T, ev1K (z : (contCochains k G M).X 1) h = 0 := by
  simp only [sideOfSetK, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply,
    Submodule.coe_subtype, Subtype.forall]
  rfl

variable (k M) in
/-- **The finite side** over `k`: cocycles vanishing on the inertia subgroup `I`, `A_F = M^I`
(tex L5027–5037, L5060–5061). PROVED. -/
def finiteSideK (I : Subgroup G) : SideCondK k G M := sideOfSetK k M (I : Set G)

variable (k M) in
/-- **The singular side** over `k` for a Frobenius lift `φ`: cocycles with `z(φ) = 0`,
`A_S = M^φ`. -/
def singularSideK (φ : G) : SideCondK k G M := sideOfSetK k M ({φ} : Set G)

/-- With the trivial action, a `1`-cocycle is additive: `z(gh) = z(g) + z(h)`. PROVED. -/
theorem ev1K_mul_of_trivial (htriv : ∀ (g : G) (m : M), g • m = m) (z : Z1K k G M) (g h : G) :
    ev1K (z : (contCochains k G M).X 1) (g * h) =
      ev1K (z : (contCochains k G M).X 1) g + ev1K (z : (contCochains k G M).X 1) h := by
  have hd := contCochains_d_apply (k := k) (G := G) (M := M) 1 (z : (contCochains k G M).X 1)
    ![g, h]
  have hz : ((contCochains k G M).d 1 (1 + 1)).hom (z : (contCochains k G M).X 1) = 0 := z.2
  rw [hz] at hd
  have e0 : (fun i : Fin 1 => (![g, h] : Fin 2 → G) i.succ) = fun _ => h := by
    funext i; fin_cases i; rfl
  have e1 : Fin.contractNth (0 : Fin 2) (· * ·) (![g, h] : Fin 2 → G) = fun _ => g * h := by
    funext i; fin_cases i; simp [Fin.contractNth]
  have e2 : Fin.contractNth (1 : Fin 2) (· * ·) (![g, h] : Fin 2 → G) = fun _ => g := by
    funext i; fin_cases i; simp [Fin.contractNth]
  rw [Fin.sum_univ_two, e0, e1, e2, htriv] at hd
  simp only [Fin.val_zero, Fin.val_one, zero_add, pow_one, neg_smul, one_smul] at hd
  change (0 : M) = ev1K (z : (contCochains k G M).X 1) h +
      (-ev1K (z : (contCochains k G M).X 1) (g * h) +
    (-1 : k) ^ (1 + 1) • ev1K (z : (contCochains k G M).X 1) g) at hd
  rw [show ((-1 : k) ^ (1 + 1)) = 1 by norm_num, one_smul] at hd
  rw [← sub_eq_zero]
  rw [eq_comm, ← sub_eq_zero] at hd
  rw [← neg_eq_zero, ← hd]
  abel

/-- With the trivial action, an additive `1`-cochain is a cocycle. PROVED. -/
theorem mem_Z1K_of_additive (htriv : ∀ (g : G) (m : M), g • m = m)
    (c : (contCochains k G M).X 1) (hc : ∀ g h : G, ev1K c (g * h) = ev1K c g + ev1K c h) :
    c ∈ Z1K k G M := by
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  funext g
  have hd := contCochains_d_apply (k := k) (G := G) (M := M) 1 c g
  refine hd.trans ?_
  have e0 : (fun i : Fin 1 => g i.succ) = fun _ => g 1 := by
    funext i; fin_cases i; rfl
  have e1 : Fin.contractNth (0 : Fin 2) (· * ·) g = fun _ => g 0 * g 1 := by
    funext i; fin_cases i; simp [Fin.contractNth]
  have e2 : Fin.contractNth (1 : Fin 2) (· * ·) g = fun _ => g 0 := by
    funext i; fin_cases i; simp [Fin.contractNth]
  rw [Fin.sum_univ_two, e0, e1, e2, htriv]
  change ev1K c (g 1) + ((-1 : k) ^ ((0 : ℕ) + 1) • ev1K c (g 0 * g 1) +
    (-1 : k) ^ ((1 : ℕ) + 1) • ev1K c (g 0)) = (0 : M)
  rw [hc, show ((-1 : k) ^ ((0 : ℕ) + 1)) = -1 by norm_num,
    show ((-1 : k) ^ ((1 : ℕ) + 1)) = 1 by norm_num, neg_smul, one_smul, one_smul]
  abel

/-! ### Coordinates `H¹(W_rel) ≃ k² × k²` (tex L5027–5037) -/

/-- The coordinate map `z ↦ (z(φ), z(σ))` on `1`-cocycles over `k`. -/
def coordLK (φ σ : G) : Z1K k G M →ₗ[k] M × M :=
  (ev1LK φ ∘ₗ (Z1K k G M).subtype).prod (ev1LK σ ∘ₗ (Z1K k G M).subtype)

theorem coordLK_relaxedD (φ σ : G) (hφ : ∀ m : M, φ • m = m) (hσ : ∀ m : M, σ • m = m)
    (a : (contCochains k G M).X 0) : coordLK φ σ (relaxedDK k G M a) = 0 := by
  ext
  · exact (relaxedDK_ev a φ).trans (by rw [hφ, sub_self]; rfl)
  · exact (relaxedDK_ev a σ).trans (by rw [hσ, sub_self]; rfl)

/-- The coordinate map on `H¹(W_rel) = Z¹ ⧸ d⁰C⁰` over `k` (`φ`, `σ` acting trivially). -/
def coordQK (φ σ : G) (hφ : ∀ m : M, φ • m = m) (hσ : ∀ m : M, σ • m = m) :
    H1WrelK k G M →ₗ[k] M × M :=
  (LinearMap.range (relaxedDK k G M)).liftQ (coordLK φ σ) (by
    rintro _ ⟨a, rfl⟩
    exact LinearMap.mem_ker.mpr (coordLK_relaxedD φ σ hφ hσ a))

theorem coordQK_mk (φ σ : G) (hφ : ∀ m : M, φ • m = m) (hσ : ∀ m : M, σ • m = m) (z : Z1K k G M) :
    coordQK φ σ hφ hσ (Submodule.Quotient.mk z) =
      (ev1K (z : (contCochains k G M).X 1) φ, ev1K (z : (contCochains k G M).X 1) σ) :=
  rfl

variable (k M) in
/-- **GLUE: the tame coordinates over `k`** (tex L5027–5037), in the strengthened form asked for by
the tame-quotient work: `G` acts trivially on `M` (not only `φ`, `σ`; under a nontrivial wild action
bijectivity may fail), `σ ∈ I`, the coordinate map `[z] ↦ (z(φ), z(σ))` is a bijection
`H¹ ≅ M × M`, and a cocycle with `z(σ) = 0` vanishes on `I`; and `M` has rank two
(`hrank : M ≃ k²`, the only place where the rank of `M` enters). With the trivial action,
`1`-cocycles
are the continuous homomorphisms `G → M` (`ev1K_mul_of_trivial`, `mem_Z1K_of_additive`), so this is
the tame-quotient statement `Hom_cont(G, M) ≅ M × M` through the tame quotient
`⟨φ, σ | φσφ⁻¹ = σ^q⟩` (wild inertia pro-`p`, `I/P` procyclic): the form the tame-model work
(`TameModelQIso`) or the Λ-adic fibres can discharge. Over `𝔽₂` with `p` odd it is discharged by
`tameCoordinatesTrivial_galois` (`TameUnramified.lean`). Classification: GLUE. -/
structure TameCoordinatesTrivialK (I : Subgroup G) (φ σ : G) : Prop where
  htriv : ∀ (g : G) (m : M), g • m = m
  hrank : Nonempty (M ≃ₗ[k] (Fin 2 → k))
  hσI : σ ∈ I
  hbij : Function.Bijective (coordQK (k := k) (M := M) φ σ (htriv φ) (htriv σ))
  hI : ∀ z : Z1K k G M, ev1K (z : (contCochains k G M).X 1) σ = 0 →
    ∀ h ∈ I, ev1K (z : (contCochains k G M).X 1) h = 0

/-- The coordinates `M ≃ k²` chosen from the rank-two clause of the tame coordinates. -/
def TameCoordinatesTrivialK.eM {I : Subgroup G} {φ σ : G} (T : TameCoordinatesTrivialK k M I φ σ) :
    M ≃ₗ[k] (Fin 2 → k) :=
  T.hrank.some

/-- **The coordinates** `H¹(W_rel) ≃ k² × k²` over `k`, from the tame coordinates and `M ≃ k²`. -/
def coordEquivK {I : Subgroup G} {φ σ : G} (T : TameCoordinatesTrivialK k M I φ σ)
    (eM : M ≃ₗ[k] (Fin 2 → k)) :
    H1WrelK k G M ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k) :=
  (LinearEquiv.ofBijective _ T.hbij).trans (LinearEquiv.prodCongr eM eM)

theorem coordEquivK_mk {I : Subgroup G} {φ σ : G} (T : TameCoordinatesTrivialK k M I φ σ)
    (eM : M ≃ₗ[k] (Fin 2 → k)) (z : Z1K k G M) :
    coordEquivK T eM (Submodule.Quotient.mk z) =
      (eM (ev1K (z : (contCochains k G M).X 1) φ),
        eM (ev1K (z : (contCochains k G M).X 1) σ)) :=
  rfl

end Sides

end ZInQ.Contrib.CloudB3RC53.SwitchInputs

import ZInQKernel.Contrib.OneProof.RC.KummerMaps.KummerAnn
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.Maximal

/-!
# Lane RC29, round 3 (item 2): Milne's unramified local duality, ADT I.2.6, as a PRINT

Manuscript `diophantine_zq.tex`, the support comparisons (tex 3470–3500: "the unramified complex
`[Φ−1]` in degrees zero and one"; "Use it only when the actual coefficient representation is
unramified at the removed place") and tex 3815–3816 ("The remaining good unramified conditions use
the integral unramified comparison"). At the new places `w ∈ S − S₀` of the actual data the
unramified condition is used as its own exact annihilator; round 1 of this lane took this from
Nekovář's 7.5.6 (`NekovarProp756`, `OrthUnramified.lean`). This file states the independent
published source, Milne's Theorem I.2.6, and moves it to a general perfect pairing.

**The published statement** (J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, Ch. I,
§2, p. 30, subsection "Unramified cohomology"; read in the author's PDF, whose text layer drops
some symbols — restored in brackets). In §2 (p. 26), "`K` will be a nonarchimedean local field,
complete with respect to the discrete valuation `ord : K^× ↠ ℤ`, and with finite residue field
`k`. Let `R` be the ring of integers in `K`, and let `K^un` be a largest unramified extension of
`K`. Write `G = Gal(K^s/K)` and `I = Gal(K^s/K^un)`." Then (p. 30):

> A `G`-module `M` is said to be *unramified* if `M^I = M`. For a finitely generated `G`-module,
> we write `M^d` for the submodule `Hom(M, R^{un[×]})` of `M^D = Hom(M, K^{s[×]})`. Note that if
> `M` is unramified, then `H¹(G/I, M)` makes sense and is a subgroup of `H¹(G, M)`. …
>
> THEOREM 2.6 If `M` is a finitely generated unramified `G`-module whose torsion is prime to
> `char(k)`, then the groups `H¹(G/I, M)` and `H¹(G/I, M^d)` are the exact annihilators of each
> other in the cup-product pairing `H¹(G, M) × H¹(G, M^D) → H²(G, K^{s[×]}) ≅ ℚ/ℤ`.

The proof (pp. 30–31) goes through the spectral sequence of `Ext`, and ends: "(When `M` is finite,
this result can also be proved by a counting argument; see Serre 1964, II 5.5.)" Remark 2.7
(p. 31): "A finite `G`-module `M` is unramified if and only if it extends to a finite étale group
scheme over `Spec(R)`."

**This file.**
* `UrMUnits F`: `F̄^×`, written additively, discrete, with the Galois action
  (`urMUnitsVal_smul`; `UrMUnits.instContinuousSMul`).
* `UrMDual F M`: **Milne's `M^D = Hom(M, K^{s×})`** (`Hom(M, F̄^×)`) with the action
  `(σφ)(m) = σ(φ(σ⁻¹ m))` (`urMDualHom_smul`), discrete for finite `M`
  (`UrMDual.instContinuousSMul`); `urMEv : M × M^D → F̄^×`, the evaluation pairing, equivariant
  (`urMEv_smul`).
* `urMRes F : G_F → Gal(F^ur/F)` (restriction to Tau Ceti's `maximalUnramifiedExtension`), so
  `I = ker urMRes`; `UrMInflated c`: the `1`-cochain `c` is inflated from `G/I`.
* `UrMExactAnn β`: the inflated classes on the two sides are the exact annihilators of each other
  for the cup product of `β` (cocycle form, below).
* **`MilneADT_I_2_6`** (PRINT, read): Theorem 2.6 for finite modules over local fields of
  characteristic zero.
* `urM_exactAnn_of_pairing` (PROVED from the PRINT): the same for every equivariant pairing
  `β : M × M' → F̄^×` with `M' ≅ M^D` through `β` (transport along `m' ↦ β(·, m')`).

DEPARTUREs (form; each also stated at the PRINT). (1) Scope: `F` of characteristic zero (Milne:
every nonarchimedean local field), and `M` finite (Milne: finitely generated). (2) The group:
Mathlib's `Field.absoluteGaloisGroup F = Gal(F̄/F)` (equal to Milne's `Gal(K^s/K)` in
characteristic zero) with `K^{s×} = F̄^×`; `K^un` is Tau Ceti's `maximalUnramifiedExtension F F̄`
and `G/I = Gal(K^un/K)` through restriction. (3) Cochain level, in lane RC26's continuous
inhomogeneous cochains with `ℤ` coefficients: a class of `H¹` is a continuous `1`-cocycle modulo
`B¹`; `H¹(G/I, N) ⊆ H¹(G, N)` (for `N` unramified) is the set of classes of cocycles inflated from
`G/I`, i.e. whose value at `g` depends only on `g|K^un` (`UrMInflated`; for such a cocycle the
descended function is a continuous cocycle of `G/I`, the restriction being a quotient map of
compact Hausdorff groups); the pairing vanishes when the cup product is a continuous coboundary,
the isomorphism `inv : H²(G, K^{s×}) ≅ ℚ/ℤ` of Milne I.1.6(b) being bijective. (4) `M^d = M^D` for
finite `M` of order prime to `char(k)` (every value of `φ ∈ M^D` is a root of unity of order prime
to `char(k)`, a unit of `R^un`), so `M^d` is replaced by `M^D`.

Kinds: definitions and PROVED, except `MilneADT_I_2_6` (PRINT, read).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open scoped ValuativeRel

/-! ### The multiplicative group of the algebraic closure -/

section Units

variable (F : Type) [Field F]

/-- Definition. **`F̄^×`** (Milne's `K^{s×}`; `F̄ = F^s` in characteristic zero), written
additively. A type synonym, so that the discrete topology below is the only topology on it. -/
def UrMUnits : Type := Additive (AlgebraicClosure F)ˣ

/-- Definition. The group structure of `F̄^×`, written additively. -/
instance UrMUnits.instAddCommGroup : AddCommGroup (UrMUnits F) :=
  inferInstanceAs (AddCommGroup (Additive (AlgebraicClosure F)ˣ))

/-- Definition. `F̄^×` carries the discrete topology. -/
instance UrMUnits.instTopologicalSpace : TopologicalSpace (UrMUnits F) := ⊥

/-- PROVED. The topology of `F̄^×` is discrete. -/
instance UrMUnits.instDiscreteTopology : DiscreteTopology (UrMUnits F) := ⟨rfl⟩

/-- Definition. A unit of `F̄` as an element of `UrMUnits F`. -/
def urMUnitsMk (u : (AlgebraicClosure F)ˣ) : UrMUnits F := Additive.ofMul u

/-- Definition. The value in `F̄` of an element of `UrMUnits F`. -/
def urMUnitsVal (u : UrMUnits F) : AlgebraicClosure F :=
  ((Additive.toMul (show Additive (AlgebraicClosure F)ˣ from u) : (AlgebraicClosure F)ˣ) :
    AlgebraicClosure F)

variable {F}

/-- PROVED. Elements of `UrMUnits F` are determined by their values in `F̄`. -/
theorem urMUnits_ext {u u' : UrMUnits F} (h : urMUnitsVal F u = urMUnitsVal F u') : u = u' :=
  Additive.toMul.injective (Units.ext h)

/-- PROVED. The value of `urMUnitsMk u` is `u`. -/
@[simp]
theorem urMUnitsVal_mk (u : (AlgebraicClosure F)ˣ) :
    urMUnitsVal F (urMUnitsMk F u) = (u : AlgebraicClosure F) :=
  rfl

/-- PROVED. The group law of `F̄^×` is multiplication. -/
theorem urMUnitsVal_add (u u' : UrMUnits F) :
    urMUnitsVal F (u + u') = urMUnitsVal F u * urMUnitsVal F u' :=
  rfl

/-- PROVED. The zero of `F̄^×` is `1`. -/
theorem urMUnitsVal_zero : urMUnitsVal F (0 : UrMUnits F) = 1 :=
  rfl

variable (F) in
/-- Definition. The Galois action `σ • u = σ(u)` on `F̄^×`. -/
def urMUnitsSMul (σ : Field.absoluteGaloisGroup F) (u : UrMUnits F) : UrMUnits F :=
  urMUnitsMk F (Units.map σ.toAlgHom.toRingHom.toMonoidHom
    (Additive.toMul (show Additive (AlgebraicClosure F)ˣ from u)))

/-- PROVED. The value of `σ • u` is `σ` applied to the value of `u`. -/
theorem urMUnitsVal_urMUnitsSMul (σ : Field.absoluteGaloisGroup F) (u : UrMUnits F) :
    urMUnitsVal F (urMUnitsSMul F σ u) = σ.toAlgHom (urMUnitsVal F u) :=
  rfl

/-- Definition, PROVED. **`F̄^×` is a `G_F`-module.** -/
instance UrMUnits.instDistribMulAction :
    DistribMulAction (Field.absoluteGaloisGroup F) (UrMUnits F) where
  smul := urMUnitsSMul F
  one_smul u := urMUnits_ext ((urMUnitsVal_urMUnitsSMul 1 u).trans rfl)
  mul_smul σ τ u := urMUnits_ext (by
    change urMUnitsVal F (urMUnitsSMul F (σ * τ) u) =
      urMUnitsVal F (urMUnitsSMul F σ (urMUnitsSMul F τ u))
    rw [urMUnitsVal_urMUnitsSMul, urMUnitsVal_urMUnitsSMul, urMUnitsVal_urMUnitsSMul]
    rfl)
  smul_zero σ := urMUnits_ext (by
    change urMUnitsVal F (urMUnitsSMul F σ 0) = urMUnitsVal F 0
    rw [urMUnitsVal_urMUnitsSMul, urMUnitsVal_zero]
    exact map_one σ.toAlgHom)
  smul_add σ u u' := urMUnits_ext (by
    change urMUnitsVal F (urMUnitsSMul F σ (u + u')) =
      urMUnitsVal F (urMUnitsSMul F σ u + urMUnitsSMul F σ u')
    rw [urMUnitsVal_urMUnitsSMul, urMUnitsVal_add, urMUnitsVal_add, urMUnitsVal_urMUnitsSMul,
      urMUnitsVal_urMUnitsSMul]
    exact map_mul σ.toAlgHom _ _)

/-- PROVED. **The Galois action on `F̄^×` is `σ • u = σ(u)`** on values. -/
theorem urMUnitsVal_smul (σ : Field.absoluteGaloisGroup F) (u : UrMUnits F) :
    urMUnitsVal F (σ • u) = σ.toAlgHom (urMUnitsVal F u) :=
  rfl

/-- PROVED. **`F̄^×` is a discrete `G_F`-module**: the stabilizer of `u` contains the open
stabilizer of its value in `F̄` (lane RC28's `isOpen_fix`). -/
instance UrMUnits.instContinuousSMul :
    ContinuousSMul (Field.absoluteGaloisGroup F) (UrMUnits F) := by
  refine continuousSMul_iff_stabilizer_isOpen.2 fun u => ?_
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  refine Filter.mem_of_superset ((isOpen_fix (urMUnitsVal F u)).mem_nhds rfl) ?_
  intro σ hσ
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  exact urMUnits_ext ((urMUnitsVal_smul σ u).trans hσ)

end Units

/-! ### Milne's dual `M^D = Hom(M, K^{s×})` -/

section Dual

variable (F : Type) [Field F] (M : Type) [AddCommGroup M]

/-- Definition. **Milne's dual `M^D = Hom(M, K^{s×})`** (ADT I §2, p. 28; here `Hom(M, F̄^×)`), a
type synonym of the additive maps `M → F̄^×`. -/
def UrMDual : Type := M →+ UrMUnits F

/-- Definition. The group structure of `M^D` (pointwise). -/
instance UrMDual.instAddCommGroup : AddCommGroup (UrMDual F M) :=
  inferInstanceAs (AddCommGroup (M →+ UrMUnits F))

/-- Definition. An additive map `M → F̄^×` as an element of `M^D`. -/
def urMDualMk (φ : M →+ UrMUnits F) : UrMDual F M := φ

/-- Definition. An element of `M^D` as an additive map `M → F̄^×`. -/
def urMDualHom (φ : UrMDual F M) : M →+ UrMUnits F := φ

variable {F M}

/-- PROVED. Elements of `M^D` are determined by their values. -/
theorem urMDual_ext {φ ψ : UrMDual F M} (h : ∀ m, urMDualHom F M φ m = urMDualHom F M ψ m) :
    φ = ψ :=
  AddMonoidHom.ext h

/-- PROVED. `urMDualHom ∘ urMDualMk` is the identity. -/
@[simp]
theorem urMDualHom_mk (φ : M →+ UrMUnits F) : urMDualHom F M (urMDualMk F M φ) = φ :=
  rfl

/-- PROVED. The group law of `M^D` is pointwise. -/
theorem urMDualHom_add (φ ψ : UrMDual F M) (m : M) :
    urMDualHom F M (φ + ψ) m = urMDualHom F M φ m + urMDualHom F M ψ m :=
  rfl

/-- PROVED. The zero of `M^D` is the zero map. -/
theorem urMDualHom_zero (m : M) : urMDualHom F M (0 : UrMDual F M) m = 0 :=
  rfl

variable (F M) in
/-- Definition. **The evaluation pairing `M × M^D → F̄^×`**, `(m, φ) ↦ φ(m)` (the pairing of
Milne's cup product `H¹(G, M) × H¹(G, M^D) → H²(G, K^{s×})`). -/
def urMEv : M →ₗ[ℤ] UrMDual F M →ₗ[ℤ] UrMUnits F :=
  LinearMap.mk₂ ℤ (fun m φ => urMDualHom F M φ m)
    (fun m m' φ => map_add (urMDualHom F M φ) m m')
    (fun c m φ => map_zsmul (urMDualHom F M φ) c m)
    (fun m φ ψ => urMDualHom_add φ ψ m)
    (fun _ _ _ => rfl)

/-- PROVED. The evaluation pairing evaluates. -/
theorem urMEv_apply (m : M) (φ : UrMDual F M) : urMEv F M m φ = urMDualHom F M φ m :=
  rfl

variable [DistribMulAction (Field.absoluteGaloisGroup F) M]

variable (F M) in
/-- Definition. The conjugate `m ↦ σ(φ(σ⁻¹ m))` of `φ ∈ M^D` by `σ ∈ G_F`. -/
def urMDualSMulHom (σ : Field.absoluteGaloisGroup F) (φ : UrMDual F M) : M →+ UrMUnits F where
  toFun m := σ • urMDualHom F M φ (σ⁻¹ • m)
  map_zero' := by rw [smul_zero, map_zero, smul_zero]
  map_add' m m' := by rw [smul_add, map_add, smul_add]

/-- Definition, PROVED. **`M^D` is a `G_F`-module** under `(σφ)(m) = σ(φ(σ⁻¹ m))`. -/
instance UrMDual.instDistribMulAction :
    DistribMulAction (Field.absoluteGaloisGroup F) (UrMDual F M) where
  smul σ φ := urMDualMk F M (urMDualSMulHom F M σ φ)
  one_smul φ := urMDual_ext fun m => by
    change (1 : Field.absoluteGaloisGroup F) • urMDualHom F M φ
      ((1 : Field.absoluteGaloisGroup F)⁻¹ • m) = _
    rw [inv_one, one_smul, one_smul]
  mul_smul σ τ φ := urMDual_ext fun m => by
    change (σ * τ) • urMDualHom F M φ ((σ * τ)⁻¹ • m) =
      σ • (τ • urMDualHom F M φ (τ⁻¹ • σ⁻¹ • m))
    rw [mul_inv_rev, mul_smul, mul_smul]
  smul_zero σ := urMDual_ext fun m => by
    change σ • urMDualHom F M 0 (σ⁻¹ • m) = 0
    rw [urMDualHom_zero, smul_zero]
  smul_add σ φ ψ := urMDual_ext fun m => by
    change σ • urMDualHom F M (φ + ψ) (σ⁻¹ • m) =
      σ • urMDualHom F M φ (σ⁻¹ • m) + σ • urMDualHom F M ψ (σ⁻¹ • m)
    rw [urMDualHom_add, smul_add]

/-- PROVED. **The action on `M^D`**: `(σφ)(m) = σ(φ(σ⁻¹ m))`. -/
theorem urMDualHom_smul (σ : Field.absoluteGaloisGroup F) (φ : UrMDual F M) (m : M) :
    urMDualHom F M (σ • φ) m = σ • urMDualHom F M φ (σ⁻¹ • m) :=
  rfl

/-- Definition. `M^D` carries the discrete topology. -/
instance UrMDual.instTopologicalSpace : TopologicalSpace (UrMDual F M) := ⊥

/-- PROVED. The topology of `M^D` is discrete. -/
instance UrMDual.instDiscreteTopology : DiscreteTopology (UrMDual F M) := ⟨rfl⟩

/-- PROVED. **`M^D` is a discrete `G_F`-module for a finite discrete `M`**: the stabilizer of `φ`
contains the finite intersection of the (open) stabilizers of the points `m` and of their values
`φ(m)`. -/
instance UrMDual.instContinuousSMul [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul (Field.absoluteGaloisGroup F) M] [Finite M] :
    ContinuousSMul (Field.absoluteGaloisGroup F) (UrMDual F M) := by
  refine continuousSMul_iff_stabilizer_isOpen.2 fun φ => ?_
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hopen : IsOpen (⋂ m : M,
      ((MulAction.stabilizer (Field.absoluteGaloisGroup F) m : Set (Field.absoluteGaloisGroup F)) ∩
        (MulAction.stabilizer (Field.absoluteGaloisGroup F) (urMDualHom F M φ m) :
          Set (Field.absoluteGaloisGroup F)))) :=
    isOpen_iInter_of_finite fun m =>
      (continuousSMul_iff_stabilizer_isOpen.1 inferInstance m).inter
        (continuousSMul_iff_stabilizer_isOpen.1 inferInstance (urMDualHom F M φ m))
  refine Filter.mem_of_superset (hopen.mem_nhds ?_) ?_
  · simp only [Set.mem_iInter, Set.mem_inter_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
      one_smul, and_self, implies_true]
  · intro σ hσ
    simp only [Set.mem_iInter, Set.mem_inter_iff, SetLike.mem_coe,
      MulAction.mem_stabilizer_iff] at hσ
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    refine urMDual_ext fun m => ?_
    have h1 : σ⁻¹ • m = m := by rw [inv_smul_eq_iff, (hσ m).1]
    rw [urMDualHom_smul, h1, (hσ m).2]

/-- PROVED. **The evaluation pairing is `G_F`-equivariant**: `(σφ)(σm) = σ(φ(m))`. -/
theorem urMEv_smul (σ : Field.absoluteGaloisGroup F) (m : M) (φ : UrMDual F M) :
    urMEv F M (σ • m) (σ • φ) = σ • urMEv F M m φ := by
  rw [urMEv_apply, urMEv_apply, urMDualHom_smul, inv_smul_smul]

end Dual

/-! ### The unramified quotient and the inflated classes -/

section Unramified

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Definition. **`G/I = Gal(K^un/K)`**: the Galois group of Tau Ceti's maximal unramified
extension `F^ur` of `F` inside `F̄`. -/
abbrev UrMGal : Type := Gal(TauCeti.maximalUnramifiedExtension F (AlgebraicClosure F) / F)

/-- Definition. **The restriction `G_F → Gal(F^ur/F)`**, whose kernel is the inertia group `I`. -/
def urMRes : Field.absoluteGaloisGroup F →ₜ* UrMGal F :=
  ⟨AlgEquiv.restrictNormalHom _, InfiniteGalois.restrictNormalHom_continuous _⟩

variable {F}

/-- Definition (Milne ADT I §2, p. 30: `H¹(G/I, N)` "is a subgroup of `H¹(G, N)`"). **A continuous
`1`-cochain inflated from `G/I`**: its value at `g` depends only on the restriction `g|F^ur`. -/
def UrMInflated {N : Type} [AddCommGroup N] [DistribMulAction (Field.absoluteGaloisGroup F) N]
    [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul (Field.absoluteGaloisGroup F) N]
    (c : contCochain ℤ (Field.absoluteGaloisGroup F) N 1) : Prop :=
  ∃ f : UrMGal F → N, ∀ g : Fin 1 → Field.absoluteGaloisGroup F, cfun c g = f (urMRes F (g 0))

variable (F)

/-- Definition (Milne ADT I.2.6, cocycle form). **The inflated classes on the two sides are the
exact annihilators of each other** for the cup product of `β : M × M' → T` (lane RC26's `contCup`,
`(x ∪ y)(g, h) = β(x(g), g • y(h))`): (i) cup products of inflated `1`-cocycles are coboundaries;
(ii) a `1`-cocycle of `M` whose cup products with all inflated `1`-cocycles of `M'` are coboundaries
is inflated up to a coboundary; (iii) the same with the roles of `M` and `M'` exchanged. -/
def UrMExactAnn (M M' T : Type) [AddCommGroup M] [DistribMulAction (Field.absoluteGaloisGroup F) M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M]
    [AddCommGroup M'] [DistribMulAction (Field.absoluteGaloisGroup F) M'] [TopologicalSpace M']
    [DiscreteTopology M'] [ContinuousSMul (Field.absoluteGaloisGroup F) M']
    [AddCommGroup T] [DistribMulAction (Field.absoluteGaloisGroup F) T] [TopologicalSpace T]
    [DiscreteTopology T] [ContinuousSMul (Field.absoluteGaloisGroup F) T]
    (β : M →ₗ[ℤ] M' →ₗ[ℤ] T) : Prop :=
  (∀ (x : contCochain ℤ (Field.absoluteGaloisGroup F) M 1)
      (y : contCochain ℤ (Field.absoluteGaloisGroup F) M' 1),
      contD ℤ (Field.absoluteGaloisGroup F) M 1 x = 0 →
      contD ℤ (Field.absoluteGaloisGroup F) M' 1 y = 0 → UrMInflated x → UrMInflated y →
        kannCup β x y ∈ LinearMap.range (contD ℤ (Field.absoluteGaloisGroup F) T 1)) ∧
  (∀ x : contCochain ℤ (Field.absoluteGaloisGroup F) M 1,
      contD ℤ (Field.absoluteGaloisGroup F) M 1 x = 0 →
      (∀ y : contCochain ℤ (Field.absoluteGaloisGroup F) M' 1,
        contD ℤ (Field.absoluteGaloisGroup F) M' 1 y = 0 → UrMInflated y →
          kannCup β x y ∈ LinearMap.range (contD ℤ (Field.absoluteGaloisGroup F) T 1)) →
      ∃ x₀ : contCochain ℤ (Field.absoluteGaloisGroup F) M 1,
        UrMInflated x₀ ∧ x - x₀ ∈ contB1 ℤ (Field.absoluteGaloisGroup F) M) ∧
  (∀ y : contCochain ℤ (Field.absoluteGaloisGroup F) M' 1,
      contD ℤ (Field.absoluteGaloisGroup F) M' 1 y = 0 →
      (∀ x : contCochain ℤ (Field.absoluteGaloisGroup F) M 1,
        contD ℤ (Field.absoluteGaloisGroup F) M 1 x = 0 → UrMInflated x →
          kannCup β x y ∈ LinearMap.range (contD ℤ (Field.absoluteGaloisGroup F) T 1)) →
      ∃ y₀ : contCochain ℤ (Field.absoluteGaloisGroup F) M' 1,
        UrMInflated y₀ ∧ y - y₀ ∈ contB1 ℤ (Field.absoluteGaloisGroup F) M')

/-- PROVED. Non-vacuity of `UrMInflated`: the zero cochain is inflated. -/
theorem urMInflated_zero {N : Type} [AddCommGroup N]
    [DistribMulAction (Field.absoluteGaloisGroup F) N] [TopologicalSpace N] [DiscreteTopology N]
    [ContinuousSMul (Field.absoluteGaloisGroup F) N] :
    UrMInflated (0 : contCochain ℤ (Field.absoluteGaloisGroup F) N 1) :=
  ⟨fun _ => 0, fun _ => rfl⟩

/-- PROVED. Non-vacuity of `UrMExactAnn`: zero modules. -/
theorem urMExactAnn_of_subsingleton (M M' T : Type) [AddCommGroup M]
    [DistribMulAction (Field.absoluteGaloisGroup F) M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul (Field.absoluteGaloisGroup F) M] [Subsingleton M]
    [AddCommGroup M'] [DistribMulAction (Field.absoluteGaloisGroup F) M'] [TopologicalSpace M']
    [DiscreteTopology M'] [ContinuousSMul (Field.absoluteGaloisGroup F) M'] [Subsingleton M']
    [AddCommGroup T] [DistribMulAction (Field.absoluteGaloisGroup F) T] [TopologicalSpace T]
    [DiscreteTopology T] [ContinuousSMul (Field.absoluteGaloisGroup F) T]
    (β : M →ₗ[ℤ] M' →ₗ[ℤ] T) : UrMExactAnn F M M' T β := by
  have hM : ∀ x : contCochain ℤ (Field.absoluteGaloisGroup F) M 1, x = 0 := fun x =>
    Subtype.ext (funext fun _ => @Subsingleton.elim M _ _ _)
  have hM' : ∀ y : contCochain ℤ (Field.absoluteGaloisGroup F) M' 1, y = 0 := fun y =>
    Subtype.ext (funext fun _ => @Subsingleton.elim M' _ _ _)
  refine ⟨fun x y _ _ _ _ => ?_, fun x _ _ => ⟨0, urMInflated_zero F, ?_⟩,
    fun y _ _ => ⟨0, urMInflated_zero F, ?_⟩⟩
  · rw [hM x, map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  · rw [hM x, sub_zero]
    exact Submodule.zero_mem _
  · rw [hM' y, sub_zero]
    exact Submodule.zero_mem _

end Unramified

/-! ### The PRINT -/

/-- **PRINT — J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed. (2006), Ch. I, Theorem 2.6
(p. 30)** (read in the author's PDF; cited by the manuscript as `[milne]`, Chapter I; used here for
the unramified conditions of the support comparisons, tex 3483–3498, 3815–3816): for a
nonarchimedean local field `K` with finite residue field `k`, `G = Gal(K^s/K)`, `I` its inertia
group, and a finitely generated unramified `G`-module `M` whose torsion is prime to `char(k)`, the
groups `H¹(G/I, M)` and `H¹(G/I, M^d)` are the exact annihilators of each other in the cup-product
pairing `H¹(G, M) × H¹(G, M^D) → H²(G, K^{s×}) ≅ ℚ/ℤ`, `M^D = Hom(M, K^{s×})`,
`M^d = Hom(M, R^{un×})`.

Stated for a nonarchimedean local field `F` of characteristic zero (Tau Ceti's
`IsNonarchimedeanLocalField`) and a finite discrete `G_F`-module `M` on which the inertia group acts
trivially, of order prime to the residue characteristic `ringChar 𝓀[F]`, in lane RC26's
continuous cochains: `UrMExactAnn` for the evaluation pairing `M × M^D → F̄^×`. DEPARTUREs (form):
characteristic zero and `M` finite (narrower scope); `G = Gal(F̄/F)`, `K^{s×} = F̄^×`; classes as
cocycles modulo coboundaries, `H¹(G/I, −)` as the inflated cocycles, vanishing in
`H²(G, F̄^×) ≅ ℚ/ℤ` as being a coboundary; `M^d = M^D` for finite `M` of order prime to `char(k)`
(see the module docstring). -/
def MilneADT_I_2_6 : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (M : Type) [AddCommGroup M] [DistribMulAction (Field.absoluteGaloisGroup F) M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M]
    [Finite M],
    (∀ σ : Field.absoluteGaloisGroup F, urMRes F σ = 1 → ∀ m : M, σ • m = m) →
    ¬ ringChar 𝓀[F] ∣ Nat.card M →
    UrMExactAnn F M (UrMDual F M) (UrMUnits F) (urMEv F M)

/-! ### Transport to a perfect pairing into `F̄^×` -/

section Transport

variable {F : Type} [Field F]
  {M : Type} [AddCommGroup M] [DistribMulAction (Field.absoluteGaloisGroup F) M]
  {M' : Type} [AddCommGroup M'] [DistribMulAction (Field.absoluteGaloisGroup F) M']
  (β : M →ₗ[ℤ] M' →ₗ[ℤ] UrMUnits F)
  (hβ : ∀ (σ : Field.absoluteGaloisGroup F) (a : M) (b : M'), β (σ • a) (σ • b) = σ • β a b)

/-- Definition. **The map `M' → M^D`, `m' ↦ β(·, m')`**, of a pairing `β : M × M' → F̄^×`. -/
def urMPhi : M' →+ UrMDual F M where
  toFun m' := urMDualMk F M (β.flip m').toAddMonoidHom
  map_zero' := urMDual_ext fun m => by
    change β m 0 = 0
    exact map_zero _
  map_add' a b := urMDual_ext fun m => by
    change β m (a + b) = β m a + β m b
    exact map_add _ _ _

omit [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M'] in
/-- PROVED. `urMPhi β m'` is `β(·, m')`. -/
theorem urMDualHom_urMPhi (m' : M') (m : M) : urMDualHom F M (urMPhi β m') m = β m m' :=
  rfl

include hβ in
/-- PROVED. **`m' ↦ β(·, m')` is equivariant** for an equivariant `β`. -/
theorem urMPhi_smul (σ : Field.absoluteGaloisGroup F) (m' : M') :
    urMPhi β (σ • m') = σ • urMPhi β m' := by
  refine urMDual_ext fun m => ?_
  rw [urMDualHom_urMPhi, urMDualHom_smul, urMDualHom_urMPhi, ← hβ, smul_inv_smul]

variable [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M]
  [Finite M] [TopologicalSpace M'] [DiscreteTopology M']
  [ContinuousSMul (Field.absoluteGaloisGroup F) M']

/-- PROVED. **The cup product through `β` is the cup product through the evaluation pairing**, after
pushing the second factor to `M^D` along `m' ↦ β(·, m')`. -/
theorem urM_kannCup_eq (hβ' : ∀ (σ : Field.absoluteGaloisGroup F) (m' : M'),
      urMPhi β (σ • m') = σ • urMPhi β m')
    (x : contCochain ℤ (Field.absoluteGaloisGroup F) M 1)
    (y : contCochain ℤ (Field.absoluteGaloisGroup F) M' 1) :
    kannCup β x y = kannCup (urMEv F M) x (kannPost (k' := ℤ) (urMPhi β) y) := by
  apply Subtype.ext
  funext g
  change cupFun β 1 1 2 rfl (cfun x) (cfun y) g =
    cupFun (urMEv F M) 1 1 2 rfl (cfun x) (cfun (kannPost (k' := ℤ) (urMPhi β) y)) g
  rw [cupFun_one_one_apply, cupFun_one_one_apply, cfun_kannPost, ← hβ', urMEv_apply,
    urMDualHom_urMPhi]

/-- PROVED. Pushing a cochain along an additive map is additive. -/
theorem urM_kannPost_sub {N N' : Type} [AddCommGroup N]
    [DistribMulAction (Field.absoluteGaloisGroup F) N] [TopologicalSpace N] [DiscreteTopology N]
    [ContinuousSMul (Field.absoluteGaloisGroup F) N] [AddCommGroup N']
    [DistribMulAction (Field.absoluteGaloisGroup F) N'] [TopologicalSpace N'] [DiscreteTopology N']
    [ContinuousSMul (Field.absoluteGaloisGroup F) N'] (f : N →+ N')
    (c c' : contCochain ℤ (Field.absoluteGaloisGroup F) N 1) :
    kannPost (k' := ℤ) f (c - c') = kannPost (k' := ℤ) f c - kannPost (k' := ℤ) f c' := by
  apply Subtype.ext
  funext g
  exact map_sub f _ _

/-- PROVED. Pushing a cochain along an equivariant additive map preserves `B¹`. -/
theorem urM_kannPost_mem_B1 {N N' : Type} [AddCommGroup N]
    [DistribMulAction (Field.absoluteGaloisGroup F) N] [TopologicalSpace N] [DiscreteTopology N]
    [ContinuousSMul (Field.absoluteGaloisGroup F) N] [AddCommGroup N']
    [DistribMulAction (Field.absoluteGaloisGroup F) N'] [TopologicalSpace N'] [DiscreteTopology N']
    [ContinuousSMul (Field.absoluteGaloisGroup F) N'] (f : N →+ N')
    (hf : ∀ (σ : Field.absoluteGaloisGroup F) (x : N), f (σ • x) = σ • f x)
    {c : contCochain ℤ (Field.absoluteGaloisGroup F) N 1}
    (hc : c ∈ contB1 ℤ (Field.absoluteGaloisGroup F) N) :
    kannPost (k' := ℤ) f c ∈ contB1 ℤ (Field.absoluteGaloisGroup F) N' := by
  obtain ⟨e, rfl⟩ := (mem_contB1_iff c).1 hc
  exact (mem_contB1_iff _).2 ⟨kannPost f e, (kannPost_contD_zero f hf e).symm⟩

/-- PROVED. Pushing along `f` and then along a left inverse of `f` is the identity. -/
theorem urM_kannPost_kannPost {N N' : Type} [AddCommGroup N]
    [DistribMulAction (Field.absoluteGaloisGroup F) N] [TopologicalSpace N] [DiscreteTopology N]
    [ContinuousSMul (Field.absoluteGaloisGroup F) N] [AddCommGroup N']
    [DistribMulAction (Field.absoluteGaloisGroup F) N'] [TopologicalSpace N'] [DiscreteTopology N']
    [ContinuousSMul (Field.absoluteGaloisGroup F) N'] (f : N →+ N') (f' : N' →+ N)
    (hff : ∀ x, f' (f x) = x) {n : ℕ} (c : contCochain ℤ (Field.absoluteGaloisGroup F) N n) :
    kannPost (k' := ℤ) f' (kannPost (k' := ℤ) f c) = c := by
  apply Subtype.ext
  funext g
  exact hff _

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- PROVED. Pushing a cochain along an additive map preserves inflation. -/
theorem urMInflated_kannPost {N N' : Type} [AddCommGroup N]
    [DistribMulAction (Field.absoluteGaloisGroup F) N] [TopologicalSpace N] [DiscreteTopology N]
    [ContinuousSMul (Field.absoluteGaloisGroup F) N] [AddCommGroup N']
    [DistribMulAction (Field.absoluteGaloisGroup F) N'] [TopologicalSpace N'] [DiscreteTopology N']
    [ContinuousSMul (Field.absoluteGaloisGroup F) N'] (f : N →+ N')
    {c : contCochain ℤ (Field.absoluteGaloisGroup F) N 1} (hc : UrMInflated c) :
    UrMInflated (kannPost (k' := ℤ) f c) := by
  obtain ⟨a, ha⟩ := hc
  exact ⟨fun γ => f (a γ), fun g => by rw [cfun_kannPost, ha g]⟩

include hβ in
/-- PROVED from the PRINT. **Milne's Theorem 2.6 for a perfect pairing into `F̄^×`**: if `M` is
finite, unramified, of order prime to the residue characteristic, and `β : M × M' → F̄^×` is an
equivariant pairing for which `m' ↦ β(·, m')` is a bijection `M' ≃ M^D`, then the inflated classes
of `M` and of `M'` are the exact annihilators of each other for the cup product of `β`
(transport of the PRINT along `M' ≃ M^D`). -/
theorem urM_exactAnn_of_pairing (hM : MilneADT_I_2_6) [CharZero F]
    (hur : ∀ σ : Field.absoluteGaloisGroup F, urMRes F σ = 1 → ∀ m : M, σ • m = m)
    (hord : ¬ ringChar 𝓀[F] ∣ Nat.card M) (hbij : Function.Bijective (urMPhi β)) :
    UrMExactAnn F M M' (UrMUnits F) β := by
  obtain ⟨h1, h2, h3⟩ := hM F M hur hord
  have hφ := urMPhi_smul β hβ
  let e : M' ≃+ UrMDual F M := AddEquiv.ofBijective (urMPhi β) hbij
  have he : ∀ m', e m' = urMPhi β m' := fun _ => rfl
  have hes : ∀ (σ : Field.absoluteGaloisGroup F) (φ : UrMDual F M), e.symm (σ • φ) = σ • e.symm φ := by
    intro σ φ
    apply e.injective
    rw [AddEquiv.apply_symm_apply, he, hφ, ← he, AddEquiv.apply_symm_apply]
  have hpost : ∀ y : contCochain ℤ (Field.absoluteGaloisGroup F) M' 1,
      kannPost (k' := ℤ) (urMPhi β) y = kannPost (k' := ℤ) e.toAddMonoidHom y := fun _ => rfl
  have hback : ∀ {n : ℕ} (z : contCochain ℤ (Field.absoluteGaloisGroup F) (UrMDual F M) n),
      kannPost (k' := ℤ) (urMPhi β) (kannPost (k' := ℤ) e.symm.toAddMonoidHom z) = z := by
    intro n z
    exact urM_kannPost_kannPost e.symm.toAddMonoidHom (urMPhi β)
      (fun φ => e.apply_symm_apply φ) z
  refine ⟨fun x y hx hy hix hiy => ?_, fun x hx horth => ?_, fun y hy horth => ?_⟩
  · rw [urM_kannCup_eq β hφ]
    exact h1 x _ hx (kannPost_cocycle _ hφ hy) hix (urMInflated_kannPost _ hiy)
  · refine h2 x hx fun yd hyd hiyd => ?_
    have hy' : contD ℤ (Field.absoluteGaloisGroup F) M' 1
        (kannPost (k' := ℤ) e.symm.toAddMonoidHom yd) = 0 := kannPost_cocycle _ hes hyd
    have := horth _ hy' (urMInflated_kannPost _ hiyd)
    rwa [urM_kannCup_eq β hφ, hback] at this
  · have hy' := kannPost_cocycle (k' := ℤ) (urMPhi β) hφ hy
    obtain ⟨yd₀, hiyd₀, hdiff⟩ := h3 _ hy' fun x hx hix => by
      have := horth x hx hix
      rwa [urM_kannCup_eq β hφ] at this
    refine ⟨kannPost (k' := ℤ) e.symm.toAddMonoidHom yd₀, urMInflated_kannPost _ hiyd₀, ?_⟩
    have hmem := urM_kannPost_mem_B1 e.symm.toAddMonoidHom hes hdiff
    rw [urM_kannPost_sub, hpost, urM_kannPost_kannPost e.toAddMonoidHom e.symm.toAddMonoidHom
      (fun m' => e.symm_apply_apply m')] at hmem
    exact hmem

end Transport

end ZInQ.Manuscript.RC.KummerMaps

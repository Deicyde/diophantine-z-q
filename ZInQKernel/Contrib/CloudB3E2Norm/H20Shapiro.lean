import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.Shapiro
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.Basic

/-!
# The Shapiro identification: the explicit Shapiro cochain map induces the inverse of Shapiro's
isomorphism in continuous cohomology

Manuscript `diophantine_zq.tex`, tex 3203–3250 ("Under Shapiro, followed by the equivariant
coefficient map … (H20), obtain the class `P_{I,m}` over `K`"; "These are the integral Shapiro and
transfer maps of [Nekovář, 8.1.1–8.1.6]").

The tree's `TwistedTransfer.Sh` is an explicit Shapiro cochain map from `H`-cochains in `M` to
`G`-cochains in the induced module `G/H → M` (diagonal action `indRep`), with
`coeff ∘ Sh = 𝒯_θ` (`coeff_shapiro_eq_transfer`) and `Sh` a section of restriction followed by
evaluation at the trivial coset (`shapiro_section`). The vendored Tau Ceti library proves Shapiro's
lemma in continuous cohomology for the coinduced module `Coind_H^G M` (`TauCeti.DiscreteCoind`):
`explicitShapiro1 : H¹(G, Coind_H^G M) ≃+ H¹(H, M)`, restriction followed by evaluation at `1`.

* `toCoind H F` (definition): the `G`-equivariant comparison `(G/H → M) → Coind_H^G M`,
  `F ↦ (x ↦ x • F(x⁻¹ H))`; `toCoind_smul` (PROVED, equivariance), `toCoind_apply_one`
  (evaluation at `1` is evaluation at the trivial coset), `ofCoind_toCoind` (PROVED, a left inverse
  `f ↦ (δ ↦ r_δ • f(r_δ⁻¹))`).
* `shCocycle` (definition): `g ↦ toCoind (Sh c g)` for a continuous `1`-cocycle `c` of `H`, a
  continuous `1`-cocycle of `G` with values in `Coind_H^G M` (`continuous_sh`, `isCocycle_sh`).
* **`shapiro_identification`** (PROVED): for `G` profinite, `H` open normal, `M` a discrete
  `G`-module and a section `r` with `r 1 = 1`, the class of `shCocycle c` is
  `explicitShapiro1⁻¹ [c]`: the explicit Shapiro map induces the inverse of Shapiro's
  isomorphism in continuous cohomology.
* **`shapiro_coeff_transfer`** (PROVED): every value of `shCocycle c`, read back in the induced
  module and pushed by the coefficient map (H20), is the twisted transfer `𝒯_θ(c)`: the text's
  class "Shapiro⁻¹ then (H20)" is represented by the explicit transfer (a pointwise cochain
  identity; degree one only).
* `exists_section_one` (PROVED): a normalized section exists, so `hr1` is dischargeable.
* Non-vacuity: `nonVacuity_shapiro` (the trivial group).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open TauCeti TauCeti.ContCohomology

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) [H.Normal] (hHo : IsOpen (H : Set G))
  {M : Type} [AddCommGroup M] [DistribMulAction G M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M]

/-- The action of `G` on `M` as `ℤ`-linear endomorphisms. -/
abbrev rhoZ : G →* Module.End ℤ M := DistribMulAction.toModuleEnd ℤ M

theorem rhoZ_apply (g : G) (m : M) : rhoZ (G := G) g m = g • m := rfl

include hHo in
/-- The quotient `G/H` is discrete for `H` open. -/
theorem discrete_quot : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hHo

include hHo in
/-- **The comparison** `F ↦ (x ↦ x • F(x⁻¹ H))` from the induced module to the coinduced module.
Kind: definition. -/
def toCoind (F : G ⧸ H → M) : DiscreteCoind G H M :=
  DiscreteCoind.mk G H M (fun x => x • F ((x⁻¹ : G) : G ⧸ H))
    (by
      haveI := discrete_quot H hHo
      refine (IsLocallyConstant.iff_continuous _).2 ?_
      have h2 : Continuous fun x : G => F ((x⁻¹ : G) : G ⧸ H) :=
        (continuous_of_discreteTopology (f := F)).comp
          (continuous_quotient_mk'.comp continuous_inv)
      exact continuous_id.smul h2)
    (fun u x => by
      have hq : (((u : G) * x)⁻¹ : G) = x⁻¹ * (u : G)⁻¹ := mul_inv_rev _ _
      have h1 : ((((u : G) * x)⁻¹ : G) : G ⧸ H) = ((x⁻¹ : G) : G ⧸ H) := by
        rw [hq, QuotientGroup.mk_mul,
          (QuotientGroup.eq_one_iff _).2 (H.inv_mem u.2), mul_one]
      change ((u : G) * x) • F ((((u : G) * x)⁻¹ : G) : G ⧸ H) = (u : G) • (x • F _)
      rw [h1, mul_smul])

include hHo in
theorem toCoind_apply (F : G ⧸ H → M) (x : G) :
    toCoind H hHo F x = x • F ((x⁻¹ : G) : G ⧸ H) := rfl

include hHo in
/-- Evaluation at `1` of the comparison is evaluation at the trivial coset. Kind: PROVED. -/
theorem toCoind_apply_one (F : G ⧸ H → M) : toCoind H hHo F 1 = F 1 := by
  rw [toCoind_apply, inv_one, one_smul]
  rfl

include hHo in
/-- **The comparison is `G`-equivariant** (PROVED). -/
theorem toCoind_smul (g : G) (F : G ⧸ H → M) :
    toCoind H hHo (indRep H (rhoZ (G := G) (M := M)) g F) = g • toCoind H hHo F := by
  apply DiscreteCoind.ext
  intro x
  rw [DiscreteCoind.coe_smul, toCoind_apply, toCoind_apply, indRep_apply, rhoZ_apply, ← mul_smul,
    mul_inv_rev, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]

include hHo in
/-- The comparison is additive. Kind: PROVED. -/
theorem toCoind_add (F F' : G ⧸ H → M) :
    toCoind H hHo (F + F') = toCoind H hHo F + toCoind H hHo F' := by
  apply DiscreteCoind.ext
  intro x
  rw [DiscreteCoind.coe_add, Pi.add_apply, toCoind_apply, toCoind_apply, toCoind_apply,
    Pi.add_apply, smul_add]

/-- The left inverse `f ↦ (δ ↦ r_δ • f(r_δ⁻¹))`. Kind: definition. -/
def ofCoind (r : G ⧸ H → G) (f : DiscreteCoind G H M) : G ⧸ H → M :=
  fun δ => r δ • f (r δ)⁻¹

include hHo in
/-- **`ofCoind ∘ toCoind = id`** (PROVED), for a section `r`. -/
theorem ofCoind_toCoind (r : G ⧸ H → G) (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ)
    (F : G ⧸ H → M) : ofCoind H r (toCoind H hHo F) = F := by
  funext δ
  rw [ofCoind, toCoind_apply, inv_inv, ← mul_smul, mul_inv_cancel, one_smul, hr]

section Cocycle

variable [Fintype (G ⧸ H)] (r : G ⧸ H → G) (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ)

/-- The degree-one Shapiro value `Sh(c)(g) ∈ (G/H → M)` of `c : H → M`. Kind: definition. -/
def sh1 (c : H → M) (g : G) : G ⧸ H → M :=
  Sh H r hr (rhoZ (G := G) (M := M)) 1 (fun x => c (x 0)) (fun _ => g)

/-- `Sh` in degree one, explicitly (`T_one`). Kind: PROVED. -/
theorem sh1_eq (c : H → M) (g : G) :
    sh1 H r hr c g = ∑ δ : G ⧸ H, indRep H (rhoZ (G := G) (M := M)) (r ((g : G ⧸ H) * δ))
      (iota H (c ⟨hc H r g δ, hc_mem H r hr g δ⟩)) := by
  rw [sh1, Sh, T_one]
  simp only [R_trivial]
  rfl

include hHo in
/-- **The degree-one Shapiro value is continuous in `g`** (PROVED), for `c` continuous. -/
theorem continuous_sh1 (c : H → M) (hcont : Continuous c) : Continuous (sh1 H r hr c) := by
  haveI := discrete_quot H hHo
  have hfun : sh1 H r hr c = fun g : G => ∑ δ : G ⧸ H, indRep H (rhoZ (G := G) (M := M))
      (r ((g : G ⧸ H) * δ)) (iota H (c ⟨hc H r g δ, hc_mem H r hr g δ⟩)) :=
    funext (sh1_eq H r hr c)
  rw [hfun]
  refine continuous_finsetSum _ fun δ _ => ?_
  have hq : Continuous fun g : G => ((g : G) : G ⧸ H) := continuous_quotient_mk'
  have hh : Continuous fun g : G => hc H r g δ := by
    have h1 : Continuous fun g : G => (r ((g : G ⧸ H) * δ))⁻¹ :=
      (continuous_of_discreteTopology (f := fun q : G ⧸ H => (r (q * δ))⁻¹)).comp hq
    exact (h1.mul continuous_id).mul continuous_const
  have hcm : Continuous fun g : G => c ⟨hc H r g δ, hc_mem H r hr g δ⟩ :=
    hcont.comp (hh.subtype_mk _)
  exact (continuous_of_discreteTopology
    (f := fun p : (G ⧸ H) × M => indRep H (rhoZ (G := G) (M := M)) (r (p.1 * δ)) (iota H p.2))).comp
    (hq.prodMk hcm)

/-- **The degree-one Shapiro value is a `1`-cocycle in the induced module** (PROVED), for `c` a
`1`-cocycle (from the tree's `shapiro_cochain_map`). -/
theorem sh1_cocycle (c : H → M) (hcoc : ∀ a b : H, c (a * b) = a • c b + c a) (g k : G) :
    sh1 H r hr c (g * k) = indRep H (rhoZ (G := G) (M := M)) g (sh1 H r hr c k) + sh1 H r hr c g := by
  have h := shapiro_cochain_map H r hr (rhoZ (G := G) (M := M)) 1 (fun x => c (x 0)) ![g, k]
  have hz : dInh (fun (x : H) m => (rhoZ (G := G) (M := M)) (x : G) m) 1 (fun x => c (x 0)) = 0 := by
    funext x
    simp only [dInh, Fin.sum_univ_succ, Fin.sum_univ_zero, Pi.zero_apply]
    simp [Fin.contractNth, Fin.tail]
    rw [hcoc (x 0) (x 1), Subgroup.smul_def]
    abel
  rw [hz] at h
  have h0 : Sh H r hr (rhoZ (G := G) (M := M)) (1 + 1) 0 ![g, k] = 0 := by
    simp [Sh, T, map_zero]
  rw [h0] at h
  simp only [dInh, Fin.sum_univ_succ, Fin.sum_univ_zero] at h
  simp [Fin.tail] at h
  have e0 : Fin.contractNth (0 : Fin 2) (fun x1 x2 : G => x1 * x2) ![g, k] = fun _ => g * k :=
    funext fun i => by rw [Fin.fin_one_eq_zero i]; simp [Fin.contractNth]
  have e1 : Fin.contractNth (1 : Fin 2) (fun x1 x2 : G => x1 * x2) ![g, k] = fun _ => g :=
    funext fun i => by rw [Fin.fin_one_eq_zero i]; simp [Fin.contractNth]
  have e2 : (![k] : Fin 1 → G) = fun _ => k := funext fun i => by rw [Fin.fin_one_eq_zero i]; rfl
  rw [e0, e1, e2] at h
  change indRep H (rhoZ (G := G) (M := M)) g (sh1 H r hr c k) +
    (-sh1 H r hr c (g * k) + sh1 H r hr c g) = 0 at h
  rw [← sub_eq_zero, ← neg_eq_zero, ← h]
  abel

end Cocycle

section Identification

variable [Fintype (G ⧸ H)] (r : G ⧸ H → G) (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ)

include hHo in
/-- **The explicit Shapiro cocycle in the coinduced module**: `g ↦ toCoind (Sh(c)(g))`, a continuous
`1`-cocycle of `G` with values in `Coind_H^G M`. Kind: definition. -/
def shCocycle (c : Z1 H M) : Z1 G (DiscreteCoind G H M) :=
  ⟨fun g => toCoind H hHo (sh1 H r hr (c : H → M) g), by
    refine mem_Z1_iff.2 ⟨?_, fun g k => ?_⟩
    · haveI := discrete_quot H hHo
      exact (continuous_of_discreteTopology (f := toCoind H hHo)).comp
        (continuous_sh1 H hHo r hr _ (mem_Z1_iff.1 c.2).1)
    · change toCoind H hHo (sh1 H r hr (c : H → M) (g * k)) =
        g • toCoind H hHo (sh1 H r hr (c : H → M) k) + toCoind H hHo (sh1 H r hr (c : H → M) g)
      rw [sh1_cocycle H r hr _ (fun a b => (mem_Z1_iff.1 c.2).2 a b), toCoind_add, toCoind_smul]⟩

theorem shCocycle_apply (c : Z1 H M) (g : G) :
    (shCocycle H hHo r hr c : G → DiscreteCoind G H M) g = toCoind H hHo (sh1 H r hr (c : H → M) g) :=
  rfl

include hHo in
/-- **The Shapiro image of the explicit Shapiro cocycle is `c`** (PROVED; the tree's
`shapiro_section`, for a section with `r 1 = 1`). -/
theorem shapiroCocycles1_shCocycle (hr1 : r 1 = 1) (c : Z1 H M) :
    shapiroCocycles1 G H M (shCocycle H hHo r hr c) = c := by
  apply Subtype.ext
  funext u
  rw [shapiroCocycles1_apply, shCocycle_apply, toCoind_apply_one]
  exact shapiro_section H r hr (rhoZ (G := G) (M := M)) hr1 1 (fun x => (c : H → M) (x 0))
    (fun _ => u)

variable [CompactSpace G] [TotallyDisconnectedSpace G] [ContinuousSMul H M]

include hHo in
/-- **The Shapiro identification** (PROVED; tex 3203–3206, 3245–3247): the explicit Shapiro
cochain map induces the inverse of Shapiro's isomorphism in continuous cohomology,
`[shCocycle c] = explicitShapiro1⁻¹ [c]`. -/
theorem shapiro_identification (hr1 : r 1 = 1) (c : Z1 H M) :
    (explicitShapiro1 G H M (H.isClosed_of_isOpen hHo)).symm (c : H1 H M) =
      (shCocycle H hHo r hr c : H1 G (DiscreteCoind G H M)) := by
  refine (AddEquiv.symm_apply_eq _).2 ?_
  rw [explicitShapiro1_apply, explicitMap1_mk]
  exact congrArg (fun z : Z1 H M => (z : H1 H M))
    (shapiroCocycles1_shCocycle H hHo r hr hr1 c).symm

include hHo in
/-- **Shapiro⁻¹ followed by (H20) is the twisted transfer** (PROVED; tex 3203–3250): every value of
the explicit Shapiro cocycle, read back in the induced module (`ofCoind`) and pushed by the
coefficient map (H20), is `𝒯_θ(c)`. (The reading of `shCocycle c` as a representative of
`Shapiro⁻¹ [c]` is `shapiro_identification`, which uses a normalized section `r 1 = 1`.) This is a
pointwise cochain identity; the class-level statement in the twisted target `H¹(G, M(θ))` would need
the comparison packaged as an equivariant equivalence and is not formalized here. -/
theorem shapiro_coeff_transfer {A : Type} [CommRing A] [Module A M] [SMulCommClass G A M]
    (θ : G ⧸ H →* Aˣ) (c : Z1 H M) (g : G) :
    coeff H θ (ofCoind H r ((shCocycle H hHo r hr c : G → DiscreteCoind G H M) g)) =
      T H r hr (DistribMulAction.toModuleEnd A M) θ 1 (fun x => (c : H → M) (x 0)) (fun _ => g) := by
  rw [shCocycle_apply, ofCoind_toCoind H hHo r hr]
  have h := coeff_shapiro_eq_transfer H r hr (DistribMulAction.toModuleEnd A M) θ 1
    (fun x => (c : H → M) (x 0)) (fun _ => g)
  rw [← h]
  congr 1
  funext δ
  simp only [sh1, Sh, T, R, Finset.sum_apply, LinearMap.smul_apply, indRep_apply,
    MonoidHom.one_apply, Units.val_one, one_smul, rhoZ_apply,
    DistribMulAction.toModuleEnd_apply]
  rfl

end Identification

/-- **A normalized section exists** (PROVED): `r 1 = 1`, `r δ ∈ δ`. -/
theorem exists_section_one : ∃ r : G ⧸ H → G, (∀ δ, ((r δ : G) : G ⧸ H) = δ) ∧ r 1 = 1 := by
  classical
  refine ⟨fun δ => if δ = 1 then 1 else δ.out, fun δ => ?_, by simp⟩
  by_cases h : δ = 1
  · simp [h]
  · simp [h]

/-- **Non-vacuity of the subgroup and section hypotheses of `shapiro_identification`**: the trivial
group, with `H = ⊤` open and the section `r = 1` (the remaining hypotheses — `G` profinite, `M` a
discrete `G`-module, `G/H` finite — hold for `G = G_{K,S}` and `H = G_L`). Kind: PROVED. -/
theorem nonVacuity_shapiro :
    IsOpen ((⊤ : Subgroup Unit) : Set Unit) ∧ ∃ r : Unit ⧸ (⊤ : Subgroup Unit) → Unit,
      (∀ δ, ((r δ : Unit) : Unit ⧸ (⊤ : Subgroup Unit)) = δ) ∧ r 1 = 1 :=
  ⟨isOpen_univ, fun _ => (), fun _ => Subsingleton.elim _ _, rfl⟩

end ZInQ.Contrib.CloudB3E2.NormCochain

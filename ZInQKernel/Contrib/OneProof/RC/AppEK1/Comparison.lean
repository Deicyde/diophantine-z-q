import ZInQKernel.Contrib.OneProof.RC.AppEK1.FiniteIdentity
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Cyclotomic
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Tate
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Corestriction

/-!
# The missing comparison on the retained classes

This is a named GLUE obligation and is not added as a theorem or print. Each target
is the actual degree-one continuous cohomology of a cyclotomic kernel in the fixed
`G_{ℚ,S}`, with the actual elliptic-curve torsion coefficients. The comparison must
respect reduction, corestriction and the action of Galois lifts; an arbitrary abstract
coefficient module or zero comparison does not implement these conditions.

The formulation is in the ambient support `S = prime(2NF)`, so for a primitive
level the arithmetic construction must already include inflation from its own support.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AppEK1

open CategoryTheory NumberField IsDedekindDomain SelmerComplex CoefModules LambdaCoef
open _root_.ZInQ.Manuscript.RC.Even PrintsArith ZInQ.Contrib.CloudB3RC53

section CohomologyMaps

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [DistribMulAction G M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousAdd M] [ContinuousSMul G M]

/-- Finite continuous cohomology of a subgroup with the actual restricted action. -/
abbrev subgroupH1 (U : Subgroup G) (M : Type) [AddCommGroup M] [DistribMulAction G M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] :=
  contCohomology ℤ U (ResMod (subgroupIncl U) M) 1

/-- The canonical identification of the upper subgroup with its copy in the lower group. -/
def fromNested {U V : Subgroup G} (h : V ≤ U) : V.subgroupOf U →ₜ* V where
  toMonoidHom := (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
  continuous_toFun := by
    apply continuous_induced_rng.2
    change Continuous (fun u : V.subgroupOf U => ((u.1 : U) : G))
    exact continuous_subtype_val.comp continuous_subtype_val

set_option backward.isDefEq.respectTransparency false in
/-- Corestriction between nested open subgroups of a common ambient group.
The first map only reindexes the source subgroup and the coefficients. -/
def nestedCorH1 {U V : Subgroup G} (h : V ≤ U) (hV : IsOpen (V : Set G))
    (R : RightTransversal (V.subgroupOf U)) : subgroupH1 V M ⟶ subgroupH1 U M := by
  letI : ContinuousAdd (ResMod (subgroupIncl U) M) := ⟨continuous_of_discreteTopology⟩
  letI : ContinuousAdd (ResMod (subgroupIncl (V.subgroupOf U)) (ResMod (subgroupIncl U) M)) :=
    ⟨continuous_of_discreteTopology⟩
  let f : ResMod (subgroupIncl V) M →ₗ[ℤ]
      ResMod (subgroupIncl (V.subgroupOf U)) (ResMod (subgroupIncl U) M) := LinearMap.id
  exact contCohomologyMap (G := V) (H := V.subgroupOf U) (fromNested h) f continuous_id
      (fun _ _ => rfl) 1 ≫
    R.corCohomology (k := ℤ) (M := ResMod (subgroupIncl U) M)
      (hV.preimage continuous_subtype_val) 1

/-- Inverse conjugation on a normal subgroup, for the usual deck action on cochains. -/
def deckConj (U : Subgroup G) [U.Normal] (g : G) : U →ₜ* U where
  toFun u := ⟨g⁻¹ * (u : G) * g, ‹U.Normal›.conj_mem' _ u.property g⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := continuous_induced_rng.2
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)

/-- The action of a Galois lift on subgroup cohomology: pull back by inverse conjugation
and apply the lift to the coefficient. -/
def deckH1 (U : Subgroup G) [U.Normal] (g : G) : subgroupH1 U M ⟶ subgroupH1 U M :=
  contCohomologyMap (deckConj U g)
    ({ toFun := fun z : ResMod (subgroupIncl U) M => (show M from g • (show M from z))
       map_add' := fun a b => smul_add g (show M from a) (show M from b)
       map_smul' := fun k z => smul_comm g k (show M from z) } :
      ResMod (subgroupIncl U) M →ₗ[ℤ] ResMod (subgroupIncl U) M)
    continuous_of_discreteTopology
    (by
      intro u z
      let z₀ : M := z
      change g • ((g⁻¹ * (u : G) * g) • z₀) = (u : G) • (g • z₀)
      calc
        _ = (g * (g⁻¹ * (u : G) * g)) • z₀ := (mul_smul _ _ _).symm
        _ = ((u : G) * g) • z₀ := by simp [← mul_assoc]
        _ = _ := mul_smul _ _ _) 1

end CohomologyMaps

/-- The finite places over the prime support of `2NF`. -/
def familyPlaces {N : ℕ} (fam : BinaryFamily N) : Set (HeightOneSpectrum (𝓞 ℚ)) :=
  {v | ∃ p ∈ (2 * N * supportProduct fam).primeFactors, (p : 𝓞 ℚ) ∈ v.asIdeal}

/-- Only the cyclotomic indices built from a divisor of `F) and positive dyadic level.
These include both the primitive levels and the whole family tower. -/
abbrev FamilyIndex {N : ℕ} (fam : BinaryFamily N) :=
  {m : ℕ // m ≠ 0 ∧ ∃ d n : ℕ, d ∣ supportProduct fam ∧ 0 < n ∧ m = d * 2 ^ n}

instance {N : ℕ} {fam : BinaryFamily N} (m : FamilyIndex fam) : NeZero (m : ℕ) := ⟨m.2.1⟩

/-- The genuine cyclotomic kernel, from roots of unity in `ℚ_S`. -/
abbrev cyclotomicKernel {N : ℕ} {fam : BinaryFamily N} {m : FamilyIndex fam}
    (μ : HasRootsOfUnity ℚ (familyPlaces fam) (m : ℕ)) :
    Subgroup (GKS ℚ (familyPlaces fam)) := (cycS μ).ker

local instance (S : Set (HeightOneSpectrum (𝓞 ℚ))) (E : WeierstrassCurve ℚ) (i : ℕ) :
    TopologicalSpace (Lev ℚ S E i) := ⊥

local instance (S : Set (HeightOneSpectrum (𝓞 ℚ))) (E : WeierstrassCurve ℚ) (i : ℕ) :
    DiscreteTopology (Lev ℚ S E i) := ⟨rfl⟩

local instance (S : Set (HeightOneSpectrum (𝓞 ℚ))) (E : WeierstrassCurve ℚ) (i : ℕ) :
    ContinuousAdd (Lev ℚ S E i) := ⟨continuous_of_discreteTopology⟩

local instance (S : Set (HeightOneSpectrum (𝓞 ℚ))) (E : WeierstrassCurve ℚ) (i : ℕ) :
    ContinuousSMul (GKS ℚ S) (Lev ℚ S E i) :=
  continuousSMul_iff_stabilizer_isOpen.mpr fun P => isOpen_stabilizer_torsS P

/-- Application of the actual coefficient reduction on the restricted cohomology. -/
def reduceH1 {S : Set (HeightOneSpectrum (𝓞 ℚ))} {E : WeierstrassCurve ℚ}
    (U : Subgroup (GKS ℚ S)) (i : ℕ) :
    subgroupH1 U (Lev ℚ S E (i + 1)) ⟶ subgroupH1 U (Lev ℚ S E i) :=
  contCohomologyMap (ContinuousMonoidHom.id U)
    ((transLev ℚ S E i).toIntLinearMap :
      ResMod (subgroupIncl U) (Lev ℚ S E (i + 1)) →ₗ[ℤ] ResMod (subgroupIncl U) (Lev ℚ S E i))
    continuous_of_discreteTopology
    (by
      intro u P
      apply Subtype.ext
      change ((transLev ℚ S E i ((u : GKS ℚ S) • (show Lev ℚ S E (i + 1) from P))) :
          Pt ℚ S E) = (((u : GKS ℚ S) • transLev ℚ S E i P : Lev ℚ S E i) : Pt ℚ S E)
      rw [coe_transLev, smul_lev_coe, smul_lev_coe, coe_transLev, map_nsmul]) 1

/-- The missing arithmetic comparison at a family. `J` includes the fixed lattice
map to the elliptic Tate module and the finite-coefficient and support maps. Its kernel
over all precisions is allowed to contain (2)-primary torsion, as changing lattices
by an isogeny can kill it. This proposition does not construct (Z_F), assert (E.1)
or assert any Selmer bound. -/
def KatoFiniteComparison {E : WeierstrassCurve ℚ} {Sig Sbad : Finset ℕ}
    (K : KatoZetaInterface E Sig Sbad) {N : ℕ} (fam : BinaryFamily N)
    (μ : ∀ m : FamilyIndex fam, HasRootsOfUnity ℚ (familyPlaces fam) (m : ℕ))
    (nested : ∀ (m m' : FamilyIndex fam), (m : ℕ) ∣ (m' : ℕ) →
      cyclotomicKernel (μ m') ≤ cyclotomicKernel (μ m)) : Prop :=
  ∃ J : ∀ (m : FamilyIndex fam) (i : ℕ),
      K.es.H m →+ subgroupH1 (cyclotomicKernel (μ m)) (Lev ℚ (familyPlaces fam) E i),
    (∀ m i z, reduceH1 (cyclotomicKernel (μ m)) i (J m (i + 1) z) = J m i z) ∧
    (∀ (m m' : FamilyIndex fam) (h : (m : ℕ) ∣ (m' : ℕ))
        (R : RightTransversal ((cyclotomicKernel (μ m')).subgroupOf (cyclotomicKernel (μ m))))
        (i : ℕ) (z : K.es.H m'),
      nestedCorH1 (nested m m' h) (IsOpenKer.isOpen_ker (α := cycS (μ m'))) R (J m' i z) =
        J m i (K.es.cor m m' h z)) ∧
    (∀ m i (g : GKS ℚ (familyPlaces fam)) z,
      deckH1 (cyclotomicKernel (μ m)) g (J m i z) =
        J m i (MonoidAlgebra.of ℤ_[2] _ (cycS (μ m) g) • z)) ∧
    (∀ m z, (∀ i, J m i z = 0) → ∃ c : ℕ, (2 ^ c : ℕ) • z = 0)

/-- The comparison at the fixed curve and fixed level (N₀ ℓ =
`CST.newformLevel (Ecurve ℓ)`. No witness is supplied by the existing interface. -/
abbrev FixedKatoFiniteComparison (ℓ : ℕ) {Sig : Finset ℕ}
    (K : KatoZetaInterface (Ecurve ℓ) Sig (2 * CST.newformLevel (Ecurve ℓ)).primeFactors)
    (fam : BinaryFamily (CST.newformLevel (Ecurve ℓ)))
    (μ : ∀ m : FamilyIndex fam, HasRootsOfUnity ℚ (familyPlaces fam) (m : ℕ))
    (nested : ∀ (m m' : FamilyIndex fam), (m : ℕ) ∣ (m' : ℕ) →
      cyclotomicKernel (μ m') ≤ cyclotomicKernel (μ m)) : Prop :=
  KatoFiniteComparison K fam μ nested

/-- Once the comparison exists, the anchored signed deck sum is visible at
some finite precision in genuine continuous cohomology. To transfer this anchor
further to the specialization one must compare the signed deck sum with restriction
of the actual weighted corestriction. -/
theorem exists_nonzero_image_of_anchored_weightedSum {E : WeierstrassCurve ℚ}
    {Sig Sbad : Finset ℕ} (K : KatoZetaInterface E Sig Sbad) {N : ℕ} (fam : BinaryFamily N)
    (μ : ∀ m : FamilyIndex fam, HasRootsOfUnity ℚ (familyPlaces fam) (m : ℕ))
    (nested : ∀ (m m' : FamilyIndex fam), (m : ℕ) ∣ (m' : ℕ) →
      cyclotomicKernel (μ m') ≤ cyclotomicKernel (μ m))
    (hcomp : KatoFiniteComparison K fam μ nested)
    (m : FamilyIndex fam) (hm : KatoXi 2 Sig m)
    (χ : DirichletCharacter ℂ (m : ℕ)) (signs : (ZMod (m : ℕ))ˣ → ℤ)
    (hχ : ∀ g, (signs g : ℂ) = χ (g : ZMod (m : ℕ))) (hL : K.Lcont χ 1 ≠ 0) :
    ∃ i, hcomp.choose m i
      (∑ g : (ZMod (m : ℕ))ˣ, signs g • (MonoidAlgebra.of ℤ_[2] _ g • K.es.z m)) ≠ 0 := by
  classical
  by_contra! h
  obtain ⟨c, hc⟩ := hcomp.choose_spec.2.2.2 _ _ h
  exact anchored_weightedSum_nsmul_ne_zero K hm χ signs hχ hL
    (pow_ne_zero c (by decide)) hc

end ZInQ.Manuscript.RC.AppEK1

import ZInQKernel.Contrib.TYZGenus.ShimuraModFn
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.NormSubgroup
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.OpenSubgroup
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.ClassQuotient
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# t5-glue2, part 1: surjectivity of Tau Ceti's absolute Artin map for totally complex fields

`AbsArtinSurjective K` (verbatim copy of t5-glue's `parts/Artin.lean`) is proved for every
number field `K` without real places, in particular for `K = ℚ(√−m)` (`absArtinSurjectiveQNeg`).

Proof: compactness. `X = ⋃_q q̃ · [Ô^×]` (`q̃` representatives of `C_K / raySubgroup 1`, `Ô^×` the
units of the integral finite adeles, compact) is a compact subset of `C_K`. For each open normal
`V ≤ G_K` the fibre `{c : Art_V(c) = Art_V(g)}` is a coset of the global norm subgroup `N_V`
(Tau Ceti: kernel of the finite Artin map), which is open (Tau Ceti), hence closed. It meets `X`:
every class is `q̃ · [u] · [y]` with `y` an idele with trivial finite part, and `[y]` lies in every
ray subgroup when `K` has no real places, hence in `N_V` (Tau Ceti: every open subgroup contains a
ray subgroup). The fibres are directed (`V ⊓ W`), so they meet in `X`; a point of the intersection
has absolute Artin symbol `g` (Tau Ceti: elements of `G_K^ab` are determined by their finite
projections).
-/

noncomputable section

namespace T5Glue2

open NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory IsDedekindDomain

/-- **(verbatim copy of t5-glue `AbsArtinSurjective`)** GLUE ABS-ARTIN-SURJ. -/
def AbsArtinSurjective (K : Type) [Field K] [NumberField K] : Prop :=
  ∀ g : TauCeti.AbsoluteGaloisGroup K, ∃ c : IdeleClassGroup (𝓞 K) K,
    Additive.ofMul (g : TopologicalAbelianization (TauCeti.AbsoluteGaloisGroup K)) =
      (globalClassFormation K).absoluteArtinMap (globalGroundEquiv K (Additive.ofMul c))

section General

variable {K : Type} [Field K] [NumberField K]

local notation "CK" => IdeleClassGroup (𝓞 K) K
local notation "GabK" => Additive (TopologicalAbelianization (TauCeti.AbsoluteGaloisGroup K))

/-- The absolute Artin symbol of an idele class. -/
def art (c : CK) : GabK :=
  (globalClassFormation K).absoluteArtinMap (globalGroundEquiv K (Additive.ofMul c))

theorem art_mul (c d : CK) : art (c * d) = art c + art d := by
  simp only [art, ofMul_mul, map_add]

/-- The finite projection of the Artin symbol vanishes exactly on the global norm subgroup. -/
theorem abRestr_art_eq_zero_iff (V : OpenNormalSubgroup (TauCeti.AbsoluteGaloisGroup K)) (c : CK) :
    NormalLayer.abelianizationRestrict V (art c) = 0 ↔ c ∈ globalNormSubgroup K V :=
  (globalClassFormation K).abelianizationRestrict_absoluteArtinMap_eq_zero_iff V _

theorem abRestr_art_mul_of_mem (V : OpenNormalSubgroup (TauCeti.AbsoluteGaloisGroup K)) (c : CK)
    {n : CK} (hn : n ∈ globalNormSubgroup K V) :
    NormalLayer.abelianizationRestrict V (art (c * n)) =
      NormalLayer.abelianizationRestrict V (art c) := by
  rw [art_mul, map_add, (abRestr_art_eq_zero_iff V n).2 hn, add_zero]

/-- The fibres of a finite projection of the Artin map are closed (cosets of an open subgroup). -/
theorem isClosed_fibre (V : OpenNormalSubgroup (TauCeti.AbsoluteGaloisGroup K)) (y) :
    IsClosed {c : CK | NormalLayer.abelianizationRestrict V (art c) = y} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro c hc
  refine ⟨{x | c⁻¹ * x ∈ (globalNormSubgroup K V : Set CK)}, ?_, ?_, ?_⟩
  · intro x hx hxy
    apply hc
    have hx' : x = c * (c⁻¹ * x) := (mul_inv_cancel_left c x).symm
    show NormalLayer.abelianizationRestrict V (art c) = y
    rw [← hxy, hx', abRestr_art_mul_of_mem V c hx]
  · have h := (isOpen_globalNormSubgroup K V).preimage (Homeomorph.mulLeft c⁻¹).continuous
    exact h
  · show c⁻¹ * c ∈ globalNormSubgroup K V
    rw [inv_mul_cancel]; exact one_mem _

/-- Every finite projection of the Artin map is onto. -/
theorem exists_abRestr_art_eq (V : OpenNormalSubgroup (TauCeti.AbsoluteGaloisGroup K)) (y : GabK) :
    ∃ c : CK, NormalLayer.abelianizationRestrict V (art c) =
      NormalLayer.abelianizationRestrict V y := by
  obtain ⟨a', ha'⟩ := (globalClassFormation K).surjective_artinMap (NormalLayer.ofOpenNormal V)
    (NormalLayer.abelianizationRestrict V y)
  obtain ⟨a, rfl⟩ := (NormalLayer.groundEquivOfOpenNormal (globalFormation K) V).surjective a'
  obtain ⟨c, rfl⟩ := (globalGroundEquiv K).surjective a
  refine ⟨c.toMul, ?_⟩
  rw [art, ofMul_toMul, ClassFormation.abelianizationRestrict_absoluteArtinMap, ha']

/-- The image of the units of the integral finite adeles in `C_K`. -/
def unitSet : Set ((FiniteAdeleRing (𝓞 K) K)ˣ) :=
  ((FiniteAdeleRing.integralAdeles (𝓞 K) K).toSubmonoid.units : Set _)

/-- The class of the idele with finite part `u` and trivial infinite part. -/
def toCl (u : (FiniteAdeleRing (𝓞 K) K)ˣ) : CK :=
  ((IdeleGroup.ofFiniteIdele (𝓞 K) K u : IdeleGroup (𝓞 K) K) : CK)

theorem continuous_toCl : Continuous (toCl (K := K)) := by
  refine continuous_quot_mk.comp ?_
  exact Continuous.units_map _ (continuous_const.prodMk continuous_id)

theorem isCompact_unitSet : IsCompact (unitSet (K := K)) :=
  Submonoid.units_isCompact FiniteAdeleRing.isCompact_integralAdeles

/-- The compact set `X = ⋃_q q̃ · [Ô^×]`. -/
def compactX : Set CK :=
  ⋃ q : CK ⧸ raySubgroup (Modulus.one K), (fun c => Quotient.out q * c) '' (toCl '' unitSet)

theorem isCompact_compactX : IsCompact (compactX (K := K)) := by
  refine isCompact_iUnion fun q => ?_
  exact (isCompact_unitSet.image continuous_toCl).image (Homeomorph.mulLeft (Quotient.out q)).continuous

theorem toFiniteIdele_mem_integralAdeles {x : IdeleGroup (𝓞 K) K}
    (hx : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1) :
    ((IdeleGroup.toFiniteIdele (𝓞 K) K x : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) ∈
      FiniteAdeleRing.integralAdeles (𝓞 K) K := by
  intro v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (hx v).le

theorem ideleFiniteCoord_eq_one {y : IdeleGroup (𝓞 K) K}
    (hy : IdeleGroup.toFiniteIdele (𝓞 K) K y = 1) (v : HeightOneSpectrum (𝓞 K)) :
    (v.ideleFiniteCoord y : v.adicCompletion K) = 1 := by
  rw [HeightOneSpectrum.coe_ideleFiniteCoord, ← IdeleGroup.coe_toFiniteIdele, hy]
  rfl

/-- With no real places, an idele with trivial finite part satisfies every congruence condition. -/
theorem mem_ideleCongruenceSubgroup_of_toFiniteIdele_eq_one (hK : ∀ w : InfinitePlace K, ¬ w.IsReal)
    (𝔪 : Modulus K) {y : IdeleGroup (𝓞 K) K} (hy : IdeleGroup.toFiniteIdele (𝓞 K) K y = 1) :
    y ∈ ideleCongruenceSubgroup 𝔪 := by
  refine mem_ideleCongruenceSubgroup_iff.mpr ⟨fun v _ => ?_, fun v _ => ?_, fun w _ => ?_⟩
  · rw [ideleFiniteCoord_eq_one hy v, map_one]
  · rw [ideleFiniteCoord_eq_one hy v, sub_self, map_zero]; exact zero_le
  · exact absurd w.2 (hK w.1)

/-- Every class is congruent to a point of `X` modulo every global norm subgroup. -/
theorem exists_mem_compactX (hK : ∀ w : InfinitePlace K, ¬ w.IsReal)
    (V : OpenNormalSubgroup (TauCeti.AbsoluteGaloisGroup K)) (c : CK) :
    ∃ c' ∈ compactX (K := K), NormalLayer.abelianizationRestrict V (art c') =
      NormalLayer.abelianizationRestrict V (art c) := by
  set q : CK ⧸ raySubgroup (Modulus.one K) := (c : CK ⧸ raySubgroup (Modulus.one K))
  have hq : (Quotient.out q)⁻¹ * c ∈ raySubgroup (Modulus.one K) := by
    rw [← QuotientGroup.eq]
    exact QuotientGroup.out_eq' q
  obtain ⟨x, hx, hxc⟩ := mem_raySubgroup_iff.mp hq
  have hxv := mem_ideleCongruenceSubgroup_one_iff.mp hx
  set u := IdeleGroup.toFiniteIdele (𝓞 K) K x
  have hu : u ∈ unitSet (K := K) := by
    refine Submonoid.mem_units_of_val_mem_inv_val_mem _ (toFiniteIdele_mem_integralAdeles hxv) ?_
    have hxinv : x⁻¹ ∈ ideleCongruenceSubgroup (Modulus.one K) := inv_mem hx
    have := toFiniteIdele_mem_integralAdeles (mem_ideleCongruenceSubgroup_one_iff.mp hxinv)
    rwa [map_inv] at this
  set y := x * (IdeleGroup.ofFiniteIdele (𝓞 K) K u)⁻¹
  have hy : IdeleGroup.toFiniteIdele (𝓞 K) K y = 1 := by
    simp only [y, map_mul, map_inv, IdeleGroup.toFiniteIdele_ofFiniteIdele, u, mul_inv_cancel]
  obtain ⟨𝔪, h𝔪⟩ := exists_raySubgroup_le_of_isOpen (globalNormSubgroup K V)
    (isOpen_globalNormSubgroup K V)
  have hyN : ((y : IdeleGroup (𝓞 K) K) : CK) ∈ globalNormSubgroup K V :=
    h𝔪 (mem_raySubgroup_iff.mpr ⟨y, mem_ideleCongruenceSubgroup_of_toFiniteIdele_eq_one hK 𝔪 hy, rfl⟩)
  refine ⟨Quotient.out q * toCl u, Set.mem_iUnion.2 ⟨q, ⟨toCl u, ⟨u, hu, rfl⟩, rfl⟩⟩, ?_⟩
  have hc : c = Quotient.out q * toCl u * ((y : IdeleGroup (𝓞 K) K) : CK) := by
    have hxy : x = IdeleGroup.ofFiniteIdele (𝓞 K) K u * y := by
      simp only [y]; rw [mul_comm x, mul_inv_cancel_left]
    have h1 : ((x : IdeleGroup (𝓞 K) K) : CK) = toCl u * ((y : IdeleGroup (𝓞 K) K) : CK) := by
      rw [hxy]; rfl
    have h2 : c = Quotient.out q * ((x : IdeleGroup (𝓞 K) K) : CK) := by
      have hxc' : ((x : IdeleGroup (𝓞 K) K) : CK) = (Quotient.out q)⁻¹ * c := hxc
      rw [hxc', mul_inv_cancel_left]
    rw [h2, h1]; exact (mul_assoc (Quotient.out q) (toCl u) ((y : IdeleGroup (𝓞 K) K) : CK)).symm
  rw [hc, abRestr_art_mul_of_mem V _ hyN]

/-- The top open normal subgroup (to see that the index type is nonempty). -/
def topONS (G : Type) [Group G] [TopologicalSpace G] : OpenNormalSubgroup G :=
  { toOpenSubgroup := ⊤
    isNormal' := by
      show (⊤ : Subgroup G).Normal
      infer_instance }

/-- **Surjectivity of Tau Ceti's absolute Artin map for number fields without real places.** -/
theorem absArtinSurjective_of_noReal (hK : ∀ w : InfinitePlace K, ¬ w.IsReal) :
    AbsArtinSurjective K := by
  intro g
  set g' : GabK := Additive.ofMul (g : TopologicalAbelianization (TauCeti.AbsoluteGaloisGroup K))
  let t : OpenNormalSubgroup (TauCeti.AbsoluteGaloisGroup K) → Set CK := fun V =>
    {c | NormalLayer.abelianizationRestrict V (art c) = NormalLayer.abelianizationRestrict V g'}
  have hdir : ∀ V W : OpenNormalSubgroup (TauCeti.AbsoluteGaloisGroup K), W ≤ V → t W ⊆ t V := by
    intro V W hWV c hc
    have T := LayerRefinement.ofOpenNormal hWV
    show NormalLayer.abelianizationRestrict V (art c) = NormalLayer.abelianizationRestrict V g'
    rw [← T.quotientHom_abelianizationRestrict, ← T.quotientHom_abelianizationRestrict]
    exact congrArg _ hc
  have hne : ∀ u : Finset (OpenNormalSubgroup (TauCeti.AbsoluteGaloisGroup K)),
      (compactX (K := K) ∩ ⋂ V ∈ u, t V).Nonempty := by
    intro u
    have : Nonempty (OpenNormalSubgroup (TauCeti.AbsoluteGaloisGroup K)) :=
      ⟨topONS _⟩
    have hD : Directed (· ≥ ·) (id : OpenNormalSubgroup (TauCeti.AbsoluteGaloisGroup K) →
        OpenNormalSubgroup (TauCeti.AbsoluteGaloisGroup K)) :=
      fun a b => ⟨a ⊓ b, inf_le_left, inf_le_right⟩
    obtain ⟨W, hW⟩ := hD.finset_le u
    obtain ⟨c0, hc0⟩ := exists_abRestr_art_eq W g'
    obtain ⟨c, hcX, hc⟩ := exists_mem_compactX hK W c0
    refine ⟨c, hcX, Set.mem_iInter₂.2 fun V hV => hdir V W (hW V hV) ?_⟩
    show NormalLayer.abelianizationRestrict W (art c) = NormalLayer.abelianizationRestrict W g'
    rw [hc, hc0]
  obtain ⟨c, -, hc⟩ := isCompact_compactX.inter_iInter_nonempty t (fun V => isClosed_fibre V _) hne
  refine ⟨c, ?_⟩
  symm
  exact NormalLayer.eq_of_forall_abelianizationRestrict_eq fun V => Set.mem_iInter.1 hc V

end General

end T5Glue2

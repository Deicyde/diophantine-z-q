import ZInQKernel.Contrib.OneProof.RC.HCMV21.DeuringRankFour
import ZInQKernel.Contrib.OneProof.RC.ExplicitSplit.Ramification

/-! Supersingular enhanced elliptic curves of level `N` over an algebraic
closure of `ZMod q`, their isomorphism relation and the type of isomorphism
classes (tex 8465–8466). The elliptic curve is a one-dimensional
`PkgI3.AbVar k`. Supersingularity is Voight's Def. 42.1.6 (`End(E)_ℚ` is a
quaternion algebra) in rank form, `Module.finrank ℤ A.End = 4`: over
`k = F_q^al` the printed Theorem 42.1.9 candidate gives the quaternion algebra
from rank four, and a quaternion algebra has `ℚ`-dimension four. The level is a
cyclic subgroup of `A.Pt k` of order `N`. Two enhanced curves are identified by
an isomorphism of abelian varieties carrying one subgroup onto the other. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory Eichler PkgI3.AbVar
open scoped CategoryTheory.MonObj

/-- Supersingular in Voight's sense (Def. 42.1.6), in the rank form used
throughout part (2): a one-dimensional abelian variety whose endomorphism
ring has `ℤ`-rank four. -/
def IsSupersingular {k : Type} [Field k] (A : PkgI3.AbVar k) : Prop :=
  A.dim = 1 ∧ Module.finrank ℤ A.End = 4

section Setting

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (ZMod q) k]
  [IsAlgClosure (ZMod q) k]

include q in
theorem charP_of_isAlgClosure : CharP k q :=
  charP_of_injective_algebraMap (algebraMap (ZMod q) k).injective q

include q in
theorem isAlgClosed_of_isAlgClosure : IsAlgClosed k :=
  IsAlgClosure.isAlgClosed (ZMod q)

/-- A supersingular elliptic curve over `k = F_q^al` with a cyclic subgroup
of order `N` of its `k`-points. Like `PkgI3.AbVar k`, this lives in `Type 1`. -/
structure SupersingularEnhanced (q : ℕ) [Fact q.Prime] (k : Type) [Field k]
    [Algebra (ZMod q) k] [IsAlgClosure (ZMod q) k] (N : ℕ) where
  curve : PkgI3.AbVar k
  supersingular : IsSupersingular curve
  level : Subgroup (curve.Pt k)
  cyclic : IsCyclic level
  card_level : Nat.card level = N

variable {q k}

/-- An isomorphism of enhanced curves: an isomorphism of abelian varieties
carrying the level subgroup onto the level subgroup. -/
structure EnhancedIso {N : ℕ} (X Y : SupersingularEnhanced q k N) where
  hom : Hom X.curve Y.curve
  inv : Hom Y.curve X.curve
  hom_inv : hom.hom ≫ inv.hom = 𝟙 _
  inv_hom : inv.hom ≫ hom.hom = 𝟙 _
  map_level : X.level.map (ptMap (L := k) hom) = Y.level

theorem ptMap_mk'_comp {A B C : PkgI3.AbVar k} (f : Hom A B) (g : Hom B C) :
    ptMap (L := k) (Hom.mk' (f.hom ≫ g.hom)) = (ptMap (L := k) g).comp (ptMap (L := k) f) := by
  refine MonoidHom.ext fun P => ?_
  change P ≫ (f.hom ≫ g.hom) = (P ≫ f.hom) ≫ g.hom
  rw [Category.assoc]

theorem ptMap_mk'_id (A : PkgI3.AbVar k) :
    ptMap (L := k) (Hom.mk' (𝟙 A.X) : Hom A A) = MonoidHom.id _ := by
  refine MonoidHom.ext fun P => ?_
  change P ≫ 𝟙 A.X = P
  rw [Category.comp_id]

variable (q k) in
/-- Isomorphism of enhanced curves, an equivalence relation. -/
def enhancedSetoid (N : ℕ) : Setoid (SupersingularEnhanced q k N) where
  r X Y := Nonempty (EnhancedIso X Y)
  iseqv := {
    refl X := ⟨{
      hom := Hom.mk' (𝟙 _)
      inv := Hom.mk' (𝟙 _)
      hom_inv := Category.id_comp _
      inv_hom := Category.id_comp _
      map_level := by rw [ptMap_mk'_id, Subgroup.map_id] }⟩
    symm := by
      rintro X Y ⟨e⟩
      refine ⟨{
        hom := e.inv
        inv := e.hom
        hom_inv := e.inv_hom
        inv_hom := e.hom_inv
        map_level := ?_ }⟩
      rw [← e.map_level, Subgroup.map_map, ← ptMap_mk'_comp]
      have h : (Hom.mk' (e.hom.hom ≫ e.inv.hom) : Hom X.curve X.curve) = Hom.mk' (𝟙 _) :=
        Hom.ext' e.hom_inv
      rw [h, ptMap_mk'_id, Subgroup.map_id]
    trans := by
      rintro X Y Z ⟨e⟩ ⟨f⟩
      refine ⟨{
        hom := Hom.mk' (e.hom.hom ≫ f.hom.hom)
        inv := Hom.mk' (f.inv.hom ≫ e.inv.hom)
        hom_inv := ?_
        inv_hom := ?_
        map_level := ?_ }⟩
      · change (e.hom.hom ≫ f.hom.hom) ≫ (f.inv.hom ≫ e.inv.hom) = 𝟙 _
        rw [Category.assoc, ← Category.assoc f.hom.hom, f.hom_inv, Category.id_comp, e.hom_inv]
      · change (f.inv.hom ≫ e.inv.hom) ≫ (e.hom.hom ≫ f.hom.hom) = 𝟙 _
        rw [Category.assoc, ← Category.assoc e.inv.hom, e.inv_hom, Category.id_comp, f.inv_hom]
      · rw [ptMap_mk'_comp, ← Subgroup.map_map, e.map_level, f.map_level] }

variable (q k) in
/-- Isomorphism classes of supersingular enhanced elliptic curves of level `N`. -/
abbrev EnhancedClasses (N : ℕ) := Quotient (enhancedSetoid q k N)

theorem zpowers_isCyclic {G : Type*} [Group G] (P : G) : IsCyclic (Subgroup.zpowers P) := by
  refine ⟨⟨⟨P, Subgroup.mem_zpowers P⟩, ?_⟩⟩
  rintro ⟨y, n, rfl⟩
  exact ⟨n, Subtype.ext (by simp)⟩

/-- The reference enhanced curve `(E₀, ⟨P₀⟩)`. -/
def referenceEnhanced {N : ℕ} (E₀ : PkgI3.AbVar k) (h₀ : IsSupersingular E₀) (P₀ : E₀.Pt k)
    (hP₀ : orderOf P₀ = N) : SupersingularEnhanced q k N where
  curve := E₀
  supersingular := h₀
  level := Subgroup.zpowers P₀
  cyclic := zpowers_isCyclic P₀
  card_level := by rw [Nat.card_zpowers, hP₀]

/-- The level subgroup is generated by a point of order `N`, the form taken
by `levelOrderOfEndOrder_isEichler`. -/
theorem SupersingularEnhanced.exists_generator {N : ℕ} (X : SupersingularEnhanced q k N) :
    ∃ P : X.curve.Pt k, X.level = Subgroup.zpowers P ∧ orderOf P = N := by
  haveI := X.cyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := X.level)
  refine ⟨g.val, ?_, ?_⟩
  · apply le_antisymm
    · intro y hy
      obtain ⟨n, hn⟩ := hg ⟨y, hy⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    · exact Subgroup.zpowers_le.mpr g.prop
  · rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, X.card_level]

end Setting

/-- The frame of the reference: the printed Theorem 42.1.9 candidate and the
uniqueness candidate put `End(E₀)` as a maximal order of the explicit algebra
`ℍ[ℚ,-1,0,-q]`, ramified exactly at `q` and `∞` by
`explicit_ramifiedExactlyAtEll0Infty`. No torsion bridge is used. -/
theorem exists_referenceFrame (hT : VoightThm4219) (hV : QuaternionRamificationUniqueness)
    (q : ℕ) [Fact q.Prime] (h : q % 4 = 3) {k : Type} [Field k] [Algebra (ZMod q) k]
    [IsAlgClosure (ZMod q) k] (E₀ : PkgI3.AbVar k) (h₀ : IsSupersingular E₀) :
    ∃ S : Order (-1) (-(q : ℚ)), Nonempty (E₀.End ≃+* S.ring) ∧
      ∀ T : Order (-1) (-(q : ℚ)), S.ring ≤ T.ring → T.ring ≤ S.ring := by
  have := charP_of_isAlgClosure q k
  exact exists_referenceEndOrder_of_rankFour hT hV q
    (ExplicitSplit.explicit_ramifiedExactlyAtEll0Infty Fact.out h) h₀.1 h₀.2

end ZInQ.Manuscript.RC.HCMV21

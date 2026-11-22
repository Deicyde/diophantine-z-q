import ZInQKernel.Contrib.OneProof.SZThm33.TateIdentityComponent
import ZInQKernel.Contrib.OneProof.SZThm33.TorsionCountExact
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The Tate rank of a semiabelian group over an algebraically closed field
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.HeightSplit ZInQ.Contrib.AbVarBC
open T5Torsion.TateFree (tb mem_tb)
open IsLocalRing

namespace SZRaynaud

variable {k : Type} [Field k] [IsAlgClosed k]

/-- A surjective morphism locally of finite type over an algebraically
closed field is surjective on points over that field. -/
theorem surjective_mapGroupPoint {U X : Over (Spec (.of k))} [GrpObj U] [GrpObj X]
    (f : U ⟶ X) [IsMonHom f] [LocallyOfFiniteType f.left] [Surjective f.left] :
    Function.Surjective (mapGroupPoint (P := algPt k k) f) := by
  intro x
  let p : Spec (.of k) ⟶ X.left := x.left
  let W := pullback f.left p
  let q : W ⟶ Spec (.of k) := pullback.snd f.left p
  have : Surjective q := inferInstanceAs (Surjective (pullback.snd f.left p))
  have : LocallyOfFiniteType q := inferInstanceAs (LocallyOfFiniteType (pullback.snd f.left p))
  have : Nonempty W := ⟨(q.surjective (closedPoint k)).choose⟩
  have : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace q
  obtain ⟨z, -, hzc⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set W))
    Set.univ_nonempty isOpen_univ.isLocallyClosed
  let s := pointOfClosedPoint q z hzc
  have hs : s ≫ q = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  have h : s ≫ pullback.fst f.left p ≫ f.left = p := by
    rw [pullback.condition, ← Category.assoc, hs, Category.id_comp]
  let y : algPt k k ⟶ U := Over.homMk (s ≫ pullback.fst f.left p) (by
    change (s ≫ pullback.fst f.left p) ≫ U.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k k))
    rw [← Over.w f, ← Category.assoc _ f.left, Category.assoc s, h]
    exact x.w)
  exact ⟨y, Over.OverMorphism.ext (by
    change (s ≫ pullback.fst f.left p) ≫ f.left = p
    rw [Category.assoc, h])⟩

private theorem pow_surjective_units (m : ℕ) (hm : 0 < m) :
    Function.Surjective (fun x : kˣ => x ^ m) := by
  intro x
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : k) hm
  have hy' : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hy
    exact x.ne_zero hy.symm
  refine ⟨Units.mk0 y hy', Units.ext ?_⟩
  exact hy

variable {ℓ : ℕ} [Fact ℓ.Prime]

private def torusTorsionEquiv (r n : ℕ) :
    tb ℓ (Additive (Fin r → kˣ)) n ≃ (Fin r → rootsOfUnity (ℓ ^ n) k) where
  toFun t j := ⟨Additive.toMul t.1 j, (mem_rootsOfUnity _ _).mpr
    (congrArg (fun x : Additive (Fin r → kˣ) => Additive.toMul x j) (mem_tb.mp t.2))⟩
  invFun x := ⟨Additive.ofMul (fun j => (x j).1), mem_tb.mpr <| by
    apply Additive.toMul.injective
    funext j
    exact (mem_rootsOfUnity _ _).mp (x j).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The split torus of dimension r has exactly ℓ^(nr) points killed by ℓ^n. -/
theorem card_torsion_splitTorus (r n : ℕ) (hℓ : (ℓ : k) ≠ 0) :
    Nat.card (tb ℓ (Additive (Fin r → kˣ)) n) = ℓ ^ (n * r) := by
  have : NeZero ((ℓ ^ n : ℕ) : k) := ⟨by simpa only [Nat.cast_pow] using pow_ne_zero n hℓ⟩
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  rw [Nat.card_congr (torusTorsionEquiv (k := k) r n), Nat.card_fun, Nat.card_fin,
    HasEnoughRootsOfUnity.natCard_rootsOfUnity k (ℓ ^ n), pow_mul]

private def torsionEquivAtAlgebraicallyClosed (B : PkgI3.AbVar k) (n : ℕ) :
    tb ℓ (Additive (B.Pt k)) n ≃ tb ℓ (Additive (B.Pt (AlgebraicClosure k))) n := by
  let e := AlgEquiv.ofBijective (Algebra.ofId k (AlgebraicClosure k))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let f := extPt B e.toAlgHom
  have h : Function.Bijective f := ⟨extPt_injective B _, by
    intro x
    refine ⟨extPt B e.symm.toAlgHom x, ?_⟩
    rw [ReductGlue.extPt_extPt]
    have H : e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id k (AlgebraicClosure k) :=
      AlgHom.ext fun y => e.apply_symm_apply y
    rw [H]
    apply Over.OverMorphism.ext
    let p : Spec (.of (AlgebraicClosure k)) ⟶ B.X.left := x.left
    change Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ p = p
    rw [show Spec.map (CommRingCat.ofHom (RingHom.id (AlgebraicClosure k))) = 𝟙 _ from Spec.map_id _,
      Category.id_comp]⟩
  let f' := f.toAdditive
  refine (Equiv.ofBijective f' h).subtypeEquiv fun x => ?_
  change x ∈ tb ℓ (Additive (B.Pt k)) n ↔ f' x ∈ tb ℓ (Additive (B.Pt (AlgebraicClosure k))) n
  rw [mem_tb, mem_tb, ← map_nsmul, ← map_zero f']
  exact h.1.eq_iff.symm

/-- The abelian quotient's ℓ^n torsion over the algebraically closed base
has the cardinality given by the project's torsion structure theorem. -/
theorem card_torsion_abelian_algClosed (B : PkgI3.AbVar k) (b n : ℕ)
    (hb : B.dim = (b : WithBot ℕ∞)) (hℓ : (ℓ : k) ≠ 0) :
    Nat.card (tb ℓ (Additive (B.Pt k)) n) = ℓ ^ (n * (2 * b)) := by
  have hT := AvSplit.torsionStructure_of_mumford
    ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof k
  obtain ⟨e, -⟩ := hT (ObjBridge.toGrp B) b (ℓ ^ n) hb
    (pow_pos (Fact.out : ℓ.Prime).pos n) (by simpa only [Nat.cast_pow] using pow_ne_zero n hℓ)
  rw [Nat.card_congr (torsionEquivAtAlgebraicallyClosed B n),
    ← Nat.card_congr (T5Torsion.TateFree.torsionEquivTb B ℓ n), Nat.card_congr e,
    Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_mul]

/-- The number of prime-power torsion points in a split semiabelian group
is the product of the numbers in its torus and abelian quotient. -/
theorem card_torsion_semiabelian
    (U : Over (Spec (.of k))) [GrpObj U] [IsCommMonObj U]
    (B : PkgI3.AbVar k) (π : U ⟶ B.X) [IsMonHom π]
    [LocallyOfFiniteType π.left] [Surjective π.left]
    (r b : ℕ) (hb : B.dim = (b : WithBot ℕ∞)) (hℓ : (ℓ : k) ≠ 0)
    (e : (Fin r → kˣ) →* (algPt k k ⟶ U))
    (he : Function.Injective e)
    (hk : ∀ u : algPt k k ⟶ U, u ≫ π = 1 ↔ u ∈ e.range) (n : ℕ) :
    Nat.card (tb ℓ (Additive (algPt k k ⟶ U)) n) = ℓ ^ (n * (2 * b + r)) := by
  let f := mapGroupPoint (P := algPt k k) π
  have hseq : e.toAdditive.range = f.toAdditive.ker := by
    ext u
    exact (hk (Additive.toMul u)).symm
  have hdiv : Function.Surjective (fun t : Additive (Fin r → kˣ) => (ℓ ^ n) • t) := by
    intro x
    choose y hy using fun j : Fin r => pow_surjective_units (ℓ ^ n)
      (pow_pos (Fact.out : ℓ.Prime).pos n) (Additive.toMul x j)
    exact ⟨Additive.ofMul y, congrArg Additive.ofMul (funext hy)⟩
  rw [card_torsionBy_of_exact e.toAdditive f.toAdditive he (surjective_mapGroupPoint π) hseq
    (ℓ ^ n) hdiv, card_torsion_splitTorus r n hℓ]
  change ℓ ^ (n * r) * Nat.card (tb ℓ (Additive (B.Pt k)) n) = _
  rw [card_torsion_abelian_algClosed B b n hb hℓ, ← pow_add, Nat.mul_add,
    Nat.add_comm (n * (2 * b))]

/-- The split semiabelian identity component has Tate module free of
rank twice the abelian quotient dimension plus the torus rank. -/
theorem semiabelian_tate_equiv
    (U : Over (Spec (.of k))) [GrpObj U] [IsCommMonObj U]
    (B : PkgI3.AbVar k) (π : U ⟶ B.X) [IsMonHom π]
    [LocallyOfFiniteType π.left] [Surjective π.left]
    (r b : ℕ) (hb : B.dim = (b : WithBot ℕ∞)) (hℓ : (ℓ : k) ≠ 0)
    (e : (Fin r → kˣ) →* (algPt k k ⟶ U)) (he : Function.Injective e)
    (hk : ∀ u : algPt k k ⟶ U, u ≫ π = 1 ↔ u ∈ e.range) :
    Nonempty (PkgI3.Tate.T ℓ (Additive (algPt k k ⟶ U)) ≃ₗ[ℤ_[ℓ]]
      (Fin (2 * b + r) → ℤ_[ℓ])) :=
  T5Torsion.TateFree.tate_linearEquiv _
    (card_torsion_semiabelian U B π r b hb hℓ e he hk)

#print axioms card_torsion_semiabelian
#print axioms semiabelian_tate_equiv

end SZRaynaud

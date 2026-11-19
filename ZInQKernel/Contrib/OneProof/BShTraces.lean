import ZInQKernel.Contrib.OneProof.BShTracesStalks
import ZInQKernel.Contrib.OneProof.BShTracesGeometry
import ZInQKernel.Contrib.OneProof.BShTracesMeromorphic
import ZInQKernel.Contrib.OneProof.BShTracesLattices
import ZInQKernel.Contrib.OneProof.BShTracesPrimeLattice
import ZInQKernel.Contrib.OneProof.BShTracesVelu
import ZInQKernel.Contrib.OneProof.BShTracesTorsion
import ZInQKernel.Contrib.OneProof.BShTracesBranchField

/-! ON THE SPOT (provenance (c)): a finite Galois family of generic marked
branches, with its punctured germ comparison, gives the fixed prime trace. -/

noncomputable section

namespace BShTraces

open scoped MatrixGroups Topology
open AlgebraicGeometry CategoryTheory UpperHalfPlane Filter
open LeafModCurves PkgI3 PkgI3.AbVar AfTateLam ShimuraPointDict BShStandard

set_option backward.isDefEq.respectTransparency false

open T5Glue X1Igusa.Weber in
/-- The triangular superlattice gives the short Vélu pair at `(τ+i)/p`. -/
theorem triangular_coordinates (p : ℕ) (hp : 0 < p) (i : Fin p) (τ : ℍ)
    {N : ℕ} (hN : 2 ≤ N)
    (h₂ : (pp (shiftDiv p i τ)).g₂ ≠ 0) (h₃ : (pp (shiftDiv p i τ)).g₃ ≠ 0) :
    markedLatticeCoordinates (triangularCosets p hp i τ) ⟨0, hp⟩ (1 / (N : ℂ)) =
      (jL (pp (shiftDiv p i τ)), weber (pp (shiftDiv p i τ)) (1 / (N : ℂ))) := by
  refine short_coordinates_of_surviving_mark _ _ (by simp [triangularCosets])
    (discNeZero_pp τ) _ ?_ h₂ h₃
  intro h
  have hh := (triangular_mark_order p i τ (by omega : 0 < N) 1).mp
    (by simpa only [Nat.cast_one] using h)
  exact (by omega : N ≠ 1) (Nat.dvd_one.mp hh)

open T5Glue X1Igusa.Weber in
/-- The horizontal superlattice at a good prime gives the short Vélu pair
at the diamond translate of `pτ`. -/
theorem horizontal_coordinates (p : ℕ) (hp : p.Prime) (τ : ℍ)
    {N : ℕ} (hN : 2 ≤ N) (hpN : ¬ p ∣ N)
    (g : SL(2, ℤ)) (hg : (N : ℤ) ∣ g 1 0) (hd : (g 1 1 : ZMod N) = (p : ZMod N))
    (h₂ : (horizontal p hp.pos τ).g₂ ≠ 0) (h₃ : (horizontal p hp.pos τ).g₃ ≠ 0) :
    markedLatticeCoordinates (horizontalCosets p hp.pos τ) ⟨0, hp.pos⟩ (1 / (N : ℂ)) =
      (jL (pp (g • mulNat p τ)), weber (pp (g • mulNat p τ)) (1 / (N : ℂ))) := by
  rw [← horizontal_diamond p hp.pos τ N g hg hd]
  refine short_coordinates_of_surviving_mark _ _ (by simp [horizontalCosets])
    (discNeZero_pp τ) _ ?_ h₂ h₃
  intro h
  have hh := (horizontal_mark_order p hp.pos τ (by omega : 0 < N) 1).mp
    (by simpa only [Nat.cast_one] using h)
  rw [mul_one] at hh
  rcases (Nat.dvd_prime hp).mp hh with hh | hh
  · omega
  · exact hpN (hh ▸ dvd_refl _)

/-- The triangular branches and the horizontal branch when it preserves the level. -/
abbrev PrimeBranch (N p : ℕ) := Fin p ⊕ {u : Unit // ¬ p ∣ N}

variable {X : Over SpecQ} [IsIntegral X.left] {J : AbVar ℚ}
variable {N p : ℕ} {jX tX : X.left.functionField}
local notation "K" => X.left.functionField

/-- If the two generators agree under continuation to a branch, agreement of
the whole function field follows from generation. Here `k` is composition
of punctured germs with the branch reparametrization. -/
theorem ringHom_eq_of_generators {R : Type*} [CommRing R] [Nontrivial R]
    {a b : K} (h : Subfield.closure {a, b} = ⊤)
    (f g : K →+* R) (ha : f a = g a) (hb : f b = g b) : f = g := by
  apply RingHom.eq_of_eqOn_of_field_closure_eq_top h
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact ha
  · exact hb

/-- Pull back punctured germs along a branch reparametrization. -/
def pullGerm {z w : ℂ} (f : ℂ → ℂ) (hf : Tendsto f (𝓝[≠] z) (𝓝[≠] w)) :
    PuncturedGerm w →+* PuncturedGerm z where
  toFun g := g.compTendsto f hf
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by induction a using Germ.inductionOn; induction b using Germ.inductionOn; rfl
  map_mul' a b := by induction a using Germ.inductionOn; induction b using Germ.inductionOn; rfl

/-- Agreement on the two generators after a reparametrization transports
all finite values. In particular, a comparison of pairs suffices for
the specialization theorem. -/
theorem transfer_of_generator_germs (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX)
    {z : ℂ} {τ : ℍ} (f : ℂ → ℂ) (hf : Tendsto f (𝓝[≠] z) (𝓝[≠] (τ : ℂ)))
    (u : K →+* PuncturedGerm z)
    (hj : u jX = pullGerm f hf (fieldGerm hN hG τ jX))
    (ht : u tX = pullGerm f hf (fieldGerm hN hG τ tX))
    {a : K} {c : ℂ} (h : HasValue (fieldGerm hN hG τ a) c) : HasValue (u a) c := by
  have hmap : u = (pullGerm f hf).comp (fieldGerm hN hG τ) :=
    ringHom_eq_of_generators hG.1 _ _ hj ht
  rw [hmap, RingHom.comp_apply]
  generalize fieldGerm hN hG τ a = k at h ⊢
  induction k using Germ.inductionOn with
  | _ k => exact hasValue_coe.mpr ((hasValue_coe.mp h).comp hf)

open MonoidalCategory CartesianMonoidalCategory MonObj in
/-- A finite Galois family with the local finite-germ comparison at each
parameter gives a trace morphism for the exact `IsPrimeTrace` formula. -/
theorem exists_primeTrace_of_branch_germs
    (hN : 2 ≤ N) (hC : IsCurve X) (hG : IsX1Gen N X jX tX)
    (aj : X ⟶ J.X)
    {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (b : PrimeBranch N p → K →+* L)
    (hperm : ∀ σ : L ≃ₐ[K] L, ∃ π : Equiv.Perm (PrimeBranch N p),
      ∀ i, (σ : L →+* L).comp (b i) = b (π i))
    (hgerms : ∀ (τ : ℍ),
      ∃ (u : L →+* MeromorphicGerm (τ : ℂ)) (π : Equiv.Perm (PrimeBranch N p)),
      ((meromorphicIncl _).comp u).comp (algebraMap K L) = fieldGerm hN hG τ ∧
      (∀ (i : Fin p) (a : K) (c : ℂ),
        HasValue (fieldGerm hN hG (shiftDiv p i τ) a) c → HasValue (meromorphicIncl _ (u (b (π (.inl i)) a))) c) ∧
      (∀ (i : {u : Unit // ¬ p ∣ N}) (g : SL(2, ℤ)),
        (N : ℤ) ∣ g 1 0 → (g 1 1 : ZMod N) = (p : ZMod N) →
        ∀ (a : K) (c : ℂ), HasValue (fieldGerm hN hG (g • mulNat p τ) a) c →
          HasValue (meromorphicIncl _ (u (b (π (.inr i)) a))) c)) :
    ∃ F : X ⟶ J.X, IsPrimeTrace jX tX aj N p F := by
  classical
  obtain ⟨F, hF⟩ := exists_extension_of_permuted_branches hC aj b hperm
  refine ⟨F, fun τ x y hx hy => ?_⟩
  obtain ⟨m, π, huK, hut, huh⟩ := hgerms τ
  let u := (meromorphicIncl _).comp m
  have hu (a : L) : ∃ f : ℂ → ℂ, (f : PuncturedGerm (τ : ℂ)) = u a ∧ MeromorphicAt f (τ : ℂ) :=
    (m a).property
  let Bgen (i : PrimeBranch N p) := b (π i)
  have hFπ : ratSpecMap (qR := baseMap X) (qS := (algebraMap K L).comp (baseMap X))
      (algebraMap K L) ≫ genericBranch (baseMap X) (RingHom.id K) ≫ F =
      ∏ i, genericBranch ((algebraMap K L).comp (baseMap X)) (Bgen i) ≫ aj := by
    rw [hF]
    exact (Equiv.prod_comp π (fun i => genericBranch _ (b i) ≫ aj)).symm
  let A := finiteValuationSubring u hu
  let q := (algebraMap K L).comp (baseMap X)
  have hq : u.comp q = (Germ.coeRingHom _).comp
      (RingHom.pi fun _ : ℂ => Rat.castHom ℂ) := RingHom.ext_rat _ _
  let qA : ℚ →+* A := q.codRestrict A.toSubring fun r => by
    refine ⟨(r : ℂ), ?_⟩
    change HasValue ((u.comp q) r) (r : ℂ)
    rw [hq]
    exact tendsto_const_nhds
  let G := ratSpecMap (qR := qA) (qS := q) A.subtype
  obtain ⟨f, hf₁, hf₂⟩ := exists_branch_lift_of_stalk_values u hu q qA (algebraMap K L) x
    (fun r => by
      change HasValue ((u.comp (algebraMap K L)) (algebraMap _ K r)) _
      rw [huK]
      exact atTau_stalk_value hN hG hx r)
  have hfG : G ≫ f =
      ratSpecMap (qR := baseMap X) (qS := q) (algebraMap K L) ≫
        genericBranch (baseMap X) (RingHom.id K) := by
    rw [hf₁]
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ X.left.fromSpecFunctionField =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
        Spec.map (CommRingCat.ofHom (RingHom.id K)) ≫ X.left.fromSpecFunctionField
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have core (pt : PrimeBranch N p → CPt X)
      (hv : ∀ i, ∀ r : X.left.presheaf.stalk (complexMap (pt i) (IsLocalRing.closedPoint ℂ)),
        HasValue (u (Bgen i (algebraMap _ K r))) (Scheme.stalkClosedPointTo (complexMap (pt i)) r)) :
      x ≫ F = ∏ i, pt i ≫ aj := by
    choose B hB₁ hB₂ using
      fun i => exists_branch_lift_of_stalk_values u hu q qA (Bgen i) (pt i) (hv i)
    have h : G ≫ f ≫ F = ∏ i, G ≫ B i ≫ aj := by
      rw [← Category.assoc, hfG, Category.assoc, hFπ]
      apply Finset.prod_congr rfl
      intro i _
      rw [← Category.assoc, hB₁ i]
    have hh := specialize_sum_of_branches F aj A qA q (algebraMap ℚ ℂ) (finiteValue u) f B h
    simpa only [← Category.assoc, hf₂, hB₂] using hh
  constructor
  · intro hbad
    let pt : PrimeBranch N p → CPt X := fun i => i.elim y (fun a => (a.property hbad).elim)
    have h := core pt (fun i => by
      cases i with
      | inl i => exact fun r => hut i _ _ (atTau_stalk_value hN hG (hy i) r)
      | inr i => exact (i.property hbad).elim)
    haveI : IsEmpty {u : Unit // ¬ p ∣ N} := ⟨fun a => a.property hbad⟩
    simpa [Fintype.prod_sum_type, pt] using h
  · intro hgood g hg hd z hz
    let pt : PrimeBranch N p → CPt X := fun i => i.elim y (fun _ => z)
    have h := core pt (fun i => by
      cases i with
      | inl i => exact fun r => hut i _ _ (atTau_stalk_value hN hG (hy i) r)
      | inr i => exact fun r => huh i g hg hd _ _ (atTau_stalk_value hN hG hz r))
    letI : Unique {u : Unit // ¬ p ∣ N} :=
      ⟨⟨⟨(), hgood⟩⟩, fun a => Subtype.ext (Subsingleton.elim _ _)⟩
    simpa [Fintype.prod_sum_type, pt, ajC] using h

/-- A version of the trace theorem requiring the local comparison only on
the two algebraic generators, under puncture preserving reparametrizations. -/
theorem exists_primeTrace_of_coordinate_germs
    (hN : 2 ≤ N) (hC : IsCurve X) (hG : IsX1Gen N X jX tX)
    (aj : X ⟶ J.X)
    {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (b : PrimeBranch N p → K →+* L)
    (hperm : ∀ σ : L ≃ₐ[K] L, ∃ π : Equiv.Perm (PrimeBranch N p),
      ∀ i, (σ : L →+* L).comp (b i) = b (π i))
    (hgerms : ∀ (τ : ℍ),
      ∃ (u : L →+* MeromorphicGerm (τ : ℂ)) (π : Equiv.Perm (PrimeBranch N p)),
      ((meromorphicIncl _).comp u).comp (algebraMap K L) = fieldGerm hN hG τ ∧
      let matched (i : PrimeBranch N p) (s : ℍ) :=
        ∃ (f : ℂ → ℂ) (hf : Tendsto f (𝓝[≠] (τ : ℂ)) (𝓝[≠] (s : ℂ))),
          meromorphicIncl _ (u (b (π i) jX)) = pullGerm f hf (fieldGerm hN hG s jX) ∧
          meromorphicIncl _ (u (b (π i) tX)) = pullGerm f hf (fieldGerm hN hG s tX)
      (∀ i : Fin p, matched (.inl i) (shiftDiv p i τ)) ∧
      (∀ (i : {u : Unit // ¬ p ∣ N}) (g : SL(2, ℤ)),
        (N : ℤ) ∣ g 1 0 → (g 1 1 : ZMod N) = (p : ZMod N) → matched (.inr i) (g • mulNat p τ))) :
    ∃ F : X ⟶ J.X, IsPrimeTrace jX tX aj N p F := by
  refine exists_primeTrace_of_branch_germs hN hC hG aj b hperm fun τ => ?_
  obtain ⟨u, π, hu, ht, hh⟩ := hgerms τ
  refine ⟨u, π, hu, ?_, ?_⟩
  · intro i a c h
    obtain ⟨f, hf, hj, hw⟩ := ht i
    exact transfer_of_generator_germs hN hG f hf
      (((meromorphicIncl _).comp u).comp (b (π (.inl i)))) hj hw h
  · intro i g hg hd a c h
    obtain ⟨f, hf, hj, hw⟩ := hh i g hg hd
    exact transfer_of_generator_germs hN hG f hf
      (((meromorphicIncl _).comp u).comp (b (π (.inr i)))) hj hw h

#print axioms triangular_coordinates
#print axioms horizontal_coordinates
#print axioms ringHom_eq_of_generators
#print axioms transfer_of_generator_germs
#print axioms exists_primeTrace_of_branch_germs
#print axioms exists_primeTrace_of_coordinate_germs

end BShTraces

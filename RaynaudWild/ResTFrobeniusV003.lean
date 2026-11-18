import RaynaudWild.SpecialFibreFrobV001

/-!
# The residue Frobenius power on torus points over any algebra, in the exact shape of the
# semistable-special-fibre torus data

1. `frob_pow_torus_point_alg`: for a torus presentation `e` of a `k`-scheme `X` locally of finite
   presentation, natural in `Ω`-algebra maps, there is `n` such that for every `j`, every
   `Ω`-algebra `L` and every ring endomorphism `τ` of `L` with `τ y = y ^ (q ^ (n! * j))`,
   precomposition of `e_L(χ)` with `Spec τ` is `e_L(χ ^ (q ^ (n! * j)))`.  `L` need not be `Ω`:
   e.g. the residue field of a valuation ring above, with `τ` the residue action of a power of a
   Frobenius lift, once it is given an `Ω`-algebra structure over `k`.
2. `algPt'`, `algPtMap'`, `algK'`, `φbar'`: verbatim copies (same bodies) of the definitions used in
   the semistable special-fibre condition over the residue field (torus not necessarily split);
   `ResTTorusData` restates the torus clause of that condition verbatim.
3. `resT_frob_pow`: from that torus clause for an open subgroup `U` of a `k`-scheme locally of
   finite presentation, the statement of 1 in group form `P ↦ P ^ (q ^ (n! * j))`.
4. `resT_frob_pow_specialFibre`: the same with `U` an open subgroup of the special fibre of a
   smooth group model over a ring with finite residue field.
-/

open CategoryTheory AlgebraicGeometry MonObj

noncomputable section

namespace RaynaudWild.FrobDescent

variable {k Ω : Type} [Field k] [Finite k] [Field Ω] [Algebra k Ω]

/-- `c ^ (q ^ m) = c` for `c` in the image of `k`. -/
theorem base_pow_card_pow (L : Type) [CommRing L] [Algebra Ω L] (m : ℕ) (c : k) :
    ((algebraMap Ω L).comp (algebraMap k Ω)) c ^ (Nat.card k ^ m) =
      ((algebraMap Ω L).comp (algebraMap k Ω)) c := by
  haveI : Fintype k := Fintype.ofFinite k
  rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card_pow]

/-- A `q ^ m`-power ring endomorphism of an `Ω`-algebra, as a `k`-morphism of its spectrum. -/
def frobPt (L : Type) [CommRing L] [Algebra Ω L] (m : ℕ) (τ : L →+* L)
    (hτ : ∀ y, τ y = y ^ (Nat.card k ^ m)) : kPt (k := k) (Ω := Ω) L ⟶ kPt (k := k) (Ω := Ω) L :=
  kPtSemi (k := k) τ (by
    ext c
    rw [RingHom.comp_apply, hτ, base_pow_card_pow])

variable {M : Type} [CommGroup M]

/-- Evaluation of `Ω[M]` at a character with values in an `Ω`-algebra. -/
def evL {L : Type} [CommRing L] [Algebra Ω L] (χ : M →* Lˣ) : MonoidAlgebra Ω M →ₐ[Ω] L :=
  MonoidAlgebra.lift Ω L M ((Units.coeHom L).comp χ)

theorem evL_single {L : Type} [CommRing L] [Algebra Ω L] (χ : M →* Lˣ) (g : M) (a : Ω) :
    evL χ (MonoidAlgebra.single g a) = algebraMap Ω L a * (χ g : L) := by
  simp [evL, MonoidAlgebra.lift_single, Algebra.smul_def]

theorem evL_univ {L : Type} [CommRing L] [Algebra Ω L] (χ : M →* Lˣ) :
    (Units.map (evL (Ω := Ω) χ : MonoidAlgebra Ω M →* L)).comp (univ M) = χ := by
  ext g
  simp [univ, evL_single, MonoidAlgebra.of]

/-- `σ ^ (a + b)` acts on coefficients as the composite. -/
theorem coeffAct_pow_add (σ : Ω ≃ₐ[k] Ω) (a b : ℕ) :
    coeffAct (M := M) (σ ^ (a + b)) = (coeffAct (σ ^ a)).comp (coeffAct (σ ^ b)) := by
  apply RingHom.ext
  intro x
  apply MonoidAlgebra.coeff_injective
  ext g
  simp [coeffAct, pow_add, AlgEquiv.mul_apply]

/-- **Over an arbitrary algebra.** -/
theorem frob_pow_torus_point_alg [Algebra.IsAlgebraic k Ω] (σ : Ω ≃ₐ[k] Ω)
    (hσ : ∀ x : Ω, σ x = x ^ Nat.card k) (X : Over (Spec (CommRingCat.of k)))
    [LocallyOfFinitePresentation X.hom]
    (e : ∀ (R : Type) [CommRing R] [Algebra Ω R], (M →* Rˣ) → (kPt (k := k) (Ω := Ω) R ⟶ X))
    (he : ∀ (R S : Type) [CommRing R] [Algebra Ω R] [CommRing S] [Algebra Ω S]
      (f : R →ₐ[Ω] S) (χ : M →* Rˣ),
      e S ((Units.map (f : R →* S)).comp χ) = kPtMap f ≫ e R χ) :
    ∃ n : ℕ, ∀ (j : ℕ) (L : Type) [CommRing L] [Algebra Ω L] (τ : L →+* L)
      (hτ : ∀ y, τ y = y ^ (Nat.card k ^ (n.factorial * j))) (χ : M →* Lˣ),
      frobPt L (n.factorial * j) τ hτ ≫ e L χ = e L (χ ^ (Nat.card k ^ (n.factorial * j))) := by
  let x0 : Spec (CommRingCat.of (MonoidAlgebra Ω M)) ⟶ X.left :=
    (e (MonoidAlgebra Ω M) (univ M)).left
  have hx : x0 ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra Ω M))) := by
    change (e (MonoidAlgebra Ω M) (univ M)).left ≫ X.hom = _
    rw [Over.w (e (MonoidAlgebra Ω M) (univ M))]
    change Spec.map (CommRingCat.ofHom
      ((algebraMap Ω (MonoidAlgebra Ω M)).comp (algebraMap k Ω))) = _
    rw [← IsScalarTower.algebraMap_eq]
  obtain ⟨n, hn⟩ := exists_frob_invariant σ M hσ X x0 hx
  refine ⟨n, fun j L _ _ τ hτ χ => ?_⟩
  set m := n.factorial * j with hm
  -- invariance of the universal point under `σ ^ (n! * j)`
  have hinvj : ∀ i : ℕ, Spec.map (CommRingCat.ofHom (coeffAct (M := M) (σ ^ (n.factorial * i)))) ≫
      x0 = x0 := by
    intro i
    induction i with
    | zero =>
      have h1 : coeffAct (M := M) (σ ^ (n.factorial * 0)) = RingHom.id _ := by
        apply RingHom.ext
        intro x
        apply MonoidAlgebra.coeff_injective
        ext g
        simp [coeffAct]
      rw [h1, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    | succ i ih =>
      rw [Nat.mul_succ, coeffAct_pow_add, CommRingCat.ofHom_comp, Spec.map_comp,
        Category.assoc]
      change _ ≫ (Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapAlgHom M
        ((σ ^ n.factorial : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω)).toRingHom) ≫ x0) = x0
      rw [hn]
      exact ih
  have hspec : ∀ ψ : M →* Lˣ, e L ψ = kPtMap (evL ψ) ≫ e (MonoidAlgebra Ω M) (univ M) := by
    intro ψ
    have h := he (MonoidAlgebra Ω M) L (evL ψ) (univ M)
    rw [evL_univ] at h
    exact h
  have hp : ∀ r : Ω, (⇑σ)^[m] r = r ^ (Nat.card k ^ m) := fun r => by
    rw [← pow_apply_eq σ hσ m r]
    simp
  have hsemiRing : τ.comp (evL χ).toRingHom =
      (evL (χ ^ (Nat.card k ^ m))).toRingHom.comp (coeffAct (σ ^ m)) := by
    apply MonoidAlgebra.ringHom_ext
    · intro r
      simp [coeffAct, evL_single, hτ, hp]
    · intro g
      simp [coeffAct, evL_single, hτ]
  have hsemi : frobPt L m τ hτ ≫ kPtMap (evL χ) =
      kPtMap (evL (χ ^ (Nat.card k ^ m))) ≫
        kPtSemi (coeffAct (σ ^ m)) (coeffAct_compat _) := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (CommRingCat.ofHom (evL χ).toRingHom) =
      Spec.map (CommRingCat.ofHom (evL (χ ^ (Nat.card k ^ m))).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (coeffAct (σ ^ m)))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      hsemiRing]
  have hinv : kPtSemi (coeffAct (σ ^ m)) (coeffAct_compat _) ≫
      e (MonoidAlgebra Ω M) (univ M) = e (MonoidAlgebra Ω M) (univ M) := by
    apply Over.OverMorphism.ext
    exact hinvj j
  calc frobPt L m τ hτ ≫ e L χ
      = frobPt L m τ hτ ≫ (kPtMap (evL χ) ≫ e (MonoidAlgebra Ω M) (univ M)) := by
        rw [← hspec]
    _ = (frobPt L m τ hτ ≫ kPtMap (evL χ)) ≫ e (MonoidAlgebra Ω M) (univ M) :=
        (Category.assoc _ _ _).symm
    _ = (kPtMap (evL (χ ^ (Nat.card k ^ m))) ≫
          kPtSemi (coeffAct (σ ^ m)) (coeffAct_compat _)) ≫
          e (MonoidAlgebra Ω M) (univ M) := by rw [hsemi]
    _ = kPtMap (evL (χ ^ (Nat.card k ^ m))) ≫
          (kPtSemi (coeffAct (σ ^ m)) (coeffAct_compat _) ≫
            e (MonoidAlgebra Ω M) (univ M)) := Category.assoc _ _ _
    _ = kPtMap (evL (χ ^ (Nat.card k ^ m))) ≫ e (MonoidAlgebra Ω M) (univ M) := by
        rw [hinv]
    _ = e L (χ ^ (Nat.card k ^ m)) := (hspec _).symm

/-! ### Verbatim copies of the special-fibre torus clause -/

section Verbatim

/-- Copy of `algPt` (same body). -/
def algPt' (k : Type) [Field k] (R : Type) [CommRing R] [Algebra k R] :
    Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R)))

/-- Copy of `algPtMap` (same body). -/
def algPtMap' {k : Type} [Field k] {R S : Type} [CommRing R] [Algebra k R] [CommRing S]
    [Algebra k S] (f : R →ₐ[k] S) : algPt' k S ⟶ algPt' k R :=
  Over.homMk (Spec.map (CommRingCat.ofHom (f : R →+* S))) (by
    simp only [algPt', Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])

/-- Copy of `algK` (same body). -/
@[reducible] def algK' {k k' : Type} [Field k] [Field k'] (φ : k →+* k') (R : Type) [CommRing R]
    [Algebra k' R] : Algebra k R :=
  ((algebraMap k' R).comp φ).toAlgebra

/-- Copy of `φbar` (same body). -/
abbrev φbar' (k : Type) [Field k] : k →+* AlgebraicClosure k :=
  algebraMap k (AlgebraicClosure k)

end Verbatim

/-- The torus clause of the special-fibre semistability condition over `k` (torus split over
`k̄`), verbatim, for a fixed `U`, `r`, `e`. -/
def ResTTorusNat (k : Type) [Field k] (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      letI := algK' (φbar' k) R
      (Fin r → Rˣ) →* (algPt' k R ⟶ U)) : Prop :=
  ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
    [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
    letI := algK' (φbar' k) R
    letI := algK' (φbar' k) S
    e S (fun i => Units.map (f : R →* S) (t i)) =
      algPtMap' (k := k) ({ (f : R →+* S) with commutes' := fun a => f.commutes (φbar' k a) } :
        R →ₐ[k] S) ≫ e R t

/-- The verbatim point objects are the `kPt` objects. -/
theorem algPt'_eq_kPt (k : Type) [Field k] (R : Type) [CommRing R]
    [Algebra (AlgebraicClosure k) R] :
    (letI := algK' (φbar' k) R; algPt' k R) = kPt (k := k) (Ω := AlgebraicClosure k) R := rfl

/-- **The verbatim torus clause gives the group form over every `k̄`-algebra.** -/
theorem resT_frob_pow (k : Type) [Field k] [Finite k] (U : Over (Spec (CommRingCat.of k)))
    [GrpObj U] [LocallyOfFinitePresentation U.hom] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      letI := algK' (φbar' k) R
      (Fin r → Rˣ) →* (algPt' k R ⟶ U))
    (he : ResTTorusNat k U r e) :
    ∃ n : ℕ, ∀ (j : ℕ) (L : Type) [CommRing L] [Algebra (AlgebraicClosure k) L] (τ : L →+* L)
      (hτ : ∀ y, τ y = y ^ (Nat.card k ^ (n.factorial * j))) (t : Fin r → Lˣ),
      frobPt (k := k) (Ω := AlgebraicClosure k) L (n.factorial * j) τ hτ ≫ e L t =
        (e L t) ^ (Nat.card k ^ (n.factorial * j)) := by
  haveI : Fintype k := Fintype.ofFinite k
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)
  have hσ : ∀ x : AlgebraicClosure k, σ x = x ^ Nat.card k := fun x => by
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Nat.card_eq_fintype_card]
  let e' : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Multiplicative (Fin r → ℤ) →* Rˣ) → (kPt (k := k) (Ω := AlgebraicClosure k) R ⟶ U) :=
    fun R _ _ χ => e R (finOfChar χ)
  have he' : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S)
      (χ : Multiplicative (Fin r → ℤ) →* Rˣ),
      e' S ((Units.map (f : R →* S)).comp χ) = kPtMap f ≫ e' R χ := by
    intro R S _ _ _ _ f χ
    exact he R S f (finOfChar χ)
  obtain ⟨n, hn⟩ := frob_pow_torus_point_alg σ hσ U e' he'
  refine ⟨n, fun j L _ _ τ hτ t => ?_⟩
  have h1 := hn j L τ hτ (charOfFin t)
  have hb : finOfChar (charOfFin t) = t := funext fun i => charOfFin_basis t i
  have hp : finOfChar (charOfFin t ^ (Nat.card k ^ (n.factorial * j))) =
      t ^ (Nat.card k ^ (n.factorial * j)) := by
    funext i
    simp only [finOfChar, MonoidHom.pow_apply, Pi.pow_apply]
    rw [charOfFin_basis]
  change frobPt L (n.factorial * j) τ hτ ≫ e L (finOfChar (charOfFin t)) =
    e L (finOfChar (charOfFin t ^ (Nat.card k ^ (n.factorial * j)))) at h1
  rw [hb, hp, map_pow] at h1
  exact h1

/-- **Special fibre.** The same for `U` an open subgroup of the special fibre (base change along
`O → k`) of a smooth `O`-scheme, `k` finite. -/
theorem resT_frob_pow_specialFibre {O k : Type} [CommRing O] [Field k] [Finite k] [Algebra O k]
    (𝒢 : Over (Spec (CommRingCat.of O))) [Smooth 𝒢.hom]
    (U : Over (Spec (CommRingCat.of k))) [GrpObj U]
    (inc : U ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O k)))).obj 𝒢)
    [IsOpenImmersion inc.left] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      letI := algK' (φbar' k) R
      (Fin r → Rˣ) →* (algPt' k R ⟶ U))
    (he : ResTTorusNat k U r e) :
    ∃ n : ℕ, ∀ (j : ℕ) (L : Type) [CommRing L] [Algebra (AlgebraicClosure k) L] (τ : L →+* L)
      (hτ : ∀ y, τ y = y ^ (Nat.card k ^ (n.factorial * j))) (t : Fin r → Lˣ),
      frobPt (k := k) (Ω := AlgebraicClosure k) L (n.factorial * j) τ hτ ≫ e L t =
        (e L t) ^ (Nat.card k ^ (n.factorial * j)) := by
  haveI := lfp_baseChange_of_smooth (k := k) 𝒢
  haveI := lfp_of_openImmersion inc
  exact resT_frob_pow k U r e he

end RaynaudWild.FrobDescent

#print axioms RaynaudWild.FrobDescent.frob_pow_torus_point_alg
#print axioms RaynaudWild.FrobDescent.algPt'_eq_kPt
#print axioms RaynaudWild.FrobDescent.resT_frob_pow
#print axioms RaynaudWild.FrobDescent.resT_frob_pow_specialFibre

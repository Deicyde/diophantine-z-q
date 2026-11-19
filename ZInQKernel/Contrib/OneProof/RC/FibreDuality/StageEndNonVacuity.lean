import ZInQKernel.Contrib.OneProof.RC.FibreDuality.StageArith
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.StageNonVacuity

/-!
# Lane RC31, round 3: end-to-end non-vacuity of the stage interfaces

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4391–4451), the retained data
(tex 4385–4388, 4400–4406) and the split local model `L = D⁰ ⊕ (F ⊕ S)[−1] ⊕ D²[−2]`
(tex 4860–4868).

For the explicit example of `StageNonVacuity` (the complex `A²` in degrees `0` and `1`):
* the stage duality map of `exPair` is a quasi-isomorphism (`exPair_quasiIso`);
* an explicit Selmer pairing datum `exSel` with the split local model, its trace `exTr`, and the
  quasi-isomorphy of its global duality map (`exSel_globalDuality`), with `stageLocMat = exLoc`;
* residual finiteness and the residual rank bounds over a local ring;
* every hypothesis of `exists_retained_of_stageInputs` holds for the constant inputs over the
  stages `A_i`, so the producer's conclusion holds (`exists_retained_nonvacuous`), with a
  nonzero local pairing (`exists_retained_loc_nondegenerate`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open CategoryTheory Matrix IsLocalRing TensorProduct
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex ComplexStages)
open ZInQ.Contrib.RC53Assist.InnerLimitArith (ResidualCohomologyFinite gcxBaseChange)
open ZInQ.Manuscript.RC.Limits (GradedModel residualCohomologyAt subquotientOf residualDiff
  StageA stageMap stageIdeal Lambda)

variable (A : Type) [CommRing A]

/-- **The stage duality map of the example is a quasi-isomorphism**, from the example diagram by
`quasiIso_stageDualityMap_of_diagram` with all four model equations definitional (tex 4391–4451; tex
4385–4388). Kind: PROVED. -/
theorem exPair_quasiIso : QuasiIso (GHom.toCC (stageDualityMap (exPair A))) :=
  quasiIso_stageDualityMap_of_diagram (exModel A) (exPair A) (exDiagram A) rfl rfl rfl rfl

/-- The zero complex (`PUnit` in every degree): the local condition and the global target of the
example (tex 4391–4451). Kind: definition. -/
def exZero : GCx A where
  X _ := ModuleCat.of A PUnit
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

/-- The (zero) local condition map of the example into the split model (split model tex 4860–4868).
Kind: definition. -/
def exIota : GHom (exZero A) (splitLocalComplex A) where
  f _ _ _ := 0
  comm _ _ _ _ _ _ _ _ _ := rfl

/-- The terms of the example local target: `A` in degree `2`, `PUnit` elsewhere; by pattern
matching, so that the degree `3 − 1` term is `A` definitionally (tex 4391–4451). Kind: definition.
-/
def exELTerms : ℤ → ModuleCat A
  | .ofNat 2 => ModuleCat.of A A
  | _ => ModuleCat.of A PUnit

/-- **The example local target complex** (zero differentials) (tex 4391–4451). Kind: definition. -/
def exEL : GCx A where
  X := exELTerms A
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

/-- The (zero) restriction of the example targets (tex 4391–4451). Kind: definition. -/
def exResE : GHom (exZero A) (exEL A) where
  f _ _ _ := 0
  comm _ _ _ _ _ _ _ _ _ := rfl

/-- **The example Selmer datum** with the split local model and zero local condition (split model
tex 4860–4868). Kind: definition. -/
abbrev exSelData : SelData A := splitSelData (exCx A) (exRes A) (exZero A) (exIota A)

/-- The example local cup product: `locForm exLoc` into degree `2`, zero into every other degree
(split model tex 4860–4868). Kind: definition. -/
def exCupL (a b : ℤ) : ∀ k : ℤ,
    (splitLocalComplex A).X a →ₗ[A] (splitLocalComplex A).X b →ₗ[A] (exEL A).X k
  | .ofNat 2 => locForm (exLoc A) a b
  | .ofNat 0 => 0
  | .ofNat 1 => 0
  | .ofNat (_ + 3) => 0
  | .negSucc _ => 0

/-- The example local cup product vanishes outside target degree `2` (split model tex 4860–4868).
Kind: PROVED. -/
theorem exCupL_ne (a b k : ℤ) (hk : k ≠ 2) : exCupL A a b k = 0 := by
  rcases k with (_ | _ | _ | m) | m
  · rfl
  · rfl
  · exact absurd rfl hk
  · rfl
  · rfl

/-- The example local cup product in target degree `2` is `locForm exLoc` (split model tex
4860–4868). Kind: PROVED (definitional). -/
theorem exCupL_two (a b : ℤ) (u : (splitLocalComplex A).X a) (v : (splitLocalComplex A).X b) :
    exCupL A a b 2 u v = locForm (exLoc A) a b u v :=
  rfl

/-- The localizations of the example are isotropic for the local pairing in total degree `2` (tex
4391–4451; split model tex 4860–4868). Kind: PROVED. -/
theorem exLoc_res (a b : ℤ) (h : a + b = 2) (x : (exCx A).X a) (y : (exCx A).X b) :
    locForm (exLoc A) a b ((exRes A).f a a rfl x) ((exRes A).f b b rfl y) = 0 := by
  rcases (show a = 1 ∨ a ≠ 0 ∧ a ≠ 1 ∨ a = 0 by omega) with rfl | ha | rfl
  · obtain rfl : b = 1 := by omega
    rw [locForm_apply]
    exact exHyp_iso A x y
  · rw [exCx_eq_zero A a ha.1 ha.2 x, map_zero, map_zero, LinearMap.zero_apply]
  · rw [exCx_eq_zero A b (by omega) (by omega) y, map_zero, map_zero]

/-- The (zero) global cup product of the example (tex 4391–4451). Kind: definition (PROVED Leibniz
rule). -/
def exCupG : GPair (exCx A) (exCx A) (exZero A) where
  P _ _ _ _ := 0
  leib _ _ _ _ _ _ _ _ _ _ _ _ := rfl

/-- The local cup product of the example as a pairing of complexes; the Leibniz rule holds since all
differentials vanish (split model tex 4860–4868). Kind: definition (PROVED Leibniz rule). -/
def exCupLPair : GPair (splitLocalComplex A) (splitLocalComplex A) (exEL A) where
  P a b k _ := exCupL A a b k
  leib i i₁ j j₁ k k₁ h hi hj hk x y := by
    change (0 : (exEL A).X k →ₗ[A] (exEL A).X k₁) _ =
      exCupL A i₁ j k₁ ((0 : (splitLocalComplex A).X i →ₗ[A] (splitLocalComplex A).X i₁) x) y +
        sgn i • exCupL A i j₁ k₁ x
          ((0 : (splitLocalComplex A).X j →ₗ[A] (splitLocalComplex A).X j₁) y)
    simp

/-- **The example Selmer pairing datum**: zero global target and global cup product, local cup
product `exCupL`, zero isotropy homotopy (tex 4391–4451; split model tex 4860–4868). Kind:
definition (PROVED compatibility and isotropy). -/
def exSel : SelPairData (exSelData A) (exSelData A) where
  E := exZero A
  EL := exEL A
  resE := exResE A
  cupG := exCupG A
  cupL := exCupLPair A
  compat i j k i' j' k' h h' hi hj hk a b := by
    subst hi hj hk
    change (0 : (exEL A).X k) = exCupL A i j k ((exRes A).f i i rfl a) ((exRes A).f j j rfl b)
    rcases eq_or_ne k 2 with rfl | hk2
    · rw [exCupL_two]
      exact (exLoc_res A i j h' a b).symm
    · rw [exCupL_ne A i j k hk2, LinearMap.zero_apply, LinearMap.zero_apply]
  hU _ _ _ _ := 0
  isotropy i i₁ j j₁ k k₁ h hi hj hk u v := by
    change (0 : (exEL A).X k₁) + 0 + sgn i • 0 =
      exCupL A i j k₁ ((0 : (exZero A).X i →ₗ[A] (splitLocalComplex A).X i) u)
        ((0 : (exZero A).X j →ₗ[A] (splitLocalComplex A).X j) v)
    simp

/-- **The example trace** `(e, l) ↦ l` on degree `3` of the target cone (tex 4385–4388). Kind:
definition. -/
def exTr : (coneCx (exSel A).resE).X 3 →ₗ[A] A := LinearMap.snd A PUnit A

/-- The example trace kills coboundaries: the cone differential into degree `3` is zero (tex
4385–4388). Kind: PROVED. -/
theorem exHtr (z : (coneCx (exSel A).resE).X 2) :
    exTr A ((coneCx (exSel A).resE).d 2 3 rfl z) = 0 :=
  sub_zero (0 : A)


/-- The example local pairing vanishes outside total degree `2` (split model tex 4860–4868). Kind:
PROVED. -/
theorem exLoc_eq_zero (a b : ℤ) (h : a + b ≠ 2) : exLoc A a b = 0 := by
  rcases a with (_ | _ | _ | m) | m <;> rcases b with (_ | _ | _ | n) | n
  all_goals first
    | rfl
    | exact absurd rfl h

/-- Local pairing matrices with equal forms in degrees `(a, b)` are equal there (split model tex
4860–4868). Kind: PROVED. -/
theorem locMat_eq_of_form (M M' : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) A) (a b : ℤ)
    (h : ∀ u v, locForm M a b u v = locForm M' a b u v) : M a b = M' a b := by
  ext s t
  have e := h ((lCoordR A a).symm (Pi.single s 1)) ((lCoordR A b).symm (Pi.single t 1))
  rw [locForm_apply, locForm_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    Matrix.mulVec_single_one, Matrix.mulVec_single_one, single_dotProduct, single_dotProduct,
    one_mul, one_mul] at e
  exact e

/-- **The coordinate local pairing of the example Selmer datum is `exLoc`** (split model tex
4860–4868; tex 5037). Kind: PROVED. -/
theorem exStageLocMat_eq : stageLocMat (exSel A) (exTr A) = exLoc A := by
  funext a b
  by_cases h : a + b = 2
  · refine locMat_eq_of_form A _ _ a b fun u v => ?_
    rw [locForm_stageLocMat _ _ a b h]
    rfl
  · rw [stageLocMat, dite_eq_right_iff.mpr (fun h' => absurd h' h), exLoc_eq_zero A a b h]

/-- The model trace pairing of the example Selmer stage data is zero (tex 4385–4388). Kind: PROVED.
-/
theorem exStageGlob_eq :
    modelGlob (exModel A) (stagePairingInputOfSel (exSel A) (exTr A) (exHtr A)) = exGlob A := by
  funext a b h
  ext i j
  rfl

/-- **The global duality map of the example Selmer datum is a quasi-isomorphism** (the shape of the
PRINT input; Nekovář, *Selmer complexes*, 5.4.3; tex 4391–4451). Kind: PROVED. -/
theorem exSel_globalDuality :
    QuasiIso (GHom.toCC (globalDualityMap (exSel A) (exTr A) (exHtr A))) := by
  have e := quasiIso_stageDualityMap_of_diagram (exModel A)
    (stagePairingInputOfSel (exSel A) (exTr A) (exHtr A)) (exDiagram A) rfl rfl
    ((exModelGlob_eq A).trans (exStageGlob_eq A).symm) (exStageLocMat_eq A).symm
  rwa [stageDualityMap_eq_globalDualityMap] at e

/-- **The example complex satisfies `ResidualCohomologyFinite`** over a local ring (tex 4392–4394).
Kind: PROVED. -/
theorem exCx_residualCohomologyFinite [IsLocalRing A] : ResidualCohomologyFinite (exCx A) :=
  fun n => (moduleFinite_homology_iff (gcxBaseChange (ResidueField A) (exCx A)) n).2
    (exCx_residual_finite A n)

/-- The residual ranks of the example are bounded by its model ranks (tex 4392–4394, 4400–4406).
Kind: PROVED. -/
theorem exCx_finrank_le_rank [IsLocalRing A] (n : ℤ) :
    Module.finrank (ResidueField A) (residualCohomologyAt (exCx A) n) ≤ exRank n := by
  have : Module.Finite A ((exCx A).X n) := inferInstanceAs (Module.Finite A (Fin (exRank n) → A))
  have : Module.Free A ((exCx A).X n) := inferInstanceAs (Module.Free A (Fin (exRank n) → A))
  calc Module.finrank (ResidueField A) (residualCohomologyAt (exCx A) n)
      ≤ Module.finrank (ResidueField A) (LinearMap.ker (residualDiff (exCx A) n (n + 1) rfl)) :=
        Submodule.finrank_quotient_le _
    _ ≤ Module.finrank (ResidueField A) (ResidueField A ⊗[A] (exCx A).X n) :=
        Submodule.finrank_le _
    _ = Module.finrank A ((exCx A).X n) := Module.finrank_baseChange
    _ = exRank n := Module.finrank_fin_fun A

/-- The example ranks are at most `2` (tex 4391–4451). Kind: PROVED. -/
theorem exRank_le_two (n : ℤ) : exRank n ≤ 2 := by
  rcases n with (_ | _ | m) | m
  all_goals first
    | decide
    | exact Nat.zero_le 2

/-- **The residual cohomology of the example vanishes outside degrees `0` and `1`** (tex 4400–4406).
Kind: PROVED. -/
theorem exCx_finrank_eq_zero [IsLocalRing A] (n : ℤ) (h : n < 0 ∨ 1 < n) :
    Module.finrank (ResidueField A) (residualCohomologyAt (exCx A) n) = 0 :=
  Nat.eq_zero_of_le_zero ((exCx_finrank_le_rank A n).trans
    (exRank_eq_zero n (by omega) (by omega)).le)

/-- **The residual ranks of the example are at most `2`** (tex 4400–4406). Kind: PROVED. -/
theorem exCx_finrank_le_two [IsLocalRing A] (n : ℤ) :
    Module.finrank (ResidueField A) (residualCohomologyAt (exCx A) n) ≤ 2 :=
  (exCx_finrank_le_rank A n).trans (exRank_le_two n)


/-- **End-to-end non-vacuity of the producer**: `exists_retained_of_stageInputs` applied to the
constant example inputs over the stages `A_i` (`lo = 0`, `hi = 1`, `B = 2`) gives retained data
whose local pairing lifts `exLoc` at every stage `i ≠ 0` (tex 4391–4451; tex 4385–4388, 4400–4406).
Kind: PROVED. -/
theorem exists_retained_nonvacuous (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite) :
    ∃ (r₀ : ℤ → ℕ) (C : ComplexStages (R := Lambda) stageIdeal U)
      (D : RetainedLimitPairingStages U C) (_ : RetainedGlobalDualityStages D),
      C.rank = r₀ ∧ C.low = 0 ∧ C.high = 1 ∧ (∀ n, r₀ n ≤ 2) ∧
      (∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i] (n : ℤ),
        r₀ n = Module.finrank (ResidueField (StageA i))
          (residualCohomologyAt (exCx (StageA i)) n)) ∧
      ∀ i, i ≠ 0 → ∀ a b, (D.loc a b i).map (stageMap i) = exLoc (StageA i) a b := by
  obtain ⟨r₀, C, D, E, h1, h2, h3, h4, h5, h6⟩ := exists_retained_of_stageInputs U hU
    (fun i => exCx (StageA i)) (fun i n => exCx_flat _ n) (fun i => exZero _)
    (fun i => exRes _) (fun i => exIota _) (fun i => exSel _) (fun i => exTr _)
    (fun i => exHtr _) (fun i => exSel_globalDuality _)
    (fun i _ => exCx_residualCohomologyFinite _) 0 1
    (fun i _ n hn => exCx_finrank_eq_zero _ n hn) 2 (fun i _ n => exCx_finrank_le_two _ n)
  refine ⟨r₀, C, D, E, h1, h2, h3, h4, h5, fun i hi a b => (h6 i hi a b).trans ?_⟩
  rw [exStageLocMat_eq]

/-- **Non-degeneracy of the produced local pairing**: in degrees `(0, 2)` it reduces to the identity
at every stage `i ≠ 0`, so it is nonzero (tex 4391–4451; split model tex 4860–4868). Kind: PROVED.
-/
theorem exists_retained_loc_nondegenerate (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ Filter.cofinite) :
    ∃ (C : ComplexStages (R := Lambda) stageIdeal U) (D : RetainedLimitPairingStages U C)
      (_ : RetainedGlobalDualityStages D), C.low = 0 ∧ C.high = 1 ∧
      ∀ i, i ≠ 0 →
        @Eq (Matrix (Fin 2) (Fin 2) (StageA i)) ((D.loc 0 2 i).map (stageMap i)) 1 ∧
        D.loc 0 2 i ≠ 0 := by
  obtain ⟨_, C, D, E, -, h2, h3, -, -, h6⟩ := exists_retained_nonvacuous U hU
  refine ⟨C, D, E, h2, h3, fun i hi => ⟨h6 i hi 0 2, fun h0 => ?_⟩⟩
  have := stageA_nontrivial i hi
  have e : @Eq (Matrix (Fin 2) (Fin 2) (StageA i)) ((D.loc 0 2 i).map (stageMap i)) 1 :=
    h6 i hi 0 2
  rw [h0, Matrix.map_zero _ (map_zero (stageMap i))] at e
  exact one_ne_zero (α := Matrix (Fin 2) (Fin 2) (StageA i)) e.symm

end ZInQ.Manuscript.RC.FibreDuality

import ZInQKernel.Contrib.OneProof.RC.FibreDuality.StageGlobal
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.StageAssembly
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitCertificate
import ZInQKernel.Contrib.OneProof.RC.Limits.GradedFiniteFree
import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.StageInputs

/-!
# Lane RC31, round 3: the arithmetic stage inputs and the end-to-end producer of the retained data

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4391–4451) and the retained
inner limit (tex 4385–4388, 4400–4406): at every coefficient stage `A_i`, the bounded finite free
model of the stage complex carries the transported duality diagram; the stage-to-`Λ` ultralimit
of these matrix diagrams is the retained diagram over `Λ`.

This file consumes the arithmetic stage inputs of `InnerLimitArith.StageInputs` directly:
* the stage pairing data come from a Selmer pairing datum `Q` whose local complex is the split
  model at the derivative label (`splitSelData`): `glob(x, y) = tr(x ∪ y, 0)` (`stageGlobMap`),
  `loc` = the coordinates of `β(u, v) = tr(0, u ∪ v)` (`stageLocMat`), and the reciprocity is
  `trace_reciprocity` (`stagePairingInputOfSel`);
* the stage duality map of these data IS the global duality map of `Q`
  (`stageDualityMap_eq_globalDualityMap`), so the quasi-isomorphism is taken in the shape of
  `stageGlobalDuality` (`quasiIso_stageDualityMap_of_global`);
* the finiteness hypothesis of the finite free model is taken in the shape
  `ResidualCohomologyFinite` (`finite_residualCohomologyAt_of`).

The end-to-end theorem `exists_retained_of_stageInputs` turns stagewise inputs into the retained
data `C`, `D`, `E` of round two. Its hypotheses, per stage `i ≠ 0`, are exactly:
* (GLUE) the stage complex `G i` (flat terms) and the Selmer pairing datum `Q i` with the split
  local model at the derivative label `q_i`, with a trace `tr i` killing coboundaries. Producing
  `Q i` from the actual Galois cochains needs the comparison of the local cochains at `q_i` with the
  split model, whose degree-two part is a `LocalDegreeTwoCoordinate` (`LocalDegreeTwoNormalized`)
  at `q_i` — OPEN (`InnerLimitArith.StageInputs`);
* (PRINT) `QuasiIso (GHom.toCC (globalDualityMap (Q i) (tr i) (htr i)))`, Nekovář, *Selmer
  complexes*, 5.4.3 (for the relaxed/strict pair at `q_i`, 6.3.4 with `OrthogonalComplementsT`)
  at `A_i`, the shape of `stageGlobalDuality`;
* (OPEN) `ResidualCohomologyFinite (G i)`, the residual finiteness of the stage complex;
* (ELLIOT) bounded residual cohomology (zero outside `[lo, hi]`) and a uniform bound `B` on the
  residual ranks (tex 4400–4406: "a tuple whose model ranks are bounded").

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open CategoryTheory Matrix IsLocalRing
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex ComplexStages)
open ZInQ.Contrib.RC53Assist.InnerLimitArith (ResidualCohomologyFinite gcxBaseChange
  trace_reciprocity)
open ZInQ.Manuscript.RC.Limits (GradedModel residualCohomologyAt subquotientOf residualDiff
  StageA stageMap stageIdeal Lambda exists_gradedModel)

/-! ### Bilinear forms in coordinates -/

section Bilinear

variable {A : Type} [CommRing A]

/-- **A bilinear form in coordinates**: `β u v = e u ⬝ (M (e' v))` with `M s t = β(e⁻¹ s, e'⁻¹ t)`.
Kind: PROVED. -/
theorem bilin_eq_dot_coords {V W ι κ : Type} [AddCommGroup V] [Module A V] [AddCommGroup W]
    [Module A W] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (β : V →ₗ[A] W →ₗ[A] A) (e : V ≃ₗ[A] (ι → A)) (e' : W ≃ₗ[A] (κ → A)) (u : V) (v : W) :
    β u v = e u ⬝ᵥ (Matrix.of (fun s t => β (e.symm (Pi.single s 1)) (e'.symm (Pi.single t 1)))
      *ᵥ e' v) := by
  conv_lhs => rw [← e.symm_apply_apply u, ← e'.symm_apply_apply v, coord_expandR (e u),
    coord_expandR (e' v)]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring

end Bilinear

/-! ### The stage pairing data of a Selmer pairing datum with the split local model -/

section Sel

variable {A : Type} [CommRing A]

/-- **The stage Selmer datum with the split local model at the derivative label**: global complex
`G`, local condition `U → L`, and the localization `G → L` into the split model
`L = D⁰ ⊕ (F ⊕ S)[−1] ⊕ D²[−2]` (tex 4860–4868). Kind: definition. -/
abbrev splitSelData (G : GCx A) (res : GHom G (splitLocalComplex A)) (U : GCx A)
    (ι : GHom U (splitLocalComplex A)) : SelData A :=
  ⟨G, U, splitLocalComplex A, res, ι⟩

variable {G U : GCx A} {res : GHom G (splitLocalComplex A)} {ι : GHom U (splitLocalComplex A)}
  (Q : SelPairData (splitSelData G res U ι) (splitSelData G res U ι))
  (tr : (coneCx Q.resE).X 3 →ₗ[A] A)

/-- **The global trace pairing** `glob(x, y) = tr(x ∪ y, 0)` (the trace of the global cup product;
tex 4385–4388). Kind: definition. -/
def stageGlobMap (a b : ℤ) (h : a + b = 3) : G.X a →ₗ[A] G.X b →ₗ[A] A :=
  (Q.cupG.P a b 3 h).compr₂ (tr ∘ₗ LinearMap.inl A (Q.E.X 3) (Q.EL.X (3 - 1)))

/-- Evaluation of the global trace pairing. Kind: PROVED (definitional). -/
theorem stageGlobMap_apply (a b : ℤ) (h : a + b = 3) (x : G.X a) (y : G.X b) :
    stageGlobMap Q tr a b h x y = tr ((Q.cupG.P a b 3 h x y, 0) : coneT Q.resE 3) :=
  rfl

/-- The local pairing `β(u, v) = tr(0, u ∪ v)` of the split model, `a + b = 2`. Kind:
definition. -/
def stageLocForm (a b : ℤ) (h : a + b = 2) :
    (splitLocalComplex A).X a →ₗ[A] (splitLocalComplex A).X b →ₗ[A] A :=
  (Q.cupL.P a b (3 - 1) (by omega)).compr₂ (tr ∘ₗ LinearMap.inr A (Q.E.X 3) (Q.EL.X (3 - 1)))

/-- **The local pairing in the coordinates of the split model**: the matrix of
`β(u, v) = tr(0, u ∪ v)` for `a + b = 2`, zero otherwise (tex 4860–4868, 5037). Kind:
definition. -/
def stageLocMat (a b : ℤ) : Matrix (lIdx a) (lIdx b) A :=
  if h : a + b = 2 then
    Matrix.of fun s t => stageLocForm Q tr a b h ((lCoordR A a).symm (Pi.single s 1))
      ((lCoordR A b).symm (Pi.single t 1))
  else 0

/-- The coordinate local pairing is `β(u, v) = tr(0, u ∪ v)`. Kind: PROVED. -/
theorem locForm_stageLocMat (a b : ℤ) (h : a + b = 2) (u : (splitLocalComplex A).X a)
    (v : (splitLocalComplex A).X b) :
    locForm (stageLocMat Q tr) a b u v =
      tr ((0, Q.cupL.P a b (3 - 1) (by omega) u v) : coneT Q.resE 3) := by
  rw [locForm_apply, stageLocMat, dite_eq_left h]
  exact (bilin_eq_dot_coords (stageLocForm Q tr a b h) (lCoordR A a) (lCoordR A b) u v).symm

variable (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)

/-- **The stage pairing data of a Selmer pairing datum with the split local model**:
`res` its localization, `glob = tr(· ∪ ·, 0)`, `loc` the coordinates of `tr(0, · ∪ ·)`, and the
reciprocity `trace_reciprocity` (tex 4385–4388; the stage form of the retained reciprocity).
Kind: definition (PROVED reciprocity). -/
def stagePairingInputOfSel : StagePairingInput G where
  res := res
  glob := stageGlobMap Q tr
  loc := stageLocMat Q tr
  recip a b h x y := by
    rw [stageGlobMap_apply, stageGlobMap_apply, locForm_stageLocMat Q tr a b h]
    exact trace_reciprocity Q tr htr a b h x y

/-- Evaluation of the global duality map of `Q`: `(b, y) ↦ tr(x ∪ b, 0) + (−1)^a tr(0, res x ∪ y)`.
Kind: PROVED. -/
theorem globalDualityMap_eval (a : ℤ) (x : G.X a) (b : G.X (3 - a))
    (y : (splitLocalComplex A).X (3 - a - 1)) :
    asDual ((globalDualityMap Q tr htr).f a a rfl x)
        ((b, y) : (compactCx (splitSelData G res U ι)).X (3 - a)) =
      tr ((Q.cupG.P a (3 - a) 3 (by omega) x b, 0) : coneT Q.resE 3) +
        sgn a • tr ((0, Q.cupL.P a (3 - a - 1) (3 - 1) (by omega) (res.f a a rfl x) y) :
          coneT Q.resE 3) := by
  change tr (selCupFun Q a (3 - a) 3 (by omega) (x, 0, 0) (b, 0, y)) = _
  have e : selCupFun Q a (3 - a) 3 (by omega) (x, 0, 0) (b, 0, y) =
      ((Q.cupG.P a (3 - a) 3 (by omega) x b, 0) : coneT Q.resE 3) +
        sgn a • ((0, Q.cupL.P a (3 - a - 1) (3 - 1) (by omega) (res.f a a rfl x) y) :
          coneT Q.resE 3) := by
    refine Prod.ext ?_ ?_
    · change Q.cupG.P a (3 - a) 3 _ x b = Q.cupG.P a (3 - a) 3 _ x b + sgn a • 0
      rw [smul_zero, add_zero]
    · change Q.cupL.P (a - 1) (3 - a) (3 - 1) _ 0 (ι.f (3 - a) (3 - a) rfl 0) +
          sgn a • Q.cupL.P a (3 - a - 1) (3 - 1) _ (res.f a a rfl x) y +
          Q.hU a (3 - a) (3 - 1) _ 0 0 =
        0 + sgn a • Q.cupL.P a (3 - a - 1) (3 - 1) _ (res.f a a rfl x) y
      simp only [map_zero, add_zero, zero_add]
  rw [e]
  let trP : (Q.E.X 3 × Q.EL.X (3 - 1)) →ₗ[A] A := tr
  change trP (_ + _) = trP _ + sgn a • trP _
  rw [map_add, map_zsmul]

/-- **The stage duality map of the Selmer stage data is the global duality map of `Q`**
(Nekovář, *Selmer complexes*, 5.4.3: `a ↦ ((b, y) ↦ tr(a ∪ b, (−1)^a res a ∪ y))`). Kind:
PROVED. -/
theorem stageDualityMap_eq_globalDualityMap :
    GHom.toCC (stageDualityMap (stagePairingInputOfSel Q tr htr)) =
      GHom.toCC (globalDualityMap Q tr htr) := by
  refine GHom.toCC_ext fun a x => dualCx_ext fun z => ?_
  obtain ⟨b, y⟩ := z
  refine (stageDualForm_apply (stagePairingInputOfSel Q tr htr) a (3 - a) (by omega) x
    (b, y)).trans ?_
  refine Eq.trans ?_ (globalDualityMap_eval Q tr htr a x b y).symm
  change stageGlobMap Q tr a (3 - a) _ x b +
    sgn a • locForm (stageLocMat Q tr) a (3 - a - 1) (res.f a a rfl x) y = _
  rw [stageGlobMap_apply, locForm_stageLocMat Q tr a (3 - a - 1) (by omega)]

/-- **The PRINT in the shape of `stageGlobalDuality`** gives the quasi-isomorphy of the stage
duality map (Nekovář, *Selmer complexes*, 5.4.3 at the stage). Kind: PROVED. -/
theorem quasiIso_stageDualityMap_of_global
    (hQ : QuasiIso (GHom.toCC (globalDualityMap Q tr htr))) :
    QuasiIso (GHom.toCC (stageDualityMap (stagePairingInputOfSel Q tr htr))) := by
  rw [stageDualityMap_eq_globalDualityMap]
  exact hQ

end Sel

/-! ### Residual finiteness in the shape `ResidualCohomologyFinite` -/

section ResidualFinite

variable {R : Type} [CommRing R]

/-- Finiteness of a subquotient along equalities of the maps. Kind: PROVED. -/
theorem moduleFinite_subquotient_congr {V W Z : Type} [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z] {f f' : V →ₗ[R] W}
    {g g' : W →ₗ[R] Z} (hf : f = f') (hg : g = g') :
    Module.Finite R (subquotientOf f g) ↔ Module.Finite R (subquotientOf f' g') := by
  subst hf hg
  rfl

/-- **The cohomology of a relation-indexed complex in degree `n` is its cocycles modulo
coboundaries**, for finiteness over the ring. Kind: PROVED. -/
theorem moduleFinite_homology_iff (C : GCx R) (n : ℤ) :
    Module.Finite R (C.toCC.homology n) ↔
      Module.Finite R (subquotientOf (C.d (n - 1) n (by omega)) (C.d n (n + 1) rfl)) := by
  have e := C.toCC.homologyIsoSc' (n - 1) n (n + 1) (CochainComplex.prev ℤ n)
    (CochainComplex.next ℤ n)
  have hr : LinearMap.range (C.toCC.sc' (n - 1) n (n + 1)).moduleCatToCycles =
      (LinearMap.range (C.toCC.sc' (n - 1) n (n + 1)).f.hom).comap
        (LinearMap.ker (C.toCC.sc' (n - 1) n (n + 1)).g.hom).subtype :=
    LinearMap.range_codRestrict _ _ _
  have e2 : C.toCC.homology n ≃ₗ[R] subquotientOf (C.toCC.sc' (n - 1) n (n + 1)).f.hom
      (C.toCC.sc' (n - 1) n (n + 1)).g.hom :=
    (e.toLinearEquiv.trans (C.toCC.sc' (n - 1) n (n + 1)).moduleCatHomologyIso.toLinearEquiv).trans
      (Submodule.quotEquivOfEq _ _ hr)
  have hf : (C.toCC.sc' (n - 1) n (n + 1)).f.hom = C.d (n - 1) n (by omega) :=
    LinearMap.ext fun x => GCx.toCC_d_hom C (n - 1) n (by omega) x
  have hg : (C.toCC.sc' (n - 1) n (n + 1)).g.hom = C.d n (n + 1) rfl :=
    LinearMap.ext fun x => GCx.toCC_d_hom C n (n + 1) rfl x
  refine Iff.trans ?_ (moduleFinite_subquotient_congr hf hg)
  exact Module.Finite.equiv_iff e2

variable [IsLocalRing R]

/-- **The finiteness of the finite free model from `ResidualCohomologyFinite`** (the shape of the
arithmetic input, `InnerLimitArith.StageInputs`): the residual cohomology of `C` in every degree is
finite over the residue field (tex 4392–4394). Kind: PROVED. -/
theorem finite_residualCohomologyAt_of {C : GCx R} (h : ResidualCohomologyFinite C) (n : ℤ) :
    Module.Finite (ResidueField R) (residualCohomologyAt C n) :=
  (moduleFinite_homology_iff (gcxBaseChange (ResidueField R) C) n).1 (h n)

end ResidualFinite

/-! ### The stage rings -/

section StageRings

/-- The zeroth stage ring is the zero ring. Kind: PROVED. -/
theorem stageA_zero_subsingleton : Subsingleton (StageA 0) :=
  Ideal.Quotient.subsingleton_iff.2 (by simp)

/-- The stage rings `A_i`, `i ≠ 0`, are local (the stage ring of Elliot's lemma). Kind: PROVED
(instance). -/
instance stageA_isLocalRing (i : ℕ) [NeZero i] : IsLocalRing (StageA i) :=
  inferInstanceAs (IsLocalRing (ZInQ.Manuscript.RC.Limits.ElliotRing i))

/-- The maximal ideal of a stage ring `A_i`, `i ≠ 0`, is nilpotent. Kind: PROVED. -/
theorem stageA_isNilpotent_maximalIdeal (i : ℕ) [NeZero i] :
    IsNilpotent (maximalIdeal (StageA i)) :=
  ZInQ.Manuscript.RC.Limits.ElliotRing.isNilpotent_maximalIdeal i

/-- **The stage matrix diagram over a zero ring**: every identity holds. Kind: definition. -/
def StageMatrixDiagram.ofSubsingleton (A : Type) [CommRing A] [Subsingleton A]
    (rank : ℤ → ℕ) : StageMatrixDiagram A rank where
  dC _ _ _ := 0
  dC_sq _ _ _ _ _ := Matrix.ext fun _ _ => Subsingleton.elim _ _
  res _ := 0
  res_comm _ := Matrix.ext fun _ _ => Subsingleton.elim _ _
  glob _ _ _ := 0
  loc _ _ := 0
  recip _ _ _ := Matrix.ext fun _ _ => Subsingleton.elim _ _
  rev _ := 0
  srcHom _ _ _ := 0
  tgtHom _ _ _ := 0
  chain _ := Matrix.ext fun _ _ => Subsingleton.elim _ _
  src _ := Matrix.ext fun _ _ => Subsingleton.elim _ _
  tgt _ := Matrix.ext fun _ _ => Subsingleton.elim _ _

end StageRings

/-! ### The end-to-end producer -/

section Producer

/-- **One stage of the producer** (tex 4391–4451 at the stage `A_i`): from the stage complex `G`
(flat terms, finite residual cohomology `ResidualCohomologyFinite`, bounded and bounded by `B`),
the Selmer pairing datum `Q` with the split local model and the PRINT quasi-isomorphism of its
global duality map, the graded finite free model and the transported matrix diagram; at the zero
ring `A_0` the trivial diagram. Kind: PROVED. -/
theorem exists_stage_diagram_of_inputs (i : ℕ) (G : GCx (StageA i))
    (hflat : ∀ n, Module.Flat (StageA i) (G.X n)) {U : GCx (StageA i)}
    {res : GHom G (splitLocalComplex (StageA i))} {ι : GHom U (splitLocalComplex (StageA i))}
    (Q : SelPairData (splitSelData G res U ι) (splitSelData G res U ι))
    (tr : (coneCx Q.resE).X 3 →ₗ[StageA i] StageA i)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (hdual : QuasiIso (GHom.toCC (globalDualityMap Q tr htr)))
    (hres : ∀ [NeZero i], ResidualCohomologyFinite G) (lo hi : ℤ)
    (hbdd : ∀ [NeZero i] (n : ℤ), n < lo ∨ hi < n →
      Module.finrank (ResidueField (StageA i)) (residualCohomologyAt G n) = 0)
    (B : ℕ) (hB : ∀ [NeZero i] (n : ℤ),
      Module.finrank (ResidueField (StageA i)) (residualCohomologyAt G n) ≤ B) :
    ∃ rk : ℤ → ℕ, (∀ n, n < lo ∨ hi < n → rk n = 0) ∧ (∀ n, rk n ≤ B) ∧
      (∀ [NeZero i] (n : ℤ),
        rk n = Module.finrank (ResidueField (StageA i)) (residualCohomologyAt G n)) ∧
      ∃ S : StageMatrixDiagram (StageA i) rk, i ≠ 0 → S.loc = stageLocMat Q tr := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    have := stageA_zero_subsingleton
    refine ⟨fun _ => 0, fun _ _ => rfl, fun _ => Nat.zero_le _, ?_,
      StageMatrixDiagram.ofSubsingleton _ _, fun h => absurd rfl h⟩
    intro _ _
    exact absurd rfl (NeZero.ne 0)
  · have : NeZero i := ⟨by omega⟩
    have : ∀ n, Module.Flat (StageA i) (G.X n) := hflat
    obtain ⟨R, hR⟩ := exists_gradedModel (stageA_isNilpotent_maximalIdeal i) G
      (finite_residualCohomologyAt_of hres)
    have hr : ∀ k, k < lo ∨ hi < k → R.rank k = 0 := fun k hk => (hR k).trans (hbdd k hk)
    obtain ⟨S, -, -, -, hloc⟩ := exists_stageMatrixDiagram R (stagePairingInputOfSel Q tr htr)
      (quasiIso_stageDualityMap_of_global Q tr htr hdual) lo hi hr
    exact ⟨R.rank, hr, fun n => (hR n).trans_le (hB n), fun n => hR n, S, fun _ => hloc⟩

/-- **The end-to-end producer of the retained inner-limit data** (Lemma `ex:limits-inner-limit`,
tex 4391–4451; tex 4385–4388, 4400–4406): from the stagewise arithmetic inputs — the stage
complexes `G i` with flat terms (GLUE: the actual stage Selmer cochains, flat by
`InnerLimitArith.StageFlat`), the Selmer pairing data `Q i` with the split local model at the
derivative label and traces `tr i` (GLUE; their production from the actual local cochains at `q_i`
needs a `LocalDegreeTwoCoordinate` — OPEN), the global duality quasi-isomorphisms (PRINT,
Nekovář, *Selmer complexes*, 5.4.3 at `A_i`, the shape of `stageGlobalDuality`), the residual
finiteness `ResidualCohomologyFinite (G i)` (OPEN), bounded residual cohomology and a uniform
bound `B` on the residual ranks (ELLIOT: "a tuple whose model ranks are bounded") — the retained
data `C`, `D`, `E` of round two over `Λ` exist, with the model ranks the residual ranks on a
`U`-large set, and the local pairing of `D` lifting the actual stage local pairings
`tr(0, · ∪ ·)` at every stage. Kind: PROVED. -/
theorem exists_retained_of_stageInputs (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (G : ∀ i, GCx (StageA i)) (hflat : ∀ i n, Module.Flat (StageA i) ((G i).X n))
    (Uc : ∀ i, GCx (StageA i)) (res : ∀ i, GHom (G i) (splitLocalComplex (StageA i)))
    (ι : ∀ i, GHom (Uc i) (splitLocalComplex (StageA i)))
    (Q : ∀ i, SelPairData (splitSelData (G i) (res i) (Uc i) (ι i))
      (splitSelData (G i) (res i) (Uc i) (ι i)))
    (tr : ∀ i, (coneCx (Q i).resE).X 3 →ₗ[StageA i] StageA i)
    (htr : ∀ i z, tr i ((coneCx (Q i).resE).d 2 3 rfl z) = 0)
    (hdual : ∀ i, QuasiIso (GHom.toCC (globalDualityMap (Q i) (tr i) (htr i))))
    (hres : ∀ i [NeZero i], ResidualCohomologyFinite (G i)) (lo hi : ℤ)
    (hbdd : ∀ i [NeZero i] (n : ℤ), n < lo ∨ hi < n →
      Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (G i) n) = 0)
    (B : ℕ) (hB : ∀ i [NeZero i] (n : ℤ),
      Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (G i) n) ≤ B) :
    ∃ (r₀ : ℤ → ℕ) (C : ComplexStages (R := Lambda) stageIdeal U)
      (D : RetainedLimitPairingStages U C) (_ : RetainedGlobalDualityStages D),
      C.rank = r₀ ∧ C.low = lo ∧ C.high = hi ∧ (∀ n, r₀ n ≤ B) ∧
      (∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i] (n : ℤ),
        r₀ n = Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (G i) n)) ∧
      ∀ i, i ≠ 0 → ∀ a b, (D.loc a b i).map (stageMap i) = stageLocMat (Q i) (tr i) a b := by
  choose rk hrk0 hrkB hrkfin hS using fun i => exists_stage_diagram_of_inputs i (G i) (hflat i)
    (Q i) (tr i) (htr i) (hdual i) (hres i) lo hi (hbdd i) B (hB i)
  choose S hSloc using hS
  obtain ⟨r₀, C, D, E, hC, hlow, hhigh, hr₀B, hev, hloc, -⟩ :=
    exists_retained_of_stageDiagrams U hU rk S lo hi B hrk0 hrkB
  refine ⟨r₀, C, D, E, hC, hlow, hhigh, hr₀B, ?_, ?_⟩
  · filter_upwards [hev] with i hri
    intro _ n
    rw [← hri]
    exact hrkfin i n
  · intro i hi0 a b
    rw [hloc i a b, hSloc i hi0]

end Producer

/-! ### The chain to the inner-limit certificate -/

section Certificate

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open ZInQ.Contrib.RC53Assist.InnerLimit (FibreInnerLimitPairingCertificate)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **From the stagewise arithmetic inputs to the inner-limit pairing certificate** (tex
4385–4451, 5027–5070): the retained data produced by `exists_retained_of_stageInputs` satisfy the
round-two certificate `fibreInnerLimitPairingCertificate_of_retained` at every height-one prime `𝔭`
at which the limit local pairing is the transported switch pairing (`hloc`, the residue identity
with `J = ρ_T(τ)`, tex 5037; supplied by the arithmetic label). The stage local pairings of the
produced `D` are the actual `tr(0, · ∪ ·)` at every stage. Kind: PROVED. -/
theorem exists_certificate_of_stageInputs (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (G : ∀ i, GCx (StageA i)) (hflat : ∀ i n, Module.Flat (StageA i) ((G i).X n))
    (Uc : ∀ i, GCx (StageA i)) (res : ∀ i, GHom (G i) (splitLocalComplex (StageA i)))
    (ι : ∀ i, GHom (Uc i) (splitLocalComplex (StageA i)))
    (Q : ∀ i, SelPairData (splitSelData (G i) (res i) (Uc i) (ι i))
      (splitSelData (G i) (res i) (Uc i) (ι i)))
    (tr : ∀ i, (coneCx (Q i).resE).X 3 →ₗ[StageA i] StageA i)
    (htr : ∀ i z, tr i ((coneCx (Q i).resE).d 2 3 rfl z) = 0)
    (hdual : ∀ i, QuasiIso (GHom.toCC (globalDualityMap (Q i) (tr i) (htr i))))
    (hres : ∀ i [NeZero i], ResidualCohomologyFinite (G i)) (lo hi : ℤ)
    (hbdd : ∀ i [NeZero i] (n : ℤ), n < lo ∨ hi < n →
      Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (G i) n) = 0)
    (B : ℕ) (hB : ∀ i [NeZero i] (n : ℤ),
      Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (G i) n) ≤ B) :
    ∃ (C : ComplexStages (R := Lambda) stageIdeal U) (D : RetainedLimitPairingStages U C),
      (∀ i, i ≠ 0 → ∀ a b, (D.loc a b i).map (stageMap i) = stageLocMat (Q i) (tr i) a b) ∧
      ∀ (P : Ideal Lambda) [P.IsPrime] (ε₀ ε₂ ε σ : ResAt P), ε₂ ≠ 0 → ε ≠ 0 → σ ≠ 0 →
        localPairingOfMat (D.locK P) = transportedPairing ε₀ ε₂ ε σ (conjMatrix Cn W hW P) →
        FibreInnerLimitPairingCertificate U hU P C (D.resLimit hU P) ε σ
          (conjMatrix Cn W hW P) := by
  obtain ⟨_, C, D, E, -, -, -, -, -, hloc⟩ := exists_retained_of_stageInputs U hU G hflat Uc res
    ι Q tr htr hdual hres lo hi hbdd B hB
  exact ⟨C, D, hloc, fun P _ ε₀ ε₂ ε σ hε₂ hε hσ hl =>
    fibreInnerLimitPairingCertificate_of_retained hU E P Cn W hW ε₀ ε₂ ε σ hε₂ hε hσ hl⟩

end Certificate

end ZInQ.Manuscript.RC.FibreDuality

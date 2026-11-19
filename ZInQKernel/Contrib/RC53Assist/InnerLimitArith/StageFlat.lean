import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Selmer
import ZInQKernel.Contrib.OneProof.RC.Limits.FlatFree

/-!
# The actual stage cochain modules are flat and free

The finite free model of the retained inner-limit lemma applies to a complex of flat modules over
a local ring with nilpotent maximal ideal whose residual cohomology is finite. This file supplies
the flatness for the actual continuous cochains of the Selmer complexes at a finite coefficient
stage.

* `contCochainLCEquiv`: for a discrete coefficient module, the continuous cochains
  `C^n_cont(G, M)` are the locally constant functions `G^n → M`, linearly.
* `flat_contCochains`, `free_contCochains`: for compact `G` and a flat discrete `M`, the actual
  cochain modules are flat, and free over a local ring with nilpotent maximal ideal.
* `free_selmerCochains`, `flat_selmerCochains`: over a local ring with nilpotent maximal ideal,
  the Selmer cochain modules of the actual Galois Selmer data with finitely many places are free,
  hence flat, as soon as the local-condition modules are free; in particular for the relaxed and
  the strict conditions.

Source: the retained inner-limit lemma, manuscript lines 4391–4414.
-/

set_option maxHeartbeats 400000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.InnerLimitArith

open CategoryTheory Module
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

section Cochains

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

variable (R G M) in
/-- **Continuous cochains with discrete coefficients are the locally constant functions.** -/
def contCochainLCEquiv (n : ℕ) :
    (contCochains R G M).X n ≃ₗ[R] LocallyConstant (Fin n → G) M where
  toFun f := ⟨asFun R G M ((contSubCx R G M).el f : contCochain R G M n),
    (IsLocallyConstant.iff_continuous _).mpr ((contSubCx R G M).el f).2⟩
  invFun g := (contSubCx R G M).ofSub ⟨(g : (Fin n → G) → M), g.continuous⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The actual cochain modules are flat** for compact `G` and flat discrete coefficients. -/
theorem flat_contCochains [CompactSpace G] [Module.Flat R M] (n : ℕ) :
    Module.Flat R ((contCochains R G M).X n) :=
  have := ZInQ.Manuscript.RC.Limits.flat_locallyConstant R (X := Fin n → G) M
  Module.Flat.of_linearEquiv (contCochainLCEquiv R G M n)

/-- **The actual cochain modules are free** over a local ring with nilpotent maximal ideal. -/
theorem free_contCochains [IsLocalRing R] (hnil : IsNilpotent (IsLocalRing.maximalIdeal R))
    [CompactSpace G] [Module.Flat R M] (n : ℕ) : Module.Free R ((contCochains R G M).X n) :=
  have := flat_contCochains (R := R) (G := G) (M := M) n
  ZInQ.Manuscript.RC.Limits.flat_module_free hnil

end Cochains

/-! ### The Selmer cochain modules -/

section Selmer

variable {k : Type} [CommRing k] [IsLocalRing k] (hnil : IsNilpotent (IsLocalRing.maximalIdeal k))

omit [IsLocalRing k] in
/-- Extension by zero preserves freeness. -/
theorem free_natX (K : CochainComplex (ModuleCat.{0} k) ℕ)
    (hK : ∀ n, Module.Free k (K.X n)) (m : ℤ) : Module.Free k ((natCx K).X m) := by
  match m with
  | Int.ofNat n => exact hK n
  | Int.negSucc _ =>
    change Module.Free k PUnit
    infer_instance

omit [IsLocalRing k] in
/-- The Selmer cochain modules `G^n × U^n × L^{n-1}` are free when the three are. -/
theorem free_selX (D : SelData k) (n : ℤ) [Module.Free k (D.G.X n)] [Module.Free k (D.U.X n)]
    [Module.Free k (D.L.X (n - 1))] : Module.Free k ((selCx D).X n) := by
  change Module.Free k (D.G.X n × D.U.X n × D.L.X (n - 1))
  infer_instance

variable (GS : Type) [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS] [CompactSpace GS]
  {ι : Type} [Fintype ι] (Gv : ι → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] [∀ v, CompactSpace (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul GS M] [Module.Flat k M]

omit [Fintype ι] in
include hnil in
/-- The global cochain modules of the actual Selmer data are free. -/
theorem free_globalCx (m : ℤ) : Module.Free k ((globalCx k GS M).X m) :=
  free_natX _ (fun n => free_contCochains (R := k) (G := GS) (M := M) hnil n) m

omit [IsTopologicalGroup GS] [CompactSpace GS] in
include hnil in
/-- The local cochain modules of the actual Selmer data are free. -/
theorem free_localSumCx (m : ℤ) : Module.Free k ((localSumCx k GS Gv loc M).X m) := by
  have : ∀ v, Module.Flat k (ResMod (loc v) M) := fun v => inferInstanceAs (Module.Flat k M)
  have : ∀ v, Module.Free k ((localCx k GS Gv loc M v).X m) := fun v =>
    free_natX _ (fun n => free_contCochains (R := k) (G := Gv v) (M := ResMod (loc v) M)
      hnil n) m
  change Module.Free k (∀ v, (localCx k GS Gv loc M v).X m)
  infer_instance

include hnil in
/-- **The Selmer cochain modules of the actual Galois Selmer data are free**, hence flat, over a
local ring with nilpotent maximal ideal, when the local-condition modules are free. -/
theorem free_selmerCochains (Δ : LocalConditions k GS Gv loc M)
    (hΔ : ∀ v (m : ℤ), Module.Free k ((Δ.U v).X m)) (n : ℤ) :
    Module.Free k ((selCx (selData k GS Gv loc M Δ)).X n) := by
  have : Module.Free k ((selData k GS Gv loc M Δ).G.X n) := free_globalCx hnil GS M n
  have : Module.Free k ((selData k GS Gv loc M Δ).U.X n) := by
    have := fun v => hΔ v n
    change Module.Free k (∀ v, (Δ.U v).X n)
    infer_instance
  have : Module.Free k ((selData k GS Gv loc M Δ).L.X (n - 1)) :=
    free_localSumCx hnil GS Gv loc M (n - 1)
  exact free_selX _ n

include hnil in
theorem flat_selmerCochains (Δ : LocalConditions k GS Gv loc M)
    (hΔ : ∀ v (m : ℤ), Module.Free k ((Δ.U v).X m)) (n : ℤ) :
    Module.Flat k ((selCx (selData k GS Gv loc M Δ)).X n) :=
  have := free_selmerCochains hnil GS Gv loc M Δ hΔ n
  inferInstance

include hnil in
/-- The Selmer cochain modules with the relaxed conditions are free. -/
theorem free_relaxedSelmerCochains (n : ℤ) :
    Module.Free k ((selCx (selData k GS Gv loc M (relaxedConditions k GS Gv loc M))).X n) := by
  have : ∀ v, Module.Flat k (ResMod (loc v) M) := fun v => inferInstanceAs (Module.Flat k M)
  exact free_selmerCochains hnil GS Gv loc M _ (fun v m => free_natX _
    (fun n => free_contCochains (R := k) (G := Gv v) (M := ResMod (loc v) M) hnil n) m) n

include hnil in
/-- The Selmer cochain modules with the strict conditions are free. -/
theorem free_strictSelmerCochains (n : ℤ) :
    Module.Free k ((selCx (selData k GS Gv loc M (strictConditions k GS Gv loc M))).X n) :=
  free_selmerCochains hnil GS Gv loc M _ (fun _ _ => by
    change Module.Free k PUnit
    infer_instance) n

end Selmer

end ZInQ.Contrib.RC53Assist.InnerLimitArith

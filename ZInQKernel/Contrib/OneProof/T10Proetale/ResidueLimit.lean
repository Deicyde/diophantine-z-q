import ZInQKernel.Contrib.OneProof.T10Proetale.Tower

/-!
# Continuous sections in the residue tower

The topology on the padic integers is detected by their finite residues.
Consequently, compatible continuous sections of the residue tower assemble to
a continuous padic section over every object.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped PadicInt Topology

namespace ZInQ.Manuscript.T10Proetale

noncomputable section

variable (ℓ : ℕ)

/-- Compatible families of residues, as a ring. -/
def compatibleResidues : Subring (∀ n : ℕ, ZMod (ℓ ^ n)) where
  carrier := {a | ∀ n, residueStep ℓ n (a (n + 1)) = a n}
  one_mem' n := map_one _
  mul_mem' ha hb n := by
    change residueStep ℓ n (_ * _) = _
    rw [map_mul, ha n, hb n]
    rfl
  zero_mem' n := map_zero _
  add_mem' ha hb n := by
    change residueStep ℓ n (_ + _) = _
    rw [map_add, ha n, hb n]
    rfl
  neg_mem' ha n := by
    change residueStep ℓ n (-_) = _
    rw [map_neg, ha n]
    rfl

/-- Evaluation of a compatible family at level `n`. -/
def residueEval (n : ℕ) : compatibleResidues ℓ →+* ZMod (ℓ ^ n) :=
  (Pi.evalRingHom _ n).comp (compatibleResidues ℓ).subtype

/-- Compatibility of adjacent residues implies compatibility for all reductions. -/
theorem residueEval_compat (i j : ℕ) (h : i ≤ j) :
    (ZMod.castHom (pow_dvd_pow ℓ h) _).comp (residueEval ℓ j) = residueEval ℓ i := by
  induction h with
  | refl =>
    ext a
    change ZMod.castHom (dvd_refl _) _ (a.val i) = a.val i
    simp
  | @step j h ih =>
    ext a
    have ha : residueStep ℓ j (residueEval ℓ (j + 1) a) = residueEval ℓ j a := a.2 j
    have hi := DFunLike.congr_fun ih a
    change ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ_of_le h)) _ (residueEval ℓ (j + 1) a) = _
    rw [← ZMod.castHom_comp (pow_dvd_pow ℓ h) (pow_dvd_pow ℓ (Nat.le_succ j))]
    exact (congrArg (ZMod.castHom (pow_dvd_pow ℓ h) _) ha).trans hi

variable [Fact ℓ.Prime]

/-- The padic integer with the specified residues. -/
def padicOfResidues : compatibleResidues ℓ →+* ℤ_[ℓ] :=
  PadicInt.lift (residueEval_compat ℓ)

/-- The lift has the given residues. -/
theorem toResidue_padicOfResidues (n : ℕ) (a : compatibleResidues ℓ) :
    PadicInt.toZModPow n (padicOfResidues ℓ a) = a.val n :=
  DFunLike.congr_fun (PadicInt.lift_spec (residueEval_compat ℓ) n) a

/-- A map into the padic integers is continuous if all its residue maps are continuous. -/
theorem continuous_of_continuous_residues {T : Type*} [TopologicalSpace T] (f : T → ℤ_[ℓ])
    (hf : ∀ n, Continuous (fun t => PadicInt.toZModPow n (f t))) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt ℓ hε
  let r (s : T) := PadicInt.toZModPow n (f s)
  have hr : ∀ᶠ s in 𝓝 t, r s = r t :=
    (hf n).continuousAt.eventually_mem
      ((isOpen_discrete ({r t} : Set (ZMod (ℓ ^ n)))).mem_nhds (Set.mem_singleton _))
  filter_upwards [hr] with s hs
  apply lt_of_le_of_lt _ hn
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
    RingHom.mem_ker, map_sub, sub_eq_zero]
  exact hs

/-- A compatible family of continuous residue maps has a unique continuous padic lift. -/
theorem existsUnique_continuous_residueLift {T : Type*} [TopologicalSpace T]
    (s : ∀ n, C(T, ZMod (ℓ ^ n)))
    (hs : ∀ n t, residueStep ℓ n (s (n + 1) t) = s n t) :
    ∃! f : C(T, ℤ_[ℓ]), ∀ n t, PadicInt.toZModPow n (f t) = s n t := by
  let f (t : T) := padicOfResidues ℓ ⟨fun n => s n t, fun n => hs n t⟩
  have hf (n : ℕ) (t : T) : PadicInt.toZModPow n (f t) = s n t :=
    toResidue_padicOfResidues ℓ n _
  have hc : Continuous f := continuous_of_continuous_residues ℓ f
    (fun n => by simpa only [hf] using (s n).continuous)
  refine ⟨⟨f, hc⟩, hf, fun g hg => ContinuousMap.ext fun t => ?_⟩
  exact PadicInt.ext_of_toZModPow.mp fun n => (hg n t).trans (hf n t).symm

end
end ZInQ.Manuscript.T10Proetale

import ZInQKernel.Contrib.OneProof.RC.Local.TameLocalQuotientPlace
import ZInQKernel.Contrib.CloudB3E1TameKummer.TameKummerPlace

/-!
# The quotient retraction at the two places from the two literature statements

Manuscript `diophantine_zq.tex`, tex 3470–3481 ((4.4) at augmentation), tex 4176–4184 (the two
quotient blocks at the conjugate places of an unused split prime).

Lane RC31's `exists_retract_localQuotient_place` and `exists_retract_twoPlaces_place` take the
statement `TameCochainQuasiIso`. The instance they consume (at the completion of a number field
at a finite place of odd residue cardinality, field coefficients inflated from the unramified
quotient) is PROVED by lane E1 from the PRINT `MilneADT_I_2_8`
(`TameKummerPlace.quasiIso_inflation_of_milne`). Here the two retractions are restated with
`MilneADT_I_2_8` in place of `TameCochainQuasiIso`, so that they rest on the two literature
statements `MilneADT_I_2_8` (Milne, *Arithmetic Duality Theorems*, I.2.8) and
`IwasawaGenerators` (Iwasawa 1955; Neukirch–Schmidt–Wingberg 7.5.1–7.5.3).

* `exists_retract_localQuotient_milne`: at one place.
* **`exists_retract_twoPlaces_milne`**: at the two conjugate places, onto `twoSingCx Fr q z z⁻¹`.

Kinds: PROVED (from the PRINTs).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.Limits
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
open ZInQ.Contrib.CloudB3RC53.RankCounts (GUr)
open ZInQ.Manuscript.RC.Local (IwasawaGenerators singCx twoSingCx prodGCx
  exists_retract_localQuotient_sep two_not_mem_of_odd_card natCard_residueField_adicCompletion
  resUr_of_isArithFrobeniusLift resUr_of_mem_inertia)

attribute [local instance] TopRep.distribMulAction

/-- **The local quotient at a finite place retracts onto the singular block, from Milne and
Iwasawa** (tex 3470–3480, 4176–4184): lane RC31's `exists_retract_localQuotient_place` with the
PRINT `MilneADT_I_2_8` in place of `TameCochainQuasiIso` (lane E1's
`quasiIso_inflation_of_milne`). Kind: PROVED (from the PRINTs). -/
theorem exists_retract_localQuotient_milne (h28 : MilneADT_I_2_8) (hI : IwasawaGenerators)
    {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type} [Field k]
    [TopologicalSpace k] {M : Type} [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [Finite M]
    (w : Places K S) (X : TopRep.{0} k (GUr K w.1)) [ContinuousSMul (GUr K w.1) X.V]
    [DiscreteTopology X.V] [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x)
    (hbij : Function.Bijective f) (hexp : ∃ n : ℕ, ∀ m : M, (2 ^ n) • m = 0)
    (q : ℕ) (hq : Odd q) (hqcard : q = Nat.card (𝓞 K ⧸ w.1.asIdeal))
    (E : SplitInclusion (ofCC (urCx K w.1 X))
      (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M w))
    (hE : E.i = ofCCHom (urToLocal_galois K S w X f hf)) :
    Nonempty (GRetract E.quotientCx (singCx (frob (eUr K w.1) X) q)) := by
  have h2 : (2 : 𝓞 K) ∉ w.1.asIdeal := two_not_mem_of_odd_card (hqcard ▸ hq)
  obtain ⟨φ, σ, P, hIw⟩ := hI K w.1 h2
  have hq' := hqcard.trans (natCard_residueField_adicCompletion K w.1).symm
  subst hq'
  have : Finite (ResMod (locMap K S w.1) M) := inferInstanceAs (Finite M)
  have hexp' : ∃ e : ℕ, ∀ m : ResMod (locMap K S w.1) M, 2 ^ e • m = 0 := hexp
  let f' : X.V →ₗ[k] ResMod (locMap K S w.1) M := f
  have hbij' : Function.Bijective f' := hbij
  have hf' : ∀ (g : Gloc K w.1) (x : X.V), f' (resUr K w.1 g • x) = g • f' x := hf
  have hQ := ZInQ.Manuscript.RC.Local.TameKummerPlace.quasiIso_inflation_of_milne h28 h2 k
    (ResMod (locMap K S w.1) M) X f' hf' hbij'.2 hIw hexp'
  obtain ⟨R, -⟩ := exists_retract_localQuotient_sep (eUr K w.1) (resUr K w.1) X
    (G := Gloc K w.1) (M := ResMod (locMap K S w.1) M) f' hbij' hf' _ φ σ _ hq _
    (resUr_of_isArithFrobeniusLift hIw.frob) (resUr_of_mem_inertia hIw.mem_inertia) hIw.rel
    E hE hQ
  exact ⟨R⟩

/-- **The two local quotients at the conjugate places retract onto the two singular blocks, from
Milne and Iwasawa** (tex 4176–4184): lane RC31's `exists_retract_twoPlaces_place` with the PRINT
`MilneADT_I_2_8` in place of `TameCochainQuasiIso`. Kind: PROVED (from the PRINTs). -/
theorem exists_retract_twoPlaces_milne (h28 : MilneADT_I_2_8) (hI : IwasawaGenerators)
    {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type} [Field k]
    [TopologicalSpace k] {M : Type} [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [Finite M]
    (hexp : ∃ n : ℕ, ∀ m : M, (2 ^ n) • m = 0) (q : ℕ) (hq : Odd q)
    (F : Matrix (Fin 2) (Fin 2) k) (z zi : k)
    (w₁ : Places K S) (X₁ : TopRep.{0} k (GUr K w₁.1)) [ContinuousSMul (GUr K w₁.1) X₁.V]
    [DiscreteTopology X₁.V] [Finite X₁.V] (f₁ : X₁.V →ₗ[k] M)
    (hf₁ : ∀ (g : Gloc K w₁.1) (x : X₁.V), f₁ (resUr K w₁.1 g • x) = locMap K S w₁.1 g • f₁ x)
    (hbij₁ : Function.Bijective f₁) (hq₁ : q = Nat.card (𝓞 K ⧸ w₁.1.asIdeal))
    (E₁ : SplitInclusion (ofCC (urCx K w₁.1 X₁))
      (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M w₁))
    (hE₁ : E₁.i = ofCCHom (urToLocal_galois K S w₁ X₁ f₁ hf₁))
    (b₁ : X₁.V ≃ₗ[k] (Fin 2 → k))
    (hb₁ : ∀ v, b₁ (frob (eUr K w₁.1) X₁ v) = Matrix.toLin' (z • F) (b₁ v))
    (w₂ : Places K S) (X₂ : TopRep.{0} k (GUr K w₂.1)) [ContinuousSMul (GUr K w₂.1) X₂.V]
    [DiscreteTopology X₂.V] [Finite X₂.V] (f₂ : X₂.V →ₗ[k] M)
    (hf₂ : ∀ (g : Gloc K w₂.1) (x : X₂.V), f₂ (resUr K w₂.1 g • x) = locMap K S w₂.1 g • f₂ x)
    (hbij₂ : Function.Bijective f₂) (hq₂ : q = Nat.card (𝓞 K ⧸ w₂.1.asIdeal))
    (E₂ : SplitInclusion (ofCC (urCx K w₂.1 X₂))
      (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M w₂))
    (hE₂ : E₂.i = ofCCHom (urToLocal_galois K S w₂ X₂ f₂ hf₂))
    (b₂ : X₂.V ≃ₗ[k] (Fin 2 → k))
    (hb₂ : ∀ v, b₂ (frob (eUr K w₂.1) X₂ v) = Matrix.toLin' (zi • F) (b₂ v)) :
    Nonempty (GRetract (prodGCx E₁.quotientCx E₂.quotientCx) (twoSingCx F q z zi)) := by
  obtain ⟨R₁⟩ := exists_retract_localQuotient_milne h28 hI w₁ X₁ f₁ hf₁ hbij₁ hexp q hq hq₁ E₁
    hE₁
  obtain ⟨R₂⟩ := exists_retract_localQuotient_milne h28 hI w₂ X₂ f₂ hf₂ hbij₂ hexp q hq hq₂ E₂
    hE₂
  exact ⟨ZInQ.Manuscript.RC.Local.GRetract.twoPlaces _ _ F q z zi b₁ hb₁ b₂ hb₂ R₁ R₂⟩

end ZInQ.Manuscript.RC.Wiring

import ZInQKernel.Contrib.OneProof.RC.Visibility.Genus
import ZInQKernel.Contrib.OneProof.RC.Wiring.Odd

/-!
# Lane RC23: `VisibilityInputs D` from the genuine genus points (App F, (O.7)–(O.8), tex 9101–9445)

The integration tree's wiring (`RC/Wiring/Odd.lean`) reduces the skeleton's field
`RCSteps.visibility` ((O.8), App F `ex:app-visibility`, tex 9407–9445) to

`VisibilityInputs D = ∃ λ ω C, (O.7) for λ ∧ (native-index bound at simple zeros) ∧ (torsion bound)`.

This file produces `VisibilityInputs D` over the genuine objects of `Visibility/Genus.lean`:
`λ := lamOf` (the stage maps applied to `L` times the genus points of the selected genus data),
`j_gen := jgenOf` (batch 3's native index), constant `C = 0`. The native-index bound and the torsion
clause are PROVED (from the printed leaves, batch 3's GLUE and the stage maps' additivity); the only
remaining input about the theta side is (O.7) itself for this `λ`, which `Visibility/Theta.lean`
derives in turn from the finite theta coefficient (O.4), its orbit parametrization, the
Cornut–Jetchev reduction identity and the orientation signs (`Visibility/Models.lean`).

Every hypothesis of `visibilityInputs_of_genuine`, with its kind and tex lines:
* `P : Prints` — PRINT (BCDT, Dokchitser–Dokchitser, Cai–Shu–Tian) and GLUE (Kolyvagin Thm 1,
  cited statement); the shared layer;
* `hArtin : ArtinFactorization` — batch 3's GLUE: `L(E/K, χ_{h_*} ∘ N, s) = L(E^{(h_*)}, s) L(E^{(D)}, s)`
  (Artin formalism; tex 2432, 8268–8270) — the only GLUE of the height-formula step (the splitting
  criterion is batch 3's `splittingCriterion_proof`, PROVED);
* `hf hLat hNC hκ` — the newform, period lattice and parametrization data of the shared layer's
  Cai–Shu–Tian statement (definitions);
* `hgp : GenusPartner` — the genus partner `h_*` (tex 2403–2408, App F 8249–8256; RC13 / batch 3);
* `selG`, `hjgen` — the selected genus data and `j_gen = jgenOf` on admissible `D` (definition,
  tex 2411–2416; batch 3's form);
* `hL : MultiplierKillsNativeTorsion` — GLUE (tex 8274–8297, 9423);
* `ev : StageKummer` — the stage maps `λ_{M_θ} ∘ reduction` (interface, tex 8378–8456, 9283–9290);
* `hprep : AdmissiblePrepared` — definition (tex 8209–8212: admissible `D` are positive,
  squarefree, prime to the fixed support, squares at `2N`);
* `hsign : AdmissibleOddSign` — GLUE (tex 9417 states the torsion clause for "admissible odd-sign
  `D`"; every admissible `D` has odd sign by the twist root-number formula of tex 8587–8588);
* `hO7` — (O.7) for `λ = lamOf` (ELLIOT + PRINT, tex 9101–9405; reduced in `Visibility/Models.lean`).
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory

namespace ZInQ.Manuscript.RC.Visibility

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring ZInQ.Contrib.CloudB3RC53
  ZInQ.Contrib.CloudB3RC53.GenusOdd ZInQ.Contrib.CloudB3RC53.CST

/-- **Definition (tex 8209–8212).** Admissible parameters lie in batch 3's prepared filter: an
admissible `D` is positive, squarefree, a unit square at every prime of `2N` and prime to `h_*`. -/
def AdmissiblePrepared {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∀ θ : ℕ, ∀ Dd : ℤ, D.admissible θ Dd → Prepared (Ecurve ℓ) D.hstar Dd

/-- **GLUE (tex 9417, 8209–8212, 8587–8588).** Every admissible `D` has odd sign:
`w(E^{(D)}) = w(E) χ_D(−N) = −1` (root number `−1` of `E`, `D > 0` and `D` a square at the primes of
`N`). Elliot states the torsion clause for "an admissible odd-sign `D`"; the wiring's
`VisibilityInputs` drops "odd-sign", so this is the GLUE that restores it. -/
def AdmissibleOddSign {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∀ θ : ℕ, ∀ Dd : ℤ, D.admissible θ Dd → RootNumber (Etw ℓ Dd) (-1)

/-- **`VisibilityInputs D` (PROVED from the inputs listed in the module docstring).** The witness is
`λ = lamOf`, `ω` the given `ω(N)`, `C = 0`. -/
theorem visibilityInputs_of_genuine {ℓ : ℕ} (D : RCData ℓ) [(Ecurve ℓ).IsElliptic]
    (P : Prints) (hArtin : ArtinFactorization)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat) (hNC : IsNonCMLattice Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ)
    (hgp : GenusPartner (Ecurve ℓ) D.hstar)
    (selG : (h : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ (h * D.hstar) 1 D.hstar))
    (hjgen : ∀ θ : ℕ, ∀ Dd : ℤ, D.admissible θ Dd →
      D.jgen Dd = jgenOf (Ecurve ℓ) f Lat κ D.hstar selG Dd)
    {L : ℕ} (hL : MultiplierKillsNativeTorsion (Ecurve ℓ) f Lat κ D.hstar L)
    (ev : StageKummer (Ecurve ℓ) f Lat κ D.hstar D.Mθ)
    (hprep : AdmissiblePrepared D) (hsign : AdmissibleOddSign D) (ω : ℕ)
    (hO7 : Odd.ThetaComparison D.Mθ D.aθ (lamOf D.Mθ L selG ev) D.admissible ω) :
    VisibilityInputs D := by
  refine ⟨lamOf D.Mθ L selG ev, ω, 0, hO7, ?_, ?_⟩
  · intro θ Dd hadm _ k hk hkj
    rw [hjgen θ Dd hadm, sub_zero] at hkj
    exact lamOf_native_bound D.Mθ selG ev hL θ Dd k hk hkj
  · intro θ Dd hadm hnot
    exact lamOf_torsion P hArtin hf hLat hNC hκ hgp D.Mθ selG ev hL
      (hprep θ Dd hadm) (hsign θ Dd hadm) hnot θ

/-- **`RCSteps.visibility` ((O.8))**, PROVED from the same inputs through the wiring's
`visibilityTarget_of_inputs`. -/
theorem visibilityTarget_of_genuine {ℓ : ℕ} (D : RCData ℓ) [(Ecurve ℓ).IsElliptic]
    (P : Prints) (hArtin : ArtinFactorization)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat) (hNC : IsNonCMLattice Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ)
    (hgp : GenusPartner (Ecurve ℓ) D.hstar)
    (selG : (h : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ (h * D.hstar) 1 D.hstar))
    (hjgen : ∀ θ : ℕ, ∀ Dd : ℤ, D.admissible θ Dd →
      D.jgen Dd = jgenOf (Ecurve ℓ) f Lat κ D.hstar selG Dd)
    {L : ℕ} (hL : MultiplierKillsNativeTorsion (Ecurve ℓ) f Lat κ D.hstar L)
    (ev : StageKummer (Ecurve ℓ) f Lat κ D.hstar D.Mθ)
    (hprep : AdmissiblePrepared D) (hsign : AdmissibleOddSign D) (ω : ℕ)
    (hO7 : Odd.ThetaComparison D.Mθ D.aθ (lamOf D.Mθ L selG ev) D.admissible ω) :
    VisibilityTarget D :=
  visibilityTarget_of_inputs D (visibilityInputs_of_genuine D P hArtin hf hLat hNC hκ hgp selG hjgen hL
    ev hprep hsign ω hO7)

end ZInQ.Manuscript.RC.Visibility

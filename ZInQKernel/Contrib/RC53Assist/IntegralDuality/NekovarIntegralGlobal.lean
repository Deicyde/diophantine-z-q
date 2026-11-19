import ZInQKernel.Contrib.RC53Assist.IntegralDuality.IntegralTatePairing
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TruncIsotropyGenuine
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Prints
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Duality

/-!
# Integral global Poitou–Tate duality over the two-adic integers: the printed interface

This file records, as a proposition with no inhabitant, the specialization of
Nekovář, *Selmer complexes*, Proposition 5.4.3(ii) (printed p. 127) to the ring of two-adic
integers. The dualizing complex is the normalized one; the ring is Gorenstein of dimension
one, so the dualizing target is the derived dual shifted by three (2.4.4, 2.5, 2.7(iii),
pp. 54–55). The standing hypotheses are those of 5.1 (p. 113): a number field without real
places, and a finite set of finite places containing the places above two.

The coefficients are arbitrary finite free modules with the two-adic module topology and a
continuous Galois action (admissible in the sense of 3.2.1). The pairing takes values in the
actual integral cyclotomic line and is equivariant, continuous and perfect. No local condition
enters: the complexes are the global continuous cochains and the compactly supported ones,
i.e. the Selmer complexes of the strict conditions, with the zero isotropy homotopy.

The degree-three trace is a single map on the compact cone that kills coboundaries and
induces an isomorphism on degree-three cohomology. Since the compact cohomology of the
cyclotomic line vanishes above degree three, a map to the scalars in degree three is
determined in the derived category by its effect on degree-three cohomology, so any such
trace is a unit multiple of the canonical trace of (5.4.1.3); a unit does not affect the
conclusion.

The conclusion is stated on bounded finite free models, which represent the derived dual
without dualizing infinite cochain modules: the model map is the traced global cup adjoint
pulled back along the given model comparisons. It asserts global duality only; it says
nothing about any Selmer complex with nonzero local conditions.
-/

noncomputable section

set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.SwitchInputs

section Strict

universe u

variable (k : Type u) [CommRing k] (GS : Type u) [Group GS] [TopologicalSpace GS]
  [IsTopologicalGroup GS] {ι : Type u} (Gv : ι → Type u) [∀ v, Group (Gv v)]
  [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  {A B T : Type u}
  [AddCommGroup A] [Module k A] [DistribMulAction GS A] [SMulCommClass GS k A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul k A] [ContinuousSMul GS A]
  [AddCommGroup B] [Module k B] [DistribMulAction GS B] [SMulCommClass GS k B]
  [TopologicalSpace B] [ContinuousAdd B] [ContinuousConstSMul k B] [ContinuousSMul GS B]
  [AddCommGroup T] [Module k T] [DistribMulAction GS T] [SMulCommClass GS k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul GS T]
  (β : A →ₗ[k] B →ₗ[k] T) (hβ : ∀ (g : GS) (a : A) (b : B), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : A × B => β x.1 x.2)

/-- The zero isotropy homotopy of the strict conditions on both factors. -/
def strictTruncIsotropy :
    TruncIsotropyData k GS Gv loc β hβ hβc (strictConditions k GS Gv loc A)
      (strictConditions k GS Gv loc B) where
  h _ _ _ _ _ := 0
  isotropy₂ v i i₁ j j₁ hh hi hj x y := by
    obtain rfl : x = 0 := Subsingleton.elim (α := PUnit.{u + 1}) x 0
    simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero, sub_zero]
    exact Submodule.zero_mem _
  isotropy₃ v i i₁ j j₁ l l₁ hh hi hj hl _ x y := by
    obtain rfl : x = 0 := Subsingleton.elim (α := PUnit.{u + 1}) x 0
    simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero]

/-- The cup-product data of the strict conditions: global continuous cochains, compactly
supported cochains, truncated local target, zero isotropy homotopy. -/
def strictPairData :
    SelPairData (selData k GS Gv loc A (strictConditions k GS Gv loc A))
      (selData k GS Gv loc B (strictConditions k GS Gv loc B)) :=
  (genuinePairDataTrunc k GS Gv loc β hβ hβc (strictConditions k GS Gv loc A)
    (strictConditions k GS Gv loc B) (strictTruncIsotropy k GS Gv loc β hβ hβc)).toSelPairData

end Strict

/-- A relation-indexed complex is a bounded complex of finite free modules. -/
def IsBoundedFiniteFree {R : Type} [CommRing R] (P : GCx R) : Prop :=
  (∃ a b : ℤ, ∀ n, n < a ∨ b < n → Subsingleton (P.X n)) ∧
    ∀ n, Module.Free R (P.X n) ∧ Module.Finite R (P.X n)

/-- **Nekovář 5.4.3(ii) over the two-adic integers, global form** (printed p. 127, with
5.1 p. 113, 5.4.1–5.4.2 pp. 125–127, 2.4.4–2.7 pp. 54–55).

For a number field without real places, a finite set of finite places containing those above
two, finite free two-adic coefficient modules with continuous Galois action, and an
equivariant, continuous, perfect pairing into the integral cyclotomic line: for every
degree-three trace on the compact cone that kills coboundaries and induces an isomorphism on
degree-three cohomology, and for all bounded finite free models of the global cochains of the
first module and of the compactly supported cochains of the second, the traced global cup
adjoint pulled back to the models is a quasi-isomorphism. -/
def NekovarIntegralGlobalDuality : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K →
    ∀ (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite →
    (∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    ∀ (M M' : Type)
      [AddCommGroup M] [Module ℤ_[2] M] [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
      [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) ℤ_[2] M]
      [TopologicalSpace M] [IsModuleTopology ℤ_[2] M]
      [ContinuousAdd M] [ContinuousConstSMul ℤ_[2] M] [ContinuousSMul (GKS K S) M]
      [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M'] [Module.Finite ℤ_[2] M']
      [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) ℤ_[2] M']
      [TopologicalSpace M'] [IsModuleTopology ℤ_[2] M']
      [ContinuousAdd M'] [ContinuousConstSMul ℤ_[2] M'] [ContinuousSMul (GKS K S) M']
      (β : M →ₗ[ℤ_[2]] M' →ₗ[ℤ_[2]] IntegralTate1 K S)
      (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)
      (hβc : Continuous fun x : M × M' => β x.1 x.2),
      Function.Bijective β → Function.Bijective β.flip →
      ∀ (tr : (coneCx (strictPairData ℤ_[2] (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) β hβ hβc).resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
        (htr : ∀ z, tr ((coneCx (strictPairData ℤ_[2] (GKS K S)
          (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ hβc).resE).d 2 3 rfl z)
            = 0),
        InducesIsoH3 tr →
      ∀ (P P' : GCx ℤ_[2]), IsBoundedFiniteFree P → IsBoundedFiniteFree P' →
      ∀ (c : GHom P (selData ℤ_[2] (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) M
          (strictConditions ℤ_[2] (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) M)).G)
        (c' : GHom P' (compactCx (selData ℤ_[2] (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) M'
          (strictConditions ℤ_[2] (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) M')))),
        QuasiIso (GHom.toCC c) → QuasiIso (GHom.toCC c') →
        QuasiIso (GHom.toCC (ghomComp (ghomComp c (globalDualityMap
          (strictPairData ℤ_[2] (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) β hβ hβc) tr htr)) (dualHom c' 3)))

end ZInQ.Contrib.RC53Assist.IntegralDuality

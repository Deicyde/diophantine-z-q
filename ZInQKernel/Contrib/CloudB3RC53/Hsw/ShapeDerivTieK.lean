import ZInQKernel.Contrib.CloudB3RC53.Hsw.ShapeDerivTie
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenericCoords

/-!
# RC53 `hsw` shape: `hcoord` from the field-generic switch coordinates

The hypothesis `hcoord` of `derivSwitch_switchCoordinates_of_two_ne_zero` and
`derivSwitch_switchCoordinates_char2` holds for the field-generic coordinates
`eR = eRAtK (Frobenius φ, tame generator σ)` (`SwitchInputs/GenericCoords.lean`) of a family
switched at `q`. It needs the tame coordinates `TameCoordinatesTrivialK` at `q` and that inertia
contains `ker(urRes)`. This is the port of `hcoord_of_tame` from `𝔽₂` to an arbitrary
coefficient field.

* `hrelq_of_relAtK`: the relaxed condition at `q` contains every local cocycle.
* `htriv_of_tameK`: the action at `q` is trivial.
* `hcoord_of_tameK`: the hypothesis `hcoord`.
* `derivSwitch_switchCoordinates_tameK`: `SwitchCoordinates` for the switch of a family switched at
  `q` with the coordinates `eRAtK`. Nondegeneracy of the residue form is the only remaining
  input.

## Scope

`TameCoordinatesTrivialK k M I φ σ` asks that the decomposition group, in particular `φ` and `σ`,
act trivially on `M`. With the tame relation `φ σ φ⁻¹ = σ^q` it then forces `(q : k) = 1` for
`M ≠ 0` (`not_tameCoordinatesTrivialK_of_tame`). Likewise, with unramified coordinates, the
`2 + 2` shape of `H¹(W_rel)` holds iff `(q : k) = 1` (`two_plus_two_iff_q_eq_one`). So these
results apply in two cases:
* the residual case;
* inner-limit objects, where `qᵢ → 1`.

They do not apply at a single characteristic-zero fibre. In addition,
`derivSwitch_switchCoordinates_tameK` assumes a finite target module `T`, for the vanishing of
`H²(Gal(K_q^ur/K_q), T)`. Over a field of characteristic zero a finite module is zero, so there
the hypotheses force `T = 0`.

All results are `PROVED`. No new axioms.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Hsw

open CategoryTheory NumberField IsDedekindDomain ZInQ.Manuscript.RC.Uniform
  ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.RankCounts ZInQ.Contrib.CloudB3RC53.GenuineInst

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [Field k] {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M] [DecidableEq (Places K S)]
  (F : DerivFamily (galLv (k := k) K S M)) {q : Places K S}
  (hR : RelAtK (k := k) (Gv := fun v : Places K S => Gloc K v.1)
    (Mv := fun v : Places K S => ResMod (locMap K S v.1) M) F.str F.rel q)

omit [DecidableEq (Places K S)] in
include hR in
/-- For a family switched at `q`, the relaxed condition at `q` contains every local cocycle. -/
theorem hrelq_of_relAtK (z : (galLv (k := k) K S M q).X 1)
    (hz : (galLv (k := k) K S M q).d 1 2 rfl z = 0) : z ∈ (F.rel q).S 1 :=
  (hR.rel1 z).2 hz

omit [DecidableEq (Places K S)] in
/-- The tame coordinates make the action at `q` trivial. -/
theorem htriv_of_tameK {φ σ : Gloc K q.1} {I : Subgroup (Gloc K q.1)}
    (T : TameCoordinatesTrivialK k (ResMod (locMap K S q.1) M) I φ σ) (g : Gloc K q.1) (m : M) :
    locMap K S q.1 g • m = m :=
  T.htriv g m

/-- **`hcoord` from the field-generic switch coordinates** (`PROVED`). With the coordinates
`eR = eRAtK` of the switch of a family switched at `q`, and inertia containing `ker(urRes)`, every
finite-plane vector is the class of a local cocycle at `q` that vanishes on `ker(urRes)`. -/
theorem hcoord_of_tameK (φ σ : Gloc K q.1)
    (eM : ResMod (locMap K S q.1) M ≃ₗ[k] (Fin 2 → k)) {I : Subgroup (Gloc K q.1)}
    (T : TameCoordinatesTrivialK k (ResMod (locMap K S q.1) M) I φ σ)
    (hIur : ∀ g, urRes K q.1 g = 1 → g ∈ I) :
    ∀ a, a ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      ∃ (z : (galLv (k := k) K S M q).X 1)
        (hz : (galLv (k := k) K S M q).d 1 2 rfl z = 0),
        (∀ g, urRes K q.1 g = 1 → cFun z (fun _ => g) = 0) ∧
          gClass (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM T)).toQuasi
            (relSingle F q (hrelq_of_relAtK F hR) z hz)
            (relSingle_d F q (hrelq_of_relAtK F hR) z hz) = a := by
  intro a ha
  obtain ⟨u, hu⟩ := (coordEquivK T eM).surjective a
  obtain ⟨zz, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  have hcz : coordAtK (Gv := fun v : Places K S => Gloc K v.1)
      (Mv := fun v : Places K S => ResMod (locMap K S v.1) M) q φ σ eM
      (zz : (contCochains k (Gloc K q.1) (ResMod (locMap K S q.1) M)).X 1) = a :=
    (coordAt_mkK (Gv := fun v : Places K S => Gloc K v.1)
      (Mv := fun v : Places K S => ResMod (locMap K S v.1) M) (q := q) φ σ eM T zz).trans hu
  have hBF := (finite_side_iffK (Gv := fun v : Places K S => Gloc K v.1)
      (Mv := fun v : Places K S => ResMod (locMap K S v.1) M) (q := q) φ σ eM T zz).2
    (hcz.symm ▸ ha)
  rw [mem_sideOfSetK_BF] at hBF
  refine ⟨zz.1, zz.2, fun g hg => hBF g (hIur g hg), ?_⟩
  change coordCK (derivHsrK F) hR φ σ eM (T.htriv φ) (T.htriv σ)
    (phiAtK (derivHsrK F) hR (Submodule.Quotient.mk zz)) = a
  rw [coordC_phiAtK (Gv := fun v : Places K S => Gloc K v.1)
    (Mv := fun v : Places K S => ResMod (locMap K S v.1) M)]
  exact hcz

variable {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) k T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T] [Finite T]

/-- **`SwitchCoordinates` for the switch of a family switched at `q`, with the field-generic
coordinates** (`PROVED` from the inputs; a coefficient field with `2 ≠ 0`, a finite target `T`,
and the tame coordinates with trivial action, so `(q : k) = 1`: the residual case and
inner-limit objects, not a single characteristic-zero fibre). Inputs:
* the coordinates `eRAtK` from the tame coordinates at `q`;
* a `c`-symmetric equivariant self-pairing with `c² = 1`;
* isotropy data and strict complexes vanishing in degree two;
* trivial action of `G_{K_q}` on `T`;
* inertia containing `ker(urRes)`.

Nondegeneracy of the residue form (local duality at the coefficients) is the only remaining
input. -/
theorem derivSwitch_switchCoordinates_tameK (h2 : (2 : k) ≠ 0) (φ σ : Gloc K q.1)
    (eM : ResMod (locMap K S q.1) M ≃ₗ[k] (Fin 2 → k)) {I : Subgroup (Gloc K q.1)}
    (Tc : TameCoordinatesTrivialK k (ResMod (locMap K S q.1) M) I φ σ)
    (hIur : ∀ g, urRes K q.1 g = 1 → g ∈ I)
    (β : M →ₗ[k] M →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
    (c : k) (hc : ∀ x y, β x y = c • β y x) (hc2 : c * c = 1)
    (Iso : GaloisIsotropyData K S k β hβ (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc)).ΔR)
    (tr : (coneCx (galoisPairData K S k β hβ
      (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc)).ΔR Iso).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (galoisPairData K S k β hβ
      (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc)).ΔR Iso).resE).d 2 3 rfl z) = 0)
    (hUS2 : ∀ v (x : (F.str v).cx.X 2), x = 0) {ε : k} (hε : ε ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1)
    (htrivT : ∀ (g : Gloc K q.1) (m : T), locMap K S q.1 g • m = m)
    (hnd : ∀ t
      (ht : (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc)).toQuasi.D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc)).toQuasi.D.U.d 1 2 rfl u = 0),
        resForm (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc)).toQuasi
          (piCx (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc)).US)
          (piMap (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc)).φ)
          (galoisPairData K S k β hβ (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc)).ΔS
            (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc)).ΔR Iso) tr t u = 0) →
        gClass (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc)).toQuasi t ht = 0) :
    ∃ Φ : ((Fin 2 → k) × (Fin 2 → k)) ≃ₗ[k] ((Fin 2 → k) × (Fin 2 → k)),
      (finPlane k (Fin 2 → k) (Fin 2 → k)).map Φ.toLinearMap =
        finPlane k (Fin 2 → k) (Fin 2 → k) ∧
      ({ derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc) with
          eR := (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc)).eR.trans Φ } :
        GenuineSwitch K S k M).SwitchCoordinates
        (galoisPairData K S k β hβ (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc)).ΔS
          (derivSwitch F (eRAtK (derivHsrK F) hR φ σ eM Tc)).ΔR Iso) tr ε (-c) J :=
  derivSwitch_switchCoordinates_of_two_ne_zero F q (hrelq_of_relAtK F hR) h2
    (eRAtK (derivHsrK F) hR φ σ eM Tc) β hβ c hc hc2 Iso tr htr hUS2 hε hJ2
    (htriv_of_tameK Tc) htrivT (hcoord_of_tameK F hR φ σ eM Tc hIur) hnd

end ZInQ.Contrib.CloudB3RC53.Hsw

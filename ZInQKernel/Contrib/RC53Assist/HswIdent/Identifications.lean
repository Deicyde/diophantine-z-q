import ZInQKernel.Contrib.RC53Assist.HswResidual.Residual
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Weil
import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.CoefResidualCounts

/-!
# The coefficient and trace identifications of the residual switch, for the genuine objects

The residual bridge `derivSwitch_switchCoordinates_tame_of_Milne` takes six identifications at the
switch place `q`: coordinates `eT : T_q ≃ F_2`, a second coordinate system `eM₂` of `M_q`, the
transported Weil formula `hWeil`, an identification `eμ : T_q ≃ μ_2` over `K_q` with its
equivariance `heμ`, and the matching `hmatch` of the restricted cone trace with the local Brauer
invariant. This file supplies them for the genuine residual objects:

* the coefficient module is `E(K_S)[2]` (`ETwo K S W`), the `2`-torsion of the points of the
  curve with coordinates in `K_S`, with `G_{K,S}` acting on coordinates, as a discrete
  `F_2[G_{K,S}]`-module; the same is done for the actual residual module
  `F_2 ⊗_{A_{j+1}} M_{j+1}` (`ResidualM`), identified with `E(K_S)[2]` by `residualEquiv`;
* the target is `μ_2 = F_2(1)` over `G_{K,S}` (`MuTwo K S`): `μ_2 = {±1} ⊂ K`, so the action is
  trivial; this is `F_2` with the trivial action (`isCyclotomicTwist_muTwo`), identified
  equivariantly with the square roots of unity of `K_S` (`muTwoRoots`, `muTwoRoots_smul`,
  `muTwoRoots_one`);
* the pairing is the Weil pairing `e_2` (`weilTwo K S W`): the pairing of Silverman III.8.1
  (vendored Tau Ceti construction) on `E(K_S)[2]`, read in `F_2` (`weilS`), as in the
  manuscript's Lemma `ex:arith-conjugate-duality` (tex 2798: "The Weil pairing gives the
  following perfect pairing").

## Coefficients: `eT`, `eM₂`, `hWeil`

* `alternating_eq_weil`, `alternating_eq_weil_of_nondegenerate`: over `F_2`, a nonzero
  alternating pairing of a two-dimensional space into a line is the determinant form `weil` in
  every coordinate system.
* `weilTwo_self`, `weilTwo_nondegenerate` (under the existing hypothesis `FullTorsion K S W 2`,
  i.e. `|E(K_S)[2]| = 4`), `weilTwo_smul` (equivariance: `e_2` transforms by the cyclotomic
  character, trivial modulo `2`).
* `eTq`; `weilTwo_hWeil`: `hWeil` holds for every coordinate system `eM` at `q`, in particular
  the tame coordinates of the switch, with `eM₂ = eM`. For the conjugate pairing
  `(x, y) ↦ e_2(x, J y)` (tex 2818, 4889–4890, 5035–5036) the second coordinates are `J ≫ eM`
  (`weilTwo_hWeil_conj`); the tame consumer needs a polarized, hence alternating, pairing, which
  over `F_2` is `e_2` itself.
* `weilTwo_polarization`: when `G_{K,S}` fixes `E(K_S)[2]` (tex 4479–4480), the polarization
  `γ` of `e_2` required by the consumer.

## `μ_2` over `K_q`: `eμ`, `heμ`

* `eMuq`, `eMuq_one`, `heMuq`: the identification of `μ_2` with `μ_2(K_q^sep)`, sending `1` to
  `-1`, equivariant since both actions are trivial (`-1 ∈ K_q`).

## The trace matching: `hmatch`

The cone trace `tr` is an input of the consumer. With the project's convention for the genuine
trace (`InducesIsoH3 tr`, as in `NekovarProp543`):

* `localTraceMatchesInvariant_of_inducesIsoH2`: given the A23 comparison `hKB`, a local trace
  matches the Brauer invariant as soon as it induces `H^2(K_q, T) ≅ F_2`. Over `F_2` the
  normalization `1 ↦ 1/2` is automatic: both sides vanish exactly on coboundaries and take the
  unique nonzero two-torsion value `1/2` otherwise.
* `inducesIsoH2_residualTraceAt`: the restriction of the cone trace to the `q`-summand induces
  `H^2(K_q, T) ≅ F_2`, from `InducesIsoH3 tr`, from the reciprocity statement `ReciprocityAt`
  (a global two-cocycle that is locally a coboundary at every place of `S` other than `q` is
  locally a coboundary at `q`), and from `H^2(K_q, T) ≠ 0`.
* `hmatch_of_reciprocity`, `hmatch_genuine`: the resulting `hmatch`.
* `reciprocityAt_of_inducesIsoH2`, `hmatch_iff_reciprocityAt`, `hmatch_genuine_iff`: conversely
  `hmatch` implies `ReciprocityAt`; so, for a trace inducing `H^3_c ≅ F_2`, `hmatch` is
  equivalent to `ReciprocityAt` and nothing weaker can replace it.

`ReciprocityAt` is an explicit input, not proved here. It is the reciprocity law for
`H^2(G_{K,S}, μ_2)`: by the Hasse sum formula (proved in the vendored Tau Ceti library as
`TauCeti.ClassFieldTheory.sumLocalInv_brLocalization_eq_zero`), the local invariants of a global
Brauer class sum to zero; a class inflated from `G_{K,S}` has no invariant at a finite place
outside `S`, and none at a complex place. It holds for `K` totally complex, as in the manuscript
(tex 2839: `K` imaginary quadratic; tex 4584: no real places). It fails when `K` has a real
place: over `Q` with `S = {2}`, the class of the quaternion algebra `(-1, -1)` lies in
`H^2(G_{Q,S}, μ_2)` and is nonzero at `2`. Its derivation from the sum formula needs comparisons
that are not in the library: inflation from `G_{K,S}` to the absolute Galois group and from `μ_2`
to the units; the identification of `locMap` with the localizations of `brLocalization` (Tau Ceti
proves that base change does not depend on the embedding of separable closures,
`TauCeti.ClassFieldTheory.brBaseChange_apply`, so an embedding compatible with `locMap` must be
produced); the vanishing at the finite places outside `S` (through the factorization
`UnramifiedAtFactorization`, stated but not proved in the tree, or through Tau Ceti's vanishing
of unramified inflated classes together with a comparison of `IsUnramifiedOutside` with
`Algebra.IsUnramifiedAt`); and the vanishing at the complex places.

## The assembled consumer

* `derivSwitch_switchCoordinates_tame_genuine`: the consumer `derivSwitch_switchCoordinates_tame`
  for `M = E(K_S)[2]`, `T = μ_2`, `β = e_2`, with all six identifications supplied.
* `derivSwitch_switchCoordinates_tame_genuine_rational`: the same when `G_{K,S}` fixes
  `E(K_S)[2]`, with the polarization and the local triviality derived.
* `derivSwitch_switchCoordinates_tame_curveEll`: the same for the manuscript's curve
  `E_ℓ : y^2 = x (x - ℓ) (x + 3 ℓ)` (tex 1763–1766, full rational two-torsion), where
  `FullTorsion` and the trivial action are proved.
* `derivSwitch_switchCoordinates_tame_residualM`: the same for the actual residual module
  `F_2 ⊗_{A_{j+1}} M_{j+1}`.

The remaining inputs are the printed `MilneCor23Residual`, the A23 comparison
`KummerBrauerComparisonF2 K_q`, `InducesIsoH3 tr`, `ReciprocityAt`, `FullTorsion` (proved for
`E_ℓ`), and the switch inputs of the consumer. No new printed statement is introduced.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HswIdent

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.GenuineInst ZInQ.Contrib.CloudB3RC53.Hsw
open ZInQ.Contrib.RC53Assist.HswResidual

/-! ### Alternating pairings on a two-dimensional `F_2`-space -/

section Linear

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

/-- Every element of `ZMod 2` other than `0` is `1`. -/
theorem zmod2_eq_one_of_ne_zero {c : ZMod 2} (hc : c ≠ 0) : c = 1 := by
  fin_cases c
  · exact absurd rfl hc
  · rfl

/-- A vector is the combination of the two basis vectors of a coordinate system. -/
theorem eq_coord_combination (e : V ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)) (x : V) :
    x = e x 0 • e.symm (Pi.single 0 1) + e x 1 • e.symm (Pi.single 1 1) := by
  apply e.injective
  rw [map_add, map_smul, map_smul, e.apply_symm_apply, e.apply_symm_apply]
  funext i
  fin_cases i <;> simp

/-- **An alternating `F_2`-valued form is a multiple of the Weil form** in any coordinates:
`B x y = weil (e x) (e y) · B (u, w)` for the basis `u, w` of the coordinates `e`. -/
theorem alternating_eq_weil_mul (e : V ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (halt : ∀ x, B x x = 0) (x y : V) :
    B x y = weil (e x) (e y) * B (e.symm (Pi.single 0 1)) (e.symm (Pi.single 1 1)) := by
  have hwu : B (e.symm (Pi.single 1 1)) (e.symm (Pi.single 0 1)) =
      -B (e.symm (Pi.single 0 1)) (e.symm (Pi.single 1 1)) := by
    have h := halt (e.symm (Pi.single 0 1) + e.symm (Pi.single 1 1))
    simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
    linear_combination h
  have hx := eq_coord_combination e x
  have hy := eq_coord_combination e y
  rw [weil_apply]
  calc B x y = B (e x 0 • e.symm (Pi.single 0 1) + e x 1 • e.symm (Pi.single 1 1))
        (e y 0 • e.symm (Pi.single 0 1) + e y 1 • e.symm (Pi.single 1 1)) := by
          rw [← hx, ← hy]
    _ = _ := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, halt,
        smul_eq_mul, hwu]
      ring

variable {T : Type} [AddCommGroup T] [Module (ZMod 2) T]

/-- **A nonzero alternating pairing into a line over `F_2` is the Weil form in every
coordinates**: `eT (B x y) = weil (e x) (e y)` for all coordinates `e : V ≃ F_2^2` and
`eT : T ≃ F_2`. -/
theorem alternating_eq_weil (e : V ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)) (eT : T ≃ₗ[ZMod 2] ZMod 2)
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] T) (halt : ∀ x, B x x = 0) (hne : ∃ x y, B x y ≠ 0)
    (x y : V) : eT (B x y) = weil (e x) (e y) := by
  let P : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2 := B.compr₂ eT.toLinearMap
  have hP : ∀ a b, P a b = eT (B a b) := fun _ _ => rfl
  have hPalt : ∀ a, P a a = 0 := fun a => by rw [hP, halt, map_zero]
  have hc : P (e.symm (Pi.single 0 1)) (e.symm (Pi.single 1 1)) = 1 := by
    apply zmod2_eq_one_of_ne_zero
    intro h0
    obtain ⟨a, b, hab⟩ := hne
    apply hab
    apply eT.injective
    rw [map_zero, ← hP, alternating_eq_weil_mul e P hPalt a b, h0, mul_zero]
  rw [← hP, alternating_eq_weil_mul e P hPalt x y, hc, mul_one]

/-- A left-nondegenerate pairing on a nonzero space takes a nonzero value. -/
theorem exists_ne_zero_of_nondegenerate [Nontrivial V] (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] T)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) : ∃ x y, B x y ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  by_contra h
  apply hx
  apply hnd x
  intro y
  by_contra hy
  exact h ⟨x, y, hy⟩

/-- **A nondegenerate alternating pairing on a two-dimensional space is the Weil form in every
coordinates.** -/
theorem alternating_eq_weil_of_nondegenerate (e : V ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (eT : T ≃ₗ[ZMod 2] ZMod 2) (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] T) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (x y : V) : eT (B x y) = weil (e x) (e y) := by
  have : Nontrivial V := e.toEquiv.nontrivial
  exact alternating_eq_weil e eT B halt (exists_ne_zero_of_nondegenerate B hnd) x y

/-- **The conjugate pairing** `(x, y) ↦ A (x, J y)`, for `A` nonzero alternating and an
automorphism `J`, is the Weil form in the coordinates `e` and `J ≫ e`. -/
theorem conjugate_eq_weil (e : V ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)) (eT : T ≃ₗ[ZMod 2] ZMod 2)
    (A : V →ₗ[ZMod 2] V →ₗ[ZMod 2] T) (halt : ∀ x, A x x = 0) (hne : ∃ x y, A x y ≠ 0)
    (J : V ≃ₗ[ZMod 2] V) (x y : V) :
    eT (A x (J y)) = weil (e x) ((J.trans e) y) :=
  alternating_eq_weil e eT A halt hne x (J y)

/-- An additive pairing of `F_2`-modules is `F_2`-bilinear. -/
def toZModBilin {V' T' : Type} [AddCommGroup V'] [Module (ZMod 2) V'] [AddCommGroup T']
    [Module (ZMod 2) T'] (f : V →+ V' →+ T') : V →ₗ[ZMod 2] V' →ₗ[ZMod 2] T' :=
  LinearMap.mk₂ (ZMod 2) (fun x y => f x y)
    (fun x x' y => by rw [map_add, AddMonoidHom.add_apply])
    (fun c x y => ZMod.map_smul (f.flip y) c x)
    (fun x y y' => map_add (f x) y y')
    (fun c x y => ZMod.map_smul (f x) c y)

theorem toZModBilin_apply {V' T' : Type} [AddCommGroup V'] [Module (ZMod 2) V'] [AddCommGroup T']
    [Module (ZMod 2) T'] (f : V →+ V' →+ T') (x : V) (y : V') : toZModBilin f x y = f x y :=
  rfl

end Linear

/-! ### The genuine residual coefficient module `E(K_S)[2]` and `μ_2` -/

section Genuine

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (W : WeierstrassCurve K)

/-- **`E(K_S)[2]`**: the `2`-torsion of the points of `W` with coordinates in `K_S`, with
`G_{K,S}` acting on coordinates, as a discrete `F_2[G_{K,S}]`-module (a type synonym of
`TorsS K S W 2` carrying the module instances). -/
def ETwo : Type := TorsS K S W ((2 : ℕ) : ℤ)

instance : AddCommGroup (ETwo K S W) :=
  inferInstanceAs (AddCommGroup (TorsS K S W ((2 : ℕ) : ℤ)))

instance : Module (ZMod 2) (ETwo K S W) :=
  show Module (ZMod 2) (TorsS K S W ((2 : ℕ) : ℤ)) from AddSubgroup.torsionBy.zmodModule

instance : DistribMulAction (GKS K S) (ETwo K S W) :=
  inferInstanceAs (DistribMulAction (GKS K S) (TorsS K S W ((2 : ℕ) : ℤ)))

instance : SMulCommClass (GKS K S) (ZMod 2) (ETwo K S W) where
  smul_comm σ c P := ZMod.map_smul (DistribSMul.toAddMonoidHom (ETwo K S W) σ) c P

instance : TopologicalSpace (ETwo K S W) := ⊥

instance : DiscreteTopology (ETwo K S W) := ⟨rfl⟩

/-- `E(K_S)[2]` is a discrete `G_{K,S}`-module: stabilizers are open. -/
instance : ContinuousSMul (GKS K S) (ETwo K S W) :=
  continuousSMul_iff_stabilizer_isOpen.2 fun P =>
    isOpen_stabilizer_torsS (K := K) (S := S) (W := W) (N := ((2 : ℕ) : ℤ)) P

/-- **`μ_2 = F_2(1)` over `G_{K,S}`**: the cyclotomic character modulo `2` is trivial, so this is
`F_2` with the trivial action (`isCyclotomicTwist_muTwo`). -/
abbrev MuTwo : Type := TrivMod (GKS K S) (ZMod 2)

/-- `MuTwo K S` is the cyclotomic twist `F_2(1)` in the sense of the Selmer-duality statements
(`IsCyclotomicTwist`: `μ_2 = {±1} ⊂ K_S` has two elements and `G_{K,S}` fixes it). -/
theorem isCyclotomicTwist_muTwo : IsCyclotomicTwist K S (ZMod 2) (MuTwo K S) :=
  isCyclotomicTwist_example K S

/-- `μ_2(K_S)` has two elements. -/
theorem natCard_rootsOfUnity_two_KS : Nat.card (rootsOfUnity 2 (KS K S)) = 2 :=
  card_rootsOfUnity_KS (hasRootsOfUnity_two (K := K) S)

/-- **`MuTwo K S` is the group `μ_2(K_S)` of square roots of unity of `K_S`**: the unique
isomorphism `F_2 ≅ μ_2(K_S)`; it sends `1` to `-1` (`muTwoRoots_one`) and is equivariant for the
Galois action on roots of unity (`muTwoRoots_smul`). -/
def muTwoRoots : MuTwo K S ≃+ Additive (rootsOfUnity 2 (KS K S)) :=
  (addEquivOfAddCyclicCardEq (G := ZMod 2) (G' := Additive (rootsOfUnity 2 (KS K S)))
    (by rw [Nat.card_zmod, Nat.card_congr Additive.toMul, natCard_rootsOfUnity_two_KS]) :
    ZMod 2 ≃+ Additive (rootsOfUnity 2 (KS K S)))

omit [NumberField K] in
/-- `G_{K,S}` fixes the square roots of unity of `K_S` (they are `±1`). -/
theorem galS_rootsOfUnity_two (σ : GKS K S) (ζ : rootsOfUnity 2 (KS K S)) :
    restrictRootsOfUnity (galS K S σ) 2 ζ = ζ := by
  have hsq : ((ζ : (KS K S)ˣ) : KS K S) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp ζ.2, Units.val_one]
  apply Subtype.ext
  apply Units.ext
  change galS K S σ ((ζ : (KS K S)ˣ) : KS K S) = ((ζ : (KS K S)ˣ) : KS K S)
  rcases sq_eq_one_iff.mp hsq with h | h <;> rw [h]
  · exact map_one _
  · rw [map_neg, map_one]

/-- **`muTwoRoots` is `G_{K,S}`-equivariant** for the Galois action on `μ_2(K_S)`. -/
theorem muTwoRoots_smul (σ : GKS K S) (t : MuTwo K S) :
    muTwoRoots K S (σ • t) =
      Additive.ofMul (restrictRootsOfUnity (galS K S σ) 2 (Additive.toMul (muTwoRoots K S t))) := by
  rw [galS_rootsOfUnity_two]
  rfl

/-- **`muTwoRoots` sends `1` to `-1`.** -/
theorem muTwoRoots_one :
    (((muTwoRoots K S (show MuTwo K S from (1 : ZMod 2))).toMul : rootsOfUnity 2 (KS K S)) :
      (KS K S)ˣ) = -1 := by
  set u : rootsOfUnity 2 (KS K S) :=
    (muTwoRoots K S (show MuTwo K S from (1 : ZMod 2))).toMul with hu
  have hne : u ≠ 1 := by
    intro h1
    have h0 : muTwoRoots K S (show MuTwo K S from (1 : ZMod 2)) = 0 := by
      apply Additive.toMul.injective
      rw [← hu, h1]
      rfl
    have := (muTwoRoots K S).injective (h0.trans (map_zero (muTwoRoots K S)).symm)
    exact one_ne_zero (α := ZMod 2) this
  have hsq : ((u : (KS K S)ˣ) : KS K S) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp u.2, Units.val_one]
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact absurd (Subtype.ext (Units.ext h)) hne
  · exact Units.ext h

variable [W.IsElliptic]

/-- **The Weil pairing** `e_2 : E(K_S)[2] × E(K_S)[2] → μ_2`, as an additive pairing: Tau Ceti's
`e_2` over `K̄` (Silverman III.8.1) on the images of the points, read in `F_2` (`weilS`). -/
def weilTwoAdd : ETwo K S W →+ ETwo K S W →+ MuTwo K S :=
  weilS W (hasRootsOfUnity_two (K := K) S)

/-- **The Weil pairing `e_2` on `E(K_S)[2]` with values in `μ_2`**, `F_2`-bilinear. -/
def weilTwo : ETwo K S W →ₗ[ZMod 2] ETwo K S W →ₗ[ZMod 2] MuTwo K S :=
  toZModBilin (weilTwoAdd K S W)

theorem weilTwo_apply (P Q : ETwo K S W) :
    weilTwo K S W P Q = weilS W (hasRootsOfUnity_two (K := K) S) P Q :=
  rfl

/-- Every unit of `ZMod 2` is `1`. -/
theorem zmod2_units_val (u : (ZMod 2)ˣ) : (u : ZMod 2) = 1 :=
  zmod2_eq_one_of_ne_zero u.ne_zero

/-- **The Weil pairing is equivariant** for `G_{K,S}` with values in `μ_2`: `e_2` transforms by
the cyclotomic character, which is trivial modulo `2`. -/
theorem weilTwo_smul (g : GKS K S) (P Q : ETwo K S W) :
    weilTwo K S W (g • P) (g • Q) = g • weilTwo K S W P Q := by
  have h := weilS_smul W (hasRootsOfUnity_two (K := K) S) g P Q
  rw [zmod2_units_val, one_mul] at h
  exact h

/-- The Weil pairing `weilS` on `E(K_S)[2]` is alternating. -/
theorem weilS_two_self (P : TorsS K S W ((2 : ℕ) : ℤ)) :
    weilS W (hasRootsOfUnity_two (K := K) S) P P = 0 := by
  rw [weilS_apply]
  have h := TauCeti.Isogeny.weilPairing_self (W.baseChange (AlgebraicClosure K)) 2
    (natCast_ne_zero_bar (K := K) 2) (inclTors W 2 P)
  change weilBar W 2 (inclTors W 2 P) (inclTors W 2 P) = 0 at h
  rw [h, map_zero]

/-- **The Weil pairing is alternating**: `e_2(P, P) = 1` multiplicatively (Silverman
III.8.1(b)). -/
theorem weilTwo_self (P : ETwo K S W) : weilTwo K S W P P = 0 :=
  weilS_two_self K S W P

variable {K S W}

/-- **The Weil pairing is nondegenerate** on `E(K_S)[2]` when `E[2]` is defined over `K_S`
(`FullTorsion`, the existing Néron–Ogg–Shafarevich hypothesis). -/
theorem weilTwo_nondegenerate (hW : FullTorsion K S W 2) (P : ETwo K S W)
    (hP : ∀ Q, weilTwo K S W P Q = 0) : P = 0 := by
  have hinj := weilS_injective W (hasRootsOfUnity_two (K := K) S) hW
  have h0 : weilS W (hasRootsOfUnity_two (K := K) S) (P : TorsS K S W ((2 : ℕ) : ℤ)) = 0 :=
    AddMonoidHom.ext fun Q => hP Q
  exact hinj (h0.trans (map_zero _).symm)

variable (K S)

/-- **The coordinate of `μ_2` at `q`**: `μ_2 ≃ F_2` (the restricted module is `F_2` itself). -/
def eTq (q : Places K S) : ResMod (locMap K S q.1) (MuTwo K S) ≃ₗ[ZMod 2] ZMod 2 :=
  LinearEquiv.refl (ZMod 2) (ZMod 2)

variable {K S}

/-- **The transported Weil formula `hWeil` for the genuine objects**, with `eM₂ = eM`: for the
genuine Weil pairing on `E(K_S)[2]` and ANY coordinates `eM` of the restricted module at `q`
(in particular the tame coordinates of the switch),
`eT (e_2(x, y)) = weil (eM x) (eM y)`. -/
theorem weilTwo_hWeil (hW : FullTorsion K S W 2) (q : Places K S)
    (eM : ResMod (locMap K S q.1) (ETwo K S W) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (x y : ResMod (locMap K S q.1) (ETwo K S W)) :
    eTq K S q (resPairing (ZMod 2) (GKS K S) (weilTwo K S W) (locMap K S q.1) x y) =
      weil (eM x) (eM y) :=
  alternating_eq_weil_of_nondegenerate eM (eTq K S q)
    (resPairing (ZMod 2) (GKS K S) (weilTwo K S W) (locMap K S q.1))
    (fun x => weilTwo_self K S W x) (fun x hx => weilTwo_nondegenerate hW x hx) x y

/-- **The transported Weil formula for the conjugate pairing** `(x, y) ↦ e_2(x, J y)` of the
switch (`β(x, y) = ε e_2(x, J y)`, tex 2818, 4889–4890 and 5035–5036, with `ε = 1` over `F_2`):
the second coordinates are `J ≫ eM`. -/
theorem weilTwo_hWeil_conj (hW : FullTorsion K S W 2) (q : Places K S)
    (eM : ResMod (locMap K S q.1) (ETwo K S W) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (J : ResMod (locMap K S q.1) (ETwo K S W) ≃ₗ[ZMod 2] ResMod (locMap K S q.1) (ETwo K S W))
    (x y : ResMod (locMap K S q.1) (ETwo K S W)) :
    eTq K S q (resPairing (ZMod 2) (GKS K S) (weilTwo K S W) (locMap K S q.1) x (J y)) =
      weil (eM x) ((J.trans eM) y) := by
  have : Nontrivial (ResMod (locMap K S q.1) (ETwo K S W)) := eM.toEquiv.nontrivial
  exact conjugate_eq_weil eM (eTq K S q)
    (resPairing (ZMod 2) (GKS K S) (weilTwo K S W) (locMap K S q.1))
    (fun x => weilTwo_self K S W x)
    (exists_ne_zero_of_nondegenerate _ fun x hx => weilTwo_nondegenerate hW x hx) J x y

omit [W.IsElliptic] in
/-- **Coordinates on `E(K_S)[2]`** when `|E(K_S)[2]| = 4` (`torsTwoEquiv`). -/
def eTwoCoords (hW : FullTorsion K S W 2) : ETwo K S W ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
  LinearEquiv.ofBijective
    ((torsTwoEquiv K S W hW : ETwo K S W ≃+ (Fin 2 → ZMod 2)).toAddMonoidHom.toZModLinearMap 2)
    (torsTwoEquiv K S W hW).bijective

/-- **The polarization of the Weil pairing when `E[2]` is rational** (tex 4479–4480: the residual
representation is trivial). If `G_{K,S}` fixes `E(K_S)[2]`, then in any coordinates `e` the form
`γ(x, y) = e(x)_0 e(y)_1` is equivariant and `e_2(x, y) = γ(x, y) - γ(y, x)`. -/
theorem weilTwo_polarization (hW : FullTorsion K S W 2)
    (e : ETwo K S W ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (htrivG : ∀ (g : GKS K S) (P : ETwo K S W), g • P = P) :
    ∃ γ : ETwo K S W →ₗ[ZMod 2] ETwo K S W →ₗ[ZMod 2] MuTwo K S,
      (∀ (g : GKS K S) x y, γ (g • x) (g • y) = g • γ x y) ∧
        ∀ x y, weilTwo K S W x y = γ x y - γ y x := by
  let γ0 : ETwo K S W →ₗ[ZMod 2] ETwo K S W →ₗ[ZMod 2] ZMod 2 :=
    LinearMap.mk₂ (ZMod 2) (fun x y => e x 0 * e y 1)
      (fun x x' y => by simp only [map_add, Pi.add_apply]; ring)
      (fun c x y => by simp only [map_smul, Pi.smul_apply, smul_eq_mul]; ring)
      (fun x y y' => by simp only [map_add, Pi.add_apply]; ring)
      (fun c x y => by simp only [map_smul, Pi.smul_apply, smul_eq_mul]; ring)
  let γ : ETwo K S W →ₗ[ZMod 2] ETwo K S W →ₗ[ZMod 2] MuTwo K S := γ0
  refine ⟨γ, fun g x y => by rw [htrivG, htrivG]; rfl, fun x y => ?_⟩
  have h := alternating_eq_weil_of_nondegenerate e (LinearEquiv.refl (ZMod 2) (ZMod 2))
    (weilTwo K S W) (fun x => weilTwo_self K S W x) (fun x hx => weilTwo_nondegenerate hW x hx)
    x y
  rw [weil_apply] at h
  change weilTwo K S W x y = (e x 0 * e y 1 - e y 0 * e x 1 : ZMod 2)
  rw [mul_comm (e y 0) (e x 1)]
  exact h

/-! ### `μ_2` over the local field -/

/-- `2` is a unit of the local field `K_q`. -/
theorem isUnit_two_adicCompletion (q : Places K S) : IsUnit ((2 : ℕ) : q.1.adicCompletion K) :=
  isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by norm_num))

variable (K S) in
/-- **`μ_2 ≅ μ_2(K_q^sep)`**: the identification of the restricted `μ_2` with Tau Ceti's Kummer
coefficient module of `K_q`. Both groups have two elements, so it is the unique isomorphism; it
sends `1` to `-1` (`eMuq_one`). -/
def eMuq (q : Places K S) :
    ResMod (locMap K S q.1) (MuTwo K S) ≃+ TauCeti.KummerCoeff (q.1.adicCompletion K) 2 :=
  ((AddEquiv.refl (ZMod 2) : ResMod (locMap K S q.1) (MuTwo K S) ≃+ ZMod 2)).trans
    (TauCeti.kummerCoeffAddEquivZMod (isUnit_two_adicCompletion q)).symm

/-- **The identification sends `1` to the root of unity `-1`.** -/
theorem eMuq_one (q : Places K S) :
    (((eMuq K S q (show ResMod (locMap K S q.1) (MuTwo K S) from (1 : ZMod 2))).toMul :
      rootsOfUnity 2 (SeparableClosure (q.1.adicCompletion K))) :
        (SeparableClosure (q.1.adicCompletion K))ˣ) = -1 := by
  set u : rootsOfUnity 2 (SeparableClosure (q.1.adicCompletion K)) :=
    (eMuq K S q (show ResMod (locMap K S q.1) (MuTwo K S) from (1 : ZMod 2))).toMul with hu
  have hne : u ≠ 1 := by
    intro h1
    have h0 : eMuq K S q (show ResMod (locMap K S q.1) (MuTwo K S) from (1 : ZMod 2)) = 0 := by
      apply Additive.toMul.injective
      rw [← hu, h1]
      rfl
    have := (eMuq K S q).injective (h0.trans (map_zero (eMuq K S q)).symm)
    exact one_ne_zero (α := ZMod 2) this
  have hsq : ((u : (SeparableClosure (q.1.adicCompletion K))ˣ) :
      SeparableClosure (q.1.adicCompletion K)) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp u.2, Units.val_one]
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact absurd (Subtype.ext (Units.ext h)) hne
  · exact Units.ext h

/-- `-1` is a primitive square root of unity of `K_q`. -/
theorem isPrimitiveRoot_neg_one_adicCompletion (q : Places K S) :
    IsPrimitiveRoot (-1 : q.1.adicCompletion K) 2 :=
  IsPrimitiveRoot.neg_one 0 (by norm_num)

variable (K S) in
/-- **Equivariance of `eMuq`**: `G_{K_q}` acts trivially on both sides. -/
theorem heMuq (q : Places K S) (g : TauCeti.AbsoluteGaloisGroup (q.1.adicCompletion K))
    (t : ResMod (locMap K S q.1) (MuTwo K S)) :
    eMuq K S q ((TauCeti.absoluteGaloisGroupRestrictEquiv (q.1.adicCompletion K)).symm g • t) =
      g • eMuq K S q t :=
  (TauCeti.smul_kummerCoeff_eq_self (isPrimitiveRoot_neg_one_adicCompletion q) g _).symm

/-- The local action on `μ_2` is trivial. -/
theorem locMap_smul_muTwo (q : Places K S) (g : Gloc K q.1) (m : MuTwo K S) :
    locMap K S q.1 g • m = m :=
  rfl

end Genuine

/-! ### The matching of the restricted trace with the Brauer invariant -/

section TwoTorsion

/-- **The two-torsion of `Q/Z`** is `{0, 1/2}`. -/
theorem addCircle_two_torsion (x : AddCircle (1 : ℚ)) (hx : 2 • x = 0) :
    x = 0 ∨ x = ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  induction x using QuotientAddGroup.induction_on with
  | H q =>
  have hq : ((2 • q : ℚ) : AddCircle (1 : ℚ)) = 0 := by rw [AddCircle.coe_nsmul]; exact hx
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℚ)).mp hq
  simp only [zsmul_eq_mul, mul_one, nsmul_eq_mul, Nat.cast_ofNat] at hn
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    apply (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one]
    push_cast at hn
    linarith
  · right
    rw [← sub_eq_zero, ← AddCircle.coe_sub]
    apply (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one]
    push_cast at hn
    linarith

/-- Two nonzero two-torsion elements of `Q/Z` are equal. -/
theorem eq_of_two_torsion {x y : AddCircle (1 : ℚ)} (hx0 : x ≠ 0) (hx : 2 • x = 0)
    (hy0 : y ≠ 0) (hy : 2 • y = 0) : x = y := by
  rcases addCircle_two_torsion x hx with h | h
  · exact absurd h hx0
  rcases addCircle_two_torsion y hy with h' | h'
  · exact absurd h' hy0
  rw [h, h']

end TwoTorsion

section LocalTrace

variable {L : Type} [Field L] [CharZero L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
  {T : Type} [AddCommGroup T] [Module (ZMod 2) T]
  [DistribMulAction (Field.absoluteGaloisGroup L) T]
  [SMulCommClass (Field.absoluteGaloisGroup L) (ZMod 2) T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (Field.absoluteGaloisGroup L) T]
  (eμ : T ≃+ TauCeti.KummerCoeff L 2)
  (heμ : ∀ (g : TauCeti.AbsoluteGaloisGroup L) (t : T),
    eμ ((TauCeti.absoluteGaloisGroupRestrictEquiv L).symm g • t) = g • eμ t)

include eμ heμ in
/-- **`H^2(K, T) ≠ 0`**: some local two-cocycle is not a coboundary (from the surjectivity half
of the A23 comparison and the local invariant `Br L ≅ Q/Z`). -/
theorem exists_kerToH2_ne_zero (hKB : KummerBrauerComparisonF2 L) :
    ∃ c : LinearMap.ker ((contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T).d 2 3).hom,
      kerToH2 c ≠ 0 := by
  let E := kummerH2Transport eμ heμ
  let b := (TauCeti.ClassFieldTheory.invMap L).symm (f2ToQmodZ 1)
  have hb0 : (2 : ℕ) • b = 0 := by
    apply (TauCeti.ClassFieldTheory.invMap L).injective
    change TauCeti.ClassFieldTheory.invMap L ((2 : ℕ) •
      (TauCeti.ClassFieldTheory.invMap L).symm (f2ToQmodZ 1)) =
      TauCeti.ClassFieldTheory.invMap L 0
    rw [map_nsmul, AddEquiv.apply_symm_apply, ← map_nsmul,
      show (2 : ℕ) • (1 : ZMod 2) = 0 from by decide, map_zero, map_zero]
  have hb : b ∈ (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := L) 2).range := by
    rw [hKB.2]
    exact AddSubgroup.torsionBy.nsmul_iff.mpr hb0
  obtain ⟨a, ha⟩ := hb
  obtain ⟨c, hc⟩ := kerToH2_surjective (k := ZMod 2)
    (G := Field.absoluteGaloisGroup L) (M := T) (E.symm a)
  refine ⟨c, fun h0 => ?_⟩
  rw [hc] at h0
  have ha0 : a = 0 := by
    have := congrArg E h0
    rwa [AddEquiv.apply_symm_apply, map_zero] at this
  rw [ha0, map_zero] at ha
  have h1 : f2ToQmodZ 1 = 0 := by
    have := congrArg (TauCeti.ClassFieldTheory.invMap L) ha
    rw [map_zero] at this
    exact (this.trans ((TauCeti.ClassFieldTheory.invMap L).apply_symm_apply (f2ToQmodZ 1))).symm
  exact one_ne_zero (f2ToQmodZ_injective (h1.trans (map_zero f2ToQmodZ).symm))

/-- **The matching with the Brauer invariant from the trace isomorphism.** Over `F_2`, given the
A23 comparison, a local trace killing coboundaries and inducing `H^2(K, T) ≅ F_2` agrees with the
Brauer invariant on every two-cocycle: both vanish exactly on coboundaries, and on the other
cocycles both are the unique nonzero two-torsion value `1/2`. -/
theorem localTraceMatchesInvariant_of_inducesIsoH2 (hKB : KummerBrauerComparisonF2 L)
    (tr2 : (contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T).X 2 →ₗ[ZMod 2] ZMod 2)
    (htr2 : ∀ c, tr2 (((contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T).d 1 2).hom c) = 0)
    (hiso : InducesIsoH2 (C := natCx (contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T))
      tr2) :
    LocalTraceMatchesInvariant eμ heμ tr2 := by
  intro c
  by_cases h0 : kerToH2 c = 0
  · obtain ⟨y, hy⟩ := (kerToH2_eq_zero_iff c).mp h0
    rw [h0, map_zero, map_zero, map_zero, ← hy, htr2, map_zero]
  · have htc : tr2 c.1 = 1 := by
      apply zmod2_eq_one_of_ne_zero
      intro htc
      obtain ⟨y, hy⟩ := hiso.1 c.1 c.2 htc
      exact h0 ((kerToH2_eq_zero_iff c).mpr ⟨y, hy⟩)
    rw [htc]
    have h2c : (2 : ℕ) • c = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2), show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_smul]
    apply eq_of_two_torsion
    · intro h
      exact one_ne_zero (f2ToQmodZ_injective (h.trans (map_zero f2ToQmodZ).symm))
    · rw [← map_nsmul, show (2 : ℕ) • (1 : ZMod 2) = 0 from by decide, map_zero]
    · intro h
      apply h0
      apply (kummerH2Transport eμ heμ).injective
      apply hKB.1
      apply (TauCeti.ClassFieldTheory.invMap L).injective
      rw [map_zero, map_zero, map_zero]
      exact h
    · rw [← map_nsmul, ← map_nsmul, ← map_nsmul, ← map_nsmul, h2c, map_zero, map_zero, map_zero,
        map_zero]

end LocalTrace

section Reciprocity

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M] [DecidableEq (Places K S)]
  {T : Type} [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) (ZMod 2) T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T]

variable (K S T) in
/-- **Reciprocity at `q` in degree two** (an explicit input, not proved here): a continuous
two-cocycle of `G_{K,S}` with values in `T` whose restrictions to all places of `S` other than `q`
are coboundaries has a coboundary restriction at `q`. For `T = μ_2` and `K` totally complex this is
the reciprocity law: the local invariants of a global Brauer class sum to zero (Hasse's sum
formula), and a class from `G_{K,S}` has no invariant outside `S` or at the complex places. For
finite `S` containing the places above `2`, this is the statement that the composite
`H^2(G_{K,S}, μ_2) → ⊕_{v ∈ S} H^2(K_v, μ_2) → Q/Z` (sum of invariants) vanishes, a part of the
Poitou–Tate sequence (Milne, Arithmetic Duality Theorems, I.4.10, cited at tex 4526; locator
not checked against the printed text). -/
def ReciprocityAt (q : Places K S) : Prop :=
  ∀ e : (globalCx (ZMod 2) (GKS K S) T).X 2,
    (globalCx (ZMod 2) (GKS K S) T).d 2 3 rfl e = 0 →
    (∀ v : Places K S, v ≠ q →
      ∃ y : (localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) T v).X 1,
        (localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) T v).d 1 2 rfl y =
          (resS (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) T).f 2 2 rfl e v) →
    ∃ y : (localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) T q).X 1,
      (localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) T q).d 1 2 rfl y =
        (resS (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) T).f 2 2 rfl e q

/-- **The restricted cone trace induces `H^2(K_q, T) ≅ F_2`.** If the cone trace induces
`H^3_c ≅ F_2` (the project's genuine trace hypothesis), reciprocity holds at `q`, and some local
two-cocycle at `q` is not a coboundary, then the restriction of the cone trace to the `q`-summand
kills exactly the coboundaries among the local two-cocycles and takes the value `1`. -/
theorem inducesIsoH2_residualTraceAt (X : GenuineSwitch K S (ZMod 2) M)
    (β : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
    (hβ : ∀ (g : GKS K S) x y, β (g • x) (g • y) = g • β x y)
    (Iso : GaloisIsotropyData K S (ZMod 2) β hβ X.ΔS X.ΔR)
    (tr : (coneCx (galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).X 3 →ₗ[ZMod 2] ZMod 2)
    (htr3 : InducesIsoH3 (C := coneCx (galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE) tr)
    (q : Places K S) (hrec : ReciprocityAt K S T q)
    (hex : ∃ z : (contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) T)).X 2,
      ((contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) T)).d 2 3).hom z = 0 ∧
        ¬ ∃ y, ((contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) T)).d 1 2).hom y =
          z) :
    InducesIsoH2 (C := natCx (contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) T)))
      (residualTraceAt X β hβ Iso tr q) := by
  let Q := galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso
  have key : ∀ z : (contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) T)).X 2,
      ((contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) T)).d 2 3).hom z = 0 →
      residualTraceAt X β hβ Iso tr q z = 0 →
      ∃ y, ((contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) T)).d 1 2).hom y =
        z := by
    intro z hz htz
    let A := localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T
    let z' : (A q).X 2 := z
    have hz' : (A q).d 2 3 rfl z' = 0 := hz
    let w : (coneCx Q.resE).X 3 := locT Q (Pi.single q z')
    have hw : (coneCx Q.resE).d 3 4 rfl w = 0 := by
      refine Prod.ext ?_ ?_
      · exact map_zero (Q.E.d 3 4 rfl)
      · change Q.resE.f 3 (4 - 1) (by omega) 0 - Q.EL.d (3 - 1) (4 - 1) (by omega)
          (Pi.single q z') = 0
        rw [map_zero, zero_sub, neg_eq_zero]
        have hs : Pi.single (M := fun v => (A v).X 3) q ((A q).d 2 3 rfl z') = 0 := by
          rw [hz', Pi.single_zero]
        exact (piCx_d_single A 2 3 rfl q z').trans hs
    obtain ⟨⟨e, zz⟩, hy⟩ := htr3.1 w hw htz
    let R := resS (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T
    let e' : (globalCx (ZMod 2) (GKS K S) T).X 2 := e
    let zz' : ∀ v : Places K S, (A v).X 1 := zz
    have h1 : (globalCx (ZMod 2) (GKS K S) T).d 2 3 rfl e' = 0 := congrArg Prod.fst hy
    have h2 : ∀ v, R.f 2 2 rfl e' v - (A v).d 1 2 rfl (zz' v) =
        (Pi.single q z' : ∀ v : Places K S, (A v).X 2) v :=
      fun v => congrFun (congrArg Prod.snd hy) v
    obtain ⟨y, hy'⟩ := hrec e' h1 fun v hv => ⟨zz' v, by
      have := h2 v
      rw [Pi.single_eq_of_ne hv, sub_eq_zero] at this
      exact this.symm⟩
    refine ⟨y - zz' q, ?_⟩
    have hq := h2 q
    rw [Pi.single_eq_same] at hq
    change (A q).d 1 2 rfl (y - zz' q) = z'
    rw [map_sub, hy']
    exact hq
  refine ⟨fun z hz htz => key z hz htz, ?_⟩
  obtain ⟨z, hz, hnz⟩ := hex
  refine ⟨z, hz, zmod2_eq_one_of_ne_zero fun h => hnz (key z hz h)⟩

/-- **`hmatch` from reciprocity**: under the hypotheses of `inducesIsoH2_residualTraceAt` and the
A23 comparison, the restricted cone trace matches the Brauer invariant of `K_q`, for every
identification `eμ` of `T_q` with `μ_2`. -/
theorem hmatch_of_reciprocity (X : GenuineSwitch K S (ZMod 2) M)
    (β : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
    (hβ : ∀ (g : GKS K S) x y, β (g • x) (g • y) = g • β x y)
    (Iso : GaloisIsotropyData K S (ZMod 2) β hβ X.ΔS X.ΔR)
    (tr : (coneCx (galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).X 3 →ₗ[ZMod 2] ZMod 2)
    (htr : ∀ c, tr ((coneCx (galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).d 2 3 rfl c) = 0)
    (htr3 : InducesIsoH3 (C := coneCx (galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE) tr)
    (q : Places K S) (hrec : ReciprocityAt K S T q)
    (hKB : KummerBrauerComparisonF2 (q.1.adicCompletion K))
    (eμ : ResMod (locMap K S q.1) T ≃+ TauCeti.KummerCoeff (q.1.adicCompletion K) 2)
    (heμ : ∀ (g : TauCeti.AbsoluteGaloisGroup (q.1.adicCompletion K))
      (t : ResMod (locMap K S q.1) T),
      eμ ((TauCeti.absoluteGaloisGroupRestrictEquiv (q.1.adicCompletion K)).symm g • t) =
        g • eμ t) :
    LocalTraceMatchesInvariant eμ heμ (residualTraceAt X β hβ Iso tr q) := by
  have hex : ∃ z : (contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) T)).X 2,
      ((contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) T)).d 2 3).hom z = 0 ∧
        ¬ ∃ y, ((contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) T)).d 1 2).hom y =
          z := by
    obtain ⟨c, hc⟩ := exists_kerToH2_ne_zero eμ heμ hKB
    exact ⟨c.1, c.2, fun hy => hc ((kerToH2_eq_zero_iff c).mpr hy)⟩
  exact localTraceMatchesInvariant_of_inducesIsoH2 eμ heμ hKB _
    (residualTraceAt_d X β hβ Iso tr htr q)
    (inducesIsoH2_residualTraceAt X β hβ Iso tr htr3 q hrec hex)

/-- **Conversely, the trace isomorphism at `q` forces reciprocity at `q`.** If the restricted cone
trace (killing cone coboundaries) induces `H^2(K_q, T) ≅ F_2`, then `ReciprocityAt` holds: for a
global cocycle `e` that is locally a coboundary `d y_v` away from `q`, the cone coboundary of
`(e, (y_v))` is the local class of `e` at `q`, which therefore has trace zero. -/
theorem reciprocityAt_of_inducesIsoH2 (X : GenuineSwitch K S (ZMod 2) M)
    (β : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
    (hβ : ∀ (g : GKS K S) x y, β (g • x) (g • y) = g • β x y)
    (Iso : GaloisIsotropyData K S (ZMod 2) β hβ X.ΔS X.ΔR)
    (tr : (coneCx (galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).X 3 →ₗ[ZMod 2] ZMod 2)
    (htr : ∀ c, tr ((coneCx (galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).d 2 3 rfl c) = 0)
    (q : Places K S)
    (hiso : InducesIsoH2
      (C := natCx (contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) T)))
      (residualTraceAt X β hβ Iso tr q)) :
    ReciprocityAt K S T q := by
  intro e he hloc
  let Q := galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso
  let A := localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) T
  let R := resS (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) T
  choose y hy using hloc
  let z : ∀ v : Places K S, (A v).X 1 := fun v => if h : v = q then 0 else y v h
  let c : (A q).X 2 := R.f 2 2 rfl e q
  have hc : (A q).d 2 3 rfl c = 0 := by
    have hcomm := R.comm 2 3 2 3 rfl rfl rfl rfl e
    rw [he, map_zero] at hcomm
    exact (congrFun hcomm q).symm
  have hcone : (coneCx Q.resE).d 2 3 rfl (e, z) = locT Q (Pi.single q c) := by
    refine Prod.ext ?_ ?_
    · exact he
    · funext v
      change R.f 2 2 rfl e v - (A v).d 1 2 rfl (z v) = (Pi.single q c : ∀ v, (A v).X 2) v
      by_cases hv : v = q
      · rw [hv, Pi.single_eq_same]
        have hz : z q = 0 := dite_eq_left rfl
        rw [hz, map_zero, sub_zero]
      · rw [Pi.single_eq_of_ne hv]
        have hz : z v = y v hv := dite_eq_right hv
        rw [hz, hy v hv, sub_self]
  have h0 : residualTraceAt X β hβ Iso tr q c = 0 :=
    calc residualTraceAt X β hβ Iso tr q c = tr (locT Q (Pi.single q c)) := rfl
      _ = tr ((coneCx Q.resE).d 2 3 rfl (e, z)) := by rw [hcone]
      _ = 0 := htr (e, z)
  exact hiso.1 c hc h0

/-- **`hmatch` is equivalent to reciprocity at `q`** for the genuine trace: given that the cone
trace kills coboundaries and induces `H^3_c ≅ F_2`, and given the A23 comparison, the matching of
the restricted trace with the Brauer invariant of `K_q` holds exactly when `ReciprocityAt` does. -/
theorem hmatch_iff_reciprocityAt (X : GenuineSwitch K S (ZMod 2) M)
    (β : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
    (hβ : ∀ (g : GKS K S) x y, β (g • x) (g • y) = g • β x y)
    (Iso : GaloisIsotropyData K S (ZMod 2) β hβ X.ΔS X.ΔR)
    (tr : (coneCx (galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).X 3 →ₗ[ZMod 2] ZMod 2)
    (htr : ∀ c, tr ((coneCx (galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).d 2 3 rfl c) = 0)
    (htr3 : InducesIsoH3 (C := coneCx (galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE) tr)
    (q : Places K S) (hKB : KummerBrauerComparisonF2 (q.1.adicCompletion K))
    (eμ : ResMod (locMap K S q.1) T ≃+ TauCeti.KummerCoeff (q.1.adicCompletion K) 2)
    (heμ : ∀ (g : TauCeti.AbsoluteGaloisGroup (q.1.adicCompletion K))
      (t : ResMod (locMap K S q.1) T),
      eμ ((TauCeti.absoluteGaloisGroupRestrictEquiv (q.1.adicCompletion K)).symm g • t) =
        g • eμ t) :
    LocalTraceMatchesInvariant eμ heμ (residualTraceAt X β hβ Iso tr q) ↔
      ReciprocityAt K S T q :=
  ⟨fun h => reciprocityAt_of_inducesIsoH2 X β hβ Iso tr htr q
      (inducesIsoH2_of_KummerBrauer eμ heμ hKB _ h),
    fun h => hmatch_of_reciprocity X β hβ Iso tr htr htr3 q h hKB eμ heμ⟩

end Reciprocity

/-! ### The tame switch consumer for the genuine residual objects -/

section Assembly

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  [DecidableEq (Places K S)] {W : WeierstrassCurve K} [W.IsElliptic]
  (F : DerivFamily (galLv (k := ZMod 2) K S (ETwo K S W))) {q : Places K S}
  (hR : RelAt (Gv := fun v : Places K S => Gloc K v.1)
    (Mv := fun v : Places K S => ResMod (locMap K S v.1) (ETwo K S W)) F.str F.rel q)

/-- **`hmatch` for the genuine residual objects**: for the switch of a derivative family of
`E(K_S)[2]` with the Weil pairing, the restriction of a cone trace inducing `H^3_c ≅ F_2` to the
switch place matches the Brauer invariant of `K_q` through `eMuq`, given reciprocity at `q` and the
A23 comparison. -/
theorem hmatch_genuine (φ σ : Gloc K q.1)
    (eM : ResMod (locMap K S q.1) (ETwo K S W) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    {I : Subgroup (Gloc K q.1)}
    (Tc : TameCoordinates (M := ResMod (locMap K S q.1) (ETwo K S W)) I φ σ)
    (Iso : GaloisIsotropyData K S (ZMod 2) (weilTwo K S W) (weilTwo_smul K S W)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR)
    (tr : (coneCx (galoisPairData K S (ZMod 2) (weilTwo K S W) (weilTwo_smul K S W)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).X 3 →ₗ[ZMod 2] ZMod 2)
    (htr : ∀ c, tr ((coneCx (galoisPairData K S (ZMod 2) (weilTwo K S W) (weilTwo_smul K S W)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).d 2 3 rfl c) = 0)
    (htr3 : InducesIsoH3 (C := coneCx (galoisPairData K S (ZMod 2) (weilTwo K S W)
      (weilTwo_smul K S W) (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE) tr)
    (hrec : ReciprocityAt K S (MuTwo K S) q)
    (hKB : KummerBrauerComparisonF2 (q.1.adicCompletion K)) :
    LocalTraceMatchesInvariant (eMuq K S q) (heMuq K S q)
      (residualTraceAt (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)) (weilTwo K S W)
        (weilTwo_smul K S W) Iso tr q) :=
  hmatch_of_reciprocity _ (weilTwo K S W) (weilTwo_smul K S W) Iso tr htr htr3 q hrec hKB
    (eMuq K S q) (heMuq K S q)

/-- **For the genuine objects, `hmatch` is equivalent to reciprocity at `q`** (given the trace
hypotheses and the A23 comparison). -/
theorem hmatch_genuine_iff (φ σ : Gloc K q.1)
    (eM : ResMod (locMap K S q.1) (ETwo K S W) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    {I : Subgroup (Gloc K q.1)}
    (Tc : TameCoordinates (M := ResMod (locMap K S q.1) (ETwo K S W)) I φ σ)
    (Iso : GaloisIsotropyData K S (ZMod 2) (weilTwo K S W) (weilTwo_smul K S W)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR)
    (tr : (coneCx (galoisPairData K S (ZMod 2) (weilTwo K S W) (weilTwo_smul K S W)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).X 3 →ₗ[ZMod 2] ZMod 2)
    (htr : ∀ c, tr ((coneCx (galoisPairData K S (ZMod 2) (weilTwo K S W) (weilTwo_smul K S W)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).d 2 3 rfl c) = 0)
    (htr3 : InducesIsoH3 (C := coneCx (galoisPairData K S (ZMod 2) (weilTwo K S W)
      (weilTwo_smul K S W) (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE) tr)
    (hKB : KummerBrauerComparisonF2 (q.1.adicCompletion K)) :
    LocalTraceMatchesInvariant (eMuq K S q) (heMuq K S q)
      (residualTraceAt (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)) (weilTwo K S W)
        (weilTwo_smul K S W) Iso tr q) ↔ ReciprocityAt K S (MuTwo K S) q :=
  hmatch_iff_reciprocityAt _ (weilTwo K S W) (weilTwo_smul K S W) Iso tr htr htr3 q hKB
    (eMuq K S q) (heMuq K S q)

/-- **The tame switch consumer with the six identifications supplied for the genuine residual
objects**: coefficient module `E(K_S)[2]`, target `μ_2`, coefficient pairing the Weil pairing
`e_2`. The identifications are `eTq`, `eM₂ = eM`, `weilTwo_hWeil`, `eMuq`, `heMuq`, and
`hmatch_of_reciprocity`. The remaining inputs are the printed `MilneCor23Residual`, the A23
comparison `KummerBrauerComparisonF2 K_q`, `FullTorsion K S W 2`, the genuine trace hypothesis
`InducesIsoH3 tr`, the reciprocity statement `ReciprocityAt`, and the switch inputs of the
consumer. -/
theorem derivSwitch_switchCoordinates_tame_genuine (hW : FullTorsion K S W 2)
    (hMilne : MilneCor23Residual) (hKB : KummerBrauerComparisonF2 (q.1.adicCompletion K))
    (hrec : ReciprocityAt K S (MuTwo K S) q)
    (φ σ : Gloc K q.1)
    (eM : ResMod (locMap K S q.1) (ETwo K S W) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    {I : Subgroup (Gloc K q.1)}
    (Tc : TameCoordinates (M := ResMod (locMap K S q.1) (ETwo K S W)) I φ σ)
    (hIur : ∀ g, urRes K q.1 g = 1 → g ∈ I)
    (γ : ETwo K S W →ₗ[ZMod 2] ETwo K S W →ₗ[ZMod 2] MuTwo K S)
    (hγ : ∀ (g : GKS K S) x y, γ (g • x) (g • y) = g • γ x y)
    (hpol : ∀ x y, weilTwo K S W x y = γ x y - γ y x)
    (Iso : GaloisIsotropyData K S (ZMod 2) (weilTwo K S W) (weilTwo_smul K S W)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR)
    (tr : (coneCx (galoisPairData K S (ZMod 2) (weilTwo K S W) (weilTwo_smul K S W)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).X 3 →ₗ[ZMod 2] ZMod 2)
    (htr : ∀ c, tr ((coneCx (galoisPairData K S (ZMod 2) (weilTwo K S W) (weilTwo_smul K S W)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).d 2 3 rfl c) = 0)
    (htr3 : InducesIsoH3 (C := coneCx (galoisPairData K S (ZMod 2) (weilTwo K S W)
      (weilTwo_smul K S W) (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE) tr)
    (hUS2 : ∀ v (x : (F.str v).cx.X 2), x = 0)
    {ε : ZMod 2} (hε : ε ≠ 0) {J : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hJ2 : J * J = 1)
    (htriv : ∀ (g : Gloc K q.1) (m : ETwo K S W), locMap K S q.1 g • m = m) :
    let X := derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)
    ∃ Φ : ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) ≃ₗ[ZMod 2]
        ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)),
      (finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2)).map Φ.toLinearMap =
        finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ∧
      ({ X with eR := X.eR.trans Φ } : GenuineSwitch K S (ZMod 2) (ETwo K S W)).SwitchCoordinates
        (galoisPairData K S (ZMod 2) (weilTwo K S W) (weilTwo_smul K S W) X.ΔS X.ΔR Iso) tr ε
        (-(-1)) J :=
  derivSwitch_switchCoordinates_tame_of_Milne F hR hMilne φ σ eM Tc hIur (weilTwo K S W) γ
    (weilTwo_smul K S W) hγ hpol Iso tr htr hUS2 hε hJ2 htriv (locMap_smul_muTwo q)
    (eTq K S q) eM (weilTwo_hWeil hW q eM) hKB (eMuq K S q) (heMuq K S q)
    (hmatch_of_reciprocity _ (weilTwo K S W) (weilTwo_smul K S W) Iso tr htr htr3 q hrec hKB
      (eMuq K S q) (heMuq K S q))

/-- **The same with the polarization supplied, when `E[2]` is rational** (tex 4479–4480): if
`G_{K,S}` fixes `E(K_S)[2]`, the polarization `γ` and the local triviality at `q` are derived. -/
theorem derivSwitch_switchCoordinates_tame_genuine_rational (hW : FullTorsion K S W 2)
    (hMilne : MilneCor23Residual) (hKB : KummerBrauerComparisonF2 (q.1.adicCompletion K))
    (hrec : ReciprocityAt K S (MuTwo K S) q)
    (htrivG : ∀ (g : GKS K S) (P : ETwo K S W), g • P = P)
    (φ σ : Gloc K q.1)
    (eM : ResMod (locMap K S q.1) (ETwo K S W) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    {I : Subgroup (Gloc K q.1)}
    (Tc : TameCoordinates (M := ResMod (locMap K S q.1) (ETwo K S W)) I φ σ)
    (hIur : ∀ g, urRes K q.1 g = 1 → g ∈ I)
    (Iso : GaloisIsotropyData K S (ZMod 2) (weilTwo K S W) (weilTwo_smul K S W)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR)
    (tr : (coneCx (galoisPairData K S (ZMod 2) (weilTwo K S W) (weilTwo_smul K S W)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).X 3 →ₗ[ZMod 2] ZMod 2)
    (htr : ∀ c, tr ((coneCx (galoisPairData K S (ZMod 2) (weilTwo K S W) (weilTwo_smul K S W)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).d 2 3 rfl c) = 0)
    (htr3 : InducesIsoH3 (C := coneCx (galoisPairData K S (ZMod 2) (weilTwo K S W)
      (weilTwo_smul K S W) (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE) tr)
    (hUS2 : ∀ v (x : (F.str v).cx.X 2), x = 0)
    {ε : ZMod 2} (hε : ε ≠ 0) {J : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hJ2 : J * J = 1) :
    let X := derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)
    ∃ Φ : ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) ≃ₗ[ZMod 2]
        ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)),
      (finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2)).map Φ.toLinearMap =
        finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ∧
      ({ X with eR := X.eR.trans Φ } : GenuineSwitch K S (ZMod 2) (ETwo K S W)).SwitchCoordinates
        (galoisPairData K S (ZMod 2) (weilTwo K S W) (weilTwo_smul K S W) X.ΔS X.ΔR Iso) tr ε
        (-(-1)) J := by
  obtain ⟨γ, hγ, hpol⟩ := weilTwo_polarization hW eM htrivG
  exact derivSwitch_switchCoordinates_tame_genuine F hR hW hMilne hKB hrec φ σ eM Tc hIur γ hγ
    hpol Iso tr htr htr3 hUS2 hε hJ2 (fun g m => htrivG (locMap K S q.1 g) m)

end Assembly

/-! ### The manuscript's residual curve `E_ℓ : y^2 = x (x - ℓ) (x + 3 ℓ)` -/

section Curve

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  [DecidableEq (Places K S)] {ℓ : K} [(curveEll ℓ).IsElliptic]
  (F : DerivFamily (galLv (k := ZMod 2) K S (ETwo K S (curveEll ℓ)))) {q : Places K S}
  (hR : RelAt (Gv := fun v : Places K S => Gloc K v.1)
    (Mv := fun v : Places K S => ResMod (locMap K S v.1) (ETwo K S (curveEll ℓ))) F.str F.rel q)

/-- **The tame switch consumer for the curve `E_ℓ` of the manuscript** (tex 1760–1830, with full
rational `2`-torsion, `ℓ ≠ 0`): `E_ℓ[2] ⊆ E_ℓ(K)`, so `FullTorsion` and the triviality of the
Galois action on `E_ℓ(K_S)[2]` are proved, and with them the polarization and the six
identifications. The remaining inputs are `MilneCor23Residual`, `KummerBrauerComparisonF2 K_q`,
`ReciprocityAt`, the trace hypothesis `InducesIsoH3 tr`, and the switch inputs of the consumer. -/
theorem derivSwitch_switchCoordinates_tame_curveEll (hℓ : ℓ ≠ 0)
    (hMilne : MilneCor23Residual) (hKB : KummerBrauerComparisonF2 (q.1.adicCompletion K))
    (hrec : ReciprocityAt K S (MuTwo K S) q)
    (φ σ : Gloc K q.1)
    (eM : ResMod (locMap K S q.1) (ETwo K S (curveEll ℓ)) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    {I : Subgroup (Gloc K q.1)}
    (Tc : TameCoordinates (M := ResMod (locMap K S q.1) (ETwo K S (curveEll ℓ))) I φ σ)
    (hIur : ∀ g, urRes K q.1 g = 1 → g ∈ I)
    (Iso : GaloisIsotropyData K S (ZMod 2) (weilTwo K S (curveEll ℓ)) (weilTwo_smul K S _)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR)
    (tr : (coneCx (galoisPairData K S (ZMod 2) (weilTwo K S (curveEll ℓ)) (weilTwo_smul K S _)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).X 3 →ₗ[ZMod 2] ZMod 2)
    (htr : ∀ c, tr ((coneCx (galoisPairData K S (ZMod 2) (weilTwo K S (curveEll ℓ))
      (weilTwo_smul K S _) (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).d 2 3 rfl c) = 0)
    (htr3 : InducesIsoH3 (C := coneCx (galoisPairData K S (ZMod 2) (weilTwo K S (curveEll ℓ))
      (weilTwo_smul K S _) (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE) tr)
    (hUS2 : ∀ v (x : (F.str v).cx.X 2), x = 0)
    {ε : ZMod 2} (hε : ε ≠ 0) {J : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hJ2 : J * J = 1) :
    let X := derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)
    ∃ Φ : ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) ≃ₗ[ZMod 2]
        ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)),
      (finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2)).map Φ.toLinearMap =
        finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ∧
      ({ X with eR := X.eR.trans Φ } :
          GenuineSwitch K S (ZMod 2) (ETwo K S (curveEll ℓ))).SwitchCoordinates
        (galoisPairData K S (ZMod 2) (weilTwo K S (curveEll ℓ)) (weilTwo_smul K S _) X.ΔS X.ΔR
          Iso) tr ε (-(-1)) J :=
  derivSwitch_switchCoordinates_tame_genuine_rational F hR (fullTorsion_two_curveEll hℓ) hMilne
    hKB hrec (fun g P => smul_torsTwo_cubicCurve 0 ℓ (-3 * ℓ) g P) φ σ eM Tc hIur Iso tr htr htr3
    hUS2 hε hJ2

end Curve

/-! ### The actual residual module `F_2 ⊗_{A_{j+1}} M_{j+1}` -/

section ResidualModule

open ZInQ.Manuscript.RC.HeegnerAlgebra

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (j : ℕ) (α : GKS K S →* (Acoef (j + 1))ˣ)
  (hT : FullTorsion K S W (2 ^ (j + 1))) (hM : FullTorsion K S W (2 ^ j))
  (h2 : FullTorsion K S W 2)

/-- **The actual residual module is `E(K_S)[2]`**, `F_2`-linearly: the identification
`residualEquiv` of `F_2 ⊗_{A_{j+1}} M_{j+1}` with `E(K_S)[2]`. -/
def residualToETwo : ResidualM W j α ≃ₗ[ZMod 2] ETwo K S W :=
  LinearEquiv.ofBijective
    ((residualEquiv j α hT hM h2 : ResidualM W j α ≃+ ETwo K S W).toAddMonoidHom.toZModLinearMap 2)
    (residualEquiv j α hT hM h2).bijective

omit [NumberField K] [W.IsElliptic] in
/-- The identification is `G_{K,S}`-equivariant (`residualEquiv_resAct`). -/
theorem residualToETwo_smul (σ : GKS K S) (x : ResidualM W j α) :
    residualToETwo W j α hT hM h2 (σ • x) = σ • residualToETwo W j α hT hM h2 x :=
  residualEquiv_resAct j α hT hM h2 σ x

/-- **The Weil pairing on the actual residual module**, transported from `E(K_S)[2]`. -/
def weilResidual : ResidualM W j α →ₗ[ZMod 2] ResidualM W j α →ₗ[ZMod 2] MuTwo K S :=
  (weilTwo K S W).compl₁₂ (residualToETwo W j α hT hM h2).toLinearMap
    (residualToETwo W j α hT hM h2).toLinearMap

theorem weilResidual_apply (x y : ResidualM W j α) :
    weilResidual W j α hT hM h2 x y =
      weilTwo K S W (residualToETwo W j α hT hM h2 x) (residualToETwo W j α hT hM h2 y) :=
  rfl

/-- The transported Weil pairing is equivariant. -/
theorem weilResidual_smul (σ : GKS K S) (x y : ResidualM W j α) :
    weilResidual W j α hT hM h2 (σ • x) (σ • y) = σ • weilResidual W j α hT hM h2 x y := by
  rw [weilResidual_apply, weilResidual_apply, residualToETwo_smul, residualToETwo_smul,
    weilTwo_smul]

theorem weilResidual_self (x : ResidualM W j α) : weilResidual W j α hT hM h2 x x = 0 :=
  weilTwo_self K S W _

theorem weilResidual_nondegenerate (x : ResidualM W j α)
    (hx : ∀ y, weilResidual W j α hT hM h2 x y = 0) : x = 0 := by
  apply (residualToETwo W j α hT hM h2).injective
  rw [map_zero]
  refine weilTwo_nondegenerate h2 _ fun Q => ?_
  have h := hx ((residualToETwo W j α hT hM h2).symm Q)
  rwa [weilResidual_apply, LinearEquiv.apply_symm_apply] at h

/-- **`hWeil` for the actual residual module**, with `eM₂ = eM`, for any coordinates `eM` at `q`. -/
theorem weilResidual_hWeil (q : Places K S)
    (eM : ResMod (locMap K S q.1) (ResidualM W j α) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (x y : ResMod (locMap K S q.1) (ResidualM W j α)) :
    eTq K S q (resPairing (ZMod 2) (GKS K S) (weilResidual W j α hT hM h2) (locMap K S q.1) x y) =
      weil (eM x) (eM y) :=
  alternating_eq_weil_of_nondegenerate eM (eTq K S q)
    (resPairing (ZMod 2) (GKS K S) (weilResidual W j α hT hM h2) (locMap K S q.1))
    (fun x => weilResidual_self W j α hT hM h2 x)
    (fun x hx => weilResidual_nondegenerate W j α hT hM h2 x hx) x y

/-- **The polarization on the actual residual module** when `E[2]` is rational. -/
theorem weilResidual_polarization
    (htriv : ∀ (σ : GKS K S) (P : TorsS K S W ((2 : ℕ) : ℤ)), σ • P = P) :
    ∃ γ : ResidualM W j α →ₗ[ZMod 2] ResidualM W j α →ₗ[ZMod 2] MuTwo K S,
      (∀ (g : GKS K S) x y, γ (g • x) (g • y) = g • γ x y) ∧
        ∀ x y, weilResidual W j α hT hM h2 x y = γ x y - γ y x := by
  obtain ⟨γ, hγ, hpol⟩ := weilTwo_polarization h2 (eTwoCoords h2) htriv
  refine ⟨γ.compl₁₂ (residualToETwo W j α hT hM h2).toLinearMap
    (residualToETwo W j α hT hM h2).toLinearMap, fun g x y => ?_, fun x y => hpol _ _⟩
  change γ (residualToETwo W j α hT hM h2 (g • x)) (residualToETwo W j α hT hM h2 (g • y)) =
    g • γ (residualToETwo W j α hT hM h2 x) (residualToETwo W j α hT hM h2 y)
  rw [residualToETwo_smul, residualToETwo_smul, hγ]

variable [ContinuousSMul (GKS K S) (ResidualM W j α)] [DecidableEq (Places K S)]
  (F : DerivFamily (galLv (k := ZMod 2) K S (ResidualM W j α))) {q : Places K S}
  (hR : RelAt (Gv := fun v : Places K S => Gloc K v.1)
    (Mv := fun v : Places K S => ResMod (locMap K S v.1) (ResidualM W j α)) F.str F.rel q)

/-- **The tame switch consumer for the actual residual module** `F_2 ⊗_{A_{j+1}} M_{j+1}`,
with the Weil pairing transported from `E(K_S)[2]`, when `E[2]` is rational (the residual
representation is trivial, tex 4479–4480). The continuity instance is supplied by
`continuousSMul_residualM` under the same hypotheses. -/
theorem derivSwitch_switchCoordinates_tame_residualM
    (htriv : ∀ (σ : GKS K S) (P : TorsS K S W ((2 : ℕ) : ℤ)), σ • P = P)
    (hMilne : MilneCor23Residual) (hKB : KummerBrauerComparisonF2 (q.1.adicCompletion K))
    (hrec : ReciprocityAt K S (MuTwo K S) q)
    (φ σ : Gloc K q.1)
    (eM : ResMod (locMap K S q.1) (ResidualM W j α) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    {I : Subgroup (Gloc K q.1)}
    (Tc : TameCoordinates (M := ResMod (locMap K S q.1) (ResidualM W j α)) I φ σ)
    (hIur : ∀ g, urRes K q.1 g = 1 → g ∈ I)
    (Iso : GaloisIsotropyData K S (ZMod 2) (weilResidual W j α hT hM h2)
      (weilResidual_smul W j α hT hM h2)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR)
    (tr : (coneCx (galoisPairData K S (ZMod 2) (weilResidual W j α hT hM h2)
      (weilResidual_smul W j α hT hM h2)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).X 3 →ₗ[ZMod 2] ZMod 2)
    (htr : ∀ c, tr ((coneCx (galoisPairData K S (ZMod 2) (weilResidual W j α hT hM h2)
      (weilResidual_smul W j α hT hM h2)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).d 2 3 rfl c) = 0)
    (htr3 : InducesIsoH3 (C := coneCx (galoisPairData K S (ZMod 2)
      (weilResidual W j α hT hM h2) (weilResidual_smul W j α hT hM h2)
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE) tr)
    (hUS2 : ∀ v (x : (F.str v).cx.X 2), x = 0)
    {ε : ZMod 2} (hε : ε ≠ 0) {J : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hJ2 : J * J = 1) :
    let X := derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)
    ∃ Φ : ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) ≃ₗ[ZMod 2]
        ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)),
      (finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2)).map Φ.toLinearMap =
        finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ∧
      ({ X with eR := X.eR.trans Φ } : GenuineSwitch K S (ZMod 2) (ResidualM W j α)).SwitchCoordinates
        (galoisPairData K S (ZMod 2) (weilResidual W j α hT hM h2)
          (weilResidual_smul W j α hT hM h2) X.ΔS X.ΔR Iso) tr ε (-(-1)) J := by
  obtain ⟨γ, hγ, hpol⟩ := weilResidual_polarization W j α hT hM h2 htriv
  exact derivSwitch_switchCoordinates_tame_of_Milne F hR hMilne φ σ eM Tc hIur
    (weilResidual W j α hT hM h2) γ (weilResidual_smul W j α hT hM h2) hγ hpol Iso tr htr hUS2
    hε hJ2 (fun g m => smul_residualM_eq W j α hT hM h2 htriv (locMap K S q.1 g) m)
    (locMap_smul_muTwo q) (eTq K S q) eM (weilResidual_hWeil W j α hT hM h2 q eM) hKB
    (eMuq K S q) (heMuq K S q)
    (hmatch_of_reciprocity _ (weilResidual W j α hT hM h2) (weilResidual_smul W j α hT hM h2) Iso
      tr htr htr3 q hrec hKB (eMuq K S q) (heMuq K S q))

end ResidualModule

end ZInQ.Contrib.RC53Assist.HswIdent

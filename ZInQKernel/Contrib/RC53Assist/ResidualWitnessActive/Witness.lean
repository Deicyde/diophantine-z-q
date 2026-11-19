import ZInQKernel.Contrib.OneProof.RC.CoefModules.CocycleCondition
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Surjective
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Galois
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.KernelCard
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Galois
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Selmer
import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.CoefResidualCounts
import ZInQKernel.Contrib.CloudB3RC53.ContBridge.Discrete
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedFactorization
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Instances
import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.ResidualAfterT

/-!
# A non-degenerate witness for the residual rank counts

The two constructors `ZInQ.Contrib.CloudB3RC53.Mattuck.residualRankCounts_genuine` and
`ZInQ.Contrib.CloudB3RC53.GenuineInst.residualRankCounts_actual` (manuscript Lemma
`ex:limits-residual-bound`, tex 4453–4648) are applied to one instance in which the condition
labels, the local conditions, the support change and the residual model all carry content.

**The instance.** `K = ℚ(i)`, `k = −1`, `A = 0`. The curve is `E₁₁ : y² = x(x − 11)(x + 33)`,
with the integral equation `y² = x³ + 22x² − 363x` at every finite place; all four points killed
by `2` are rational. `N = 66`, the moving prime is `r = 5`, the derivative primes are `D = {7}`
(an inert prime), and `13` is an active prime. `S₀ = Sloc = S` is the set of places above
`{2, 3, 5, 7, 11}` and `S'` adds the places above `13`, so `S' − S` is nonempty. The coefficients
are the actual residual module `𝔽₂ ⊗ M₁` of `E₁₁` at index `j = 0` (four elements, trivial
action; at `j = 0` the only character is the trivial one).

**The local conditions** are genuine complexes with cochain maps into the continuous local
cochains `C^•(G_{K_v}, M)`:
* the old Kummer condition above `2, 3, 11`: all `0`-cochains, and in degree one the span of the
  Kummer cocycles `σ ↦ ι(σQ − Q)` of the points of `E₁₁(K_v)` together with the coboundaries, for an
  `𝔽₂`-isomorphism `ι : E₁₁(K̄_v)[2] ≅ M` (both sides carry the trivial action);
* the relaxed derivative condition `τ≤1 C^•(G_{K_v}, M)` above `7`;
* the full condition above `5`;
* at the active places, the unramified condition `C^•(G_q/I_q, M)` of the support change, with the
  factorizations of the localizations through `G_q/I_q` proved in the repository.

**The residual model.** Over a field every complex is quasi-isomorphic to its cohomology, and a
cochain map agrees with the map it induces on cohomology up to an explicit homotopy. The residual
model is the Selmer cone of the cohomology of the global complex, of each local condition and of
each local complex, with the induced maps; `formalMap_quasiIso` is an actual quasi-isomorphism from
its cone to the genuine Selmer complex, for arbitrary local conditions. No rank of a localization
map is computed.

**What the hypotheses carry here.** A place above `7` has the relaxed derivative label and the
places above `2, 3, 11` the old Kummer label (`exists_derivative_place`, `exists_oldKummer_place`).
The condition and local parts of the residual model are nonzero and are bounded by the genuine
dimensions (`act_hUm`, `act_hLm`, `act_U_positive`, `act_L_positive`); the condition bound holds
with equality (`act_hUm_eq`): at the old Kummer rows the cohomology of the Kummer complex has
exactly Mattuck's dimension `dim E(K_v)[2] + dim E(K_v)/2`, with `H¹ ≅ E(K_v)/2 ≠ 0`
(`oldKummer_places_exact`). The map `pP` is a quasi-isomorphism onto the genuine smaller-support Selmer
complex with these conditions. The support change is the genuine one with a nonempty set of new
places (`newPlaces_nonempty`). The change of condition is not the identity and has a nonzero
acyclic quotient (`actW_nontrivial`). The minimal model `L` of the original-support complex is
reached through the support change and the change of condition; it is nonzero and has strictly
smaller rank than the residual cone: `2 ≤ genericRank < rankTot` for both constructors
(`two_le_genericRank`, `activeGenuineCounts_strict`, `activeActualCounts_strict`).

**The case over `𝔽₂`.** Over `𝔽₂` the change from the unramified to the full condition at an
active place has a non-acyclic quotient (`active_full_change_not_acyclic`, from `h¹ = 2` against
`h¹ = 4`). For the constructors with coefficients `𝔽₂` the change of condition used here thickens
the unramified conditions at the active places by the contractible cone of their identity.

**After inverting `t`.** The constructor `residualRankCounts_afterT` (imported from
`GenuineInst.ResidualAfterT`) takes the transfer over `𝔽₂[[t]]` and `𝔽₂((t))`, as in the text (tex 4612–4631). It
is applied to the same instance (`activeAfterTCounts`) with:
* the smaller-support free model `P` over `𝔽₂[[t]]`: the residual cone extended to `𝔽₂[[t]]`, whose
  reduction modulo `t` has the ranks of the residual cone (`afterP_hred`), and its base change `P'`
  to `𝔽₂((t))`;
* at each place above `13`, the active comparison block `[𝔽₂[[t]]² --((1+t)^e − 1)--> 𝔽₂[[t]]²]` in
  degrees `1, 2` (the reduction of (4.4), with `e = 1` at a chosen place and `e = −1` at the other
  places above `13`); its entry vanishes modulo `t` and is `t` times a unit (`activeC_constantCoeff`,
  `activeC_eq_X_mul`); the blocks are not acyclic over `𝔽₂[[t]]` (`activeW_not_acyclic`) and their
  base change to `𝔽₂((t))` is acyclic (`activeW'_acyclic`);
* the integral original-support model `Q = P ⊕ W` and its base change `Q'`, with the generic change
  of condition `0 → P' → Q' → W' → 0` (`afterSES_shortExact`); the inclusion `P' → Q'` is a
  quasi-isomorphism because the active blocks are acyclic after inverting `t` (`afterIncl_quasiIso`);
* the generic minimal model `L`, the cohomology of `Q'`, and the homotopy equivalence `L ≃ P'`
  obtained through `Q'` (`afterE`).
It gives `2 ≤ genericRank ≤ rankTot` and `genericRank ≤ 294` (`residualRankCounts_afterT_active`,
`two_le_afterT_genericRank`). The smaller-support model over `𝔽₂[[t]]` is the constant extension of
the residual cone: the global character over `S` with Frobenius `(1+t)^e` at the active places is
not constructed (it requires class field theory), and the gluing of `Q` is split.

The printed inputs (Milne, ADT I.4.10, I.5.1, I.2.8, I.2.3; Nekovář 7.8.8(ii)) remain explicit
hypotheses of the statements; no new proposition is introduced.
-/

noncomputable section

set_option maxHeartbeats 400000

/-! ## Local Kummer conditions

The declarations of this namespace are a verbatim copy of those of the module
`ZInQKernel.Contrib.OneProof.RC.CoefModules.Kummer` (Lemma `ex:arith-local-kummer`, tex
3413–3468), whose compiled form is not part of this build; only the namespace is changed. -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive.LocalKummer

open ZInQ.Manuscript.RC.CoefModules

open CategoryTheory WeierstrassCurve ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Manuscript.RC.SelmerComplex NumberField
  IsDedekindDomain

/-! ### The Galois module `B(F̄)` and its `m`-torsion -/

section Points

variable (F : Type) [Field F] (B : WeierstrassCurve F)

/-- Definition (tex 3413–3416: the points of the local twist over `F̄`). The points `B(F̄)` of
`B` over the algebraic closure `F̄ = AlgebraicClosure F`, as a type synonym of the points of the
base change, carrying the discrete topology and the Galois action. -/
def PtAlg : Type := (B.baseChange (AlgebraicClosure F)).toAffine.Point

open scoped Classical in
/-- Definition (tex 3413–3416). The group law of `B(F̄)`. -/
instance PtAlg.instAddCommGroup : AddCommGroup (PtAlg F B) :=
  inferInstanceAs (AddCommGroup (B.baseChange (AlgebraicClosure F)).toAffine.Point)

/-- Definition (tex 3413–3416). `B(F̄)` carries the discrete topology. -/
instance PtAlg.instTopologicalSpace : TopologicalSpace (PtAlg F B) := ⊥

/-- PROVED (tex 3413–3416). The topology of `B(F̄)` is discrete. -/
instance PtAlg.instDiscreteTopology : DiscreteTopology (PtAlg F B) := ⟨rfl⟩

open scoped Classical in
/-- Definition (tex 3413–3416). The identification of `PtAlg F B` with the points of the base
change of `B` to `F̄`. -/
def ptEquiv : (B.baseChange (AlgebraicClosure F)).toAffine.Point ≃+ PtAlg F B :=
  AddEquiv.refl _

variable {F B}

open scoped Classical in
/-- Definition (tex 3413–3416). The absolute Galois group `G_F = Gal(F̄/F)` (Mathlib's
`Field.absoluteGaloisGroup F`) acts on `B(F̄)` through the coordinates (Mathlib's
`WeierstrassCurve.Affine.Point.map` along each automorphism). -/
instance PtAlg.instSMul : SMul (Field.absoluteGaloisGroup F) (PtAlg F B) where
  smul σ P := ptEquiv F B (Affine.Point.map (W' := B) σ.toAlgHom ((ptEquiv F B).symm P))

open scoped Classical in
/-- PROVED (tex 3413–3416). The Galois action on a point is the point map along the
automorphism. -/
theorem smul_ptEquiv (σ : Field.absoluteGaloisGroup F)
    (P : (B.baseChange (AlgebraicClosure F)).toAffine.Point) :
    σ • ptEquiv F B P = ptEquiv F B (Affine.Point.map (W' := B) σ.toAlgHom P) :=
  rfl

open scoped Classical in
/-- PROVED (tex 3413–3416). The Galois action is the action `WeierstrassCurve.pointGaloisAction`
(`ZInQKernel/Contrib/TauCeti/AlgebraicGeometry/EllipticCurve/Affine/Point/Galois.lean`). -/
theorem pointGaloisAction_eq_smul (σ : Field.absoluteGaloisGroup F)
    (P : (B.baseChange (AlgebraicClosure F)).toAffine.Point) :
    ptEquiv F B (Multiplicative.toAdd (B.pointGaloisAction σ) P) = σ • ptEquiv F B P :=
  congrArg (ptEquiv F B) (pointGaloisAction_apply B σ P)

open scoped Classical in
/-- PROVED (tex 3413–3416). `B(F̄)` is a `G_F`-module. -/
instance PtAlg.instDistribMulAction :
    DistribMulAction (Field.absoluteGaloisGroup F) (PtAlg F B) where
  one_smul P := by
    obtain ⟨P, rfl⟩ := (ptEquiv F B).surjective P
    rw [smul_ptEquiv]
    congr 1
    rcases P with _ | ⟨x, y, h⟩ <;> rfl
  mul_smul σ τ P := by
    obtain ⟨P, rfl⟩ := (ptEquiv F B).surjective P
    rw [smul_ptEquiv, smul_ptEquiv, smul_ptEquiv, Affine.Point.map_map]
    rfl
  smul_zero σ := by
    rw [← (ptEquiv F B).map_zero, smul_ptEquiv, map_zero]
  smul_add σ P Q := by
    obtain ⟨P, rfl⟩ := (ptEquiv F B).surjective P
    obtain ⟨Q, rfl⟩ := (ptEquiv F B).surjective Q
    rw [← map_add, smul_ptEquiv, smul_ptEquiv, smul_ptEquiv, map_add, map_add]

/-- PROVED (tex 3413–3416). The stabilizer in `G_F` of an element of `F̄` is open (Krull
topology; `F̄/F` is algebraic). -/
theorem isOpen_fix (x : AlgebraicClosure F) :
    IsOpen {σ : Field.absoluteGaloisGroup F | σ.toAlgHom x = x} := by
  have h := stabilizer_isOpen_of_isIntegral (K := F) (L := AlgebraicClosure F) x
  have e : {σ : Field.absoluteGaloisGroup F | σ.toAlgHom x = x} =
      ((MulAction.stabilizer (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) x :
        Set (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)) :
          Set (Field.absoluteGaloisGroup F)) := by
    ext σ
    exact Iff.rfl
  rw [e]
  exact h

open scoped Classical in
/-- PROVED (tex 3413–3416). **`B(F̄)` is a discrete `G_F`-module**: the stabilizer of a point
contains the (open) stabilizers of its coordinates. -/
instance PtAlg.instContinuousSMul : ContinuousSMul (Field.absoluteGaloisGroup F) (PtAlg F B) := by
  refine continuousSMul_iff_stabilizer_isOpen.2 fun P => ?_
  obtain ⟨P, rfl⟩ := (ptEquiv F B).surjective P
  rcases P with _ | ⟨x, y, h⟩
  · convert isOpen_univ
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_univ, iff_true]
    rw [← Affine.Point.zero_def, map_zero, smul_zero]
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    refine Filter.mem_of_superset (((isOpen_fix x).inter (isOpen_fix y)).mem_nhds ⟨rfl, rfl⟩) ?_
    rintro σ ⟨hx, hy⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, smul_ptEquiv, Affine.Point.map_some]
    congr 1
    simp only [Affine.Point.some.injEq]
    exact ⟨hx, hy⟩

variable (F B) in
/-- Definition (tex 3415–3417: `B[2^a]`, here for any `m`). **The `G_F`-module `B(F̄)[m]`**: the
`m`-torsion subgroup `AddSubgroup.torsionBy (B(F̄)) m` of the points of `B` over `F̄`. It is a
discrete (`Subtype.discreteTopology`) `G_F`-module, finite for `B` elliptic and `m ≠ 0`. -/
abbrev TorsAlg (m : ℕ) : Type := AddSubgroup.torsionBy (PtAlg F B) (m : ℤ)

/-- PROVED (tex 3415–3417). The Galois action preserves `B(F̄)[m]`. -/
theorem smul_mem_torsAlg {m : ℕ} (σ : Field.absoluteGaloisGroup F) {P : PtAlg F B}
    (hP : P ∈ AddSubgroup.torsionBy (PtAlg F B) (m : ℤ)) :
    σ • P ∈ AddSubgroup.torsionBy (PtAlg F B) (m : ℤ) := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← smul_comm, hP, smul_zero]

/-- PROVED (tex 3415–3417). `B(F̄)[m]` is a `G_F`-module. -/
instance TorsAlg.instDistribMulAction (m : ℕ) :
    DistribMulAction (Field.absoluteGaloisGroup F) (TorsAlg F B m) where
  smul σ t := ⟨σ • (t : PtAlg F B), smul_mem_torsAlg σ t.2⟩
  one_smul t := Subtype.ext (one_smul _ (t : PtAlg F B))
  mul_smul σ τ t := Subtype.ext (mul_smul σ τ (t : PtAlg F B))
  smul_zero σ := Subtype.ext (smul_zero σ)
  smul_add σ s t := Subtype.ext (smul_add σ (s : PtAlg F B) t)

/-- PROVED (tex 3415–3417). The action on `B(F̄)[m]` is the action on `B(F̄)`. -/
@[simp]
theorem coe_smul_torsAlg {m : ℕ} (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m) :
    ((σ • t : TorsAlg F B m) : PtAlg F B) = σ • (t : PtAlg F B) :=
  rfl

open scoped Classical in
/-- PROVED (tex 3415–3417). The action on `B(F̄)[m]` is the action
`WeierstrassCurve.torsionGaloisAction`
(`ZInQKernel/Contrib/TauCeti/AlgebraicGeometry/EllipticCurve/Affine/Point/Galois.lean`), read
through `ptEquiv`. -/
theorem torsionGaloisAction_eq_smul {m : ℕ} (σ : Field.absoluteGaloisGroup F)
    (t : AddSubgroup.torsionBy (B.baseChange (AlgebraicClosure F)).toAffine.Point (m : ℤ)) :
    ptEquiv F B ((Multiplicative.toAdd (B.torsionGaloisAction (m : ℤ) σ) t :
      AddSubgroup.torsionBy (B.baseChange (AlgebraicClosure F)).toAffine.Point (m : ℤ)) :
        (B.baseChange (AlgebraicClosure F)).toAffine.Point) =
      σ • ptEquiv F B (t : (B.baseChange (AlgebraicClosure F)).toAffine.Point) :=
  (congrArg (ptEquiv F B) (torsionGaloisAction_apply_coe B (m : ℤ) σ t)).trans
    (pointGaloisAction_eq_smul (B := B) σ (t : (B.baseChange (AlgebraicClosure F)).toAffine.Point))

/-- PROVED (tex 3415–3417). **`B(F̄)[m]` is a discrete `G_F`-module.** -/
instance TorsAlg.instContinuousSMul (m : ℕ) :
    ContinuousSMul (Field.absoluteGaloisGroup F) (TorsAlg F B m) :=
  ⟨Continuous.subtype_mk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩

open scoped Classical in
/-- PROVED (tex 3415–3417). **`B(F̄)[m]` is finite** for `B` elliptic and `m ≠ 0` (the other
group's `WeierstrassCurve.finite_torsionBy`). -/
instance TorsAlg.instFinite [B.IsElliptic] (m : ℕ) [NeZero m] : Finite (TorsAlg F B m) :=
  WeierstrassCurve.finite_torsionBy (B.baseChange (AlgebraicClosure F)) (n := (m : ℤ))
    (Int.natCast_ne_zero.2 (NeZero.ne m))

variable [DecidableEq F]

variable (F B) in
open scoped Classical in
/-- Definition (tex 3413–3417). The inclusion `B(F) → B(F̄)`, induced by `F → F̄`. -/
def basePt : B.toAffine.Point →+ PtAlg F B :=
  (ptEquiv F B).toAddMonoidHom.comp <|
    (Affine.Point.map (W' := B.toAffine) (Algebra.ofId F (AlgebraicClosure F))).comp
      (Affine.Point.equivBaseChangeSelf B.toAffine).toAddMonoidHom

open scoped Classical in
/-- PROVED (tex 3413–3417). The inclusion `B(F) → B(F̄)` keeps the coordinates. -/
theorem basePt_some {x y : F} (h : B.toAffine.Nonsingular x y) :
    basePt F B (.some x y h) =
      ptEquiv F B (.some (algebraMap F (AlgebraicClosure F) x)
        (algebraMap F (AlgebraicClosure F) y)
        ((B.toAffine.baseChange_nonsingular (Algebra.ofId F (AlgebraicClosure F)).injective
          x y).2 h)) := by
  simp only [basePt, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    Affine.Point.equivBaseChangeSelf_some, Affine.Point.map_some]
  rfl

/-- PROVED (tex 3413–3417). The inclusion `B(F) → B(F̄)` is injective. -/
theorem basePt_injective : Function.Injective (basePt F B) := by
  classical
  exact (ptEquiv F B).injective.comp <| (Affine.Point.map_injective _).comp
    (Affine.Point.equivBaseChangeSelf B.toAffine).injective

/-- PROVED (tex 3413–3417). The points of `B(F)` are fixed by `G_F`. -/
theorem smul_basePt (σ : Field.absoluteGaloisGroup F) (P : B.toAffine.Point) :
    σ • basePt F B P = basePt F B P := by
  classical
  rw [basePt, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, smul_ptEquiv,
    AddMonoidHom.comp_apply, Affine.Point.map_map]
  rw [Subsingleton.elim (σ.toAlgHom.comp (Algebra.ofId F (AlgebraicClosure F)))
    (Algebra.ofId F (AlgebraicClosure F))]

/-- PROVED (tex 3415–3417; Galois descent, `F` of characteristic zero so that `F̄/F` is Galois).
**A point of `B(F̄)` fixed by `G_F` comes from `B(F)`** (Mathlib's
`InfiniteGalois.mem_range_algebraMap_iff_fixed` applied to the coordinates). -/
theorem exists_basePt_of_fixed [CharZero F] {Q : PtAlg F B}
    (hQ : ∀ σ : Field.absoluteGaloisGroup F, σ • Q = Q) :
    ∃ P : B.toAffine.Point, basePt F B P = Q := by
  classical
  obtain ⟨Q, rfl⟩ := (ptEquiv F B).surjective Q
  rcases Q with _ | ⟨x, y, h⟩
  · exact ⟨0, by rw [map_zero, ← Affine.Point.zero_def, map_zero]⟩
  · have hfix : ∀ σ : Field.absoluteGaloisGroup F, σ.toAlgHom x = x ∧ σ.toAlgHom y = y :=
      fun σ => by
        have h := hQ σ
        rw [smul_ptEquiv, Affine.Point.map_some] at h
        simpa only [Affine.Point.some.injEq] using (ptEquiv F B).injective h
    obtain ⟨x₀, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).2 fun σ => (hfix σ).1
    obtain ⟨y₀, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed y).2 fun σ => (hfix σ).2
    have h₀ : B.toAffine.Nonsingular x₀ y₀ :=
      (B.toAffine.baseChange_nonsingular (Algebra.ofId F (AlgebraicClosure F)).injective
        x₀ y₀).1 h
    exact ⟨.some x₀ y₀ h₀, by rw [basePt_some]⟩

omit [DecidableEq F] in
/-- PROVED (tex 3413–3417). **`B(F̄)` is `m`-divisible** for `B` elliptic, `m ≠ 0`, `F` of
characteristic zero (`WeierstrassCurve.Affine.nsmul_surjective`,
`ZInQKernel/Contrib/TauCeti/AlgebraicGeometry/EllipticCurve/Isogeny/MulByInt/Surjective.lean`). -/
theorem exists_nsmul_eq [CharZero F] [B.IsElliptic] (m : ℕ) [NeZero m] (Q : PtAlg F B) :
    ∃ R : PtAlg F B, m • R = Q := by
  classical
  have hm : ((m : ℕ) : AlgebraicClosure F) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  obtain ⟨R, hR⟩ := Affine.nsmul_surjective (B.baseChange (AlgebraicClosure F)).toAffine hm
    ((ptEquiv F B).symm Q)
  refine ⟨ptEquiv F B R, ?_⟩
  rw [← map_nsmul]
  exact (congrArg (ptEquiv F B) hR).trans ((ptEquiv F B).apply_symm_apply Q)

variable (F B) in
/-- Definition (tex 3415–3417). The inclusion `B(F)[m] → B(F̄)[m]`. -/
def baseTors (m : ℕ) : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ) →+ TorsAlg F B m :=
  ((basePt F B).comp (AddSubgroup.torsionBy B.toAffine.Point (m : ℤ)).subtype).codRestrict _
    fun T => by
      rw [AddSubgroup.torsionBy.nsmul_iff, AddMonoidHom.comp_apply, ← map_nsmul,
        AddSubgroup.coe_subtype, AddSubgroup.torsionBy.nsmul_iff.1 T.2, map_zero]

/-- PROVED (tex 3415–3417). The inclusion `B(F)[m] → B(F̄)[m]` on underlying points. -/
@[simp]
theorem coe_baseTors {m : ℕ} (T : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ)) :
    (baseTors F B m T : PtAlg F B) = basePt F B T :=
  rfl

/-- PROVED (tex 3415–3417). The points of `B(F)[m]` are fixed by `G_F`. -/
theorem smul_baseTors {m : ℕ} (σ : Field.absoluteGaloisGroup F)
    (T : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ)) :
    σ • baseTors F B m T = baseTors F B m T :=
  Subtype.ext (by rw [coe_smul_torsAlg, coe_baseTors, smul_basePt])

/-- PROVED (tex 3415–3417). The inclusion `B(F)[m] → B(F̄)[m]` is injective. -/
theorem baseTors_injective (m : ℕ) : Function.Injective (baseTors F B m) :=
  fun _ _ h => Subtype.ext (basePt_injective (congrArg Subtype.val h))

/-- PROVED (tex 3415–3417: "`B(F)[2^a]` in degree zero"). **The `G_F`-invariants of `B(F̄)[m]`
are the points of `B(F)[m]`.** -/
theorem exists_baseTors_of_fixed [CharZero F] {m : ℕ} {Q : TorsAlg F B m}
    (h : ∀ σ : Field.absoluteGaloisGroup F, σ • Q = Q) :
    ∃ T : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ), baseTors F B m T = Q := by
  obtain ⟨T, hT⟩ := exists_basePt_of_fixed (B := B) (Q := (Q : PtAlg F B))
    fun σ => congrArg Subtype.val (h σ)
  refine ⟨⟨T, AddSubgroup.torsionBy.nsmul_iff.2 (basePt_injective ?_)⟩, Subtype.ext hT⟩
  rw [map_nsmul, hT, map_zero, AddSubgroup.torsionBy.nsmul_iff.1 Q.2]

end Points

/-! ### Kummer cocycles -/

section KummerCocycle

variable (F : Type) [Field F] [CharZero F] [DecidableEq F] (B : WeierstrassCurve F) [B.IsElliptic]
  (m : ℕ) [NeZero m]

omit [DecidableEq F] [B.IsElliptic] in
/-- PROVED (tex 3413–3417). The text's hypothesis `(m : F) ≠ 0` (`m = 2^a` invertible in `F`)
is automatic in characteristic zero. -/
theorem natCast_ne_zero_of_charZero : (m : F) ≠ 0 :=
  Nat.cast_ne_zero.2 (NeZero.ne m)

/-- PROVED (tex 3413–3417). Every point of `B(F)` has an `m`-th division point in `B(F̄)`. -/
theorem exists_divPt (P : B.toAffine.Point) : ∃ Q : PtAlg F B, m • Q = basePt F B P :=
  exists_nsmul_eq m _

/-- Definition (tex 3413–3417). A chosen `m`-th division point `Q ∈ B(F̄)` of `P ∈ B(F)`,
`m • Q = P`. -/
def divPt (P : B.toAffine.Point) : PtAlg F B :=
  Classical.choose (exists_divPt F B m P)

/-- PROVED (tex 3413–3417). `m • divPt P = P`. -/
theorem nsmul_divPt (P : B.toAffine.Point) : m • divPt F B m P = basePt F B P :=
  Classical.choose_spec (exists_divPt F B m P)

/-- PROVED (tex 3413–3417). The Kummer difference `σ Q − Q` is `m`-torsion (`P` is fixed by
`G_F`). -/
theorem smul_sub_divPt_mem (P : B.toAffine.Point) (σ : Field.absoluteGaloisGroup F) :
    σ • divPt F B m P - divPt F B m P ∈ AddSubgroup.torsionBy (PtAlg F B) (m : ℤ) := by
  rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, smul_comm, nsmul_divPt, smul_basePt, sub_self]

/-- Definition (tex 3417–3418, the Kummer map). The Kummer function `σ ↦ σ Q − Q ∈ B(F̄)[m]` of
`P ∈ B(F)`, for the chosen division point `Q = divPt P`. -/
def kummerFun (P : B.toAffine.Point) (σ : Field.absoluteGaloisGroup F) : TorsAlg F B m :=
  ⟨σ • divPt F B m P - divPt F B m P, smul_sub_divPt_mem F B m P σ⟩

/-- PROVED (tex 3417–3418). The value of the Kummer function. -/
@[simp]
theorem coe_kummerFun (P : B.toAffine.Point) (σ : Field.absoluteGaloisGroup F) :
    (kummerFun F B m P σ : PtAlg F B) = σ • divPt F B m P - divPt F B m P :=
  rfl

/-- PROVED (tex 3417–3418). The Kummer function is continuous (locally constant). -/
theorem continuous_kummerFun (P : B.toAffine.Point) : Continuous (kummerFun F B m P) :=
  Continuous.subtype_mk ((continuous_id.smul continuous_const).sub continuous_const) _

/-- PROVED (tex 3417–3418). The cocycle identity `κ(στ) = σ • κ(τ) + κ(σ)`. -/
theorem kummerFun_mul (P : B.toAffine.Point) (σ τ : Field.absoluteGaloisGroup F) :
    kummerFun F B m P (σ * τ) = σ • kummerFun F B m P τ + kummerFun F B m P σ := by
  apply Subtype.ext
  simp only [AddSubgroup.coe_add, coe_smul_torsAlg, coe_kummerFun, mul_smul, smul_sub]
  abel

/-- Definition (tex 3417–3418). **The Kummer cocycle** `κ_P ∈ C¹_cont(G_F, B(F̄)[m])`,
`σ ↦ σ Q − Q` with `m • Q = P`, a genuine continuous inhomogeneous `1`-cochain. -/
def kummerCocycle (P : B.toAffine.Point) :
    contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 :=
  ⟨(fun g => kummerFun F B m P (g 0) :
      (Fin 1 → Field.absoluteGaloisGroup F) → TorsAlg F B m),
    (continuous_kummerFun F B m P).comp (continuous_apply 0)⟩

/-- PROVED (tex 3417–3418). The value of the Kummer cocycle. -/
@[simp]
theorem cfun_kummerCocycle (P : B.toAffine.Point) (g : Fin 1 → Field.absoluteGaloisGroup F) :
    cfun (kummerCocycle F B m P) g = kummerFun F B m P (g 0) :=
  rfl

/-- PROVED (tex 3417–3418). **The Kummer cocycle is a cocycle**: `d¹ κ_P = 0`. -/
theorem kummerCocycle_isCocycle (P : B.toAffine.Point) :
    contD ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 (kummerCocycle F B m P) = 0 := by
  apply Subtype.ext
  funext g
  have h1 := contCochains_d_apply (k := ℤ) (G := Field.absoluteGaloisGroup F)
    (M := TorsAlg F B m) 1 (kummerCocycle F B m P) g
  refine h1.trans ?_
  rw [Fin.sum_univ_two]
  change g 0 • kummerFun F B m P (g 1) + ((-1 : ℤ) ^ ((0 : ℕ) + 1) •
    kummerFun F B m P (g 0 * g 1) + (-1 : ℤ) ^ ((1 : ℕ) + 1) • kummerFun F B m P (g 0)) = 0
  rw [kummerFun_mul]
  simp only [zero_add, pow_one, neg_one_smul, Nat.reduceAdd, even_two, Even.neg_pow, one_pow,
    one_smul]
  abel

/-- PROVED (tex 3417–3418). **The Kummer cocycle is additive up to a continuous coboundary**:
`κ_{P+P'} − κ_P − κ_{P'} = d⁰(T)` with `T = Q_{P+P'} − Q_P − Q_{P'} ∈ B(F̄)[m]`. -/
theorem kummerCocycle_add (P P' : B.toAffine.Point) :
    kummerCocycle F B m (P + P') - kummerCocycle F B m P - kummerCocycle F B m P' ∈
      contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) := by
  have hT : divPt F B m (P + P') - divPt F B m P - divPt F B m P' ∈
      AddSubgroup.torsionBy (PtAlg F B) (m : ℤ) := by
    rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, nsmul_sub, nsmul_divPt, nsmul_divPt,
      nsmul_divPt, map_add, sub_sub, sub_self]
  refine (mem_contB1_iff _).2 ⟨constCochain (⟨_, hT⟩ : TorsAlg F B m), ?_⟩
  apply Subtype.ext
  funext g
  refine (cfun_contD_constCochain (k := ℤ) (G := Field.absoluteGaloisGroup F)
    (M := TorsAlg F B m) _ g).trans ?_
  change _ = kummerFun F B m (P + P') (g 0) - kummerFun F B m P (g 0) - kummerFun F B m P' (g 0)
  apply Subtype.ext
  simp only [AddSubgroup.coe_sub, coe_smul_torsAlg, coe_kummerFun, smul_sub]
  abel

/-- PROVED (tex 3417–3418: the kernel of the Kummer map). **`κ_P` is a continuous coboundary iff
`P ∈ m B(F)`.** -/
theorem kummerCocycle_mem_coboundaries_iff (P : B.toAffine.Point) :
    kummerCocycle F B m P ∈ contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) ↔
      ∃ P' : B.toAffine.Point, m • P' = P := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := (mem_contB1_iff _).1 h
    have key : ∀ σ : Field.absoluteGaloisGroup F,
        σ • (divPt F B m P - ((cfun c default : TorsAlg F B m) : PtAlg F B)) =
          divPt F B m P - ((cfun c default : TorsAlg F B m) : PtAlg F B) := by
      intro σ
      have h1 : σ • (cfun c default : TorsAlg F B m) - cfun c default = kummerFun F B m P σ :=
        (contD_zero_apply (k := ℤ) (G := Field.absoluteGaloisGroup F) (M := TorsAlg F B m) c
          (fun _ => σ)).symm.trans (congrArg (fun f => cfun f (fun _ => σ)) hc)
      have h2 := congrArg Subtype.val h1
      simp only [AddSubgroup.coe_sub, coe_smul_torsAlg, coe_kummerFun] at h2
      rw [smul_sub, sub_eq_sub_iff_sub_eq_sub]
      exact h2.symm
    obtain ⟨P', hP'⟩ := exists_basePt_of_fixed key
    refine ⟨P', basePt_injective ?_⟩
    rw [map_nsmul, hP', nsmul_sub, nsmul_divPt,
      AddSubgroup.torsionBy.nsmul_iff.1 (cfun c default : TorsAlg F B m).2, sub_zero]
  · rintro ⟨P', rfl⟩
    have hT : divPt F B m (m • P') - basePt F B P' ∈ AddSubgroup.torsionBy (PtAlg F B) (m : ℤ) := by
      rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, nsmul_divPt, map_nsmul, sub_self]
    refine (mem_contB1_iff _).2 ⟨constCochain (⟨_, hT⟩ : TorsAlg F B m), ?_⟩
    apply Subtype.ext
    funext g
    refine (cfun_contD_constCochain (k := ℤ) (G := Field.absoluteGaloisGroup F)
      (M := TorsAlg F B m) _ g).trans ?_
    change _ = kummerFun F B m (m • P') (g 0)
    apply Subtype.ext
    simp only [AddSubgroup.coe_sub, coe_smul_torsAlg, coe_kummerFun, smul_sub, smul_basePt]
    abel

/-- PROVED (tex 3417–3418). The Kummer cocycle of a point of `m B(F)` (e.g. of `0`) is a
continuous coboundary. -/
theorem kummerCocycle_zero_mem :
    kummerCocycle F B m 0 ∈ contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) :=
  (kummerCocycle_mem_coboundaries_iff F B m 0).2 ⟨0, smul_zero _⟩

/-- Definition (tex 3417–3418). The Kummer map into `H¹`-level cochains,
`B(F) → C¹_cont(G_F, B(F̄)[m]) ⧸ B¹_cont`, `P ↦ [κ_P]`; additive by `kummerCocycle_add`. -/
def kummerToQuot :
    B.toAffine.Point →+
      (contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 ⧸
        contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m)) :=
  AddMonoidHom.mk' (fun P => Submodule.Quotient.mk (kummerCocycle F B m P)) fun P P' => by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq, ← sub_sub]
    exact kummerCocycle_add F B m P P'

/-- PROVED (tex 3417–3418). The value of `kummerToQuot`. -/
@[simp]
theorem kummerToQuot_apply (P : B.toAffine.Point) :
    kummerToQuot F B m P = Submodule.Quotient.mk (kummerCocycle F B m P) :=
  rfl

/-! ### The Kummer condition -/

/-- Definition (tex 3417–3418: the Kummer image). **The Kummer submodule**
`kummerZ F B m ⊆ C¹_cont(G_F, B(F̄)[m])`, the `ℤ`-span of the Kummer cocycles `κ_P`, `P ∈ B(F)`. -/
abbrev kummerZ :=
  cochainSpan (k := ℤ) (G := Field.absoluteGaloisGroup F) (M := TorsAlg F B m)
    (Set.range (kummerCocycle F B m))

/-- PROVED (tex 3417–3418). The Kummer submodule consists of cocycles. -/
theorem kummerZ_cocycle :
    ∀ z ∈ kummerZ F B m, contD ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 z = 0 :=
  cochainSpan_cocycle _ (by
    rintro _ ⟨P, rfl⟩
    exact kummerCocycle_isCocycle F B m P)

/-- PROVED (tex 3417–3418). Every element of the Kummer submodule is congruent modulo continuous
coboundaries to a single Kummer cocycle `κ_P`. -/
theorem exists_kummerToQuot_eq (z : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1)
    (hz : z ∈ kummerZ F B m) :
    ∃ P : B.toAffine.Point, kummerToQuot F B m P = Submodule.Quotient.mk z := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨P, rfl⟩ := hx
    exact ⟨P, rfl⟩
  | zero => exact ⟨0, by rw [map_zero, Submodule.Quotient.mk_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨P, hP⟩ := hx
    obtain ⟨P', hP'⟩ := hy
    exact ⟨P + P', by rw [map_add, hP, hP', Submodule.Quotient.mk_add]⟩
  | smul a x _ hx =>
    obtain ⟨P, hP⟩ := hx
    refine ⟨a • P, ?_⟩
    rw [map_zsmul, hP, Submodule.Quotient.mk_smul]
    exact (int_smul_eq_zsmul _ a _).symm

/-- Definition (tex 3413–3418; DEPARTURE of form, see `CocycleCondition.lean`). **The finite-level
local Kummer condition** `U = [C⁰_cont(G_F, B(F̄)[m]) --d⁰--> kummerZ ⊔ B¹_cont]`, the cocycle
condition of the Kummer submodule, a relation-indexed complex `GCx ℤ`. -/
abbrev kummerCondition : GCx ℤ :=
  cocycleCondition (kummerZ F B m) (kummerZ_cocycle F B m)

/-- Definition (tex 3413–3418, the local map `U_F → RΓ(F, B[m])`). The inclusion of the Kummer
condition into the genuine local complex `C^•_cont(G_F, B(F̄)[m])`. -/
abbrev kummerConditionι :
    GHom (kummerCondition F B m)
      (natCx (contCochains ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m))) :=
  cocycleConditionι (kummerZ F B m) (kummerZ_cocycle F B m)

/-- PROVED (tex 3413–3418). **The Kummer condition maps injectively into the local cochains**, in
every degree. -/
theorem kummerConditionι_injective (i : ℤ) :
    Function.Injective ((kummerConditionι F B m).f i i rfl) :=
  cocycleConditionι_injective _ _ i

/-- Definition (tex 3417–3418). The Kummer function `σ ↦ σ Q − Q` of an arbitrary `m`-th division
point `Q` of `P` (`m • Q = P`). -/
def kummerFunOf {P : B.toAffine.Point} {Q : PtAlg F B} (hQ : m • Q = basePt F B P)
    (σ : Field.absoluteGaloisGroup F) : TorsAlg F B m :=
  ⟨σ • Q - Q, by
    rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, smul_comm, hQ, smul_basePt, sub_self]⟩

/-- Definition (tex 3417–3418). The Kummer cocycle `σ ↦ σ Q − Q` of an arbitrary `m`-th division
point `Q` of `P`, a continuous `1`-cochain. -/
def kummerCocycleOf {P : B.toAffine.Point} {Q : PtAlg F B} (hQ : m • Q = basePt F B P) :
    contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 :=
  ⟨(fun g => kummerFunOf F B m hQ (g 0) :
      (Fin 1 → Field.absoluteGaloisGroup F) → TorsAlg F B m),
    (Continuous.subtype_mk ((continuous_id.smul continuous_const).sub continuous_const) _).comp
      (continuous_apply 0)⟩

/-- PROVED (tex 3417–3418). Two choices of division points give Kummer cocycles differing by a
continuous coboundary. -/
theorem kummerCocycleOf_sub_mem {P : B.toAffine.Point} {Q : PtAlg F B}
    (hQ : m • Q = basePt F B P) :
    kummerCocycleOf F B m hQ - kummerCocycle F B m P ∈
      contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) := by
  have hT : Q - divPt F B m P ∈ AddSubgroup.torsionBy (PtAlg F B) (m : ℤ) := by
    rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, hQ, nsmul_divPt, sub_self]
  refine (mem_contB1_iff _).2 ⟨constCochain (⟨_, hT⟩ : TorsAlg F B m), ?_⟩
  apply Subtype.ext
  funext g
  refine (cfun_contD_constCochain (k := ℤ) (G := Field.absoluteGaloisGroup F)
    (M := TorsAlg F B m) _ g).trans ?_
  change _ = kummerFunOf F B m hQ (g 0) - kummerFun F B m P (g 0)
  apply Subtype.ext
  change g 0 • (Q - divPt F B m P) - (Q - divPt F B m P) =
    (g 0 • Q - Q) - (g 0 • divPt F B m P - divPt F B m P)
  rw [smul_sub]
  abel

/-- PROVED (tex 3417–3418). **The Kummer condition does not depend on the chosen division
points**: the Kummer cocycle of any `m`-th division point of any `P ∈ B(F)` lies in
`U¹ = kummerZ ⊔ B¹_cont`. -/
theorem kummerCocycleOf_mem_sup {P : B.toAffine.Point} {Q : PtAlg F B}
    (hQ : m • Q = basePt F B P) :
    kummerCocycleOf F B m hQ ∈
      kummerZ F B m ⊔ contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) := by
  have h := Submodule.add_mem_sup (Submodule.subset_span ⟨P, rfl⟩ : kummerCocycle F B m P ∈
    kummerZ F B m) (kummerCocycleOf_sub_mem F B m hQ)
  rwa [add_sub_cancel] at h

/-! ### First cohomology of the Kummer condition: `B(F) ⧸ m B(F)` -/

/-- PROVED (tex 3417–3418). The Kummer cocycle `κ_P` lies in `U¹ = kummerZ ⊔ B¹`. -/
theorem kummerCocycle_mem_sup (P : B.toAffine.Point) :
    kummerCocycle F B m P ∈
      kummerZ F B m ⊔ contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨P, rfl⟩)

/-- Definition (tex 3417–3418). **The Kummer map into the first cohomology of the condition**,
`B(F) → U¹ ⧸ B¹`, `P ↦ [κ_P]`; additive by `kummerCocycle_add`. -/
def kummerH1Hom :
    B.toAffine.Point →+
      ((kummerCondition F B m).X 1 ⧸ condB1 (kummerZ F B m) (kummerZ_cocycle F B m)) :=
  AddMonoidHom.mk' (fun P => Submodule.Quotient.mk (ofCondOne (kummerZ F B m)
      (kummerZ_cocycle F B m) ⟨kummerCocycle F B m P, kummerCocycle_mem_sup F B m P⟩))
    fun P P' => by
      rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
      change kummerCocycle F B m (P + P') -
        (kummerCocycle F B m P + kummerCocycle F B m P') ∈
          contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m)
      rw [← sub_sub]
      exact kummerCocycle_add F B m P P'

/-- PROVED (tex 3417–3418). The value of `kummerH1Hom`. -/
theorem kummerH1Hom_apply (P : B.toAffine.Point) :
    kummerH1Hom F B m P = Submodule.Quotient.mk (ofCondOne (kummerZ F B m)
      (kummerZ_cocycle F B m) ⟨kummerCocycle F B m P, kummerCocycle_mem_sup F B m P⟩) :=
  rfl

/-- PROVED (tex 3417–3418). **The kernel of the Kummer map is `m B(F)`** (pointwise form). -/
theorem kummerH1Hom_eq_zero_iff (P : B.toAffine.Point) :
    kummerH1Hom F B m P = 0 ↔ ∃ P' : B.toAffine.Point, m • P' = P := by
  rw [← kummerCocycle_mem_coboundaries_iff]
  exact Submodule.Quotient.mk_eq_zero _

/-- PROVED (tex 3417–3418). **The kernel of the Kummer map is `m B(F)`.** -/
theorem kummerH1Hom_ker :
    (kummerH1Hom F B m).ker = (nsmulAddMonoidHom (α := B.toAffine.Point) m).range := by
  ext P
  rw [AddMonoidHom.mem_ker, kummerH1Hom_eq_zero_iff, AddMonoidHom.mem_range]
  rfl

/-- PROVED (tex 3417–3418: the Kummer image fills the condition). **The Kummer map onto the first
cohomology of the condition is surjective.** -/
theorem kummerH1Hom_surjective : Function.Surjective (kummerH1Hom F B m) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨z, hz, b, hb, hzb⟩ := Submodule.mem_sup.1 (condOne (kummerZ F B m)
    (kummerZ_cocycle F B m) x).2
  obtain ⟨P, hP⟩ := exists_kummerToQuot_eq F B m z hz
  refine ⟨P, ?_⟩
  rw [kummerH1Hom_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  change kummerCocycle F B m P - (condOne (kummerZ F B m) (kummerZ_cocycle F B m) x :
    contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1) ∈
      contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m)
  rw [← hzb, ← sub_sub]
  exact sub_mem ((Submodule.Quotient.eq _).1 hP) hb

/-- PROVED (tex 3415–3417: "`B(F)/2^aB(F)` in degree one", for any `m`). **`B(F) ⧸ m B(F)` is
the first cohomology `U¹ ⧸ B¹` of the Kummer condition**, via `P ↦ [κ_P]`. -/
def kummerH1Equiv :
    (B.toAffine.Point ⧸ (nsmulAddMonoidHom (α := B.toAffine.Point) m).range) ≃+
      ((kummerCondition F B m).X 1 ⧸ condB1 (kummerZ F B m) (kummerZ_cocycle F B m)) :=
  (QuotientAddGroup.quotientAddEquivOfEq (kummerH1Hom_ker F B m).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (kummerH1Hom_surjective F B m))

/-- PROVED (tex 3417–3418). `kummerH1Equiv` sends the class of `P` to the class of `κ_P`. -/
theorem kummerH1Equiv_mk (P : B.toAffine.Point) :
    kummerH1Equiv F B m (QuotientAddGroup.mk P) = kummerH1Hom F B m P :=
  rfl

/-- PROVED (tex 3415–3417). **`H¹` of the Kummer condition is `B(F) ⧸ m B(F)`**: an isomorphism
between `B(F) ⧸ m B(F)` and Mathlib's homology `H¹((kummerCondition F B m).toCC)`. -/
def kummerH1AddEquiv :
    (B.toAffine.Point ⧸ (nsmulAddMonoidHom (α := B.toAffine.Point) m).range) ≃+
      ((kummerCondition F B m).toCC.homology 1) :=
  (kummerH1Equiv F B m).trans
    (cocycleConditionH1Iso (kummerZ F B m) (kummerZ_cocycle F B m)).toLinearEquiv.toAddEquiv.symm

/-- PROVED (tex 3417–3418: the Kummer image inside the local cohomology). The first cohomology of
the Kummer condition injects into the first cohomology of the genuine local complex
`C^•_cont(G_F, B(F̄)[m])` (instance of `cocycleCondition_mono_homologyMap_one`). -/
theorem kummerCondition_mono_homologyMap_one :
    Mono (HomologicalComplex.homologyMap (GHom.toCC (kummerConditionι F B m)) 1) :=
  cocycleCondition_mono_homologyMap_one (kummerZ F B m) (kummerZ_cocycle F B m)

/-- Definition (tex 3417–3418, 3442–3445: the Kummer map). **The Kummer map**
`B(F) ⧸ m B(F) → H¹(C^•_cont(G_F, B(F̄)[m]))` into the first cohomology of the genuine local
complex, `[P] ↦ [κ_P]`. -/
def kummerMapH1 :
    (B.toAffine.Point ⧸ (nsmulAddMonoidHom (α := B.toAffine.Point) m).range) →+
      ((natCx (contCochains ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m))).toCC.homology 1) :=
  (HomologicalComplex.homologyMap (GHom.toCC (kummerConditionι F B m)) 1).hom.toAddMonoidHom.comp
    (kummerH1AddEquiv F B m).toAddMonoidHom

/-- PROVED (tex 3417–3418). **The Kummer map `B(F) ⧸ m B(F) → H¹(G_F, B(F̄)[m])` is injective**
(genuine continuous cohomology). -/
theorem kummerMapH1_injective : Function.Injective (kummerMapH1 F B m) :=
  ((ModuleCat.mono_iff_injective _).1 (kummerCondition_mono_homologyMap_one F B m)).comp
    (kummerH1AddEquiv F B m).injective

/-- PROVED (tex 3417–3418, 3442–3445). **The Kummer map sends `[P]` to the cohomology class of the
Kummer cocycle**: `kummerMapH1 [P] = π(c)` for the `1`-cycle `c` of the genuine local complex
`C^•_cont(G_F, B(F̄)[m])` with underlying cochain `κ_P`. -/
theorem kummerMapH1_mk (P : B.toAffine.Point) :
    ∃ c : (natCx (contCochains ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m))).toCC.cycles 1,
      ((natCx (contCochains ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m))).toCC.iCycles 1).hom
          c = kummerCocycle F B m P ∧
      kummerMapH1 F B m (QuotientAddGroup.mk P) =
        ((natCx (contCochains ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m))).toCC.homologyπ
          1).hom c :=
  cocycleCondition_homologyMap_inv_mk (kummerZ F B m) (kummerZ_cocycle F B m)
    (ofCondOne (kummerZ F B m) (kummerZ_cocycle F B m)
      ⟨kummerCocycle F B m P, kummerCocycle_mem_sup F B m P⟩)

/-! ### Zeroth cohomology of the Kummer condition: `B(F)[m]` -/

/-- PROVED (tex 3415–3417, degree zero). The Kummer condition has the `H⁰` of the genuine local
complex `C^•_cont(G_F, B(F̄)[m])` (instance of `cocycleCondition_isIso_homologyMap_zero`). -/
theorem kummerCondition_isIso_homologyMap_zero :
    IsIso (HomologicalComplex.homologyMap (GHom.toCC (kummerConditionι F B m)) 0) :=
  cocycleCondition_isIso_homologyMap_zero (kummerZ F B m) (kummerZ_cocycle F B m)

/-- PROVED (tex 3415–3417). The constant `0`-cochain at a point of `B(F)[m]` is a `0`-cocycle of
the Kummer condition. -/
theorem kummerH0_mem (T : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ)) :
    ofCondZero (kummerZ F B m) (kummerZ_cocycle F B m) (constCochain (baseTors F B m T)) ∈
      LinearMap.ker ((kummerCondition F B m).toCC.sc' (-1) 0 1).g.hom := by
  change ((kummerCondition F B m).toCC.d 0 1).hom (ofCondZero (kummerZ F B m)
    (kummerZ_cocycle F B m) (constCochain (baseTors F B m T))) = 0
  refine (cocycleCondition_toCC_d₀_eq_zero_iff (kummerZ F B m) (kummerZ_cocycle F B m) _).2 ?_
  apply Subtype.ext
  funext g
  refine (cfun_contD_constCochain (k := ℤ) (G := Field.absoluteGaloisGroup F)
    (M := TorsAlg F B m) _ g).trans ?_
  rw [smul_baseTors, sub_self]
  rfl

/-- Definition (tex 3415–3417). The map `B(F)[m] → H⁰(U)` (the `0`-cocycles of the Kummer
condition), `T ↦` the constant `0`-cochain at `T`. -/
def kummerH0Hom : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ) →+
    ↥(LinearMap.ker ((kummerCondition F B m).toCC.sc' (-1) 0 1).g.hom) :=
  AddMonoidHom.mk' (fun T => ⟨ofCondZero (kummerZ F B m) (kummerZ_cocycle F B m)
      (constCochain (baseTors F B m T)), kummerH0_mem F B m T⟩)
    fun T T' => by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      funext x
      exact map_add (baseTors F B m) T T'

/-- PROVED (tex 3415–3417). The value of `kummerH0Hom` at the point of `G⁰`. -/
theorem kummerH0Hom_apply (T : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ)) :
    cfun (condZero (kummerZ F B m) (kummerZ_cocycle F B m) (kummerH0Hom F B m T).1 :
      contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 0) default = baseTors F B m T :=
  rfl

/-- PROVED (tex 3415–3417). `kummerH0Hom` is injective. -/
theorem kummerH0Hom_injective : Function.Injective (kummerH0Hom F B m) := by
  intro T T' h
  apply baseTors_injective (F := F) (B := B) m
  rw [← kummerH0Hom_apply F B m T, ← kummerH0Hom_apply F B m T', h]

/-- PROVED (tex 3415–3417: the degree-zero torsion; Galois descent). `kummerH0Hom` is surjective:
every `0`-cocycle is the constant cochain at a `G_F`-invariant point of `B(F̄)[m]`, i.e. at a
point of `B(F)[m]`. -/
theorem kummerH0Hom_surjective : Function.Surjective (kummerH0Hom F B m) := by
  rintro ⟨x, hx⟩
  have hx' : ((kummerCondition F B m).toCC.d 0 1).hom x = 0 := hx
  have hc := (cocycleCondition_toCC_d₀_eq_zero_iff (kummerZ F B m) (kummerZ_cocycle F B m) x).1 hx'
  set c : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 0 :=
    (condZero (kummerZ F B m) (kummerZ_cocycle F B m) x).1 with hcdef
  have hfix : ∀ σ : Field.absoluteGaloisGroup F,
      σ • (cfun c default : TorsAlg F B m) = cfun c default := by
    intro σ
    have h1 := (contD_zero_apply (k := ℤ) (G := Field.absoluteGaloisGroup F) (M := TorsAlg F B m) c
      (fun _ => σ)).symm.trans (congrArg (fun f => cfun f (fun _ => σ)) hc)
    exact sub_eq_zero.1 h1
  obtain ⟨T, hT⟩ := exists_baseTors_of_fixed hfix
  refine ⟨T, Subtype.ext ?_⟩
  change ofCondZero (kummerZ F B m) (kummerZ_cocycle F B m) (constCochain (baseTors F B m T)) = x
  rw [hT, ← eq_constCochain c]
  rfl

/-- PROVED (tex 3415–3417). `B(F)[m]` is the group of `0`-cocycles of the Kummer condition. -/
def kummerH0Equiv : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ) ≃+
    ↥(LinearMap.ker ((kummerCondition F B m).toCC.sc' (-1) 0 1).g.hom) :=
  AddEquiv.ofBijective (kummerH0Hom F B m)
    ⟨kummerH0Hom_injective F B m, kummerH0Hom_surjective F B m⟩

/-- PROVED (tex 3415–3417: "`B(F)[2^a]` in degree zero", for any `m`). **`H⁰` of the Kummer
condition is `B(F)[m]`**: an isomorphism between `B(F)[m]` and Mathlib's homology
`H⁰((kummerCondition F B m).toCC)`. -/
def kummerH0AddEquiv : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ) ≃+
    ((kummerCondition F B m).toCC.homology 0) :=
  (kummerH0Equiv F B m).trans
    (cocycleConditionH0Iso (kummerZ F B m) (kummerZ_cocycle F B m)).toLinearEquiv.toAddEquiv.symm

end KummerCocycle

/-! ### Coefficient extension -/

section CoefficientExtension

variable {F : Type} [Field F] [CharZero F] [DecidableEq F] {B : WeierstrassCurve F} [B.IsElliptic]
  {m : ℕ} [NeZero m]
  {k : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (Field.absoluteGaloisGroup F) M]
  (ι : TorsAlg F B m →+ M)

/-- Definition (tex 3430–3438: "derived coefficient extension defines the scalar `A_i`
condition"). The extended Kummer cochain `g ↦ a • ι(κ_P(g))` in `C¹_cont(G_F, M)`, for a scalar
`a : k` and an additive map `ι : B(F̄)[m] → M` into a discrete `k[G_F]`-module. -/
def kummerCocycleIn (a : k) (P : B.toAffine.Point) :
    contCochain k (Field.absoluteGaloisGroup F) M 1 :=
  ⟨(fun g => a • ι (kummerFun F B m P (g 0)) : (Fin 1 → Field.absoluteGaloisGroup F) → M),
    (continuous_of_discreteTopology (f := fun t : TorsAlg F B m => a • ι t)).comp
      ((continuous_kummerFun F B m P).comp (continuous_apply 0))⟩

omit [ContinuousSMul (Field.absoluteGaloisGroup F) M] in
/-- PROVED (tex 3430–3438). The value of the extended Kummer cochain. -/
@[simp]
theorem cfun_kummerCocycleIn (a : k) (P : B.toAffine.Point)
    (g : Fin 1 → Field.absoluteGaloisGroup F) :
    cfun (kummerCocycleIn ι a P) g = a • ι (kummerFun F B m P (g 0)) :=
  rfl

omit [ContinuousSMul (Field.absoluteGaloisGroup F) M] in
/-- PROVED (tex 3430–3438). `g ↦ a • ι(κ_P(g))` is `a` times `g ↦ ι(κ_P(g))`. -/
theorem kummerCocycleIn_eq_smul (a : k) (P : B.toAffine.Point) :
    kummerCocycleIn ι a P = a • kummerCocycleIn ι 1 P := by
  apply Subtype.ext
  funext g
  change a • ι (kummerFun F B m P (g 0)) = a • (1 : k) • ι (kummerFun F B m P (g 0))
  rw [one_smul]

/-- PROVED (tex 3430–3438). **The extended Kummer cochains are cocycles**, for `ι` equivariant
(`ι (σ • t) = σ • ι t`). -/
theorem kummerCocycleIn_isCocycle
    (hι : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (σ • t) = σ • ι t)
    (a : k) (P : B.toAffine.Point) :
    contD k (Field.absoluteGaloisGroup F) M 1 (kummerCocycleIn ι a P) = 0 := by
  apply Subtype.ext
  funext g
  have h1 := contCochains_d_apply (k := k) (G := Field.absoluteGaloisGroup F) (M := M) 1
    (kummerCocycleIn ι a P) g
  refine h1.trans ?_
  rw [Fin.sum_univ_two]
  change g 0 • (a • ι (kummerFun F B m P (g 1))) + ((-1 : k) ^ ((0 : ℕ) + 1) •
    (a • ι (kummerFun F B m P (g 0 * g 1))) + (-1 : k) ^ ((1 : ℕ) + 1) •
      (a • ι (kummerFun F B m P (g 0)))) = 0
  rw [kummerFun_mul, map_add, hι, smul_add, smul_comm (g 0) a]
  simp only [zero_add, pow_one, neg_one_smul, Nat.reduceAdd, even_two, Even.neg_pow, one_pow,
    one_smul]
  abel

variable (k) in
/-- Definition (tex 3430–3438). **The extended Kummer submodule** `kummerZ' k ι ⊆ C¹_cont(G_F, M)`:
the `k`-span of the cocycles `g ↦ a • ι(κ_P(g))`, `a : k`, `P ∈ B(F)`. -/
abbrev kummerZ' : Submodule k (contCochain k (Field.absoluteGaloisGroup F) M 1) :=
  cochainSpan (Set.range fun p : k × B.toAffine.Point => kummerCocycleIn ι p.1 p.2)

omit [ContinuousSMul (Field.absoluteGaloisGroup F) M] in
/-- PROVED (tex 3430–3438). The extended Kummer cochains lie in `kummerZ' k ι`. -/
theorem kummerCocycleIn_mem (a : k) (P : B.toAffine.Point) :
    kummerCocycleIn ι a P ∈ kummerZ' k ι :=
  Submodule.subset_span ⟨(a, P), rfl⟩

variable (k) in
/-- PROVED (tex 3430–3438). The extended Kummer submodule consists of cocycles. -/
theorem kummerZ'_cocycle
    (hι : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (σ • t) = σ • ι t) :
    ∀ z ∈ kummerZ' k ι, contD k (Field.absoluteGaloisGroup F) M 1 z = 0 :=
  cochainSpan_cocycle _ (by
    rintro _ ⟨p, rfl⟩
    exact kummerCocycleIn_isCocycle ι hι p.1 p.2)

variable (k) in
/-- Definition (tex 3430–3438; DEPARTURE of form as in `CocycleCondition.lean`). **The Kummer
condition with coefficients extended along `ι`**:
`[C⁰_cont(G_F, M) --d⁰--> kummerZ' k ι ⊔ B¹_cont(G_F, M)]`, a relation-indexed complex `GCx k`. -/
abbrev kummerConditionIn
    (hι : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (σ • t) = σ • ι t) : GCx k :=
  cocycleCondition (kummerZ' k ι) (kummerZ'_cocycle k ι hι)

variable (k) in
/-- Definition (tex 3430–3438). The inclusion of the extended Kummer condition into the genuine
local complex `natCx (contCochains k G_F M)`. -/
abbrev kummerConditionInι
    (hι : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (σ • t) = σ • ι t) :
    GHom (kummerConditionIn k ι hι) (natCx (contCochains k (Field.absoluteGaloisGroup F) M)) :=
  cocycleConditionι (kummerZ' k ι) (kummerZ'_cocycle k ι hι)

variable (k) in
/-- PROVED (tex 3430–3438). **The extended Kummer condition maps injectively into the local
cochains**, in every degree. -/
theorem kummerConditionInι_injective
    (hι : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (σ • t) = σ • ι t) (i : ℤ) :
    Function.Injective ((kummerConditionInι k ι hι).f i i rfl) :=
  cocycleConditionι_injective (kummerZ' k ι) (kummerZ'_cocycle k ι hι) i

variable (k) in
/-- PROVED (tex 3430–3438). `H¹` of the extended Kummer condition is `(kummerZ' k ι ⊔ B¹) ⧸ B¹`
(an instance of `cocycleConditionH1Iso`). -/
def kummerConditionInH1Iso
    (hι : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (σ • t) = σ • ι t) :
    (kummerConditionIn k ι hι).toCC.homology 1 ≅
      ModuleCat.of k ((kummerConditionIn k ι hι).X 1 ⧸
        condB1 (kummerZ' k ι) (kummerZ'_cocycle k ι hι)) :=
  cocycleConditionH1Iso (kummerZ' k ι) (kummerZ'_cocycle k ι hι)

variable (k) in
/-- PROVED (tex 3430–3438). The extended Kummer condition has the `H⁰` of the full local complex
(an instance of `cocycleCondition_isIso_homologyMap_zero`). -/
theorem kummerConditionIn_isIso_homologyMap_zero
    (hι : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (σ • t) = σ • ι t) :
    IsIso (HomologicalComplex.homologyMap (GHom.toCC (kummerConditionInι k ι hι)) 0) :=
  cocycleCondition_isIso_homologyMap_zero (kummerZ' k ι) (kummerZ'_cocycle k ι hι)

end CoefficientExtension

/-! ### Genuine local conditions -/

/-- Definition (tex 3413–3468 with (4.3) at tex 3455–3463: "These are the local maps used in the
Selmer-cone duality above"). **Kummer local conditions** in the format `LocalConditions` of the
genuine Selmer data (`SelmerComplex/Selmer.lean`): for local fields `F_v` of characteristic zero
with elliptic curves `B_v`, the local groups `G_{F_v}` with continuous homomorphisms
`loc_v : G_{F_v} → G_S`, a discrete `k[G_S]`-module `M` and `G_{F_v}`-equivariant additive maps
`ι_v : B_v(F̄_v)[m] → M` (`M` with the action through `loc_v`, `ResMod (loc v) M`), the local
conditions are `U_v = kummerConditionIn k ι_v _` with their inclusions into the genuine local
complexes `C^•_cont(G_{F_v}, M)`. -/
def kummerLocalConditions {GS : Type} [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
    {V : Type} (Fv : V → Type) [∀ v, Field (Fv v)] [∀ v, CharZero (Fv v)]
    [∀ v, DecidableEq (Fv v)] (Bv : ∀ v, WeierstrassCurve (Fv v)) [∀ v, (Bv v).IsElliptic]
    (m : ℕ) [NeZero m] (loc : ∀ v, Field.absoluteGaloisGroup (Fv v) →ₜ* GS)
    (k : Type) [CommRing k] (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction GS M]
    [SMulCommClass GS k M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul GS M]
    (ι : ∀ v, TorsAlg (Fv v) (Bv v) m →+ ResMod (loc v) M)
    (hι : ∀ v (σ : Field.absoluteGaloisGroup (Fv v)) (t : TorsAlg (Fv v) (Bv v) m),
      ι v (σ • t) = σ • ι v t) :
    LocalConditions k GS (fun v => Field.absoluteGaloisGroup (Fv v)) loc M :=
  ⟨fun v => kummerConditionIn k (ι v) (hι v), fun v => kummerConditionInι k (ι v) (hι v)⟩

/-- PROVED (tex 3413–3468). The local condition complexes of `kummerLocalConditions` are the
extended Kummer conditions. -/
theorem kummerLocalConditions_U {GS : Type} [Group GS] [TopologicalSpace GS]
    [IsTopologicalGroup GS] {V : Type} (Fv : V → Type) [∀ v, Field (Fv v)] [∀ v, CharZero (Fv v)]
    [∀ v, DecidableEq (Fv v)] (Bv : ∀ v, WeierstrassCurve (Fv v)) [∀ v, (Bv v).IsElliptic]
    (m : ℕ) [NeZero m] (loc : ∀ v, Field.absoluteGaloisGroup (Fv v) →ₜ* GS)
    (k : Type) [CommRing k] (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction GS M]
    [SMulCommClass GS k M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul GS M]
    (ι : ∀ v, TorsAlg (Fv v) (Bv v) m →+ ResMod (loc v) M)
    (hι : ∀ v (σ : Field.absoluteGaloisGroup (Fv v)) (t : TorsAlg (Fv v) (Bv v) m),
      ι v (σ • t) = σ • ι v t) (v : V) :
    (kummerLocalConditions Fv Bv m loc k M ι hι).U v = kummerConditionIn k (ι v) (hι v) :=
  rfl

/-- Definition (tex 3413–3468 with (4.3) at tex 3455–3463). **Kummer local conditions for the
genuine Galois Selmer data** of a number field `K` and a set `S` of finite primes: at `v ∈ S` the
local field `K_v = v.adicCompletion K` (characteristic zero), an elliptic curve `B_v` over `K_v`,
and a `G_{K_v}`-equivariant additive map `ι_v : B_v(K̄_v)[m] → M` into a discrete
`k[G_{K,S}]`-module `M` (with `G_{K_v}` acting through the localization `locMap K S v`); this
specializes `kummerLocalConditions` to lane RC26's `Gloc K v = G_{K_v}`. -/
def kummerGaloisLocalConditions (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)]
    (B : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
    (m : ℕ) [NeZero m] (k : Type) [CommRing k] (M : Type) [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
    (ι : ∀ v : Places K S, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M)
    (hι : ∀ v (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ι v (σ • t) = σ • ι v t) :
    GaloisLocalConditions K S k M :=
  kummerLocalConditions (fun v : Places K S => v.1.adicCompletion K) B m
    (fun v => locMap K S v.1) k M ι hι

/-- PROVED (tex 3413–3468). The Kummer local conditions of the genuine Galois Selmer data are
injective in every degree at every place. -/
theorem kummerGaloisLocalConditions_injective (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)]
    (B : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
    (m : ℕ) [NeZero m] (k : Type) [CommRing k] (M : Type) [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
    (ι : ∀ v : Places K S, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M)
    (hι : ∀ v (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ι v (σ • t) = σ • ι v t) (v : Places K S) (n : ℤ) :
    Function.Injective (((kummerGaloisLocalConditions K S B m k M ι hι).i v).f n n rfl) :=
  kummerConditionInι_injective k (ι v) (hι v) n

/-- PROVED (tex 3455–3463, (4.3)). The genuine Selmer data with the Kummer local conditions
(`galoisSelData` of lane RC26); its Selmer complex is `selCx` of these data. -/
example (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)]
    (B : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
    (m : ℕ) [NeZero m] (k : Type) [CommRing k] (M : Type) [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
    (ι : ∀ v : Places K S, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M)
    (hι : ∀ v (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ι v (σ • t) = σ • ι v t) : SelData k :=
  galoisSelData K S k M (kummerGaloisLocalConditions K S B m k M ι hι)

/-- PROVED (tex 3430–3438). For the identity coefficients (`k = ℤ`, `M = B(F̄)[m]`, `ι = id`,
`a = 1`) the extended Kummer cochain is the Kummer cocycle. -/
theorem kummerCocycleIn_id {F : Type} [Field F] [CharZero F] [DecidableEq F]
    {B : WeierstrassCurve F} [B.IsElliptic] {m : ℕ} [NeZero m] (P : B.toAffine.Point) :
    kummerCocycleIn (AddMonoidHom.id (TorsAlg F B m)) (1 : ℤ) P = kummerCocycle F B m P := by
  apply Subtype.ext
  funext g
  exact one_smul ℤ (kummerFun F B m P (g 0))

/-- PROVED (tex 3430–3438). For the identity coefficients the extended Kummer submodule is the
Kummer submodule. -/
theorem kummerZ'_id {F : Type} [Field F] [CharZero F] [DecidableEq F]
    {B : WeierstrassCurve F} [B.IsElliptic] {m : ℕ} [NeZero m] :
    kummerZ' ℤ (AddMonoidHom.id (TorsAlg F B m)) = kummerZ F B m := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨a, P⟩, rfl⟩
    change kummerCocycleIn (AddMonoidHom.id (TorsAlg F B m)) a P ∈ kummerZ F B m
    rw [kummerCocycleIn_eq_smul, kummerCocycleIn_id]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨P, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨P, rfl⟩
    rw [← kummerCocycleIn_id]
    exact kummerCocycleIn_mem _ 1 P

/-- PROVED (tex 3430–3438). For the identity coefficients the extended Kummer condition is the
Kummer condition. -/
theorem kummerConditionIn_id {F : Type} [Field F] [CharZero F] [DecidableEq F]
    {B : WeierstrassCurve F} [B.IsElliptic] {m : ℕ} [NeZero m] :
    kummerConditionIn ℤ (AddMonoidHom.id (TorsAlg F B m)) (fun _ _ => rfl) =
      kummerCondition F B m := by
  unfold kummerConditionIn kummerCondition
  congr 1
  exact kummerZ'_id

/-! ### Non-vacuity: `y² = x³ − x` over `ℚ`, `m = 2` -/

section Example

/-- Definition (non-vacuity of the hypotheses of tex 3413–3468). The elliptic curve
`y² = x³ − x` over `ℚ`. -/
def curveY2X3mX : WeierstrassCurve ℚ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -1, a₆ := 0 }

/-- PROVED (non-vacuity of the hypotheses of tex 3413–3468). `y² = x³ − x` is elliptic
(`Δ = 64`). -/
instance curveY2X3mX.instIsElliptic : curveY2X3mX.IsElliptic :=
  ⟨by
    rw [isUnit_iff_ne_zero]
    norm_num [curveY2X3mX, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]⟩

/-- PROVED (non-vacuity of the hypotheses of tex 3413–3468). `(0, 0)` is a nonsingular point of
`y² = x³ − x`. -/
theorem curveY2X3mX_nonsingular : curveY2X3mX.toAffine.Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  norm_num [curveY2X3mX, WeierstrassCurve.Affine.equation_iff']

/-- Definition (non-vacuity of the hypotheses of tex 3413–3468). The rational `2`-torsion point
`(0, 0)` of `y² = x³ − x`. -/
def curveY2X3mXPt : AddSubgroup.torsionBy curveY2X3mX.toAffine.Point ((2 : ℕ) : ℤ) :=
  ⟨.some 0 0 curveY2X3mX_nonsingular, by
    rw [AddSubgroup.torsionBy.nsmul_iff, two_nsmul]
    exact Affine.Point.add_self_of_Y_eq (by
      norm_num [curveY2X3mX, WeierstrassCurve.Affine.negY])⟩

/-- PROVED (non-vacuity of the hypotheses of tex 3413–3468). The Kummer condition of
`y² = x³ − x` over `ℚ` with `m = 2` (all hypotheses `CharZero ℚ`, `IsElliptic`, `NeZero 2` are
satisfied). -/
example : GCx ℤ := kummerCondition ℚ curveY2X3mX 2

/-- PROVED (non-vacuity of the hypotheses of tex 3413–3468). Its injective map into
`C^•_cont(G_ℚ, B(ℚ̄)[2])`. -/
example : GHom (kummerCondition ℚ curveY2X3mX 2)
    (natCx (contCochains ℤ (Field.absoluteGaloisGroup ℚ) (TorsAlg ℚ curveY2X3mX 2))) :=
  kummerConditionι ℚ curveY2X3mX 2

/-- PROVED (non-vacuity of the hypotheses of tex 3413–3468). `H¹ ≅ B(ℚ)/2B(ℚ)` for
`y² = x³ − x`. -/
example : (curveY2X3mX.toAffine.Point ⧸
      (nsmulAddMonoidHom (α := curveY2X3mX.toAffine.Point) 2).range) ≃+
    ((kummerCondition ℚ curveY2X3mX 2).toCC.homology 1) :=
  kummerH1AddEquiv ℚ curveY2X3mX 2

/-- PROVED (non-vacuity of the hypotheses of tex 3413–3468). `H⁰` of the Kummer condition of
`y² = x³ − x`, `m = 2`, is nonzero: it contains the class of the rational `2`-torsion point
`(0, 0)`. -/
theorem kummerCondition_curveY2X3mX_H0_nontrivial :
    Nontrivial ((kummerCondition ℚ curveY2X3mX 2).toCC.homology 0) := by
  refine ⟨⟨kummerH0AddEquiv ℚ curveY2X3mX 2 curveY2X3mXPt, 0, fun h => ?_⟩⟩
  have h' := (kummerH0AddEquiv ℚ curveY2X3mX 2).injective
    (h.trans (map_zero (kummerH0AddEquiv ℚ curveY2X3mX 2)).symm)
  exact Affine.Point.some_ne_zero curveY2X3mX_nonsingular (congrArg Subtype.val h')

/-- PROVED (non-vacuity of the coefficient-extension hypotheses, tex 3430–3438). The identity
coefficients `ι = id : B(ℚ̄)[2] → B(ℚ̄)[2]` (over `k = ℤ`) satisfy the equivariance hypothesis,
giving an extended Kummer condition. -/
example : GCx ℤ :=
  kummerConditionIn ℤ (AddMonoidHom.id (TorsAlg ℚ curveY2X3mX 2)) (fun _ _ => rfl)

end Example

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive.LocalKummer

set_option backward.isDefEq.respectTransparency false

open scoped Classical

/-! ## Formal residual models of Selmer data over a field -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open CategoryTheory CategoryTheory.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Manuscript.RC.SelmerComplex

section HomologyModel

variable {k : Type} [Field k]

/-- The cohomology of a complex, with zero differentials. -/
def homologyModel (C : CochainComplex (ModuleCat.{0} k) ℤ) : GCx k where
  X n := C.homology n
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

theorem homologyModel_d (C : CochainComplex (ModuleCat.{0} k) ℤ)
    (i j : ℤ) : (homologyModel C).toCC.d i j = 0 := by
  dsimp [GCx.toCC, homologyModel]
  split_ifs <;> rfl

/-- A linear section of the projection from cycles to cohomology. -/
def cycleSection (C : CochainComplex (ModuleCat.{0} k) ℤ) (n : ℤ) :
    C.homology n ⟶ C.cycles n :=
  Projective.factorThru (𝟙 (C.homology n)) (C.homologyπ n)

theorem cycleSection_π (C : CochainComplex (ModuleCat.{0} k) ℤ) (n : ℤ) :
    cycleSection C n ≫ C.homologyπ n = 𝟙 _ :=
  Projective.factorThru_comp _ _

/-- The cochain map choosing linear representatives of classes. -/
def homologyModelTo (C : CochainComplex (ModuleCat.{0} k) ℤ) :
    (homologyModel C).toCC ⟶ C where
  f n := cycleSection C n ≫ C.iCycles n
  comm' i j _ := by
    rw [homologyModel_d, zero_comp, Category.assoc, HomologicalComplex.iCycles_d, comp_zero]

/-- Field-valued formality: the representative map is a quasi-isomorphism. -/
theorem homologyModelTo_quasiIso (C : CochainComplex (ModuleCat.{0} k) ℤ) :
    QuasiIso (homologyModelTo C) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := (homologyModel C).toCC
  have : IsIso (H.iCycles n) :=
    H.isIso_iCycles n (n + 1) (by simp) (homologyModel_d C n (n + 1))
  have : IsIso (H.homologyπ n) :=
    H.isIso_homologyπ (n - 1) n (by simp) (homologyModel_d C (n - 1) n)
  have hcyc : HomologicalComplex.cyclesMap (homologyModelTo C) n =
      H.iCycles n ≫ cycleSection C n := by
    apply (cancel_mono (C.iCycles n)).1
    rw [HomologicalComplex.cyclesMap_i, Category.assoc]
    rfl
  have hmap : H.homologyπ n ≫
      HomologicalComplex.homologyMap (homologyModelTo C) n = H.iCycles n := by
    rw [HomologicalComplex.homologyπ_naturality, hcyc, Category.assoc, cycleSection_π]
    rfl
  have : IsIso (H.homologyπ n ≫
      HomologicalComplex.homologyMap (homologyModelTo C) n) := by
    rw [hmap]
    infer_instance
  exact IsIso.of_isIso_comp_left (H.homologyπ n) _

/-- A cochain map and the map it induces on cohomology agree up to a boundary: the difference
of the two composites `H(X) → Y` is `d ∘ h` for a linear `h`. -/
theorem exists_htpy {X Y : CochainComplex (ModuleCat.{0} k) ℤ} (f : X ⟶ Y) (n : ℤ) :
    ∃ h : X.homology n ⟶ Y.X (n - 1), h ≫ Y.d (n - 1) n =
      ((homologyModelTo X).f n ≫ f.f n : X.homology n ⟶ Y.X n) -
        HomologicalComplex.homologyMap f n ≫ (homologyModelTo Y).f n := by
  let S : ShortComplex (ModuleCat.{0} k) :=
    ShortComplex.mk (Y.toCycles (n - 1) n) (Y.homologyπ n) (Y.toCycles_comp_homologyπ (n - 1) n)
  have hS : S.Exact := S.exact_of_g_is_cokernel (Y.homologyIsCokernel (n - 1) n (by simp))
  let φ : X.homology n ⟶ Y.cycles n := cycleSection X n ≫ HomologicalComplex.cyclesMap f n -
    HomologicalComplex.homologyMap f n ≫ cycleSection Y n
  have hφ : φ ≫ S.g = 0 := by
    change (cycleSection X n ≫ HomologicalComplex.cyclesMap f n -
      HomologicalComplex.homologyMap f n ≫ cycleSection Y n) ≫ Y.homologyπ n = 0
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc,
      ← HomologicalComplex.homologyπ_naturality, cycleSection_π, ← Category.assoc,
      cycleSection_π, Category.id_comp, Category.comp_id, sub_self]
  refine ⟨hS.liftFromProjective φ hφ, ?_⟩
  have h1 : hS.liftFromProjective φ hφ ≫ Y.toCycles (n - 1) n = φ :=
    hS.liftFromProjective_comp φ hφ
  rw [← HomologicalComplex.toCycles_i, ← Category.assoc, h1]
  simp only [φ, homologyModelTo, Preadditive.sub_comp, Category.assoc,
    HomologicalComplex.cyclesMap_i]

end HomologyModel

section Relation

variable {k : Type} [Field k]

/-- A Mathlib cochain map between the Mathlib forms of two complexes, relation-indexed. -/
def ghomOfCC {A B : GCx k} (φ : A.toCC ⟶ B.toCC) : GHom A B where
  f i j h := by subst h; exact (φ.f i).hom
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    have e := congrArg (fun g => g.hom x) (φ.comm i i₁)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    rw [GCx.toCC_d_hom A i i₁ h₁, GCx.toCC_d_hom B i i₁ h₂] at e
    exact e.symm

theorem toCC_ghomOfCC {A B : GCx k} (φ : A.toCC ⟶ B.toCC) : GHom.toCC (ghomOfCC φ) = φ := by
  ext i x
  rfl

/-- The cohomology model of a relation-indexed complex. -/
abbrev hm (X : GCx k) : GCx k := homologyModel X.toCC

/-- The chosen cochain representatives of cohomology classes. -/
def sec (X : GCx k) : GHom (hm X) X := ghomOfCC (homologyModelTo X.toCC)

theorem sec_quasiIso (X : GCx k) : QuasiIso (GHom.toCC (sec X)) := by
  rw [sec, toCC_ghomOfCC]
  exact homologyModelTo_quasiIso X.toCC

/-- The map induced on cohomology models. -/
def hmap {X Y : GCx k} (f : GHom X Y) : GHom (hm X) (hm Y) where
  f i j h := by subst h; exact (HomologicalComplex.homologyMap (GHom.toCC f) i).hom
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    change (HomologicalComplex.homologyMap (GHom.toCC f) i₁).hom 0 = 0
    exact map_zero _

/-- The homotopy between the two composites `H(X) → Y`. -/
def htpy {X Y : GCx k} (f : GHom X Y) (n : ℤ) : (hm X).X n →ₗ[k] Y.X (n - 1) :=
  (Classical.choose (exists_htpy (GHom.toCC f) n)).hom

theorem htpy_spec {X Y : GCx k} (f : GHom X Y) (n : ℤ) (x : (hm X).X n) :
    Y.d (n - 1) n (by omega) (htpy f n x) =
      f.f n n rfl ((sec X).f n n rfl x) - (sec Y).f n n rfl ((hmap f).f n n rfl x) := by
  have h := congrArg (fun g => g.hom x) (Classical.choose_spec (exists_htpy (GHom.toCC f) n))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sub,
    LinearMap.sub_apply] at h
  rw [GCx.toCC_d_hom Y (n - 1) n (by omega)] at h
  exact h

end Relation

section ModelMaps

variable {k : Type} [Field k]

/-- A map of Selmer data out of data with zero differentials, commuting with the restriction
and the condition maps up to explicit homotopies. -/
structure ModelMap (D₁ D₂ : SelData k) where
  gG : GHom D₁.G D₂.G
  gU : GHom D₁.U D₂.U
  gL : GHom D₁.L D₂.L
  hres : ∀ i, D₁.G.X i →ₗ[k] D₂.L.X (i - 1)
  hι : ∀ i, D₁.U.X i →ₗ[k] D₂.L.X (i - 1)
  dG : ∀ i j h (x : D₁.G.X i), D₁.G.d i j h x = 0
  dU : ∀ i j h (x : D₁.U.X i), D₁.U.d i j h x = 0
  dL : ∀ i j h (x : D₁.L.X i), D₁.L.d i j h x = 0
  hres_spec : ∀ i j (h : i = j) (a : D₁.G.X i),
    D₂.res.f i j h (gG.f i i rfl a) - gL.f i j h (D₁.res.f i i rfl a) =
      D₂.L.d (i - 1) j (by omega) (hres i a)
  hι_spec : ∀ i j (h : i = j) (u : D₁.U.X i),
    D₂.ι.f i j h (gU.f i i rfl u) - gL.f i j h (D₁.ι.f i i rfl u) =
      D₂.L.d (i - 1) j (by omega) (hι i u)

variable {D₁ D₂ : SelData k}

/-- The induced map of Selmer complexes, `(a, u, x) ↦ (g a, g u, g x + h a − h u)`. -/
def ModelMap.sel (F : ModelMap D₁ D₂) : GHom (selCx D₁) (selCx D₂) where
  f i j h := by
    subst h
    exact ((F.gG.f i i rfl).comp (LinearMap.fst k _ _)).prod
      (((F.gU.f i i rfl).comp ((LinearMap.fst k _ _).comp (LinearMap.snd k _ _))).prod
        ((F.gL.f (i - 1) (i - 1) rfl).comp ((LinearMap.snd k _ _).comp (LinearMap.snd k _ _)) +
          (F.hres i).comp (LinearMap.fst k _ _) -
          (F.hι i).comp ((LinearMap.fst k _ _).comp (LinearMap.snd k _ _))))
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, u, x⟩ := c
    change (F.gG.f i₁ i₁ rfl (D₁.G.d i i₁ h₁ a), F.gU.f i₁ i₁ rfl (D₁.U.d i i₁ h₁ u),
        F.gL.f (i₁ - 1) (i₁ - 1) rfl (D₁.res.f i (i₁ - 1) (by omega) a -
            D₁.ι.f i (i₁ - 1) (by omega) u - D₁.L.d (i - 1) (i₁ - 1) (by omega) x) +
          F.hres i₁ (D₁.G.d i i₁ h₁ a) - F.hι i₁ (D₁.U.d i i₁ h₁ u)) =
      (D₂.G.d i i₁ h₂ (F.gG.f i i rfl a), D₂.U.d i i₁ h₂ (F.gU.f i i rfl u),
        D₂.res.f i (i₁ - 1) (by omega) (F.gG.f i i rfl a) -
          D₂.ι.f i (i₁ - 1) (by omega) (F.gU.f i i rfl u) -
          D₂.L.d (i - 1) (i₁ - 1) (by omega) (F.gL.f (i - 1) (i - 1) rfl x +
            F.hres i a - F.hι i u))
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact F.gG.comm i i₁ i i₁ rfl h₁ h₂ rfl a
    · exact F.gU.comm i i₁ i i₁ rfl h₁ h₂ rfl u
    · change F.gL.f (i₁ - 1) (i₁ - 1) rfl (D₁.res.f i (i₁ - 1) (by omega) a -
            D₁.ι.f i (i₁ - 1) (by omega) u - D₁.L.d (i - 1) (i₁ - 1) (by omega) x) +
          F.hres i₁ (D₁.G.d i i₁ h₁ a) - F.hι i₁ (D₁.U.d i i₁ h₁ u) =
        D₂.res.f i (i₁ - 1) (by omega) (F.gG.f i i rfl a) -
          D₂.ι.f i (i₁ - 1) (by omega) (F.gU.f i i rfl u) -
          D₂.L.d (i - 1) (i₁ - 1) (by omega) (F.gL.f (i - 1) (i - 1) rfl x +
            F.hres i a - F.hι i u)
      have e3 := F.gL.comm (i - 1) (i₁ - 1) (i - 1) (i₁ - 1) rfl (by omega) (by omega) rfl x
      have r1 := F.hres_spec i (i₁ - 1) (by omega) a
      have r2 := F.hι_spec i (i₁ - 1) (by omega) u
      rw [F.dL, map_zero] at e3
      rw [F.dG, F.dU, F.dL]
      simp only [map_zero, sub_zero, add_zero]
      rw [map_sub, ghom_reindex D₁.res F.gL i (i₁ - 1) (by omega) a,
        ghom_reindex D₁.ι F.gL i (i₁ - 1) (by omega) u, map_sub, map_add, ← e3, ← r1, ← r2]
      abel

/-- The induced map of local cones, `(u, x) ↦ (g u, g x − h u)`. -/
def ModelMap.loc (F : ModelMap D₁ D₂) : GHom (locCx D₁) (locCx D₂) where
  f i j h := by
    subst h
    exact ((F.gU.f i i rfl).comp (LinearMap.fst k _ _)).prod
      ((F.gL.f (i - 1) (i - 1) rfl).comp (LinearMap.snd k _ _) -
        (F.hι i).comp (LinearMap.fst k _ _))
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨u, x⟩ := c
    refine Prod.ext ?_ ?_
    · exact F.gU.comm i i₁ i i₁ rfl h₁ h₂ rfl u
    · change F.gL.f (i₁ - 1) (i₁ - 1) rfl (-(D₁.ι.f i (i₁ - 1) (by omega) u) -
            D₁.L.d (i - 1) (i₁ - 1) (by omega) x) - F.hι i₁ (D₁.U.d i i₁ h₁ u) =
          -(D₂.ι.f i (i₁ - 1) (by omega) (F.gU.f i i rfl u)) -
            D₂.L.d (i - 1) (i₁ - 1) (by omega) (F.gL.f (i - 1) (i - 1) rfl x - F.hι i u)
      have e3 := F.gL.comm (i - 1) (i₁ - 1) (i - 1) (i₁ - 1) rfl (by omega) (by omega) rfl x
      have r2 := F.hι_spec i (i₁ - 1) (by omega) u
      rw [F.dL, map_zero] at e3
      rw [F.dU, F.dL]
      simp only [map_zero, sub_zero]
      rw [map_neg, ghom_reindex D₁.ι F.gL i (i₁ - 1) (by omega) u, map_sub, ← e3, ← r2]
      abel

/-- The morphism of the sequences `0 → loc → Selmer → G → 0`. -/
def ModelMap.sesTopHom (F : ModelMap D₁ D₂) : sesTop D₁ ⟶ sesTop D₂ where
  τ₁ := GHom.toCC F.loc
  τ₂ := GHom.toCC F.sel
  τ₃ := GHom.toCC F.gG
  comm₁₂ := by
    change GHom.toCC F.loc ≫ GHom.toCC (inclLoc D₂) = GHom.toCC (inclLoc D₁) ≫ GHom.toCC F.sel
    rw [GHom.toCC_comp, GHom.toCC_comp]
    refine GHom.toCC_ext fun i c => ?_
    obtain ⟨u, x⟩ := c
    change ((0 : D₂.G.X i), F.gU.f i i rfl u, F.gL.f (i - 1) (i - 1) rfl x - F.hι i u) =
      (F.gG.f i i rfl 0, F.gU.f i i rfl u, F.gL.f (i - 1) (i - 1) rfl x + F.hres i 0 - F.hι i u)
    rw [map_zero, map_zero, add_zero]
  comm₂₃ := by
    change GHom.toCC F.sel ≫ GHom.toCC (projG D₂) = GHom.toCC (projG D₁) ≫ GHom.toCC F.gG
    rw [GHom.toCC_comp, GHom.toCC_comp]
    exact GHom.toCC_ext fun i c => rfl

/-- The shifted map `x ↦ g x` on `A[−1]`. -/
def shiftDownMap {A B : GCx k} (g : GHom A B) : GHom (shiftDown A) (shiftDown B) where
  f i j h := by subst h; exact g.f (i - 1) (i - 1) rfl
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    change g.f (i₁ - 1) (i₁ - 1) rfl (-(A.d (i - 1) (i₁ - 1) (by omega) x)) =
      -(B.d (i - 1) (i₁ - 1) (by omega) (g.f (i - 1) (i - 1) rfl x))
    rw [map_neg, g.comm (i - 1) (i₁ - 1) (i - 1) (i₁ - 1) rfl (by omega) (by omega) rfl x]

/-- The morphism of the cone sequences `0 → L[−1] → loc → U → 0`. -/
def ModelMap.coneHom (F : ModelMap D₁ D₂) : coneSES (negι D₁) ⟶ coneSES (negι D₂) where
  τ₁ := GHom.toCC (shiftDownMap F.gL)
  τ₂ := GHom.toCC F.loc
  τ₃ := GHom.toCC F.gU
  comm₁₂ := by
    change GHom.toCC (shiftDownMap F.gL) ≫ GHom.toCC (coneIncl (negι D₂)) =
      GHom.toCC (coneIncl (negι D₁)) ≫ GHom.toCC F.loc
    rw [GHom.toCC_comp, GHom.toCC_comp]
    refine GHom.toCC_ext fun i b => ?_
    change ((0 : D₂.U.X i), F.gL.f (i - 1) (i - 1) rfl b) =
      (F.gU.f i i rfl 0, F.gL.f (i - 1) (i - 1) rfl b - F.hι i 0)
    rw [map_zero, map_zero, sub_zero]
  comm₂₃ := by
    change GHom.toCC F.loc ≫ GHom.toCC (coneProj (negι D₂)) =
      GHom.toCC (coneProj (negι D₁)) ≫ GHom.toCC F.gU
    rw [GHom.toCC_comp, GHom.toCC_comp]
    exact GHom.toCC_ext fun i c => rfl

/-- `(a, b) ↦ (g a, g b)` on cones of identities. -/
def coneIdMap {A B : GCx k} (g : GHom A B) : GHom (coneCx (idGHom A)) (coneCx (idGHom B)) where
  f i j h := by subst h; exact (g.f i i rfl).prodMap (g.f (i - 1) (i - 1) rfl)
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, b⟩ := c
    refine Prod.ext ?_ ?_
    · exact g.comm i i₁ i i₁ rfl h₁ h₂ rfl a
    · change g.f (i₁ - 1) (i₁ - 1) rfl ((idGHom A).f i (i₁ - 1) (by omega) a -
            A.d (i - 1) (i₁ - 1) (by omega) b) =
          (idGHom B).f i (i₁ - 1) (by omega) (g.f i i rfl a) -
            B.d (i - 1) (i₁ - 1) (by omega) (g.f (i - 1) (i - 1) rfl b)
      rw [map_sub, g.comm (i - 1) (i₁ - 1) (i - 1) (i₁ - 1) rfl (by omega) (by omega) rfl b,
        ghom_reindex (idGHom A) g i (i₁ - 1) (by omega) a, idGHom_f_self, idGHom_f_comp]

/-- The morphism of cone sequences of identities induced by a map. -/
def coneIdHom {A B : GCx k} (g : GHom A B) : coneSES (idGHom A) ⟶ coneSES (idGHom B) where
  τ₁ := GHom.toCC (shiftDownMap g)
  τ₂ := GHom.toCC (coneIdMap g)
  τ₃ := GHom.toCC g
  comm₁₂ := by
    change GHom.toCC (shiftDownMap g) ≫ GHom.toCC (coneIncl (idGHom B)) =
      GHom.toCC (coneIncl (idGHom A)) ≫ GHom.toCC (coneIdMap g)
    rw [GHom.toCC_comp, GHom.toCC_comp]
    refine GHom.toCC_ext fun i b => ?_
    change ((0 : B.X i), g.f (i - 1) (i - 1) rfl b) = (g.f i i rfl 0, g.f (i - 1) (i - 1) rfl b)
    rw [map_zero]
  comm₂₃ := by
    change GHom.toCC (coneIdMap g) ≫ GHom.toCC (coneProj (idGHom B)) =
      GHom.toCC (coneProj (idGHom A)) ≫ GHom.toCC g
    rw [GHom.toCC_comp, GHom.toCC_comp]
    exact GHom.toCC_ext fun i c => rfl

/-- Shifting preserves quasi-isomorphisms. -/
theorem shiftDownMap_quasiIso {A B : GCx k} (g : GHom A B) (hg : QuasiIso (GHom.toCC g)) :
    QuasiIso (GHom.toCC (shiftDownMap g)) := by
  have h2 : QuasiIso (coneIdHom g).τ₂ := quasiIso_of_acyclic _
    ((acyclic_toCC_iff _).2 (coneCx_id_acyclic A)) ((acyclic_toCC_iff _).2 (coneCx_id_acyclic B))
  exact quasiIso_τ₁ (coneIdHom g) (coneSES_shortExact _) (coneSES_shortExact _) h2 hg

/-- **The induced map of Selmer cones is a quasi-isomorphism** when the three component maps are. -/
theorem ModelMap.sel_quasiIso (F : ModelMap D₁ D₂) (hG : QuasiIso (GHom.toCC F.gG))
    (hU : QuasiIso (GHom.toCC F.gU)) (hL : QuasiIso (GHom.toCC F.gL)) :
    QuasiIso (GHom.toCC F.sel) := by
  have h1 : QuasiIso (GHom.toCC (shiftDownMap F.gL)) := shiftDownMap_quasiIso F.gL hL
  have h2 : QuasiIso (GHom.toCC F.loc) :=
    quasiIso_τ₂ F.coneHom (coneSES_shortExact _) (coneSES_shortExact _) h1 hU
  exact quasiIso_τ₂ F.sesTopHom (sesTop_shortExact _) (sesTop_shortExact _) h2 hG

/-- A product of quasi-isomorphisms is a quasi-isomorphism (its cone is the product of the
acyclic cones). -/
theorem piMap_quasiIso {ι : Type} {A B : ι → GCx k} (f : ∀ v, GHom (A v) (B v))
    (hf : ∀ v, QuasiIso (GHom.toCC (f v))) : QuasiIso (GHom.toCC (piMap f)) := by
  have hv : ∀ v, GAcyclic (coneCx (f v)) := fun v => coneCx_acyclic_of_quasiIso (f v) (hf v)
  have hc : GAcyclic (coneCx (piMap f)) := by
    intro i j l hij hjl c hc
    obtain ⟨e, z⟩ := c
    have hcv : ∀ v, (coneCx (f v)).d j l hjl (e v, z v) = 0 := fun v =>
      Prod.ext (congrArg (fun c => c.1 v) hc) (congrArg (fun c => c.2 v) hc)
    choose y hy using fun v => hv v i j l hij hjl (e v, z v) (hcv v)
    refine ⟨(fun v => (y v).1, fun v => (y v).2), ?_⟩
    exact Prod.ext (funext fun v => congrArg Prod.fst (hy v))
      (funext fun v => congrArg Prod.snd (hy v))
  have h2 : QuasiIso (coneSESHom (piMap f)).τ₂ := quasiIso_of_acyclic _
    ((acyclic_toCC_iff _).2 hc) ((acyclic_toCC_iff _).2 (coneCx_id_acyclic _))
  have h1 : QuasiIso (coneSESHom (piMap f)).τ₁ := by
    change QuasiIso (GHom.toCC (idGHom (shiftDown (piCx B))))
    rw [toCC_idGHom]
    infer_instance
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ (coneSESHom (piMap f))
    (coneSES_shortExact _) (coneSES_shortExact _) h1 h2

end ModelMaps

section GenuineModel

variable {k : Type} [Field k]
  (GS : Type) [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {ι : Type} (Gv : ι → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]
  (Δ : LocalConditions k GS Gv loc M)

/-- The restriction to one local complex. -/
abbrev resAt (v : ι) : GHom (globalCx k GS M) (localCx k GS Gv loc M v) :=
  natHom (resCochains (k := k) (M := M) (loc v))

/-- **The formal residual model of genuine Selmer data**: the cohomology of the global complex,
of every local condition and of every local complex, with the maps induced on cohomology. -/
def formalData : SelData k where
  G := hm (globalCx k GS M)
  U := piCx fun v => hm (Δ.U v)
  L := piCx fun v => hm (localCx k GS Gv loc M v)
  res := piLift fun v => hmap (resAt GS Gv loc M v)
  ι := piMap fun v => hmap (Δ.i v)

/-- The comparison of the formal model with the genuine Selmer data. -/
def formalMap : ModelMap (formalData GS Gv loc M Δ) (selData k GS Gv loc M Δ) where
  gG := sec _
  gU := piMap fun v => sec (Δ.U v)
  gL := piMap fun v => sec (localCx k GS Gv loc M v)
  hres i := LinearMap.pi fun v => htpy (resAt GS Gv loc M v) i
  hι i := LinearMap.pi fun v => (htpy (Δ.i v) i).comp (LinearMap.proj v)
  dG _ _ _ _ := rfl
  dU _ _ _ _ := rfl
  dL _ _ _ _ := rfl
  hres_spec i j h a := by
    subst h
    funext v
    exact (htpy_spec (resAt GS Gv loc M v) i a).symm
  hι_spec i j h u := by
    subst h
    funext v
    exact (htpy_spec (Δ.i v) i (u v)).symm

/-- **The formal model is connected to the genuine Selmer complex by an actual
quasi-isomorphism.** -/
theorem formalMap_quasiIso :
    QuasiIso (GHom.toCC (formalMap GS Gv loc M Δ).sel) :=
  (formalMap GS Gv loc M Δ).sel_quasiIso (sec_quasiIso _)
    (piMap_quasiIso _ fun v => sec_quasiIso (Δ.U v))
    (piMap_quasiIso _ fun v => sec_quasiIso (localCx k GS Gv loc M v))

end GenuineModel

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive

/-! ## The field, the curve, the supports and the actual residual module -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Contrib.RC53Assist.ResidualWitnessActive.LocalKummer
  ZInQ.Manuscript.RC.HeegnerAlgebra

section NaturalHomology

variable {k : Type} [CommRing k]

private theorem extension_d_neg (C : CochainComplex (ModuleCat.{0} k) ℕ) :
    (natCx C).toCC.d (-1) 0 = 0 := by
  ext x
  exact GCx.toCC_d_hom (natCx C) (-1) 0 (by omega) x

private def zeroScHom (C : CochainComplex (ModuleCat.{0} k) ℕ) :
    (natCx C).toCC.sc' (-1) 0 1 ⟶ C.sc' 0 0 1 where
  τ₁ := 0
  τ₂ := 𝟙 (C.X 0)
  τ₃ := 𝟙 (C.X 1)
  comm₁₂ := by
    rw [zero_comp]
    change 0 = (natCx C).toCC.d (-1) 0 ≫ 𝟙 _
    rw [Category.comp_id, extension_d_neg]
  comm₂₃ := by
    ext x
    exact (GCx.toCC_d_hom (natCx C) 0 1 rfl x).trans rfl

private def zeroCyclesMap (C : CochainComplex (ModuleCat.{0} k) ℕ) :
    (natCx C).toCC.cycles 0 ⟶ C.cycles 0 :=
  ((natCx C).toCC.cyclesIsoSc' (-1) 0 1 (by simp) (by simp)).hom ≫
    ShortComplex.cyclesMap (zeroScHom C) ≫
    (C.cyclesIsoSc' 0 0 1 (by simp) (by simp)).inv

private def zeroHomologyIso (C : CochainComplex (ModuleCat.{0} k) ℕ) :
    (natCx C).toCC.homology 0 ≅ C.homology 0 := by
  have : IsIso (ShortComplex.cyclesMap (zeroScHom C)) :=
    ShortComplex.isIso_cyclesMap_of_isIso_of_mono' _
      (by change IsIso (𝟙 _); infer_instance) (by change Mono (𝟙 _); infer_instance)
  have : IsIso (zeroCyclesMap C) := by unfold zeroCyclesMap; infer_instance
  exact ((natCx C).toCC.isoHomologyπ (-1) 0 (by simp) (extension_d_neg C)).symm ≪≫
    asIso (zeroCyclesMap C) ≪≫ C.isoHomologyπ 0 0 (by simp) (C.shape 0 0 (by simp))

/-- Cohomology is unchanged by extension of natural cochains by zero. -/
def natHomologyIso (C : CochainComplex (ModuleCat.{0} k) ℕ) (n : ℕ) :
    (natCx C).toCC.homology (n : ℤ) ≅ C.homology n := by
  cases n with
  | zero => exact zeroHomologyIso C
  | succ n =>
    let e : (natCx C).toCC.sc' (n : ℤ) ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ) ≅
        C.sc' n (n + 1) (n + 2) :=
      ShortComplex.isoMk (Iso.refl (C.X n)) (Iso.refl (C.X (n + 1)))
        (Iso.refl (C.X (n + 2)))
        (by
          ext x
          exact (GCx.toCC_d_hom (natCx C) (n : ℤ) ((n + 1 : ℕ) : ℤ)
            (by omega) x).trans rfl |>.symm)
        (by
          ext x
          exact (GCx.toCC_d_hom (natCx C) ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)
            (by omega) x).trans rfl |>.symm)
    exact (natCx C).toCC.homologyIsoSc' (n : ℤ) ((n + 1 : ℕ) : ℤ)
        ((n + 2 : ℕ) : ℤ) (by simp) (by simp; omega) ≪≫
      ShortComplex.homologyMapIso e ≪≫
      (C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).symm

theorem natHomology_negative (C : CochainComplex (ModuleCat.{0} k) ℕ)
    (n : ℤ) (hn : n < 0) : Subsingleton ((natCx C).toCC.homology n) := by
  have : Subsingleton ((natCx C).toCC.X n) := by
    cases n with
    | ofNat m => simp only [Int.ofNat_eq_natCast] at hn; omega
    | negSucc m => exact inferInstanceAs (Subsingleton PUnit.{1})
  have : Subsingleton (((natCx C).toCC.sc n).X₂) :=
    inferInstanceAs (Subsingleton ((natCx C).toCC.X n))
  have hex : (natCx C).toCC.ExactAt n :=
    ((natCx C).toCC.sc n).exact_of_isZero_X₂ (ModuleCat.isZero_of_subsingleton _)
  exact ModuleCat.subsingleton_of_isZero
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 hex)

end NaturalHomology

/-! ### The field `ℚ(i)` and the curve `E₁₁` -/

/-- The imaginary quadratic field `ℚ(i)`. -/
abbrev SmallK := CyclotomicField 4 ℚ

local instance : IsCyclotomicExtension {4} ℚ SmallK := by
  have : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  exact CyclotomicField.isCyclotomicExtension 4 ℚ

theorem smallK_degree : Module.finrank ℚ SmallK = 2 := by
  rw [IsCyclotomicExtension.finrank (n := 4) SmallK
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
  decide

theorem smallK_complex : IsTotallyComplex SmallK :=
  IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) _ (by norm_num)

/-- An integral square root of minus one. -/
def smallAlpha : 𝓞 SmallK :=
  ⟨IsCyclotomicExtension.zeta 4 ℚ SmallK,
    (IsCyclotomicExtension.zeta_spec 4 ℚ SmallK).isIntegral (by norm_num)⟩

theorem smallAlpha_sq : smallAlpha ^ 2 = (-1 : 𝓞 SmallK) := by
  apply Subtype.ext
  have h : IsPrimitiveRoot (IsCyclotomicExtension.zeta 4 ℚ SmallK ^ 2) 2 := by
    simpa using (IsCyclotomicExtension.zeta_spec 4 ℚ SmallK).pow_of_dvd
      (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : (2 : ℕ) ∣ 4)
  exact h.eq_neg_one_of_two_right

theorem smallAlpha_radicand : IsQuadraticRadicand SmallK (-1) smallAlpha :=
  ⟨smallK_degree, by simpa using smallAlpha_sq,
    IsCyclotomicExtension.adjoin_primitive_root_eq_top
      (IsCyclotomicExtension.zeta_spec 4 ℚ SmallK)⟩

/-- The least admissible positive curve parameter. -/
theorem eleven_admissible :
    0 < (11 : ℕ) ∧ Squarefree (11 : ℕ) ∧ 11 % 12 = 11 ∧
      ∀ ℓ : ℕ, ℓ % 12 = 11 → 11 ≤ ℓ := by
  refine ⟨by decide, (show Nat.Prime 11 by decide).squarefree, by decide, ?_⟩
  intro ℓ hℓ
  have := Nat.mod_le ℓ 12
  omega

/-- The curve `E₁₁ : y² = x(x − 11)(x + 33)`. -/
def SmallE : WeierstrassCurve SmallK := cubicCurve 0 11 (-33)

theorem smallE_roots :
    (0 : SmallK) ≠ 11 ∧ (0 : SmallK) ≠ -33 ∧ (11 : SmallK) ≠ -33 := by
  norm_num

/-- Full rational `2`-torsion and trivial action on it, over every support. -/
theorem smallE_residual_hypotheses (S : Set (HeightOneSpectrum (𝓞 SmallK))) :
    FullTorsion SmallK S SmallE (2 ^ (0 + 1)) ∧
      FullTorsion SmallK S SmallE (2 ^ 0) ∧ FullTorsion SmallK S SmallE 2 ∧
      ∀ (σ : GKS SmallK S) (P : TorsS SmallK S SmallE ((2 : ℕ) : ℤ)), σ • P = P :=
  residualFin2_hyps_cubicCurve smallE_roots.1 smallE_roots.2.1 smallE_roots.2.2

/-- The integral equation of `E₁₁` over any base ring. -/
def smallCurve (R : Type*) [CommRing R] : WeierstrassCurve R := ⟨0, 22, 0, -363, 0⟩

theorem smallCurve_elliptic (F : Type*) [Field F] [CharZero F] :
    (smallCurve F).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  apply IsUnit.mk0
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, smallCurve]

theorem smallCurve_eq_smallE : smallCurve SmallK = SmallE := by
  ext <;> norm_num [smallCurve, SmallE, cubicCurve]

/-- The same integral curve at every finite place. -/
def smallLocalModels (w : HeightOneSpectrum (𝓞 SmallK)) :
    WeierstrassCurve (w.adicCompletionIntegers SmallK) :=
  smallCurve (w.adicCompletionIntegers SmallK)

theorem smallCurve_map {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A) :
    (smallCurve R).map f = smallCurve A := by
  ext <;> simp [smallCurve, WeierstrassCurve.map]
  · exact map_ofNat f 22
  · exact map_ofNat f 363

theorem smallLocal_baseChange (w : HeightOneSpectrum (𝓞 SmallK)) :
    (smallLocalModels w).baseChange (w.adicCompletion SmallK) =
      smallCurve (w.adicCompletion SmallK) :=
  smallCurve_map (algebraMap (w.adicCompletionIntegers SmallK) (w.adicCompletion SmallK))

instance (w : HeightOneSpectrum (𝓞 SmallK)) : CharZero (w.adicCompletion SmallK) :=
  ZInQ.Contrib.CloudB3RC53.Mattuck.charZero_adicCompletion SmallK w

instance smallLocal_elliptic (w : HeightOneSpectrum (𝓞 SmallK)) :
    ((smallLocalModels w).baseChange (w.adicCompletion SmallK)).IsElliptic := by
  rw [smallLocal_baseChange]
  exact smallCurve_elliptic _

/-- The local integral equations and the global curve have the same generic fiber. -/
theorem local_models_are_baseChanges (w : HeightOneSpectrum (𝓞 SmallK)) :
    (smallLocalModels w).baseChange (w.adicCompletion SmallK) =
      SmallE.baseChange (w.adicCompletion SmallK) := by
  rw [smallLocal_baseChange, ← smallCurve_eq_smallE]
  exact (smallCurve_map (algebraMap SmallK (w.adicCompletion SmallK))).symm

section ConcreteTorsion

open WeierstrassCurve

variable (F : Type*) [Field F] [CharZero F]

theorem rootZero_nonsingular : (smallCurve F).toAffine.Nonsingular 0 0 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  refine ⟨?_, Or.inl ?_⟩ <;> norm_num [smallCurve]

theorem rootEleven_nonsingular : (smallCurve F).toAffine.Nonsingular 11 0 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  refine ⟨?_, Or.inl ?_⟩ <;> norm_num [smallCurve]

theorem rootNegThirtyThree_nonsingular : (smallCurve F).toAffine.Nonsingular (-33) 0 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  refine ⟨?_, Or.inl ?_⟩ <;> norm_num [smallCurve]

/-- The four points killed by `2`. -/
def fourTorsionPoints : Fin 4 → (smallCurve F).toAffine.Point
  | 0 => 0
  | 1 => .some 0 0 (rootZero_nonsingular F)
  | 2 => .some 11 0 (rootEleven_nonsingular F)
  | 3 => .some (-33) 0 (rootNegThirtyThree_nonsingular F)

theorem two_zsmul_eq_zero_iff (P : (smallCurve F).toAffine.Point) :
    (2 : ℤ) • P = 0 ↔ ∃ i, fourTorsionPoints F i = P := by
  constructor
  · intro h
    rcases P with _ | ⟨x, y, hxy⟩
    · exact ⟨0, rfl⟩
    rw [two_zsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some,
      Affine.Point.some.injEq] at h
    have hy : y = 0 := by
      have hyy := h.2
      simp only [Affine.negY, smallCurve, zero_mul, sub_zero] at hyy
      have h2y : (2 : F) * y = 0 := by linear_combination hyy
      exact (mul_eq_zero.mp h2y).resolve_left two_ne_zero
    subst hy
    have he := hxy.1
    rw [Affine.equation_iff'] at he
    simp only [smallCurve] at he
    have hfac : x * (x - 11) * (x + 33) = 0 := by linear_combination -he
    rcases mul_eq_zero.mp hfac with h12 | h3
    · rcases mul_eq_zero.mp h12 with hx | hx
      · subst hx
        exact ⟨1, rfl⟩
      · have hx' : x = 11 := sub_eq_zero.mp hx
        subst hx'
        exact ⟨2, rfl⟩
    · have hx : x = -33 := eq_neg_of_add_eq_zero_left h3
      subst hx
      exact ⟨3, rfl⟩
  · rintro ⟨i, rfl⟩
    rw [two_zsmul, add_eq_zero_iff_eq_neg]
    fin_cases i <;> simp [fourTorsionPoints, Affine.Point.neg_some, Affine.negY, smallCurve]

theorem fourTorsionPoints_injective : Function.Injective (fourTorsionPoints F) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [fourTorsionPoints] <;> norm_num at h

/-- Exactly four points killed by `2` on the integral equation of `E₁₁`. -/
theorem smallCurve_two_torsion :
    Nat.card (Submodule.torsionBy ℤ (smallCurve F).toAffine.Point 2) = 4 := by
  have hmem : ∀ i, fourTorsionPoints F i ∈ Submodule.torsionBy ℤ (smallCurve F).toAffine.Point 2 :=
    fun i => (Submodule.mem_torsionBy_iff _ _).mpr
      ((two_zsmul_eq_zero_iff F _).mpr ⟨i, rfl⟩)
  let f : Fin 4 → Submodule.torsionBy ℤ (smallCurve F).toAffine.Point 2 :=
    fun i => ⟨fourTorsionPoints F i, hmem i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact fourTorsionPoints_injective F (congrArg Subtype.val h)
    · intro P
      have hP : (2 : ℤ) • (P : (smallCurve F).toAffine.Point) = 0 :=
        (Submodule.mem_torsionBy_iff _ _).mp P.2
      obtain ⟨i, hi⟩ := (two_zsmul_eq_zero_iff F _).mp hP
      exact ⟨i, Subtype.ext hi⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_fin]

end ConcreteTorsion

/-- Exactly four rational points killed by `2` on the local curve at every finite place. -/
theorem local_models_have_full_two_torsion (w : HeightOneSpectrum (𝓞 SmallK)) :
    Nat.card (Submodule.torsionBy ℤ
      ((smallLocalModels w).baseChange (w.adicCompletion SmallK)).toAffine.Point 2) = 4 := by
  rw [smallLocal_baseChange]
  exact smallCurve_two_torsion _

/-! ### The supports -/

open ZInQ.Manuscript.RC.Limits

/-- The derivative primes: one inert derivative prime. -/
def actD : Finset ℕ := {7}

theorem actD_prime : ∀ p ∈ actD, p.Prime := by
  intro p hp
  simp only [actD, Finset.mem_singleton] at hp
  subst hp
  decide

theorem actD_odd : ∀ p ∈ actD, p ≠ 2 := by
  intro p hp
  simp only [actD, Finset.mem_singleton] at hp
  subst hp
  decide

theorem actPrimeFactors : (2 * 66).primeFactors = {2, 3, 11} := by
  rw [show 2 * 66 = 2 * (2 * 3 * 11) by decide,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.prime_two.primeFactors, Nat.prime_three.primeFactors,
    (show Nat.Prime 11 by decide).primeFactors]
  decide

/-- The charged rational primes: the prime divisors of `2N`, the moving prime and the derivative
prime. -/
theorem actCharged_eq : chargedPrimes 66 5 actD = {2, 3, 5, 7, 11} := by
  simp only [chargedPrimes, actPrimeFactors, actD]
  decide

/-- `S₀ = Sloc = S`: the places above `2N`, the moving prime `5` and the derivative prime `7`. -/
def SmallS : Set (HeightOneSpectrum (𝓞 SmallK)) :=
  primesAboveSet SmallK (chargedPrimes 66 5 actD)

theorem smallS_finite : SmallS.Finite :=
  primesAboveSet_finite SmallK _
    (ne_zero_of_mem_chargedPrimes (by decide) (by decide) actD_prime)

theorem smallS_above_two (v : HeightOneSpectrum (𝓞 SmallK))
    (hv : (2 : 𝓞 SmallK) ∈ v.asIdeal) : v ∈ SmallS :=
  two_mem_primesAboveSet SmallK (two_mem_chargedPrimes (by decide)) v hv

/-- The larger support: one active prime `13` added. -/
def SmallS' : Set (HeightOneSpectrum (𝓞 SmallK)) :=
  primesAboveSet SmallK (insert 13 (chargedPrimes 66 5 actD))

theorem smallS_sub : SmallS ⊆ SmallS' :=
  primesAboveSet_mono SmallK (Finset.subset_insert _ _)

theorem smallS'_finite : SmallS'.Finite := by
  refine primesAboveSet_finite SmallK _ ?_
  intro p hp
  rw [Finset.mem_insert] at hp
  rcases hp with rfl | hp
  · decide
  · exact ne_zero_of_mem_chargedPrimes (by decide) (by decide) actD_prime p hp

/-- **A place above the active prime `13`.** -/
theorem exists_place_above_thirteen :
    ∃ q : HeightOneSpectrum (𝓞 SmallK), ((13 : ℤ) : 𝓞 SmallK) ∈ q.asIdeal := by
  have hP : (Ideal.span {(13 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).mpr (Int.prime_iff_natAbs_prime.mpr (by decide))
  obtain ⟨Q, -, hQ, hQu⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 SmallK)
    (Ideal.span {(13 : ℤ)}) ⊥ (by
      intro x hx
      have : algebraMap ℤ (𝓞 SmallK) x = 0 := hx
      have hx0 : x = 0 := by
        rw [eq_intCast] at this
        exact_mod_cast this
      rw [hx0]
      exact Ideal.zero_mem _)
  have h13 : (13 : ℤ) ∈ Q.under ℤ := by rw [hQu]; exact Ideal.mem_span_singleton_self _
  have h13' : ((13 : ℤ) : 𝓞 SmallK) ∈ Q := by
    have := Ideal.mem_comap.mp h13
    rwa [eq_intCast] at this
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have h0 : ((13 : ℤ) : 𝓞 SmallK) = 0 := (Submodule.mem_bot _).mp h13'
    have : ((13 : ℤ) : 𝓞 SmallK) ≠ 0 := by exact_mod_cast (by norm_num : (13 : ℤ) ≠ 0)
    exact this h0
  exact ⟨⟨Q, hQ, hne⟩, h13'⟩

/-- **The active support is nonempty**: some place of `S'` is not in `S`. -/
theorem newPlaces_nonempty : Nonempty (NewPlaces SmallK SmallS SmallS') := by
  obtain ⟨q, hq⟩ := exists_place_above_thirteen
  refine ⟨⟨q, ⟨13, Finset.mem_insert_self _ _, by exact_mod_cast hq⟩, ?_⟩⟩
  rintro ⟨p, hp, hpq⟩
  have hpP : p.Prime := prime_of_mem_chargedPrimes (by decide) actD_prime p hp
  have := ZInQ.Contrib.CloudB3RC53.RankCounts.Genus.prime_eq_of_mem (K := SmallK) q.isPrime.ne_top
    hpP (by decide : Nat.Prime 13) hpq (by exact_mod_cast hq)
  subst this
  rw [actCharged_eq] at hp
  revert hp
  decide

theorem smallSetting : NekovarFiniteSetting SmallK SmallS 2 (ZMod 2) where
  prime := Nat.prime_two
  finite_S := smallS_finite
  above_p := smallS_above_two
  condP _ := smallK_complex
  finite_R := inferInstance
  nilpotent_p := ⟨1, by decide⟩
  selfInjective := Module.injective_of_isSemisimpleRing (ZMod 2) (ZMod 2)

instance : Finite (Places SmallK SmallS) := smallS_finite.to_subtype

/-! ### The actual residual module -/

/-- The trivial character at the first coefficient stage. -/
def smallCharacter : GKS SmallK SmallS →* (Acoef (0 + 1))ˣ := 1

/-- The actual residual module `𝔽₂ ⊗ M₁` of `E₁₁` over `S`. -/
abbrev SmallM : Type := ResidualM SmallE 0 smallCharacter

theorem smallTorsion :
    FullTorsion SmallK SmallS SmallE (2 ^ (0 + 1)) ∧
      FullTorsion SmallK SmallS SmallE (2 ^ 0) ∧ FullTorsion SmallK SmallS SmallE 2 ∧
      ∀ (σ : GKS SmallK SmallS) (P : TorsS SmallK SmallS SmallE ((2 : ℕ) : ℤ)), σ • P = P :=
  smallE_residual_hypotheses SmallS

instance : ContinuousSMul (GKS SmallK SmallS) SmallM :=
  continuousSMul_residualM SmallE 0 smallCharacter smallTorsion.1 smallTorsion.2.1
    smallTorsion.2.2.1 smallTorsion.2.2.2

instance : Finite SmallM :=
  finite_residualM SmallE 0 smallCharacter smallTorsion.1 smallTorsion.2.1 smallTorsion.2.2.1

/-- The actual residual coefficients identified with the trivial two-dimensional module. -/
def smallMEquiv : SmallM ≃ₗ[ZMod 2] Wgen SmallK SmallS :=
  residualMEquivWgen SmallE 0 smallCharacter smallTorsion.1 smallTorsion.2.1 smallTorsion.2.2.1

theorem smallM_smul (σ : GKS SmallK SmallS) (x : SmallM) : σ • x = x :=
  smul_residualM_eq SmallE 0 smallCharacter smallTorsion.1 smallTorsion.2.1
    smallTorsion.2.2.1 smallTorsion.2.2.2 σ x

theorem smallM_finrank : Module.finrank (ZMod 2) SmallM = 2 :=
  smallMEquiv.finrank_eq.trans finrank_zmod2_sq

/-- The actual residual representation has four elements, dimension two, and trivial action. -/
theorem smallM_facts : Nat.card SmallM = 4 ∧ Module.finrank (ZMod 2) SmallM = 2 ∧
    ∀ (σ : GKS SmallK SmallS) (x : SmallM), σ • x = x := by
  refine ⟨?_, smallM_finrank, smallM_smul⟩
  rw [Nat.card_congr smallMEquiv.toEquiv]
  change Nat.card (ZMod 2 × ZMod 2) = 4
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]

/-! ### The global complex -/

abbrev smallGlobal : GCx (ZMod 2) := globalCx (ZMod 2) (GKS SmallK SmallS) SmallM

/-- The actual-coefficient identification of a global term in a natural degree. -/
def smallActualHEquiv (n : ℕ) : smallGlobal.toCC.homology (n : ℤ) ≃ₗ[ZMod 2]
    contCohomology (ZMod 2) (GKS SmallK SmallS) SmallM n :=
  (natHomologyIso (contCochains (ZMod 2) (GKS SmallK SmallS) SmallM) n).toLinearEquiv

/-- The genuine-coefficient identification of the same global term. -/
def smallGlobalHEquiv (n : ℕ) : smallGlobal.toCC.homology (n : ℤ) ≃ₗ[ZMod 2]
    genH SmallK SmallS n :=
  (smallActualHEquiv n).trans
    (residualCohIso SmallE 0 smallCharacter smallTorsion.1 smallTorsion.2.1
      smallTorsion.2.2.1 smallTorsion.2.2.2 n).toLinearEquiv

def allGenHEquiv (n : ℕ) : genH SmallK SmallS n ≃ₗ[ZMod 2]
    continuousCohomology n (Wrep SmallK SmallS) := by
  have : LocallyCompactSpace (GKS SmallK SmallS) := locallyCompactSpace_GS SmallK SmallS
  have : ContinuousSMul (ZMod 2) (Wgen SmallK SmallS) :=
    ZInQ.Contrib.CloudB3RC53.ContBridge.continuousSMul_of_discrete (ZMod 2) (Wgen SmallK SmallS)
  exact (ZInQ.Contrib.CloudB3RC53.ContBridge.contCohomologyLinearEquiv
    (ZMod 2) (GKS SmallK SmallS) (Wgen SmallK SmallS) n).symm

theorem smallGenH_finite (h51 : MilneADT_I_5_1_totallyComplex) (n : ℕ) (hn : n ≤ 2) :
    Module.Finite (ZMod 2) (genH SmallK SmallS n) := by
  obtain ⟨h0, h1, h2, _⟩ := h51 SmallK smallK_complex SmallS smallS_finite smallS_above_two
    (Wrep SmallK SmallS) inferInstance inferInstance
    (continuous_trivialRepS_action (GaloisGroupS SmallK SmallS) (ZMod 2 × ZMod 2))
  have : Module.Finite (ZMod 2) (continuousCohomology n (Wrep SmallK SmallS)) := by
    rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  exact (genHEquiv SmallK SmallS n hn).symm.finiteDimensional

theorem smallGenH_upper (h410 : MilneADT_I_4_10_totallyComplex) (n : ℕ) (hn : 2 < n) :
    Subsingleton (genH SmallK SmallS n) := by
  have := h410 SmallK smallK_complex SmallS smallS_finite smallS_above_two
    (Wrep SmallK SmallS) inferInstance inferInstance
    (continuous_trivialRepS_action (GaloisGroupS SmallK SmallS) (ZMod 2 × ZMod 2)) n hn
  exact ⟨fun x y => (allGenHEquiv n).injective (Subsingleton.elim _ _)⟩

theorem smallGlobal_finite (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (n : ℤ) :
    Module.Finite (ZMod 2) ((hm smallGlobal).X n) := by
  change Module.Finite (ZMod 2) (smallGlobal.toCC.homology n)
  cases n with
  | negSucc m =>
    have := natHomology_negative
      (contCochains (ZMod 2) (GKS SmallK SmallS) SmallM) (Int.negSucc m)
      (Int.negSucc_lt_zero m)
    infer_instance
  | ofNat m =>
    have : Module.Finite (ZMod 2) (genH SmallK SmallS m) := by
      by_cases hm : m ≤ 2
      · exact smallGenH_finite h51 m hm
      · have := smallGenH_upper h410 m (by omega)
        infer_instance
    exact (smallGlobalHEquiv m).symm.finiteDimensional

theorem smallGlobal_off (h410 : MilneADT_I_4_10_totallyComplex)
    (n : ℤ) (hn : n < 0 ∨ 2 < n) : Subsingleton ((hm smallGlobal).X n) := by
  change Subsingleton (smallGlobal.toCC.homology n)
  cases n with
  | negSucc m =>
    exact natHomology_negative (contCochains (ZMod 2) (GKS SmallK SmallS) SmallM)
      (Int.negSucc m) (Int.negSucc_lt_zero m)
  | ofNat m =>
    have hm : 2 < m := by simp only [Int.ofNat_eq_natCast] at hn; omega
    have := smallGenH_upper h410 m hm
    exact ⟨fun x y => (smallGlobalHEquiv m).injective (Subsingleton.elim _ _)⟩

/-- `h⁰ = 2`. -/
theorem smallGlobal_zero_rank : Module.finrank (ZMod 2) ((hm smallGlobal).X 0) = 2 := by
  change Module.finrank (ZMod 2) (smallGlobal.toCC.homology ((0 : ℕ) : ℤ)) = 2
  rw [((smallGlobalHEquiv 0).trans (genHEquiv SmallK SmallS 0 (by decide))).finrank_eq]
  exact (finrank_H0_trivialRepS (GaloisGroupS SmallK SmallS) (ZMod 2 × ZMod 2)).trans
    finrank_zmod2_sq

/-- `h¹ ≥ 4`, from the printed global Euler characteristic. -/
theorem smallGlobal_one_rank (h51 : MilneADT_I_5_1_totallyComplex) :
    4 ≤ Module.finrank (ZMod 2) ((hm smallGlobal).X 1) := by
  change 4 ≤ Module.finrank (ZMod 2) (smallGlobal.toCC.homology ((1 : ℕ) : ℤ))
  rw [((smallGlobalHEquiv 1).trans (genHEquiv SmallK SmallS 1 (by decide))).finrank_eq]
  obtain ⟨_, _, _, he⟩ := h51 SmallK smallK_complex SmallS smallS_finite smallS_above_two
    (Wrep SmallK SmallS) inferInstance inferInstance
    (continuous_trivialRepS_action (GaloisGroupS SmallK SmallS) (ZMod 2 × ZMod 2))
  have hc : InfinitePlace.nrComplexPlaces SmallK = 1 :=
    nrComplexPlaces_eq_one_of_imaginaryQuadratic SmallK smallK_degree smallK_complex
  have hd : Module.finrank (ZMod 2) (Wrep SmallK SmallS) = 2 := finrank_zmod2_sq
  have hh0 : hW SmallK SmallS 0 = 2 :=
    (finrank_H0_trivialRepS (GaloisGroupS SmallK SmallS) (ZMod 2 × ZMod 2)).trans finrank_zmod2_sq
  change (hW SmallK SmallS 0 : ℤ) - hW SmallK SmallS 1 + hW SmallK SmallS 2 =
    -((InfinitePlace.nrComplexPlaces SmallK : ℤ) * Module.finrank (ZMod 2) (Wrep SmallK SmallS)) at he
  rw [hh0, hc, hd] at he
  change 4 ≤ hW SmallK SmallS 1
  omega

/-! ### Local cohomology at the places of `S` -/

/-- The local coefficient module at a place: `M` with the action through localization. -/
abbrev locM (v : HeightOneSpectrum (𝓞 SmallK)) : Type := ResMod (locMap SmallK SmallS v) SmallM

theorem locM_smul (v : HeightOneSpectrum (𝓞 SmallK)) (g : Gloc SmallK v) (x : locM v) :
    g • x = x :=
  smallM_smul (locMap SmallK SmallS v g) x

/-- A place of `S` lies above a charged prime. -/
theorem place_above (v : Places SmallK SmallS) :
    ∃ p ∈ chargedPrimes 66 5 actD, p.Prime ∧ v.1.asIdeal ∈ primesAbove SmallK p := by
  obtain ⟨p, hp, hv⟩ := v.2
  have hpP : p.Prime := prime_of_mem_chargedPrimes (by decide) actD_prime p hp
  exact ⟨p, hp, hpP, (natCast_mem_asIdeal_iff SmallK hpP v.1).mp hv⟩

/-- **Local finiteness and vanishing** (the printed local theorem, Milne I.2.8), for the actual
residual module, in every degree. -/
theorem local_finite_vanishing (h28 : MilneADT_I_2_8) (v : HeightOneSpectrum (𝓞 SmallK))
    {p : ℕ} (hp : p.Prime) (hv : v.asIdeal ∈ primesAbove SmallK p) :
    (∀ n, Module.Finite (ZMod 2) (contCohomology (ZMod 2) (Gloc SmallK v) (locM v) n)) ∧
      ∀ n, 2 < n → Subsingleton (contCohomology (ZMod 2) (Gloc SmallK v) (locM v) n) := by
  have : Fact p.Prime := ⟨hp⟩
  have hlo : v.asIdeal.LiesOver (vP ⟨p, hp⟩).asIdeal := by
    rw [vP_asIdeal]; exact hv.2
  let _ := qpAlg SmallK ⟨p, hp⟩ v
  have : FiniteDimensional ℚ_[p] (v.adicCompletion SmallK) :=
    qp_finiteDimensional SmallK ⟨p, hp⟩ v.asIdeal hv
  have : LocallyCompactSpace (Gloc SmallK v) := locallyCompactSpace_Gloc SmallK v
  have : ContinuousSMul (ZMod 2) (locM v) :=
    ZInQ.Contrib.CloudB3RC53.ContBridge.continuousSMul_of_discrete (ZMod 2) (locM v)
  have hF : Finite (locM v) := inferInstanceAs (Finite SmallM)
  have hD : DiscreteTopology (locM v) := inferInstanceAs (DiscreteTopology SmallM)
  obtain ⟨hfin, hvan, -⟩ := h28 p (v.adicCompletion SmallK)
    (TauCeti.ofDiscreteModule (ZMod 2) (Gloc SmallK v) (locM v)) hF hD
    (ZInQ.Contrib.CloudB3RC53.ContBridge.hcontDisc (ZMod 2) (Gloc SmallK v) (locM v))
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · have := hfin n
    exact (ZInQ.Contrib.CloudB3RC53.ContBridge.contCohomologyLinearEquiv (ZMod 2)
      (Gloc SmallK v) (locM v) n).finiteDimensional
  · have := hvan n hn
    exact ⟨fun x y => (ZInQ.Contrib.CloudB3RC53.ContBridge.contCohomologyLinearEquiv (ZMod 2)
      (Gloc SmallK v) (locM v) n).symm.injective (Subsingleton.elim _ _)⟩

/-- The actual local coefficients and the trivial two-dimensional module have the same cohomology. -/
def locCohEquiv (v : HeightOneSpectrum (𝓞 SmallK)) (n : ℕ) :
    contCohomology (ZMod 2) (Gloc SmallK v) (locM v) n ≃ₗ[ZMod 2]
      genLocH SmallK SmallS W2v v n := by
  let e : locM v ≃ₗ[ZMod 2] locMod SmallK SmallS W2v v :=
    smallMEquiv.trans (LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2)).symm
  let f : contCochains (ZMod 2) (Gloc SmallK v) (locM v) ⟶
      contCochains (ZMod 2) (Gloc SmallK v) (locMod SmallK SmallS W2v v) :=
    contCochainsMap (ContinuousMonoidHom.id _) e.toLinearMap continuous_of_discreteTopology
      (fun g m => by
        change e (g • m) = g • e m
        rw [locM_smul v g m]
        rfl)
  let g : contCochains (ZMod 2) (Gloc SmallK v) (locMod SmallK SmallS W2v v) ⟶
      contCochains (ZMod 2) (Gloc SmallK v) (locM v) :=
    contCochainsMap (ContinuousMonoidHom.id _) e.symm.toLinearMap continuous_of_discreteTopology
      (fun g m => by
        change e.symm (g • m) = g • e.symm m
        rw [locM_smul v g (e.symm m)]
        rfl)
  have hfg : f ≫ g = 𝟙 _ := by
    rw [← contCochainsMap_comp, ← contCochainsMap_id (ZMod 2) (Gloc SmallK v) (locM v)]
    congr 1
    exact LinearMap.ext fun x => e.symm_apply_apply x
  have hgf : g ≫ f = 𝟙 _ := by
    rw [← contCochainsMap_comp,
      ← contCochainsMap_id (ZMod 2) (Gloc SmallK v) (locMod SmallK SmallS W2v v)]
    congr 1
    exact LinearMap.ext fun x => e.apply_symm_apply x
  exact (HomologicalComplex.homologyMapIso ⟨f, g, hfg, hgf⟩ n).toLinearEquiv

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive

/-! ## The full and the relaxed derivative conditions -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain WeierstrassCurve
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Contrib.RC53Assist.ResidualWitnessActive.LocalKummer
  ZInQ.Manuscript.RC.Limits

/-! ### Complexes with finite cohomology concentrated in degrees `0, 1, 2` -/

/-- Finite-dimensional cohomology in every degree, vanishing outside `[0, 2]`. -/
def Good (C : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ) : Prop :=
  (∀ n, Module.Finite (ZMod 2) (C.homology n)) ∧
    ∀ n, (n < 0 ∨ 2 < n) → Subsingleton (C.homology n)

theorem good_of_iso {C D : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ} (e : C ≅ D) (h : Good D) :
    Good C := by
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · have := h.1 n
    exact (HomologicalComplex.homologyMapIso e n).toLinearEquiv.symm.finiteDimensional
  · have := h.2 n hn
    exact ⟨fun x y => (HomologicalComplex.homologyMapIso e n).toLinearEquiv.injective
      (Subsingleton.elim _ _)⟩

theorem homology_subsingleton_of_X {C : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ} (n : ℤ)
    (h : Subsingleton (C.X n)) : Subsingleton (C.homology n) := by
  have : Subsingleton ((C.sc n).X₂) := h
  have hex : C.ExactAt n := (C.sc n).exact_of_isZero_X₂ (ModuleCat.isZero_of_subsingleton _)
  exact ModuleCat.subsingleton_of_isZero
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 hex)

/-- A Mathlib complex and its relation-indexed form have the same terms and differentials. -/
def ofCCIso (C : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ) : (ofCC C).toCC ≅ C :=
  HomologicalComplex.Hom.isoOfComponents (fun n => Iso.refl _) (fun i j hij => by
    have h : i + 1 = j := hij
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    ext x
    exact (GCx.toCC_d_hom (ofCC C) i j h x).symm)

/-! ### The full local condition -/

abbrev locCC (v : HeightOneSpectrum (𝓞 SmallK)) : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ :=
  (natCx (contCochains (ZMod 2) (Gloc SmallK v) (locM v))).toCC

theorem good_full (h28 : MilneADT_I_2_8) (v : HeightOneSpectrum (𝓞 SmallK)) {p : ℕ}
    (hp : p.Prime) (hv : v.asIdeal ∈ primesAbove SmallK p) : Good (locCC v) := by
  obtain ⟨hfin, hvan⟩ := local_finite_vanishing h28 v hp hv
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · cases n with
    | ofNat m =>
      have := hfin m
      exact (natHomologyIso (contCochains (ZMod 2) (Gloc SmallK v) (locM v)) m).toLinearEquiv.symm.finiteDimensional
    | negSucc m =>
      have := natHomology_negative (contCochains (ZMod 2) (Gloc SmallK v) (locM v))
        (Int.negSucc m) (Int.negSucc_lt_zero m)
      infer_instance
  · cases n with
    | ofNat m =>
      have hm : 2 < m := by simp only [Int.ofNat_eq_natCast] at hn; omega
      have := hvan m hm
      exact ⟨fun x y => (natHomologyIso (contCochains (ZMod 2) (Gloc SmallK v) (locM v))
        m).toLinearEquiv.injective (Subsingleton.elim _ _)⟩
    | negSucc m =>
      exact natHomology_negative (contCochains (ZMod 2) (Gloc SmallK v) (locM v))
        (Int.negSucc m) (Int.negSucc_lt_zero m)

/-- The cohomology of the full condition in degrees `0, 1, 2` is the local cohomology. -/
theorem finrank_full (v : HeightOneSpectrum (𝓞 SmallK)) (m : ℕ) :
    Module.finrank (ZMod 2) ((locCC v).homology (m : ℤ)) =
      Module.finrank (ZMod 2) (genLocH SmallK SmallS W2v v m) :=
  ((natHomologyIso (contCochains (ZMod 2) (Gloc SmallK v) (locM v)) m).toLinearEquiv.trans
    (locCohEquiv v m)).finrank_eq

/-! ### The relaxed derivative condition -/

abbrev relCC (v : HeightOneSpectrum (𝓞 SmallK)) : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ :=
  relaxedCx (Gloc SmallK v) (locM v)

/-- `H⁰` of the relaxed derivative condition is local `H⁰`. -/
def relH0Equiv (v : HeightOneSpectrum (𝓞 SmallK)) :
    (relCC v).homology 0 ≃ₗ[ZMod 2] contCohomology (ZMod 2) (Gloc SmallK v) (locM v) 0 :=
  (dblH0Iso (relaxedD (Gloc SmallK v) (locM v))).toLinearEquiv.trans
    ((LinearEquiv.ofEq _ _ (LinearMap.ker_codRestrict _ _ _)).trans
      (toLin ((z0EquivH0 (Gloc SmallK v) (locM v)).trans
        (contH0AddEquiv (ZMod 2) (Gloc SmallK v) (locM v)).symm)))

/-- `H¹` of the relaxed derivative condition is local `H¹`. -/
def relH1Equiv (v : HeightOneSpectrum (𝓞 SmallK)) :
    (relCC v).homology 1 ≃ₗ[ZMod 2] contCohomology (ZMod 2) (Gloc SmallK v) (locM v) 1 :=
  (dblH1Iso (relaxedD (Gloc SmallK v) (locM v))).toLinearEquiv.trans
    (toLin ((z1QuotEquivH1 (Gloc SmallK v) (locM v)).trans
      (contH1AddEquiv (ZMod 2) (Gloc SmallK v) (locM v)).symm))

theorem relCC_X_subsingleton (v : HeightOneSpectrum (𝓞 SmallK)) (n : ℤ) (h0 : n ≠ 0)
    (h1 : n ≠ 1) : Subsingleton ((relCC v).X n) :=
  ModuleCat.subsingleton_of_isZero (HomologicalComplex.isZero_double_X _ _ n h0 h1)

theorem good_rel (h28 : MilneADT_I_2_8) (v : HeightOneSpectrum (𝓞 SmallK)) {p : ℕ}
    (hp : p.Prime) (hv : v.asIdeal ∈ primesAbove SmallK p) : Good (relCC v) := by
  obtain ⟨hfin, -⟩ := local_finite_vanishing h28 v hp hv
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · by_cases h0 : n = 0
    · subst h0
      have := hfin 0
      exact (relH0Equiv v).symm.finiteDimensional
    by_cases h1 : n = 1
    · subst h1
      have := hfin 1
      exact (relH1Equiv v).symm.finiteDimensional
    · have := homology_subsingleton_of_X n (relCC_X_subsingleton v n h0 h1)
      infer_instance
  · exact homology_subsingleton_of_X n (relCC_X_subsingleton v n (by omega) (by omega))

theorem finrank_rel (v : HeightOneSpectrum (𝓞 SmallK)) :
    Module.finrank (ZMod 2) ((relCC v).homology 0) +
        Module.finrank (ZMod 2) ((relCC v).homology 1) =
      Module.finrank (ZMod 2) (genLocH SmallK SmallS W2v v 0) +
        Module.finrank (ZMod 2) (genLocH SmallK SmallS W2v v 1) := by
  rw [((relH0Equiv v).trans (locCohEquiv v 0)).finrank_eq,
    ((relH1Equiv v).trans (locCohEquiv v 1)).finrank_eq]

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive

/-! ## The old Kummer condition -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain WeierstrassCurve
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Contrib.RC53Assist.ResidualWitnessActive.LocalKummer
  ZInQ.Manuscript.RC.Limits

/-! ### The old Kummer condition at a place -/

section KummerPlace

variable (v : HeightOneSpectrum (𝓞 SmallK))

instance smallCurve_isElliptic_local :
    (smallCurve (v.adicCompletion SmallK)).IsElliptic :=
  smallCurve_elliptic _

/-- The points of `E₁₁` over an algebraic closure of `K_v` killed by `2`. -/
abbrev Tv : Type := TorsAlg (v.adicCompletion SmallK) (smallCurve (v.adicCompletion SmallK)) 2

theorem card_torsionBy_two (F : Type) [Field F] [CharZero F] :
    Nat.card (AddSubgroup.torsionBy (smallCurve F).toAffine.Point ((2 : ℕ) : ℤ)) = 4 := by
  rw [← smallCurve_two_torsion F]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun P => by
    rw [AddSubgroup.torsionBy.nsmul_iff, Submodule.mem_torsionBy_iff]
    constructor
    · intro h; rw [two_zsmul]; rw [two_nsmul] at h; exact h
    · intro h; rw [two_nsmul]; rw [two_zsmul] at h; exact h)

theorem card_Tv : Nat.card (Tv v) = 4 := by
  have h := smallCurve_map (algebraMap (v.adicCompletion SmallK)
    (AlgebraicClosure (v.adicCompletion SmallK)))
  have key : ∀ W : WeierstrassCurve (AlgebraicClosure (v.adicCompletion SmallK)),
      W = smallCurve _ → Nat.card (AddSubgroup.torsionBy W.toAffine.Point ((2 : ℕ) : ℤ)) = 4 := by
    rintro W rfl
    exact card_torsionBy_two _
  exact key _ h

/-- **The Galois action on `E₁₁(K̄_v)[2]` is trivial**: all four points are rational. -/
theorem Tv_trivial (σ : Gloc SmallK v) (t : Tv v) : σ • t = t := by
  have hinj := baseTors_injective (F := v.adicCompletion SmallK)
    (B := smallCurve (v.adicCompletion SmallK)) 2
  have hbij : Function.Bijective (baseTors (v.adicCompletion SmallK)
      (smallCurve (v.adicCompletion SmallK)) 2) :=
    hinj.bijective_of_nat_card_le (by rw [card_Tv, card_torsionBy_two])
  obtain ⟨s, rfl⟩ := hbij.2 t
  exact smul_baseTors σ s

instance Tv_module : Module (ZMod 2) (Tv v) :=
  AddCommGroup.zmodModule (n := 2) fun t => Subtype.ext (by
    have := AddSubgroup.torsionBy.nsmul_iff.mp t.2
    simp)

instance locM_finite : Finite (locM v) := inferInstanceAs (Finite SmallM)

instance locM_moduleFinite : Module.Finite (ZMod 2) (locM v) := Module.Finite.of_finite

instance Tv_moduleFinite : Module.Finite (ZMod 2) (Tv v) := Module.Finite.of_finite

theorem finrank_Tv : Module.finrank (ZMod 2) (Tv v) = 2 :=
  ZInQ.Contrib.CloudB3RC53.Mattuck.finrank_eq_two_of_card (card_Tv v)

/-- **The coefficient identification** `E₁₁(K̄_v)[2] ≅ M` (both carry the trivial action). -/
def kumIotaEquiv : Tv v ≃ₗ[ZMod 2] locM v :=
  LinearEquiv.ofFinrankEq (Tv v) (locM v) ((finrank_Tv v).trans smallM_finrank.symm)

def kumIota : Tv v →+ locM v := (kumIotaEquiv v).toLinearMap.toAddMonoidHom

theorem kumIota_injective : Function.Injective (kumIota v) := (kumIotaEquiv v).injective

theorem kumIota_equivariant (σ : Gloc SmallK v) (t : Tv v) :
    kumIota v (σ • t) = σ • kumIota v t := by
  rw [Tv_trivial v σ t, locM_smul]

/-- **The old Kummer condition at `v`**: Kummer cocycles of `E₁₁(K_v)` with coefficients in `M`,
together with the coboundaries. -/
abbrev kumU : GCx (ZMod 2) := kummerConditionIn (ZMod 2) (kumIota v) (kumIota_equivariant v)

abbrev kumI : GHom (kumU v) (natCx (contCochains (ZMod 2) (Gloc SmallK v) (locM v))) :=
  kummerConditionInι (ZMod 2) (kumIota v) (kumIota_equivariant v)

abbrev kumCC : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ := (kumU v).toCC

/-- The Kummer function of `E₁₁` is additive: the division-point defect is rational. -/
theorem kummerFun_add (P P' : (smallCurve (v.adicCompletion SmallK)).toAffine.Point)
    (σ : Gloc SmallK v) :
    kummerFun (v.adicCompletion SmallK) (smallCurve (v.adicCompletion SmallK)) 2 (P + P') σ =
      kummerFun (v.adicCompletion SmallK) (smallCurve (v.adicCompletion SmallK)) 2 P σ +
        kummerFun (v.adicCompletion SmallK) (smallCurve (v.adicCompletion SmallK)) 2 P' σ := by
  apply Subtype.ext
  simp only [AddSubgroup.coe_add, coe_kummerFun]
  set Q := divPt (v.adicCompletion SmallK) (smallCurve (v.adicCompletion SmallK)) 2 (P + P')
  set Q₁ := divPt (v.adicCompletion SmallK) (smallCurve (v.adicCompletion SmallK)) 2 P
  set Q₂ := divPt (v.adicCompletion SmallK) (smallCurve (v.adicCompletion SmallK)) 2 P'
  have hT : Q - Q₁ - Q₂ ∈ AddSubgroup.torsionBy
      (PtAlg (v.adicCompletion SmallK) (smallCurve (v.adicCompletion SmallK))) ((2 : ℕ) : ℤ) := by
    rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, nsmul_sub, nsmul_divPt, nsmul_divPt,
      nsmul_divPt, map_add]
    abel
  have hfix : σ • (Q - Q₁ - Q₂) = Q - Q₁ - Q₂ := by
    have := congrArg Subtype.val (Tv_trivial v σ ⟨_, hT⟩)
    rwa [coe_smul_torsAlg] at this
  have hQ : σ • Q = (Q - Q₁ - Q₂) + σ • Q₁ + σ • Q₂ := by
    conv_lhs => rw [show Q = (Q - Q₁ - Q₂) + Q₁ + Q₂ by abel]
    rw [smul_add, smul_add, hfix]
  rw [hQ]
  abel

theorem zmod2_two_zsmul {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (x : V) :
    (2 : ℤ) • x = 0 := by
  rw [two_zsmul, ← two_smul (ZMod 2) x]
  have : (2 : ZMod 2) = 0 := rfl
  rw [this, zero_smul]

/-- The Kummer cochains as an additive map on `E₁₁(K_v)`. -/
def kumCochainHom :
    (smallCurve (v.adicCompletion SmallK)).toAffine.Point →+
      contCochain (ZMod 2) (Gloc SmallK v) (locM v) 1 :=
  AddMonoidHom.mk' (fun P => kummerCocycleIn (kumIota v) (1 : ZMod 2) P) (fun P P' => by
    apply Subtype.ext
    funext g
    change (1 : ZMod 2) • kumIota v (kummerFun _ _ 2 (P + P') (g 0)) =
      (1 : ZMod 2) • kumIota v (kummerFun _ _ 2 P (g 0)) +
        (1 : ZMod 2) • kumIota v (kummerFun _ _ 2 P' (g 0))
    rw [kummerFun_add, map_add, smul_add])

/-- The Kummer cochains factor through `E₁₁(K_v)/2`. -/
def kumLambda :
    ModN (smallCurve (v.adicCompletion SmallK)).toAffine.Point 2 →ₗ[ZMod 2]
      contCochain (ZMod 2) (Gloc SmallK v) (locM v) 1 :=
  (Submodule.liftQ _ (kumCochainHom v).toIntLinearMap (by
    rintro _ ⟨R, rfl⟩
    rw [LinearMap.mem_ker]
    change kumCochainHom v ((2 : ℤ) • R) = 0
    rw [map_zsmul, zmod2_two_zsmul])).toAddMonoidHom.toZModLinearMap 2

theorem kumLambda_mk (P : (smallCurve (v.adicCompletion SmallK)).toAffine.Point) :
    kumLambda v (Submodule.Quotient.mk P) = kummerCocycleIn (kumIota v) (1 : ZMod 2) P :=
  rfl

theorem kummerZ'_le_range :
    kummerZ' (ZMod 2) (kumIota v) ≤ LinearMap.range (kumLambda v) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨a, P⟩, rfl⟩
  refine ⟨a • Submodule.Quotient.mk P, ?_⟩
  change kumLambda v (a • Submodule.Quotient.mk P) = kummerCocycleIn (kumIota v) a P
  rw [map_smul, kumLambda_mk, ← kummerCocycleIn_eq_smul]

end KummerPlace

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive

/-! ## The old Kummer row: finiteness and Mattuck's bound -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain WeierstrassCurve
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Contrib.RC53Assist.ResidualWitnessActive.LocalKummer
  ZInQ.Manuscript.RC.Limits

section KummerCounts

variable (v : HeightOneSpectrum (𝓞 SmallK))

theorem kum_X_subsingleton (m : ℕ) : Subsingleton ((kumCC v).X ((m + 2 : ℕ) : ℤ)) := by
  change Subsingleton ↥(⊥ : Submodule (ZMod 2)
    (contCochain (ZMod 2) (Gloc SmallK v) (locM v) (m + 2)))
  infer_instance

/-- The old Kummer condition has finite cohomology concentrated in degrees `0, 1`. -/
theorem good_kum (h28 : MilneADT_I_2_8) {p : ℕ} (hp : p.Prime)
    (hv : v.asIdeal ∈ primesAbove SmallK p) : Good (kumCC v) := by
  have hL := good_full h28 v hp hv
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · by_cases h0 : n = 0
    · subst h0
      have := hL.1 0
      have : IsIso (HomologicalComplex.homologyMap (GHom.toCC (kumI v)) 0) :=
        kummerConditionIn_isIso_homologyMap_zero (ZMod 2) (kumIota v) (kumIota_equivariant v)
      exact (asIso (HomologicalComplex.homologyMap (GHom.toCC (kumI v)) 0)).toLinearEquiv.symm.finiteDimensional
    by_cases h1 : n = 1
    · subst h1
      have := hL.1 1
      have hm : Mono (HomologicalComplex.homologyMap (GHom.toCC (kumI v)) 1) :=
        cocycleCondition_mono_homologyMap_one _ _
      exact Module.Finite.of_injective _ ((ModuleCat.mono_iff_injective _).1 hm)
    cases n with
    | ofNat m =>
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by simp only [Int.ofNat_eq_natCast] at h0 h1; omega⟩
      have := homology_subsingleton_of_X _ (kum_X_subsingleton v k)
      infer_instance
    | negSucc m =>
      have : Subsingleton ((kumCC v).X (Int.negSucc m)) := inferInstanceAs (Subsingleton PUnit.{1})
      have := homology_subsingleton_of_X _ this
      infer_instance
  · cases n with
    | ofNat m =>
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by simp only [Int.ofNat_eq_natCast] at hn; omega⟩
      exact homology_subsingleton_of_X _ (kum_X_subsingleton v k)
    | negSucc m =>
      have : Subsingleton ((kumCC v).X (Int.negSucc m)) := inferInstanceAs (Subsingleton PUnit.{1})
      exact homology_subsingleton_of_X _ this

/-- Transport of the Mattuck dimensions along the identification of the local curves. -/
theorem kummerResidualDim_eq :
    kummerResidualDim v (smallLocalModels v) =
      finrankTwoTorsion (smallCurve (v.adicCompletion SmallK)).toAffine.Point +
        Module.finrank (ZMod 2) (ModN (smallCurve (v.adicCompletion SmallK)).toAffine.Point 2) := by
  have key : ∀ W : WeierstrassCurve (v.adicCompletion SmallK), W = smallCurve _ →
      finrankTwoTorsion W.toAffine.Point + Module.finrank (ZMod 2) (ModN W.toAffine.Point 2) =
        finrankTwoTorsion (smallCurve (v.adicCompletion SmallK)).toAffine.Point +
          Module.finrank (ZMod 2) (ModN (smallCurve (v.adicCompletion SmallK)).toAffine.Point 2) := by
    rintro W rfl
    rfl
  exact key _ (smallLocal_baseChange v)

theorem finrankTwoTorsion_smallCurve :
    finrankTwoTorsion (smallCurve (v.adicCompletion SmallK)).toAffine.Point = 2 :=
  finrankTwoTorsion_eq_two (smallCurve_two_torsion _)

/-- `E₁₁(K_v)/2` is finite (Mattuck, at odd places and at the places above `2`). -/
theorem modN_finite :
    Module.Finite (ZMod 2) (ModN (smallCurve (v.adicCompletion SmallK)).toAffine.Point 2) := by
  have key : ∀ W : WeierstrassCurve (v.adicCompletion SmallK), W = smallCurve _ →
      Module.Finite (ZMod 2) (ModN W.toAffine.Point 2) →
        Module.Finite (ZMod 2) (ModN (smallCurve (v.adicCompletion SmallK)).toAffine.Point 2) := by
    rintro W rfl h
    exact h
  refine key _ (smallLocal_baseChange v) ?_
  by_cases h2 : (2 : 𝓞 SmallK) ∈ v.asIdeal
  · have hv : v.asIdeal ∈ primesAbove SmallK 2 :=
      (natCast_mem_asIdeal_iff SmallK Nat.prime_two v).mp (by exact_mod_cast h2)
    have hlo : v.asIdeal.LiesOver (vP two).asIdeal := by
      rw [vP_asIdeal]; exact hv.2
    have h := (finrank_two SmallK v (smallLocalModels v) (local_models_have_full_two_torsion v)).2
    apply Module.finite_of_finrank_pos
    rw [h]
    omega
  · have hc := card_modN_two_eq_card_twoTorsion v (smallLocalModels v) h2
    rw [local_models_have_full_two_torsion v] at hc
    have : Finite (ModN ((smallLocalModels v).baseChange (v.adicCompletion SmallK)).toAffine.Point 2) :=
      Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
    exact Module.Finite.of_finite

/-- The Kummer cocycles span a space of dimension at most `dim E₁₁(K_v)/2`. -/
theorem finrank_kum_H1_le :
    Module.finrank (ZMod 2) ((kumCC v).homology 1) ≤
      Module.finrank (ZMod 2) (ModN (smallCurve (v.adicCompletion SmallK)).toAffine.Point 2) := by
  have := modN_finite v
  set Z := kummerZ' (ZMod 2) (kumIota v)
  set hZ := kummerZ'_cocycle (ZMod 2) (kumIota v) (kumIota_equivariant v)
  rw [(kummerConditionInH1Iso (ZMod 2) (kumIota v) (kumIota_equivariant v)).toLinearEquiv.finrank_eq]
  let incl : Z →ₗ[ZMod 2] (kumU v).X 1 :=
    Submodule.inclusion (le_sup_left : Z ≤ Z ⊔ contB1 (ZMod 2) (Gloc SmallK v) (locM v))
  let q : Z →ₗ[ZMod 2] ((kumU v).X 1 ⧸ condB1 Z hZ) := (condB1 Z hZ).mkQ ∘ₗ incl
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hx : ((condOne Z hZ x : ↥(Z ⊔ contB1 (ZMod 2) (Gloc SmallK v) (locM v))) :
        contCochain (ZMod 2) (Gloc SmallK v) (locM v) 1) ∈
        Z ⊔ contB1 (ZMod 2) (Gloc SmallK v) (locM v) := (condOne Z hZ x).2
    obtain ⟨z, hz, b, hb, hzb⟩ := Submodule.mem_sup.1 hx
    refine ⟨⟨z, hz⟩, ?_⟩
    change Submodule.Quotient.mk (incl ⟨z, hz⟩) = Submodule.Quotient.mk x
    rw [Submodule.Quotient.eq, mem_condB1]
    have : (condOne Z hZ (incl ⟨z, hz⟩ - x) : contCochain (ZMod 2) (Gloc SmallK v) (locM v) 1) =
        -b := by
      change z - ((condOne Z hZ x : ↥(Z ⊔ contB1 (ZMod 2) (Gloc SmallK v) (locM v))) :
        contCochain (ZMod 2) (Gloc SmallK v) (locM v) 1) = -b
      rw [← hzb]
      abel
    rw [this]
    exact neg_mem hb
  have hfinR : Module.Finite (ZMod 2) (LinearMap.range (kumLambda v)) := inferInstance
  have hfinZ : Module.Finite (ZMod 2) Z :=
    Submodule.finiteDimensional_of_le (kummerZ'_le_range v)
  calc Module.finrank (ZMod 2) ((kumU v).X 1 ⧸ condB1 Z hZ)
      ≤ Module.finrank (ZMod 2) Z := LinearMap.finrank_le_finrank_of_surjective hq
    _ ≤ Module.finrank (ZMod 2) (LinearMap.range (kumLambda v)) :=
        Submodule.finrank_mono (kummerZ'_le_range v)
    _ ≤ _ := LinearMap.finrank_range_le _

theorem finrank_kum_H0 :
    Module.finrank (ZMod 2) ((kumCC v).homology 0) = 2 := by
  have : IsIso (HomologicalComplex.homologyMap (GHom.toCC (kumI v)) 0) :=
    kummerConditionIn_isIso_homologyMap_zero (ZMod 2) (kumIota v) (kumIota_equivariant v)
  rw [(asIso (HomologicalComplex.homologyMap (GHom.toCC (kumI v)) 0)).toLinearEquiv.finrank_eq]
  have h := finrank_full v 0
  change Module.finrank (ZMod 2) ((locCC v).homology ((0 : ℕ) : ℤ)) = 2
  rw [h, finrank_genLocH SmallK SmallS W2v v 0 (by omega)]
  exact hLoc_zero SmallK v

/-- **The old Kummer row**: the cohomology of the actual Kummer condition has total dimension at
most Mattuck's residual dimension `dim E(K_v)[2] + dim E(K_v)/2`. -/
theorem kum_dims_le :
    Module.finrank (ZMod 2) ((kumCC v).homology 0) +
        Module.finrank (ZMod 2) ((kumCC v).homology 1) +
        Module.finrank (ZMod 2) ((kumCC v).homology 2) ≤
      kummerResidualDim v (smallLocalModels v) := by
  have h2 : Module.finrank (ZMod 2) ((kumCC v).homology 2) = 0 := by
    have := homology_subsingleton_of_X _ (kum_X_subsingleton v 0)
    exact Module.finrank_zero_of_subsingleton
  rw [kummerResidualDim_eq, finrankTwoTorsion_smallCurve, finrank_kum_H0, h2, add_zero]
  have := finrank_kum_H1_le v
  omega

end KummerCounts

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive

/-! ## The condition table, the genuine local conditions and the residual model -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain WeierstrassCurve
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Contrib.RC53Assist.ResidualWitnessActive.LocalKummer
  ZInQ.Manuscript.RC.Limits

/-! ### The condition table and the genuine local conditions -/

/-- **The condition labels**: the relaxed derivative condition above the derivative prime `7`, the
old Kummer condition above the old primes `2, 3, 11` of `2N = 132`, the full condition at the
moving prime `5` (and, as junk, everywhere else). -/
def actCond (P : Ideal (𝓞 SmallK)) : LocalCondition :=
  if P ∈ primesAbove SmallK 7 then .derivRelaxed
  else if P ∈ primesAbove SmallK 2 ∨ P ∈ primesAbove SmallK 3 ∨ P ∈ primesAbove SmallK 11 then
    .oldKummer
  else .full

theorem actCond_derivative : ∀ P : Ideal (𝓞 SmallK), actCond P = .derivRelaxed →
    ∃ q ∈ actD, P ∈ primesAbove SmallK q := by
  intro P h
  unfold actCond at h
  split_ifs at h with h7 hk
  · exact ⟨7, by simp [actD], h7⟩

theorem actCond_full_torsion : ∀ w : HeightOneSpectrum (𝓞 SmallK), actCond w.asIdeal = .oldKummer →
    Nat.card (Submodule.torsionBy ℤ
      ((smallLocalModels w).baseChange (w.adicCompletion SmallK)).toAffine.Point 2) = 4 :=
  fun w _ => local_models_have_full_two_torsion w

/-- The local condition complex of each row. -/
def condCx (v : HeightOneSpectrum (𝓞 SmallK)) :
    LocalCondition → CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ
  | .derivRelaxed => relCC v
  | .oldKummer => kumCC v
  | .unramified => locCC v
  | .zero => locCC v
  | .full => locCC v
  | .derivStrict => locCC v
  | .derivFiniteOrSingular => locCC v

/-- The local condition maps: the inclusion of `τ≤1`, the inclusion of the Kummer subcomplex,
the identity. -/
def condTo (v : HeightOneSpectrum (𝓞 SmallK)) : ∀ c : LocalCondition, condCx v c ⟶ locCC v
  | .derivRelaxed => relaxedToLocal (Gloc SmallK v) (locM v)
  | .oldKummer => GHom.toCC (kumI v)
  | .unramified => 𝟙 _
  | .zero => 𝟙 _
  | .full => 𝟙 _
  | .derivStrict => 𝟙 _
  | .derivFiniteOrSingular => 𝟙 _

/-- **The genuine local conditions** at the places of `S`, by row. -/
def actΔ : GaloisLocalConditions SmallK SmallS (ZMod 2) SmallM :=
  localConditionsOfCC (fun v : Places SmallK SmallS => condCx v.1 (actCond v.1.asIdeal))
    (fun v => condTo v.1 (actCond v.1.asIdeal))

theorem good_cond (h28 : MilneADT_I_2_8) (v : Places SmallK SmallS) (c : LocalCondition) :
    Good (condCx v.1 c) := by
  obtain ⟨p, -, hp, hv⟩ := place_above v
  cases c
  · exact good_kum v.1 h28 hp hv
  · exact good_full h28 v.1 hp hv
  · exact good_full h28 v.1 hp hv
  · exact good_full h28 v.1 hp hv
  · exact good_full h28 v.1 hp hv
  · exact good_full h28 v.1 hp hv
  · exact good_rel h28 v.1 hp hv

theorem good_U (h28 : MilneADT_I_2_8) (v : Places SmallK SmallS) : Good (actΔ.U v).toCC :=
  good_of_iso (ofCCIso _) (good_cond h28 v _)

theorem good_L (h28 : MilneADT_I_2_8) (v : Places SmallK SmallS) :
    Good (localCx (ZMod 2) (GKS SmallK SmallS) (fun v : Places SmallK SmallS => Gloc SmallK v.1)
      (fun v => locMap SmallK SmallS v.1) SmallM v).toCC := by
  obtain ⟨p, -, hp, hv⟩ := place_above v
  exact good_full h28 v.1 hp hv

/-! ### The formal residual model of the genuine Selmer data -/

/-- **The residual model**: global cohomology, condition cohomology and local cohomology, with the
maps induced on cohomology. -/
abbrev actSel : SelData (ZMod 2) :=
  formalData (GKS SmallK SmallS) (fun v : Places SmallK SmallS => Gloc SmallK v.1)
    (fun v => locMap SmallK SmallS v.1) SmallM actΔ

/-- The genuine smaller-support Selmer data. -/
abbrev actGenuine : SelData (ZMod 2) :=
  selData (ZMod 2) (GKS SmallK SmallS) (fun v : Places SmallK SmallS => Gloc SmallK v.1)
    (fun v => locMap SmallK SmallS v.1) SmallM actΔ

/-- **The actual cochain map from the residual cone to the genuine Selmer complex.** -/
abbrev actPP : (selCx actSel).toCC ⟶ (selCx actGenuine).toCC :=
  GHom.toCC (formalMap (GKS SmallK SmallS) (fun v : Places SmallK SmallS => Gloc SmallK v.1)
    (fun v => locMap SmallK SmallS v.1) SmallM actΔ).sel

theorem actPP_quasiIso : QuasiIso actPP :=
  formalMap_quasiIso (GKS SmallK SmallS) (fun v : Places SmallK SmallS => Gloc SmallK v.1)
    (fun v => locMap SmallK SmallS v.1) SmallM actΔ

theorem actSel_G_finite (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (n : ℤ) :
    Module.Finite (ZMod 2) (actSel.G.X n) :=
  smallGlobal_finite h410 h51 n

theorem actSel_U_finite (h28 : MilneADT_I_2_8) (n : ℤ) :
    Module.Finite (ZMod 2) (actSel.U.X n) := by
  change Module.Finite (ZMod 2) (∀ v : Places SmallK SmallS, (actΔ.U v).toCC.homology n)
  have := fun v => (good_U h28 v).1 n
  infer_instance

theorem actSel_L_finite (h28 : MilneADT_I_2_8) (n : ℤ) :
    Module.Finite (ZMod 2) (actSel.L.X n) := by
  change Module.Finite (ZMod 2) (∀ v : Places SmallK SmallS,
    (localCx (ZMod 2) (GKS SmallK SmallS) (fun v : Places SmallK SmallS => Gloc SmallK v.1)
      (fun v => locMap SmallK SmallS v.1) SmallM v).toCC.homology n)
  have := fun v => (good_L h28 v).1 n
  infer_instance

theorem actSel_U_off (h28 : MilneADT_I_2_8) (n : ℤ) (hn : n < 0 ∨ 2 < n) :
    Subsingleton (actSel.U.X n) := by
  change Subsingleton (∀ v : Places SmallK SmallS, (actΔ.U v).toCC.homology n)
  have := fun v => (good_U h28 v).2 n hn
  infer_instance

theorem actSel_L_off (h28 : MilneADT_I_2_8) (n : ℤ) (hn : n < 0 ∨ 2 < n) :
    Subsingleton (actSel.L.X n) := by
  change Subsingleton (∀ v : Places SmallK SmallS,
    (localCx (ZMod 2) (GKS SmallK SmallS) (fun v : Places SmallK SmallS => Gloc SmallK v.1)
      (fun v => locMap SmallK SmallS v.1) SmallM v).toCC.homology n)
  have := fun v => (good_L h28 v).2 n hn
  infer_instance

theorem actP_X_subsingleton (h410 : MilneADT_I_4_10_totallyComplex) (h28 : MilneADT_I_2_8)
    (n : ℤ) (hn : n < 0 ∨ 3 < n) : Subsingleton ((selCx actSel).toCC.X n) := by
  have h1 : Subsingleton (actSel.G.X n) := smallGlobal_off h410 n (by omega)
  have h2 : Subsingleton (actSel.U.X n) := actSel_U_off h28 n (by omega)
  have h3 : Subsingleton (actSel.L.X (n - 1)) := actSel_L_off h28 (n - 1) (by omega)
  change Subsingleton (actSel.G.X n × actSel.U.X n × actSel.L.X (n - 1))
  infer_instance

theorem actP_ge (h410 : MilneADT_I_4_10_totallyComplex) (h28 : MilneADT_I_2_8) :
    (selCx actSel).toCC.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  have := actP_X_subsingleton h410 h28 n (Or.inl hn)
  exact ModuleCat.isZero_of_subsingleton _

theorem actP_le (h410 : MilneADT_I_4_10_totallyComplex) (h28 : MilneADT_I_2_8) :
    (selCx actSel).toCC.IsStrictlyLE 3 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  have := actP_X_subsingleton h410 h28 n (Or.inr hn)
  exact ModuleCat.isZero_of_subsingleton _

theorem actP_finite (h410 : MilneADT_I_4_10_totallyComplex) (h51 : MilneADT_I_5_1_totallyComplex)
    (h28 : MilneADT_I_2_8) (n : ℤ) : Module.Finite (ZMod 2) ((selCx actSel).toCC.X n) := by
  have := actSel_G_finite h410 h51 n
  have := actSel_U_finite h28 n
  have := actSel_L_finite h28 (n - 1)
  change Module.Finite (ZMod 2) (actSel.G.X n × actSel.U.X n × actSel.L.X (n - 1))
  infer_instance

/-- Every degree with nonzero global cohomology is counted. -/
def actDegrees : Finset ℤ := Finset.Icc 0 2

/-- The global part in the counted degrees is the genuine global cohomology. -/
def actEG (n : ℤ) (hn : n ∈ actDegrees) : actSel.G.X n ≃ₗ[ZMod 2]
    genH SmallK SmallS n.toNat := by
  change smallGlobal.toCC.homology n ≃ₗ[ZMod 2] _
  have h0 : 0 ≤ n := (Finset.mem_Icc.mp hn).1
  have hcast : (n.toNat : ℤ) = n := by omega
  rw [← hcast]
  exact smallGlobalHEquiv n.toNat

/-- The global part in the counted degrees is the cohomology of the actual residual module. -/
def actEGact (n : ℤ) (hn : n ∈ actDegrees) : actSel.G.X n ≃ₗ[ZMod 2]
    contCohomology (ZMod 2) (GKS SmallK SmallS) SmallM n.toNat := by
  change smallGlobal.toCC.homology n ≃ₗ[ZMod 2] _
  have h0 : 0 ≤ n := (Finset.mem_Icc.mp hn).1
  have hcast : (n.toNat : ℤ) = n := by omega
  rw [← hcast]
  exact smallActualHEquiv n.toNat

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive

/-! ## The condition and local parts: `hUm` and `hLm` -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain WeierstrassCurve
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Contrib.RC53Assist.ResidualWitnessActive.LocalKummer
  ZInQ.Manuscript.RC.Limits

noncomputable instance : Fintype (Places SmallK SmallS) := Fintype.ofFinite _

/-! ### Sums over the places of `S` -/

theorem charged_prime : ∀ p ∈ chargedPrimes 66 5 actD, p.Prime :=
  prime_of_mem_chargedPrimes (by decide) actD_prime

/-- The places of `S` are exactly the prime ideals above the charged primes. -/
theorem places_image :
    (chargedPrimes 66 5 actD).biUnion (fun p => (primesAbove_finite (K := SmallK) p).toFinset) =
      Finset.univ.image (fun v : Places SmallK SmallS => v.1.asIdeal) := by
  ext P
  simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨p, hp, hP⟩
    have hpP := charged_prime p hp
    have hne : P ≠ ⊥ := ne_bot_of_mem_primesAbove SmallK hpP.ne_zero hP
    exact ⟨⟨⟨P, hP.1, hne⟩, ⟨p, hp, (natCast_mem_asIdeal_iff SmallK hpP ⟨P, hP.1, hne⟩).mpr hP⟩⟩,
      rfl⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨p, hp, -, hv⟩ := place_above v
    exact ⟨p, hp, hv⟩

theorem places_disjoint : Set.PairwiseDisjoint (↑(chargedPrimes 66 5 actD) : Set ℕ)
    (fun p => (primesAbove_finite (K := SmallK) p).toFinset) := by
  intro p hp q hq hpq
  rw [Function.onFun, Finset.disjoint_left]
  intro P hPp hPq
  rw [Set.Finite.mem_toFinset] at hPp hPq
  have hpP := charged_prime p hp
  have hqP := charged_prime q hq
  have hne : P ≠ ⊥ := ne_bot_of_mem_primesAbove SmallK hpP.ne_zero hPp
  have h1 := (natCast_mem_asIdeal_iff SmallK hpP ⟨P, hPp.1, hne⟩).mpr hPp
  have h2 := (natCast_mem_asIdeal_iff SmallK hqP ⟨P, hPp.1, hne⟩).mpr hPq
  exact hpq (Genus.prime_eq_of_mem hPp.1.ne_top hpP hqP h1 h2)

/-- A sum over the places of `S` is the sum over the charged primes and the places above them. -/
theorem sum_places (F : Ideal (𝓞 SmallK) → ℕ) :
    ∑ v : Places SmallK SmallS, F v.1.asIdeal =
      ∑ p ∈ chargedPrimes 66 5 actD, ∑ P ∈ (primesAbove_finite (K := SmallK) p).toFinset, F P := by
  rw [← Finset.sum_biUnion places_disjoint, places_image, Finset.sum_image]
  intro v _ w _ h
  exact Subtype.ext (HeightOneSpectrum.ext h)

theorem sum_actDegrees (f : ℤ → ℕ) : ∑ n ∈ actDegrees, f n = f 0 + f 1 + f 2 := by
  rw [show actDegrees = {0, 1, 2} by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem actCond_cases (P : Ideal (𝓞 SmallK)) :
    actCond P = .derivRelaxed ∨ actCond P = .oldKummer ∨ actCond P = .full := by
  unfold actCond
  split_ifs <;> simp

/-! ### The condition part: `hUm` -/

theorem finrank_actU (h28 : MilneADT_I_2_8) (n : ℤ) :
    Module.finrank (ZMod 2) (actSel.U.X n) =
      ∑ v : Places SmallK SmallS, Module.finrank (ZMod 2) ((actΔ.U v).toCC.homology n) := by
  have := fun v => (good_U h28 v).1 n
  change Module.finrank (ZMod 2) (∀ v : Places SmallK SmallS, (actΔ.U v).toCC.homology n) = _
  exact Module.finrank_pi_fintype (ZMod 2)

theorem finrank_actU_place (v : Places SmallK SmallS) (n : ℤ) :
    Module.finrank (ZMod 2) ((actΔ.U v).toCC.homology n) =
      Module.finrank (ZMod 2) ((condCx v.1 (actCond v.1.asIdeal)).homology n) :=
  (HomologicalComplex.homologyMapIso (ofCCIso _) n).toLinearEquiv.finrank_eq

/-- **The condition dimensions at one place**, from the genuine condition complexes: equality for
the full and relaxed derivative rows, Mattuck's bound for the old Kummer row. -/
theorem place_U_dims (v : Places SmallK SmallS) :
    ∑ n ∈ actDegrees, Module.finrank (ZMod 2) ((actΔ.U v).toCC.homology n) ≤
      genCondDimFun2 SmallK SmallS actCond
        (kummerDimOfCurves SmallK smallLocalModels (kd2OfCurves SmallK smallLocalModels))
        v.1.asIdeal := by
  rw [sum_actDegrees, finrank_actU_place, finrank_actU_place, finrank_actU_place]
  unfold genCondDimFun2
  rw [dite_eq_left ⟨v.1.isPrime, v.1.ne_bot⟩]
  rcases actCond_cases v.1.asIdeal with hc | hc | hc
  · rw [hc]
    have h2 : Module.finrank (ZMod 2) ((relCC v.1).homology 2) = 0 := by
      have := homology_subsingleton_of_X 2 (relCC_X_subsingleton v.1 2 (by decide) (by decide))
      exact Module.finrank_zero_of_subsingleton
    change Module.finrank (ZMod 2) ((relCC v.1).homology 0) +
        Module.finrank (ZMod 2) ((relCC v.1).homology 1) +
        Module.finrank (ZMod 2) ((relCC v.1).homology 2) ≤
      Module.finrank (ZMod 2) ((relaxedCx (Gloc SmallK v.1)
          (locMod SmallK SmallS W2v v.1)).homology 0) +
        Module.finrank (ZMod 2) ((relaxedCx (Gloc SmallK v.1)
          (locMod SmallK SmallS W2v v.1)).homology 1)
    rw [h2, add_zero, finrank_rel, finrank_relaxedCx]
  · rw [hc]
    have hk := kum_dims_le v.1
    change Module.finrank (ZMod 2) ((kumCC v.1).homology 0) +
        Module.finrank (ZMod 2) ((kumCC v.1).homology 1) +
        Module.finrank (ZMod 2) ((kumCC v.1).homology 2) ≤
      kummerDimOfCurves SmallK smallLocalModels (kd2OfCurves SmallK smallLocalModels) v.1.asIdeal
    unfold kummerDimOfCurves
    rw [dite_eq_left ⟨v.1.isPrime, v.1.ne_bot⟩]
    split_ifs
    · unfold kd2OfCurves
      rw [dite_eq_left ⟨v.1.isPrime, v.1.ne_bot⟩]
      exact hk
    · exact hk
  · rw [hc]
    change Module.finrank (ZMod 2) ((locCC v.1).homology ((0 : ℕ) : ℤ)) +
        Module.finrank (ZMod 2) ((locCC v.1).homology ((1 : ℕ) : ℤ)) +
        Module.finrank (ZMod 2) ((locCC v.1).homology ((2 : ℕ) : ℤ)) ≤
      genLocDim SmallK SmallS v.1
    rw [finrank_full, finrank_full, finrank_full, genLocDim]
    simp [Finset.sum_range_succ]

/-- **`hUm` with nonzero condition parts**: the condition part of the residual model is bounded by
the genuine condition dimensions at the places above the charged primes. -/
theorem act_hUm (h28 : MilneADT_I_2_8) :
    ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.U.X n) ≤
      ∑ p ∈ chargedPrimes 66 5 actD,
        condSum SmallK (genCondDimFun2 SmallK SmallS actCond
          (kummerDimOfCurves SmallK smallLocalModels (kd2OfCurves SmallK smallLocalModels))) p := by
  simp only [finrank_actU h28]
  rw [Finset.sum_comm]
  calc ∑ v : Places SmallK SmallS, ∑ n ∈ actDegrees,
        Module.finrank (ZMod 2) ((actΔ.U v).toCC.homology n)
      ≤ ∑ v : Places SmallK SmallS, genCondDimFun2 SmallK SmallS actCond
          (kummerDimOfCurves SmallK smallLocalModels (kd2OfCurves SmallK smallLocalModels))
          v.1.asIdeal := Finset.sum_le_sum fun v _ => place_U_dims v
    _ = _ := sum_places _

/-! ### The local part: `hLm` -/

theorem finrank_actL (h28 : MilneADT_I_2_8) (n : ℤ) :
    Module.finrank (ZMod 2) (actSel.L.X n) =
      ∑ v : Places SmallK SmallS, Module.finrank (ZMod 2) ((locCC v.1).homology n) := by
  have := fun v => (good_L h28 v).1 n
  change Module.finrank (ZMod 2) (∀ v : Places SmallK SmallS, (locCC v.1).homology n) = _
  exact Module.finrank_pi_fintype (ZMod 2)

theorem place_L_dims (v : Places SmallK SmallS) :
    ∑ n ∈ actDegrees, Module.finrank (ZMod 2) ((locCC v.1).homology (n - 1)) ≤
      genLocDim SmallK SmallS v.1 := by
  rw [sum_actDegrees]
  have hneg : Module.finrank (ZMod 2) ((locCC v.1).homology ((0 : ℤ) - 1)) = 0 := by
    have := natHomology_negative (contCochains (ZMod 2) (Gloc SmallK v.1) (locM v.1))
      ((0 : ℤ) - 1) (by norm_num)
    exact Module.finrank_zero_of_subsingleton
  rw [hneg]
  change 0 + Module.finrank (ZMod 2) ((locCC v.1).homology ((0 : ℕ) : ℤ)) +
      Module.finrank (ZMod 2) ((locCC v.1).homology ((1 : ℕ) : ℤ)) ≤ genLocDim SmallK SmallS v.1
  rw [finrank_full, finrank_full, genLocDim]
  simp [Finset.sum_range_succ]

/-- The local dimension as a function of the prime ideal (junk `0` off primes). -/
def locDimFun (P : Ideal (𝓞 SmallK)) : ℕ :=
  if h : P.IsPrime ∧ P ≠ ⊥ then genLocDim SmallK SmallS ⟨P, h.1, h.2⟩ else 0

theorem locDimFun_place (v : Places SmallK SmallS) :
    locDimFun v.1.asIdeal = genLocDim SmallK SmallS v.1 := by
  rw [locDimFun, dite_eq_left ⟨v.1.isPrime, v.1.ne_bot⟩]

theorem genLocSum_eq (p : ℕ) (hp : p ∈ chargedPrimes 66 5 actD) :
    genLocSum SmallK SmallS p =
      ∑ P ∈ (primesAbove_finite (K := SmallK) p).toFinset, locDimFun P := by
  have hpP := charged_prime p hp
  rw [genLocSum, dite_eq_left hpP,
    ← Finset.sum_attach (primesAbove_finite (K := SmallK) p).toFinset locDimFun]
  refine Finset.sum_congr rfl fun P _ => ?_
  have hP := (primesAbove_finite (K := SmallK) p).mem_toFinset.mp P.2
  rw [locDimFun, dite_eq_left ⟨hP.1, ne_bot_of_mem_primesAbove SmallK hpP.ne_zero hP⟩]
  rfl

/-- **`hLm` with nonzero local parts**: the local part of the residual model is bounded by the
genuine local cohomology dimensions at the places above the charged primes. -/
theorem act_hLm (h28 : MilneADT_I_2_8) :
    ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes 66 5 actD, genLocSum SmallK SmallS p := by
  simp only [finrank_actL h28]
  rw [Finset.sum_comm, Finset.sum_congr rfl genLocSum_eq, ← sum_places locDimFun]
  exact Finset.sum_le_sum fun v _ => (locDimFun_place v).symm ▸ place_L_dims v

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive

/-! ## The support change, the change of condition, the minimal model and the constructors -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain WeierstrassCurve
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Contrib.CloudB3RC53.ResidualTransfer
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Contrib.RC53Assist.ResidualWitnessActive.LocalKummer
  ZInQ.Manuscript.RC.Limits
  ZInQ.Manuscript.RC.HeegnerAlgebra

/-! ### The support change with a nonempty active support -/

/-- **The genuine support change** from `S` to `S' = S ∪ {places above 13}`, with the unramified
conditions at the new places and the canonical factorizations through `G_q / I_q`. -/
abbrev actT : SupportChangeData (ZMod 2) :=
  galoisSupportData SmallK smallS_sub (ZMod 2) SmallM (urFactor SmallK) (urFactor_spec SmallK) actΔ

/-- The old conditions, retained at the places of `S`. -/
abbrev actA : GCx (ZMod 2) := piCx actΔ.U

/-- The unramified conditions `C^•_cont(G_q/I_q, M)` at the active places `q ∈ S' − S`. -/
abbrev actB : GCx (ZMod 2) := piCx fun q : NewPlaces SmallK SmallS SmallS' =>
  natCx (contCochains (ZMod 2) (GUr SmallK q.1) (ResMod (urFactor SmallK q) SmallM))

/-! ### A change of condition at the active places with acyclic quotient -/

section Thick

variable {k : Type} [CommRing k]

/-- The second projection `A ⊕ B → B`. -/
def prodSnd (A B : GCx k) : GHom (prodCx A B) B where
  f i j h := by subst h; exact LinearMap.snd k _ _
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    rfl

/-- The thickened condition map, `(a, (b, (e, z))) ↦ ι (a, b) + ι (0, e)`: the active condition
`B` becomes `B ⊕ Cone(id_B)`. -/
def activeThickι (A B L : GCx k) (ι : GHom (prodCx A B) L) :
    GHom (prodCx A (prodCx B (coneCx (idGHom B)))) L where
  f i j h := (ι.f i j h).comp ((LinearMap.fst k _ _).prod
      ((LinearMap.fst k _ _).comp (LinearMap.snd k _ _))) +
    (ι.f i j h).comp ((0 : (A.X i × (B.X i × (coneCx (idGHom B)).X i)) →ₗ[k] A.X i).prod
      ((LinearMap.fst k _ _).comp ((LinearMap.snd k _ _).comp (LinearMap.snd k _ _))))
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    obtain ⟨a, b, e, z⟩ := c
    change ι.f i₁ j₁ hj (A.d i i₁ h₁ a, B.d i i₁ h₁ b) + ι.f i₁ j₁ hj (0, B.d i i₁ h₁ e) =
      L.d j j₁ h₂ (ι.f i j hij (a, b) + ι.f i j hij (0, e))
    have e1 := ι.comm i i₁ j j₁ hij h₁ h₂ hj (a, b)
    have e2 := ι.comm i i₁ j j₁ hij h₁ h₂ hj (0, e)
    have hd : (prodCx A B).d i i₁ h₁ ((0 : A.X i), e) = (0, B.d i i₁ h₁ e) :=
      Prod.ext (show A.d i i₁ h₁ 0 = 0 from map_zero _) rfl
    rw [hd] at e2
    rw [map_add, ← e2]
    exact congrArg (· + ι.f i₁ j₁ hj (0, B.d i i₁ h₁ e)) e1

/-- The inclusion `(a, b) ↦ (a, (b, 0))`. -/
def activeF (A B : GCx k) : GHom (prodCx A B) (prodCx A (prodCx B (coneCx (idGHom B)))) :=
  prodMapG (idGHom A) (prodLift (idGHom B) (zeroGHom _ _))

/-- The quotient `(a, (b, c)) ↦ c`, onto the cone of the identity of the active condition. -/
def activeG (A B : GCx k) :
    GHom (prodCx A (prodCx B (coneCx (idGHom B)))) (coneCx (idGHom B)) :=
  ghomComp (prodSnd A _) (prodSnd B _)

theorem sameGHom {A B : GCx k} (f g : GHom A B)
    (h : ∀ i (x : A.X i), f.f i i rfl x = g.f i i rfl x) : f = g := by
  obtain ⟨ff, hf⟩ := f
  obtain ⟨gg, hg⟩ := g
  have he : ff = gg := by
    funext i j hij
    subst hij
    ext x
    exact h i x
  subst he
  rfl

theorem activeThick_restrict (A B L : GCx k) (ι : GHom (prodCx A B) L) :
    ghomComp (activeF A B) (activeThickι A B L ι) = ι := by
  refine sameGHom _ _ fun n c => ?_
  obtain ⟨a, b⟩ := c
  change ι.f n n rfl ((idGHom A).f n n rfl a, (idGHom B).f n n rfl b) +
      ι.f n n rfl (0, ((0 : (coneCx (idGHom B)).X n)).1) = ι.f n n rfl (a, b)
  have h0 : ((0 : A.X n), ((0 : (coneCx (idGHom B)).X n)).1) = 0 := rfl
  rw [h0, map_zero, add_zero]
  rfl

theorem activeFG (A B : GCx k) (i : ℤ) (u : (prodCx A B).X i) :
    (activeG A B).f i i rfl ((activeF A B).f i i rfl u) = 0 := rfl

theorem activeF_injective (A B : GCx k) (i : ℤ) : Function.Injective ((activeF A B).f i i rfl) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun c => c.2.1) h
  exact Prod.ext h1 h2

theorem activeG_surjective (A B : GCx k) (i : ℤ) :
    Function.Surjective ((activeG A B).f i i rfl) :=
  fun w => ⟨(0, 0, w), rfl⟩

theorem activeExact (A B : GCx k) (i : ℤ) (u : (prodCx A (prodCx B (coneCx (idGHom B)))).X i)
    (hu : (activeG A B).f i i rfl u = 0) : ∃ u', (activeF A B).f i i rfl u' = u := by
  obtain ⟨a, b, c⟩ := u
  refine ⟨(a, b), ?_⟩
  change ((a, b, 0) : A.X i × B.X i × (coneCx (idGHom B)).X i) = (a, b, c)
  rw [show c = 0 from hu]

theorem activeW_acyclic (B : GCx k) : (coneCx (idGHom B)).toCC.Acyclic :=
  (acyclic_toCC_iff _).2 (coneCx_id_acyclic _)

end Thick

/-- **The original-support data**: the retained old conditions at `S`, and at the active places the
unramified condition thickened by the contractible cone of its identity. -/
def actFull : SelData (ZMod 2) where
  G := actT.Dp.G
  U := prodCx actA (prodCx actB (coneCx (idGHom actB)))
  L := actT.Dp.L
  res := actT.Dp.res
  ι := activeThickι actA actB actT.Dp.L actT.Dp.ι

/-- The quotient of the change of condition: the cone of the identity of the active conditions. -/
abbrev actW : GCx (ZMod 2) := coneCx (idGHom actB)

abbrev actF : GHom actT.Dp.U actFull.U := activeF actA actB

abbrev actG : GHom actFull.U actW := activeG actA actB

theorem act_fg (i : ℤ) (u : actT.Dp.U.X i) : actG.f i i rfl (actF.f i i rfl u) = 0 :=
  activeFG actA actB i u

theorem act_inj (i : ℤ) : Function.Injective (actF.f i i rfl) := activeF_injective actA actB i

theorem act_surj (i : ℤ) : Function.Surjective (actG.f i i rfl) := activeG_surjective actA actB i

theorem act_ex (i : ℤ) (u : actFull.U.X i) (hu : actG.f i i rfl u = 0) :
    ∃ u', actF.f i i rfl u' = u :=
  activeExact actA actB i u hu

theorem act_hW : actW.toCC.Acyclic := activeW_acyclic actB

theorem act_hDp : actT.Dp = restrictData actFull actF := by
  have hi : ghomComp actF actFull.ι = actT.Dp.ι :=
    activeThick_restrict actA actB actT.Dp.L actT.Dp.ι
  change actT.Dp = (⟨actT.Dp.G, actT.Dp.U, actT.Dp.L, actT.Dp.res,
    ghomComp actF actFull.ι⟩ : SelData (ZMod 2))
  rw [hi]

/-! ### The minimal model of the original-support complex -/

theorem homology_finite_of_X {C : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ} (n : ℤ)
    [Module.Finite (ZMod 2) (C.X n)] : Module.Finite (ZMod 2) (C.homology n) := by
  have : Module.Finite (ZMod 2) (C.cycles n) :=
    Module.Finite.of_injective _ ((ModuleCat.mono_iff_injective (C.iCycles n)).1 inferInstance)
  exact Module.Finite.of_surjective _ ((ModuleCat.epi_iff_surjective (C.homologyπ n)).1 inferInstance)

/-- **The minimal model** `L`: the cohomology of the residual cone, with zero differential. -/
abbrev actL : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ :=
  (homologyModel (selCx actSel).toCC).toCC

/-- The actual map from the minimal model to the genuine original-support complex: the
representatives, the residual comparison, the genuine support change and the change of
condition. -/
def actPL : actL ⟶ (selCx actFull).toCC :=
  homologyModelTo (selCx actSel).toCC ≫ actPP ≫ GHom.toCC (supportMap actT) ≫
    (eqToIso (congrArg (fun D => (selCx D).toCC) act_hDp)).hom ≫
    GHom.toCC (changeMap actFull actF)

theorem actPL_quasiIso (h788 : NekovarProp788ii SmallK) : QuasiIso actPL := by
  have h1 := homologyModelTo_quasiIso (selCx actSel).toCC
  have h2 := actPP_quasiIso
  have h3 : QuasiIso (GHom.toCC (supportMap actT)) :=
    supportChange_of_print SmallK h788 smallS_sub 2 smallSetting smallS'_finite
      (urFactor SmallK) (urFactor_spec SmallK) actΔ
  have hSE := relaxedQuotientNode_proof (ZMod 2) actFull actT.Dp.U actW actF actG
    act_fg act_inj act_surj act_ex
  have h4 : QuasiIso (GHom.toCC (changeMap actFull actF)) :=
    quasiIso_f_of_shortExact_acyclic (E := changeSES actFull actF actG act_fg) hSE act_hW
  unfold actPL
  infer_instance

theorem actL_X_subsingleton (h410 : MilneADT_I_4_10_totallyComplex) (h28 : MilneADT_I_2_8)
    (n : ℤ) (hn : n < 0 ∨ 3 < n) : Subsingleton (actL.X n) :=
  homology_subsingleton_of_X n (actP_X_subsingleton h410 h28 n hn)

theorem actL_ge (h410 : MilneADT_I_4_10_totallyComplex) (h28 : MilneADT_I_2_8) :
    actL.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  have := actL_X_subsingleton h410 h28 n (Or.inl hn)
  exact ModuleCat.isZero_of_subsingleton _

theorem actL_le (h410 : MilneADT_I_4_10_totallyComplex) (h28 : MilneADT_I_2_8) :
    actL.IsStrictlyLE 3 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  have := actL_X_subsingleton h410 h28 n (Or.inr hn)
  exact ModuleCat.isZero_of_subsingleton _

theorem actL_finite (h410 : MilneADT_I_4_10_totallyComplex) (h51 : MilneADT_I_5_1_totallyComplex)
    (h28 : MilneADT_I_2_8) (n : ℤ) : Module.Finite (ZMod 2) (actL.X n) := by
  have := actP_finite h410 h51 h28 n
  exact homology_finite_of_X (C := (selCx actSel).toCC) n

theorem actL_minimal (i j : ℤ) (x : actL.X i) :
    (actL.d i j).hom x ∈ IsLocalRing.maximalIdeal (ZMod 2) • (⊤ : Submodule (ZMod 2) (actL.X j)) := by
  rw [homologyModel_d]
  exact Submodule.zero_mem _

/-! ### The infinite place -/

/-- A complex infinite place. -/
def smallInfinitePlace : InfinitePlace SmallK := Classical.arbitrary _

theorem smallInfinitePlace_complex : smallInfinitePlace.IsComplex := by
  apply InfinitePlace.not_isReal_iff_isComplex.mp
  intro hw
  let f : SmallK →+* ℝ := InfinitePlace.embedding_of_isReal hw
  have hs : (smallAlpha : SmallK) ^ 2 = -1 :=
    congrArg (fun x : 𝓞 SmallK => (x : SmallK)) smallAlpha_sq
  have h := congrArg f hs
  rw [map_pow, map_neg, map_one] at h
  have hpos := sq_nonneg (f (smallAlpha : SmallK))
  linarith

/-! ### The two constructors -/

/-- **The genuine constructor on the active-support instance.** -/
def activeGenuineCounts (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) : ResidualRankCounts := by
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.G.X n) := actSel_G_finite h410 h51
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.U.X n) := actSel_U_finite h28
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.L.X n) := actSel_L_finite h28
  letI : (selCx actSel).toCC.IsStrictlyGE 0 := actP_ge h410 h28
  letI : (selCx actSel).toCC.IsStrictlyLE 3 := actP_le h410 h28
  letI : QuasiIso actPP := actPP_quasiIso
  letI : actL.IsStrictlyGE 0 := actL_ge h410 h28
  letI : actL.IsStrictlyLE 3 := actL_le h410 h28
  letI : ∀ n, Module.Finite (ZMod 2) (actL.X n) := actL_finite h410 h51 h28
  letI : QuasiIso actPL := actPL_quasiIso h788
  exact ZInQ.Contrib.CloudB3RC53.Mattuck.residualRankCounts_genuine
    SmallK smallLocalModels h410 h51 h28 h23 h788 (-1) smallAlpha smallAlpha_radicand
    smallK_complex 66 (by decide) 0 (by simp) 5 (by decide) actD actD_prime actD_odd
    actCond actCond_derivative actCond_full_torsion smallInfinitePlace smallInfinitePlace_complex
    SmallS actSel actDegrees (Finset.Subset.refl _) actEG (act_hUm h28) (act_hLm h28)
    smallS_sub 2 smallSetting smallS'_finite SmallM (urFactor SmallK) (urFactor_spec SmallK) actΔ
    actFull actW actF actG act_hDp act_fg act_inj act_surj act_ex act_hW 0 3 actPP actL
    actL_minimal actPL

/-- **The actual-coefficient constructor on the same instance.** -/
def activeActualCounts (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) : ResidualRankCounts := by
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.G.X n) := actSel_G_finite h410 h51
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.U.X n) := actSel_U_finite h28
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.L.X n) := actSel_L_finite h28
  letI : (selCx actSel).toCC.IsStrictlyGE 0 := actP_ge h410 h28
  letI : (selCx actSel).toCC.IsStrictlyLE 3 := actP_le h410 h28
  letI : QuasiIso actPP := actPP_quasiIso
  letI : actL.IsStrictlyGE 0 := actL_ge h410 h28
  letI : actL.IsStrictlyLE 3 := actL_le h410 h28
  letI : ∀ n, Module.Finite (ZMod 2) (actL.X n) := actL_finite h410 h51 h28
  letI : QuasiIso actPL := actPL_quasiIso h788
  exact residualRankCounts_actual SmallK smallLocalModels h410 h51 h28 h23 h788
    (-1) smallAlpha smallAlpha_radicand smallK_complex 66 (by decide) 0 (by simp)
    5 (by decide) actD actD_prime actD_odd actCond actCond_derivative actCond_full_torsion
    smallInfinitePlace smallInfinitePlace_complex SmallE 0 smallCharacter smallTorsion.1
    smallTorsion.2.1 smallTorsion.2.2.1 smallTorsion.2.2.2 SmallS actSel
    actDegrees (Finset.Subset.refl _) actEGact (act_hUm h28) (act_hLm h28) smallS_sub
    2 smallSetting smallS'_finite smallCharacter (urFactor SmallK) (urFactor_spec SmallK) actΔ
    actFull actW actF actG act_hDp act_fg act_inj act_surj act_ex act_hW 0 3 actPP actL
    actL_minimal actPL

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive

/-! ## The non-degenerate features and the main statements -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain WeierstrassCurve
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Contrib.RC53Assist.ResidualWitnessActive.LocalKummer
  ZInQ.Manuscript.RC.Limits

/-! ### The non-degenerate features of the instance -/

/-- A place of `ℚ(i)` above any rational prime. -/
theorem exists_place_above (p : ℕ) (hp : p.Prime) :
    ∃ q : HeightOneSpectrum (𝓞 SmallK), ((p : ℤ) : 𝓞 SmallK) ∈ q.asIdeal := by
  have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨Q, -, hQ, hQu⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 SmallK)
    (Ideal.span {(p : ℤ)}) ⊥ (by
      intro x hx
      have : algebraMap ℤ (𝓞 SmallK) x = 0 := hx
      have hx0 : x = 0 := by
        rw [eq_intCast] at this
        exact_mod_cast this
      rw [hx0]
      exact Ideal.zero_mem _)
  have hp' : (p : ℤ) ∈ Q.under ℤ := by rw [hQu]; exact Ideal.mem_span_singleton_self _
  have hp'' : ((p : ℤ) : 𝓞 SmallK) ∈ Q := by
    have := Ideal.mem_comap.mp hp'
    rwa [eq_intCast] at this
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have h0 : ((p : ℤ) : 𝓞 SmallK) = 0 := (Submodule.mem_bot _).mp hp''
    have : ((p : ℤ) : 𝓞 SmallK) ≠ 0 := by exact_mod_cast hp.ne_zero
    exact this h0
  exact ⟨⟨Q, hQ, hne⟩, hp''⟩

/-- **A derivative label**: some place of `S` carries the relaxed derivative condition (above the
derivative prime `7`), so the premise of `hcondD` is used. -/
theorem exists_derivative_place :
    ∃ v : Places SmallK SmallS, actCond v.1.asIdeal = .derivRelaxed := by
  obtain ⟨q, hq⟩ := exists_place_above 7 (by decide)
  have h7 : q.asIdeal ∈ primesAbove SmallK 7 :=
    (natCast_mem_asIdeal_iff SmallK (by decide) q).mp hq
  refine ⟨⟨q, ⟨7, by rw [actCharged_eq]; decide, hq⟩⟩, ?_⟩
  change actCond q.asIdeal = _
  rw [actCond, ite_eq_left h7]

/-- **An old-Kummer label**: some place of `S` carries the old Kummer condition (above `3`), so the
premise of `hfull` is used. -/
theorem exists_oldKummer_place :
    ∃ v : Places SmallK SmallS, actCond v.1.asIdeal = .oldKummer := by
  obtain ⟨q, hq⟩ := exists_place_above 3 (by decide)
  have h3 : q.asIdeal ∈ primesAbove SmallK 3 :=
    (natCast_mem_asIdeal_iff SmallK (by decide) q).mp hq
  have h7 : q.asIdeal ∉ primesAbove SmallK 7 := by
    intro h
    have h7' := (natCast_mem_asIdeal_iff SmallK (by decide) q).mpr h
    have := Genus.prime_eq_of_mem q.isPrime.ne_top (by decide : Nat.Prime 3)
      (by decide : Nat.Prime 7) hq h7'
    omega
  refine ⟨⟨q, ⟨3, by rw [actCharged_eq]; decide, hq⟩⟩, ?_⟩
  change actCond q.asIdeal = _
  rw [actCond, ite_eq_right h7, ite_eq_left (Or.inr (Or.inl h3))]

/-- At an old-Kummer place the local condition of the Selmer data is the Kummer complex. -/
theorem actΔ_U_oldKummer (v : Places SmallK SmallS) (hv : actCond v.1.asIdeal = .oldKummer) :
    actΔ.U v = ofCC (kumCC v.1) := by
  change ofCC (condCx v.1 (actCond v.1.asIdeal)) = _
  rw [hv]
  rfl

/-- At a derivative place the local condition is the relaxed derivative complex `τ≤1`. -/
theorem actΔ_U_derivRelaxed (v : Places SmallK SmallS) (hv : actCond v.1.asIdeal = .derivRelaxed) :
    actΔ.U v = ofCC (relCC v.1) := by
  change ofCC (condCx v.1 (actCond v.1.asIdeal)) = _
  rw [hv]
  rfl

/-- At a full place the local condition is the whole local complex. -/
theorem actΔ_U_full (v : Places SmallK SmallS) (hv : actCond v.1.asIdeal = .full) :
    actΔ.U v = ofCC (locCC v.1) := by
  change ofCC (condCx v.1 (actCond v.1.asIdeal)) = _
  rw [hv]
  rfl

/-- Every local condition has two-dimensional `H⁰`. -/
theorem finrank_U_zero (v : Places SmallK SmallS) :
    Module.finrank (ZMod 2) ((actΔ.U v).toCC.homology 0) = 2 := by
  rw [finrank_actU_place]
  rcases actCond_cases v.1.asIdeal with hc | hc | hc
  · rw [hc]
    change Module.finrank (ZMod 2) ((relCC v.1).homology 0) = 2
    rw [((relH0Equiv v.1).trans (locCohEquiv v.1 0)).finrank_eq,
      finrank_genLocH SmallK SmallS W2v v.1 0 (by omega)]
    exact hLoc_zero SmallK v.1
  · rw [hc]
    exact finrank_kum_H0 v.1
  · rw [hc]
    change Module.finrank (ZMod 2) ((locCC v.1).homology ((0 : ℕ) : ℤ)) = 2
    rw [finrank_full, finrank_genLocH SmallK SmallS W2v v.1 0 (by omega)]
    exact hLoc_zero SmallK v.1

theorem finrank_L_zero (v : Places SmallK SmallS) :
    Module.finrank (ZMod 2) ((locCC v.1).homology 0) = 2 := by
  change Module.finrank (ZMod 2) ((locCC v.1).homology ((0 : ℕ) : ℤ)) = 2
  rw [finrank_full, finrank_genLocH SmallK SmallS W2v v.1 0 (by omega)]
  exact hLoc_zero SmallK v.1

/-- **Nonzero condition part**: the left side of `hUm` is at least two. -/
theorem act_U_positive (h28 : MilneADT_I_2_8) :
    2 ≤ ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.U.X n) := by
  obtain ⟨v, -⟩ := exists_derivative_place
  have h0 : 2 ≤ Module.finrank (ZMod 2) (actSel.U.X 0) := by
    rw [finrank_actU h28]
    exact (finrank_U_zero v).symm.le.trans (Finset.single_le_sum (f := fun w : Places SmallK SmallS =>
      Module.finrank (ZMod 2) ((actΔ.U w).toCC.homology 0)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ v))
  exact h0.trans (Finset.single_le_sum (f := fun n => Module.finrank (ZMod 2) (actSel.U.X n))
    (fun _ _ => Nat.zero_le _) (show (0 : ℤ) ∈ actDegrees by decide))

/-- **Nonzero local part**: the left side of `hLm` is at least two. -/
theorem act_L_positive (h28 : MilneADT_I_2_8) :
    2 ≤ ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.L.X (n - 1)) := by
  obtain ⟨v, -⟩ := exists_derivative_place
  have h0 : 2 ≤ Module.finrank (ZMod 2) (actSel.L.X ((1 : ℤ) - 1)) := by
    rw [finrank_actL h28]
    change 2 ≤ ∑ w : Places SmallK SmallS, Module.finrank (ZMod 2) ((locCC w.1).homology 0)
    exact (finrank_L_zero v).symm.le.trans (Finset.single_le_sum (f := fun w : Places SmallK SmallS =>
      Module.finrank (ZMod 2) ((locCC w.1).homology 0)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ v))
  exact h0.trans (Finset.single_le_sum (f := fun n => Module.finrank (ZMod 2) (actSel.L.X (n - 1)))
    (fun _ _ => Nat.zero_le _) (show (1 : ℤ) ∈ actDegrees by decide))

/-! ### The main statements -/

theorem actPrimeFactors_card : (2 * 66).primeFactors.card = 3 := by
  rw [actPrimeFactors]; rfl

/-- The numerical bound of both constructors at this instance: `56·3 + 8·0 + 56·1 + 70 = 294`. -/
theorem activeBound :
    residualBoundConstant (2 * 66).primeFactors.card 0 actD.card = 294 := by
  rw [actPrimeFactors_card]
  rfl

theorem activeGenuineCounts_genericRank (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    (activeGenuineCounts h410 h51 h28 h23 h788).genericRank =
      ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actL.X n) := rfl

theorem activeGenuineCounts_rankTot (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    (activeGenuineCounts h410 h51 h28 h23 h788).rankTot =
      ∑ n ∈ actDegrees, Module.finrank (ZMod 2) ((selCx actSel).toCC.X n) := rfl

/-- **Non-vacuity of the genuine constructor on the active instance.** -/
theorem residualRankCounts_genuine_active (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    (activeGenuineCounts h410 h51 h28 h23 h788).genericRank ≤
        (activeGenuineCounts h410 h51 h28 h23 h788).rankTot ∧
      (activeGenuineCounts h410 h51 h28 h23 h788).genericRank ≤ 294 := by
  refine ⟨(activeGenuineCounts h410 h51 h28 h23 h788).transfer, ?_⟩
  have hb := (activeGenuineCounts h410 h51 h28 h23 h788).genericRank_le
  change (activeGenuineCounts h410 h51 h28 h23 h788).genericRank ≤
    residualBoundConstant (2 * 66).primeFactors.card 0 actD.card at hb
  rwa [activeBound] at hb

/-- **Non-vacuity of the actual-coefficient constructor on the same instance.** -/
theorem residualRankCounts_actual_active (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    (activeActualCounts h410 h51 h28 h23 h788).genericRank ≤
        (activeActualCounts h410 h51 h28 h23 h788).rankTot ∧
      (activeActualCounts h410 h51 h28 h23 h788).genericRank ≤ 294 := by
  refine ⟨(activeActualCounts h410 h51 h28 h23 h788).transfer, ?_⟩
  have hb := (activeActualCounts h410 h51 h28 h23 h788).genericRank_le
  change (activeActualCounts h410 h51 h28 h23 h788).genericRank ≤
    residualBoundConstant (2 * 66).primeFactors.card 0 actD.card at hb
  rwa [activeBound] at hb

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive

/-! ## The transfer is exercised -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain WeierstrassCurve
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Contrib.RC53Assist.ResidualWitnessActive.LocalKummer
  ZInQ.Manuscript.RC.Limits

/-! ### The transfer is exercised: the minimal model is strictly smaller -/

theorem homology_finrank_le {C : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ} (n : ℤ)
    [Module.Finite (ZMod 2) (C.X n)] :
    Module.finrank (ZMod 2) (C.homology n) ≤ Module.finrank (ZMod 2) (C.X n) := by
  have hinj := (ModuleCat.mono_iff_injective (C.iCycles n)).1 inferInstance
  have : Module.Finite (ZMod 2) (C.cycles n) := Module.Finite.of_injective _ hinj
  exact (LinearMap.finrank_le_finrank_of_surjective
    ((ModuleCat.epi_iff_surjective (C.homologyπ n)).1 inferInstance)).trans
    (LinearMap.finrank_le_finrank_of_injective hinj)

/-- A degree with a nonzero differential loses rank in cohomology. -/
theorem homology_finrank_lt {C : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ} (n : ℤ)
    [Module.Finite (ZMod 2) (C.X n)] (x : C.X n) (hx : (C.d n (n + 1)).hom x ≠ 0) :
    Module.finrank (ZMod 2) (C.homology n) < Module.finrank (ZMod 2) (C.X n) := by
  have hinj := (ModuleCat.mono_iff_injective (C.iCycles n)).1 inferInstance
  have : Module.Finite (ZMod 2) (C.cycles n) := Module.Finite.of_injective _ hinj
  have hne : LinearMap.range (C.iCycles n).hom ≠ ⊤ := by
    intro h
    obtain ⟨z, rfl⟩ : x ∈ LinearMap.range (C.iCycles n).hom := h ▸ Submodule.mem_top
    apply hx
    have := congrArg (fun f => f.hom z) (C.iCycles_d n (n + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at this
    exact this
  refine (LinearMap.finrank_le_finrank_of_surjective
    ((ModuleCat.epi_iff_surjective (C.homologyπ n)).1 inferInstance)).trans_lt ?_
  rw [← LinearMap.finrank_range_of_inj hinj]
  exact Submodule.finrank_lt hne

/-- At every row except the relaxed derivative one, the condition map is an isomorphism on `H⁰`. -/
theorem condTo_injective_zero (v : HeightOneSpectrum (𝓞 SmallK)) (c : LocalCondition)
    (hc : c ≠ .derivRelaxed) :
    Function.Injective (HomologicalComplex.homologyMap
      (GHom.toCC (ofCCHom (B := natCx (contCochains (ZMod 2) (Gloc SmallK v) (locM v)))
        (condTo v c))) 0).hom := by
  have key : ∀ (C : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ) (φ : C ⟶ locCC v),
      IsIso (HomologicalComplex.homologyMap φ 0) →
        Function.Injective (HomologicalComplex.homologyMap
          (GHom.toCC (ofCCHom (B := natCx (contCochains (ZMod 2) (Gloc SmallK v) (locM v))) φ))
            0).hom := by
    intro C φ hφ
    have he : GHom.toCC (ofCCHom (B := natCx (contCochains (ZMod 2) (Gloc SmallK v) (locM v))) φ) =
        (ofCCIso C).hom ≫ φ := by
      ext n x
      rfl
    rw [he, HomologicalComplex.homologyMap_comp]
    have : IsIso (HomologicalComplex.homologyMap (ofCCIso C).hom 0) := inferInstance
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  cases c with
  | derivRelaxed => exact absurd rfl hc
  | oldKummer =>
    exact key _ _ (kummerConditionIn_isIso_homologyMap_zero (ZMod 2) (kumIota v)
      (kumIota_equivariant v))
  | unramified => exact key _ _ (by change IsIso (HomologicalComplex.homologyMap (𝟙 _) 0); simp; infer_instance)
  | zero => exact key _ _ (by change IsIso (HomologicalComplex.homologyMap (𝟙 _) 0); simp; infer_instance)
  | full => exact key _ _ (by change IsIso (HomologicalComplex.homologyMap (𝟙 _) 0); simp; infer_instance)
  | derivStrict => exact key _ _ (by change IsIso (HomologicalComplex.homologyMap (𝟙 _) 0); simp; infer_instance)
  | derivFiniteOrSingular =>
    exact key _ _ (by change IsIso (HomologicalComplex.homologyMap (𝟙 _) 0); simp; infer_instance)

/-- **The residual cone has a nonzero differential**: a class of a local condition at an
old-Kummer place is sent to a nonzero local class. -/
theorem actP_d_ne_zero :
    ∃ x : (selCx actSel).toCC.X 0, ((selCx actSel).toCC.d 0 (0 + 1)).hom x ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_oldKummer_place
  have hfin : Module.finrank (ZMod 2) ((hm (actΔ.U v)).X 0) = 2 := finrank_U_zero v
  have : Nontrivial ((hm (actΔ.U v)).X 0) :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [hfin]; norm_num)
  obtain ⟨u₀, hu₀⟩ := exists_ne (0 : (hm (actΔ.U v)).X 0)
  let u : actSel.U.X 0 := Pi.single (M := fun w : Places SmallK SmallS => (hm (actΔ.U w)).X 0)
    v u₀
  refine ⟨((0 : actSel.G.X 0), u, (0 : actSel.L.X (0 - 1))), ?_⟩
  rw [GCx.toCC_d_hom _ 0 (0 + 1) rfl]
  intro h
  have h3 := congrArg (fun c : (selCx actSel).X (0 + 1) => c.2.2) h
  change actSel.res.f 0 (0 + 1 - 1) (by omega) 0 - actSel.ι.f 0 (0 + 1 - 1) (by omega) u -
      actSel.L.d (0 - 1) (0 + 1 - 1) (by omega) 0 = 0 at h3
  rw [map_zero, map_zero, zero_sub, sub_zero, neg_eq_zero] at h3
  have h4 := congrFun h3 v
  change (HomologicalComplex.homologyMap (GHom.toCC (actΔ.i v)) 0).hom (u v) = 0 at h4
  have hinj := condTo_injective_zero v.1 (actCond v.1.asIdeal) (by rw [hv]; decide)
  have h5 : u v = u₀ := Pi.single_eq_same (M := fun w : Places SmallK SmallS =>
    (hm (actΔ.U w)).X 0) v u₀
  rw [h5] at h4
  exact hu₀ (hinj (h4.trans (map_zero _).symm))

/-- **The transfer is exercised**: the minimal model of the original-support complex has strictly
smaller total rank than the residual cone of the smaller-support complex. -/
theorem activeGenuineCounts_strict (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    (activeGenuineCounts h410 h51 h28 h23 h788).genericRank <
      (activeGenuineCounts h410 h51 h28 h23 h788).rankTot := by
  rw [activeGenuineCounts_genericRank, activeGenuineCounts_rankTot]
  have hfin := actP_finite h410 h51 h28
  obtain ⟨x, hx⟩ := actP_d_ne_zero
  apply Finset.sum_lt_sum
  · intro n _
    exact homology_finrank_le n
  · exact ⟨0, by decide, homology_finrank_lt 0 x hx⟩

theorem activeActualCounts_genericRank (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    (activeActualCounts h410 h51 h28 h23 h788).genericRank =
      ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actL.X n) := rfl

theorem activeActualCounts_rankTot (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    (activeActualCounts h410 h51 h28 h23 h788).rankTot =
      ∑ n ∈ actDegrees, Module.finrank (ZMod 2) ((selCx actSel).toCC.X n) := rfl

/-- The same strict inequality for the actual-coefficient constructor. -/
theorem activeActualCounts_strict (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    (activeActualCounts h410 h51 h28 h23 h788).genericRank <
      (activeActualCounts h410 h51 h28 h23 h788).rankTot := by
  rw [activeActualCounts_genericRank, activeActualCounts_rankTot]
  have hfin := actP_finite h410 h51 h28
  obtain ⟨x, hx⟩ := actP_d_ne_zero
  apply Finset.sum_lt_sum
  · intro n _
    exact homology_finrank_le n
  · exact ⟨0, by decide, homology_finrank_lt 0 x hx⟩

/-- Continuous `0`-cochains with values in a nonzero module are nonzero. -/
theorem natCx_X_zero_nontrivial {G M : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod 2) M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousConstSMul (ZMod 2) M] [ContinuousSMul G M] [Nontrivial M] :
    Nontrivial ((natCx (contCochains (ZMod 2) G M)).X 0) := by
  obtain ⟨t, ht⟩ := exists_ne (0 : M)
  refine ⟨⟨constCochain (k := ZMod 2) (G := G) (M := M) t, 0, fun h => ht ?_⟩⟩
  exact congrArg (fun z : ↥(contCochain (ZMod 2) G M 0) => cfun z default) h

/-- **The change of condition is not the identity**: its quotient, the cone of the identity of
the unramified conditions at the active places, is nonzero. -/
theorem actW_nontrivial : Nontrivial (actW.X 0) := by
  obtain ⟨q⟩ := newPlaces_nonempty
  have hM : Nontrivial (ResMod (urFactor SmallK q) SmallM) :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by
      change 0 < Module.finrank (ZMod 2) SmallM
      rw [smallM_finrank]; norm_num)
  have hq : Nontrivial ((natCx (contCochains (ZMod 2) (GUr SmallK q.1)
      (ResMod (urFactor SmallK q) SmallM))).X 0) := natCx_X_zero_nontrivial
  have hB : Nontrivial (actB.X 0) := by
    change Nontrivial (∀ q' : NewPlaces SmallK SmallS SmallS', (natCx (contCochains (ZMod 2)
      (GUr SmallK q'.1) (ResMod (urFactor SmallK q') SmallM))).X 0)
    exact Pi.nontrivial_at q
  change Nontrivial (actB.X 0 × actB.X (0 - 1))
  infer_instance

/-- **Summary of the non-degenerate features of the instance.** -/
theorem active_instance_nondegenerate (h28 : MilneADT_I_2_8) :
    (∃ v : Places SmallK SmallS, actCond v.1.asIdeal = .derivRelaxed) ∧
      (∃ v : Places SmallK SmallS, actCond v.1.asIdeal = .oldKummer) ∧
      Nonempty (NewPlaces SmallK SmallS SmallS') ∧
      2 ≤ ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.U.X n) ∧
      2 ≤ ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.L.X (n - 1)) ∧
      Nontrivial (actW.X 0) ∧
      ∃ x : (selCx actSel).toCC.X 0, ((selCx actSel).toCC.d 0 (0 + 1)).hom x ≠ 0 :=
  ⟨exists_derivative_place, exists_oldKummer_place, newPlaces_nonempty, act_U_positive h28,
    act_L_positive h28, actW_nontrivial, actP_d_ne_zero⟩

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive

/-! ## Why the text's active change of condition is not available over `𝔽₂` -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain WeierstrassCurve
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Contrib.CloudB3RC53.ResidualTransfer
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Contrib.RC53Assist.ResidualWitnessActive.LocalKummer
  ZInQ.Manuscript.RC.Limits

/-! ### Over `𝔽₂`, the full condition at an active place has a non-acyclic quotient -/

/-- Two modules with the trivial action and a linear equivalence have the same cohomology. -/
def trivCohEquiv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {M₁ M₂ : Type} [AddCommGroup M₁] [Module (ZMod 2) M₁] [DistribMulAction G M₁]
    [SMulCommClass G (ZMod 2) M₁] [TopologicalSpace M₁] [DiscreteTopology M₁] [ContinuousAdd M₁]
    [ContinuousConstSMul (ZMod 2) M₁] [ContinuousSMul G M₁]
    [AddCommGroup M₂] [Module (ZMod 2) M₂] [DistribMulAction G M₂]
    [SMulCommClass G (ZMod 2) M₂] [TopologicalSpace M₂] [DiscreteTopology M₂] [ContinuousAdd M₂]
    [ContinuousConstSMul (ZMod 2) M₂] [ContinuousSMul G M₂]
    (e : M₁ ≃ₗ[ZMod 2] M₂) (h₁ : ∀ (g : G) (m : M₁), g • m = m)
    (h₂ : ∀ (g : G) (m : M₂), g • m = m) (n : ℕ) :
    contCohomology (ZMod 2) G M₁ n ≃ₗ[ZMod 2] contCohomology (ZMod 2) G M₂ n := by
  let f : contCochains (ZMod 2) G M₁ ⟶ contCochains (ZMod 2) G M₂ :=
    contCochainsMap (ContinuousMonoidHom.id G) e.toLinearMap continuous_of_discreteTopology
      (fun g m => by
        change e (g • m) = g • e m
        rw [h₁, h₂])
  let g : contCochains (ZMod 2) G M₂ ⟶ contCochains (ZMod 2) G M₁ :=
    contCochainsMap (ContinuousMonoidHom.id G) e.symm.toLinearMap continuous_of_discreteTopology
      (fun g m => by
        change e.symm (g • m) = g • e.symm m
        rw [h₁, h₂])
  have hfg : f ≫ g = 𝟙 _ := by
    rw [← contCochainsMap_comp, ← contCochainsMap_id (ZMod 2) G M₁]
    congr 1
    exact LinearMap.ext fun x => e.symm_apply_apply x
  have hgf : g ≫ f = 𝟙 _ := by
    rw [← contCochainsMap_comp, ← contCochainsMap_id (ZMod 2) G M₂]
    congr 1
    exact LinearMap.ext fun x => e.apply_symm_apply x
  exact (HomologicalComplex.homologyMapIso ⟨f, g, hfg, hgf⟩ n).toLinearEquiv

/-- `M ≅ 𝔽₂²` as a plain vector space. -/
def smallMW2v : SmallM ≃ₗ[ZMod 2] W2v :=
  smallMEquiv.trans (LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2)).symm

/-- The active prime. -/
def p13 : Nat.Primes := ⟨13, by norm_num⟩

/-- An active place lies above `13`. -/
theorem newPlace_above (q : NewPlaces SmallK SmallS SmallS') :
    q.1.asIdeal ∈ primesAbove SmallK 13 := by
  obtain ⟨⟨p, hp, hpq⟩, hS⟩ := q.2
  rw [Finset.mem_insert] at hp
  rcases hp with rfl | hp
  · exact (natCast_mem_asIdeal_iff SmallK (by decide) q.1).mp hpq
  · exact absurd ⟨p, hp, hpq⟩ hS

/-- The unramified condition at an active place has two-dimensional `H¹`. -/
theorem finrank_active_ur_one (q : NewPlaces SmallK SmallS SmallS') :
    Module.finrank (ZMod 2) (contCohomology (ZMod 2) (GUr SmallK q.1)
      (ResMod (urFactor SmallK q) SmallM) 1) = 2 := by
  let e : ResMod (urFactor SmallK q) SmallM ≃ₗ[ZMod 2] TrivMod (GUr SmallK q.1) W2v := smallMW2v
  rw [(trivCohEquiv e (fun g m => smallM_smul (urFactor SmallK q g) m) (fun _ _ => rfl) 1).finrank_eq,
    (toLin (trivH1Equiv (GUr SmallK q.1) W2v)).finrank_eq]
  exact hUr_one SmallK q.1

/-- The full local complex at an active place has four-dimensional `H¹` (local Euler characteristic
and local duality, Milne I.2.8 and I.2.3). -/
theorem finrank_active_full_one (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (q : NewPlaces SmallK SmallS SmallS') :
    Module.finrank (ZMod 2) (contCohomology (ZMod 2) (Gloc SmallK q.1)
      (ResMod (locMap SmallK SmallS' q.1) (ResMod (inflMap SmallK smallS_sub) SmallM)) 1) = 4 := by
  let e : ResMod (locMap SmallK SmallS' q.1) (ResMod (inflMap SmallK smallS_sub) SmallM) ≃ₗ[ZMod 2]
      TrivMod (Gloc SmallK q.1) W2v := smallMW2v
  rw [(trivCohEquiv e (fun g m => smallM_smul (inflMap SmallK smallS_sub (locMap SmallK SmallS' q.1 g)) m)
      (fun _ _ => rfl) 1).finrank_eq,
    (toLin (trivH1Equiv (Gloc SmallK q.1) W2v)).finrank_eq]
  have hv : q.1.asIdeal ∈ primesAbove SmallK (p13 : ℕ) := newPlace_above q
  have hlo : q.1.asIdeal.LiesOver (vP p13).asIdeal := by
    rw [vP_asIdeal]; exact hv.2
  let _ := qpAlg SmallK p13 q.1
  have : FiniteDimensional ℚ_[(p13 : ℕ)] (q.1.adicCompletion SmallK) :=
    qp_finiteDimensional SmallK p13 q.1.asIdeal hv
  have h := (local_cohomology_dims h28 h23 (p13 : ℕ) (q.1.adicCompletion SmallK)).2.1
  have h13 : (p13 : ℕ) ≠ 2 := by decide
  rw [h, ite_eq_right h13]

/-- **No quasi-isomorphism** between the unramified condition and the full local complex at an
active place, over `𝔽₂` (their `H¹` have dimensions `2` and `4`). -/
theorem active_unramified_not_full (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (q : NewPlaces SmallK SmallS SmallS')
    (φ : GHom (natCx (contCochains (ZMod 2) (GUr SmallK q.1) (ResMod (urFactor SmallK q) SmallM)))
      (natCx (contCochains (ZMod 2) (Gloc SmallK q.1)
        (ResMod (locMap SmallK SmallS' q.1) (ResMod (inflMap SmallK smallS_sub) SmallM))))) :
    ¬ QuasiIso (GHom.toCC φ) := by
  intro hq
  have hiso : IsIso (HomologicalComplex.homologyMap (GHom.toCC φ) ((1 : ℕ) : ℤ)) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance
  have h := ((natHomologyIso _ 1).toLinearEquiv.symm.trans
    ((asIso (HomologicalComplex.homologyMap (GHom.toCC φ) ((1 : ℕ) : ℤ))).toLinearEquiv.trans
      (natHomologyIso _ 1).toLinearEquiv)).finrank_eq
  rw [finrank_active_ur_one, finrank_active_full_one h28 h23] at h
  omega

/-- **The manuscript's change of condition is not available over `𝔽₂`**: replacing the unramified
condition by the full condition at an active place has a non-acyclic quotient. (Its acyclicity in
the text holds only after inverting `t`.) -/
theorem active_full_change_not_acyclic (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (q : NewPlaces SmallK SmallS SmallS') {W : GCx (ZMod 2)}
    (f : GHom (natCx (contCochains (ZMod 2) (GUr SmallK q.1) (ResMod (urFactor SmallK q) SmallM)))
      (natCx (contCochains (ZMod 2) (Gloc SmallK q.1)
        (ResMod (locMap SmallK SmallS' q.1) (ResMod (inflMap SmallK smallS_sub) SmallM)))))
    (g : GHom (natCx (contCochains (ZMod 2) (Gloc SmallK q.1)
        (ResMod (locMap SmallK SmallS' q.1) (ResMod (inflMap SmallK smallS_sub) SmallM)))) W)
    (hfg : ∀ i u, g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl))
    (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i u, g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u) :
    ¬ W.toCC.Acyclic := by
  intro hW
  let E : ShortComplex (CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ) :=
    ShortComplex.mk (GHom.toCC f) (GHom.toCC g) (by
      rw [GHom.toCC_comp]
      ext i x
      exact hfg i x)
  have hE : E.ShortExact := by
    refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.moduleCat_exact_iff]
      intro u hu
      exact hex i u hu
    · rw [ModuleCat.mono_iff_injective]
      exact hinj i
    · rw [ModuleCat.epi_iff_surjective]
      exact hsurj i
  exact active_unramified_not_full h28 h23 q f (quasiIso_f_of_shortExact_acyclic hE hW)

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive

/-! ## The old Kummer row is exact -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain WeierstrassCurve
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Contrib.RC53Assist.ResidualWitnessActive.LocalKummer
  ZInQ.Manuscript.RC.Limits

/-! ### The old Kummer condition has exactly Mattuck's dimensions -/

section KummerExact

variable (v : HeightOneSpectrum (𝓞 SmallK))

/-- With the trivial action there are no nonzero continuous `1`-coboundaries. -/
theorem contB1_eq_bot : contB1 (ZMod 2) (Gloc SmallK v) (locM v) = ⊥ := by
  rw [eq_bot_iff]
  rintro b ⟨c, rfl⟩
  rw [Submodule.mem_bot]
  exact (contD_zero_eq_zero_iff c).2 fun g => locM_smul v g _

/-- **The Kummer map is injective on `E₁₁(K_v)/2`**: a point whose Kummer cocycle vanishes has a
rational half (Galois descent). -/
theorem kumLambda_injective : Function.Injective (kumLambda v) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨P, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker, kumLambda_mk] at hx
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  have hfix : ∀ σ : Gloc SmallK v,
      σ • divPt (v.adicCompletion SmallK) (smallCurve (v.adicCompletion SmallK)) 2 P =
        divPt (v.adicCompletion SmallK) (smallCurve (v.adicCompletion SmallK)) 2 P := by
    intro σ
    have h1 := congrArg (fun c : contCochain (ZMod 2) (Gloc SmallK v) (locM v) 1 =>
      cfun c (fun _ : Fin 1 => σ)) hx
    change (1 : ZMod 2) • kumIota v (kummerFun _ _ 2 P σ) = 0 at h1
    rw [one_smul] at h1
    have h2 : kummerFun _ _ 2 P σ = 0 := kumIota_injective v (h1.trans (map_zero _).symm)
    have h3 := congrArg Subtype.val h2
    rw [coe_kummerFun] at h3
    exact sub_eq_zero.mp h3
  obtain ⟨R, hR⟩ := exists_basePt_of_fixed (F := v.adicCompletion SmallK)
    (B := smallCurve (v.adicCompletion SmallK)) hfix
  refine ⟨R, ?_⟩
  change (2 : ℤ) • R = P
  apply basePt_injective (F := v.adicCompletion SmallK) (B := smallCurve (v.adicCompletion SmallK))
  rw [map_zsmul, hR, two_zsmul, ← two_nsmul, nsmul_divPt]

theorem kummerZ'_eq_range :
    kummerZ' (ZMod 2) (kumIota v) = LinearMap.range (kumLambda v) := by
  refine le_antisymm (kummerZ'_le_range v) ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨P, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [kumLambda_mk]
  exact kummerCocycleIn_mem _ 1 P

/-- **`H¹` of the old Kummer condition is `E₁₁(K_v)/2`.** -/
theorem finrank_kum_H1_eq :
    Module.finrank (ZMod 2) ((kumCC v).homology 1) =
      Module.finrank (ZMod 2) (ModN (smallCurve (v.adicCompletion SmallK)).toAffine.Point 2) := by
  have := modN_finite v
  set Z := kummerZ' (ZMod 2) (kumIota v)
  set hZ := kummerZ'_cocycle (ZMod 2) (kumIota v) (kumIota_equivariant v)
  rw [(kummerConditionInH1Iso (ZMod 2) (kumIota v) (kumIota_equivariant v)).toLinearEquiv.finrank_eq]
  have hB : condB1 Z hZ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_condB1] at hx
    obtain ⟨c, hc⟩ := hx
    have h0 : (contD (ZMod 2) (Gloc SmallK v) (locM v) 0) c = 0 :=
      (contD_zero_eq_zero_iff c).2 fun g => locM_smul v g _
    rw [Submodule.mem_bot]
    change (condOne Z hZ x) = (0 : ↥(Z ⊔ contB1 (ZMod 2) (Gloc SmallK v) (locM v)))
    exact Subtype.ext (hc.symm.trans h0)
  rw [hB, (Submodule.quotEquivOfEqBot _ rfl).finrank_eq]
  change Module.finrank (ZMod 2) ↥(Z ⊔ contB1 (ZMod 2) (Gloc SmallK v) (locM v)) = _
  rw [contB1_eq_bot, sup_bot_eq, show Z = LinearMap.range (kumLambda v) from kummerZ'_eq_range v,
    LinearMap.finrank_range_of_inj (kumLambda_injective v)]

/-- **The old Kummer row is exact**: the cohomology of the actual Kummer condition has total
dimension exactly Mattuck's `dim E(K_v)[2] + dim E(K_v)/2`. -/
theorem kum_dims_eq :
    Module.finrank (ZMod 2) ((kumCC v).homology 0) +
        Module.finrank (ZMod 2) ((kumCC v).homology 1) +
        Module.finrank (ZMod 2) ((kumCC v).homology 2) =
      kummerResidualDim v (smallLocalModels v) := by
  have h2 : Module.finrank (ZMod 2) ((kumCC v).homology 2) = 0 := by
    have := homology_subsingleton_of_X _ (kum_X_subsingleton v 0)
    exact Module.finrank_zero_of_subsingleton
  rw [kummerResidualDim_eq, finrankTwoTorsion_smallCurve, finrank_kum_H0, h2, add_zero,
    finrank_kum_H1_eq]

/-- Mattuck: `E₁₁(K_v)/2` has dimension at least two. -/
theorem two_le_finrank_modN :
    2 ≤ Module.finrank (ZMod 2) (ModN (smallCurve (v.adicCompletion SmallK)).toAffine.Point 2) := by
  have key : ∀ W : WeierstrassCurve (v.adicCompletion SmallK), W = smallCurve _ →
      2 ≤ Module.finrank (ZMod 2) (ModN W.toAffine.Point 2) →
        2 ≤ Module.finrank (ZMod 2) (ModN (smallCurve (v.adicCompletion SmallK)).toAffine.Point 2) := by
    rintro W rfl h
    exact h
  refine key _ (smallLocal_baseChange v) ?_
  by_cases h2 : (2 : 𝓞 SmallK) ∈ v.asIdeal
  · have hv : v.asIdeal ∈ primesAbove SmallK 2 :=
      (natCast_mem_asIdeal_iff SmallK Nat.prime_two v).mp (by exact_mod_cast h2)
    have hlo : v.asIdeal.LiesOver (vP two).asIdeal := by
      rw [vP_asIdeal]; exact hv.2
    have h := (finrank_two SmallK v (smallLocalModels v) (local_models_have_full_two_torsion v)).2
    rw [h]
    omega
  · have h := (finrank_odd v (smallLocalModels v) h2 (local_models_have_full_two_torsion v)).2
    rw [h]

/-- **The old Kummer condition is not degenerate**: its `H¹` is nonzero. -/
theorem kum_H1_pos : 0 < Module.finrank (ZMod 2) ((kumCC v).homology 1) := by
  rw [finrank_kum_H1_eq]
  have := two_le_finrank_modN v
  omega

end KummerExact

/-- **At every old-Kummer place, the local condition of the Selmer data is the Kummer complex,
with nonzero `H¹` and exactly Mattuck's total dimension.** -/
theorem oldKummer_places_exact (v : Places SmallK SmallS)
    (hv : actCond v.1.asIdeal = .oldKummer) :
    actΔ.U v = ofCC (kumCC v.1) ∧ 0 < Module.finrank (ZMod 2) ((kumCC v.1).homology 1) ∧
      Module.finrank (ZMod 2) ((kumCC v.1).homology 0) +
          Module.finrank (ZMod 2) ((kumCC v.1).homology 1) +
          Module.finrank (ZMod 2) ((kumCC v.1).homology 2) =
        kummerResidualDim v.1 (smallLocalModels v.1) :=
  ⟨actΔ_U_oldKummer v hv, kum_H1_pos v.1, kum_dims_eq v.1⟩

/-- **The condition dimensions at one place, exactly**: every row of the table is attained. -/
theorem place_U_dims_eq (v : Places SmallK SmallS) :
    ∑ n ∈ actDegrees, Module.finrank (ZMod 2) ((actΔ.U v).toCC.homology n) =
      genCondDimFun2 SmallK SmallS actCond
        (kummerDimOfCurves SmallK smallLocalModels (kd2OfCurves SmallK smallLocalModels))
        v.1.asIdeal := by
  rw [sum_actDegrees, finrank_actU_place, finrank_actU_place, finrank_actU_place]
  unfold genCondDimFun2
  rw [dite_eq_left ⟨v.1.isPrime, v.1.ne_bot⟩]
  rcases actCond_cases v.1.asIdeal with hc | hc | hc
  · rw [hc]
    have h2 : Module.finrank (ZMod 2) ((relCC v.1).homology 2) = 0 := by
      have := homology_subsingleton_of_X 2 (relCC_X_subsingleton v.1 2 (by decide) (by decide))
      exact Module.finrank_zero_of_subsingleton
    change Module.finrank (ZMod 2) ((relCC v.1).homology 0) +
        Module.finrank (ZMod 2) ((relCC v.1).homology 1) +
        Module.finrank (ZMod 2) ((relCC v.1).homology 2) =
      Module.finrank (ZMod 2) ((relaxedCx (Gloc SmallK v.1)
          (locMod SmallK SmallS W2v v.1)).homology 0) +
        Module.finrank (ZMod 2) ((relaxedCx (Gloc SmallK v.1)
          (locMod SmallK SmallS W2v v.1)).homology 1)
    rw [h2, add_zero, finrank_rel, finrank_relaxedCx]
  · rw [hc]
    have hk := kum_dims_eq v.1
    change Module.finrank (ZMod 2) ((kumCC v.1).homology 0) +
        Module.finrank (ZMod 2) ((kumCC v.1).homology 1) +
        Module.finrank (ZMod 2) ((kumCC v.1).homology 2) =
      kummerDimOfCurves SmallK smallLocalModels (kd2OfCurves SmallK smallLocalModels) v.1.asIdeal
    unfold kummerDimOfCurves
    rw [dite_eq_left ⟨v.1.isPrime, v.1.ne_bot⟩]
    split_ifs
    · unfold kd2OfCurves
      rw [dite_eq_left ⟨v.1.isPrime, v.1.ne_bot⟩]
      exact hk
    · exact hk
  · rw [hc]
    change Module.finrank (ZMod 2) ((locCC v.1).homology ((0 : ℕ) : ℤ)) +
        Module.finrank (ZMod 2) ((locCC v.1).homology ((1 : ℕ) : ℤ)) +
        Module.finrank (ZMod 2) ((locCC v.1).homology ((2 : ℕ) : ℤ)) =
      genLocDim SmallK SmallS v.1
    rw [finrank_full, finrank_full, finrank_full, genLocDim]
    simp [Finset.sum_range_succ]

/-- **`hUm` holds with equality**: the condition part of the residual model has exactly the genuine
condition dimensions at the places above the charged primes (Mattuck's dimension at the old
Kummer rows). -/
theorem act_hUm_eq (h28 : MilneADT_I_2_8) :
    ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.U.X n) =
      ∑ p ∈ chargedPrimes 66 5 actD,
        condSum SmallK (genCondDimFun2 SmallK SmallS actCond
          (kummerDimOfCurves SmallK smallLocalModels (kd2OfCurves SmallK smallLocalModels))) p := by
  simp only [finrank_actU h28]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun v _ => place_U_dims_eq v]
  exact sum_places _

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive

/-! ## The generic rank is positive -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain WeierstrassCurve
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Contrib.RC53Assist.ResidualWitnessActive.LocalKummer
  ZInQ.Manuscript.RC.Limits

/-! ### The minimal model is nonzero -/

/-- If nothing comes into degree `0`, then `H⁰` contains the kernel of the outgoing differential. -/
theorem finrank_ker_le_homology_zero (C : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ)
    [Module.Finite (ZMod 2) (C.X 0)] (h : Subsingleton (C.X (-1))) :
    Module.finrank (ZMod 2) (LinearMap.ker (C.d 0 1).hom) ≤
      Module.finrank (ZMod 2) (C.homology 0) := by
  have hd : C.d (-1) 0 = 0 := by
    ext x
    rw [Subsingleton.elim x 0, map_zero]
    rfl
  rw [← (C.isoHomologyπ (-1) 0 (by simp) hd).toLinearEquiv.finrank_eq]
  have hinjC := (ModuleCat.mono_iff_injective (C.iCycles 0)).1 inferInstance
  have : Module.Finite (ZMod 2) (C.cycles 0) := Module.Finite.of_injective _ hinjC
  let k : ModuleCat.of (ZMod 2) (LinearMap.ker (C.d 0 1).hom) ⟶ C.X 0 :=
    ModuleCat.ofHom (LinearMap.ker (C.d 0 1).hom).subtype
  have hk : k ≫ C.d 0 1 = 0 := by
    ext x
    exact x.2
  let l := C.liftCycles k 1 (by simp) hk
  have hl : Function.Injective l.hom := by
    intro x y hxy
    have := congrArg (C.iCycles 0).hom hxy
    have h1 := congrArg (fun f => f.hom x) (C.liftCycles_i k 1 (by simp) hk)
    have h2 := congrArg (fun f => f.hom y) (C.liftCycles_i k 1 (by simp) hk)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
    exact Subtype.ext (h1.symm.trans (this.trans h2))
  exact LinearMap.finrank_le_finrank_of_injective hl

theorem finrank_actU_zero (h28 : MilneADT_I_2_8) :
    Module.finrank (ZMod 2) (actSel.U.X 0) = 2 * Fintype.card (Places SmallK SmallS) := by
  rw [finrank_actU h28, Finset.sum_congr rfl fun v _ => finrank_U_zero v, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_comm]

theorem finrank_actL_zero (h28 : MilneADT_I_2_8) :
    Module.finrank (ZMod 2) (actSel.L.X 0) = 2 * Fintype.card (Places SmallK SmallS) := by
  rw [finrank_actL h28, Finset.sum_congr rfl fun v _ => finrank_L_zero v, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_comm]

theorem finrank_actP_zero (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) :
    Module.finrank (ZMod 2) ((selCx actSel).toCC.X 0) =
      2 + 2 * Fintype.card (Places SmallK SmallS) := by
  have := actSel_G_finite h410 h51 0
  have := actSel_U_finite h28 0
  have := actSel_L_finite h28 (0 - 1)
  have hL : Subsingleton (actSel.L.X (0 - 1)) := actSel_L_off h28 (0 - 1) (by omega)
  change Module.finrank (ZMod 2) (actSel.G.X 0 × actSel.U.X 0 × actSel.L.X (0 - 1)) = _
  rw [Module.finrank_prod, Module.finrank_prod, finrank_actU_zero h28,
    Module.finrank_zero_of_subsingleton (M := actSel.L.X (0 - 1)), add_zero]
  change Module.finrank (ZMod 2) ((hm smallGlobal).X 0) + _ = _
  rw [smallGlobal_zero_rank]

/-- **The residual cone has at least two-dimensional `H⁰`**: its degree-zero differential lands in
the local part, of dimension `2·#S`, while its degree-zero term has dimension `2 + 2·#S`. -/
theorem two_le_actL_zero (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) :
    2 ≤ Module.finrank (ZMod 2) (actL.X 0) := by
  have hfin := actP_finite h410 h51 h28
  have := actSel_L_finite h28 (1 - 1)
  have hsub : Subsingleton ((selCx actSel).toCC.X (-1)) :=
    actP_X_subsingleton h410 h28 (-1) (Or.inl (by norm_num))
  refine le_trans ?_ (finrank_ker_le_homology_zero (selCx actSel).toCC hsub)
  let ψ : (selCx actSel).toCC.X 0 →ₗ[ZMod 2] actSel.L.X (1 - 1) :=
    ((LinearMap.snd (ZMod 2) _ _).comp (LinearMap.snd (ZMod 2) _ _)).comp
      ((selCx actSel).toCC.d 0 1).hom
  have hker : LinearMap.ker ((selCx actSel).toCC.d 0 1).hom = LinearMap.ker ψ := by
    ext c
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    constructor
    · intro h
      change (((selCx actSel).toCC.d 0 1).hom c).2.2 = 0
      rw [h]
      rfl
    · intro h
      have h' : (((selCx actSel).toCC.d 0 1).hom c).2.2 = 0 := h
      rw [GCx.toCC_d_hom _ 0 1 rfl] at h' ⊢
      obtain ⟨a, u, x⟩ := c
      exact Prod.ext rfl (Prod.ext rfl h')
  rw [hker]
  have hrn := LinearMap.finrank_range_add_finrank_ker ψ
  have hr : Module.finrank (ZMod 2) (LinearMap.range ψ) ≤ Module.finrank (ZMod 2) (actSel.L.X 0) :=
    Submodule.finrank_le _
  rw [finrank_actP_zero h410 h51 h28] at hrn
  rw [finrank_actL_zero h28] at hr
  omega

/-- **The generic rank is positive**: both constructors give `2 ≤ genericRank`. -/
theorem two_le_genericRank (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    2 ≤ (activeGenuineCounts h410 h51 h28 h23 h788).genericRank ∧
      2 ≤ (activeActualCounts h410 h51 h28 h23 h788).genericRank := by
  rw [activeGenuineCounts_genericRank, activeActualCounts_genericRank]
  have h := (two_le_actL_zero h410 h51 h28).trans (Finset.single_le_sum
    (f := fun n => Module.finrank (ZMod 2) (actL.X n)) (fun _ _ => Nat.zero_le _)
    (show (0 : ℤ) ∈ actDegrees by decide))
  exact ⟨h, h⟩

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive

/-! ## Base change and the active comparison blocks over `𝔽₂[[t]]` -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open CategoryTheory CategoryTheory.Limits TensorProduct
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Manuscript.RC.SelmerComplex

/-! ### Base change of relation-indexed complexes -/

section BaseChange

variable {R : Type} [CommRing R] (A : Type) [CommRing A] [Algebra R A]

/-- The degreewise base change `A ⊗_R C` of a complex. -/
def bcG (C : GCx R) : GCx A where
  X n := ModuleCat.of A (A ⊗[R] C.X n)
  d i j h := (C.d i j h).baseChange A
  d_d i j k hij hjk x := by
    have h0 : (C.d j k hjk).comp (C.d i j hij) = 0 := LinearMap.ext (C.d_d i j k hij hjk)
    change ((C.d j k hjk).baseChange A ∘ₗ (C.d i j hij).baseChange A) x = 0
    rw [← LinearMap.baseChange_comp, h0, LinearMap.baseChange_zero]
    rfl

/-- The degreewise base change of a chain map. -/
def bcHom {C D : GCx R} (f : GHom C D) : GHom (bcG A C) (bcG A D) where
  f i j h := (f.f i j h).baseChange A
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    have hc : (f.f i₁ j₁ hj).comp (C.d i i₁ h₁) = (D.d j j₁ h₂).comp (f.f i j hij) :=
      LinearMap.ext (f.comm i i₁ j j₁ hij h₁ h₂ hj)
    change ((f.f i₁ j₁ hj).baseChange A ∘ₗ (C.d i i₁ h₁).baseChange A) x =
      ((D.d j j₁ h₂).baseChange A ∘ₗ (f.f i j hij).baseChange A) x
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hc]

/-- **A homotopy from `c` to `0`, relation-indexed**: `d h + h d = c` on `C`. -/
structure CHomotopy (C : GCx R) (c : R) where
  h : ∀ i j : ℤ, j + 1 = i → C.X i →ₗ[R] C.X j
  spec : ∀ (i j k : ℤ) (hji : j + 1 = i) (hik : i + 1 = k) (x : C.X i),
    C.d j i hji (h i j hji x) + h k i hik (C.d i k hik x) = c • x

/-- **Base change inverting `c` makes the complex acyclic.** -/
theorem bcG_acyclic_of_homotopy {C : GCx R} {c : R} (H : CHomotopy C c)
    (hc : IsUnit (algebraMap R A c)) : GAcyclic (bcG A C) := by
  obtain ⟨u, hu⟩ := hc
  have key : ∀ (i j k : ℤ) (hji : j + 1 = i) (hik : i + 1 = k) (x : A ⊗[R] C.X i),
      (C.d j i hji).baseChange A ((H.h i j hji).baseChange A x) +
        (H.h k i hik).baseChange A ((C.d i k hik).baseChange A x) = algebraMap R A c • x := by
    intro i j k hji hik x
    induction x using TensorProduct.inductionOn with
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        LinearMap.baseChange_tmul, ← TensorProduct.tmul_add, H.spec i j k hji hik m,
        TensorProduct.tmul_smul, algebraMap_smul]
    | add x y hx hy =>
      rw [map_add, map_add, map_add, map_add, smul_add, ← hx, ← hy]
      abel
  intro i j k hij hjk x hx
  refine ⟨((u⁻¹ : Aˣ) : A) • (H.h j i hij).baseChange A x, ?_⟩
  have h1 := key j i k hij hjk x
  have hx' : (C.d j k hjk).baseChange A x = 0 := hx
  rw [hx', map_zero, add_zero, ← hu] at h1
  change (C.d i j hij).baseChange A (((u⁻¹ : Aˣ) : A) • (H.h j i hij).baseChange A x) = x
  rw [map_smul, h1, smul_smul, Units.inv_mul, one_smul]

end BaseChange

/-! ### The active comparison blocks -/

section Blocks

variable {S : Type} [CommRing S]

/-- `S²` placed in degree one, zero elsewhere. -/
def degOne (S : Type) [CommRing S] : GCx S where
  X n := ModuleCat.of S (Fin (if n = 1 then 2 else 0) → S)
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

/-- Multiplication by a scalar, as a chain map of a complex to itself. -/
def smulGHom (c : S) (B : GCx S) : GHom B B where
  f i j h := c • (idGHom B).f i j h
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    change c • B.d i i₁ h₁ x = B.d i i₁ h₂ (c • x)
    rw [map_smul]

/-- **The active comparison block** `[S² --c--> S²]` in degrees `1, 2`: the cone of
multiplication by `c` on `S²` in degree one. -/
abbrev activeCone (S : Type) [CommRing S] (c : S) : GCx S := coneCx (smulGHom c (degOne S))

theorem toCC_smulGHom_comp (c c' : S) (B : GCx S) :
    GHom.toCC (smulGHom c B) ≫ GHom.toCC (smulGHom c' B) = GHom.toCC (smulGHom (c' * c) B) := by
  ext n x
  change c' • (c • x) = (c' * c) • x
  rw [smul_smul]

theorem toCC_smulGHom_one (B : GCx S) : GHom.toCC (smulGHom (1 : S) B) = 𝟙 _ := by
  ext n x
  change (1 : S) • x = x
  rw [one_smul]

/-- **If `c` is a unit, the active block is acyclic** (multiplication by `c` is an isomorphism, so
its cone is acyclic). -/
theorem activeCone_acyclic_of_isUnit {c : S} (hc : IsUnit c) :
    GAcyclic (activeCone S c) := by
  obtain ⟨u, rfl⟩ := hc
  have : IsIso (GHom.toCC (smulGHom (u : S) (degOne S))) :=
    ⟨⟨GHom.toCC (smulGHom ((u⁻¹ : Sˣ) : S) (degOne S)), by
      rw [toCC_smulGHom_comp, Units.inv_mul, toCC_smulGHom_one], by
      rw [toCC_smulGHom_comp, Units.mul_inv, toCC_smulGHom_one]⟩⟩
  exact coneCx_acyclic_of_quasiIso _ inferInstance

theorem degOne_X_subsingleton (n : ℤ) (hn : n ≠ 1) : Subsingleton ((degOne S).X n) :=
  ⟨fun a b => funext fun i => by
    have := i.2
    simp only [ite_eq_right hn] at this
    exact absurd this (Nat.not_lt_zero _)⟩

/-- **If `c` is not a unit, the active block is not acyclic**: `e₀` in degree two is a cycle that is
not a boundary. -/
theorem activeCone_not_acyclic {c : S} (hc : ¬ IsUnit c) : ¬ GAcyclic (activeCone S c) := by
  intro h
  have h3 : Subsingleton ((activeCone S c).X 3) := by
    have := degOne_X_subsingleton (S := S) 3 (by decide)
    have := degOne_X_subsingleton (S := S) (3 - 1) (by decide)
    change Subsingleton ((degOne S).X 3 × (degOne S).X (3 - 1))
    infer_instance
  let i0 : Fin (if (2 : ℤ) - 1 = 1 then 2 else 0) := ⟨0, by simp⟩
  let e0 : (degOne S).X (2 - 1) := Pi.single i0 1
  obtain ⟨y, hy⟩ := h 1 2 3 rfl rfl ((0 : (degOne S).X 2), e0) (Subsingleton.elim _ _)
  have h2 := congrArg Prod.snd hy
  change c • ((idGHom (degOne S)).f 1 (2 - 1) (by omega) y.1) - 0 = e0 at h2
  have h4 := congrFun h2 i0
  rw [sub_zero] at h4
  have h5 : e0 i0 = 1 := Pi.single_eq_same i0 1
  rw [h5] at h4
  apply hc
  exact IsUnit.of_mul_eq_one _ h4

/-- **The homotopy `d h + h d = c` on the active block**: `h (e, z) = (z, 0)`. -/
def activeHomotopy (c : S) : CHomotopy (activeCone S c) c where
  h i j hji := (LinearMap.inl S _ _).comp
    (((idGHom (degOne S)).f (i - 1) j (by omega)).comp (LinearMap.snd S _ _))
  spec i j k hji hik x := by
    obtain ⟨e, z⟩ := x
    subst hji hik
    refine Prod.ext ?_ ?_
    · change (0 : (degOne S).X (j + 1)) + (idGHom (degOne S)).f (j + 1 + 1 - 1) (j + 1) (by omega)
          (c • (idGHom (degOne S)).f (j + 1) (j + 1 + 1 - 1) (by omega) e - 0) = c • e
      rw [zero_add, sub_zero, map_smul, idGHom_f_f, idGHom_f_self]
    · change c • (idGHom (degOne S)).f j (j + 1 - 1) (by omega)
          ((idGHom (degOne S)).f (j + 1 - 1) j (by omega) z) - 0 + 0 = c • z
      rw [sub_zero, add_zero, idGHom_f_f, idGHom_f_self]

end Blocks

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive


/-! ## The active blocks after inverting `t` -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain TensorProduct
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Contrib.CloudB3RC53.ResidualTransfer
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.Limits

/-! ### The coefficient rings `𝔽₂[[t]]` and `𝔽₂((t))` -/

/-- `𝔽₂[[t]]`. -/
abbrev Rt : Type := PowerSeries (ZMod 2)

/-- `𝔽₂((t))`. -/
abbrev Kt : Type := LaurentSeries (ZMod 2)

theorem zmod2_units_eq_one (v : (ZMod 2)ˣ) : v = 1 := by
  revert v
  decide

/-- `1 + t` is a unit of `𝔽₂[[t]]`. -/
def onePlusT : Rtˣ :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr (by simp) : IsUnit (1 + PowerSeries.X : Rt)).unit

theorem onePlusT_val : (onePlusT : Rt) = 1 + PowerSeries.X := rfl

/-- **The entry `(1 + t)^e − 1` of the reduction of (4.4) at an active place** (tex 4619–4625). -/
def activeC (e : ℤ) : Rt := ((onePlusT ^ e : Rtˣ) : Rt) - 1

/-- The entry vanishes modulo `t`: the reduction modulo `t` of the active block is zero. -/
theorem activeC_constantCoeff (e : ℤ) : PowerSeries.constantCoeff (activeC e) = 0 := by
  have h : PowerSeries.constantCoeff ((onePlusT ^ e : Rtˣ) : Rt) = 1 := by
    have := zmod2_units_eq_one (Units.map (PowerSeries.constantCoeff (R := ZMod 2)).toMonoidHom
      (onePlusT ^ e))
    exact congrArg Units.val this
  rw [activeC, map_sub, h, map_one, sub_self]

/-- **Before inverting `t` the entry is not a unit.** -/
theorem activeC_not_isUnit (e : ℤ) : ¬ IsUnit (activeC e) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, activeC_constantCoeff]
  exact not_isUnit_zero

theorem onePlusT_ne_one : onePlusT ≠ 1 := by
  intro h
  have h1 := congrArg Units.val h
  rw [onePlusT_val, Units.val_one, add_eq_left] at h1
  exact PowerSeries.X_ne_zero h1

/-- The exponents at the active places are `±1`. -/
theorem activeC_ne_zero {e : ℤ} (he : e = 1 ∨ e = -1) : activeC e ≠ 0 := by
  intro h
  have h1 : onePlusT ^ e = 1 := Units.ext (sub_eq_zero.mp h)
  rcases he with rfl | rfl
  · exact onePlusT_ne_one (by simpa using h1)
  · exact onePlusT_ne_one (by simpa using h1)

/-- **`((1 + t)^e − 1)/t` is a unit** for `e = ±1` (tex 4623–4624). -/
theorem activeC_eq_X_mul {e : ℤ} (he : e = 1 ∨ e = -1) :
    ∃ v : Rtˣ, activeC e = PowerSeries.X * (v : Rt) := by
  rcases he with rfl | rfl
  · refine ⟨1, ?_⟩
    rw [activeC, zpow_one, onePlusT_val, Units.val_one, mul_one]
    ring
  · refine ⟨-onePlusT⁻¹, ?_⟩
    have hu : (onePlusT : Rt) * ((onePlusT⁻¹ : Rtˣ) : Rt) = 1 := Units.mul_inv onePlusT
    rw [activeC, zpow_neg, zpow_one, Units.val_neg]
    rw [onePlusT_val] at hu
    have h2 : (2 : Rt) = 0 := by
      have h : (2 : ZMod 2) = 0 := by decide
      have := congrArg (PowerSeries.C (R := ZMod 2)) h
      rwa [map_ofNat, map_zero] at this
    linear_combination (-1 : Rt) * hu +
      (-1 + ((onePlusT⁻¹ : Rtˣ) : Rt) + ((onePlusT⁻¹ : Rtˣ) : Rt) * PowerSeries.X) * h2

/-- **After inverting `t` the entry is a unit** (`𝔽₂((t))` is a field). -/
theorem activeC_isUnit_generic {e : ℤ} (he : e = 1 ∨ e = -1) :
    IsUnit (algebraMap Rt Kt (activeC e)) := by
  refine isUnit_iff_ne_zero.mpr fun h => activeC_ne_zero he ?_
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ZMod 2)
  rw [map_zero]
  exact h

/-! ### The active places -/

instance : Finite (NewPlaces SmallK SmallS SmallS') :=
  (smallS'_finite.subset Set.sdiff_subset).to_subtype

noncomputable instance : Fintype (NewPlaces SmallK SmallS SmallS') := Fintype.ofFinite _

/-- A chosen (oriented) place above `13`. -/
def orientedPlace : NewPlaces SmallK SmallS SmallS' := Classical.choice newPlaces_nonempty

/-- The exponent: `1` at the oriented place, `−1` at the other places above `13`. -/
def activeExp (q : NewPlaces SmallK SmallS SmallS') : ℤ := if q = orientedPlace then 1 else -1

theorem activeExp_cases (q : NewPlaces SmallK SmallS SmallS') :
    activeExp q = 1 ∨ activeExp q = -1 := by
  unfold activeExp
  split_ifs <;> simp

/-- **The active comparison blocks over `𝔽₂[[t]]`**: at each place above `13`,
`[𝔽₂[[t]]² --((1+t)^e − 1)--> 𝔽₂[[t]]²]` in degrees `1, 2`. -/
abbrev activeW : GCx Rt := piCx fun q : NewPlaces SmallK SmallS SmallS' =>
  activeCone Rt (activeC (activeExp q))

/-- **The same blocks after inverting `t`**: the base change of `activeW` to `𝔽₂((t))`. -/
abbrev activeW' : GCx Kt := bcG Kt activeW

/-- Homotopies on the factors give a homotopy on the product, for the product of the scalars. -/
def piHomotopy {S : Type} [CommRing S] {ι : Type} [Fintype ι] (A : ι → GCx S) (c : ι → S)
    (H : ∀ q, CHomotopy (A q) (c q)) : CHomotopy (piCx A) (∏ q, c q) where
  h i j hji := LinearMap.pi fun q =>
    (∏ q' ∈ Finset.univ.erase q, c q') • ((H q).h i j hji).comp (LinearMap.proj q)
  spec i j k hji hik x := by
    funext q
    change (A q).d j i hji ((∏ q' ∈ Finset.univ.erase q, c q') • (H q).h i j hji (x q)) +
      (∏ q' ∈ Finset.univ.erase q, c q') • (H q).h k i hik ((A q).d i k hik (x q)) =
        (∏ q, c q) • x q
    rw [map_smul, ← smul_add, (H q).spec i j k hji hik (x q), smul_smul,
      Finset.prod_erase_mul _ _ (Finset.mem_univ q)]

/-- The product of the entries of the active blocks. -/
def activeProd : Rt := ∏ q : NewPlaces SmallK SmallS SmallS', activeC (activeExp q)

theorem activeProd_isUnit_generic : IsUnit (algebraMap Rt Kt activeProd) := by
  rw [activeProd, map_prod]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun q _ =>
    (activeC_isUnit_generic (activeExp_cases q)).ne_zero)

theorem piCx_acyclic {S : Type} [CommRing S] {ι : Type} (A : ι → GCx S)
    (h : ∀ v, GAcyclic (A v)) : GAcyclic (piCx A) := by
  intro i j k hij hjk x hx
  have hv : ∀ v, (A v).d j k hjk (x v) = 0 := fun v => congrFun hx v
  choose y hy using fun v => h v i j k hij hjk (x v) (hv v)
  exact ⟨fun v => y v, funext hy⟩

theorem acyclic_of_piCx {S : Type} [CommRing S] {ι : Type} (A : ι → GCx S)
    (h : GAcyclic (piCx A)) (v : ι) : GAcyclic (A v) := by
  intro i j k hij hjk x hx
  let X : (piCx A).X j := Pi.single (M := fun w => (A w).X j) v x
  have hX : (piCx A).d j k hjk X = 0 := by
    funext w
    by_cases hw : w = v
    · subst hw
      change (A w).d j k hjk (Pi.single (M := fun w => (A w).X j) w x w) = 0
      rw [Pi.single_eq_same]
      exact hx
    · change (A w).d j k hjk (Pi.single (M := fun w => (A w).X j) v x w) = 0
      rw [Pi.single_eq_of_ne hw, map_zero]
  obtain ⟨y, hy⟩ := h i j k hij hjk X hX
  refine ⟨y v, ?_⟩
  have := congrFun hy v
  change (A v).d i j hij (y v) = Pi.single (M := fun w => (A w).X j) v x v at this
  rwa [Pi.single_eq_same] at this

/-- **The active comparison cones are not acyclic before inverting `t`.** -/
theorem activeW_not_acyclic : ¬ activeW.toCC.Acyclic := by
  rw [acyclic_toCC_iff]
  intro h
  exact activeCone_not_acyclic (activeC_not_isUnit (activeExp orientedPlace))
    (acyclic_of_piCx _ h orientedPlace)

/-- **After inverting `t` every active comparison cone is acyclic** (tex 4626–4631): the base
change of the active blocks to `𝔽₂((t))` is acyclic, by the homotopy `d h + h d = ∏ ((1+t)^e − 1)`
and the invertibility of that product in `𝔽₂((t))`. -/
theorem activeW'_acyclic : activeW'.toCC.Acyclic := by
  rw [acyclic_toCC_iff]
  exact bcG_acyclic_of_homotopy Kt
    (piHomotopy _ (fun q => activeC (activeExp q)) fun q => activeHomotopy _)
    activeProd_isUnit_generic

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive

/-! ## The free models over `𝔽₂[[t]]` and `𝔽₂((t))` and the constructor -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain TensorProduct
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Contrib.CloudB3RC53.ResidualTransfer
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.Limits

theorem homology_subsingleton_of_X' {S : Type} [CommRing S]
    {C : CochainComplex (ModuleCat.{0} S) ℤ} (n : ℤ)
    (h : Subsingleton (C.X n)) : Subsingleton (C.homology n) := by
  have : Subsingleton ((C.sc n).X₂) := h
  have hex : C.ExactAt n := (C.sc n).exact_of_isZero_X₂ (ModuleCat.isZero_of_subsingleton _)
  exact ModuleCat.subsingleton_of_isZero
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 hex)

theorem homology_finite_of_X' {S : Type} [Field S] {C : CochainComplex (ModuleCat.{0} S) ℤ}
    (n : ℤ) [Module.Finite S (C.X n)] : Module.Finite S (C.homology n) := by
  have : Module.Finite S (C.cycles n) :=
    Module.Finite.of_injective _ ((ModuleCat.mono_iff_injective (C.iCycles n)).1 inferInstance)
  exact Module.Finite.of_surjective _ ((ModuleCat.epi_iff_surjective (C.homologyπ n)).1 inferInstance)

/-! ### The free models over `𝔽₂[[t]]` and `𝔽₂((t))` -/

/-- **The smaller-support free model over `𝔽₂[[t]]`**: the residual cone over `𝔽₂` extended to
`𝔽₂[[t]]`. Its reduction modulo `t` is the residual cone. -/
abbrev afterP_G : GCx Rt := bcG Rt (selCx actSel)

abbrev afterP : CochainComplex (ModuleCat.{0} Rt) ℤ := afterP_G.toCC

/-- Its base change to `𝔽₂((t))`. -/
abbrev afterP'_G : GCx Kt := bcG Kt afterP_G

abbrev afterP' : CochainComplex (ModuleCat.{0} Kt) ℤ := afterP'_G.toCC

/-- **The original-support model over `𝔽₂[[t]]`**: the smaller-support model together with the
active comparison blocks at the places above `13` (the singular quotients of the change from the
unramified to the full condition). -/
abbrev afterQ_G : GCx Rt := prodCx afterP_G activeW

/-- **The generic original-support model over `𝔽₂((t))`**: the base change of the integral one. -/
abbrev afterQ'_G : GCx Kt := bcG Kt afterQ_G

abbrev afterQ' : CochainComplex (ModuleCat.{0} Kt) ℤ := afterQ'_G.toCC

/-- The inclusion of the smaller-support model, over `𝔽₂((t))`. -/
def afterIncl : GHom afterP'_G afterQ'_G := bcHom Kt (prodLift (idGHom afterP_G) (zeroGHom _ _))

/-- The projection onto the active blocks, over `𝔽₂((t))`. -/
def afterProj : GHom afterQ'_G activeW' := bcHom Kt (prodSnd afterP_G activeW)

/-- `0 → P' → Q' → W' → 0`, the generic change of condition. -/
def afterSES : ShortComplex (CochainComplex (ModuleCat.{0} Kt) ℤ) :=
  ShortComplex.mk (GHom.toCC afterIncl) (GHom.toCC afterProj) (by
    rw [GHom.toCC_comp]
    ext i x
    change ((LinearMap.snd Rt _ _).baseChange Kt ∘ₗ
      (LinearMap.inl Rt (afterP_G.X i) (activeW.X i)).baseChange Kt) x = 0
    rw [← LinearMap.baseChange_comp, LinearMap.snd_comp_inl, LinearMap.baseChange_zero]
    rfl)

theorem afterSES_shortExact : afterSES.ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
  let ι := (LinearMap.inl Rt (afterP_G.X i) (activeW.X i)).baseChange Kt
  let π := (LinearMap.snd Rt (afterP_G.X i) (activeW.X i)).baseChange Kt
  let ρ := (LinearMap.fst Rt (afterP_G.X i) (activeW.X i)).baseChange Kt
  let σ := (LinearMap.inr Rt (afterP_G.X i) (activeW.X i)).baseChange Kt
  have hρι : ∀ x, ρ (ι x) = x := fun x => by
    change ((LinearMap.fst Rt _ _).baseChange Kt ∘ₗ (LinearMap.inl Rt _ _).baseChange Kt) x = x
    rw [← LinearMap.baseChange_comp, LinearMap.fst_comp_inl, LinearMap.baseChange_id]
    rfl
  have hπσ : ∀ x, π (σ x) = x := fun x => by
    change ((LinearMap.snd Rt _ _).baseChange Kt ∘ₗ (LinearMap.inr Rt _ _).baseChange Kt) x = x
    rw [← LinearMap.baseChange_comp, LinearMap.snd_comp_inr, LinearMap.baseChange_id]
    rfl
  have hsplit : ∀ x, ι (ρ x) + σ (π x) = x := fun x => by
    change ((LinearMap.inl Rt _ _).baseChange Kt ∘ₗ (LinearMap.fst Rt _ _).baseChange Kt) x +
      ((LinearMap.inr Rt _ _).baseChange Kt ∘ₗ (LinearMap.snd Rt _ _).baseChange Kt) x = x
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, ← LinearMap.add_apply,
      ← LinearMap.baseChange_add]
    have hid : LinearMap.inl Rt (afterP_G.X i) (activeW.X i) ∘ₗ LinearMap.fst Rt _ _ +
        LinearMap.inr Rt (afterP_G.X i) (activeW.X i) ∘ₗ LinearMap.snd Rt _ _ = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      obtain ⟨a, b⟩ := x
      simp
    rw [hid, LinearMap.baseChange_id]
    rfl
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro z hz
    refine ⟨ρ z, ?_⟩
    have hz' : π z = 0 := hz
    have := hsplit z
    rw [hz', map_zero, add_zero] at this
    exact this
  · rw [ModuleCat.mono_iff_injective]
    intro a b h
    have h' : ι a = ι b := h
    rw [← hρι a, ← hρι b, h']
  · rw [ModuleCat.epi_iff_surjective]
    intro w
    exact ⟨σ w, hπσ w⟩

/-- **The text's transfer after inverting `t`**: since every active comparison block is acyclic over
`𝔽₂((t))`, the generic smaller-support model includes into the generic original-support model by a
quasi-isomorphism (tex 4626–4631). -/
theorem afterIncl_quasiIso : QuasiIso (GHom.toCC afterIncl) :=
  quasiIso_f_of_shortExact_acyclic afterSES_shortExact activeW'_acyclic

/-! ### Bounds and finiteness -/

theorem afterP'_X_subsingleton (h410 : MilneADT_I_4_10_totallyComplex) (h28 : MilneADT_I_2_8)
    (n : ℤ) (hn : n < 0 ∨ 3 < n) : Subsingleton (afterP'.X n) := by
  have h1 : Subsingleton ((selCx actSel).X n) := actP_X_subsingleton h410 h28 n hn
  have : Unique (Rt ⊗[ZMod 2] (selCx actSel).X n) := TensorProduct.uniqueRight
  have : Unique (Kt ⊗[Rt] (Rt ⊗[ZMod 2] (selCx actSel).X n)) := TensorProduct.uniqueRight
  change Subsingleton (Kt ⊗[Rt] (Rt ⊗[ZMod 2] (selCx actSel).X n))
  infer_instance

theorem activeW_X_subsingleton (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) :
    Subsingleton (activeW.X n) := by
  have := degOne_X_subsingleton (S := Rt) n h1
  have := degOne_X_subsingleton (S := Rt) (n - 1) (by omega)
  change Subsingleton (∀ q : NewPlaces SmallK SmallS SmallS',
    (degOne Rt).X n × (degOne Rt).X (n - 1))
  infer_instance

theorem afterQ'_X_subsingleton (h410 : MilneADT_I_4_10_totallyComplex) (h28 : MilneADT_I_2_8)
    (n : ℤ) (hn : n < 0 ∨ 3 < n) : Subsingleton (afterQ'.X n) := by
  have h1 : Subsingleton ((selCx actSel).X n) := actP_X_subsingleton h410 h28 n hn
  have : Unique (Rt ⊗[ZMod 2] (selCx actSel).X n) := TensorProduct.uniqueRight
  have h2 : Subsingleton (activeW.X n) := activeW_X_subsingleton n (by omega) (by omega)
  have : Subsingleton (afterP_G.X n × activeW.X n) := by
    change Subsingleton ((Rt ⊗[ZMod 2] (selCx actSel).X n) × activeW.X n)
    infer_instance
  have : Unique (Kt ⊗[Rt] (afterP_G.X n × activeW.X n)) := TensorProduct.uniqueRight
  change Subsingleton (Kt ⊗[Rt] (afterP_G.X n × activeW.X n))
  infer_instance

theorem afterP'_ge (h410 : MilneADT_I_4_10_totallyComplex) (h28 : MilneADT_I_2_8) :
    afterP'.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  have := afterP'_X_subsingleton h410 h28 n (Or.inl hn)
  exact ModuleCat.isZero_of_subsingleton _

theorem afterP'_le (h410 : MilneADT_I_4_10_totallyComplex) (h28 : MilneADT_I_2_8) :
    afterP'.IsStrictlyLE 3 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  have := afterP'_X_subsingleton h410 h28 n (Or.inr hn)
  exact ModuleCat.isZero_of_subsingleton _

/-- **The generic minimal model**: the cohomology of the generic original-support model, with zero
differential. -/
abbrev afterL : CochainComplex (ModuleCat.{0} Kt) ℤ := (homologyModel afterQ').toCC

theorem afterL_ge (h410 : MilneADT_I_4_10_totallyComplex) (h28 : MilneADT_I_2_8) :
    afterL.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  have : Subsingleton (afterL.X n) :=
    homology_subsingleton_of_X' n (afterQ'_X_subsingleton h410 h28 n (Or.inl hn))
  exact ModuleCat.isZero_of_subsingleton _

theorem afterL_le (h410 : MilneADT_I_4_10_totallyComplex) (h28 : MilneADT_I_2_8) :
    afterL.IsStrictlyLE 3 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  have : Subsingleton (afterL.X n) :=
    homology_subsingleton_of_X' n (afterQ'_X_subsingleton h410 h28 n (Or.inr hn))
  exact ModuleCat.isZero_of_subsingleton _

theorem afterP_free (n : ℤ) : Module.Free Rt (afterP.X n) := by
  change Module.Free Rt (Rt ⊗[ZMod 2] (selCx actSel).X n)
  infer_instance

theorem afterP_finite (h410 : MilneADT_I_4_10_totallyComplex) (h51 : MilneADT_I_5_1_totallyComplex)
    (h28 : MilneADT_I_2_8) (n : ℤ) : Module.Finite Rt (afterP.X n) := by
  have := actP_finite h410 h51 h28 n
  change Module.Finite Rt (Rt ⊗[ZMod 2] (selCx actSel).toCC.X n)
  infer_instance

theorem afterP'_finite (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (n : ℤ) :
    Module.Finite Kt (afterP'.X n) := by
  have := afterP_finite h410 h51 h28 n
  change Module.Finite Kt (Kt ⊗[Rt] afterP.X n)
  infer_instance

theorem afterQ'_finite (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (n : ℤ) :
    Module.Finite Kt (afterQ'.X n) := by
  have h1 : Module.Finite Rt (afterP_G.X n) := afterP_finite h410 h51 h28 n
  have hd : ∀ m, Module.Finite Rt ((degOne Rt).X m) := fun m => by
    change Module.Finite Rt (Fin _ → Rt)
    infer_instance
  have := hd n
  have := hd (n - 1)
  have : Module.Finite Rt (activeW.X n) := by
    change Module.Finite Rt (∀ q : NewPlaces SmallK SmallS SmallS',
      (degOne Rt).X n × (degOne Rt).X (n - 1))
    infer_instance
  change Module.Finite Kt (Kt ⊗[Rt] (afterP_G.X n × activeW.X n))
  infer_instance

theorem afterL_finite (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (n : ℤ) :
    Module.Finite Kt (afterL.X n) := by
  have := afterQ'_finite h410 h51 h28 n
  exact homology_finite_of_X' (C := afterQ') n

theorem afterL_minimal (i j : ℤ) (x : afterL.X i) :
    (afterL.d i j).hom x ∈
      IsLocalRing.maximalIdeal Kt • (⊤ : Submodule Kt (afterL.X j)) := by
  rw [homologyModel_d]
  exact Submodule.zero_mem _

/-- The reduction modulo `t` of the smaller-support model has the ranks of the residual cone. -/
theorem afterP_hred (n : ℤ) :
    Module.finrank Rt (afterP.X n) = Module.finrank (ZMod 2) ((selCx actSel).X n) :=
  Module.finrank_baseChange

/-- **The homotopy equivalence `L ≃ P'`**, through the generic original-support model `Q'`: the
cohomology representatives `L → Q'` and the inclusion `P' → Q'`, a quasi-isomorphism because the
active comparison blocks are acyclic after inverting `t`. -/
def afterE (h410 : MilneADT_I_4_10_totallyComplex) (h28 : MilneADT_I_2_8) :
    HomotopyEquiv afterL afterP' := by
  haveI := afterL_ge h410 h28
  haveI := afterL_le h410 h28
  haveI := afterP'_ge h410 h28
  haveI := afterP'_le h410 h28
  haveI := homologyModelTo_quasiIso afterQ'
  haveI := afterIncl_quasiIso
  exact (homotopyEquiv_of_zigzag afterL afterP' afterQ' 0 3 (homologyModelTo afterQ')
    (GHom.toCC afterIncl)).some

/-! ### The constructor with the transfer after inverting `t` -/

/-- **`residualRankCounts_afterT` on the active instance.** -/
def activeAfterTCounts (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) : ResidualRankCounts := by
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.G.X n) := actSel_G_finite h410 h51
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.U.X n) := actSel_U_finite h28
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.L.X n) := actSel_L_finite h28
  letI : ∀ n, Module.Free Rt (afterP.X n) := afterP_free
  letI : ∀ n, Module.Finite Rt (afterP.X n) := afterP_finite h410 h51 h28
  letI : afterP'.IsStrictlyGE 0 := afterP'_ge h410 h28
  letI : afterP'.IsStrictlyLE 3 := afterP'_le h410 h28
  letI : afterL.IsStrictlyGE 0 := afterL_ge h410 h28
  letI : afterL.IsStrictlyLE 3 := afterL_le h410 h28
  letI : ∀ n, Module.Finite Kt (afterP'.X n) := afterP'_finite h410 h51 h28
  letI : ∀ n, Module.Finite Kt (afterL.X n) := afterL_finite h410 h51 h28
  exact ZInQ.Contrib.CloudB3RC53.GenuineInst.residualRankCounts_afterT SmallK smallLocalModels h410 h51 h28 h23
    (-1) smallAlpha smallAlpha_radicand smallK_complex 66 (by decide) 0 (by simp) 5 (by decide)
    actD actD_prime actD_odd actCond actCond_derivative actCond_full_torsion
    smallInfinitePlace smallInfinitePlace_complex SmallS actSel actDegrees
    (Finset.Subset.refl _) actEG (act_hUm h28) (act_hLm h28) afterP
    (fun n _ => afterP_hred n) afterP' afterL 0 3 (fun n => ⟨LinearEquiv.refl _ _⟩)
    afterL_minimal (afterE h410 h28)

theorem activeAfterTCounts_genericRank (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    (activeAfterTCounts h410 h51 h28 h23).genericRank =
      ∑ n ∈ actDegrees, Module.finrank Kt (afterQ'.homology n) := rfl

theorem activeAfterTCounts_rankTot (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    (activeAfterTCounts h410 h51 h28 h23).rankTot =
      ∑ n ∈ actDegrees, Module.finrank (ZMod 2) ((selCx actSel).X n) := rfl

/-- **Non-vacuity of the constructor with the transfer after inverting `t`, on the active
instance.** -/
theorem residualRankCounts_afterT_active (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    (activeAfterTCounts h410 h51 h28 h23).genericRank ≤
        (activeAfterTCounts h410 h51 h28 h23).rankTot ∧
      (activeAfterTCounts h410 h51 h28 h23).genericRank ≤ 294 := by
  refine ⟨(activeAfterTCounts h410 h51 h28 h23).transfer, ?_⟩
  have hb := (activeAfterTCounts h410 h51 h28 h23).genericRank_le
  change (activeAfterTCounts h410 h51 h28 h23).genericRank ≤
    residualBoundConstant (2 * 66).primeFactors.card 0 actD.card at hb
  rwa [activeBound] at hb

/-- **The text's active case, after inverting `t`** (tex 4612–4631): at the places above `13` the
entries `(1+t)^e − 1` of the reduction of (4.4) vanish modulo `t` and are `t` times a unit; the
active comparison blocks are not acyclic over `𝔽₂[[t]]` but are acyclic over `𝔽₂((t))`; hence the
generic smaller-support model includes into the generic original-support model (the base change of
the integral one) by a quasi-isomorphism. -/
theorem afterT_active_case :
    Nonempty (NewPlaces SmallK SmallS SmallS') ∧
      (∀ q, PowerSeries.constantCoeff (activeC (activeExp q)) = 0 ∧
        ∃ v : Rtˣ, activeC (activeExp q) = PowerSeries.X * (v : Rt)) ∧
      ¬ activeW.toCC.Acyclic ∧ activeW'.toCC.Acyclic ∧ QuasiIso (GHom.toCC afterIncl) :=
  ⟨newPlaces_nonempty, fun q => ⟨activeC_constantCoeff _, activeC_eq_X_mul (activeExp_cases q)⟩,
    activeW_not_acyclic, activeW'_acyclic, afterIncl_quasiIso⟩

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive

/-! ## The generic rank is positive -/

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain TensorProduct
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Contrib.CloudB3RC53.ResidualTransfer
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.Limits

/-! ### The generic minimal model is nonzero -/

/-- The rank of a twice base-changed map is at most the rank of the map. -/
theorem finrank_range_bc_bc_le {V W : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) V] [Module.Finite (ZMod 2) W]
    (f : V →ₗ[ZMod 2] W) :
    Module.finrank Kt (LinearMap.range ((f.baseChange Rt).baseChange Kt)) ≤
      Module.finrank (ZMod 2) (LinearMap.range f) := by
  let g := ((LinearMap.range f).subtype.baseChange Rt).baseChange Kt
  have hfac : (f.baseChange Rt).baseChange Kt = g ∘ₗ (f.rangeRestrict.baseChange Rt).baseChange Kt := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    rfl
  have hle : LinearMap.range ((f.baseChange Rt).baseChange Kt) ≤ LinearMap.range g := by
    rw [hfac]
    exact LinearMap.range_comp_le_range _ _
  calc Module.finrank Kt (LinearMap.range ((f.baseChange Rt).baseChange Kt))
      ≤ Module.finrank Kt (LinearMap.range g) := Submodule.finrank_mono hle
    _ ≤ Module.finrank Kt (Kt ⊗[Rt] (Rt ⊗[ZMod 2] LinearMap.range f)) :=
        LinearMap.finrank_range_le g
    _ = Module.finrank (ZMod 2) (LinearMap.range f) := by
        rw [Module.finrank_baseChange, Module.finrank_baseChange]

/-- If nothing comes into degree `0`, then `H⁰` contains the kernel of the outgoing differential
(over any field). -/
theorem finrank_ker_le_homology_zero' {S : Type} [Field S]
    (C : CochainComplex (ModuleCat.{0} S) ℤ)
    [Module.Finite S (C.X 0)] (h : Subsingleton (C.X (-1))) :
    Module.finrank S (LinearMap.ker (C.d 0 1).hom) ≤ Module.finrank S (C.homology 0) := by
  have hd : C.d (-1) 0 = 0 := by
    ext x
    rw [Subsingleton.elim x 0, map_zero]
    rfl
  rw [← (C.isoHomologyπ (-1) 0 (by simp) hd).toLinearEquiv.finrank_eq]
  have hinjC := (ModuleCat.mono_iff_injective (C.iCycles 0)).1 inferInstance
  have : Module.Finite S (C.cycles 0) := Module.Finite.of_injective _ hinjC
  let k : ModuleCat.of S (LinearMap.ker (C.d 0 1).hom) ⟶ C.X 0 :=
    ModuleCat.ofHom (LinearMap.ker (C.d 0 1).hom).subtype
  have hk : k ≫ C.d 0 1 = 0 := by
    ext x
    exact x.2
  let l := C.liftCycles k 1 (by simp) hk
  have hl : Function.Injective l.hom := by
    intro x y hxy
    have := congrArg (C.iCycles 0).hom hxy
    have h1 := congrArg (fun f => f.hom x) (C.liftCycles_i k 1 (by simp) hk)
    have h2 := congrArg (fun f => f.hom y) (C.liftCycles_i k 1 (by simp) hk)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
    exact Subtype.ext (h1.symm.trans (this.trans h2))
  exact LinearMap.finrank_le_finrank_of_injective hl

/-- The rank of the degree-zero differential of the residual cone is at most `2·#S`. -/
theorem finrank_range_actP_d_le (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) :
    Module.finrank (ZMod 2) (LinearMap.range ((selCx actSel).toCC.d 0 1).hom) ≤
      2 * Fintype.card (Places SmallK SmallS) := by
  have hfin := actP_finite h410 h51 h28
  have := actSel_L_finite h28 (1 - 1)
  let ψ : (selCx actSel).toCC.X 0 →ₗ[ZMod 2] actSel.L.X (1 - 1) :=
    ((LinearMap.snd (ZMod 2) _ _).comp (LinearMap.snd (ZMod 2) _ _)).comp
      ((selCx actSel).toCC.d 0 1).hom
  have hker : LinearMap.ker ((selCx actSel).toCC.d 0 1).hom = LinearMap.ker ψ := by
    ext c
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    constructor
    · intro h
      change (((selCx actSel).toCC.d 0 1).hom c).2.2 = 0
      rw [h]
      rfl
    · intro h
      have h' : (((selCx actSel).toCC.d 0 1).hom c).2.2 = 0 := h
      rw [GCx.toCC_d_hom _ 0 1 rfl] at h' ⊢
      obtain ⟨a, u, x⟩ := c
      exact Prod.ext rfl (Prod.ext rfl h')
  have h1 := LinearMap.finrank_range_add_finrank_ker ((selCx actSel).toCC.d 0 1).hom
  have h2 := LinearMap.finrank_range_add_finrank_ker ψ
  have hr : Module.finrank (ZMod 2) (LinearMap.range ψ) ≤ Module.finrank (ZMod 2) (actSel.L.X 0) :=
    Submodule.finrank_le _
  rw [finrank_actL_zero h28] at hr
  rw [hker] at h1
  omega

/-- **The generic minimal model has at least two-dimensional `H⁰`.** -/
theorem two_le_afterL_zero (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) :
    2 ≤ Module.finrank Kt (afterL.X 0) := by
  have hfin := actP_finite h410 h51 h28
  have hP'fin := afterP'_finite h410 h51 h28
  have := hfin 1
  have := hfin 0
  -- `H⁰(Q') ≅ H⁰(P')`
  have hq : IsIso (HomologicalComplex.homologyMap (GHom.toCC afterIncl) 0) := by
    have := afterIncl_quasiIso
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance
  change 2 ≤ Module.finrank Kt (afterQ'.homology 0)
  rw [← (asIso (HomologicalComplex.homologyMap (GHom.toCC afterIncl) 0)).toLinearEquiv.finrank_eq]
  have hsub : Subsingleton (afterP'.X (-1)) := afterP'_X_subsingleton h410 h28 (-1) (Or.inl (by norm_num))
  refine le_trans ?_ (finrank_ker_le_homology_zero' afterP' hsub)
  -- the differential of `P'` is the double base change of that of the residual cone
  have e1 : ((selCx actSel).toCC.d 0 1).hom = (selCx actSel).d 0 1 rfl :=
    LinearMap.ext fun x => GCx.toCC_d_hom (selCx actSel) 0 1 rfl x
  have e2 : (afterP'.d 0 1).hom = afterP'_G.d 0 1 rfl :=
    LinearMap.ext fun x => GCx.toCC_d_hom afterP'_G 0 1 rfl x
  have hd : (afterP'.d 0 1).hom =
      ((((selCx actSel).toCC.d 0 1).hom.baseChange Rt).baseChange Kt) := by
    rw [e2, e1]
    rfl
  have hrn := LinearMap.finrank_range_add_finrank_ker (afterP'.d 0 1).hom
  have hdim : Module.finrank Kt (afterP'.X 0) = 2 + 2 * Fintype.card (Places SmallK SmallS) := by
    change Module.finrank Kt (Kt ⊗[Rt] (Rt ⊗[ZMod 2] (selCx actSel).toCC.X 0)) = _
    rw [Module.finrank_baseChange, Module.finrank_baseChange, finrank_actP_zero h410 h51 h28]
  have hr : Module.finrank Kt (LinearMap.range (afterP'.d 0 1).hom) ≤
      Module.finrank (ZMod 2) (LinearMap.range ((selCx actSel).toCC.d 0 1).hom) := by
    rw [hd]
    exact finrank_range_bc_bc_le ((selCx actSel).toCC.d 0 1).hom
  have hr2 := finrank_range_actP_d_le h410 h51 h28
  rw [hdim] at hrn
  omega

/-- **The generic rank is positive**: `2 ≤ genericRank ≤ rankTot`, and `genericRank ≤ 294`. -/
theorem two_le_afterT_genericRank (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    2 ≤ (activeAfterTCounts h410 h51 h28 h23).genericRank := by
  rw [activeAfterTCounts_genericRank]
  exact (two_le_afterL_zero h410 h51 h28).trans (Finset.single_le_sum
    (f := fun n => Module.finrank Kt (afterQ'.homology n)) (fun _ _ => Nat.zero_le _)
    (show (0 : ℤ) ∈ actDegrees by decide))

end ZInQ.Contrib.RC53Assist.ResidualWitnessActive

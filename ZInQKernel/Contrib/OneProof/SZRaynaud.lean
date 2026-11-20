import ZInQKernel.Contrib.OneProof.GaRigiditySGA7
import ZInQKernel.Contrib.OneProof.RaynaudSemistableOr
import ZInQKernel.Contrib.OneProof.NeronDVR
import ZInQKernel.Contrib.OneProof.GeomConnOfRationalPoint
import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed
import ZInQKernel.Contrib.OneProof.MulEtale

/-!
# sz-raynaud: diophantine_zq.tex L814-818 on the manuscript's own route

At a prime `p` the manuscript takes `F = L_v(A[3])` (`A[5]` if `p = 3`) and says: "Raynaud's criterion
`\cite[Theorem 3.5]{silverbergzarhin}` gives semistable reduction there. Its wild inertia acts trivially on each
`V_ℓ(A)` with `ℓ ≠ p`" (the second sentence carries no citation). This file states the two steps as leaves and proves
what they give:

* `SilverbergZarhinThm35` (LEAF, provenance (b): Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995), Thm 3.5, p. 406,
  cited by the manuscript; read from the page image 11-17): `m ≥ 3` invertible and `A[m]` rational ⇒ semistable
  reduction in Silverberg–Zarhin's sense (`IsSemistableResT`: identity component of the special fibre over the residue
  field an extension of an abelian variety by a torus, not necessarily split);
* `ElliotWildInertiaTrivial` (ELLIOT, provenance (a): uncited manuscript sentence, diophantine_zq.tex:817-818);
* `isSemistable_of_sz`: the named step from Silverberg–Zarhin's semistability to the kernel's (geometric special
  fibre, split torus), Stacks 04KV through dict-models' `isSemistable_of_resT`;
* `raynaudSemistable_of_sz35` (the kernel's Raynaud criterion over every DVR) and `raynaudSemistableSHOr_of_sz35`
  (the bundle field `raynaudSemistableSHOr`, SGA 7 IX 4.7, statement unchanged);
* `raynaudWildNF_of_leaves`: L814-818 in Lean (wild inertia fixes `A(K̄)[ℓⁿ]` once `A[m]` is rational);
* `elliot_of_semistableUnipotent`: the ELLIOT sentence from SGA 7 IX 3.5 and the on-the-spot glue
  `WildPeriodCoprime` (wild inertia is pro-`p`), not proved; a sanity check only;
* `def34_of_sz35`: Silverberg–Zarhin's output meets the hypothesis of ga-rigidity's two Déf. 3.4 rows (rigidity for
  `𝔾_a`).

The two SGA 7 rows (`sga7_IX_Cor3_3`, `sga7_IX_3_5_ForwardGeom`) have no counterpart on this route (see
docs/research/sz-raynaud.md). No `sorry`, no `axiom`; never imports `ZInQKernel.Contrib.OneProof.Main`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety Pts torsion galAct IsInertia UnipSq)
open ReductSplit ReductGlue ZInQ.HeightSplit

namespace SZRaynaud

/-! ## §1. Wild inertia -/

/-- **Wild inertia** of a valuation ring `w` of `Ω ⊇ K` (the first lower ramification group `G₁`; Serre, *Corps
locaux*, IV §1-§2; numbers UNVERIFIED): `σ` moves every nonzero `x` by less than `x`, i.e. `v_w(σx - x) > v_w(x)`,
equivalently `σx/x ≡ 1 mod 𝔪_w`. This is the valuation-ring form of the kernel's `wildSet`
(TailH: `‖σ z - z‖ < ‖z‖` for `z ≠ 0` in `ℚ̄_p`). -/
def IsWildInertia {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)
    (σ : Ω ≃ₐ[K] Ω) : Prop :=
  ∀ x : Ω, x ≠ 0 → w.valuation (σ x - x) < w.valuation x

/-! ## §2. Raynaud's criterion as Silverberg–Zarhin Theorem 3.5 states it -/

/-- **Semistable reduction in Silverberg–Zarhin's sense** (*Semistable reduction and torsion subgroups of abelian
varieties*, Ann. Inst. Fourier 45 (1995), §3, p. 405, read from the page image, scratch/sz-raynaud/sz-thm35-reading.md):
`A` has a Néron model over `O` whose special fibre over the residue field `k` has identity component an extension of
an abelian variety by a torus, not necessarily split (`DictModels.RaynaudOr.IsSemistableResT`). -/
def HasSemistableReductionSZ {K : Type} [Field K] (A : PkgI3.AbVar K) (O : ValuationSubring K) : Prop :=
  ∃ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel ∧ DictModels.RaynaudOr.IsSemistableResT 𝒩

/-- **LEAF `SilverbergZarhinThm35`** (Raynaud's criterion as the manuscript cites it, diophantine_zq.tex L816,
`\cite[Theorem 3.5]{silverbergzarhin}`: A. Silverberg, Yu. G. Zarhin, *Semistable reduction and torsion subgroups of
abelian varieties*, Ann. Inst. Fourier 45 (1995), 403-420, Theorem 3.5, p. 406; its proof is "see SGA 7 IX Prop. 4.7").
Provenance (b): a cited print, in the manuscript's bibliography (L11077). Read from the page image by the fleet's
print reader (11-17; scratch/sz-raynaud/sz-thm35-reading.md): `X` an abelian variety over a field `F` with a discrete
valuation `v`, `n` a positive integer not divisible by the residue characteristic, the points of `X_n` defined over
an extension of `F` unramified over `v`; if `n ≥ 3`, `X` has semistable reduction at `v` (§3, p. 405: the identity
component of the special fibre of the Néron model is an extension of an abelian variety by a torus, not necessarily
split).

*Lean form* (a specialization): `F = K` with the valuation ring `O`; the unramified extension is `K` itself (all of
`A(K̄)[m]` is `K`-rational, which is how the manuscript uses it, `F = L_v(A[3])`); "not divisible by the residue
characteristic" is `IsUnit (m : O)`; the conclusion is Silverberg–Zarhin's semistability over the residue field
(`IsSemistableResT`, torus not necessarily split) for every Néron model (Néron models are unique up to unique
isomorphism, so "the" Néron model is "every" Néron model). -/
def SilverbergZarhinThm35 : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K) (m : ℕ), 3 ≤ m → IsUnit (m : O) →
    (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
    ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel → DictModels.RaynaudOr.IsSemistableResT 𝒩

/-- **The step from Silverberg–Zarhin's semistability to the kernel's** (geometric special fibre, split torus,
`GroupModelO.IsSemistable`): base change `k → k̄`, with connectedness of the identity component after base change
from Stacks 04KV (`AVGlue.GeomConnOfRationalPoint`, proved `geomConnOfRationalPoint_proof`); this is dict-models'
`DictModels.RaynaudOr.isSemistable_of_resT`. -/
theorem isSemistable_of_sz {K : Type} [Field K] {A : PkgI3.AbVar K} {O : ValuationSubring K}
    (𝒩 : GroupModelO A O) (h : DictModels.RaynaudOr.IsSemistableResT 𝒩) : 𝒩.IsSemistable :=
  DictModels.RaynaudOr.isSemistable_of_resT geomConnOfRationalPoint_proof 𝒩 h

theorem hasSemistableReduction_of_sz {K : Type} [Field K] {A : PkgI3.AbVar K} {O : ValuationSubring K}
    (h : HasSemistableReductionSZ A O) : HasSemistableReduction A O := by
  obtain ⟨𝒩, h1, h2⟩ := h
  exact ⟨𝒩, h1, isSemistable_of_sz 𝒩 h2⟩

/-- **Raynaud's criterion over every DVR, the kernel's form** (`ReductSplit.RaynaudSemistable`, statement
unchanged) from Silverberg–Zarhin 3.5 and the step `isSemistable_of_sz`. No strict henselization, no base change of
the DVR: the manuscript's route. -/
theorem raynaudSemistable_of_sz35 (h : SilverbergZarhinThm35) : ReductSplit.RaynaudSemistable :=
  fun K _ O _ A m hm hu ht 𝒩 h𝒩 => isSemistable_of_sz 𝒩 (h K O A m hm hu ht 𝒩 h𝒩)

/-- **The field `raynaudSemistableSHOr`, statement unchanged** (SGA 7 IX 4.7 over a strictly henselian DVR, with the
or-conclusion), as the specialization of Silverberg–Zarhin 3.5 to strictly henselian discrete valuation rings (left
disjunct). -/
theorem raynaudSemistableSHOr_of_sz35 (h : SilverbergZarhinThm35) :
    DictModels.RaynaudOr.RaynaudSemistableSHOr :=
  fun K _ O _ _ A m hm hu ht => Or.inl (h K O A m hm hu ht)

/-! ## §3. The manuscript's sentence at L817-818 -/

/-- **LEAF `ElliotWildInertiaTrivial`** (ELLIOT: uncited manuscript sentence, diophantine_zq.tex:817-818: wild inertia
of `F` acts trivially on each `V_ℓ(A)` with `ℓ ≠ p`, said of `F = L_v(A[3])` right after "Raynaud's criterion gives
semistable reduction there"). Provenance (a): in diophantine_zq.tex, no citation. *Lean form*, in the manuscript's
setting (an abelian variety over a number field, at a finite place): `K` a number field, `O ⊆ K` a discrete valuation
ring, `Ω` an algebraic closure of `K`, `w` a valuation ring of `Ω` over `O`, `ℓ` a prime invertible in `O`; "its wild
inertia" is the wild inertia subgroup of `w` in `Gal(Ω/K)`, which is that of the completion `F = K_O` (the
decomposition group of `w` is the Galois group of the completion; the manuscript likewise treats `G_F` inside the
global Galois group acting on `V_ℓ(A)`), and semistable reduction at `O` is semistable reduction over `F` (Néron
models commute with completion, BLR 7.2/1, the tree's field `blr_7_2_1`);
if `A` has semistable reduction at `O` in the sense the manuscript takes from Silverberg–Zarhin
(`HasSemistableReductionSZ`), every wild inertia element `σ` of `w` (`IsInertia`, `IsWildInertia`) acts trivially on
`T_ℓ(A) = lim A(Ω)[ℓⁿ]` (`galTΩ`). `T_ℓ` for `V_ℓ = T_ℓ ⊗ ℚ_ℓ`: `T_ℓ` is torsion-free and embeds in `V_ℓ`, so
trivial on `V_ℓ` gives trivial on `T_ℓ` (a consequence of the sentence). True and standard (SGA 7 IX 3.5's
unipotence with wild inertia pro-`p`; `elliot_of_semistableUnipotent` proves it from those), but the manuscript cites
nothing for it. -/
def ElliotWildInertiaTrivial : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReductionSZ A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → IsWildInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ t = t

/-! ## §4. L814-818 in Lean: wild inertia fixes `A[ℓⁿ]` once `A[m]` is rational -/

/-- **D2 on the manuscript's route** (diophantine_zq.tex L814-818), at number fields, in the objects of r6
(`PkgI2.RaynaudCriterionNF`): `O` a discrete valuation ring of the number field `K`, `w` over it in `K̄`, `m ≥ 3`
invertible in `O` with `A[m]` fixed by `Gal(K̄/K)`; then every wild inertia element of `w` fixes `A(K̄)[ℓⁿ]` for every
prime `ℓ` invertible in `O`. (r6 gives `(σ-1)² = 0` for every inertia element instead.) -/
def RaynaudWildNF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (m : ℕ), 3 ≤ m → IsUnit (m : O) →
      (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
          ∀ x ∈ torsion A (AlgebraicClosure K) m, galAct A σ x = x) →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ → IsWildInertia w σ →
        ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
          ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), galAct A σ x = x

/-- From `σ = 1` on `T_ℓ` to `σ x = x` at a point lifted to level `n`. -/
theorem fix_of_tate {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (B : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (σ : Ω ≃ₐ[K] Ω) (t : TΩ B Ω ℓ) (n : ℕ) (x : B.Pt Ω)
    (ht : t.1 n = Additive.ofMul x) (h : galTΩ B ℓ σ t = t) : B.galAct σ x = x := by
  have h' := congrArg (fun s : TΩ B Ω ℓ => Additive.toMul (s.1 n)) h
  simp only [galTΩ, PkgI3.Tate.map_apply, ht, MonoidHom.toAdditive_apply_apply, toMul_ofMul] at h'
  exact h'

/-- **L814-818 proved from its two leaves** (Silverberg–Zarhin 3.5 and the ELLIOT sentence), the Néron field at
number fields (existence of a Néron model, as in r6's proof `GapNeron.raynaudCriterion_leavesNF`), and proved glue:
Galois-fixed `m`-torsion is rational (`[m]` étale, `mulEtaleAbelianScheme_proof`) and the lift of `A(K̄)[ℓⁿ]` to `T_ℓ` (Mumford's torsion count, `mumfordTorsionAlgClosed_proof`). -/
theorem raynaudWildNF_of_leaves (hSZ : SilverbergZarhinThm35) (hE : ElliotWildInertiaTrivial)
    (hN : GapNeron.NeronSchemeModelExistsDVRNF) : RaynaudWildNF := by
  intro K _ _ O _ w hw A _ m hm hmO hrat σ hσ hwild ℓ hℓ hℓO n x hx
  have : Fact ℓ.Prime := ⟨hℓ⟩
  let B := ObjBridge.ofGrp A
  have hF := ReductGlue.fixedTorsionRational_of_mulEtale
    ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof
  have hT := AvSplit.torsionStructure_of_mumford
    ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  have hss := hSZ K O B m hm hmO
    (hF K B m (natCast_ne_zero_of_isUnit O hmO) (fun σ x hx => hrat σ x hx))
  obtain ⟨𝒩, h𝒩⟩ := GapNeron.exists_neron_groupModelNF hN O B
  obtain ⟨t, ht⟩ := exists_tate_lift A hT ℓ (natCast_ne_zero_of_isUnit O hℓO) n x hx
  exact fix_of_tate B ℓ σ t n x ht
    (hE K O (AlgebraicClosure K) w hw B ⟨𝒩, h𝒩, hss 𝒩 h𝒩⟩ ℓ hℓO σ hσ hwild t)

/-! ## §5. The ELLIOT sentence from SGA 7 IX 3.5 (sanity: what the kernel's old route used) -/

/-- **GLUE `WildPeriodCoprime`** (on-the-spot statement, in neither the manuscript nor Silverberg–Zarhin; standard:
wild inertia is pro-`p`, `p` the residue characteristic, and acts on the finite set `A(Ω)[ℓⁿ]` through a finite
quotient, so with period a power of `p`, prime to `ℓ`; Serre, *Corps locaux*, IV §2, numbers UNVERIFIED). Not
proved here; only used to show that the ELLIOT sentence follows from SGA 7 IX 3.5. -/
def WildPeriodCoprime : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → IsWildInertia w σ →
      ∀ (n : ℕ) (x : A.Pt Ω), x ^ (ℓ ^ n) = 1 →
        ∃ N : ℕ, Nat.Coprime N (ℓ ^ n) ∧ (A.galAct σ)^[N] x = x

/-- The `n`-th component of an element of `T_ℓ` is killed by `ℓⁿ`. -/
theorem pow_smul_tate {ℓ : ℕ} [Fact ℓ.Prime] {M : Type} [AddCommGroup M] (t : PkgI3.Tate.T ℓ M) (n : ℕ) :
    (ℓ ^ n) • t.1 n = 0 := by
  induction n with
  | zero => simpa using t.2.1
  | succ n ih => rw [pow_succ, mul_smul, t.2.2 n, ih]

/-- **The ELLIOT sentence from the kernel's old route**: SGA 7 IX 3.5's unipotence (`ReductSplit.SemistableUnipotent`,
which the field `sga7_IX_3_5_ForwardGeom` gives through `UnipotentForward.semistableUnipotent_of_forwardGeom`) and
the glue `WildPeriodCoprime` give `ElliotWildInertiaTrivial`. The converse fails (the ELLIOT sentence says nothing
about tame inertia), so the manuscript's route does not give `SemistableUnipotent`. -/
theorem elliot_of_semistableUnipotent (hU : SemistableUnipotent) (hP : WildPeriodCoprime) :
    ElliotWildInertiaTrivial := by
  intro K _ _ O _ Ω _ _ _ w hw A hA ℓ _ hℓO σ hσ hwild t
  have hA' := hasSemistableReduction_of_sz hA
  apply Subtype.ext
  funext n
  set x : A.Pt Ω := Additive.toMul (t.1 n) with hxdef
  have ht : t.1 n = Additive.ofMul x := rfl
  have hx : x ^ (ℓ ^ n) = 1 := by
    have := pow_smul_tate t n
    rw [ht] at this
    exact this
  have hu := unipSq_of_tate A ℓ σ t n x ht (hU K O Ω w hw A hA' ℓ hℓO σ hσ t)
  obtain ⟨N, hcop, hit⟩ := hP K O Ω w hw A ℓ hℓO σ hσ hwild n x hx
  have hfix : A.galAct σ x = x :=
    PkgI2.fixed_of_unipSq_of_iterate (ObjBridge.toGrp A) σ x ℓ n N 1 (by rwa [pow_one]) hx hu
      (by rwa [pow_one])
  show Additive.ofMul (A.galAct σ (Additive.toMul (t.1 n))) = t.1 n
  rw [← hxdef, hfix]
  rfl

/-! ## §6. Silverberg–Zarhin's output meets the hypothesis of the two Déf. 3.4 rows (GaRigidity) -/

/-- **Silverberg–Zarhin's semistability gives Déf. 3.4's** ("no `𝔾_a` in the identity component of the geometric
special fibre", `GaRigidity.SGA7.IsSemistableDef34`, the hypothesis of the rows `SGA7_IX_Cor3_3_Def34` and
`SGA7_IX_3_5_ForwardGeom_Def34`): the step `isSemistable_of_sz` (Stacks 04KV), then rigidity for `𝔾_a`
(`GaRigidity.SGA7.isSemistableDef34_of_isSemistable`, from `GaRigidity.noGaSubgroup_of_semiAbelian`). -/
theorem isSemistableDef34_of_sz {K : Type} [Field K] {A : PkgI3.AbVar K} {O : ValuationSubring K}
    (𝒩 : GroupModelO A O) (h : DictModels.RaynaudOr.IsSemistableResT 𝒩) :
    GaRigidity.SGA7.IsSemistableDef34 𝒩 :=
  GaRigidity.SGA7.isSemistableDef34_of_isSemistable 𝒩 (isSemistable_of_sz 𝒩 h)

theorem hasSemistableReductionDef34_of_sz {K : Type} [Field K] {A : PkgI3.AbVar K} {O : ValuationSubring K}
    (h : HasSemistableReductionSZ A O) : GaRigidity.SGA7.HasSemistableReductionDef34 A O :=
  GaRigidity.SGA7.hasSemistableReductionDef34_of_has (hasSemistableReduction_of_sz h)

/-- **Raynaud's criterion with Déf. 3.4's conclusion** from Silverberg–Zarhin 3.5: when `A[m]` (`m ≥ 3` invertible) is
rational, every Néron model has no `𝔾_a` in the identity component of its geometric special fibre, which is what the
two Déf. 3.4 rows take as hypothesis. -/
theorem def34_of_sz35 (h : SilverbergZarhinThm35) :
    ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
      (A : PkgI3.AbVar K) (m : ℕ), 3 ≤ m → IsUnit (m : O) →
      (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
        ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
      ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel → GaRigidity.SGA7.IsSemistableDef34 𝒩 :=
  fun K _ O _ A m hm hu ht 𝒩 h𝒩 => isSemistableDef34_of_sz 𝒩 (h K O A m hm hu ht 𝒩 h𝒩)

end SZRaynaud

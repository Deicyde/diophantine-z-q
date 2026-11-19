import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate17Chain
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate17Frob

/-!
# Lane RC32's presentation at the text's objects

Manuscript `diophantine_zq.tex`, Section `sec:arithmetic` (tex 2720–2741: `K = ℚ(√k)`,
`A_i = (ℤ/2^i)[t]/t^i`, `M_i = (T₂E ⊗ A_i)(χ_h Ψ_i)`), Lemma `ex:arith-conjugate-duality`
(tex 2778–2796), the support comparisons (tex 3455–3498) and Lemma
`ex:arith-common-coordinate` (tex 4142–4194) at the stages of the inner limit (tex 4385–4451).

The free objects `K, S₀, S, M, Δ, place, X, EU` of `GenuineStageSTUM` are pinned:

* (a) `K = C.K` for the coefficient datum `C`, with `K = ℚ(r)`, `r² = k` (`ActualPresentation`);
* (b) `actualM A s = MinS` of lane E2 at `i = s`, the actual `(T₂E ⊗ A_s)(χ_{h_x} Ψ_s)` with
  `W = E_ℓ ⊗ K`, a module over `StageRing s` through `stageEquiv s` (`mcoefModule`, which is lane
  E2's `mcoefModuleK` with `stageIsoA s`);
* (c) `actualConds A (s + 1)` is lane E2's `stageCondsK` (lane RC29's Kummer conditions at `Pk`,
  full at `S₀ − Pk`; `actualConds_succ`, by definition); at the zero ring `StageRing 0` the full
  conditions (`stageCondsK` needs `NeZero s`);
* (d) `actualX A s j = urRep (StageRing s) M_s` at `place j`, `f = urId`, and `actualEU` the split
  inclusions of the genuine inflations (`actualEU_i`: from the specification of
  `exists_genuineSplitsS`, not by `rfl`);
* (e) `A.S = S₀ ∪ range pl` and `pl j ∉ S₀` (`ActualPresentation.S`, field `hw`);
* (f) the instances, all PROVED: the discrete topology of `StageRing s` for the quotient topology
  (`stageRing_discreteTopology`), `IsOpenKer` of the characters, `Module`, `SMulCommClass`,
  `Module.Free` (a rank-two basis `actualBasis`), `Finite`, `ContinuousSMul` of `M_s`, and
  `ContinuousSMul`, `Module.Free` of `X`; the others come from lanes RC26, RC28;
* (g) `ActualGenuineStageSTUM A`: the genuine stage chains on these objects (the leaf
  `CommonCoordinateInputsGenuine` of `CommonCoordinate17Leaf.lean` uses the same objects);
* (h) **`actualFrob`**, **`actualSteps`** (`GenuineStageSteps.ofFrob`, with `q i = ps[i]`) and
  **`actualSteps_stageFrobAt`**: the Frobenius fields and the leaf's Frobenius data, PROVED from
  the presentation, through the leaf's matrix over a general support `K_{S₀}`
  (`tateBasisAt`, `frobMatrixAt_frobMatStage_at`, `exists_stageFrobInput_at`).

Remaining inputs: the GLUE fields `full` (Néron–Ogg–Shafarevich), `moving` (the prescribed value
`ξ_s(Fr_q) = 1`), `movingConj` (the anticyclotomy of `Ψ_s`), and the data fields of
`ActualPresentation`.

Kinds: definitions, PROVED, and GLUE (fields of `ActualPresentation`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain TensorProduct
open Matrix Filter ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion MilneADT_I_2_8)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.CloudB3RC53.Duality (baseChangeAct baseChangeAct_tmul)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Local (IwasawaGenerators GenuineCochainsInjective)
open ZInQ.Contrib.CloudB3E2.NormCochain (alphaStage alphaShap stageCondsK stageIsoA
  PsiTrivialAt2N univChar)
open scoped PowerSeries.WithPiTopology

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-! ### The stage rings are discrete -/

/-- **The stage rings are discrete** for the quotient topology of `Λ` (tex 4385–4451:
`stageIdeal s` is open). Kind: PROVED. -/
instance stageRing_discreteTopology (s : ℕ) : DiscreteTopology (StageRing s) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  have himg : Ideal.Quotient.mk (stageIdeal s) '' ((fun b : LamI => b - a) ⁻¹'
      (stageIdeal s : Set LamI)) = {Ideal.Quotient.mk (stageIdeal s) a} := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact Ideal.Quotient.eq.mpr hb
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      refine ⟨a, ?_, hy.symm⟩
      change a - a ∈ stageIdeal s
      rw [sub_self]
      exact Submodule.zero_mem _
  rw [← himg]
  exact QuotientRing.isOpenMap_coe _ _
    ((continuous_sub_right a).isOpen_preimage _ (ZInQ.Manuscript.RC.Limits.stageIdeal_isOpen s))

/-! ### The leaf's Frobenius matrix over a general coefficient support -/

section FrobAt

open ZInQ.Contrib.RC53Assist.InnerLimitArith (basisQ tateSEquiv tateSEquiv_gksOfQ_smul
  rhoKMatrix rhoKMatrix_eq_toMatrix gksOfQ)
open ZInQ.Contrib.RC53Assist.FrobeniusMatch (integersEquiv)
open ZInQ.Contrib.ChebFD.C10 (Zbar)
open ZInQ.Manuscript.RC.PrintsArith (GalQ)

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] (C : TateCoef E)
  (S₀ : Set (HeightOneSpectrum (𝓞 C.K))) [HasFullTwoTorsion C.K S₀ (E.baseChange C.K)]

/-- **The basis of the datum, transported to `T₂E` over `K_{S₀}`** (tex 2836–2838): lane RC28's
`tateBasis` over `K_S`, carried to `T₂E` over `ℚ̄` and back to `T₂E` over `K_{S₀}`.
Kind: definition. -/
def tateBasisAt : Module.Basis (Fin 2) ℤ_[2] (TateS C.K S₀ (E.baseChange C.K)) :=
  (basisQ C.S E C.e).map (tateSEquiv S₀ E C.e).symm

/-- **The matrix of a restricted rational element in `tateBasisAt`** is the matrix of `ρ_T`
in the basis of the datum (tex 2836–2838, 4209–4213). Kind: PROVED. -/
theorem tateMat_tateBasisAt (g : GalQ)
    (hg : ∀ x : C.K, g (C.e (algebraMap C.K (AlgebraicClosure C.K) x)) =
      C.e (algebraMap C.K (AlgebraicClosure C.K) x)) :
    tateMat (tateBasisAt C S₀) (gksOfQ S₀ C.e g hg) = rhoKMatrix C.S E C.e g := by
  rw [rhoKMatrix_eq_toMatrix]
  ext a b
  simp only [tateMat, tateBasisAt, LinearMap.toMatrix_apply, Module.Basis.map_repr,
    Module.Basis.map_apply, LinearEquiv.trans_apply, DistribSMul.toLinearMap_apply,
    LinearEquiv.symm_symm]
  rw [tateSEquiv_gksOfQ_smul, LinearEquiv.apply_symm_apply]

/-- **The stage basis over `K_{S₀}` transported along `γ`** (tex 2836–2838, 4176–4184).
Kind: definition. -/
def tateStageBasisAt (s : ℕ) (γ : GKS C.K S₀) :
    StageRing s ⊗[ℤ] Lev C.K S₀ (E.baseChange C.K) s ≃ₗ[StageRing s] (Fin 2 → StageRing s) :=
  (LinearEquiv.baseChange ℤ (StageRing s) _ _
    (DistribMulAction.toAddEquiv (Lev C.K S₀ (E.baseChange C.K) s) γ⁻¹).toIntLinearEquiv).trans
    (stageBasis (tateBasisAt C S₀) s)

/-- **The leaf's Frobenius matrix at a place outside `S₀`** (tex 4144–4145, 4176–4184,
4209–4213): if `Frob_w = γ Fr_q|_{K_{S₀}} γ⁻¹`, then `id ⊗ Frob_w` has the matrix
`frobMatStage C q s` in `tateStageBasisAt C S₀ s γ`. Kind: PROVED. -/
theorem frobMatrixAt_frobMatStage_at {q : ℕ} (hfix : FrobQFixes C q)
    {S : Set (HeightOneSpectrum (𝓞 C.K))} (w : NewPlaces C.K S₀ S) (s : ℕ) {γ : GKS C.K S₀}
    (hγ : urFrobElt C.K w = γ * gksOfQ S₀ C.e (frobQ q) hfix * γ⁻¹) :
    FrobMatrixAt (tateStageBasisAt C S₀ s γ) w (frobMatStage C q s) := by
  intro x
  have hF : ∀ y, stageBasis (tateBasisAt C S₀) s
      (baseChangeAct (StageRing s) _ (gksOfQ S₀ C.e (frobQ q) hfix) y) =
        Matrix.toLin' (frobMatStage C q s) (stageBasis (tateBasisAt C S₀) s y) := by
    intro y
    rw [stageBasis_baseChangeAct, tateMat_tateBasisAt C S₀ (frobQ q) hfix]
    rfl
  refine toLin'_transport (stageBasis (tateBasisAt C S₀) s) (gksOfQ S₀ C.e (frobQ q) hfix)
    (urFrobElt C.K w) (DistribMulAction.toAddEquiv _ γ⁻¹) (fun t => ?_) _ hF x
  change γ⁻¹ • urFrobElt C.K w • t = gksOfQ S₀ C.e (frobQ q) hfix • γ⁻¹ • t
  rw [hγ, smul_smul, smul_smul, mul_assoc γ, inv_mul_cancel_left]

omit [E.IsElliptic] [HasFullTwoTorsion C.K S₀ (E.baseChange C.K)] in
/-- **The Frobenius at one of the two places of a split prime is conjugate to `Fr_q`**
(tex 4144–4145): the prime of `ℤ̄` defining `frobQ q` lies above `v` or `v'`. Kind: PROVED. -/
theorem frobQ_conj_split_at {q : ℕ} (hq : q.Prime) (hfix : FrobQFixes C q)
    {S : Set (HeightOneSpectrum (𝓞 C.K))} {w w' : NewPlaces C.K S₀ S}
    (habove : ∀ I : Ideal (𝓞 C.K), I.IsPrime → (q : 𝓞 C.K) ∈ I →
      I = w.1.asIdeal ∨ I = w'.1.asIdeal)
    (hcard : Nat.card (𝓞 C.K ⧸ w.1.asIdeal) = q) (hcard' : Nat.card (𝓞 C.K ⧸ w'.1.asIdeal) = q) :
    (∃ γ : GKS C.K S₀, urFrobElt C.K w = γ * gksOfQ S₀ C.e (frobQ q) hfix * γ⁻¹) ∨
      ∃ γ : GKS C.K S₀, urFrobElt C.K w' = γ * gksOfQ S₀ C.e (frobQ q) hfix * γ⁻¹ := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, hPp, hPZ, hF⟩ := isFrobAtC10_frobQ hq
  have := hPp
  have hIp : ((P.comap (integersEquiv C.e)).under (𝓞 C.K)).IsPrime := Ideal.IsPrime.under _ _
  have hqI : (q : 𝓞 C.K) ∈ (P.comap (integersEquiv C.e)).under (𝓞 C.K) := by
    have hpP : ((q : ℕ) : Zbar) ∈ P := ZInQ.Contrib.ChebFD.HSyn.natCast_mem P q hPZ
    change integersEquiv C.e (algebraMap (𝓞 C.K) (𝓞 (AlgebraicClosure C.K)) (q : 𝓞 C.K)) ∈ P
    simpa only [map_natCast] using hpP
  rcases habove _ hIp hqI with h | h
  · exact Or.inl (urFrobElt_conj_of_above C.e (frobQ q) q P hPZ hF hfix w h hcard)
  · exact Or.inr (urFrobElt_conj_of_above C.e (frobQ q) q P hPZ hF hfix w' h hcard')

end FrobAt

/-! ### The two places above a split prime -/

section SplitPair

variable {K : Type} [Field K] [NumberField K]

/-- **The two places above a split prime** (tex 2720–2722, 4142–4145): `v' = κ(v)`, the primes
of `𝒪_K` containing `q` are `v` and `v'`, both of residue cardinality `q`.
Kind: definition. -/
structure SplitPair (κ : K ≃+* K) (q : ℕ) (v v' : HeightOneSpectrum (𝓞 K)) : Prop where
  /-- the second place is the conjugate of the first -/
  conj : v' = conjPlace κ v
  /-- the primes of `𝒪_K` containing `q` are the two places -/
  above : ∀ I : Ideal (𝓞 K), I.IsPrime → (q : 𝓞 K) ∈ I → I = v.asIdeal ∨ I = v'.asIdeal
  /-- the first place has residue cardinality `q` -/
  card : Nat.card (𝓞 K ⧸ v.asIdeal) = q
  /-- the second place has residue cardinality `q` -/
  card' : Nat.card (𝓞 K ⧸ v'.asIdeal) = q

omit [NumberField K] in
/-- The two places of a split pair can be exchanged when `κ² = 1` (tex 4171). Kind: PROVED. -/
theorem SplitPair.symm {κ : K ≃+* K} (hκ : ∀ x, κ (κ x) = x) {q : ℕ}
    {v v' : HeightOneSpectrum (𝓞 K)} (h : SplitPair κ q v v') : SplitPair κ q v' v where
  conj := by rw [h.conj, conjPlace_conjPlace κ hκ]
  above I hI hq := (h.above I hI hq).symm
  card := h.card'
  card' := h.card

end SplitPair

/-! ### The stage Frobenius inputs at both places of a step, over a general support -/

section StepAt

open ZInQ.Contrib.RC53Assist.InnerLimitArith (gksOfQ)

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] (C : TateCoef E)
  {S₀ : Set (HeightOneSpectrum (𝓞 C.K))} [HasFullTwoTorsion C.K S₀ (E.baseChange C.K)]

/-- **(1) The leaf's matrix in a stage basis at a place of a split prime, over `K_{S₀}`**
(tex 4144–4145, 4176–4184): `FrobMatrixAt eT w (frobMatStage C q s)` for some stage basis.
Kind: PROVED. -/
theorem exists_frobMatrixAt_at (Cc : ActualConj C.K S₀) {q : ℕ} (hq : q.Prime)
    (hfix : FrobQFixes C q) {S : Set (HeightOneSpectrum (𝓞 C.K))} {w w' : NewPlaces C.K S₀ S}
    (hpl : SplitPair Cc.κ q w.1 w'.1) (s : ℕ) :
    ∃ eT : StageRing s ⊗[ℤ] Lev C.K S₀ (E.baseChange C.K) s ≃ₗ[StageRing s]
      (Fin 2 → StageRing s), FrobMatrixAt eT w (frobMatStage C q s) := by
  rcases frobQ_conj_split_at C S₀ hq hfix hpl.above hpl.card hpl.card' with ⟨γ, hγ⟩ | ⟨γ, hγ⟩
  · exact ⟨_, frobMatrixAt_frobMatStage_at C S₀ hfix w s hγ⟩
  · obtain ⟨g, hg⟩ := frobConjugatePlaces_proved S Cc w' w (hpl.symm
      (actualConj_kappa_kappa Cc)).conj
    exact ⟨_, frobMatrixAt_conj Cc (E.baseChange C.K)
      (ZInQ.Manuscript.RC.KummerMaps.tate_baseChange_map_kappa E Cc) _ hg
      (frobMatrixAt_frobMatStage_at C S₀ hfix w' s hγ)⟩

omit [E.IsElliptic] [HasFullTwoTorsion C.K S₀ (E.baseChange C.K)] in
/-- **The quadratic character at the Frobenius of a place of a split prime is `(n/q)`**
(tex 2790–2795, 4286–4292), over `K_{S₀}`. Kind: PROVED. -/
theorem quadChar_urFrobElt_split_at (Cc : ActualConj C.K S₀) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hfix : FrobQFixes C q) {S : Set (HeightOneSpectrum (𝓞 C.K))}
    {w w' : NewPlaces C.K S₀ S} (hpl : SplitPair Cc.κ q w.1 w'.1) (sh : KS C.K S₀) {h : C.K}
    (hs : sh ^ 2 = algebraMap C.K (KS C.K S₀) h) (hs0 : sh ≠ 0) {n : ℤ} (hn : h = (n : C.K))
    (hqn : ¬ (q : ℤ) ∣ n) :
    ((quadChar sh hs hs0 (urFrobElt C.K w) : ℤˣ) : ℤ) = jacobiSym n q := by
  have hval := quadChar_gksOfQ_frobQ C.e sh hs hs0 hn hq hq2 hqn hfix
  rcases frobQ_conj_split_at C S₀ hq hfix hpl.above hpl.card hpl.card' with ⟨γ, hγ⟩ | ⟨γ, hγ⟩
  · rw [hγ, map_mul, map_mul, map_inv, mul_inv_cancel_comm, hval]
  · obtain ⟨g, hg⟩ := frobConjugatePlaces_proved S Cc w' w (hpl.symm
      (actualConj_kappa_kappa Cc)).conj
    have hκh : Cc.κ h = h := by rw [hn, map_intCast]
    rw [hg, map_mul, map_mul, map_inv, mul_inv_cancel_comm, quadChar_conj Cc sh hs hs0 hκh, hγ,
      map_mul, map_mul, map_inv, mul_inv_cancel_comm, hval]

/-- **(5) The stage Frobenius inputs at both places of one step, over `K_{S₀}`** (tex 4171,
4176–4184): at an unused split prime `q` with places `w`, `w' = κ(w)`, `StageFrobInput` with
`(frobMatStage, z)` at `w` and `(frobMatStage, z⁻¹)` at `w'`. Kind: PROVED. -/
theorem exists_stageFrobInput_at (Cc : ActualConj C.K S₀) (Fam : Family)
    (hQ : ∀ q ∈ Fam.Q, q.Prime) (x : Addr Fam.b) (s : ℕ) (sh : KS C.K S₀) {h : C.K}
    (hs : sh ^ 2 = algebraMap C.K (KS C.K S₀) h) (hs0 : sh ≠ 0)
    (hn : h = ((Fam.h x : ℤ) : C.K)) {Δ : Type} [CommGroup Δ] (π : GKS C.K S₀ →* Δ)
    (ψ : Δ →* (Acoef s)ˣ) (hξ : MovingAnticyclotomic Cc π ψ) {q : ℕ}
    {S : Set (HeightOneSpectrum (𝓞 C.K))} {w w' : NewPlaces C.K S₀ S} (hq2 : q ≠ 2)
    (hqQ : q ∈ Fam.Q) (hun : Fam.lam q x = 0) (hfix : FrobQFixes C q)
    (hpl : SplitPair Cc.κ q w.1 w'.1) (hmov : MovingValueAt s π ψ w) :
    (∃ eT : StageRing s ⊗[ℤ] Lev C.K S₀ (E.baseChange C.K) s ≃ₗ[StageRing s]
        (Fin 2 → StageRing s), StageFrobInput eT (stageRingChar s (alphaStage s sh hs hs0 π ψ))
          w (frobMatStage C q s) (stageMk s (zAt Fam x q : Lambda))) ∧
      ∃ eT : StageRing s ⊗[ℤ] Lev C.K S₀ (E.baseChange C.K) s ≃ₗ[StageRing s]
        (Fin 2 → StageRing s), StageFrobInput eT (stageRingChar s (alphaStage s sh hs hs0 π ψ))
          w' (frobMatStage C q s) (stageMk s (((zAt Fam x q)⁻¹ : Lambdaˣ) : Lambda)) := by
  have hq := hQ q hqQ
  have hqn := not_dvd_h_of_unused Fam hQ hqQ hun
  have hχ := quadChar_urFrobElt_split_at C Cc hq hq2 hfix hpl sh hs hs0 hn hqn
  have hz : CharValueAt (stageRingChar s (alphaStage s sh hs hs0 π ψ)) w
      (stageMk s (zAt Fam x q : Lambda)) := by
    rw [stageMk_zAt Fam hQ hqQ hun s]
    exact charValueAt_alphaStage_of_quad sh hs hs0 π s ψ w hχ hmov
  obtain ⟨e₁, he₁⟩ := exists_frobMatrixAt_at C Cc hq hfix hpl s
  obtain ⟨e₂, he₂⟩ := exists_frobMatrixAt_at C Cc hq hfix
    (hpl.symm (actualConj_kappa_kappa Cc)) s
  obtain ⟨g, hg⟩ := frobConjugatePlaces_proved S Cc w w' hpl.conj
  have hκh : Cc.κ h = h := by rw [hn, map_intCast]
  have hα := stageRingChar_conj s Cc _ (alphaStage_conj Cc sh hs hs0 hκh π s ψ hξ)
  have hzi : stageMk s (zAt Fam x q : Lambda) *
      stageMk s (((zAt Fam x q)⁻¹ : Lambdaˣ) : Lambda) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  exact ⟨⟨e₁, he₁, hz⟩, ⟨e₂, he₂,
    charValueAt_of_anticyclotomic hz hzi (anticyclotomicAt_of_conj Cc hα hg)⟩⟩

end StepAt

/-! ### The actual presentation of the leaf at an address -/

section Presentation

variable {ℓ : ℕ}

/-- **The actual presentation of the leaf at an address `x` of `Fam`** (tex 2720–2741,
2778–2796, 3455–3498, 4142–4194): the parameters that pin lane RC32's presentation to the text's
objects. Fields and kinds:

* `r`, `hr`, `hgen` (definition; tex 2720): `K = ℚ(√k)`, `k = D.kfin`;
* `hprime`, `split` (definition; tex 2720–2722, 2678–2680): the graph primes are odd primes,
  prime to `k` and split in `K`;
* `S₀` (definition; tex 2729–2741, 3455–3463): the support of the coefficients (the primes
  above `2N`, of the twist and the conductors of the moving characters);
* `full` (GLUE: Néron–Ogg–Shafarevich, Silverman AEC VII.7.1; tex 2836–2838):
  `E[2^∞] ⊆ E(K_{S₀})`;
* `Cc` (definition; tex 2778): an actual complex conjugation, `S₀` stable;
* `sh`, `hs`, `hs0` (definition; tex 2726): `√h_x ∈ K_{S₀}`, the twist `χ_h`, `h = h_x`;
* `Dg`, `π`, `ψ`, `hπ` (definition; tex 2729–2741, 2779–2785): the moving character
  `Ψ_s = ψ_s ∘ π_s` at the stage `s`, through a finite quotient, continuous;
* `Pk`, `hΨ` (definition; tex 2729–2730, 2743–2760): the places of the old Kummer conditions,
  where `Ψ_s` is trivial;
* `ι`, `pl`, `hw`, `pidx`, `ps`, `hnd`, `hps`, `hnew`, `places` (definition; tex 4142–4146):
  the indices and places of the chain (outside `S₀`), the order of the unused primes, each
  relaxed once, the two places of the `i`-th step above the `i`-th unused prime;
* `moving` (GLUE; tex 2731–2736): `ψ_s(π_s(Frob_w)) = 1 + t` at the first place of each index;
* `movingConj` (GLUE; tex 2781–2788): `Ψ_s(τgτ⁻¹) = Ψ_s(g)⁻¹`.

Kind: definition (data). -/
structure ActualPresentation (C : TateCoef (Ecurve ℓ)) (D : RCData ℓ) (Fam : Family)
    (x : Addr Fam.b) : Type 1 where
  /-- `√k ∈ K` (definition; tex 2720) -/
  r : C.K
  /-- `r² = k` (definition; tex 2720) -/
  hr : r ^ 2 = ((D.kfin : ℤ) : C.K)
  /-- `K = ℚ(r)` (definition; tex 2720) -/
  hgen : Algebra.adjoin ℚ {r} = ⊤
  /-- the graph primes are odd primes (definition; tex 2678–2680, 4143) -/
  hprime : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2
  /-- the graph primes are prime to `k` and split in `K` (definition; tex 2720–2722) -/
  split : ∀ q ∈ Fam.Q, ¬ (q : ℤ) ∣ D.kfin ∧ IsSquare ((D.kfin : ℤ) : ZMod q)
  /-- the support of the coefficients (definition; tex 2729–2741, 3455–3463) -/
  S₀ : Set (HeightOneSpectrum (𝓞 C.K))
  /-- `E[2^∞] ⊆ E(K_{S₀})` (GLUE: Néron–Ogg–Shafarevich, Silverman AEC VII.7.1;
  tex 2836–2838) -/
  full : HasFullTwoTorsion C.K S₀ ((Ecurve ℓ).baseChange C.K)
  /-- an actual complex conjugation (definition; tex 2778) -/
  Cc : ActualConj C.K S₀
  /-- `√h_x ∈ K_{S₀}` (definition; tex 2726) -/
  sh : KS C.K S₀
  /-- `sh² = h_x` (definition; tex 2726) -/
  hs : sh ^ 2 = algebraMap C.K (KS C.K S₀) ((Fam.h x : ℤ) : C.K)
  /-- `sh ≠ 0` (definition; tex 2726) -/
  hs0 : sh ≠ 0
  /-- the finite quotients of the moving characters (definition; tex 2779–2785) -/
  Dg : ℕ → Type
  /-- they are commutative groups (definition) -/
  [Dg_comm : ∀ s, CommGroup (Dg s)]
  /-- they are finite (definition) -/
  [Dg_fin : ∀ s, Finite (Dg s)]
  /-- the quotient maps (definition; tex 2779–2785) -/
  π : ∀ s, GKS C.K S₀ →* Dg s
  /-- the values of the moving characters (definition; tex 2783) -/
  ψ : ∀ s, Dg s →* (Acoef s)ˣ
  /-- the moving characters are continuous (definition; tex 2729) -/
  hπ : ∀ s, IsOpen ((π s).ker : Set (GKS C.K S₀))
  /-- the places of the old Kummer conditions (definition; tex 2743–2760) -/
  Pk : Set (HeightOneSpectrum (𝓞 C.K))
  /-- the moving characters are trivial there (definition; tex 2729–2730) -/
  hΨ : ∀ s, PsiTrivialAt2N s (π s) (ψ s) Pk
  /-- the indices of the chain (definition; tex 4142–4146) -/
  ι : Type
  /-- decidable equality of the indices (definition) -/
  [decι : DecidableEq ι]
  /-- the two places of each index (definition; tex 4142–4146) -/
  pl : ι × Bool → HeightOneSpectrum (𝓞 C.K)
  /-- they are outside the support of the coefficients (definition; tex 3470–3498) -/
  hw : ∀ j, pl j ∉ S₀
  /-- the index relaxed at each step (definition; tex 4142–4146) -/
  pidx : ℕ → ι
  /-- the order of the unused primes (definition; tex 4142–4146) -/
  ps : List ℕ
  /-- each unused prime is relaxed once (definition; tex 4142–4146) -/
  hnd : ps.Nodup
  /-- the chain relaxes exactly the unused primes (definition; tex 4142–4146) -/
  hps : ps.toFinset = unusedAt Fam x
  /-- each relaxed index is new (definition; tex 4142–4146) -/
  hnew : ∀ i < ps.length, pidx i ∉ chainT pidx i
  /-- the two places of the `i`-th step lie above the `i`-th unused prime (definition;
  tex 4142–4146) -/
  places : ∀ i < ps.length, SplitPair Cc.κ (ps.getD i 1) (pl (pidx i, false)) (pl (pidx i, true))
  /-- the prescribed value of the moving character at the first place (GLUE; tex 2731–2736) -/
  moving : ∀ s (p : ι), MovingValueAt s (π s) (ψ s)
    (⟨pl (p, false), Set.mem_union_right S₀ (Set.mem_range_self (p, false)), hw (p, false)⟩ :
      NewPlaces C.K S₀ (S₀ ∪ Set.range pl))
  /-- the moving characters are anticyclotomic (GLUE; tex 2781–2788) -/
  movingConj : ∀ s, MovingAnticyclotomic Cc (π s) (ψ s)

attribute [instance] ActualPresentation.Dg_comm ActualPresentation.Dg_fin ActualPresentation.decι

namespace ActualPresentation

variable {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ} {Fam : Family} {x : Addr Fam.b}
  (A : ActualPresentation C D Fam x)

/-- `E[2^∞] ⊆ E(K_{S₀})` as an instance (GLUE `full`; tex 2836–2838). Kind: definition. -/
instance fullInst : HasFullTwoTorsion C.K A.S₀ ((Ecurve ℓ).baseChange C.K) := A.full

/-- **The Selmer support** `S = S₀ ∪ {places of the chain}` (tex 3455–3463, 4142–4146).
Kind: definition. -/
abbrev S : Set (HeightOneSpectrum (𝓞 C.K)) := A.S₀ ∪ Set.range A.pl

/-- `S₀ ⊆ S` (tex 3455–3463). Kind: PROVED. -/
theorem hS : A.S₀ ⊆ A.S := Set.subset_union_left

/-- **The places of the chain as places of `S`** (tex 4142–4146). Kind: definition. -/
abbrev place (j : A.ι × Bool) : Places C.K A.S :=
  ⟨A.pl j, Set.mem_union_right A.S₀ (Set.mem_range_self j)⟩

/-- The places of the chain are outside `S₀` (tex 3470–3498). Kind: PROVED. -/
theorem hwp (j : A.ι × Bool) : (A.place j).1 ∉ A.S₀ := A.hw j

/-- **The stage character** `α_s = χ_{h_x} Ψ_s` (lane E2's `alphaStage`; tex 2726, 2791).
Kind: definition. -/
abbrev alpha (s : ℕ) : GKS C.K A.S₀ →* (Acoef s)ˣ :=
  alphaStage s A.sh A.hs A.hs0 (A.π s) (A.ψ s)

end ActualPresentation

end Presentation

/-! ### The objects of the presentation and their instances -/

section Objects

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} (A : ActualPresentation C D Fam x)

/-- A composite `ψ ∘ π` has open kernel when `π` has (tex 2729). Kind: PROVED. -/
theorem isOpenKer_comp_of_isOpen {G Δ R : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Δ] [Monoid R] (π : G →* Δ) (hπ : IsOpen (π.ker : Set G))
    (ψ : Δ →* Rˣ) : IsOpenKer (ψ.comp π) :=
  ⟨Subgroup.isOpen_mono (H₁ := π.ker) (fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.comp_apply, hg, map_one]) hπ⟩

/-- **The stage character has open kernel** (tex 2726–2729). Kind: PROVED. -/
instance alpha_isOpenKer (s : ℕ) : IsOpenKer (A.alpha s) :=
  @isOpenKer_charMul _ _ _ _ _ _ _ _ (isOpenKer_map (quadChar A.sh A.hs A.hs0) (intUnitsTo _))
    (isOpenKer_comp_of_isOpen (A.π s) (A.hπ s) (A.ψ s))

/-- **Lane E2's Shapiro-level character has open kernel** (tex 2726–2729). Kind: PROVED. -/
instance alphaShap_isOpenKer (s : ℕ) : IsOpenKer (alphaShap A.sh A.hs A.hs0 (A.π s)) :=
  @isOpenKer_charMul _ _ _ _ _ _ _ _ (isOpenKer_map (quadChar A.sh A.hs A.hs0) (intUnitsTo _))
    (isOpenKer_comp_of_isOpen (A.π s) (A.hπ s) (univChar (A.Dg s)))

/-- **`M_s = (E[2^s] ⊗ A_s)(α_s)` over the stage ring of the chain** through `stageEquiv s`
(lane E2's `mcoefModuleK` with `stageIsoA s`, `mcoefModuleK_stage_eq`; tex 2724–2727,
4385–4451). Kind: definition. -/
instance mcoefModule (s : ℕ) :
    Module (StageRing s) (Mcoef C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s (A.alpha s)) :=
  stageCompModule s (A.alpha s) _

/-- The Galois action on `M_s` commutes with the stage ring (tex 2724–2727). Kind: PROVED. -/
instance mcoefSMulComm (s : ℕ) : SMulCommClass (GKS C.K A.S₀) (StageRing s)
    (Mcoef C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s (A.alpha s)) :=
  stageComp_smulCommClass s (A.alpha s) _

/-- **The rank-two stage basis of `M_s`** (tex 2724–2727, 2836–2838): `stageCoefEquiv` followed
by the stage basis of lane RC28's `tateBasis`. Kind: definition. -/
def mcoefBasis (s : ℕ) : Module.Basis (Fin 2) (StageRing s)
    (Mcoef C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s (A.alpha s)) :=
  Module.Basis.ofEquivFun ((stageCoefEquiv s _ (A.alpha s)).trans
    (stageBasis (tateBasis (K := C.K) (S := A.S₀) (W := (Ecurve ℓ).baseChange C.K)) s))

/-- **`M_s` is free of rank two over the stage ring** (tex 2724–2727, 2836–2838).
Kind: PROVED. -/
instance mcoefFree (s : ℕ) : Module.Free (StageRing s)
    (Mcoef C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s (A.alpha s)) :=
  Module.Free.of_basis (mcoefBasis A s)

/-- `M_s` is discrete for the stage ring (tex 2724–2727). Kind: PROVED. -/
instance mcoefContinuousConstSMul (s : ℕ) : ContinuousConstSMul (StageRing s)
    (Mcoef C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s (A.alpha s)) :=
  ⟨fun _ => continuous_of_discreteTopology⟩

/-- **The actual coefficient module at the stage `s`** (tex 2724–2727, 3455–3463): lane E2's
`MinS` at `i = s`, `M_s = (T₂E ⊗ A_s)(χ_{h_x} Ψ_s)` over `G_{K,S₀}` inflated to `G_{K,S}`, a
module over `StageRing s` through `stageEquiv s` (`mcoefModule`). Kind: definition. -/
abbrev actualM (s : ℕ) : Type := MinS A.hS ((Ecurve ℓ).baseChange C.K) s (A.alpha s)

/-- **The rank-two stage basis of the actual module** (tex 2724–2727). Kind: definition. -/
def actualBasis (s : ℕ) : Module.Basis (Fin 2) (StageRing s) (actualM A s) :=
  mcoefBasis A s

/-- `M_s` is free of rank two over the stage ring (tex 2724–2727). Kind: PROVED. -/
instance actualM_free (s : ℕ) : Module.Free (StageRing s) (actualM A s) :=
  inferInstanceAs (Module.Free (StageRing s)
    (Mcoef C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s (A.alpha s)))

/-- `M_s` is finite (tex 2724–2727). Kind: PROVED. -/
instance actualM_finite (s : ℕ) : Finite (actualM A s) :=
  inferInstanceAs (Finite (Mcoef C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s (A.alpha s)))

/-- **The unramified representations at the places of the chain** (tex 3470–3498): lane E2's
`urRep (StageRing s) M_s` at `place j`. Kind: definition. -/
abbrev actualX (s : ℕ) : (j : A.ι × Bool) → TopRep.{0} (StageRing s) (GUr C.K (A.place j).1) :=
  urChainRep A.place A.hwp (Mcoef C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s (A.alpha s))

/-- The unramified representations are discrete modules (tex 3470–3498). Kind: PROVED. -/
instance actualX_continuousSMul (s : ℕ) (j : A.ι × Bool) :
    ContinuousSMul (GUr C.K (A.place j).1) (actualX A s j).V :=
  urRep_continuousSMul (StageRing s) (Mcoef C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s (A.alpha s))
    (newPlace (A.place j) (A.hwp j))

/-- The unramified representations are free over the stage ring (tex 3470–3498).
Kind: PROVED. -/
instance actualX_free (s : ℕ) (j : A.ι × Bool) : Module.Free (StageRing s) (actualX A s j).V :=
  inferInstanceAs (Module.Free (StageRing s)
    (Mcoef C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s (A.alpha s)))

/-- The splits of the genuine inflations exist at the stage rings (tex 3470–3487,
4385–4451; `exists_genuineSplitsS`). Kind: PROVED. -/
theorem actualEU_exists (s : ℕ) :
    ∃ EU : ∀ j, SplitInclusion (genuineUq C.K A.S (StageRing s) (A.place j) (actualX A s j))
        (genuineLq C.K A.S (StageRing s) (actualM A s) (A.place j)),
      ∀ j, (EU j).i = genuineιq C.K A.S (StageRing s) (actualM A s) (A.place j) (actualX A s j)
        (urId A.hS (StageRing s) (Mcoef C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s (A.alpha s))
          (newPlace (A.place j) (A.hwp j)))
        (urId_compat A.hS (StageRing s)
          (Mcoef C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s (A.alpha s)) (A.place j) (A.hwp j)) :=
  exists_genuineSplitsS C.K A.S (StageRing s) (actualM A s) A.place (actualX A s) _ _
    (fun j => (urId_bijective (StageRing s) _ A.hS (newPlace (A.place j) (A.hwp j))).1)

/-- **The splits of the presentation**: split inclusions of the genuine inflations along
`urId` (tex 3470–3487, 4385–4451). Kind: definition. -/
def actualEU (s : ℕ) (j : A.ι × Bool) :
    SplitInclusion (genuineUq C.K A.S (StageRing s) (A.place j) (actualX A s j))
      (genuineLq C.K A.S (StageRing s) (actualM A s) (A.place j)) :=
  Classical.choose (actualEU_exists A s) j

/-- **The inclusions of the splits are the genuine inflations** along `f j = urId` (the field
`hE` of `GenuineStageSteps`; tex 3470–3487). Kind: PROVED. -/
theorem actualEU_i (s : ℕ) (j : A.ι × Bool) :
    (actualEU A s j).i = ofCCHom (urToLocal_galois C.K A.S (A.place j) (actualX A s j)
      (urId A.hS (StageRing s) (Mcoef C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s (A.alpha s))
        (newPlace (A.place j) (A.hwp j)))
      (urId_compat A.hS (StageRing s)
        (Mcoef C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s (A.alpha s)) (A.place j) (A.hwp j))) :=
  Classical.choose_spec (actualEU_exists A s) j

/-- **The old local conditions of the presentation** (tex 2743–2760): at a stage `s + 1`
lane E2's `stageCondsK` (lane RC29's actual old conditions: Kummer at `Pk`, full at `S₀ − Pk`)
over `StageRing (s + 1)`; at the degenerate stage `0` (the zero ring) the full conditions.
Kind: definition. -/
def actualConds : (s : ℕ) → LocalConditions (StageRing s) (GKS C.K A.S)
    (fun v : Places C.K A.S₀ => Gloc C.K v.1) (fun v => locMap C.K A.S v.1) (actualM A s)
  | 0 => relaxedConditions (StageRing 0) (GKS C.K A.S) (fun v : Places C.K A.S₀ => Gloc C.K v.1)
      (fun v => locMap C.K A.S v.1) (actualM A 0)
  | s + 1 =>
    letI := acoefTop (s + 1)
    haveI := acoefTop_discrete (s + 1)
    letI := stageIsoA (s + 1)
    stageCondsK A.hS ((Ecurve ℓ).baseChange C.K) (s + 1) A.sh A.hs A.hs0
      (HasFullTwoTorsion.full (s + 1)) (A.π (s + 1)) (A.ψ (s + 1)) A.Pk (A.hΨ (s + 1))
      (StageRing (s + 1))

/-- **At a positive stage the conditions are lane E2's `stageCondsK`** (tex 2743–2760); this
holds by definition. Kind: PROVED. -/
theorem actualConds_succ (s : ℕ) :
    actualConds A (s + 1) =
      (letI := acoefTop (s + 1)
      haveI := acoefTop_discrete (s + 1)
      letI := stageIsoA (s + 1)
      stageCondsK A.hS ((Ecurve ℓ).baseChange C.K) (s + 1) A.sh A.hs A.hs0
        (HasFullTwoTorsion.full (s + 1)) (A.π (s + 1)) (A.ψ (s + 1)) A.Pk (A.hΨ (s + 1))
        (StageRing (s + 1))) :=
  rfl

/-- **Lane RC32's `GenuineStageSTUM` at the text's objects** (tex 3455–3498, 4142–4194,
4385–4451): `K = C.K`, `S₀`, `S`, `M = actualM`, `Δ = actualConds`, the places, `X = actualX`,
`EU = actualEU`, with the instances of this file. Kind: definition. -/
abbrev ActualGenuineStageSTUM [DecidableEq (Places C.K A.S₀)] (h28 : MilneADT_I_2_8)
    (hI : IwasawaGenerators) (hInj : GenuineCochainsInjective) : Type :=
  GenuineStageSTUM C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A) (actualEU A)
    h28 hI hInj C D Fam x A.pidx

end Objects

/-! ### (h) The Frobenius discharge on the actual presentation -/

section Discharge

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} (A : ActualPresentation C D Fam x)

omit [(Ecurve ℓ).IsElliptic] in
/-- The prime of the `i`-th step is an unused graph prime (tex 4142–4146). Kind: PROVED. -/
theorem ActualPresentation.mem_unused {i : ℕ} (hi : i < A.ps.length) :
    A.ps.getD i 1 ∈ unusedAt Fam x := by
  rw [← A.hps, List.getD_eq_getElem A.ps 1 hi]
  exact List.mem_toFinset.mpr (List.getElem_mem hi)

omit [(Ecurve ℓ).IsElliptic] in
include A in
/-- **`FrobQFixes` at every graph prime** from `K = ℚ(√k)` and the splitting of the graph
primes (`frobQFixes_of_sqrt`; tex 2720–2722). Kind: PROVED. -/
theorem ActualPresentation.frobQFixes {q : ℕ} (hq : q ∈ Fam.Q) : FrobQFixes C q :=
  frobQFixes_of_sqrt C (A.hprime q hq).1 (A.hprime q hq).2 (A.split q hq).1 (A.split q hq).2
    A.r A.hr A.hgen

/-- **(h) The stage Frobenius inputs at both places of the `i`-th step, at the leaf's values**
(tex 4144–4145, 4171, 4176–4184): from the fields of the presentation. Kind: PROVED. -/
theorem actual_stageFrobInput (s : ℕ) {i : ℕ} (hi : i < A.ps.length) :
    (∃ eT : StageRing s ⊗[ℤ] Lev C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s ≃ₗ[StageRing s]
        (Fin 2 → StageRing s), StageFrobInput eT (stageRingChar s (A.alpha s))
          (newPlace (A.place (A.pidx i, false)) (A.hwp (A.pidx i, false)))
          (((leafFrobΛ C Fam x A.ps).map (stageMk s)).Fr i)
          (((leafFrobΛ C Fam x A.ps).map (stageMk s)).z i)) ∧
      ∃ eT : StageRing s ⊗[ℤ] Lev C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s ≃ₗ[StageRing s]
        (Fin 2 → StageRing s), StageFrobInput eT (stageRingChar s (A.alpha s))
          (newPlace (A.place (A.pidx i, true)) (A.hwp (A.pidx i, true)))
          (((leafFrobΛ C Fam x A.ps).map (stageMk s)).Fr i)
          (((leafFrobΛ C Fam x A.ps).map (stageMk s)).zi i) := by
  obtain ⟨hqQ, hun⟩ := mem_unusedAt.mp (A.mem_unused hi)
  exact exists_stageFrobInput_at C A.Cc Fam (fun q hq => (A.hprime q hq).1) x s A.sh A.hs A.hs0
    rfl (A.π s) (A.ψ s) (A.movingConj s) (A.hprime _ hqQ).2 hqQ hun (A.frobQFixes hqQ)
    (A.places i hi) (A.moving s (A.pidx i))

/-- **(h) Stage bases at the two places of every step, at the leaf's values** (tex 4176–4184,
4385–4451). Kind: PROVED. -/
theorem actual_stageBases (s : ℕ) :
    ∃ e₁ e₂ : ℕ → StageRing s ⊗[ℤ] Lev C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s ≃ₗ[StageRing s]
        (Fin 2 → StageRing s), ∀ i < A.ps.length,
      StageFrobInput (e₁ i) (stageRingChar s (A.alpha s))
          (newPlace (A.place (A.pidx i, false)) (A.hwp (A.pidx i, false)))
          (((leafFrobΛ C Fam x A.ps).map (stageMk s)).Fr i)
          (((leafFrobΛ C Fam x A.ps).map (stageMk s)).z i) ∧
        StageFrobInput (e₂ i) (stageRingChar s (A.alpha s))
          (newPlace (A.place (A.pidx i, true)) (A.hwp (A.pidx i, true)))
          (((leafFrobΛ C Fam x A.ps).map (stageMk s)).Fr i)
          (((leafFrobΛ C Fam x A.ps).map (stageMk s)).zi i) := by
  have hex : ∀ i, ∃ e₁ e₂ : StageRing s ⊗[ℤ] Lev C.K A.S₀ ((Ecurve ℓ).baseChange C.K) s ≃ₗ[
      StageRing s] (Fin 2 → StageRing s), i < A.ps.length →
      StageFrobInput e₁ (stageRingChar s (A.alpha s))
          (newPlace (A.place (A.pidx i, false)) (A.hwp (A.pidx i, false)))
          (((leafFrobΛ C Fam x A.ps).map (stageMk s)).Fr i)
          (((leafFrobΛ C Fam x A.ps).map (stageMk s)).z i) ∧
        StageFrobInput e₂ (stageRingChar s (A.alpha s))
          (newPlace (A.place (A.pidx i, true)) (A.hwp (A.pidx i, true)))
          (((leafFrobΛ C Fam x A.ps).map (stageMk s)).Fr i)
          (((leafFrobΛ C Fam x A.ps).map (stageMk s)).zi i) := by
    intro i
    by_cases hi : i < A.ps.length
    · obtain ⟨⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩ := actual_stageFrobInput A s hi
      exact ⟨e₁, e₂, fun _ => ⟨h₁, h₂⟩⟩
    · exact ⟨stageBasis (tateBasisAt C A.S₀) s, stageBasis (tateBasisAt C A.S₀) s,
        fun h' => absurd h' hi⟩
  choose e₁ e₂ he using hex
  exact ⟨e₁, e₂, fun i hi => he i hi⟩

/-- **(h) The Frobenius fields of the genuine stage chain on the actual presentation**
(tex 3470–3498, 4176–4184): `f j = urId`, the bases of `actual_stageBases`, with `Fr`, `z`, `zi`
those of `leafFrobΛ` at the stage (`stageChainFrobE2`). Kind: definition. -/
def actualFrob (s : ℕ) : StageChainFrob (StageRing s) (actualM A s) A.place (actualX A s)
    A.pidx A.ps.length (fun i => ((leafFrobΛ C Fam x A.ps).map (stageMk s)).Fr i)
    (fun i => ((leafFrobΛ C Fam x A.ps).map (stageMk s)).z i)
    (fun i => ((leafFrobΛ C Fam x A.ps).map (stageMk s)).zi i) :=
  stageChainFrobE2 A.hS A.place A.hwp ((Ecurve ℓ).baseChange C.K) s (A.alpha s) A.pidx
    A.ps.length _ _ _ (Classical.choose (actual_stageBases A s))
    (Classical.choose (Classical.choose_spec (actual_stageBases A s)))
    (fun i hi => (Classical.choose_spec (Classical.choose_spec (actual_stageBases A s)) i hi).1)
    (fun i hi => (Classical.choose_spec (Classical.choose_spec (actual_stageBases A s)) i hi).2)

/-- **(h) The genuine data of one chain at one stage on the actual presentation**
(tex 4142–4194, 4176–4184, 4385–4451): `GenuineStageSteps.ofFrob` of `actualFrob`, with the step
cardinalities `q i = ps[i]`, `hE` by `actualEU_i`, `hexp`, `hqodd`, `hqc` PROVED from the
presentation; the model of `C_∅` and the relaxed classes and functionals given.
Kind: definition. -/
def actualSteps (s m0 m1 m2 : ℕ)
    (st0 : CMState m0 m1 m2
      (genCx C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A) (actualEU A) s ∅) 0)
    (zR : ∀ i, (genCx C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A) (actualEU A) s
      (insert (A.pidx i) (chainT A.pidx i))).X 1)
    (hzR : ∀ i, (genCx C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A) (actualEU A)
      s (insert (A.pidx i) (chainT A.pidx i))).d 1 2 rfl (zR i) = 0)
    (lamR : ∀ i, (genCx C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A)
      (actualEU A) s (insert (A.pidx i) (chainT A.pidx i))).X 2 →ₗ[StageRing s] StageRing s)
    (hlamR : ∀ i, lamR i ∘ₗ (genCx C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A)
      (actualEU A) s (insert (A.pidx i) (chainT A.pidx i))).d 1 2 rfl = 0) :
    GenuineStageSteps C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A) (actualEU A)
      s m0 m1 m2 A.pidx A.ps.length :=
  GenuineStageSteps.ofFrob (actualFrob A s) A.hnew st0 (fun i => A.ps.getD i 1) zR hzR lamR
    hlamR (fun j => actualEU_i A s j)
    (exists_two_pow_smul_inflMod A.hS ((Ecurve ℓ).baseChange C.K) s (A.alpha s))
    (fun i hi => by
      obtain ⟨hqQ, -⟩ := mem_unusedAt.mp (A.mem_unused hi)
      exact (A.hprime _ hqQ).1.odd_of_ne_two (A.hprime _ hqQ).2)
    (fun i hi c => by
      cases c
      · exact (A.places i hi).card.symm
      · exact (A.places i hi).card'.symm)

/-- **(h) The leaf's Frobenius data on the actual presentation** (tex 4144–4145, 4176–4184,
4385–4451): `StageFrobAt` for the chain of `actualSteps` with the traces `a` of `leafFrobΛ` at
the stage; `Fr`, `z`, `zi`, `a` by definition, `q` by `map_natCast`. Kind: PROVED. -/
theorem actualSteps_stageFrobAt [DecidableEq (Places C.K A.S₀)] (h28 : MilneADT_I_2_8)
    (hI : IwasawaGenerators) (hInj : GenuineCochainsInjective) (s m0 m1 m2 : ℕ)
    (st0 : CMState m0 m1 m2
      (genCx C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A) (actualEU A) s ∅) 0)
    (zR : ∀ i, (genCx C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A) (actualEU A) s
      (insert (A.pidx i) (chainT A.pidx i))).X 1)
    (hzR : ∀ i, (genCx C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A) (actualEU A)
      s (insert (A.pidx i) (chainT A.pidx i))).d 1 2 rfl (zR i) = 0)
    (lamR : ∀ i, (genCx C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A)
      (actualEU A) s (insert (A.pidx i) (chainT A.pidx i))).X 2 →ₗ[StageRing s] StageRing s)
    (hlamR : ∀ i, lamR i ∘ₗ (genCx C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A)
      (actualEU A) s (insert (A.pidx i) (chainT A.pidx i))).d 1 2 rfl = 0) :
    StageFrobAt (leafFrobΛ C Fam x A.ps) s
      ((actualSteps A s m0 m1 m2 st0 zR hzR lamR hlamR).toChainM h28 hI hInj)
      (fun i => ((leafFrobΛ C Fam x A.ps).map (stageMk s)).a i) := by
  intro i _
  exact ⟨rfl, map_natCast (stageMk s) (A.ps.getD i 1), rfl, rfl, rfl⟩

end Discharge

end ZInQ.Manuscript.RC.Wiring

import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitRetained
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitGlobal

/-!
# Lane RC31, round 2, part 7: the inner-limit pairing certificate from the retained stage duality

Manuscript `diophantine_zq.tex`: the retained data "include the integral duality maps, their
homotopy inverses, and the homotopies expressing compatibility of duality with localization"
(tex 4385–4388); Lemma `ex:limits-inner-limit` (tex 4391–4451): "One fixed nonprincipal
ultrafilter gives a diagram over `Λ` at all coefficient precisions, preserving its matrix
identities and retained homotopy inverses. … Mere stagewise quasi-isomorphisms without those maps
would not justify a nonflat coefficient change"; Lemma `ex:limits-derivative-switch` (tex
4834–4907) and the height-one switch (tex 5027–5070): "The retained localization-duality diagrams
give `U = U^⊥`".

**The limit object is not a fibre of the round-one setting.** The derivative labels move with the
coefficient stage (`ℓ_i → −1`, `q_i → 1`), so there is no fixed decomposition group and no fixed
`S`; lane RC31's fixed-`𝔭` PRINT `NekovarFibreGlobalDuality` does not apply to the limit diagram and
is not used here. The duality enters at the finite stages `A_i = Λ/(2^i, t^i)`: `A_i` is an Artin
local ring with residue field `𝔽₂` and a complete intersection, hence Gorenstein with
`ω_{A_i} = A_i[0]` (Nekovář, *Selmer complexes*, 2.7(iii), p. 55), so Nekovář's global duality
5.4.3 (p. 127) and 6.3.4 (p. 143) apply literally at `A_i` (lane RC26's finite-coefficient PRINT
`NekovarProp543T`). Elliot's Lemma `ex:limits-inner-limit` transports these dualities, their
homotopy inverses and the compatibility homotopies to the bounded finite free models. The data so
obtained are the hypotheses `RetainedLimitPairingStages` and `RetainedGlobalDualityStages`
(ELLIOT); this file PROVES that after the ultralimit and the specialization to `k(𝔭)` they give the
inner-limit producer contract.

* `RetainedGlobalDualityStages`: the retained reverse map of the global duality map and its two
  homotopies, at the stages (identities modulo the stage ideals on one ultrafilter-large set).
* Naturality of the coordinate formulas (`forwardMatOf`, `dualDiffMatOf`) under the ultralimit and
  under ring homomorphisms.
* **`fibreInnerLimitPairingCertificate_of_retained`**: the certificate
  `FibreInnerLimitPairingCertificate U hU P C (D.resLimit hU P) ε σ J` for the realized diagram,
  with `J = conjMatrix C W hW P` the matrix of `ρ_T(τ)` and the retained local pairing the
  transported one.
* **`fibreInnerLimitDuality_of_retained`**: the switching duality `FibreInnerLimitDuality`.

Kinds: definitions (hypothesis structures, ELLIOT) and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open Filter Matrix NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimit
open ZInQ.Manuscript.RC.Limits (ulimMat ulimMat_mul ulimMat_add ulimMat_sub ulimMat_one
  ulimMat_zero ulimMat_eq_zero_of_mem stageIdeal stageIdeal_tendsToZero)
open ZInQ.Manuscript.RC.Uniform (Lambda switchPairing)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open scoped PowerSeries.WithPiTopology

/-! ### Naturality of the coordinate formulas -/

section Naturality

variable {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) {rank : ℤ → ℕ}

/-- Ring homomorphisms commute with subtraction of matrices. Kind: PROVED. -/
theorem matrix_map_sub {m n : Type} (M N : Matrix m n S) : (M - N).map f = M.map f - N.map f := by
  ext a b
  simp

/-- Ring homomorphisms commute with the transported restriction matrix. Kind: PROVED. -/
theorem RkAtOf_map (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (rank n)) S) (m n : ℤ) (h : m = n) :
    (RkAtOf Rk m n h).map f = RkAtOf (fun n => (Rk n).map f) m n h := by
  subst h
  rfl

/-- Ring homomorphisms commute with the cone differential matrix. Kind: PROVED. -/
theorem compactDiffMatOf_map (D : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) S)
    (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (rank n)) S) (m m' : ℤ) (h : m + 1 = m') :
    (compactDiffMatOf D Rk m m' h).map f =
      compactDiffMatOf (fun a b h => (D a b h).map f) (fun n => (Rk n).map f) m m' h := by
  unfold compactDiffMatOf
  rw [Matrix.fromBlocks_map, RkAtOf_map, Matrix.map_zero _ (map_zero f),
    Matrix.map_zero _ (map_zero f)]

/-- Ring homomorphisms commute with the dual differential matrix. Kind: PROVED. -/
theorem dualDiffMatOf_map (D : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) S)
    (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (rank n)) S) (a b : ℤ) (h : a + 1 = b) :
    (dualDiffMatOf D Rk a b h).map f =
      dualDiffMatOf (fun a b h => (D a b h).map f) (fun n => (Rk n).map f) a b h := by
  unfold dualDiffMatOf
  rw [← compactDiffMatOf_map f D Rk, ← Matrix.transpose_map]
  ext x y
  simp

/-- Ring homomorphisms commute with the forward matrix of the global duality map. Kind: PROVED. -/
theorem forwardMatOf_map (Mbg : ∀ a b : ℤ, a + b = 3 → Matrix (Fin (rank a)) (Fin (rank b)) S)
    (Mbl : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) S) (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (rank n)) S)
    (a : ℤ) :
    (forwardMatOf Mbg Mbl Rk a).map f =
      forwardMatOf (fun a b h => (Mbg a b h).map f) (fun a b => (Mbl a b).map f)
        (fun n => (Rk n).map f) a := by
  unfold forwardMatOf
  ext (x | x) y
  · rfl
  · show f (((sgn a : S) • ((Mbl a (3 - a - 1))ᵀ * Rk a)) x y) =
      ((sgn a : T) • (((Mbl a (3 - a - 1)).map f)ᵀ * (Rk a).map f)) x y
    simp [Matrix.mul_apply, map_sum, map_mul]

end Naturality

section UlimNaturality

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [T2Space R] (U : Ultrafilter ℕ) {rank : ℤ → ℕ}

/-- The ultralimit commutes with scalar multiples by a constant. Kind: PROVED. -/
theorem ulimMat_smul_const {m n : Type} (c : R) (M : ℕ → Matrix m n R) :
    ulimMat U (fun i => c • M i) = c • ulimMat U M := by
  ext a b
  change ZInQ.Manuscript.RC.Limits.ulim U (fun i => c * M i a b) =
    c * ZInQ.Manuscript.RC.Limits.ulim U (fun i => M i a b)
  rw [ZInQ.Manuscript.RC.Limits.ulim_mul, ZInQ.Manuscript.RC.Limits.ulim_const]

omit [CommRing R] [IsTopologicalRing R] [CompactSpace R] [T2Space R] in
/-- The ultralimit commutes with the transported restriction matrix. Kind: PROVED. -/
theorem ulimMat_RkAtOf (Rk : ∀ n : ℤ, ℕ → Matrix (lIdx n) (Fin (rank n)) R) (m n : ℤ)
    (h : m = n) :
    ulimMat U (fun i => RkAtOf (fun n => Rk n i) m n h) =
      RkAtOf (fun n => ulimMat U (Rk n)) m n h := by
  subst h
  rfl

omit [IsTopologicalRing R] in
/-- The ultralimit commutes with the cone differential matrix. Kind: PROVED. -/
theorem ulimMat_compactDiffMatOf
    (D : ℕ → ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) R)
    (Rk : ∀ n : ℤ, ℕ → Matrix (lIdx n) (Fin (rank n)) R) (m m' : ℤ) (h : m + 1 = m') :
    ulimMat U (fun i => compactDiffMatOf (D i) (fun n => Rk n i) m m' h) =
      compactDiffMatOf (fun a b h => ulimMat U (fun i => D i a b h))
        (fun n => ulimMat U (Rk n)) m m' h := by
  unfold compactDiffMatOf
  rw [← ulimMat_RkAtOf U Rk m (m' - 1) (by omega)]
  ext (x | x) (y | y)
  · rfl
  · exact ZInQ.Manuscript.RC.Limits.ulim_const U 0
  · rfl
  · exact ZInQ.Manuscript.RC.Limits.ulim_const U 0

/-- The ultralimit commutes with the dual differential matrix. Kind: PROVED. -/
theorem ulimMat_dualDiffMatOf
    (D : ℕ → ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) R)
    (Rk : ∀ n : ℤ, ℕ → Matrix (lIdx n) (Fin (rank n)) R) (a b : ℤ) (h : a + 1 = b) :
    ulimMat U (fun i => dualDiffMatOf (D i) (fun n => Rk n i) a b h) =
      dualDiffMatOf (fun a b h => ulimMat U (fun i => D i a b h))
        (fun n => ulimMat U (Rk n)) a b h := by
  unfold dualDiffMatOf
  rw [ulimMat_smul_const, ulimMat_transpose, ulimMat_compactDiffMatOf]

/-- The ultralimit commutes with the forward matrix of the global duality map. Kind: PROVED. -/
theorem ulimMat_forwardMatOf
    (Mbg : ∀ a b : ℤ, a + b = 3 → ℕ → Matrix (Fin (rank a)) (Fin (rank b)) R)
    (Mbl : ∀ a b : ℤ, ℕ → Matrix (lIdx a) (lIdx b) R)
    (Rk : ∀ n : ℤ, ℕ → Matrix (lIdx n) (Fin (rank n)) R) (a : ℤ) :
    ulimMat U (fun i => forwardMatOf (fun a b h => Mbg a b h i) (fun a b => Mbl a b i)
        (fun n => Rk n i) a) =
      forwardMatOf (fun a b h => ulimMat U (Mbg a b h)) (fun a b => ulimMat U (Mbl a b))
        (fun n => ulimMat U (Rk n)) a := by
  unfold forwardMatOf
  have h2 : ulimMat U (fun i => (sgn a : R) • ((Mbl a (3 - a - 1) i)ᵀ * Rk a i)) =
      (sgn a : R) • ((ulimMat U (Mbl a (3 - a - 1)))ᵀ * ulimMat U (Rk a)) := by
    rw [ulimMat_smul_const, ulimMat_mul, ulimMat_transpose]
  ext (x | x) y
  · rfl
  · exact congrFun (congrFun h2 x) y

end UlimNaturality

/-! ### The retained global duality at the stages -/

variable {U : Ultrafilter ℕ} {C : ComplexStages (R := Lambda) stageIdeal U}

/-- **The retained global duality at the coefficient stages** (ELLIOT, Lemma
`ex:limits-inner-limit`, tex 4391–4451, applied to Nekovář's global duality 5.4.3 at the Gorenstein
stages `A_i`, for the realized diagram): the reverse map `rev` of the global duality map
`G → Hom(Cone(G → L)[−1], A_i)[−3]` (in the dual coordinates `cIdxOf`), a chain map at the retained
precision (`chain`), with the source homotopy (`srcHom`, on `G`) and the target homotopy (`tgtHom`,
on the dual) and both homotopy-inverse identities (`src`, `tgt`), all modulo the stage ideals on one
ultrafilter-large set. The forward map and the dual differential are the stage formulas
(`forwardMatOf`, `dualDiffMatOf`) of the retained pairing data `D`. Kind: definition (hypothesis
structure). -/
structure RetainedGlobalDualityStages (D : RetainedLimitPairingStages U C) where
  /-- The retained reverse map. -/
  rev : ∀ a : ℤ, ℕ → Matrix (Fin (C.rank a)) (cIdxOf C.rank (3 - a)) Lambda
  /-- The retained source homotopy. -/
  srcHom : ∀ a b : ℤ, b + 1 = a → ℕ → Matrix (Fin (C.rank b)) (Fin (C.rank a)) Lambda
  /-- The retained target homotopy. -/
  tgtHom : ∀ a b : ℤ, b + 1 = a → ℕ → Matrix (cIdxOf C.rank (3 - b)) (cIdxOf C.rank (3 - a)) Lambda
  /-- The reverse map is a chain map at the retained precision. -/
  chain : ∀ a : ℤ, ∀ᶠ i in (U : Filter ℕ), ∀ x y,
    (rev (a + 1) i * dualDiffMatOf (C.d i) (fun n => D.res n i) a (a + 1) rfl -
      C.d i a (a + 1) rfl * rev a i) x y ∈ stageIdeal i
  /-- The first homotopy-inverse identity at the retained precision. -/
  src : ∀ a : ℤ, ∀ᶠ i in (U : Filter ℕ), ∀ x y,
    (rev a i * forwardMatOf (fun a b h => D.glob a b h i) (fun a b => D.loc a b i)
        (fun n => D.res n i) a -
      srcHom (a + 1) a rfl i * C.d i a (a + 1) rfl -
      C.d i (a - 1) a (by omega) * srcHom a (a - 1) (by omega) i - 1 :
        Matrix (Fin (C.rank a)) (Fin (C.rank a)) Lambda) x y ∈ stageIdeal i
  /-- The second homotopy-inverse identity at the retained precision. -/
  tgt : ∀ a : ℤ, ∀ᶠ i in (U : Filter ℕ), ∀ x y,
    (forwardMatOf (fun a b h => D.glob a b h i) (fun a b => D.loc a b i)
        (fun n => D.res n i) a * rev a i -
      tgtHom (a + 1) a rfl i * dualDiffMatOf (C.d i) (fun n => D.res n i) a (a + 1) rfl -
      dualDiffMatOf (C.d i) (fun n => D.res n i) (a - 1) a (by omega) *
        tgtHom a (a - 1) (by omega) i - 1 :
        Matrix (cIdxOf C.rank (3 - a)) (cIdxOf C.rank (3 - a)) Lambda) x y ∈ stageIdeal i

variable (hU : (U : Filter ℕ) ≤ Filter.cofinite) {D : RetainedLimitPairingStages U C}
  (E : RetainedGlobalDualityStages D) (P : Ideal Lambda) [P.IsPrime]

/-- The dual differential of the limit is the limit of the stage dual differentials. Kind:
PROVED. -/
theorem dualDiffMat_limit (a b : ℤ) (h : a + 1 = b) :
    dualDiffMat (algebraMap Lambda (ResAt P)) C (D.resK P) a b h =
      (ulimMat U (fun i => dualDiffMatOf (C.d i) (fun n => D.res n i) a b h)).map
        (algebraMap Lambda (ResAt P)) := by
  rw [ulimMat_dualDiffMatOf, dualDiffMatOf_map]

/-- The forward matrix of the limit is the limit of the stage forward matrices. Kind: PROVED. -/
theorem forwardMat_limit (a : ℤ) :
    forwardMat C (D.resK P) (D.globK P) (D.locK P) a =
      (ulimMat U (fun i => forwardMatOf (fun a b h => D.glob a b h i) (fun a b => D.loc a b i)
        (fun n => D.res n i) a)).map (algebraMap Lambda (ResAt P)) := by
  rw [ulimMat_forwardMatOf, forwardMatOf_map]

/-- The retained reverse map after the inner limit, at `k(𝔭)`. Kind: definition. -/
abbrev RetainedGlobalDualityStages.revK (a : ℤ) :
    Matrix (Fin (C.rank a)) (cIdx C (3 - a)) (ResAt P) :=
  (ulimMat U (E.rev a)).map (algebraMap Lambda (ResAt P))

/-- The retained source homotopy after the inner limit. Kind: definition. -/
abbrev RetainedGlobalDualityStages.srcK (a b : ℤ) (h : b + 1 = a) :
    Matrix (Fin (C.rank b)) (Fin (C.rank a)) (ResAt P) :=
  (ulimMat U (E.srcHom a b h)).map (algebraMap Lambda (ResAt P))

/-- The retained target homotopy after the inner limit. Kind: definition. -/
abbrev RetainedGlobalDualityStages.tgtK (a b : ℤ) (h : b + 1 = a) :
    Matrix (cIdx C (3 - b)) (cIdx C (3 - a)) (ResAt P) :=
  (ulimMat U (E.tgtHom a b h)).map (algebraMap Lambda (ResAt P))

include hU in
/-- The reverse map is an exact chain map after the inner limit. Kind: PROVED. -/
theorem RetainedGlobalDualityStages.chainK (a : ℤ) :
    E.revK P (a + 1) * dualDiffMat (algebraMap Lambda (ResAt P)) C (D.resK P) a (a + 1) rfl =
      specDiff (algebraMap Lambda (ResAt P)) C a (a + 1) rfl * E.revK P a := by
  have e := ulimMat_eq_zero_of_mem stageIdeal_tendsToZero hU (E.chain a)
  rw [ulimMat_sub, ulimMat_mul, ulimMat_mul] at e
  have e' := congrArg (fun M => M.map (algebraMap Lambda (ResAt P))) e
  simp only [matrix_map_sub, Matrix.map_mul, Matrix.map_zero _ (map_zero _)] at e'
  rw [dualDiffMat_limit]
  exact sub_eq_zero.mp e'

include hU in
/-- The first homotopy-inverse identity is exact after the inner limit. Kind: PROVED. -/
theorem RetainedGlobalDualityStages.srcK_id (a : ℤ) :
    E.revK P a * forwardMat C (D.resK P) (D.globK P) (D.locK P) a =
      E.srcK P (a + 1) a rfl * specDiff (algebraMap Lambda (ResAt P)) C a (a + 1) rfl +
        specDiff (algebraMap Lambda (ResAt P)) C (a - 1) a (by omega) *
          E.srcK P a (a - 1) (by omega) + 1 := by
  have e := ulimMat_eq_zero_of_mem stageIdeal_tendsToZero hU (E.src a)
  rw [ulimMat_sub, ulimMat_sub, ulimMat_sub, ulimMat_mul, ulimMat_mul, ulimMat_mul,
    ulimMat_one] at e
  have e' := congrArg (fun M => M.map (algebraMap Lambda (ResAt P))) e
  simp only [matrix_map_sub, Matrix.map_mul, Matrix.map_zero _ (map_zero _),
    Matrix.map_one _ (map_zero _) (map_one _)] at e'
  rw [forwardMat_limit]
  rw [sub_eq_zero] at e'
  rw [← e']
  abel

include hU in
/-- The second homotopy-inverse identity is exact after the inner limit. Kind: PROVED. -/
theorem RetainedGlobalDualityStages.tgtK_id (a : ℤ) :
    forwardMat C (D.resK P) (D.globK P) (D.locK P) a * E.revK P a =
      E.tgtK P (a + 1) a rfl *
          dualDiffMat (algebraMap Lambda (ResAt P)) C (D.resK P) a (a + 1) rfl +
        dualDiffMat (algebraMap Lambda (ResAt P)) C (D.resK P) (a - 1) a (by omega) *
          E.tgtK P a (a - 1) (by omega) + 1 := by
  have e := ulimMat_eq_zero_of_mem stageIdeal_tendsToZero hU (E.tgt a)
  rw [ulimMat_sub, ulimMat_sub, ulimMat_sub, ulimMat_mul, ulimMat_mul, ulimMat_mul,
    ulimMat_one] at e
  have e' := congrArg (fun M => M.map (algebraMap Lambda (ResAt P))) e
  simp only [matrix_map_sub, Matrix.map_mul, Matrix.map_zero _ (map_zero _),
    Matrix.map_one _ (map_zero _) (map_one _)] at e'
  rw [forwardMat_limit, dualDiffMat_limit, dualDiffMat_limit]
  rw [sub_eq_zero] at e'
  rw [← e']
  abel

include hU E in
/-- **The global duality of the realized limit diagram at `k(𝔭)`**, from the retained stage
duality (Lemma `ex:limits-inner-limit`: "Retained homotopy inverses remain homotopy inverses"):
`globalDualityMap` of the limit pairing data is a quasi-isomorphism. Kind: PROVED. -/
theorem RetainedGlobalDualityStages.globalDuality :
    QuasiIso (GHom.toCC (globalDualityMap
      (limitPair (D.resLimit hU P) (globalPairingOfMat stageIdeal_tendsToZero hU
          (algebraMap Lambda (ResAt P)) C (D.globK P)) (localPairingOfMat (D.locK P))
        (limitReciprocity_ofMat stageIdeal_tendsToZero hU (algebraMap Lambda (ResAt P)) C
          (D.resK P) (D.resK_comm hU P) (D.globK P) (D.locK P) (D.matReciprocity hU P)))
      (limitTrace (ResAt P))
      (limitPair_htr (D.resLimit hU P) (globalPairingOfMat stageIdeal_tendsToZero hU
          (algebraMap Lambda (ResAt P)) C (D.globK P)) (localPairingOfMat (D.locK P))
        (limitReciprocity_ofMat stageIdeal_tendsToZero hU (algebraMap Lambda (ResAt P)) C
          (D.resK P) (D.resK_comm hU P) (D.globK P) (D.locK P) (D.matReciprocity hU P))))) :=
  globalDuality_quasiIso_ofMat stageIdeal_tendsToZero hU (algebraMap Lambda (ResAt P)) C
    (D.resK P) (D.resK_comm hU P) (D.globK P) (D.locK P) (D.matReciprocity hU P)
    (E.revK P) (E.srcK P) (E.tgtK P) (E.chainK hU P) (E.srcK_id hU P) (E.tgtK_id hU P)

/-! ### The certificate -/

include hU E in
/-- **The inner-limit producer contract from the retained stage duality, general form**: for any
`J` with `J² = 1`, if the limit local pairing in degree one is the transported switch pairing
(`hb11`, the residue identity, tex 5037) and its `D² × D⁰` part is perfect (`h20`, "`D⁰` and `D²`
are dual", tex 4866), the certificate holds. Kind: PROVED. -/
theorem fibreInnerLimitPairingCertificate_of_retained' (ε σ : ResAt P)
    (J : Matrix (Fin 2) (Fin 2) (ResAt P)) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ : J * J = 1)
    (hb11 : ∀ x y, (localPairingOfMat (D.locK P)).b11 x y = -(switchPairing ε σ J y x))
    (h20 : Function.Bijective (localPairingOfMat (D.locK P)).b20) :
    FibreInnerLimitPairingCertificate U hU P C (D.resLimit hU P) ε σ J :=
  limitPairingCertificate_of_dualities (D.resLimit hU P)
    (globalPairingOfMat stageIdeal_tendsToZero hU (algebraMap Lambda (ResAt P)) C (D.globK P))
    (localPairingOfMat (D.locK P))
    (limitReciprocity_ofMat stageIdeal_tendsToZero hU (algebraMap Lambda (ResAt P)) C
      (D.resK P) (D.resK_comm hU P) (D.globK P) (D.locK P) (D.matReciprocity hU P))
    ε σ J hb11 (E.globalDuality hU P)
    (limitLocalDuality_quasiIso _ _ _ _
      (switch_b11_bijective (localPairingOfMat (D.locK P)) ε σ J hε hσ hJ hb11) h20)


variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

include hU E in
/-- **The inner-limit producer contract for the realized diagram** (tex 4385–4388, 4391–4451,
4834–4907, 5027–5070): for the retained global model `C`, its retained localization, global and
local pairings (`D`) and retained global duality (`E`) at the coefficient stages, and a height-one
prime `𝔭`, if the retained local pairing at the derivative label is the transported one with
`J = ρ_T(τ)` (`conjMatrix Cn W hW P`, lane RC31's `conjTate` in lane RC28's basis; `hloc`, tex 5037:
`β(x, y) = ε e₂(x, J y)`) and the retained scalars are units (`ε₂, ε, σ ≠ 0`), then
`FibreInnerLimitPairingCertificate U hU P C (D.resLimit hU P) ε σ J` holds. Kind: PROVED. -/
theorem fibreInnerLimitPairingCertificate_of_retained (ε₀ ε₂ ε σ : ResAt P) (hε₂ : ε₂ ≠ 0)
    (hε : ε ≠ 0) (hσ : σ ≠ 0)
    (hloc : localPairingOfMat (D.locK P) =
      transportedPairing ε₀ ε₂ ε σ (conjMatrix Cn W hW P)) :
    FibreInnerLimitPairingCertificate U hU P C (D.resLimit hU P) ε σ (conjMatrix Cn W hW P) := by
  have hJ := conjMatrix_mul_self Cn W hW P
  have hb11 : ∀ x y, (localPairingOfMat (D.locK P)).b11 x y =
      -(switchPairing ε σ (conjMatrix Cn W hW P) y x) := by
    intro x y
    rw [hloc]
    exact transportedPairing_b11 ε₀ ε₂ ε σ _ x y
  have h20 : Function.Bijective (localPairingOfMat (D.locK P)).b20 := by
    rw [hloc]
    exact transportedPairing_b20_bijective hε₂ ε₀ ε σ hJ
  exact fibreInnerLimitPairingCertificate_of_retained' hU E P ε σ (conjMatrix Cn W hW P) hε hσ hJ
    hb11 h20

include hU E in
/-- **The switching duality of the realized limit diagram** (tex 5065–5070: "The retained
localization-duality diagrams give `U = U^⊥`"): `FibreInnerLimitDuality` for the retained diagram,
with `J = ρ_T(τ)` and `J² = 1` (`conjMatrix_mul_self`). Kind: PROVED. -/
theorem fibreInnerLimitDuality_of_retained (ε₀ ε₂ ε σ : ResAt P) (hε₂ : ε₂ ≠ 0)
    (hε : ε ≠ 0) (hσ : σ ≠ 0)
    (hloc : localPairingOfMat (D.locK P) =
      transportedPairing ε₀ ε₂ ε σ (conjMatrix Cn W hW P)) :
    FibreInnerLimitDuality U hU P C (D.resLimit hU P) ε σ (conjMatrix Cn W hW P) hε hσ
      (conjMatrix_mul_self Cn W hW P) :=
  fibreInnerLimitDuality_of_certificate U hU P C (D.resLimit hU P) ε σ (conjMatrix Cn W hW P) hε
    hσ (conjMatrix_mul_self Cn W hW P)
    (fibreInnerLimitPairingCertificate_of_retained hU E P Cn W hW ε₀ ε₂ ε σ hε₂ hε hσ hloc)

end ZInQ.Manuscript.RC.FibreDuality

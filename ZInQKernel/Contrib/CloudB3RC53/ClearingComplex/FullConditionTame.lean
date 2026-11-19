import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionIdentification

/-!
# The tame singular quotient `[M --(Φ−q)--> M]` in degrees one and two

Manuscript `diophantine_zq.tex`, tex 3479–3481 ("the singular quotient `[Φ−q]` in degrees one and
two"), tex 5320–5322 (`Q_{r,w} = [ℤ₂² --(Φ_r−r)--> ℤ₂²]` in degrees one and two), tex 5455–5463.

For the tame model `L = [M --(Φ−1, 0)--> M² --(0, Φ−q)--> M]` and its unramified condition
`U = [M --(Φ−1)--> M]` (`tL`, `tU`, `tιH` of `NewLocalConsistency.lean`):

* `tQ M Φ q`: the singular quotient `[M --(Φ−q)--> M]` in degrees one and two; `tπH : tL → tQ`
  (the second coordinate in degree one, the identity in degree two);
* `tameSES_shortExact`: `0 → tU → tL → tQ → 0` is short exact (PROVED);
* `tameQuotMap`, `tameQuotMap_quasiIso`: for a `TameModelQIso` (quasi-isomorphisms
  `tL → L`, `tU → U` compatible with the inclusions) and a termwise injective condition
  `ι : U → L`, the induced map `tQ → L/ι(U)` exists and is a quasi-isomorphism (PROVED; five
  lemma);
* `Identification3.tame_singular_quasiIso`: for the full-condition identification, at every new
  place `q` the genuine singular quotient `C^•_cont(G_{K_q}, M₀) / C^•_cont(G_q/I_q, M₀)` (the
  `q`-component of `galoisSingQ`) is quasi-isomorphic to `[M₀ --(Φ_q − q)--> M₀]` in degrees one
  and two (PROVED from the field `tame`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex (quotSES quotSES_shortExact quotCx NewPlaces urRes
  urRes_surjective GKS inflMap Gloc locMap locMap_compat)

section Tame

variable {S : Type} [CommRing S] (M : Type) [AddCommGroup M] [Module S M] (Φ : M →ₗ[S] M) (q : ℕ)

/-- The modules of the singular quotient `M → M` (degrees `1, 2`). -/
def tQX (S : Type) [CommRing S] (M : Type) [AddCommGroup M] [Module S M] : ℤ → ModuleCat S
  | 1 => ModuleCat.of S M
  | 2 => ModuleCat.of S M
  | _ => ModuleCat.of S PUnit

/-- Its differential `Φ − q`. -/
def tQd : (i : ℤ) → tQX S M i →ₗ[S] tQX S M (i + 1)
  | 1 => Φ - (q : S) • LinearMap.id
  | _ => 0

theorem tQd_tQd (i : ℤ) (x : tQX S M i) : tQd M Φ q (i + 1) (tQd M Φ q i x) = 0 := by
  match i with
  | 0 => exact map_zero _
  | 1 => rfl
  | Int.ofNat (n + 2) => rfl
  | Int.negSucc n =>
    change tQd M Φ q (Int.negSucc n + 1) 0 = 0
    exact map_zero _

/-- **The singular quotient `[M --(Φ−q)--> M]` in degrees one and two.** -/
def tQ : GCx S where
  X := tQX S M
  d i j h := by subst h; exact tQd M Φ q i
  d_d i j k hij hjk x := by subst hij hjk; exact tQd_tQd M Φ q i x

/-- The components of the projection `tL → tQ`. -/
def tπ : (i : ℤ) → tLX S M i →ₗ[S] tQX S M i
  | 1 => LinearMap.snd S M M
  | 2 => LinearMap.id
  | _ => 0

theorem tπ_comm (i : ℤ) (x : tLX S M i) :
    tπ M (i + 1) (tLd M Φ q i x) = tQd M Φ q i (tπ M i x) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | Int.ofNat (n + 3) => rfl
  | Int.negSucc n =>
    change tπ M (Int.negSucc n + 1) 0 = tQd M Φ q (Int.negSucc n) 0
    rw [map_zero, map_zero]

/-- The projection `tL → tQ`. -/
def tπH : GHom (tL M Φ q) (tQ M Φ q) where
  f i j h := by subst h; exact tπ M i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    exact tπ_comm M Φ q i x

open SelmerDuality in
/-- The sequence `tU → tL → tQ`. -/
def tameSES : ShortComplex (CochainComplex (ModuleCat.{0} S) ℤ) :=
  ShortComplex.mk (GHom.toCC (tιH M Φ q)) (GHom.toCC (tπH M Φ q)) (by
    ext i x
    change tπ M i (tι M i x) = 0
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | Int.ofNat (n + 3) => rfl
    | Int.negSucc n => rfl)

open SelmerDuality in
/-- **`0 → tU → tL → tQ → 0` is short exact.** PROVED. -/
theorem tameSES_shortExact : (tameSES M Φ q).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro c hc
    change tπ M i c = 0 at hc
    change ∃ a, tι M i a = c
    match i with
    | 0 => exact ⟨c, rfl⟩
    | 1 => exact ⟨c.1, Prod.ext rfl hc.symm⟩
    | 2 => exact ⟨0, hc.symm⟩
    | Int.ofNat (n + 3) => exact ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
    | Int.negSucc n => exact ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
  · rw [ModuleCat.mono_iff_injective]
    intro a b h
    change tι M i a = tι M i b at h
    match i with
    | 0 => exact h
    | 1 => exact congrArg Prod.fst h
    | 2 => exact Subsingleton.elim (α := PUnit) _ _
    | Int.ofNat (n + 3) => exact Subsingleton.elim (α := PUnit) _ _
    | Int.negSucc n => exact Subsingleton.elim (α := PUnit) _ _
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    change ∃ c, tπ M i c = y
    match i with
    | 1 => exact ⟨(0, y), rfl⟩
    | 2 => exact ⟨y, rfl⟩
    | 0 => exact ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
    | Int.ofNat (n + 3) => exact ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
    | Int.negSucc n => exact ⟨0, Subsingleton.elim (α := PUnit) _ _⟩

variable {M Φ q} {L U : GCx S} {ι : GHom U L} (T : TameModelQIso M Φ q L U ι)
  (hι : ∀ n, Function.Injective (ι.f n n rfl))

theorem tame_square_g : (tameSES M Φ q).f ≫ T.fL ≫ (quotSES ι).g = 0 := by
  have h1 : (tameSES M Φ q).f ≫ T.fL = T.fU ≫ (quotSES ι).f := T.comm
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [h1]
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (T.fU ≫ ·) (quotSES ι).zero).trans Limits.comp_zero

/-- **The induced map from the tame singular quotient** `[M --(Φ−q)--> M]` to `L / ι(U)`. -/
def tameQuotMap : (tameSES M Φ q).X₃ ⟶ (quotSES ι).X₃ :=
  have := (tameSES_shortExact M Φ q).epi_g
  (tameSES_shortExact M Φ q).exact.desc (T.fL ≫ (quotSES ι).g) (tame_square_g T)

theorem tameQuotMap_fac : (tameSES M Φ q).g ≫ tameQuotMap T = T.fL ≫ (quotSES ι).g := by
  have := (tameSES_shortExact M Φ q).epi_g
  exact (tameSES_shortExact M Φ q).exact.g_desc _ _

/-- The morphism of sequences `(fU, fL, tameQuotMap)`. -/
def tameSESHom : tameSES M Φ q ⟶ quotSES ι where
  τ₁ := T.fU
  τ₂ := T.fL
  τ₃ := tameQuotMap T
  comm₁₂ := T.comm.symm
  comm₂₃ := (tameQuotMap_fac T).symm

include hι in
/-- **The tame singular quotient computes the genuine singular quotient** (PROVED; five lemma). -/
theorem tameQuotMap_quasiIso : QuasiIso (tameQuotMap T) := by
  have h₁ : QuasiIso (tameSESHom T).τ₁ := T.qisU
  have h₂ : QuasiIso (tameSESHom T).τ₂ := T.qisL
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ (tameSESHom T)
    (tameSES_shortExact M Φ q) (quotSES_shortExact ι hι) h₁ h₂

end Tame

namespace Identification3

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {S S' : Set (HeightOneSpectrum (𝓞 K))}
  {hS : S ⊆ S'} [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')] {b : ℕ}
  {dK hK cE tK : ℕ} (M : Identification3 K S S' hS b dK hK cE tK)

/-- **At every new place the genuine singular quotient is the tame `[Φ_q − q]` in degrees one and
two** (PROVED from the field `tame`; `urRes` is surjective). -/
theorem tame_singular_quasiIso (q : NewPlaces K S S') : QuasiIso (tameQuotMap (M.tame q)) :=
  tameQuotMap_quasiIso (M.tame q)
    (natHom_urCond_injective (k := M.R₀) (GS := GKS K S) (GS' := GKS K S')
      (infl := inflMap K hS) (Gq := fun q : NewPlaces K S S' => Gloc K q.1)
      (locq := fun q => locMap K S' q.1)
      (Gur := fun q : NewPlaces K S S' => ZInQ.Contrib.CloudB3RC53.RankCounts.GUr K q.1)
      (π := fun q => urRes K q.1) (ψ := M.ψur) (M := M.M₀)
      (fun q g => (locMap_compat K hS q.1 g).trans (M.hψur q g))
      (fun q => urRes_surjective K q.1) q)

end Identification3

end ZInQ.Contrib.CloudB3RC53.ClearingComplex

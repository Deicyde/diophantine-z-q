import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Prints
import ZInQKernel.Contrib.CloudB3RC53.ResidualTransfer.TransferFinal

/-!
# Genuine instantiations, part 2: RC6's `transfer` from the genuine support change

Manuscript `diophantine_zq.tex`, tex L4598–4647 (the transfer of ranks from the smaller support),
with the support change of [Nekovář, Proposition 7.8.8(ii)] (tex L3480–3496).

`ResidualTransfer.transfer_final` takes `H : SupportChangeUnramified T`, whose term
isomorphisms with the three-term tame model can never hold for genuine continuous cochains (their
terms are infinite), and asks the Selmer complexes themselves to be bounded, finite and free.
`transfer_final_genuine` replaces this by the genuine data:

* `T := galoisSupportData K hS R M ψ hψ Δ` (the other team's genuine support change: inflation of
  continuous cochains, the old conditions at `S`, the unramified conditions `C^•_cont(G_q/I_q, M)`
  at `S' − S`) with the PRINT `NekovarProp788ii` (as a hypothesis named after the print), which
  makes the support comparison a quasi-isomorphism (`supportChange_of_print`);
* the original-support complex `selCx Dfull` obtained by replacing the unramified condition by the
  full one, with an acyclic singular quotient (so the change of condition is a quasi-isomorphism,
  `quasiIso_f_of_shortExact_acyclic`);
* bounded finite free **models**: `P₀ ⟶ selCx T.D` and `L ⟶ selCx Dfull`, quasi-isomorphisms (the
  genuine complexes are not themselves finite free); `rankTot` is the total rank of `P₀` and
  `genericRank` that of the minimal model `L`.

The zigzag `L → selCx Dfull ← selCx T.Dp ≅ selCx (restrictData Dfull f) ← selCx T.D ← P₀` of
quasi-isomorphisms is turned into a homotopy equivalence `L ≃ P₀` because `L` is K-projective
(Mathlib's `CochainComplex.IsKProjective.Qh_map_bijective`: maps out of `L` lift along
quasi-isomorphisms; `exists_quasiIso_of_zigzag`) and a quasi-isomorphism of bounded free complexes
is a homotopy equivalence (`homotopyEquiv_of_quasiIso_free`).

No `SupportChangeUnramified` is used.

**Classification.** PROVED from the PRINT hypothesis `NekovarProp788ii` and the inputs in the type.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open NumberField IsDedekindDomain CategoryTheory DerivedCategory
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.ResidualTransfer ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts

/-- **Lifting along a quasi-isomorphism out of a K-projective complex**: if `l : L → X` and
`p : P → X` are quasi-isomorphisms and `L` is K-projective, there is a quasi-isomorphism
`g : L → P` (with `g ≫ p` homotopic to `l`). PROVED (Mathlib's derived category). -/
theorem exists_quasiIso_of_zigzag {S : Type} [CommRing S]
    {L P X : CochainComplex (ModuleCat.{0} S) ℤ} [L.IsKProjective] (l : L ⟶ X) [QuasiIso l]
    (p : P ⟶ X) [QuasiIso p] : ∃ g : L ⟶ P, QuasiIso g := by
  let _ := HasDerivedCategory.standard (ModuleCat.{0} S)
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective L
    ((HomotopyCategory.quotient _ _).obj P)).surjective
    ((quotientCompQhIso _).hom.app L ≫ Q.map l ≫ inv (Q.map p) ≫ (quotientCompQhIso _).inv.app P)
  obtain ⟨g', rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨g', ?_⟩
  rw [← isIso_Q_map_iff_quasiIso]
  have h : Q.map g' = (quotientCompQhIso _).inv.app L ≫
      Qh.map ((HomotopyCategory.quotient _ _).map g') ≫ (quotientCompQhIso _).hom.app P := by
    simp
  rw [h, hg]
  infer_instance

/-- **Bounded free models quasi-isomorphic to the same complex are homotopy equivalent.** PROVED. -/
theorem homotopyEquiv_of_zigzag {S : Type} [CommRing S]
    (L P X : CochainComplex (ModuleCat.{0} S) ℤ) (a b : ℤ)
    [L.IsStrictlyGE a] [L.IsStrictlyLE b] [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ n, Module.Free S (L.X n)] [∀ n, Module.Free S (P.X n)]
    (l : L ⟶ X) [QuasiIso l] (p : P ⟶ X) [QuasiIso p] : Nonempty (HomotopyEquiv L P) := by
  have : L.IsKProjective := CochainComplex.isKProjective_of_projective L b
  obtain ⟨g, hg⟩ := exists_quasiIso_of_zigzag l p
  obtain ⟨e, -⟩ := homotopyEquiv_of_quasiIso_free a b g
  exact ⟨e⟩

variable (K : Type) [Field K] [NumberField K]

/-- **RC6's field `transfer` from the genuine support change** (tex L4598–4647; direction as in
tex L4612–4631), with `T := galoisSupportData …` and the PRINT `NekovarProp788ii`, and **no**
`SupportChangeUnramified`. The smaller-support complex `C_{S₀} = selCx T.D` and the
original-support complex `selCx Dfull` (full condition at the active primes, singular quotient
acyclic after inverting `t`) enter through bounded finite free models `P₀`, `L` (quasi-isomorphisms
`pP`, `pL`); then `genericRank ≤ rankTot` for `genericRank` the total rank of the minimal model `L`
and `rankTot` that of `P₀`. PROVED. -/
theorem transfer_final_genuine (h788 : NekovarProp788ii K) {S S' : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S ⊆ S') (pr : ℕ) (R : Type) [CommRing R] [IsLocalRing R]
    (hset : NekovarFiniteSetting K S pr R) (hS' : S'.Finite)
    (M : Type) [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M]
    [SMulCommClass (GKS K S) R M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul (GKS K S) M] [Finite M]
    (ψ : ∀ q : NewPlaces K S S', GUr K q.1 →ₜ* GKS K S)
    (hψ : ∀ (q : NewPlaces K S S') g, locMap K S q.1 g = ψ q (urRes K q.1 g))
    (Δ : GaloisLocalConditions K S R M)
    (Dfull : SelData R) (W : GCx R) (f : GHom (galoisSupportData K hS R M ψ hψ Δ).Dp.U Dfull.U)
    (g : GHom Dfull.U W) (hDp : (galoisSupportData K hS R M ψ hψ Δ).Dp = restrictData Dfull f)
    (hfg : ∀ i (u : (galoisSupportData K hS R M ψ hψ Δ).Dp.U.X i),
      g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hW : W.toCC.Acyclic) (a b : ℤ)
    (P₀ : CochainComplex (ModuleCat.{0} R) ℤ) [P₀.IsStrictlyGE a] [P₀.IsStrictlyLE b]
    [∀ i, Module.Free R (P₀.X i)] [∀ i, Module.Finite R (P₀.X i)]
    (pP : P₀ ⟶ (selCx (galoisSupportData K hS R M ψ hψ Δ).D).toCC) [QuasiIso pP]
    (L : CochainComplex (ModuleCat.{0} R) ℤ) [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    [∀ i, Module.Free R (L.X i)] [∀ i, Module.Finite R (L.X i)]
    (hLmin : ∀ i j x, (L.d i j).hom x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (L.X j)))
    (pL : L ⟶ (selCx Dfull).toCC) [QuasiIso pL] (s : Finset ℤ) (genericRank rankTot : ℕ)
    (hgen : genericRank = ∑ n ∈ s, Module.finrank R (L.X n))
    (htot : rankTot = ∑ n ∈ s, Module.finrank R (P₀.X n)) :
    genericRank ≤ rankTot := by
  -- the support comparison `C_{S₀} → C(U')` (PRINT)
  have h1 : QuasiIso (GHom.toCC (supportMap (galoisSupportData K hS R M ψ hψ Δ))) :=
    supportChange_of_print K h788 hS pr hset hS' ψ hψ Δ
  -- the change of condition `C(U') → C(U_full)` (acyclic singular quotient)
  have hSE := relaxedQuotientNode_proof R Dfull (galoisSupportData K hS R M ψ hψ Δ).Dp.U W f g hfg hinj hsurj hex
  have h2 : QuasiIso (GHom.toCC (changeMap Dfull f)) :=
    quasiIso_f_of_shortExact_acyclic (E := changeSES Dfull f g hfg) hSE hW
  let e3 : (selCx (galoisSupportData K hS R M ψ hψ Δ).Dp).toCC ≅ (selCx (restrictData Dfull f)).toCC :=
    eqToIso (congrArg (fun D => (selCx D).toCC) hDp)
  let q : P₀ ⟶ (selCx Dfull).toCC :=
    pP ≫ GHom.toCC (supportMap (galoisSupportData K hS R M ψ hψ Δ)) ≫ e3.hom ≫ GHom.toCC (changeMap Dfull f)
  have hq : QuasiIso q := inferInstance
  obtain ⟨e⟩ := homotopyEquiv_of_zigzag L P₀ _ a b pL q
  exact transferOfModels_final L P₀ a b hLmin e s genericRank rankTot hgen htot

end ZInQ.Contrib.CloudB3RC53.GenuineInst

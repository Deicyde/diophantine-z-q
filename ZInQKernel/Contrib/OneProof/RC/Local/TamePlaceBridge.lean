import ZInQKernel.Contrib.OneProof.RC.Local.TameFreeModelCochains
import ZInQKernel.Contrib.CloudB3RC53.UnramifiedComplex.Places

/-!
# Lane RC31, round 6: the tame comparison at a finite place of a number field

Manuscript `diophantine_zq.tex`, tex 3470–3480 (Elliot's tame local free model (4.4)), with the
tame coordinates of tex 3298–3306.

`TameCochainQuasiIso` (`TameFreeModelCochains.lean`) is stated for an abstract nonarchimedean
local field. This file supplies its place-independent hypotheses at a finite place `w` of a
number field `K`, for the completion `K_w = w.adicCompletion K` and `G_{K_w} = Gloc K w`.

* PROVED (restriction to `K_w^ur`). `resUr K w` is `localUnramifiedProjection K_w`
  (`resUr_eq_localUnramifiedProjection`, by definition), an arithmetic Frobenius lift restricts
  to `frobElt (eUr K w)` (`resUr_of_isArithFrobeniusLift`, and the converse in
  `isArithFrobeniusLift_iff_resUr`), and inertia is the kernel of `resUr K w`
  (`resUr_of_mem_inertia`, `mem_inertia_iff_resUr`).
* PROVED (instances and residue data). The instances required by `TameCochainQuasiIso` exist
  for `K_w` (`perfectField_adicCompletion`, `isNonarchimedeanLocalField_adicCompletion'`); the
  residue field of `K_w` has `Nat.card (𝓞 K ⧸ w)` elements
  (`natCard_residueField_adicCompletion`); for `w ∤ 2` its characteristic is not `2`
  (`ringChar_residueField_ne_two`) and `q` is odd (`odd_natCard_residueField`).
* Definition and ELLIOT-uncited classical + GLUE (Iwasawa generators). `IsIwasawaTriple K w φ σ P`
  collects the place-dependent hypotheses of `TameCochainQuasiIso`; `IwasawaGeneratorsAt K w`
  (classical, not cited in the manuscript: Iwasawa 1955, p. 448 and §3, the tame quotient and the
  splitting over the wild inertia; GLUE: the reading as a triple) asserts that such a triple
  exists in `G_{K_w}` with the EXACT relation `φ σ φ⁻¹ = σ^q`.
* PROVED (application). `tameCochainQuasiIso_at`: from `TameCochainQuasiIso`, `w ∤ 2` and an
  Iwasawa triple, the comparison map at `w` is a quasi-isomorphism for every coefficient module
  satisfying the module-dependent hypotheses; `tameCochainQuasiIso_at_inflation` specializes
  to inflated coefficients (`Φ = (φ • ·)`, `g = id`), where those hypotheses are automatic up
  to the `2`-power exponent.
* PROVED (inflated coefficients). On the inflation of a representation of `Gal(K_w^ur/K_w)`,
  inertia, and hence any subgroup of inertia such as the wild inertia, acts trivially
  (`smul_eq_self_of_mem_inertia_of_inflation`, `smul_eq_self_of_le_inertia_of_inflation`).

No wild inertia subgroup and no splitting of the tame quotient is available in the imported
libraries; the existing tame constructions give the relation only modulo a finite tame level
kernel. Hence `IwasawaGeneratorsAt` stays an input (ELLIOT-uncited classical + GLUE: Iwasawa
1955, p. 448 and §3, read as an Iwasawa triple; the manuscript does not cite it).

Kinds: definitions, PROVED, and one ELLIOT-uncited classical + GLUE (`IwasawaGeneratorsAt`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory TauCeti ValuativeRel NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex (eUr resUr frobElt frobElt_eUr)
open ZInQ.Contrib.CloudB3RC53.RankCounts (GUr)
open ZInQ.Contrib.RC53Assist.TameBijective (UnramifiedGaloisGroup localUnramifiedProjection
  localUnramifiedProjection_frob)

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

/-! ### Instances and residue data at `w` -/

/-- The completion `K_w` is a perfect field (it has characteristic zero), as required by
`TameCochainQuasiIso` (tex 3470–3480). Kind: PROVED. -/
theorem perfectField_adicCompletion : PerfectField (w.adicCompletion K) := inferInstance

/-- The completion `K_w`, with its valuative relation and topology, is a nonarchimedean local
field, as required by `TameCochainQuasiIso` (tex 3470–3480). Kind: PROVED. -/
theorem isNonarchimedeanLocalField_adicCompletion' :
    IsNonarchimedeanLocalField (w.adicCompletion K) := inferInstance

/-- The residue field of `K_w` has as many elements as `𝓞 K ⧸ w`; this identifies the `q` of
`TameCochainQuasiIso` with the residue cardinality of `w` (tex 3470–3480). Kind: PROVED. -/
theorem natCard_residueField_adicCompletion :
    Nat.card 𝓀[w.adicCompletion K] = Nat.card (𝓞 K ⧸ w.asIdeal) :=
  (Nat.card_congr (HeightOneSpectrum.residueFieldEquivAdicCompletion (K := K) w).toEquiv).symm

variable {K w}

/-- At a place `w ∤ 2` the residue characteristic of `K_w` is not `2` (tex 3470–3480).
Kind: PROVED. -/
theorem ringChar_residueField_ne_two (h2 : (2 : 𝓞 K) ∉ w.asIdeal) :
    ringChar 𝓀[w.adicCompletion K] ≠ 2 := by
  intro h
  have hd : ringChar 𝓀[w.adicCompletion K] ∣ 2 := h ▸ dvd_rfl
  rw [HeightOneSpectrum.ringChar_residueField_adicCompletion_dvd_iff] at hd
  exact h2 (by exact_mod_cast hd)

/-- At a place `w ∤ 2` the residue cardinality `q` of `K_w` is odd (tex 3470–3480).
Kind: PROVED. -/
theorem odd_natCard_residueField (h2 : (2 : 𝓞 K) ∉ w.asIdeal) :
    Odd (Nat.card 𝓀[w.adicCompletion K]) := by
  let _ := Fintype.ofFinite 𝓀[w.adicCompletion K]
  obtain ⟨n, hp, hn⟩ := FiniteField.card 𝓀[w.adicCompletion K] (ringChar 𝓀[w.adicCompletion K])
  rw [Nat.card_eq_fintype_card, hn]
  exact (hp.odd_of_ne_two (ringChar_residueField_ne_two h2)).pow

/-! ### Restriction to the maximal unramified extension -/

variable (K w) in
/-- The restriction `resUr K w : G_{K_w} → Gal(K_w^ur/K_w)` is the unramified projection
`localUnramifiedProjection K_w` of the tame coordinates (tex 3298–3306); the target types agree
by definition. Kind: PROVED. -/
theorem resUr_eq_localUnramifiedProjection (g : Gloc K w) :
    resUr K w g = localUnramifiedProjection (w.adicCompletion K) g := rfl

/-- An arithmetic Frobenius lift at `w` restricts to the Frobenius `frobElt (eUr K w)` of
`Gal(K_w^ur/K_w)`, which is the arithmetic Frobenius of the unramified complex
(tex 3470–3480, 3298–3306). Kind: PROVED. -/
theorem resUr_of_isArithFrobeniusLift {φ : Field.absoluteGaloisGroup (w.adicCompletion K)}
    (hφ : IsArithFrobeniusLift (w.adicCompletion K) φ) : resUr K w φ = frobElt (eUr K w) :=
  localUnramifiedProjection_frob (w.adicCompletion K) hφ

/-- The arithmetic Frobenius lifts at `w` are exactly the elements restricting to
`frobElt (eUr K w)` (tex 3470–3480). Kind: PROVED. -/
theorem isArithFrobeniusLift_iff_resUr {φ : Field.absoluteGaloisGroup (w.adicCompletion K)} :
    IsArithFrobeniusLift (w.adicCompletion K) φ ↔ resUr K w φ = frobElt (eUr K w) :=
  ⟨resUr_of_isArithFrobeniusLift, fun h => h.trans (frobElt_eUr K w)⟩

/-- Inertia at `w` is the kernel of the restriction `resUr K w` (tex 3470–3480).
Kind: PROVED. -/
theorem mem_inertia_iff_resUr {σ : Field.absoluteGaloisGroup (w.adicCompletion K)} :
    σ ∈ inertiaSubgroup (w.adicCompletion K) ↔ resUr K w σ = 1 := by
  rw [← ker_restrictMaximalUnramifiedHom]
  exact MonoidHom.mem_ker

/-- An element of the inertia subgroup at `w` restricts trivially to `K_w^ur`
(tex 3470–3480). Kind: PROVED. -/
theorem resUr_of_mem_inertia {σ : Field.absoluteGaloisGroup (w.adicCompletion K)}
    (hσ : σ ∈ inertiaSubgroup (w.adicCompletion K)) : resUr K w σ = 1 :=
  mem_inertia_iff_resUr.mp hσ

/-! ### Inflated coefficients -/

/-- On the inflation of a representation `X` of `Gal(K_w^ur/K_w)` (a surjection `f : X → M`
with `f (resUr g • x) = g • f x`), inertia at `w` acts trivially (tex 3470–3480).
Kind: PROVED. -/
theorem smul_eq_self_of_mem_inertia_of_inflation {X M : Type} [MulAction (GUr K w) X]
    [MulAction (Gloc K w) M] (f : X → M)
    (hf : ∀ (g : Gloc K w) (x : X), f (resUr K w g • x) = g • f x)
    (hsurj : Function.Surjective f) {σ : Gloc K w}
    (hσ : σ ∈ inertiaSubgroup (w.adicCompletion K)) (m : M) : σ • m = m := by
  obtain ⟨x, rfl⟩ := hsurj m
  rw [← hf, resUr_of_mem_inertia hσ, one_smul]

/-- On the inflation of a representation of `Gal(K_w^ur/K_w)`, every subgroup `P` of inertia,
in particular the wild inertia, acts trivially; this is the hypothesis of
`TameCochainQuasiIso` on `P` (tex 3470–3480). Kind: PROVED. -/
theorem smul_eq_self_of_le_inertia_of_inflation {X M : Type} [MulAction (GUr K w) X]
    [MulAction (Gloc K w) M] (f : X → M)
    (hf : ∀ (g : Gloc K w) (x : X), f (resUr K w g • x) = g • f x)
    (hsurj : Function.Surjective f) {P : Subgroup (Gloc K w)}
    (hP : P ≤ inertiaSubgroup (w.adicCompletion K)) : ∀ x ∈ P, ∀ m : M, x • m = m :=
  fun _ hx m => smul_eq_self_of_mem_inertia_of_inflation f hf hsurj (hP hx) m

/-! ### Iwasawa generators -/

variable (K w) in
/-- An Iwasawa triple at `w`: an arithmetic Frobenius lift `φ`, an inertia element `σ` with the
EXACT relation `φ σ φ⁻¹ = σ^q` in `G_{K_w}`, `q` the residue cardinality, and a closed normal
pro-`p` subgroup `P ≤ I_w` (`p` the residue characteristic) with `I_w` the closure of
`⟨σ⟩ P`. These are the place-dependent hypotheses of `TameCochainQuasiIso`
(tex 3470–3480). Kind: definition. -/
structure IsIwasawaTriple (φ σ : Gloc K w) (P : Subgroup (Gloc K w)) : Prop where
  /-- `φ` is an arithmetic Frobenius lift. -/
  frob : IsArithFrobeniusLift (w.adicCompletion K) φ
  /-- `σ` lies in inertia. -/
  mem_inertia : σ ∈ inertiaSubgroup (w.adicCompletion K)
  /-- The exact tame relation. -/
  rel : φ * σ * φ⁻¹ = σ ^ Nat.card 𝓀[w.adicCompletion K]
  /-- `P` is normal. -/
  normal : P.Normal
  /-- `P` is closed. -/
  closed : IsClosed (P : Set (Gloc K w))
  /-- `P` is pro-`p` for the residue characteristic `p`. -/
  proP : TauCeti.IsProP (ringChar 𝓀[w.adicCompletion K]) P
  /-- `P` lies in inertia. -/
  le_inertia : P ≤ inertiaSubgroup (w.adicCompletion K)
  /-- Inertia is topologically generated by `σ` and `P`. -/
  closure_eq : (Subgroup.zpowers σ ⊔ P).topologicalClosure = inertiaSubgroup (w.adicCompletion K)

variable (K w) in
/-- **ELLIOT-uncited classical + GLUE: Iwasawa generators at a finite place** (tex 3470–3480;
the manuscript uses the tame structure of the local Galois group there without a citation, and
its bibliography has no entry for Iwasawa or Neukirch–Schmidt–Wingberg). There are
`φ, σ ∈ G_{K_w}` and a subgroup `P` forming an Iwasawa triple: `P = P_w` is the wild inertia (the
pro-`p` Sylow subgroup of `I_w`, closed and normal in `G_{K_w}`); `G_{K_w}/P_w` is topologically
generated by the images of a Frobenius lift `φ` and of an inertia element `σ`, with `I_w/P_w`
procyclic generated by `σ`, subject to `φ σ φ⁻¹ = σ^q`; and the extension of `G_{K_w}/P_w` by the
pro-`p` group `P_w` splits, so that `φ` and `σ` can be chosen in `G_{K_w}` with the EXACT relation.

Literature: K. Iwasawa, "On Galois groups of local fields", Trans. Amer. Math. Soc. 80 (1955),
448–469. Verbatim, p. 448 (transcribed from the scan): "Let p be a prime number, Q_p the field of
p-adic numbers, and Ω an algebraic closure of Q_p. In the present paper, we take a finite
extension k of Q_p in Ω as the ground field and study the structure of the Galois group G(Ω/k) of
the extension Ω/k. Let V be the ramification field of Ω/k, i.e. the composite of all finite tamely
ramified extensions of k in Ω, and let G(Ω/V) and G(V/k) denote the Galois groups of the
extensions Ω/V and V/k respectively. We shall first determine the structure of the groups
G(V/k) = G(Ω/k)/G(Ω/V), and G(Ω/V) and show that the group extension G(Ω/k)/G(Ω/V) splits." and
"Using those results, we then prove in §3 the properties of G(Ω/k) as mentioned above." The
statements of §3 themselves (the generators of `G(V/k)` and their relation) are not quoted here:
the publisher's copy of those pages was not retrievable.

Reading (GLUE): `k = K_w` (a finite extension of `ℚ_p`, `p` odd here) and `G(Ω/k) = G_{K_w}`;
`V` is the maximal tamely ramified extension, so `P_w = G(Ω/V)` is the wild inertia, a closed
normal pro-`p` subgroup; the tame quotient `G(V/k)` is generated by the images of a Frobenius lift
and of a tame inertia generator with `φ σ φ⁻¹ = σ^q` (Iwasawa §3); the splitting announced on
p. 448 lifts both to `G_{K_w}` with the exact relation, and `I_w` is the closure of `⟨σ⟩ P_w`.
Further reading, not a print: Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed.,
author-hosted electronic edition v2.3, Ch. VII §5 (v2.3 page numbers; the pages of the Springer
print are not checked). (7.5.1) Proposition, p. 409: "The ramification group V_k of
the absolute Galois group G_k of a local field k with residue characteristic p is a free
pro-p-group of countably infinite rank." (7.5.3) Theorem (Iwasawa), p. 410: "The Galois group 𝒢_k
of the maximal tamely ramified extension of a local field k is isomorphic to the profinite group G
generated by two elements σ, τ with the only relation στσ⁻¹ = τ^q." The splitting is (3.5.6)
Theorem, p. 192, as used in the proof of (7.5.13), p. 418: "the group 𝒢_k is p-projective by
(3.5.6), and the exact sequence 1 → V_k → G_k → 𝒢_k → 1 splits" (printed there for local fields of
characteristic `p`; in characteristic `0` the same argument applies, since `cd_p 𝒢_k = 1`: a GLUE
reading). The Lean statement is an existence statement implied by these results.
Kind: ELLIOT-uncited classical (Iwasawa 1955, p. 448 and §3; not cited in the manuscript, so not a
PRINT) + GLUE (the reading above, the splitting reading in characteristic `0`, and the
identification of `Gloc K w` with `G_{K_w}`).
Links: Iwasawa 1955 https://doi.org/10.1090/S0002-9947-1955-0075239-5; Neukirch–Schmidt–Wingberg
https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/NSW2.3.pdf. -/
def IwasawaGeneratorsAt : Prop :=
  ∃ (φ σ : Gloc K w) (P : Subgroup (Gloc K w)), IsIwasawaTriple K w φ σ P

/-! ### The comparison at a finite place -/

/-- **The tame comparison at a finite place `w ∤ 2`** (tex 3470–3480). From the PRINT
`TameCochainQuasiIso` and an Iwasawa triple `(φ, σ, P)` at `w`, the comparison map
`tameCochainMap` of `C^•_cont(G_{K_w}, M)` to the tame free model, with `q` the residue
cardinality, is a quasi-isomorphism for every finite discrete coefficient module `M` of
`2`-power exponent on which `σ` acts as an involution commuting with `φ` and on which `P` acts
trivially (for inflated `M`, see `smul_eq_self_of_le_inertia_of_inflation`). Kind: PROVED
(from `TameCochainQuasiIso`). -/
theorem tameCochainQuasiIso_at (hT : TameCochainQuasiIso) (h2 : (2 : 𝓞 K) ∉ w.asIdeal)
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    [DistribMulAction (Gloc K w) M] [SMulCommClass (Gloc K w) R M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (Gloc K w) M] [Finite M]
    {φ σ : Gloc K w} {P : Subgroup (Gloc K w)} (hI : IsIwasawaTriple K w φ σ P)
    (Φ g : M →ₗ[R] M) (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, g m = σ • m)
    (hg : g ∘ₗ g = LinearMap.id) (hcomm : Φ ∘ₗ g = g ∘ₗ Φ)
    (hP : ∀ x ∈ P, ∀ m : M, x • m = m) (he : ∃ e : ℕ, ∀ m : M, 2 ^ e • m = 0) :
    QuasiIso (GHom.toCC (tameCochainMap Φ g φ σ
      (Nat.card 𝓀[w.adicCompletion K]) (odd_natCard_residueField h2) hΦ hgσ hg hcomm hI.rel)) :=
  hT (w.adicCompletion K) R M φ σ P Φ g _ (odd_natCard_residueField h2) hΦ hgσ hg hcomm hI.rel
    hI.frob hI.mem_inertia rfl (ringChar_residueField_ne_two h2) hI.normal hI.closed hI.proP
    hI.le_inertia hI.closure_eq hP he

/-- **The tame comparison at `w ∤ 2` for inflated coefficients** (tex 3470–3480). If `M` is the
inflation of a representation `X` of `Gal(K_w^ur/K_w)` (a surjection `f : X → M` with
`f (resUr g • x) = g • f x`), then inertia acts trivially, so `g = id` and `P` acts trivially;
with `Φ = (φ • ·)` the comparison map is a quasi-isomorphism, given `TameCochainQuasiIso` and an
Iwasawa triple. Kind: PROVED (from `TameCochainQuasiIso`). -/
theorem tameCochainQuasiIso_at_inflation (hT : TameCochainQuasiIso)
    (h2 : (2 : 𝓞 K) ∉ w.asIdeal) (R : Type) [CommRing R] (M : Type) [AddCommGroup M]
    [Module R M] [DistribMulAction (Gloc K w) M] [SMulCommClass (Gloc K w) R M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Gloc K w) M] [Finite M]
    {X : Type} [MulAction (GUr K w) X] (f : X → M)
    (hf : ∀ (g : Gloc K w) (x : X), f (resUr K w g • x) = g • f x)
    (hsurj : Function.Surjective f) {φ σ : Gloc K w} {P : Subgroup (Gloc K w)}
    (hI : IsIwasawaTriple K w φ σ P) (he : ∃ e : ℕ, ∀ m : M, 2 ^ e • m = 0) :
    QuasiIso (GHom.toCC (tameCochainMap (DistribSMul.toLinearMap R M φ) LinearMap.id φ σ
      (Nat.card 𝓀[w.adicCompletion K]) (odd_natCard_residueField h2) (fun _ => rfl)
      (fun m => (smul_eq_self_of_mem_inertia_of_inflation f hf hsurj hI.mem_inertia m).symm)
      (LinearMap.id_comp _) ((LinearMap.comp_id _).trans (LinearMap.id_comp _).symm) hI.rel)) :=
  tameCochainQuasiIso_at hT h2 R M hI _ _ (fun _ => rfl)
    (fun m => (smul_eq_self_of_mem_inertia_of_inflation f hf hsurj hI.mem_inertia m).symm)
    (LinearMap.id_comp _) ((LinearMap.comp_id _).trans (LinearMap.id_comp _).symm)
    (smul_eq_self_of_le_inertia_of_inflation f hf hsurj hI.le_inertia) he

end ZInQ.Manuscript.RC.Local

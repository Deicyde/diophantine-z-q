import ZInQKernel.Contrib.OneProof.RC.Local.TameUnramifiedSquare
import ZInQKernel.Contrib.OneProof.RC.Local.TamePlaceBridge
import ZInQKernel.Contrib.OneProof.RC.Local.TameLocalPrint

/-!
# Lane RC31, round 6: the tame local model at a place of a number field, over a field

Manuscript `diophantine_zq.tex`, tex 3470–3481 ((4.4) at augmentation, the unramified
condition).

`TameLocalModelPrintField` is the statement of `TameLocalModelPrint` for field coefficients. It is
PROVED here (`tameLocalModelPrintField_of_prints`) from exactly two literature inputs:

* `TameCochainQuasiIso` (PRINT, `TameFreeModelCochains.lean`): for Iwasawa generators the
  comparison `tameCochainMap` of the continuous cochains with the tame free model is a
  quasi-isomorphism (degrees `≤ 1` are PROVED, `TameQuasiIsoLow.lean`);
* `IwasawaGenerators` (ELLIOT-uncited classical + GLUE, through `IwasawaGeneratorsAt`,
  `TamePlaceBridge.lean`): Iwasawa generators exist at every finite place not above `2` (Iwasawa,
  Trans. Amer. Math. Soc. 80 (1955), p. 448 and §3: the tame quotient and the splitting over the
  wild inertia, both announced on p. 448; not cited in the manuscript; the reading as an Iwasawa
  triple is GLUE).

The rest is PROVED: the strict unramified square (`unr_square`), the passage from
quasi-isomorphisms to homotopy equivalences over a field (`tameLocalModelAt_of_cochainQuasiIso`),
and the identification of the Frobenius, inertia and residue data at the place
(`TamePlaceBridge.lean`; `two_not_mem_of_odd_card` here).

Kinds: PRINT (one statement), ELLIOT-uncited classical + GLUE (one statement), PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex (urCx eUr resUr frob frobCx frobElt)
open ZInQ.Contrib.CloudB3RC53.RankCounts (GUr)

attribute [local instance] TopRep.distribMulAction

open TauCeti ValuativeRel in
/-- An odd residue cardinality forces `w ∤ 2` (tex 3470–3480). Kind: PROVED. -/
theorem two_not_mem_of_odd_card {K : Type} [Field K] [NumberField K]
    {w : HeightOneSpectrum (𝓞 K)} (hodd : Odd (Nat.card (𝓞 K ⧸ w.asIdeal))) :
    (2 : 𝓞 K) ∉ w.asIdeal := by
  intro h
  have hd : ringChar 𝓀[w.adicCompletion K] ∣ 2 := by
    rw [HeightOneSpectrum.ringChar_residueField_adicCompletion_dvd_iff]
    exact_mod_cast h
  have hp : (ringChar 𝓀[w.adicCompletion K]).Prime := CharP.prime_ringChar _
  have h2 : ringChar 𝓀[w.adicCompletion K] = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd
  rw [← natCard_residueField_adicCompletion K w] at hodd
  let _ := Fintype.ofFinite 𝓀[w.adicCompletion K]
  obtain ⟨n, -, hn⟩ := FiniteField.card 𝓀[w.adicCompletion K] (ringChar 𝓀[w.adicCompletion K])
  rw [Nat.card_eq_fintype_card, hn, h2] at hodd
  exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' n.ne_zero).2 even_two)

/-- **ELLIOT-uncited classical + GLUE: Iwasawa generators at every finite place not above `2`**
(tex 3470–3480; the manuscript does not cite a source for it): the
family of `IwasawaGeneratorsAt`. Literature: K. Iwasawa, "On Galois groups of local fields",
Trans. Amer. Math. Soc. 80 (1955), 448–469; verbatim, p. 448: "We shall first determine the
structure of the groups G(V/k) = G(Ω/k)/G(Ω/V), and G(Ω/V) and show that the group extension
G(Ω/k)/G(Ω/V) splits." (`V` the ramification field: "the composite of all finite tamely ramified
extensions of k in Ω"; the proofs are in §3). Further reading, not a print:
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed., author-hosted electronic
edition v2.3, Ch. VII §5: (7.5.1), p. 409, (7.5.3), p. 410, and the splitting by (3.5.6),
p. 192, as used in the proof of (7.5.13), p. 418 (v2.3 page numbers; the Springer print pages
are not checked). The fuller quotations and the reading are at `IwasawaGeneratorsAt`.
Kind: ELLIOT-uncited classical (Iwasawa 1955, p. 448 and §3: the tame quotient and the splitting
over the wild inertia; not cited in the manuscript, so not a PRINT) + GLUE (the reading as an
Iwasawa triple at each place).
Links: Iwasawa 1955 https://doi.org/10.1090/S0002-9947-1955-0075239-5; Neukirch–Schmidt–Wingberg
https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/NSW2.3.pdf. -/
def IwasawaGenerators : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)),
    (2 : 𝓞 K) ∉ w.asIdeal → IwasawaGeneratorsAt K w

/-- **`TameLocalModelPrint` for field coefficients** (tex 3470–3481): the genuine local complex,
the genuine unramified condition and the inflation form a tame local model, for coefficients in a
field. PROVED from the two literature inputs by `tameLocalModelPrintField_of_prints`.
Kind: definition (the statement). -/
def TameLocalModelPrintField : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (k : Type)
    [Field k] [TopologicalSpace k] (M : Type) [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [Finite M]
    (w : Places K S) (X : TopRep.{0} k (GUr K w.1)) [ContinuousSMul (GUr K w.1) X.V]
    [DiscreteTopology X.V] [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x),
    Function.Bijective f → (∃ n : ℕ, ∀ m : M, (2 ^ n) • m = 0) →
    ∀ (q : ℕ) (hq : Odd q), q = Nat.card (𝓞 K ⧸ w.1.asIdeal) →
      Nonempty (TameLocalModelAt
        (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M w)
        (ofCC (urCx K w.1 X))
        (ofCCHom (urToLocal_galois K S w X f hf))
        (tameNewPlace (ModuleCat.of k X.V) (frob (eUr K w.1) X) q hq))

/-- **The tame local model at a place, over a field, from the two literature inputs**
(tex 3470–3481): `TameCochainQuasiIso` and `IwasawaGenerators` imply
`TameLocalModelPrintField`. Kind: PROVED. -/
theorem tameLocalModelPrintField_of_prints (hT : TameCochainQuasiIso)
    (hI : IwasawaGenerators) : TameLocalModelPrintField := by
  intro K _ _ S k _ _ M _ _ _ _ _ _ _ _ w X _ _ _ f hf hbij hexp q hq hqcard
  have h2 : (2 : 𝓞 K) ∉ w.1.asIdeal := two_not_mem_of_odd_card (hqcard ▸ hq)
  obtain ⟨φ, σ, P, hIw⟩ := hI K w.1 h2
  have hq' := hqcard.trans (natCard_residueField_adicCompletion K w.1).symm
  subst hq'
  have : Finite (ResMod (locMap K S w.1) M) := inferInstanceAs (Finite M)
  have hexp' : ∃ e : ℕ, ∀ m : ResMod (locMap K S w.1) M, 2 ^ e • m = 0 := hexp
  have hQ := tameCochainQuasiIso_at_inflation hT h2 k (ResMod (locMap K S w.1) M)
    (X := X.V) f hf hbij.2 hIw hexp'
  let f' : X.V →ₗ[k] ResMod (locMap K S w.1) M := f
  have hbij' : Function.Bijective f' := hbij
  have hf' : ∀ (g : Gloc K w.1) (x : X.V), f' (resUr K w.1 g • x) = g • f' x := hf
  obtain ⟨m, -, -⟩ := tameLocalModelAt_of_cochainQuasiIso (eUr K w.1) (resUr K w.1) X
    (G := Gloc K w.1) (M := ResMod (locMap K S w.1) M) f' hbij' hf' _ φ σ _ hq _
    (resUr_of_isArithFrobeniusLift hIw.frob) (resUr_of_mem_inertia hIw.mem_inertia) hIw.rel hQ
  exact ⟨m⟩

end ZInQ.Manuscript.RC.Local

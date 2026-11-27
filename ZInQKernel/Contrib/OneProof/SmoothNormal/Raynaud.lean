import ZInQKernel.Contrib.OneProof.SmoothNormal.Projective

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits
namespace Y3Buzzard.SmoothNormal

open ProjGlue

/-!
# Projectivity of abelian schemes over a normal base (Raynaud, LNM 119, p. 159)

The leaf `RaynaudLNM119Normal` states, for false elliptic curves over the spectrum of a
noetherian normal ring, the theorem that Raynaud's volume prints on p. 159, attributed there to
Grothendieck (cf. XI 1.4 ci-dessous); the text of XI 1.4 itself is not read here: an abelian
scheme over a normal base is projective. Restricting to affine opens gives `LocProjNormal`, the
form in which `Projective` uses it, and so the level-three moduli statement from nine printed
inputs.
-/

/-- Leaf (M. Raynaud, *Faisceaux amples sur les schémas en groupes et les espaces homogènes*,
Lecture Notes in Math. 119, Springer, 1970, Ch. XI, §1, p. 159), in the form used here: a false
elliptic curve over the spectrum of a noetherian normal ring is a closed subscheme of a
projective space over that ring.

The page of this quotation carries no printed number; 159 is read from "- 160 -" on the next
page.

p. 159: "1.- Quasi-projectivité globale. Soient S un schéma normal, G un S-schéma en groupes
lisse, à fibres connexes. Nous savons que G est localement quasi-projectif sur S (VI 2.4), mais
dans deux cas importants on peut même affirmer que G est globalement quasi-projectif sur S : en
effet, si les fibres maximales de G sont affines, on a vu que G était quasi-affine sur S
(VII 2.2) ; d'autre part, si G est un S-schéma abélien, Grothendieck a montré que G était
projectif sur S (cf. XI 1.4 ci-dessous) ; …"

The statement is attributed there to Grothendieck (cf. XI 1.4 ci-dessous); the text of XI 1.4
itself is not read here. Ch. XII, p. 185 (the page carries no printed number; 185 is read from
"- 186 -" on the next page), recalls it in the form "on a vu également (XI 1.4) que A est
projectif sur S si S est intègre et géométriquement unibranche". The leaf is covered by that form
too: a noetherian normal ring is a finite product of normal domains (EGA IV₂ (5.13.5), last
sentence, p. 133); a normal local domain is geometrically unibranch (BACKGROUND); and closed
immersions over the finitely many components glue to one into `P^N_R` after padding coordinates
(EGA II (5.5.5)–(5.5.6), p. 105).

Identifications.
* "S un schéma normal": EGA 0_I (4.1.4), p. 37, defines normal ringed spaces, and EGA IV₂
  (5.13.5), p. 133, the definition for rings: a ring `A` is normal when every localization `A_p`
  at a prime is an integrally closed domain. `IsNormalNoeth` asks moreover that `R` be noetherian,
  so the leaf is weaker than the print.
* `FEC (Spec R)`: a false elliptic curve over `Spec R` is in particular an abelian `Spec R`-scheme,
  a proper smooth group scheme whose geometric fibres are connected (J. S. Milne, *Abelian
  Varieties* (1986), §20, p. 42 of the author's retyped edition); the action of `O` plays no part
  here.
* "projectif": in the sense of EGA II (5.5.1)–(5.5.2), pp. 103–104, a closed subscheme of a
  `P(ℰ)` with `ℰ` quasi-coherent of finite type. If "projectif" is read as "propre et
  quasi-projectif" (an `S`-ample sheaf), (5.5.3)(ii), p. 104, gives projectivity over the
  quasi-compact `Spec R`; if it is read as "proper with a relatively very ample sheaf",
  (5.5.4)(i), p. 104, gives it, its condition 3° being automatic over a locally noetherian base
  (EGA III §3, as (5.5.4)(i) says). `Spec R` is affine, hence quasi-compact, as (5.1.2) and
  (5.5.4)(ii) require, and `𝒪_S` is ample on it ((5.1.2) c'), p. 94, an affine scheme being
  quasi-affine (5.1.1)); so by (5.5.4)(ii), p. 104, such an `X` is `S`-isomorphic to a closed
  subscheme of `P^r_S`. EGA II (4.1.1), p. 71, defines `P^r_Y = P(𝒪_Y^{r+1}) =
  Proj(S(𝒪_Y^{r+1}))`; `S_R(R^{r+1}) = R[x_0, …, x_r]`, graded by total degree (BACKGROUND); and
  `PNR R r` is `Proj` of `MvPolynomial (Fin (r+1)) R` with the total-degree grading. -/
def RaynaudLNM119Normal : Prop :=
  ∀ (R : Type) [CommRing R], IsNormalNoeth R →
    ∀ (A : FEC (Spec (CommRingCat.of R))),
      ∃ (N : ℕ) (i : A.F.left ⟶ PNR R N), IsClosedImmersion i ∧ i ≫ PNR.toSpec R N = A.F.hom

/-- The restriction of a false elliptic curve to an affine open `U` of the base, as a scheme over
`Spec Γ(X, U)`, is isomorphic to the open subscheme `A.F.hom ⁻¹ᵁ U` of the total space. -/
def preimageIsoPullback {X : Scheme.{0}} (A : FEC X) {U : X.Opens} (hU : IsAffineOpen U) :
    (A.F.hom ⁻¹ᵁ U).toScheme ≅ (A.pullback hU.fromSpec).F.left :=
  (pullbackRestrictIsoRestrict A.F.hom U).symm ≪≫
    (asIso (pullback.map A.F.hom hU.fromSpec A.F.hom U.ι (𝟙 _) hU.isoSpec.inv (𝟙 _)
      (by simp) (by simp [IsAffineOpen.isoSpec_inv_ι]))).symm

/-- `RaynaudLNM119Normal` gives `LocProjNormal`: restrict the false elliptic curve to the affine
open `U ≅ Spec Γ(X, U)`. -/
theorem locProjNormal_of_raynaud (h : RaynaudLNM119Normal) : LocProjNormal := by
  intro X A U hU hN
  obtain ⟨N, i, hi, -⟩ := h Γ(X.left, U) hN (A.pullback hU.fromSpec)
  exact ⟨N, (preimageIsoPullback A hU).hom ≫ i, inferInstance⟩

/-- `Y3RouteA.Y3FullThreeRepZ30` from nine printed inputs: `y3FullThreeRepZ30_of_printed_locProj`
with `LocProjNormal` obtained from Raynaud's theorem. -/
theorem y3FullThreeRepZ30_of_printed_raynaud (hL : XDV15.BuzzardXDV15Lit) (hM3 : MilneProp207 3)
    (hR : MilneRem84) (hBz : BuzzardLemma22Full5) (hMl : MilneThm125Pts)
    (hB4 : ZeroPreservingIsHomLN) (hE : EGAIV17_5_7) (hRay : RaynaudLNM119Normal)
    (hM5 : MilneProp207 5) : Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_locProj hL hM3 hR hBz hMl hB4 hE (locProjNormal_of_raynaud hRay)
    hM5

end Y3Buzzard.SmoothNormal

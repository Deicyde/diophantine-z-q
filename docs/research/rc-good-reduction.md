# Good reduction at the actual (O.7) row

**Scoped stop.** The Néron extension, valuative lifting, and the
passage of the generic signed identity through base change are Lean
steps. The actual `hπ` and the Atkin–Lehner field still need an
identification of the PM data with the fibres of the fixed modular map.
The existing rational normalization and the PM coarse point/divisor
interface do not give that identification. A smooth proper model of
the rational curve alone cannot identify the PM quotient: replacing
the supplied quotient by zero preserves all the operator equations of
`PMAdelic.SpecialFibre`. No new printed leaf is declared.

## Source audit and smallest missing geometry

- **(i) The modular model.** P. Deligne and M. Rapoport,
  *Les schémas de modules de courbes elliptiques*, in LNM 349 (1973),
  VI.6, proposed locator VI 6.9 (**UNVERIFIED**), is the candidate
  for the compactified coarse `Γ₀(N)` model and its good reduction
  away from `N`. J. Igusa, *Kroneckerian model of fields of elliptic
  modular functions* (1959), exact theorem **UNVERIFIED**, is the
  historical good reduction lead. The tree's `IgusaSL2X` concerns
  generic monodromy; it supplies no integral model. The cited
  passages were not available for a printed-form check. On the
  scope “the curve has good reduction,” the statement supplies
  smoothness and properness. Properness extends the rational cusp
  as a section, once that cusp is identified on the generic fibre.
  The bare assertion does not identify its reduction with the PM
  cusp, extend the specified involution as an operator, or identify
  special points with reductions of the specified enhanced elliptic
  curves. In the canonical moduli construction the cusp is the
  section from the standard marked degenerate elliptic curve;
  `W_Q`, `Q = p^vₚ(N)`, comes from the cyclic `Q`-isogeny
  and its dual, retaining the part of the level prime to `Q`.
  These are construction and comparison steps. It is unverified
  whether the proposed locator states any of them explicitly.
- **(ii) Néron mapping property.** S. Bosch, W. Lütkebohmert and
  M. Raynaud, *Néron Models* (1990), §1.2 Def. 1 and Prop. 8
  (**UNVERIFIED**): the existing `CToPrinted.IsNeronModelOver`
  gives bijectivity of generic restriction for smooth sources.
  `NeronExt.isNeronModelOver_of_grpObj` proves this property in
  the case used here, a supplied smooth proper group model over a DVR.
  The general Dedekind existence statement already has the
  formulation `GroupLawNeron.NeronSchemeExtensionDedekind` (§1.4
  Thm. 3, **UNVERIFIED**). Neither the general existence result nor
  the proposed §7.1 Thm. 1 is needed for this good target case.
- **The selected CM points.** Take the localization of the ring of
  integers of the conductor-one class field at the prime restricted
  from `StageKummer.chosenDatumPlace`. Each rational CM conjugate
  over that field lifts by properness, with the same reduction map
  for the section and its image. Inertness is not a hypothesis of
  valuative lifting. It is used for the supersingular CM
  identification and residue field: the inert prime of the
  quadratic field is principal and splits in its conductor-one
  class field. `WitnessSpec.FrobeniusPlace.ringClassReduction`
  already reads the target reduction in the detector's quadratic
  group. Identifying the lifted source point with the reduced
  enhanced elliptic curve at that same place is the separate CM
  comparison of tex 9265–9279. For the generic signed identity,
the rational translation can also be lifted by properness in the
target or obtained as the image of the moved integral cusp:
evaluating the generic identity at infinity gives that translation
because the rational map is based there.

The smallest source model interface still needed is the actual
compactified coarse moduli scheme over `ℤ_(ℓ₀)`, with its
identification over `ℚ` with `X0Model3.model N` (including the
prescribed `τ ↦ (ℂ/(ℤ+ℤτ), ⟨1/N⟩)` chart). For the consumer,
one needs its cusp section and `W_Q`, and the reading of their
specializations and of the actual point labels as PM coarse points.
The tree does not have this compactified moduli problem or the
comparison with the rational normalization. It is substantial:
it needs the compactified moduli objects, their level structure
and maps, and the comparison of the two fibres. An existential
statement about an unnamed smooth proper scheme with a generic
isomorphism would not supply these data and would not be a
printed-form transcription of a theorem about the moduli scheme.

On the target side one needs the smooth proper group scheme of
the given integral Weierstrass equation at `StageKummer.goodAt`,
its generic comparison with the `Proj` in `PreparedParam`,
and the identification of its residue point law and evaluation
with the existing coordinate reduction. In particular the
residue value of a section with generic point `y` must be
`StageKummer.reduceDatum … y`. There is already a coordinate
reduction map, but no such scheme/group comparison in these
interfaces. This part is smaller than general elliptic moduli
theory: it needs the single good Weierstrass model and its group law
and point comparison over the prescribed traits.

Finally the based PM composite on ([z]-[∞]) must **be**
the residue evaluation of the extension at the PM point (z).
This is `hPM` in `hpi_of_integralDiagram` on the chosen
conjugates, and `hval` in `atkinQuotient_of_integralRelation`
for the points used there. For the manuscript's realization,
use the specialization of the fixed based map, whose induced
map on the special Jacobian gives that composite. Alternatively
one can prove the identity using the relative Jacobian and
base change of the based Abel–Jacobi map. The row needs only the
composite on the indicated divisors, so a full relative Picard
comparison is not needed if the PM quotient is constructed from
the specialized map. Neither approach gives this identity for an
arbitrary pre-existing `G`. These are integration and model
construction steps (c), not further printed leaves.

## Checked statements

Declarations are in `ZInQ.Manuscript.RC.GoodReduction`. The new
proofs are on-the-spot glue (c).

| Declaration | Statement and what it supplies |
| --- | --- |
| `existsUnique_integralMap` | Over a DVR, given a smooth source, a smooth proper group target, identifications of their generic fibres, and a morphism between the identified fibres, there is a unique morphism over the DVR restricting to the specified one. Uses the existing good-model Néron theorem. |
| `exists_integralPoint` | Over any valuation ring mapping to the base of a proper scheme, a generic point over its fraction field over that base lifts to the valuation ring. Supplies the source and target sections at the same trait when the models have been realized. |
| `integralAffine_baseChange` | If `W_K ≫ f_K = f_K ^ ε * c_K` in morphisms to the generic group object (powers and multiplication encode the elliptic group law), the same relation holds after any base change. Base change preserves the group operations on these morphisms. |
| `atkinQuotient_of_affine` | For an evaluation `v` equal to the based quotient at the points, if `v(∞) = 0` and the same affine formula holds at `x` and `∞`, the quotient of `[Wx] - [W∞]` equals `ε` times the quotient of `[x] - [∞]`. |
| `atkinQuotient_of_integralRelation` | Given the generic affine identity (with the translation an integral section), the residue reading of `W`, and the based PM reading in the residue point group, gives the exact equation of `SpecialFibreAtSigns.atkin_quotient` at `p`, with `ε = (w p : ℤ)`. It works on every point for which those readings hold, hence on the supersingular subset. The translation cancels before applying `L`. |
| `hpi_of_integralDiagram` | From the lift of the fixed rational map, the integral sections of the labelled source conjugates and their target values, their PM and target coordinate readings at the same residue point, and the characteristic-zero comparison with the chosen datum, concludes `∀ c, G.specialize (r c) = datumReduction dat v w hg (conjugate dat (artin c))`. With `G := PMAdelic.geometricInput J G`, the chosen datum, place, good equation and Artin labels from `O7Residual.At`, this is its `hπ` goal: `StageKummer.reduceDatum` abbreviates that very reduction. |

## Remaining inputs for the actual row

References below give intended origins; locators are **UNVERIFIED**
in this run. An existing Lean input may need additional comparison
before that source supplies it.

| Input | Refereed theorem or remaining reason |
| --- | --- |
| Fixed curve, level, parametrization and stage `s`; `hN,hcop,H,hm` | Fixed data from the manuscript's setup. Modularity: C. Breuil, B. Conrad, F. Diamond, R. Taylor, *On the modularity of elliptic curves over ℚ: wild 3-adic exercises* (2001), Thm. A. The chosen stage uses finite Chebotarev (N. Chebotarev, *Die Bestimmung der Dichtigkeit einer Menge von Primzahlen, welche zu einer gegebenen Substitutionsklasse gehören*, 1926, density theorem); the reduction here uses the existing place and good equation. |
| Coarse supersingular classes and their operators (`J`) | J. Voight, *Quaternion Algebras* (2021), Main Thm. 14.6.1 for the algebra; D. Jetchev and B. Kane, *Equidistribution of Heegner points and ternary quadratic forms*, journal version (2011), §§1.1–1.2 and 2.5 as cited in the manuscript's version. Correct geometric realization and source scope remain to be checked. |
| Reference quadratic embedding | J. Voight, *Quaternion Algebras* (2021), Main Thm. 14.6.7 (V ⇒ III), via the existing embedding construction. |
| `ht` and the chosen source CM point | The chosen selector must cover all admissible rows, including torsion rows. This is an implementation choice using CM field of definition, not a theorem about arbitrary selectors. G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions* (1971), Ch. 6 (exact locator UNVERIFIED); L. Cai, Y. Chen, Y. Liu, *Heegner points on modular curves* (2018), §2. Their Thm. 2.15 is a trace relation, not the field-of-definition statement. Retain the same source point and embedding in the datum. |
| `hCM` and the reading of the actual reduced labelled points | Tex 9265–9279 uses C. Cornut and D. Jetchev, *Liftings of reduction maps for quaternion algebras* (2010), Thm. 3.1 and §§4.9–4.10. Only the preprint is identified in the manuscript and tree audit. No refereed replacement verified here. The source identification at the chosen reference origin and place is separate from Néron extension. |
| `hπ` | Deligne–Rapoport (1973), VI.6, proposed VI 6.9; Bosch–Lütkebohmert–Raynaud (1990), §1.2 Def. 1 and Prop. 8, reused in Lean. The actual integral modular and target models and the based PM reading above remain to be supplied. |
| `w`, generic signed identity and `hSign` | Atkin–Lehner sign on the fixed newform and generic affine identity at tex 2943–2946; A. O. L. Atkin and J. Lehner, *Hecke operators on Γ₀(m)* (1970), §4 (candidate for the analytic operator; not a citation for the rational identity). The fixed-scale generic passage is separate work. `SpecialFibreAtSigns.toSpecialFibre` makes the equality of the two sign reads definitional once the quotient equation is supplied. |
| Special-fibre Atkin–Lehner quotient equation | Generic signed identity plus the same Deligne–Rapoport model and Néron property. Requires the geometric `W_Q` reading on the special fibre and the common based PM composite. The reduction and cancellation steps are checked here. |
| Remaining `SpecialFibre` Hecke, cusp and Frobenius fields | Tex 8479–8487 and 8489–8492. Need geometric good Hecke correspondences, their value at the cusp and equivariance for the same quotient. The rational Hecke assertion has the citation issue below. Frobenius compatibility is functoriality once the cusp, curve and map are realized over the prime residue field. The supersingular uniformizer comparison is part of `J`. |
| `hCusp` | R. Elkik, *Le théorème de Manin–Drinfeld* (1990), Théorème p. 59, plus the fixed multiplier and specialization of the moved cusps. Separate work. |
| Beyond the row: phase reading of `W.aθ`, native torsion multiplier, admissible odd sign | Inputs for `oddStagedActual`, not additional geometry for `datumAtActual`. The phase reading is a comparison with the fixed coefficient data; multiplier and sign are the existing arithmetic inputs. |

## Known issues

- Tex 8468–8474: the existing audit records that the cited
  Jetchev–Kane comparison omits level one; see
  `docs/research/rc-stage-kummer.md`. This is a citation scope error.
- Tex 1784 and 1788: the prior source audit in
  `ZInQKernel/Contrib/OneProof/RC/PrintsAnalytic/Milne.lean` records that the specified locators
  in Milne do not give the normalized newform or the Hecke identity.
  Neither is used as a source in the new proofs.
- Tex 9265–9279: the named preprint is not an eligible new leaf.
  The locator and its use at the chosen origin remain to be checked
  against any refereed replacement.
- Deligne–Rapoport VI 6.9 and the proposed Igusa locator are not
  checked. No claims about the exact wording or a source error at
  either locator are made here.

## Manuscript check

| Tex lines | Step | Verdict |
| --- | --- | --- |
| 1785–1788 | Use the fixed based rational map and its Hecke action. | unverified |
| 2915–2919 | Choose the CM point at the datum's complex embedding and evaluate the same rational map. | OK |
| 2943–2946 | Rational affine Atkin–Lehner formula at the fixed scale. | unverified |
| 8365–8376 | Restrict the chosen detector place and use good reduction at that prime. | OK |
| 8378–8398 | Keep the same target reduction and quadratic residue detector. | OK |
| 8468–8474 | Scope of the Jetchev–Kane citation. | error |
| 8476–8479 | Realize the compactified good modular model and the good elliptic model. | unverified |
| 8476–8479 | Extend the generic morphism once those models are given; lift field points by properness (c). | gap filled |
| 8479–8487 | Realize the based PM quotient and the good Hecke correspondences on the actual fibre. | unverified |
| 8487–8489 | Match the integral `W_Q` to the coarse operator at the points and at the cusp. | unverified |
| 8487–8489 | Carry the generic affine relation to the residue group and cancel the translation on degree-zero divisors (c). | gap filled |
| 8488–8492 | Multiply by the prescribed `L` and use the Frobenius normalization. | unverified |
| 9265–9279 | Identify each coarse label with the actual point reduced at the detector's place. | unverified |
| 9283–9291 | Compare point values by restricting the integral diagram to the residue point (c). | gap filled |
| 9331–9339 | Use the same sign and kill the cusp term with `L`. | unverified |

## Verification

`Integral`, `Atkin` and `Row` each passed a targeted `lake build`
using source-matched dependency artifacts. Builds were serial, with
the host resource gate and 60 GB user scopes. The six in-module
`#print axioms` results contain only `propext`, `Classical.choice`
and `Quot.sound`. The scratch `Consumers` build checks that the
pointwise conclusion with the actual labels and place has the precise
type used by `O7Residual.At`.

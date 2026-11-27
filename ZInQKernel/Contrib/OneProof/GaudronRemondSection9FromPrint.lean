import ZInQKernel.Contrib.OneProof.GaudronRemondSection9SS
import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.ConnectedOpenFromProperModel
import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.MarkedSemiabelianComponent
import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.MarkedHeightWitness
import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed

/-!
# The printed lower bound for the stable Faltings height

É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), §9, p. 2098,
in the proof of Lemme 9.1: "Sinon nous utilisons la minoration de la hauteur de Faltings
h_F(C_{i,j}) ≥ −(3/2) dim C_{i,j} due à Bost (voir [GR1, Corollaire 8.4] en prenant garde à la
différence entre h(·) et h_F(·) rappelée au paragraphe 2.3)"; there it is applied to the
`C_{i,j}`, abelian varieties simple over `k₁`. The same bound is printed for `A` on p. 2101
("en notant que h_F(A) ≥ −3g/2 (minoration de Bost)") and for `B₁` on p. 2102.

Its source is É. Gaudron and G. Rémond, *Théorème des périodes et degrés minimaux
d'isogénies*, Comment. Math. Helv. 89 (2014), Corollaire 8.4, p. 400: "Pour toute variété
abélienne A définie sur un corps de nombres, on a h(A) ≥ −(1/2)(dim A) log(2π)". With
`h_F(A) = h(A) − (g/2) log π` (p. 352) and p. 352's own step "en majorant log(π√2) ≤ 3/2", this
gives `h_F(A) ≥ −(3/2) dim A`. Only the inequality printed in §9 of the Duke paper is assumed
here, not the stronger bound of Corollaire 8.4.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped BigOperators CategoryTheory.MonObj NumberField

namespace ZInQ.Contrib.FaltingsLowerBound

open ZInQ.DefFaltings ZInQ.HeightDict ZInQ.HeightFix ZInQ.H5Glue ZInQ.SemistabAssembly
open ZInQ.BostGR9 ZInQ.Contrib.IsogenyDegree
open ZInQ.Contrib.CloudB3W16Torsion (mumfordTorsionAlgClosed_proof)
open DictModels.RaynaudOr (HasSemiAbelianIdCompTorus)

/-- The §9 inequality evaluated on a semiabelian model of the marked variety
`A_L`. The determinant lattice, chosen section, and all squared norms belong
to that model over `𝓞 L`, in Faltings' original normalization.

The metric. CMH 89, §2.3, p. 351, defines `‖s‖² := (2π)^{−g} ∫_{A_σ} |s ∧ s̄|` for the height
`h(A)`; Faltings' original `h_F` drops the `π` (p. 352), so `‖s‖²_F = 2^{−g} ∫ |s ∧ s̄|`. For
`s = f dz₁ ∧ … ∧ dz_g`, `|s ∧ s̄| = 2^g |f|² ∏ dx_i dy_i`, since `dz ∧ dz̄ = −2i dx ∧ dy`; hence
`‖s‖²_F = ∫ |f|² ∏ dx_i dy_i`, which is the number `r τ` here (`isPrintedMetricSq_iff`:
`r = |c|² · covol`). The right-hand side
`(log [Λ : 𝓞_L η] − ½ Σ_τ log r τ) / [L : ℚ]` is therefore `h_F(A)`, the normalized Arakelov
degree of `ω` with Faltings' metric.

The model and the lattice. A `GroupModel` with connected closed fibres satisfying
`HasSemiAbelianIdCompTorus` (the quotient `B` an abelian variety, the kernel a split torus over
`k̄`) is a "modèle semi-abélien" in the sense of CMH §2.3. The lattice is
`printedDetLattice = detLattice`, the sections of `ε*Ω^g` (`printedDetLattice_eq`, through the
conormal ideals of the zero section at every point of `Spec 𝓞_L`). The height does not depend
on the field or the model: "Cette définition est indépendante des choix de K et de 𝒜"
(p. 351). -/
def DukeSec9OnSemiabelianModel : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (A : PkgI3.AbVar K) (G : GroupModel A L) (g : ℕ),
    A.dim = (g : WithBot ℕ∞) →
    (∀ (p : Ideal (𝓞 L)) [p.IsMaximal],
      ConnectedSpace (resFibre G p).left ∧ HasSemiAbelianIdCompTorus (resFibre G p)) →
    ∀ (eta : G.hodgeSpace g), eta ∈ printedDetLattice G g → eta ≠ 0 →
      secIndex (printedDetLattice G g) eta ≠ 0 →
    ∀ (r : (L →+* ℂ) → ℝ), (∀ τ, IsPrintedMetricSq G τ eta (r τ)) →
      -(3 / 2) * (g : ℝ) ≤
        (Real.log (secIndex (printedDetLattice G g) eta) -
          (1 / 2) * ∑ τ : L →+* ℂ, Real.log (r τ)) / Module.finrank ℚ L

/-- Compare the full witness for the root's height with its computation on the
actual marked semiabelian identity component. In particular the index and the
squared norm at each embedding are preserved, without any metric rescaling. -/
theorem gaudronRemondSec9LowerAnSS_of_dukeSec9 (hPrint : DukeSec9OnSemiabelianModel) :
    GaudronRemondSec9LowerAnSS := by
  intro K _ _ A g hg x hx
  obtain ⟨L, iField, iNumber, iAlg, N, g', hN, hs, hg', eta, hEta, hNZ, hIndex, r, hNorm, hVal⟩ := hx
  have heq : g' = g := by exact_mod_cast hg'.symm.trans hg
  subst g'
  obtain ⟨V, hV, hConn⟩ := connectedOpenOfGroupModels_proof K L A N
  obtain ⟨G, j, hjOpen, hjMon, _, hjIso, _, hSemi⟩ :=
    exists_markedSemiabelianComponent_of_goodOpen N hs.2 V hV hConn
  have hT35 := AvSplit.Final.h38 uniformizationLeafAll_proof mumfordTorsionAlgClosed_proof
  let eta' := hodgeMap G N j g eta
  obtain ⟨hEta', hNZ', hIndex', hNorm'⟩ :=
    @markedHeightWitness_openIso K _ _ A L _ _ _ hT35 g hg G N hN j hjMon hjOpen hjIso
      eta hEta hNZ hIndex r hNorm
  have hIndexNonzero : secIndex (printedDetLattice G g) eta' ≠ 0 := by
    rw [show secIndex (printedDetLattice G g) eta' = secIndex (printedDetLattice N g) eta from hIndex']
    exact hIndex
  have hb := hPrint K L A G g hg hSemi eta' hEta' hNZ' hIndexNonzero r hNorm'
  rw [show secIndex (printedDetLattice G g) eta' = secIndex (printedDetLattice N g) eta from hIndex',
    ← hVal] at hb
  exact hb

end ZInQ.Contrib.FaltingsLowerBound

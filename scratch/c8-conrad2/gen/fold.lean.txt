
/-! ## Hand-fold shape (c8-conrad2): the new bundle generations and the next top theorem

The fold the integrator would write once consumer (iii) (`hodgeTateDecompAbVar → r10`) no longer reads the Picard
rows: the textbook bundle gains `poincareComplement` (restored, ELLIOT), the added bundle gains the C8 inputs. Until
then the rows stay in `OpenAddedLeaves27`, so this generation only adds fields (dry run, not proposed as a fold). -/

namespace HDec
namespace HSyn

/-- `OpenTextbookLeaves18` (empty) with Poincaré's theorem restored as a printed textbook leaf (step E1-E2,
diophantine_zq.tex L865; ELLIOT: the manuscript cites nothing there). -/
structure OpenTextbookLeaves19C8 : Prop where
  /-- Poincaré complete reducibility, complement form (Milne, *Abelian varieties*, in Cornell–Silverman 1986,
  Prop. 12.1, over any field; Mumford §19 Thm 1 over an algebraically closed field; locators UNVERIFIED), stated in
  characteristic `0` without the conclusion that `Z → J` is a closed immersion (a consequence of the print). -/
  poincareComplement : _root_.ZInQ.Contrib.AVB1.PoincareComplement

/-- `OpenAddedLeaves27` with the inputs of step C8 by local algebraicity (diophantine_zq.tex L758-766). -/
structure OpenAddedLeaves28C8 : Prop where
  picRepresentableAbVar : _root_.T09Pic.PicRepresentableAbVar
  kleimanPicZeroProper954SiteQ : _root_.KleimanSite.KleimanPicZeroProper954SiteQ
  /-- Conrad, *Lifting global representations with local properties* (author preprint, 2011), App. B, pp. 32-33,
  base field `ℚ_p` (unread on host; unrefereed). -/
  conradAppBQp : _root_.HDec.G0Galois.C8Conrad.ConradAppBQp
  /-- Tate, *p-divisible groups* (1967), §3.3 Thm 2, for the completion of `K^{ur}` (locator UNVERIFIED). -/
  tateTwistInvariantsInertia : _root_.HDec.G0Galois.C8Conrad.TateTwistInvariantsInertia
  /-- GLUE (on-the-spot, N5 L758-760, L765-766): the twisting character is Hodge–Tate of weight 0 at 5. -/
  twistCharHTWt0 : _root_.HDec.G0Galois.C8Conrad.TwistCharHTWt0
  /-- GLUE (dictionary): inertia groups of `ℚ̄` above `q` are conjugate to `decomp(I_{ℚ_q})`. -/
  inertiaAtPDecomp : _root_.HDec.G0Galois.C8Conrad.InertiaAtPDecomp
  /-- GLUE (dictionary over Mathlib's Minkowski theorem): an algebraic number fixed by all inertia groups is rational. -/
  minkowskiInertiaQ : _root_.HDec.G0Galois.C8Conrad.MinkowskiInertiaQ

theorem openAddedLeaves27_of_OpenAddedLeaves28C8 (n : OpenAddedLeaves28C8) : OpenAddedLeaves27 where
  picRepresentableAbVar := n.picRepresentableAbVar
  kleimanPicZeroProper954SiteQ := n.kleimanPicZeroProper954SiteQ

theorem c8Inputs_of_OpenAddedLeaves28C8 (n : OpenAddedLeaves28C8) : _root_.HDec.G0Galois.C8Conrad.C8Inputs where
  conradAppBQp := n.conradAppBQp
  tateTwistInvariantsInertia := n.tateTwistInvariantsInertia
  twistCharHTWt0 := n.twistCharHTWt0
  inertiaAtPDecomp := n.inertiaAtPDecomp
  minkowskiInertiaQ := n.minkowskiInertiaQ

/-- **The next top theorem (hand-fold shape)**: `ZInQ.SixContactMin` with the Picard rows read only by consumer (iii). -/
theorem sixContactMin_of_open72C8 (r : OpenResearchLeaves52) (t : OpenTextbookLeaves19C8) (l : OpenAddedLeaves28C8) :
    ZInQ.SixContactMin :=
  sixContactMin_of_open71_c8 r ⟨⟩ (openAddedLeaves27_of_OpenAddedLeaves28C8 l) t.poincareComplement
    (c8Inputs_of_OpenAddedLeaves28C8 l)

end HSyn
end HDec

#print axioms HDec.HSyn.sixContactMin_of_open72C8

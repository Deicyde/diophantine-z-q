# cm-branch2 report notes (working draft; the report is docs/research/cm-branch2.md)

## CMFibreSplit decomposition (manuscript)
- L520-562 (A8): K splitting field of the fibre of the normalized cover over u, [K:Q] <= F0; fibre A/K; W0 = Res_{K/Q} A,
  geometric End lattice rank r <= 16 F0^2; kernel field E of the Galois action on End(W0_Qbar), L = EK normal,
  [L:Q] <= F0 3^{r^2} <= D; L defines every geometric endomorphism and every ordered conjugacy homomorphism of A.
  The chain's formalization: G0ModField.KernelFieldExists (KernelFieldOut), proved only through ConjMapsNoCM, i.e. FS5/NoCM
  (CMBranch/Localize.lean: KernelFieldExistsNC at fibres without CM).
- L563-577: Milne Part I Thm 2.8-2.9: rational Hodge endomorphisms = algebraic quasi-endomorphisms over Qbar; centralizer of
  J in B (x) R is Q or imaginary quadratic k; End^0(A_Qbar) = B or M_2(k).
- L582-586: End^0(A_Qbar) = M_2(k); all defined over L (A8); multiples of matrix units give E/L with CM and an
  L-isogeny E^2 -> A.
- Pieces (proposed, not formalized as separate Props, to keep the GLUE count): (i) A8 at a CM fibre (L-model with all
  geometric endomorphisms defined, [L:Q] <= D); (ii) End^0 = M_2(k) at a fibre with a non-integral endomorphism commuting
  with the QM (L567-577); (iii) the idempotent/image construction E = image of e_11 (needs images of endomorphisms as
  abelian varieties: Hom.image recipes in the tree) and the isogeny E x E -> A, (x,y) |-> e_11-part + e_21-part;
  (iv) End(E_Lbar) is an order of k (End^0(E) = e_11 M_2(k) e_11 = k, End(E) a finitely generated subring).

# h-a9c9-fix report

Applied the review `docs/research/rv-h-a9c9.md` (§§1.4, 2.4, 3, 4) to H's trust statement.

## Changes

1. `docs/research/h-trust.md`
   - Header and sources: rv-h-a9c9 added. New mark **AUDIT-READ** (the upstream
     theorem-application audit reports reading the page scan; a model's reading only).
   - **A9**: R-A9-1 (Riemann + GAGA/Chow; Mumford 1970 §§1-3 with Serre's GAGA, or Milne 1986 §1,
     replacing the course notes, whose p. 14 is AUDIT-READ; the `milne-av` bibliography entry
     names only Thm 12.1(a), so the in-text locator Thms 2.8-2.9 is to be kept). R-A9-2 (the
     descent fact: fixed by Aut(C/Qbar) ⇒ defined over Qbar, or the rigidity bijection, Conrad
     2006 §3). Centralizer step noted as VERIFIED by rv-h-a9c9. Status [M], now two model reviews.
   - **C9**: R-C9-1, the substantive one: the Euler-factor inference replaced by the K_f-linear
     Eichler–Shimura relation (V_l(A_f) free of rank 2 over K_f ⊗ Q_l, tr Frob_p = a_p; Shimura
     1971 §7 and Thm 7.9, Ribet 1977, Diamond–Im §12.5, Diamond–Shurman Thm 8.7.2), then
     Chebotarev, Brauer–Nesbitt and Faltings' semisimplicity. The text gives the Klein-four
     counterexample to the bare inference and the Hodge–Tate check that the side is right.
     R-C9-2: newness is Galois-stable (Shimura 1971 Thm 3.52 + strong multiplicity one);
     conductor invariance under duality (Corps locaux VI §2, Deligne 1973 §8). R-C9-3: "primitive
     newform" = Li's normalized newform, not twist-minimal. Shimura 1973 Thm 1: hypothesis met
     for the conjugate span in any form (Hecke, Aut(C), Fricke); Fricke form AUDIT-READ; not
     needed on the K_f-linear route. Status [R], application [M], now two model reviews.
   - §2.1: all three N5-only passages (A9, C3, C9) have two model reviews, so with C8 every
     passage new in the 11/5 text does; §2.2 note; §2.4 `milne-av` row (both locators,
     bibliography fix); §2.5: AUDIT-READ paragraph (sources checked in
     `docs/theorem-application-audit/evidence/`), item 4 (Shimura 1973) no longer decisive,
     item 9 adds the A9/C9 locators (UNVERIFIED); §2.7 item (vii) closed; Summary, [M]
     definition, route table; §3 drafts; §4; changelog entry "Task h-a9c9-fix".
2. `ZInQKernel/Hypotheses/Height.lean`, module docstring only: the review count of the A9/C9
   passages (rv-h-trust and rv-h-a9c9), Eichler–Shimura (Shimura 1971) among the newform
   suppliers, GAGA with Mumford. Lines ≤ 100 characters. `HeightMin.lean` unchanged (it states
   no review counts or C9 suppliers).
3. `KERNEL_PLAN.md`, H row: "the other two only in rv-h-trust" → rv-h-trust and rv-h-a9c9;
   Eichler–Shimura (Shimura 1971) added to the newform suppliers.

## Build

`lake build ZInQKernel`: success (9919 jobs). `lake env lean scripts/print_axioms.lean`: 59
entries, each exactly [propext, Classical.choice, Quot.sound]. `git diff` on `ZInQKernel/`:
only module-docstring lines of `Hypotheses/Height.lean` changed.

## Left / suggestions

- Statuses unchanged (A9 [M], citation [P] until the swap upstream; C9 [R] / application [M]).
  Both are still model reviews only, not human refereeing.
- Locator checks still to do: Shimura 1971 Thm 7.9 and §7 (the route now used), and Shimura
  1973 p. 526 and Li 1975 p. 296 (AUDIT-READ, optional now). The remaining A9/C9 locators are
  UNVERIFIED.
- Changelog entries of earlier tasks still say "rv-h-trust only" for these passages; left as
  history.

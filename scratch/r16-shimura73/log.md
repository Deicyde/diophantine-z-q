# r16-shimura73 results log

## Setup (06:15)
- Base bf691da22 (leaf-fold33b, top sixContactMin_of_open67, TailZ74). VERIFIED (git log).
- r16CoreY is no longer a top field: it is filled at OpenResearchLeaves41CF -> 40CF (TailZ74.lean:802) by
  `AfTateLam.r16CoreY_of_ds965 n.heckeJ1DS n.afShimura n.afCharpolyDS965 n.igusaGL2DS mumfordTorsionAlgClosed_proof`;
  top fields feeding it: heckeJ1DS, afShimura, afCharpolyDS965, igusaGL2DSGalSome (TailZ74.lean:1355
  `igusaGL2DS := igusaGL2DS_of_igusaGL2DSGalSome n.igusaGL2DSGalSome`). VERIFIED (grep).
- None of the four is read anywhere else in ZInQKernel/OneProof/ (grep of `.heckeJ1DS` etc. outside pass-through
  lines). dsThm965Printed is read by panBerger_of_printedPV (TailZ74.lean:709): it stays. VERIFIED (grep).
- r16CoreY is read only by `R16Split.r16_of_printed` (field r16). VERIFIED (grep).
- Manuscript L768-773 read (VERIFIED): Li p. 296 before Lemma 6 -> span of coefficient conjugates Fricke-stable;
  Shimura Thm 1 quotient + Euler-factor identity -> r_5 constituent of Tate module of A_f. Bibliography L11050-11057.
- locators.md row R16 (VERIFIED, read): Shimura 1973 Thm 1 pp. 526-527 gives the Q-rational quotient, coefficient
  field action, dimension; "final total Euler-factor clause has an extra Gamma0/Fricke-stability condition";
  "Individual-embedding rank-two Tate realization and Frobenius-Hecke relation must still be supplied; total
  characteristic-polynomial divisibility alone is insufficient."

## Consumers of r16CoreY (step 3) — VERIFIED (read TailA.lean:3404-3453, R16Used.lean:7-13, R16Split.lean:549-576)
- r16CoreY -> R16_EichlerShimuraJ1' (R16Split.r16_of_printed; dim used only to derive rank two via rank_two_of_dim)
  -> one consumer: G0ModNewform.g13 -> commonConstituent_of_attached (TailA.lean:3404), at l = 5 only,
  one embedding emb = embOf 5 iotaC iota5, and it uses: surjectivity of pi, the rank-two clause at emb, and the
  trace clause `tr(Frob_p | emb-component) = emb(a_p)` at every p not dividing 5N outside a finite set S (fed to
  c9_core: Brauer-Nesbitt + Frobenius density). Not used: determinant clause, dim (except to get rank two),
  [K_f:Q] < oo (bound, unused), other l, other embeddings.
- So the Lean consumer needs: a per-embedding trace identity at l = 5 for the embedding attached to iota5 at
  cofinitely many p — exactly the clause the known gap leaves unproved. The manuscript (L774-794) uses the same
  thing ("equality with its modular trace at five", for all p outside T u {3,5} and the level) plus the analogous
  modular Tate representation at 3 (r_3 identified by Chebotarev). Lean asks more than the manuscript only in:
  determinant (in R16CoreY, unused), all l (R16CoreY quantifies over every l), dim A = [K_f:Q] (used for rank two).

## Lean (VERIFIED, compiled)
- ZInQKernel/Contrib/OneProof/R16ShimuraLi.lean: compiles clean (fixes: bound `ι` reserved token -> `io`;
  `open Polynomial` removed for X/coeff ambiguity). Leaves LiFrickePrinted, ShimuraThm1Printed; steps ConjNewform,
  ShimuraTotalToComponents (known issue). Proved: frickeStable_of_li, r16CoreYTotal_of_shimura_li,
  r16CoreY_of_total, r16CoreY_of_shimura_li. Axioms standard.
- lake build R16ShimuraLi + Main + Discharges: success, frozenTarget standard axioms.
- FoldCheck.lean (step-1 module TailZ75R16 + step-2 autofold dry-run module): compiles; open68, open69 standard.
- #discharges: 36 open, 19 discharge one, none by R16ShimuraLi (r16CoreY is not a top field).
- autofold dry run on /tmp/r16af (step 1 applied): strict 4/24 on 28 -> 4/27 on 31 (net vs base 4/27 on 31: unchanged).
## Finding (known issue): Shimura Euler identity (total charpoly) does not give the per-embedding trace that the
  only Lean consumer (g13, l = 5, one embedding) needs. Stopped there; ShimuraTotalToComponents named, not proved.

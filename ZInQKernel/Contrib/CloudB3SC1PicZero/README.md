# Pic⁰ identity-component contribution

This directory supports the `picZeroAbVar` contribution. The unchanged target is `T09Pic.PicZeroAbVar`, declared in
`ZInQKernel/OneProof/H/TailZ24.lean`. No existing module, statement, assembly or dependency pin is changed.

Files:

* `Leaves.lean`: three printed statements of Kleiman, each stated over a field `K` (`S = Spec K`) over the
  vendored fppf Picard sheaf `picardFunctor`, its representing objects, its group law `picardFunctorCommGrpObj` and
  `T09Pic.identityComponent`.
* `Glue.lean`: the proof of `T09Pic.PicZeroAbVar` from them (`CloudB3SC1PicZero.picZeroAbVar_of_kleiman`).
* `../OneProof/PicZeroAbVar.lean`: the exported theorem

  ```lean
  theorem CloudB3SC1PicZero.picZeroAbVar_proof (h948 : KleimanThm948Field) (h951 : KleimanLem951)
      (h9524 : KleimanRmk9524Field) : T09Pic.PicZeroAbVar
  ```

## Source

Steven L. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA Explained*, AMS
Mathematical Surveys and Monographs 123 (2005), Chapter 9. The author's preprint, arXiv `math/0504020v1`, numbers
the statements without the chapter prefix 9. It was read by AI agents; no human reading is recorded, and no
repository source-review flag is changed. The book page numbers are unverified.

| leaf | book locator | arXiv v1 locator | what is kept |
| --- | --- | --- | --- |
| `KleimanThm948Field` | Thm 9.4.8 (Main), part (1) | Thm 4.8, p. 27 | for `X/K` projective, flat, with integral geometric fibres, the Picard scheme is locally of finite type |
| `KleimanLem951` | Lemma 9.5.1 (3) (also SGA 3 VI_A 2.4) | Lemma 5.1 (3), pp. 36-37 | the identity component of a group scheme locally of finite type over a field is an open, geometrically irreducible subgroup |
| `KleimanRmk9524Field` | Remark 9.5.24 | Remark 5.24, pp. 50-51 | for a projective abelian scheme over a Noetherian base, `Pic⁰` is a projective abelian scheme; over a field, `Pic⁰` is smooth and proper |

Each leaf is the printed statement at `S = Spec K` or a consequence of it (hypotheses added, conclusion clauses
dropped), never stronger. Projectivity is kept as an explicit hypothesis (a closed immersion into `ℙ^N_K` over `K`).
In `KleimanRmk9524Field` the relative dimension is a natural number `g` with `dim X = g`, and the group law is assumed
commutative; for an abelian variety both hold (`PkgI3.AbVar.dim_finite`, and the derived `IsCommMonObj` instance).
Remark 9.5.24 is printed as a Remark (with its argument), not as a numbered theorem.

## Credits and notices

The open-subgroup construction and the body of `picZeroAbVar_of_kleiman` are adapted from this project's
`PicDictionary` source at revision `4e95795b509f1bf8e381a405b04b836f1b59885f` (`PicDict.picZeroAbVar_of_leaves`);
only that material is reused. The fppf Picard sheaf, its group law and the projective immersion of a group
variety are the vendored frenzymath/Jacobian-Challenge files (commit c4254cce, Apache-2.0; LICENSE and NOTICE in
`ZInQKernel/Contrib/CloudW07JacobiansCurves/`). The finiteness of the dimension of an abelian variety is
`PkgI3.AbVar.dim_finite` (`ZInQKernel/Contrib/AbVarBC/Dim.lean`).

## Validation

On Lean 4.35.0 and the unchanged Mathlib pin, at fork main `0caafe66`: the three new modules compile, the exported
theorem has exactly the type above, `#print axioms` gives `[propext, Classical.choice, Quot.sound]`, and the
prescribed `#discharges` reports

```
DISCHARGES [OpenAddedLeaves17.picZeroAbVar] by CloudB3SC1PicZero.picZeroAbVar_proof
  still assumes: [CloudB3SC1PicZero.KleimanThm948Field,
 CloudB3SC1PicZero.KleimanLem951,
 CloudB3SC1PicZero.KleimanRmk9524Field]
  axioms: [propext, Classical.choice, Quot.sound]
```

An `autofold.py --dry-run` (no fold written) reports `strict count: 34/11 on 45 -> 37/10 on 47; strictest 34/11 ->
37/10`, with the three leaves flagged unread. The full compiler and `#discharges` output is in a private evidence
bundle available to the maintainer. Independent review and the fold are not asserted here.

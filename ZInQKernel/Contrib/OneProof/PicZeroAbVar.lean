import ZInQKernel.Contrib.CloudB3SC1PicZero.Glue

/-! # `picZeroAbVar`: the identity component of `Pic_{A/K}` is an abelian variety

Reduces the open hypothesis `T09Pic.PicZeroAbVar` (field `picZeroAbVar`) to three printed statements of
Kleiman, *The Picard scheme* (FGA Explained, 2005, Ch. 9), stated over a field in
`ZInQKernel/Contrib/CloudB3SC1PicZero/Leaves.lean`:
* `KleimanThm948Field` (Thm 9.4.8 (1): the Picard scheme exists and is locally of finite type),
* `KleimanLem951` (Lemma 9.5.1 (3): the identity component of a group scheme locally of finite type over a field
  is an open, geometrically irreducible subgroup),
* `KleimanRmk9524Field` (Remark 9.5.24: for a projective abelian scheme, `Pic⁰` is an abelian scheme; over a field,
  `Pic⁰_{X/K}` is smooth and proper).
The glue is in `ZInQKernel/Contrib/CloudB3SC1PicZero/Glue.lean`. -/

namespace CloudB3SC1PicZero

theorem picZeroAbVar_proof (h948 : KleimanThm948Field) (h951 : KleimanLem951)
    (h9524 : KleimanRmk9524Field) : T09Pic.PicZeroAbVar :=
  picZeroAbVar_of_kleiman h948 h951 h9524

end CloudB3SC1PicZero

# Exact plain-algebra notation

`quartic250-decimal.txt` is the expanded polynomial expression alone, encoded
in ASCII, equivalently UTF-8 without a byte-order mark. It has no whitespace,
line break or final newline, and is exactly 85,737 bytes.

- Variables `x1` through `x250` use the manuscript's coordinate order. `x1` is
  the input.
- Terms are sorted lexicographically by their expanded, nondecreasing tuples
  of variable indices. The constant term comes first.
- Coefficients are decimal integers with no leading zero or digit separator.
  Zero terms are absent. A coefficient of magnitude one is omitted on a
  nonconstant term; its sign remains where needed.
- `*` means multiplication. Repeated variables use `^2`, `^3` or `^4`, with
  exponent one omitted. Variables in each monomial have increasing indices.
- Negative terms start with `-`. Positive terms after the first start with
  `+`; a first positive term has no leading sign.
- There are no parentheses, equation sign, polynomial name, variable
  declaration, factored subexpressions or abbreviated large coefficients.

For example, this format writes an illustrative expression as
`17+x1^4-2*x1^2*x47+x2*x250`. Appending a final newline would give 85,738 bytes
for the actual polynomial and would no longer be the specified file.

`verify.py` independently serializes the JSON table, parses that expression
back, compares all 3,362 coefficients and monomials, and requires exact equality
with the committed text. The text's SHA-256 is
`71cb153fdeb7ba6084850ecb5fab596249379c270bc97add9de64c82e7150f8f`.

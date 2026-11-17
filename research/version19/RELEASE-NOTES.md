# Version 19: 195 variables and an explicit 250-variable polynomial

Version 19 incorporates José Brox's 195-variable reduction of the retained
196-variable construction, and Gemini Carbon's explicit 250-variable
construction built from Brox's additive-detector framework. The manuscript
contains the arithmetic argument, both directions of the rational-solution
correspondences, complete coordinate transformations and both quadratic tables.

The 195-variable table has 175 rows and 2,956 nonzero coordinate monomials. Its
coefficients are specified as polynomials in `C = 149^BB(2^1000)`, and have
absolute value below `BB(2^2000)` under the stated machine convention. It retains
the Version 18 arithmetic and Busy Beaver inputs. No Busy Beaver value is
computed.

The explicit construction uses `N = 10220` and a six-coordinate squaring
ladder. Its 222 rows yield a quartic in 250 variables with 3,362 nonzero
monomials and coefficient magnitudes below `2^6483`. Written in the documented
plain-algebra format with decimal coefficients, it is exactly 85,737 bytes.
The larger JSON file is a separate representation of the same polynomial.

The new exposition supplies the formal-subgroup definition, the five-contact
radical and its comparison with the retained height input, the monotone
substitution, the reflected domains and radical supports, and distinct symbols
for coordinate constants and exponent weights. It preserves the original
theorem and all previously released manuscripts. The 263-variable scratch
construction is not part of this release.

The numerical construction data are credited to Brox and Carbon as described
at their points of use. Independent finite checks cover the printed formulas
and coefficient statistics. The protected Protocol B review attached to the
release PR records the reviewers' decisions on the full incorporation and
source/PDF pair; the finite checks alone do not provide that acceptance.

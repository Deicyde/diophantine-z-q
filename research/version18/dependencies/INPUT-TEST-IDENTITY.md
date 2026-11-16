# The shifted intermediate input square

The stored square in rows 10 and 11 of both printed tables is an intermediate value, not the fourth-power input delivered to the detector. Write `rho^2=2`, `a=Y28-51Y44-2501`, `b=Y29` and `I=a-3+rho*b=L_1-(51X^2+2504)`. The input-square row gives `Y44=X^2`; rows 10 and 11 give

```text
Y61 = a^2+2b^2,
Y62 = ab.
I^2 = (Y61-6a+9) + rho*(2Y62-6b).
```

Squaring once more gives the two components

```text
U = (Y61-6a+9)^2 + 2(2Y62-6b)^2,
V = 2(Y61-6a+9)(2Y62-6b).
```

Their full expansions are exactly the right-hand definitions in rows 66 and 67 of the 198 table, with outputs `Y118,Y119`, and rows 64 and 65 of the 196 table, with outputs `Y116,Y117`. For example, the real expansion contains `-12Y28Y61+612Y44Y61+30030Y61` and the constant `225450225`; those terms implement the shift by three. The 198 detector rows 72 and 73 consume these corrected outputs with weight `q^5` after division by the inverse-weight fourth power. The 196 detector equations are related by the separately checked nonzero row and coordinate rescalings.

Thus the input test is `I=L_1-beta`, with `beta=51X^2+2504`, as used in the soundness and completeness proofs. The intermediate square `(I+3)^2` does not change the input label to `beta-3`. The retained component-typing subsection also explains this intermediate shift.

`scripts/check_v18_table_binding.py` parses these printed rows and proves the two identities coefficient by coefficient using integer polynomial arithmetic. It also requires the complete independently checked 198 and 196 components to occur in the current manuscript. The associated tests reject a changed fourth-power constant, a damaged correction term, a changed receiving component and a duplicate component. These finite checks settle this identity; they do not substitute for the remaining arithmetic proof review.

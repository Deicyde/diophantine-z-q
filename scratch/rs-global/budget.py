"""Variable budget of the 11/5 polynomial by role.

All template and recipe counts are copied from diophantine_zq.tex (template table,
lines 6739-6772) and ZInQ.Syntax.witness_count_arith (ZInQKernel/Syntax/Recipes/Arith.lean).
"""
MUL, NAT, ADD, ALPHA = 35134, 140604, 6, 1      # multiply, natural, raw_add, alpha/power(1)
SLOPE, TESTGROUP, POLE = 1298, 162, 11
HEIGHTCERT = 35106
TOTAL = 292890231904

# power_value recipe: 3 + 79(5+NAT) + 3(5+1) + 196(5+ADD) + 190(5+MUL)
power_value = 3 + 79*(5+NAT) + 3*(5+1) + 196*(5+ADD) + 190*(5+MUL)
assert power_value == 17786698
# precision recipe
precision = 3 + 5*140604 + 54051*(5+NAT) + 4*(5+1) + 125327*(5+ADD) + 98382*(5+MUL) + 15845*(5+power_value)
assert precision == 292889492836

n_nat = 5 + 54051 + 15845*79          # natural calls (5 signed_encode inputs counted as natural-size blocks)
n_mul_direct = 98382 + 15845*190
n_mul_in_nat = 4*(54051 + 15845*79)
n_mul = n_mul_direct + n_mul_in_nat
print("multiplication instances: direct %d, inside natural %d, total %d" % (n_mul_direct, n_mul_in_nat, n_mul))
w_mul = n_mul*MUL
print("witnesses inside multiplication templates: %d = %.4f of %d" % (w_mul, w_mul/TOTAL, TOTAL))
w_slopes = n_mul*27*SLOPE
w_groups = n_mul*27*6*TESTGROUP
print("  of which slope predicates: %.4f; test groups: %.4f; pole instances: %.6f" %
      (w_slopes/TOTAL, w_groups/TOTAL, n_mul*27*POLE/TOTAL))
# value relation proper (main recipe minus close/precision)
value_test = 35282
print("value test witnesses: %d (%.2e of total)" % (value_test, value_test/TOTAL))
print("cost of one extra witness in the multiplication template: %d variables" % n_mul)
print("cost of one extra test group per slope: %d variables" % (n_mul*27*TESTGROUP))
print("saving from two slopes per quantity (9 slopes fewer): %d variables" % (n_mul*9*SLOPE))
print("room for extra test groups after that saving: %d per slope (18 slopes)" %
      ((n_mul*9*SLOPE)//(n_mul*18*TESTGROUP)))

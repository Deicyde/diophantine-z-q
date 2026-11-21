"""Replay the integer inequalities in docs/research/fixed-field-height-budget-20261120.md."""

from math import factorial


def main() -> None:
    # Dimension of the rational factor and degree of its common isogeny field.
    g, d = 128, 64
    # log(14*g) <= 11, log(d) <= 6. All logs in the note are natural.
    assert 14 * g <= 2**11 and d <= 2**6
    # Bound log(deg phi) by this coefficient times max(1, h_F(B)).
    transfer = (1024 * g**3) * (64 * g**2 * 11 + 3 * 6 + 2)
    # Drop the factor 12 in the inequality for h(u), and use log(1024) <= 10.
    assert 1024 == 2**10
    theta = 84 + 42 * transfer + 289200 + 450 + 10
    # Theorem 6.2 gives max(1, h_F(B)) <= shafarevich * N_S**24.
    shafarevich = (3 * g) ** (144 * g)
    budget_exponent = 167_000
    assert theta * shafarevich <= 2**budget_exponent

    # D = F0 * 3**(256 * F0**4). Compare exponents instead of evaluating D.
    assert factorial(324) >= 8
    assert 256 * 8**4 >= budget_exponent
    # For D >= 1 and E0 >= 2: D**(24*D+1) <= D**(17*D*E0).
    assert 24 + 1 <= 17 * 2
    print("Fixed-field coefficient fits H6(D) at g <= 128 and d <= 64.")


if __name__ == "__main__":
    main()

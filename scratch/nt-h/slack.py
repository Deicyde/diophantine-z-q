"""Slack of the multiplication use (rs-height §2.3), in doubly-logarithmic units.
Known (VERIFIED in rs-height from Lean): log2 A_ht < D^7 with log2 D < 2^9010, and the target needs
(T+1)^2048 < 2^^7 = 2^(2^(2^65536)), i.e. log2 log2 (T+1) < 2^65536 - 11.
With exponent e < k = 25: N < (48A)^m, m = k/(2(k-e)); take T = (48A)^(ceil(m)+1).
log2 log2 T <= log2(ceil(m)+1) + log2(log2 A + 6) < log2(ceil(m)+1) + 7*2^9010 + 1.
We report, as exact integers, the largest log2 m and the largest x = log2 log2 A / log2 D
admissible.  All quantities are exponents of 2, so Python integers suffice."""
LL_TARGET = 2**65536 - 11          # bound on log2 log2 (T+1)
LOG2_D_MAX = 2**9010               # log2 D < 2^9010
# (a) exponent: with log2 A < 7*log2 D, need log2(m+1) + 7*2^9010 + 1 < LL_TARGET
log2_m_max = LL_TARGET - 7 * LOG2_D_MAX - 2
print("log2 m may be as large as 2^65536 - 7*2^9010 - 13; is it > 2^65535 ?", log2_m_max > 2**65535)
# so 25 - e may be as small as 25/(2m) with log2 m ~ 2^65535: e = 25 - 2^(-2^65535) is admissible
# (b) constant at e = 24 (m = 12.5, T = (48A)^13 as in Lean): log2 log2 A < LL_TARGET - log2(13) - 1
# write log2 A = D^x; log2 log2 A = x*log2 D < x*2^9010; need x*2^9010 < 2^65536 - 16
x_max_log2 = 65536 - 9010 - 1      # x < 2^(65536-9010-1) suffices since 2^(65535) < 2^65536 - 16
print("log2 A = D^x is admissible for x < 2^%d (rs-height quoted 2^56000)" % x_max_log2)
print("current x = 7; margin factor in x: 2^%d / 7" % x_max_log2)

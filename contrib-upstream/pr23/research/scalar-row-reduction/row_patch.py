"""Two source transformations contributed by the Opus exploration.

Apply to the final #17 builder, before compilation. Exact row identities,
private witness transports and unchanged consumers are checked separately.
"""


def once(source, old, new):
    if source.count(old) != 1:
        raise ValueError('Expected exactly one source fragment: '+old)
    return source.replace(old, new)


def transform(source):
    source = once(source,
        "rawFmul(Qp.x,Rp.j)),F,'totally_positive_xP_xU_plus_D');",
        "rawFmul(rawFmul(Qp.h,Qp.h),Rp.j)),F,'totally_positive_xP_xU_plus_D');")
    return once(source,
        """const rho=save('scalar.correctedR',scale(rr,42)),W2=rsq('scalar.W2',nw);
save('scalar.Bsemantic',mul(rho,W2));
pole('scalar',rho,scalar,false,mul(rho,W2));""",
        """const rho=save('scalar.correctedR',scale(rr,42));
const Tq=rquot('scalar.preparationT',scale(sq(nw),42),ri,'rInverse_nonzero_since_r_times_rInverse_is_one');
save('scalar.Bsemantic',Tq);
pole('scalar',rho,scalar,false,Tq);""")

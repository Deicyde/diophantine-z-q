"""Reuse the detector's already materialized t^3 to obtain delta^3 affinely."""


def transform(source):
    old = """let mixA=rsq('detector'+r+'.mixA',eDelta),
 mixB=rm('detector'+r+'.mixB',mixA,eDelta),
 mixC=rm('detector'+r+'.mixC',mixB,q1cube),
 mixD=rsq('detector'+r+'.mixD',mixC),
 q12=rquot('detector'+r+'.q12',sq(mixD),eDelta,'positive_inverse_R');"""
    new = """// Fmiddle = t^3 + cs[4]*t^2 + cs[3]*t + cs[2].
 // Thus both t^3 and (98*t-1)^3 are affine in existing coordinates.
 const t3=sub(middle,add(scale(t2,cs[4]),scale(t,cs[3]),term(cs[2])));
 const delta3=save('detector'+r+'.deltaCubed',add(scale(t3,98**3),scale(t2,-3*98**2),scale(t,3*98),C(-1)));
 let e3=rm('detector'+r+'.eCubed',q1cube,delta3),
 e6=rsq('detector'+r+'.eSixth',e3),
 e12=rsq('detector'+r+'.eTwelfth',e6),
 q12=rquot('detector'+r+'.q12',sq(e12),eDelta,'positive_inverse_R');"""
    if source.count(old) != 1:
        raise ValueError('Unexpected detector weight circuit')
    return source.replace(old, new)

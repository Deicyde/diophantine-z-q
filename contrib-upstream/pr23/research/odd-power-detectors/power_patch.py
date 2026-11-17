"""Uniform odd powers of q1; apply to the actual order46 parent builder."""


def transform(source):
    old = """let e3=rm('detector'+r+'.eCubed',q1cube,delta3),
 e6=rsq('detector'+r+'.eSixth',e3),
 e12=rsq('detector'+r+'.eTwelfth',e6),
 q12=rquot('detector'+r+'.q12',sq(e12),eDelta,'positive_inverse_R');"""
    new = """// Uniform weights q_m=q1^(2m-1), with one-place input D/delta^(2m-1).
 let q1p6=rsq('detector'+r+'.q1Sixth',q1cube),
 q1p12=rsq('detector'+r+'.q1Twelfth',q1p6),
 q12=rquot('detector'+r+'.q12',sq(q1p12),q1,'positive_order_one_weight');"""
    assert source.count(old)==1
    result=source.replace(old,new)
    comments={
      '// R=1/E, q1=e/delta, q12=e^23/delta, q46=e^91/delta^3; E=q1*delta^2.':
      '// R=1/E, q1=e/delta, q12=q1^23, q46=q1^91; E=q1*delta^2.',
      '// One-place inputs: D/delta^m for low tests; D/delta^47 for high order46.':
      '// One-place inputs: D/delta^(2m-1), for m=1,12,46.',
      '// Low q_m=e^(2m-1)/delta; high q46=e^91/delta^3. E=1/R; e is not stored.':
      '// Every weight q_m=(e/delta)^(2m-1); E=1/R; e is not stored.',
    }
    for a,b in comments.items():
        assert result.count(a)==1
        result=result.replace(a,b)
    return result

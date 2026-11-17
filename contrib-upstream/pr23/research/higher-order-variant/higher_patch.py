"""Order50 detector and order47 scalar alternative above uniform odd powers."""
import re


def once(s,a,b):
    if s.count(a)!=1:raise ValueError('Expected one source fragment: '+a)
    return s.replace(a,b)


def transform(source):
    source=once(source,
        """let q1p6=rsq('detector'+r+'.q1Sixth',q1cube),
 q1p12=rsq('detector'+r+'.q1Twelfth',q1p6),
 q12=rquot('detector'+r+'.q12',sq(q1p12),q1,'positive_order_one_weight');""",
        """let q1p4=rsq('detector'+r+'.q1FourthForWeights',q1square),
 q1p8=rsq('detector'+r+'.q1Eighth',q1p4),
 qInv=rquot('detector'+r+'.q1InverseSeventh',q1,q1p8,'positive_order_one_weight'),
 q12=rquot('detector'+r+'.q12',sq(q1p8),qInv,'positive_order_one_weight');""")
    source=once(source,
        "let q46=rquot('detector'+r+'.q46',sq(mixedHigh),q1,'positive_order_one_weight');",
        "let q46=rquot('detector'+r+'.q46',sq(mixedHigh),qInv,'positive_order_one_weight');")
    source=once(source,'q46=q1^91','q46=q1^99')
    source=re.sub(r'\b46\b','50',source).replace('q46','q50').replace('E46','E50')
    source=once(source,
        "      ri15=rquot('scalar.rInverse15',sq(ri7),rr,'positive_scalar_contact_product');",
        """      ri15=rquot('scalar.rInverse15',sq(ri7),rr,'positive_scalar_contact_product'),
      ri31=rquot('scalar.rInverse31',sq(ri15),rr,'positive_scalar_contact_product');""")
    source=once(source,"rquot('scalar.ratioProxyLeaf',mul(ratioProxyReal,ri15),rr,",
                "rquot('scalar.ratioProxyLeaf',mul(ratioProxyReal,ri31),rr,")
    source=once(source,'// Three Laurent steps suffice: inverse weights on the right preserve scalar order 28.',
                '// Four Laurent steps; the proxy leaf is Tproxy/r^32 and gives scalar order47.')
    source=once(source,'// New p=W*p_old, q=W*q_old, U=U_old/W; W>=1 since r>0.',
                '// New p=W*p_old, q=W*q_old, U=U_old/W; W=N>0 on the retained domain.')
    return once(source,"value:'3^2010'","value:'3^1512'")

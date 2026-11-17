"""Author experiment: order-31 scalar chain; mathematical review pending."""


def transform(source, *, exponent=2130):
    start = source.index("let leaves=[save('scalar.leaf0'")
    end = source.index("let nw=save('scalar.W'", start)
    replacement = """// Keep the four formal-place tests, placing the scalar proxy deepest.
function normTree(name,a,b,weight=rr){return assign(name,add(sq(a),mul(weight,rsq(name+'.rightSquare',b))));}
const chain3=normTree('scalar.chain3',PS.f[1],directLeaf[0],ri15);
const chain2=normTree('scalar.chain2',PS.f[0],chain3,ri15);
const chain1=normTree('scalar.chain1',PU[0].f[1],chain2,ri15);
const nCore=rquot('scalar.N',add(sq(PU[0].f[0]),mul(ri15,rsq('scalar.N.rightSquare',chain1))),rr,'positive_scalar_contact_product');
"""
    result = source[:start] + replacement + source[end:]
    assert "value:'3^2364'" in result
    result = result.replace("value:'3^2364'", f"value:'3^{exponent}'")
    return result

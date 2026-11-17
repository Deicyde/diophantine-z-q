"""Specialize scalar preparation after the order-31 chain; acceptance pending."""


def transform(source):
    substitutions = [
        (' let T=b;', " let T=preparationBase ? assign(name+'.preparationT',preparationBase) : b;"),
        ("let nw=save('scalar.W',add(one,nCore));", "let nw=save('scalar.W',nCore);"),
        ("pole('scalar',rho,scalar,true,mul(rho,W2));", "pole('scalar',rho,scalar,false,mul(rho,W2));"),
    ]
    for old, new in substitutions:
        if source.count(old) != 1:
            raise ValueError('Unexpected scalar source: ' + old)
        source = source.replace(old, new, 1)
    return source

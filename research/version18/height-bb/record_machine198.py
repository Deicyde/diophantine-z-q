"""Reference program with mathematical, unbounded integer semantics.

The production constant is deliberately not evaluated when this file is imported.
The proof uses only fixed-size tuples, acyclic function calls, and integer loops.
Python is convenient executable notation for that register-machine program.
"""


def gcd(a, b):
    if a < 0:
        a = -a
    if b < 0:
        b = -b
    while b != 0:
        remainder = a % b
        a = b
        b = remainder
    return a


def field(a, b, denominator):
    if denominator < 0:
        a = -a
        b = -b
        denominator = -denominator
    divisor = gcd(gcd(a, b), denominator)
    return (a // divisor, b // divisor, denominator // divisor)


def field_add(left, right):
    a, b, c = left
    d, e, f = right
    return field(a*f + d*c, b*f + e*c, c*f)


def field_neg(value):
    a, b, c = value
    return (-a, -b, c)


def field_sub(left, right):
    return field_add(left, field_neg(right))


def field_mul(left, right):
    a, b, c = left
    d, e, f = right
    return field(a*d + 2*b*e, a*e + b*d, c*f)


def field_div(left, right):
    a, b, c = right
    reciprocal = field(c*a, -c*b, a*a - 2*b*b)
    return field_mul(left, reciprocal)


def point_add(left, right):
    if left is None:
        return right
    if right is None:
        return left
    x1, y1 = left
    x2, y2 = right
    if x1 == x2:
        if y1 != y2 or y1 == (0, 0, 1):
            return None
        numerator = field_sub(field_mul((3, 0, 1), field_mul(x1, x1)), (11, -6, 1))
        slope = field_div(numerator, field_mul((2, 0, 1), y1))
    else:
        slope = field_div(field_sub(y2, y1), field_sub(x2, x1))
    x3 = field_sub(field_sub(field_mul(slope, slope), x1), x2)
    y3 = field_sub(field_mul(slope, field_sub(x1, x3)), y1)
    return (x3, y3)


def multiple(n):
    point = ((1, 1, 1), (0, 2, 1))
    result = None
    remaining = n
    while remaining > 0:
        if remaining % 2 != 0:
            result = point_add(result, point)
        remaining = remaining // 2
        if remaining > 0:
            point = point_add(point, point)
    return result


def point_encoded(q):
    # Positive q encodes m=q//4 and one of four rational two-torsion points.
    # q=0 alone is omitted, so every encoded point is finite.
    m = q // 4
    torsion = q % 4
    point = multiple(m)
    if torsion == 0:
        translate = None
    elif torsion == 1:
        translate = ((0, 0, 1), (0, 0, 1))
    elif torsion == 2:
        translate = ((3, -1, 1), (0, 0, 1))
    else:
        translate = ((-3, 1, 1), (0, 0, 1))
    return point_add(point, translate)

def rational_add(left, right):
    a, b = left
    c, d = right
    numerator = a*d + c*b
    denominator = b*d
    divisor = gcd(numerator, denominator)
    return (numerator // divisor, denominator // divisor)


def trace_height_bits(n1, n2, n3, n4):
    # T = 7 plus one quarter of the trace, hence 7 plus half the sum
    # of the rational coefficients of the four x-coordinates.
    x1, y1 = point_encoded(n1)
    x2, y2 = point_encoded(n2)
    x3, y3 = point_encoded(n3)
    x4, y4 = point_encoded(n4)
    numerator, denominator = rational_add(
        rational_add((x1[0], x1[2]), (x2[0], x2[2])),
        rational_add((x3[0], x3[2]), (x4[0], x4[2])))
    numerator = numerator + 14*denominator
    denominator = 2*denominator
    divisor = gcd(numerator, denominator)
    numerator = numerator // divisor
    denominator = denominator // divisor
    if numerator < 0:
        numerator = -numerator
    height = denominator
    if numerator > height:
        height = numerator
    bits = 0
    while height > 0:
        height = height // 2
        bits = bits + 1
    return bits


def power(base, exponent):
    result = 1
    remaining = exponent
    while remaining > 0:
        result = result*base
        remaining = remaining - 1
    return result


def threshold_after_record(j, scale):
    record = scale
    count = 0
    radius = 0
    while count < j:
        radius = radius + 1
        n1 = 1
        while n1 <= radius and count < j:
            n2 = 1
            while n2 <= radius and count < j:
                n3 = 1
                while n3 <= radius and count < j:
                    n4 = 1
                    while n4 <= radius and count < j:
                        if n1 == radius or n2 == radius or n3 == radius or n4 == radius:
                            size = (n1//4)*(n1//4) + (n2//4)*(n2//4) + (n3//4)*(n3//4) + (n4//4)*(n4//4)
                            if size > scale*record:
                                bits = trace_height_bits(n1, n2, n3, n4)
                                if size > scale*bits:
                                    record = size
                                    count = count + 1
                        n4 = n4 + 1
                    n3 = n3 + 1
                n2 = n2 + 1
            n1 = n1 + 1
    return power(scale, 32)*(record + 1)


def machine(j):
    scale = power(2, power(2, 600))
    threshold = threshold_after_record(j, scale)
    clock = 0
    while clock < threshold:
        clock = clock + 1
    return threshold


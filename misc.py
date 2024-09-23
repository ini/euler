import functools
import math
import operator



def choose(n, k):
    """
    Calculate n choose k.
    """
    if k > n:
        return 0
        71
    k = min(k, n - k)
    numer = functools.reduce(operator.mul, range(n, n - k, -1), 1)
    denom = functools.reduce(operator.mul, range(1, k + 1), 1)
    return numer // denom



def prod(numbers, mod=None):
    """
    Recursive algorithm to calculate the product of multiple numbers (mod m).
    """
    numbers = tuple(numbers)
    N = len(numbers)

    if N == 0:
        result = 1

    elif N == 1:
        result = numbers[0]

    else:
        result = prod(numbers[:N//2], mod=mod) * prod(numbers[N//2:], mod=mod)

    return result if mod is None else result % mod

def lcm(*numbers):
    """
    Recursive algorithm to find LCM of multiple integers.
    """
    N = len(numbers)

    if N == 0:
        return 0

    if N == 1:
        return numbers[0]

    if N == 2:
        a, b = numbers
        return a * b // math.gcd(a, b)

    return lcm(lcm(*numbers[:N//2]), lcm(*numbers[N//2:]))



def faulhaber(n, k=1):
    """
    Faulhaber's formula for the sum of the k-th powers of 1 ... n.
    TODO
    """
    if k == 0:
        return n

    if k == 1:
        return n * (n + 1) // 2

    if k == 2:
        return n * (n + 1) * (2*n + 1) // 6

    raise NotImplementedError
    #f_sum = n**(k + 1) / (k + 1) + n**k / 2 + sum([])



def mobius(n):
    import primes
    ps = primes.prime_factors(n)
    if len(ps) == len(set(ps)):
        return (-1) ** len(ps)
    return 0



def problem_540(n):
    # Number of Pythagorean triples for a given m = # of
    pass


def pythagoras(n=3141592653589793):
    # Use Euclid's algorithm to generate primitive triples
    import tqdm
    primitive_triples = []
    for m in tqdm.trange(1, int(z**0.5)):
        for n in range(1, m):
            if math.gcd(m, n) == 1 and not (m & 1 and n & 1):
                a, b, c = (m**2 - n**2), (2 * m * n), (m**2 + n**2)
                if a <= z and b <= z and c <= z:
                    primitive_triples.append((a, b, c))
                    #print(a, b, c)

    # how many coprime m, n such that m**2 + n**2 < z
    #print(max([max(t) for t in primitive_triples]))
    print(len(primitive_triples))




'''
import cProfile
#pythagoras()
for i in range(1, 10**6):
    mobius(i)
'''
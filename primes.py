import collections
import itertools
import math
import random

from functools import cache



### Primality Testing

def miller_rabin_test(n, r, d, a=2):
    """ 
    Single round of Miller-Rabin primality testing, where a = 2^r * d + 1, with d odd.
    """
    x = pow(a, d, n) # x = a^d mod n
    if x == 1 or x == n - 1: # if x = +/- 1 mod n, we pass
        return True

    for _ in range(r - 1):
        x = pow(x, 2, n) # x = x^2 mod n
        if x == n - 1: # if we get an x = - 1 mod n, we pass
            return True

    return False

@cache
def is_prime(n, k=20):
    """
    Miller-Rabin primality test with k rounds of testing.
    """
    if n in {2, 3}:
        return True
    elif n < 2:
        return False

    # Write n as 2^r * d + 1 with d odd (by factoring out powers of 2 from n − 1)
    r, d = 0, n - 1
    while not d & 1: # d is not odd
        d >>= 1 # divide by 2 (bit-shift right)
        r += 1

    # Perform k rounds of testing
    for a in range(2, k + 2):
        if not miller_rabin_test(n, r, d, a=2):
            return False

    return True



### Integer Factorization

def pollard_rho(n):
    """
    Pollard's rho factorization method. Returns an integer factor.
    """
    if not n & 1:
        return 2 # return factor of 2 if last bit is a 0 

    x, y, d = 2, 2, 1
    c = random.randint(1, n - 1)
    f = lambda x: (pow(x, 2, n) + c) % n # f(x) = (x^2 + c) mod n

    while d == 1:
        x, y = f(x), f(f(y))
        d = math.gcd(abs(x - y), n)
    
    return d

def brent(n):
    """
    Brent's factorization method. Returns an integer factor.
    See https://maths-people.anu.edu.au/~brent/pd/rpb051i.pdf.
    """
    c = random.randint(1, n - 1)
    f = lambda x: (pow(x, 2, n) + c) % n # f(x) = (x^2 + c) mod n
    y, m = random.randint(1, n - 1), random.randint(1, n - 1)
    r, q, G = 1, 1, 1

    while G == 1:
        x = y
        for _ in range(r):
            y = f(y)
        k = 0
        while (k < r and G == 1):
            ys = y
            for _ in range(min(m, r - k)):
                y = f(y)
                q = (q * abs(x - y)) % n
            G = math.gcd(q, n)
            k += m
        r *= 2

    if G == n:
        G = 1
        while G == 1:
            ys = f(ys)
            G = math.gcd(abs(x - ys), n)

    return G

@cache
def get_prime_factors(n, return_counts=False):
    """
    Gets a list of prime factors (nonunique).
    """
    if return_counts:
        return collections.Counter(get_prime_factors(n, return_counts=False))

    if n == 1:
        return []

    if is_prime(n):
        return [n]

    factor = brent(n)
    return get_prime_factors(factor) + get_prime_factors(n // factor)

def divisors(n):
    factors = get_prime_factors(n, return_counts=True)
    div = [1]

    for p, r in factors.items():
        div = [d * p**e for d in div for e in range(r + 1)]

    return sorted(div)



### Generating Primes

def sieve(n):
    """
    Uses the Sieve of Eratosthenes to generate list of all primes below n.
    """
    prime = bytearray([True]) * (n + 1)
    prime[0], prime[1] = False, False

    for i in range(2, int(n**0.5) + 1):
        if prime[i]:
            m = n//i - i + 1
            prime[i**2::i] = bytearray([False]) * m

    return list(itertools.compress(range(len(prime)), prime))







def totient(n):
    """
    Compute Euler's totient function φ(n) for an integer n.
    """
    prime_factors = get_prime_factors(n, return_counts=True)
    return math.prod(p**(k - 1) * (p - 1) for p, k in prime_factors.items())

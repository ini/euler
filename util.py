from __future__ import annotations

import bisect
import collections
import itertools
import random
import sys

from collections import Counter, defaultdict
from functools import cache, reduce
from heapq import heappop, heappush
from math import ceil, comb, gcd, isqrt, lcm, log, prod, sqrt
from numbers import Number
from typing import Callable, Hashable, Iterable, Generator, Sequence



### Primes

@cache
def is_prime(n: int) -> bool:
    """
    Test if a given integer n is prime.
    Uses a combination of trial division and the Miller-Rabin primality test.

    Parameters
    ----------
    n : int
        Integer to test for primality
    """
    if n == 2:
        return True
    elif n < 2:
        return False

    # Trial division over first few primes
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59):
        if n % p == 0:
            return n == p

    # Write n as 2^s * d + 1 with d odd (by factoring out powers of 2 from n − 1)
    d = n - 1
    s = (d & -d).bit_length() - 1  # count trailing zeros
    d >>= s
    # s, d = 0, n - 1
    # while d % 2 == 0:
    #     d //= 2
    #     s += 1

    # Use deterministic set of Miller-Rabin bases for small n
    # See https://miller-rabin.appspot.com
    if n < 341531:
        bases = (9345883071009581737,)
    elif n < 1050535501:
        bases = (336781006125, 9639812373923155)
    elif n < 350269456337:
        bases = (4230279247111683200, 14694767155120705706, 16641139526367750375)
    elif n < 55245642489451:
        bases = (2, 141889084524735, 1199124725622454117, 11096072698276303650)
    elif n < 7999252175582851:
        bases = (
            2,
            4130806001517,
            149795463772692060,
            186635894390467037,
            3967304179347715805,
        )
    elif n < 585226005592931977:
        bases = (
            2,
            123635709730000,
            9233062284813009,
            43835965440333360,
            761179012939631437,
            1263739024124850375,
        )
    elif n < 18446744073709551616: # 2^64
        bases = (2, 325, 9375, 28178, 450775, 9780504, 1795265022)
    else:
        bases = [random.randint(2, n - 2) for _ in range(20)]

    # Perform multiple rounds of Miller-Rabin testing
    for a in bases:
        if a % n == 0:
            return True
        if not _miller_rabin(n, s, d, a=a):
            return False

    return True

def primes(low: int = 2, high: int = None, num: int = None) -> Generator[int]:
    """
    Generate prime numbers in the range [low, high].
    Uses the sieve of Eratosthenes, with a segmented approach for large ranges.

    Parameters
    ----------
    low : int
        Lower bound for prime numbers
    high : int
        Upper bound for prime numbers
    num : int
        Maximum number of primes to generate (default is infinite)
    """
    DEFAULT_SIEVE_SIZE, MAX_SIEVE_SIZE = 1000, 10000000
    low, high, num = max(low, 2), high or float('inf'), num or float('inf')

    # Set initial sieve size
    # When `high` is given, sieve on range [low, high]
    # When `num` is given, sieve on range [low, low + n log(low)] containing ≈ n primes
    if high == num == float('inf'):
        sieve_size = DEFAULT_SIEVE_SIZE
    else:
        sieve_size = int(min(MAX_SIEVE_SIZE, high - low + 1, 1.01 * num * log(low)))

    # Generate initial prime
    if low <= 2 <= high and num > 0:
        yield 2
        num -= 1
    elif low >= high or num <= 0:
        return

    # Generate a list of small primes to use for the segmented sieve
    small_primes = list(_eratosthenes(max(2, isqrt(low + sieve_size))))

    # Generate additional primes
    while low <= high and num > 0:
        # Extend list of small primes if necessary
        while (p := small_primes[-1]) < isqrt(low + sieve_size):
            small_primes.extend(_segmented_eratosthenes(p + 1, p, small_primes))

        # Get new primes with segmented sieve
        new_primes = _segmented_eratosthenes(low, sieve_size, small_primes)
        if num < float('inf'):
            new_primes = tuple(itertools.islice(new_primes, num))
            num -= len(new_primes)

        # Yield new primes
        yield from new_primes

        # Update sieve range
        low += sieve_size
        sieve_size = min(2 * sieve_size, MAX_SIEVE_SIZE, high + 1 - low)

def count_primes(x: float, initial_primes: tuple[int, ...] = None) -> int:
    """
    Find the number of primes less than or equal to x.

    Parameters
    ----------
    x : float
        Upper bound for prime numbers
    initial_primes : tuple[int, ...]
        Initial primes to use for counting
    """
    if initial_primes and x < initial_primes[-1]:
        return bisect.bisect(initial_primes, x)
    else:
        return _meissel_lehmer(x, prime_list=initial_primes)

@cache
def prime_factors(n: int) -> tuple[int]:
    """
    Get all prime factors of n (with multiplicity).
    Uses Pollard's rho factorization method.

    Parameters
    ----------
    n : int
        Integer to factor
    """
    if n < 2:
        return ()
    elif is_prime(n):
        return (n,)

    factor = _pollard_rho(n)
    return prime_factors(factor) + prime_factors(n // factor)

def _miller_rabin(n: int, s: int, d: int, a: int = 2) -> bool:
    """ 
    Single round of Miller-Rabin primality testing,
    where n = 2^s * d + 1, with d odd.
    """
    x = pow(a, d, n) # x = a^d mod n
    if x == 1 or x == n - 1: # if x = ± 1 mod n, we pass
        return True

    for _ in range(s - 1):
        x = (x * x) % n # x <- x^2 mod n
        if x == n - 1: # if we get an x = -1 mod n, we pass
            return True

    return False

def _pollard_rho(n: int) -> int:
    """
    Pollard's rho factorization method. Returns an integer factor.
    """
    # Trial division over first few primes
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47):
        if n % p == 0:
            return p

    # Initialize variables
    x, y, d = 2, 2, 1
    c = random.randint(1, n - 1)
    f = lambda x: (x * x + c) % n # f(x) = (x^2 + c) mod n

    # Use Floyd's cycle-finding algorithm
    while d == 1:
        x, y = f(x), f(f(y))
        d = gcd(abs(x - y), n)

    return d

def _eratosthenes(N: int) -> Iterable[int]:
    """
    Sieve of Eratosthenes.
    Returns prime numbers in the range [2, N].
    """
    # Initialize sieve
    sieve = bytearray([True]) * (N + 1)
    sieve[0], sieve[1] = False, False

    # Mark multiples of 2, 3 and 5
    sieve[4::2] = bytearray([False]) * (N // 2 - 1)
    sieve[9::6] = bytearray([False]) * ((N - 9) // 6 + 1)
    sieve[25::10] = bytearray([False]) * ((N - 25) // 10 + 1)

    # Iterate over 6k ± 1
    wheel = (1, 5)
    for i in range(6, int(sqrt(N)) + 1, 6):
        for w in wheel:
            j = i + w
            if sieve[j]:
                sieve[j*j::2*j] = bytearray([False]) * ((N - j*j) // (2*j) + 1)

    return itertools.compress(range(N + 1), sieve)

def _segmented_eratosthenes(
    start: int,
    sieve_size: int,
    prime_list: list[int],
) -> Iterable[int]:
    """
    Segmented sieve of Eratosthenes.
    Returns prime numbers in the range [start, start + sieve_size).
    """
    assert not any(map(is_prime, range(prime_list[-1] + 1, isqrt(start + sieve_size))))

    # Initialize sieve segment
    sieve = bytearray([True]) * sieve_size

    # Mark even numbers as composite
    sieve[start%2::2] = bytearray([False]) * ((sieve_size - start%2 + 1) // 2)

    # Mark odd multiples of odd primes as composite
    for p in prime_list[1:]:
        step = 2*p
        offset = ((start + p + step - 1) // step) * step - p
        offset = max(p*p, offset) - start
        num_prime_multiples = ((sieve_size - offset - 1) // step + 1)
        sieve[offset::step] = bytearray([False]) * num_prime_multiples

    return itertools.compress(range(start, start + sieve_size), sieve)

def _meissel_lehmer(
    x: int,
    k: int = 15,
    c: float = 0.003,
    prime_list: tuple[int, ...] = None,
) -> int:
    """
    Lagarias-Miller-Odlyzko (LMO) extension of the Meissel-Lehmer algorithm.
    Returns the value of the prime counting function π(x), i.e. the number of
    primes less than or equal to x.

    See: https://www.ams.org/journals/mcom/1985-44-170/
    S0025-5718-1985-0777285-5/S0025-5718-1985-0777285-5.pdf
    """
    if x < 9:
        return [0, 0, 1, 2, 2, 3, 3, 4, 4][int(x)]

    # Set y = cx^(1/3) log^2(x) such that x^(1/3) <= y <= x^(2/5)
    y = int(c * iroot(x, 3) * (log(x) ** 2))
    y = min(max(y, iroot(x, 3)), iroot(x * x, 5))

    # Count primes up to y
    if not prime_list or y > prime_list[-1]:
        prime_list = tuple(primes(high=y))
        a = len(prime_list)
    else:
        a = bisect.bisect(prime_list, y)

    # Set other variables
    k = min(k, a)
    sqrt_x = isqrt(x)

    # Compute P2(x, a) from the LMO algorithm
    # Find the sum of pi(x // p) for all primes in the interval (y, x/y]
    limit = x // y
    if prime_list[-1] >= limit:
        # If we already have all primes in the interval,
        # directly compute pi(n) for n = 1 ... x/y
        sieve = bytearray(limit + 1)
        for p in prime_list:
            if p > limit:
                break
            sieve[p] = True

        pi = list(itertools.accumulate(sieve))
        P2 = comb(a, 2) - comb(pi[sqrt_x], 2) + sum(
            pi[x // p] for p in prime_list[a:pi[sqrt_x]])
    else:
        # Otherwise, sieve the interval in segments of size y
        P2 = 0
        prime_counts = [a]
        for low in range(y + 1, limit + 1, y):
            # Get prime counts for the interval [low, high)
            high = min(low + y, limit + 1)
            sieve = _sieve_segment(low, high - low, prime_list, max_prime=sqrt(high))
            prime_counts = itertools.accumulate(sieve, initial=prime_counts[-1])
            prime_counts = list(prime_counts)[1:]
            if low <= sqrt_x < high:
                pi_sqrt_x = prime_counts[sqrt_x - low]

            # Find all primes p ∈ (y, sqrt(x)] such that low <= x // p < high
            # by sieving the inverse interval (x // high, x // low]
            low_ = max(x // high, y) + 1
            high_ = min(x // low, sqrt_x)
            sieve_size_ = high_ - low_ + 1
            sieve_ = _sieve_segment(
                low_, sieve_size_, prime_list, max_prime=sqrt(high_))

            # Accumulate pi(x // p) for all x // p in our main interval [low, high)
            primes_ = list(itertools.compress(range(low_, high_ + 1), sieve_))
            P2 += sum(prime_counts[x // p - low] for p in primes_)

        P2 += comb(a, 2) - comb(pi_sqrt_x, 2)

    # Compute the least prime factor (lpf) and Mobius (μ) functions
    # for integers 1 ... y by iterating over the primes in reverse order
    lpf, mu = [0] * (y + 1), [1] * (y + 1)
    for p in reversed(prime_list[:a]):
        p_squared = p * p
        mu[p_squared::p_squared] = [0] * ((y - p_squared) // p_squared + 1)
        mu[p::p] = [-x for x in mu[p::p]]
        lpf[p::p] = [p] * ((y - p) // p + 1)

    # Compute S1 (sum over ordinary leaves)
    S1 = _phi_legendre(x, k, primes=prime_list[:k])
    leaves = [(i + 1, prime_list[i]) for i in range(k, a)]
    while leaves:
        b, n = leaves.pop()
        S1 += mu[n] * _phi_legendre(x // n, k, primes=prime_list[:k])
        for i in range(b, a):
            m = n * prime_list[i]
            if m > y:
                break
            leaves.append((i + 1, m))

    if k >= a:
        return a - 1 - P2 + S1

    # Compute S2 (sum over special leaves)
    S2 = 0
    phi = [0] * len(prime_list)
    limit = x // y
    sieve_size = 2**((isqrt(limit) - 1).bit_length())
    tree_size = sieve_size // 2

    for low in range(1, limit, sieve_size):
        # Sieve the segment [low, high) with the first k primes
        high = min(low + sieve_size, limit)
        sieve = _sieve_segment(low, sieve_size, prime_list[:k])

        # Initialize a Binary Indexed Tree
        # Only odd numbers are stored in the tree (tree[i] corresponds to sieve[2i])
        odd_sieve = sieve[::2]
        tree = _fenwick_tree_init(odd_sieve)

        # Sieve the segment [low, high) with the remaining primes
        for b in range(k, a):
            p = prime_list[b]
            min_m = max(x // (p * high), y // p)
            max_m = min(x // (p * low), y)
            if p >= max_m:
                break

            # Find special leaves in the tree (i.e. φ(x/n, b) where n > y)
            for m in range(max_m, min_m, -1):
                if p < lpf[m] and mu[m] != 0:
                    # Compute φ(x/pm, b) by counting the number of remaining
                    # elements after sieving the first b primes
                    pos = x // (p * m) - low
                    phi_xn = phi[b] + _fenwick_tree_query(tree, pos // 2)
                    S2 -= mu[m] * phi_xn

            # Store the number of unsieved elements
            phi[b] += _fenwick_tree_query(tree, tree_size - 1)

            # Mark odd prime multiples in the sieve
            # Update the tree for each element being marked for the first time
            next_odd_prime_multiple = ((low + p - 1) // p | 1) * p
            for index in range((next_odd_prime_multiple - low) // 2, tree_size, p):
                if odd_sieve[index]:
                    odd_sieve[index] = False
                    _fenwick_tree_update(tree, index, -1, tree_size)

    return a - 1 - P2 + S1 + S2

def _sieve_segment(
    start: int,
    sieve_size: int,
    prime_list: list[int],
    max_prime: int = None,
) -> bytearray:
    """
    Sieve the interval [start, start + sieve_size) using the given list of primes.
    Will also sieve out primes themselves if they fall within the interval.
    """
    sieve = bytearray([True]) * sieve_size
    if not prime_list:
        return sieve
    else:
        max_prime = max_prime or prime_list[-1]

    for p in prime_list:
        if p > max_prime:
            break

        offset = (-start) % p
        if offset < sieve_size:
            num_prime_multiples = ((sieve_size - offset + p - 1) // p)
            sieve[offset::p] = bytearray(num_prime_multiples) # mark false

    return sieve

@cache
def _primorial(n: int) -> int:
    """
    Calculate the product of the first n primes.
    """
    return prod(primes(num=n))

@cache
def _get_phi_legendre_offsets(d: int) -> list[int]:
    """
    Compute values for Legendre's formula φ(0, a), φ(1, a), ..., φ(d - 1, a)
    where d is the product of the first a primes, and φ(d) is Euler's totient function.
    """
    return list(itertools.accumulate(coprime_range(d)))

@cache
def _phi_legendre(x: int, a: int, primes: tuple[int] = None) -> int:
    """
    Evaluate Legendre's formula φ(x, a)
    which counts the number of positive integers less than or equal to x
    that are not divisible by any of the first a primes.
    """
    if a == 0:
        return x
    elif a < 8:
        # Use the direct formula φ(x, a) = φ(d) * (x // d) + φ(x % d, a)
        d = _primorial(a)
        return totient(d) * (x // d) + _get_phi_legendre_offsets(d)[x % d]
    else:
        # Use the recursive formula φ(x, a) = φ(x, a - 1) - φ(x // p, a - 1)
        p = primes[a - 1]
        return _phi_legendre(x, a - 1, primes) - _phi_legendre(x // p, a - 1, primes)



### Integer Divisibility

def divisors(n: int) -> list[int]:
    """
    Get all divisors of n (including both 1 and n).
    """
    prime_factorization = Counter(prime_factors(n))
    divisors = [1]

    for p, r in prime_factorization.items():
        divisors = [d * p**e for d in divisors for e in range(r + 1)]

    return divisors

def coprime_range(n: int) -> bytearray:
    """
    Return whether each integer from 0 ... (n - 1) is coprime to n.
    """
    is_coprime = bytearray([True]) * n
    is_coprime[0] = False
    for p in set(prime_factors(n)):
        is_coprime[p::p] = bytearray([False]) * ((n - 1) // p)

    return is_coprime

@cache
def totient(n: int) -> int:
    """
    Compute Euler's totient function φ(n) for an integer n.
    """
    prime_factorization = collections.Counter(prime_factors(n))
    return prod(p**(k - 1) * (p - 1) for p, k in prime_factorization.items())



### Divisibility Sieves

def get_totients(N: int) -> list[int]:
    """
    Find the value of Euler's totient function φ(n) for each n = 0, 1, 2, ..., N.
    """
    totients = list(range(N + 1))
    for p in primes(high=N):
        totients[p::p] = [x * (p - 1) // p for x in totients[p::p]]

    return totients

def get_divisor_counts(N: int) -> list[int]:
    """
    Find the number of divisors for each n = 0, 1, 2, ..., N.
    """
    divisor_counts = [1] * (N + 1)
    for d in range(2, N + 1):
        divisor_counts[d::d] = [x + 1 for x in divisor_counts[d::d]]

    return divisor_counts

def get_divisor_sums(N: int, proper: bool = False) -> list[int]:
    """
    Find the sum of divisors for each n = 0, 1, 2, ..., N.
    """
    k = 2 if proper else 1
    divisor_sums = [1] * (N + 1)
    for d in range(2, N + 1):
        divisor_sums[k*d::d] = [x + d for x in divisor_sums[k*d::d]]

    return divisor_sums

def get_prime_factorizations(N: int) -> list[dict[int, int]]:
    """
    Get the prime factorization for each n = 0, 1, 2, ..., N.

    Parameters
    ----------
    N : int
        Upper bound for n
    """
    prime_factors = [defaultdict(int) for _ in range(N + 1)]
    for p in primes(high=N):
        for e in range(1, int(log(N, p)) + 1):
            prime_power = p**e
            for factorization in prime_factors[prime_power::prime_power]:
                factorization[p] += 1

    return prime_factors



### Modular Arithmetic

@cache
def egcd(a: int, b: int) -> tuple[int, int, int]:
    """
    Extended Euclidean algorithm.

    Returns
    -------
    d : int
        Greatest common divisor of a and b
    x : int
        Coefficient of a in Bézout's identity (ax + by = d)
    y : int
        Coefficient of b in Bézout's identity (ax + by = d)
    """
    d, r = a, b
    x, s = 1, 0

    while r != 0:
        quotient = d // r
        d, r = r, d - quotient * r
        x, s = s, x - quotient * s

    y = (d - a*x) // b if b != 0 else 0
    return d, x, y

@cache
def _crt_two_congruences(congruence_1, congruence_2):
    a1, n1 = congruence_1
    a2, n2 = congruence_2
    d, m1, m2 = egcd(n1, n2)
    mod = lcm(n1, n2)
    return ((a1 * n2 * m2 + a2 * n1 * m1) // d) % mod, mod

def crt(congruences: Iterable[tuple[int, int]]) -> int:
    """
    Solve a system of linear congruences x ≡ a[i] (mod n[i])
    via the Chinese remainder theorem.

    Parameters
    ----------
    congruences : list[tuple[int, int]]
        List of residues and moduli

    Returns
    -------
    x : int
        Solution to the system of congruences
    """
    x, mod = reduce(_crt_two_congruences, congruences)
    return x % mod

def crt2(congruences) -> int:
    """
    Solve a system of linear congruences x ≡ a[i] (mod n[i])
    via the Chinese remainder theorem.

    Parameters
    ----------
    a : list[int]
        List of residues
    n : list[int]
        List of pairwise coprime moduli

    Returns
    -------
    x : int
        Solution to the system of congruences
    """
    a, n = zip(*congruences)
    N = prod(n)
    return sum(a * N // n * egcd(N // n, n)[1] for a, n in zip(a, n)) % N

@cache
def hensel(
    p: int,
    k: int,
    a: list[int],
    initial: Iterable[int] = None,
) -> Generator[int]:
    """
    Use Hensel lifting to find a solution to the polynomial congruence
    f(x) = a[0] + a[1]x + a[2]x^2 + ... = 0 (mod p^k).

    Parameters
    ----------
    p : int
        Prime base of modulus
    k : int
        Exponent of modulus
    a : list[int]
        Polynomial coefficients
    initial : list[int]
        Initial solutions to f(x) = 0 (mod p)
    """
    f = lambda x: sum(a[i] * x**i for i in range(len(a)))
    df = lambda x: sum(i * a[i] * x**(i - 1) for i in range(1, len(a)))

    solutions = {x for x in range(p) if f(x) % p == 0}
    if p == 2:
        mod = 1
        for _ in range(k):
            lifted_solutions = set()
            mod *= p
            for x in solutions:
                for x_ in (x, x + mod // 2):
                    if f(x_) % mod == 0:
                        lifted_solutions.add(x_)

            solutions = lifted_solutions

        return solutions

    solutions = set()

    initial = (x for x in range(p) if f(x) % p == 0) if initial is None else initial
    for x0 in initial:
        mod = p
        for _ in range(ceil(log(k, 2)) + 1):
            h = -f(x0) * pow(df(x0), -1, mod)
            mod **= 2
            x0 = (x0 + h) % mod

        solutions.add(x0 % p**k)
    
    return solutions



### Pythagorean Triples

def pythagorean_triples(max_sum: int) -> Generator[tuple[int, int, int]]:
    """
    Generate Pythagorean triples (a, b, c) with Euclid's formula.
    Returns all unique triples (a, b, c) such that a <= b <= c
    and a + b + c <= max_sum.
    """
    for m in range(2, ceil(sqrt(max_sum / 2))):
        for n in itertools.compress(range(m), coprime_range(m)):
            if (m + n) % 2 == 1:
                a, b, c = sorted((m*m - n*n, 2*m*n, m*m + n*n))
                for k in range(1, max_sum // (a + b + c) + 1):
                    yield (k*a, k*b, k*c)



### Fibonacci Numbers

@cache
def fibonacci(i: int, mod: int = None) -> int:
    """
    Return the i-th Fibonacci number.

    Parameters
    ----------
    i : int
        Index of the Fibonacci number
    mod : int
        Optional modulus
    """
    if i < 50:
        phi = (1 + sqrt(5)) / 2
        f = round(phi**i / sqrt(5))
    elif i % 2 == 0:
        i = i // 2
        f = fibonacci(i + 1, mod)**2 - fibonacci(i - 1, mod)**2
    else:
        i = (i + 1) // 2 
        f = fibonacci(i, mod)**2 + fibonacci(i - 1, mod)**2

    return f % mod if mod else f

def fibonacci_index(base: int, exp: int = 1) -> float:
    """
    Return the approximate index of F = base^exp in the Fibonacci sequence.

    Parameters
    ----------
    base : int
        Base of the Fibonacci number
    exp : int
        Exponent of the Fibonacci number
    """
    assert base > 1 and exp > 0
    phi = (1 + sqrt(5)) / 2 # golden ratio
    return log(sqrt(5), phi) + exp * log(base, phi)

def fibonacci_numbers(a: int = 0, b: int = 1, mod: int = None) -> Generator[int]:
    """
    Generate Fibonacci numbers.

    Parameters
    ----------
    a : int
        First element of the Fibonacci sequence
    b : int
        Second element of the Fibonacci sequence
    mod : int
        Optional modulus
    """
    while True:
        yield a
        a, b = b, a + b
        b = b % mod if mod else b



### Polygonal Numbers

def polygonal(s: int, i: int) -> int:
    """
    Return the i-th s-gonal number.
    """
    return (s - 2) * i * (i - 1) // 2 + i

def polygonal_index(s: int, n: int) -> float:
    """
    Return the s-gonal index of n.
    """
    return (sqrt(8 * n * (s - 2) + (s - 4) * (s - 4)) + s - 4) / (2 * (s - 2))

def polygonal_numbers(s: int, low: int = 1, high: int = None) -> Generator[int]:
    """
    Generate all s-gonal numbers in the range [low, high].
    """
    i = ceil(polygonal_index(s, low))
    n = polygonal(s, i)
    while high is None or n <= high:
        yield n
        n += (s - 2) * i + 1
        i += 1

def is_polygonal(s: int, n: int) -> bool:
    """
    Check if n is an s-gonal number.
    """
    D = 8 * n * (s - 2) + (s - 4) * (s - 4)
    sqrt_D = isqrt(D)
    return sqrt_D*sqrt_D == D and (sqrt_D + s - 4) % (2*s - 4) == 0

def is_square(n: int) -> bool:
    """
    Check if an integer n is a square.
    """
    return (sqrt_n := isqrt(n)) * sqrt_n == n

def non_squares(N: int) -> Generator[int]:
    """
    Return all non-square positive integers <= N.
    """
    return (n for n in range(N + 1) if not is_square(n))



### Pell Equations

def continued_fraction(D: int, P: int = 0, Q: int = 1) -> tuple[list[int], int]:
    """
    Compute coefficients for the continued fraction (P + sqrt(D)) / Q
    = a0 + 1 / a1 + 1 / (a2 + ...)).

    Returns
    -------
    coefficients : list[int]
        Coefficients of the continued fraction (through first repeating period)
    period_length : int
        Length of the repeating period
    """
    coefficients, period_start, sqrt_D = [], None, sqrt(D)
    while (P, Q) != period_start:
        xi = (P + sqrt_D) / Q
        if not period_start and 0 < abs(xi) - 1 < 2*P/abs(Q) < abs(xi):
            period_start = (P, Q)
            period_start_index = len(coefficients)

        a = int(xi)
        coefficients.append(a)
        P = a*Q - P
        Q = (D - P*P) // Q

    period_length = len(coefficients) - period_start_index
    return coefficients, period_length

def convergents(coefficients: Iterable[int]) -> list[tuple[int, int]]:
    """
    Return convergents of the continued fraction with the given coefficients.

    Returns
    -------
    convergents : list[tuple[int, int]]
        Convergents as (numerator, denominator) tuples
    """
    A, B = [0, 1], [1, 0]
    for a in coefficients:
        A.append(a * A[-1] + A[-2])
        B.append(a * B[-1] + B[-2])

    return list(zip(A[2:], B[2:]))

def pell(D: int, N: int = 1) -> Generator[tuple[int, int]]:
    """
    Generate integer solutions to the generalized Pell equation x^2 - Dy^2 = N.

    Uses the Lagrange-Matthews-Mollin (LMM) algorithm.

    Parameters
    ----------
    D : int
        Coefficient of y^2 term
    N : int
        Constant term

    Yields
    ------
    x : int
        X-coordinate of solution
    y : int
        Y-coordinate of solution
    """
    # Get convergents for continued fraction of sqrt(D)
    coefficients, period = continued_fraction(D)
    coefficients += coefficients[-period:]
    pell_convergents = convergents(coefficients)

    # Find minimal solution to x^2 - Dy^2 = -1
    solutions = ((x, y) for x, y in pell_convergents if x*x - D*y*y == -1)
    t, u = next(solutions, (None, None))

    # Find fundamental solutions to x^2 - Dy^2 = N
    fundamental_solutions = []
    for f in divisors(abs(N)):
        if (N // f) % f != 0:
            continue

        m = N // (f * f)
        for z in range(int((-abs(m) + 1) / 2), abs(m) // 2 + 1):
            if (z*z - D) % abs(m) == 0:
                a, _ = continued_fraction(D, P=z, Q=abs(m))
                i = next((i for i in range(1, len(a)) if abs(a[i]) > sqrt(D)), None)
                if i is not None:
                    A, B = zip(*convergents(a[:-1]))
                    x, y = f*(abs(m)*A[i-1] - z*B[i-1]), f*B[i-1]
                    if x*x - D*y*y == N:
                        fundamental_solutions.append((x, y))
                    elif (t, u) != (None, None):
                        fundamental_solutions.append(((x*t + y*u*D), (x*u + y*t)))

    yield from fundamental_solutions

    # Find minimal solution to x^2 - Dy^2 = 1
    t0, u0 = next((x, y) for x, y in pell_convergents if x*x - D*y*y == 1)

    # Generate additional solutions to x^2 - Dy^2 = N
    t, u = t0, u0
    while True:
        for r, s in fundamental_solutions:
            yield r*t + s*u*D, r*u + s*t

        t, u = t0*t + D*u0*u, t0*u + u0*t



### Integer Partitions

@cache
def euler_transform(a: Callable[[int], int]) -> Callable[[int], int]:
    """
    Return the Euler transform of integer sequence a.

    Parameters
    ----------
    a : Callable(int) -> int
        Integer sequence to transform
    """
    @cache
    def c(n: int) -> int:
        return sum(d * a(d) for d in divisors(n))

    @cache
    def b(n: int) -> int:
        if n == 0:
            return 1
        elif n == 1:
            return c(1)
        else:
            return ((c(n) + sum(c(k) * b(n - k) for k in range(1, n))) // n)

    return b

def num_partitions(n: int, restrict: Callable[[int], bool] | None = None) -> int:
    """
    Return the number of partitions of integer n.

    Parameters
    ----------
    n : int
        Integer to partition
    restrict : Callable(int) -> bool
        Function indicating integers that can be used in the partition
    """
    if restrict:
        return euler_transform(restrict)(n)    
    else:
        return next(p for i, p in enumerate(partition_numbers()) if i == n)

def partition_numbers(mod: int = None) -> Generator[int]:
    """
    Generate the values of the partition function.
    """
    def euler_pentagonal():
        for sign, n in zip(itertools.cycle((1, -1)), itertools.count(start=1)):
            yield sign, n * (3*n - 1) // 2
            yield sign, n * (3*n + 1) // 2

    generator = euler_pentagonal()
    recurrence = [next(generator) for _ in range(100)]
    partitions  = [1]
    yield 1

    for n in itertools.count(start=1):
        p = 0
        for i in itertools.count():
            try:
                sign, offset = recurrence[i]
            except IndexError:
                recurrence.extend(next(generator) for _ in range(100))
                sign, offset = recurrence[i]

            if offset > n: break
            p += sign * partitions[n - offset]

        partitions.append(p % mod if mod else p)
        yield partitions[n]

def get_partition_numbers(N: int, values: list[int] = None) -> list[int]:
    """
    Return the number of ways to partition integer n with the given values
    for n = 0, 1, 2, ..., N.
    """
    values = values or range(1, N + 1)
    num_partitions = [0] * (N + 1)
    num_partitions[0] = 1
    for i in values:
        for j in range(i, N + 1):
            num_partitions[j] += num_partitions[j - i]

    return num_partitions



### Graphs

Node = Hashable

def dijkstra(
    source: Node,
    get_neighbors: Callable[[Node], Iterable[Node]],
    get_edge_weight: Callable[[Node, Node], float],
) -> tuple[dict[Node, float], dict[Node, Node]]:
    """
    Use Dijkstra's algorithm to find the shortest path from a source node
    to all other nodes in a graph.

    Parameters
    ----------
    source : Node
        Source node
    get_neighbors : Callable(Node) -> Iterable[Node]
        Function that returns all neighbors of a given node
    get_edge_weight : Callable(Node, Node) -> float
        Function that returns the weight of the edge between two nodes

    Returns
    -------
    dist : dict[Node, float]
        Shortest distance from the source node to each node
    prev : dict[Node, Node]
        Predecessor of each node in the shortest path
    """
    dist = defaultdict(lambda: float('inf'), {source: 0})
    prev = defaultdict(lambda: None)
    queue = [(0, source)]
    while queue:
        _, u = heappop(queue)
        for v in get_neighbors(u):
            alt = dist[u] + get_edge_weight(u, v)
            if alt < dist[v]:
                dist[v], prev[v] = alt, u
                heappush(queue, (alt, v))

    return dist, prev

def bron_kerbosch(
    graph: dict[Node, set[Node]],
    R: set[Node] = set(),
    P: set[Node] | None = None,
    X: set[Node] = set(),
) -> list[set[Node]]:
    """
    Recursive implementation of the Bron-Kerbosch algorithm
    for finding maximal cliques.

    Parameters
    ----------
    graph : dict[Node, set[Node]]
        Graph represented as an adjacency list
    R : set[Node]
        Current clique
    P : set[Node] or None
        Nodes that can be added to clique
    X : set[Node]
        Nodes to be excluded from clique

    Returns
    -------
    maximal_cliques : list[set[Node]]
        List of maximal cliques in the graph
    """
    P = set(graph.keys()) if P is None else P

    maximal_cliques = []
    if not P and not X:
        maximal_cliques.append(R)

    for v in P.copy():
        maximal_cliques += bron_kerbosch(graph, R | {v}, P & graph[v], X & graph[v])
        P.remove(v)
        X.add(v)

    return maximal_cliques

def kruskal(
    nodes: Iterable[Node],
    edges: Iterable[tuple[Node, Node]],
    get_edge_weight: Callable[[Node, Node], float],
) -> list[tuple[Node, Node]]:
    """
    Use Kruskal's algorithm to find a minimum spanning tree.

    Parameters
    ----------
    nodes : Iterable[Node]
        Nodes in the graph
    edges : Iterable[tuple[Node, Node]]
        Edges in the graph
    get_edge_weight : Callable(Node, Node) -> float
        Function that returns the weight of the edge between two nodes

    Returns
    -------
    minimum_spanning_tree : list[tuple[Node, Node]]
        Edges in the minimum spanning tree
    """
    minimum_spanning_tree = []
    parent = {v: v for v in nodes}
    for edge in sorted(edges, key=lambda edge: get_edge_weight(*edge)):
        u, v = edge
        while parent[u] != u: u = parent[u]
        while parent[v] != v: v = parent[v]
        if u != v:
            parent[u] = v
            minimum_spanning_tree.append(edge)

    return minimum_spanning_tree
    
def find_cycles(
    find_next: Callable[[list[Node]], Iterable[Node]] = lambda path: [],
    current_path: list[Node] = [],
) -> Generator[list[Node]]:
    """
    Use DFS to find cycles in a graph.

    Parameters
    ----------
    current_path : list[Node]
        Current path in the graph
    find_next : Callable(list[Node]) -> Iterable[Node]
        Function that returns all candidates for the next node in the path
    """
    for v in find_next(current_path):
        if v in current_path:
            yield current_path[current_path.index(v):]
        else:
            for cycle in find_cycles(find_next, current_path + [v]):
                yield cycle



### Linear Algebra

def linear_solve(coefficients: list[list[float]], values: list[float]) -> list[float]:
    """
    Solve the system of linear equations.

    Parameters
    ----------
    coefficients : list[list[float]]
        M × N matrix of coefficients
    values : list[float]
        List of M values
    """
    assert len(coefficients) == len(values)
    A = [[*coefs, value] for coefs, value in zip(coefficients, values)]
    solutions = [row[-1] for row in _gauss_jordan(A)]
    return solutions

def matrix_product(A: list[list[float]], B: list[list[float]]) -> list[list[float]]:
    """
    Return the product of two matrices A and B.
    """
    assert len(A[0]) == len(B), "Matrix dimensions do not match"
    return [
        [sum(a*b for a, b in zip(row_a, col_b)) for col_b in zip(*B)]
        for row_a in A
    ]

def _gauss_jordan(A):
    """
    Gauss-Jordan elimination. Returns the given matrix in reduced row-echelon form.
    """
    num_rows, num_cols, pivot_col = len(A), len(A[0]), -1
    for current_row in range(len(A)):
        # Partial pivoting
        found_pivot = False
        while not found_pivot and pivot_col < num_cols - 1:
            pivot_col += 1
            pivot_row = max(
                range(current_row, num_rows), key=lambda i: abs(A[i][pivot_col]))
            found_pivot = (A[pivot_row][pivot_col] != 0)

        # Swap pivot row with current row
        if found_pivot:
            A[current_row], A[pivot_row] = A[pivot_row], A[current_row]
        else:
            break

        # Eliminate other coefficients in pivot column
        for row in range(len(A)):
            if row != current_row:
                A[row] = [
                    -x * A[row][pivot_col] + y * A[current_row][pivot_col]
                    for x, y in zip(A[current_row], A[row])
                ]

    # Normalize rows
    for row in range(len(A)):
        pivot_col = next((i for i in range(num_cols) if A[row][i] != 0), None)
        if pivot_col is not None:
            A[row] = [x / A[row][pivot_col] for x in A[row]]

    return A



### Miscellaneous

def group_permutations(iterable: Iterable[Sequence]) -> Iterable[list[Sequence]]:
    """
    Group permutations together.

    Returns an collection of lists of permutations, where for any given list
    all its items are permutations of each other.

    Parameters
    ----------
    iterable : Iterable[Sequence]
        Sequences to group
    """
    groups = defaultdict(list)
    for item in iterable:
        groups[tuple(sorted(item))].append(item)

    return groups.values()

def round_down(n: int, k: int = 1):
    """
    Round down n to the nearest multiple of k.
    """
    return (n // k) * k

def round_up(n: int, k: int = 1):
    """
    Round up n to the nearest multiple of k.
    """
    return ((n + k - 1) // k) * k

def get_digit_sum(n: int) -> int:
    """
    Return the sum of the digits in the decimal integer n.
    """
    mod = _int_str_mod()
    total = 0
    while n > 0:
        n, r = divmod(n, mod)
        m = map(int, str(r))
        total += sum(m)

    return total

def is_palindrome(n: int) -> bool:
    """
    Check if an integer is a palindrome.
    """
    return (s := f'{n}') == s[::-1]

def flatten(iterable: Iterable[Iterable], depth: int = 1) -> list:
    """
    Flatten a nested iterable.
    """
    for _ in range(depth):
        iterable = itertools.chain(*iterable)

    return list(iterable)

def polynomial(coefficients: Sequence[float]) -> Callable[[float], float]:
    """
    Create a polynomial with the given coefficients (a_0, ..., a_n).
    """
    return lambda x: sum(a * x**i for i, a in enumerate(coefficients))

def iroot(x: float, n: int = 2):
    """
    Return the integer part of the n-th root of x.
    """
    if x < 0:
        if n % 2 == 0:
            raise ValueError("Cannot compute even root of negative number")
        return -iroot(-x, n)

    a, b = x, x + 1
    while a < b:
        b = a
        t = (n - 1) * b + x // pow(b, n - 1)
        a = t // n

    return b



### Fenwick Tree

def _fenwick_tree_init(values: Iterable[Number]) -> list[Number]:
    """
    Create a Binary Indexed Tree (Fenwick Tree) from the given values.
    """
    tree = list(values)
    for index, parent_index in _fenwick_tree_edges(len(tree)):
        tree[parent_index] += tree[index]

    return tree

@cache
def _fenwick_tree_edges(tree_size: int) -> list[tuple[int, int]]:
    """
    Get all (index, parent_index) pairs for a Binary Indexed Tree (Fenwick Tree).
    """
    return [
        (index, index | (index + 1))
        for index in range(tree_size - 1)
        if index | (index + 1) < tree_size
    ]

def _fenwick_tree_query(tree: list[Number], index: int) -> Number:
    """
    Query the running total for the tree at the given index.
    """
    count = 0
    for i in _fenwick_tree_query_path(index):
        count += tree[i]

    return count

@cache
def _fenwick_tree_query_path(index: int) -> tuple[int, ...]:
    """
    Get all indices that need to be queried for a prefix sum.
    """
    path = []
    index += 1
    while index > 0:
        path.append(index - 1)
        index &= index - 1 # clears the lowest set bit

    return tuple(path)

def _fenwick_tree_update(
    tree: list[Number],
    index: int,
    value: Number,
    tree_size: int = None,
):
    """
    Update the given index in the tree.
    """
    tree_size = tree_size or len(tree)
    for i in _fenwick_tree_update_path(index, tree_size):
        tree[i] += value

@cache
def _fenwick_tree_update_path(index: int, tree_size: int) -> tuple[int, ...]:
    """
    Get all indices that need to be updated for a value change.
    """
    path = []
    while index < tree_size:
        path.append(index)
        index |= index + 1 # sets the lowest unset bit

    return tuple(path)



### Constants

@cache
def _int_str_mod():
    return 10**sys.get_int_max_str_digits()

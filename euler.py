# Copyright (c) 2025 Ini Oguntola
# Permission is granted to use, copy, modify, and redistribute this work
# provided attribution to the original author is retained.

from __future__ import annotations

import bisect
import itertools
import random
import string
import sys
import threading

from collections import Counter, defaultdict, deque
from collections.abc import Sequence
from functools import cache, reduce
from heapq import heappop, heappush
from math import comb, factorial, gcd, isqrt, log, prod, sqrt
from numbers import Number
from typing import Any, Callable, Hashable, Iterable, Iterator



### Primes

@cache
def is_prime(n: int) -> bool:
    """
    Test if a given integer n is prime.
    Uses a combination of trial division, Miller-Rabin primality test with
    deterministic bases for n <= 2^64, and Baillie-PSW primality test for n > 2^64
    (which is probabilistic but has no known counterexamples).

    Parameters
    ----------
    n : int
        Integer to test for primality
    """
    if n < 2:
        return False

    # Trial division over first few primes
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59):
        if n % p == 0:
            return n == p

    # Write n as 2^s * d + 1 with d odd (by factoring out powers of 2 from n − 1)
    s, d = 0, n - 1
    while d % 2 == 0:
        d //= 2
        s += 1

    # Use deterministic set of Miller-Rabin bases for n < 2^64
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
        return _baillie_psw(n, s, d)

    # Perform multiple rounds of Miller-Rabin testing
    for a in bases:
        if (a := a % n) == 0:
            continue
        if not _miller_rabin(n, s, d, a=a):
            return False

    return True

def next_prime(n: int) -> int:
    """
    Get the smallest prime number greater than n.

    Parameters
    ----------
    n : int
        Strict lower bound for prime number
    """
    if n < 2:
        return 2

    for a in itertools.count(start=(n + 1) | 1, step=2):
        if is_prime(a):
            return a

def primes(low: int = 2, high: int = None, num: int = None) -> Iterator[int]:
    """
    Generate prime numbers in increasing order within the range [low, high].
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
    low = max(low, 2)
    high = float('inf') if high is None else high
    num = float('inf') if num is None else num

    # Generate initial prime
    if low <= 2 <= high and num > 0:
        yield 2
        num -= 1
    elif low > high or num <= 0:
        return

    # Set initial sieve size
    # When `high` is given, sieve on range [low, high]
    # When `num` is given, sieve on range [low, n (log n + log log n)],
    # where n is an upper bound on `π(low) + num`
    if high == num == float('inf'):
        sieve_size = DEFAULT_SIEVE_SIZE
    else:
        n = num + 1.25506 * low / log(low)
        upper_bound = n * (log(n) + log(log(n)))
        sieve_size = int(min(MAX_SIEVE_SIZE, high - low + 1, upper_bound - low))

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

def count_primes(x: int) -> int:
    """
    Prime counting function π(x). Returns the number of primes <= x.
    Uses binary search on cached primes when possible, otherwise uses
    the LMO extension of the Meissel-Lehmer algorithm.

    Automatically stores a cache of any intermediate primes used to
    speed up repeated calls. To manually cache of primes up to N,
    use `count_primes.cache_primes(N)`, and to clear the cache,
    use `count_primes.clear_prime_cache()`.

    Parameters
    ----------
    x : int
        Upper bound for prime numbers
    """
    cached_primes = _primes_up_to_at_least()
    if x <= cached_primes[-1]:
        return bisect.bisect(cached_primes, x)
    else:
        return _meissel_lehmer(x)

def sum_primes(
    x: int,
    f: Callable[[int], Number] = None,
    f_prefix_sum: Callable[[int], Number] = None,
    intermediate_sums: bool = False,
) -> Number | dict[int, Number]:
    """
    Compute the sum of f(p) over all primes p <= x,
    where f is a completely multiplicative function.

    Uses a modified version of Lucy's Algorithm for prime summation.
    By default, f(p) = p.

    Parameters
    ----------
    x : int
        Upper bound for prime numbers
    f : Callable(int) -> int
        Completely multiplicative function f(n),
        where f(ab) = f(a) * f(b) for all a, b > 0
    f_prefix_sum : Callable(int) -> int
        Function to compute the cumulative sum Σ_{1 <= n <= v} f(n).
        Ideally this should have a closed form solution for efficiency.
    intermediate_sums : bool
        If True, return a dictionary of intermediate sums Σ_{p <= v} f(p)
        where v ranges over the values used in the computation
    """
    if x < 2:
        return 0 if not intermediate_sums else {}

    root = isqrt(x)
    values = [v for v in range(1, root + 1)]
    if root * root != x:
        values.append(x // root)
    for n in range(root - 1, 0, -1):
        values.append(x // n)

    # Choose y ~ x^(2/3) / (log x)^(2/3)
    c = 0.5
    y = int(round(c * (x**(2/3)) / (log(x)**(2/3))))
    y = max(root + 1, min(x, y))    

    # Precompute initial sums S(v) = F(v) - F(1) = F(v) - 1
    if f is None and f_prefix_sum is None:
        f, f_prefix_sum = (lambda n: n), (lambda v: v * (v + 1) // 2)
    elif f is None:
        f = lambda n: f_prefix_sum(n) - f_prefix_sum(n - 1)
    elif f_prefix_sum is None:
        f_prefix_sum = lambda v: sum(f(n) for n in range(1, v + 1))
    S = [f_prefix_sum(v) - 1 for v in values]

    # Initialize sieve and Fenwick tree
    f = cache(f)
    tree = _fenwick_tree_init([0, 0] + [f(n) for n in range(2, y + 1)])
    is_composite = bytearray(y + 1)
    is_composite[0] = is_composite[1] = True

    # Map only the "large" keys v > y to their indices for S0
    value_to_index = {v: i for i, v in enumerate(values) if v > y}
    S0 = lambda v: S[value_to_index[v]] if v > y else _fenwick_tree_query(tree, v)

    for p in range(2, root + 1):
        if is_composite[p]:
            continue

        # Update sums S(v, p) = S(v, p-1) - f(p) * (S(v // p, p-1) - S(p-1, p-1))
        limit = min(x // y, x // (p*p))
        previous_sum = S0(p - 1)
        if not intermediate_sums:
            S[-1] -= f(p) * (S0(x // p) - previous_sum)
            for i in range(p, limit + 1):
                if not is_composite[i]:
                    S[-i] -= f(p) * (S0(x // (i * p)) - previous_sum)
        else:
            for i in range(1, limit + 1):
                S[-i] -= f(p) * (S0(x // (i * p)) - previous_sum)

        # Update the sieve and Fenwick tree
        for j in range(p*p, y + 1, p):
            if not is_composite[j]:
                is_composite[j] = True
                _fenwick_tree_update(tree, j, -f(j))

    return {v: S0(v) for v in values} if intermediate_sums else S[-1]

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

def _baillie_psw(n: int, s: int, d: int) -> bool:
    """
    Baillie-PSW primality test for n,
    where n = 2^s * d + 1, with d odd.
    """
    # Perform Miller-Rabin test with base a = 2
    if not _miller_rabin(n, s, d, a=2):
        return False

    # Check if n is a perfect square
    if is_square(n):
        return False

    # Find a suitable D for the Lucas test
    D = 5
    while jacobi(D, n) != -1:
        D = -D - 2 if D > 0 else -D + 2

    # Perform a Lucas probable prime test
    P, U, V, inv2 = 1, 1, 1, (n + 1) // 2
    for bit in format(n + 1, 'b')[1:]:
        U, V = (U*V) % n, ((V*V + D*U*U) * inv2) % n
        if bit == '1':
            U, V = ((P*U + V) * inv2) % n, ((D*U + P*V) * inv2) % n

    return U == 0

def _eratosthenes(N: int) -> Iterable[int]:
    """
    Sieve of Eratosthenes.
    Returns prime numbers in the range [2, N].
    """
    # Initialize sieve
    sieve = bytearray(b'\x01') * (N + 1)
    sieve[0] = sieve[1] = False

    # Mark multiples of 2, 3 and 5
    sieve[4::2] = bytearray(b'\x00') * (N // 2 - 1)
    sieve[9::6] = bytearray(b'\x00') * ((N - 9) // 6 + 1)
    sieve[25::10] = bytearray(b'\x00') * ((N - 25) // 10 + 1)

    # Iterate over 6k ± 1
    wheel = (1, 5)
    for i in range(6, isqrt(N) + 1, 6):
        for w in wheel:
            j = i + w
            if sieve[j]:
                count = (N - j*j) // (2*j) + 1
                sieve[j*j::2*j] = bytearray(b'\x00') * count

    return itertools.compress(range(N + 1), sieve)

def _segmented_eratosthenes(
    start: int,
    sieve_size: int,
    small_primes: Sequence[int],
) -> Iterable[int]:
    """
    Segmented sieve of Eratosthenes.
    Returns odd prime numbers in the range [start, start + sieve_size).
    Expects sorted small primes up to √(start + sieve_size).
    """
    # Initialize sieve segment
    # Only odd numbers are stored in the sieve (sieve[i] corresponds to start + 2i)
    start, end = start | 1, start + sieve_size
    sieve_size = (end - start + 1) // 2
    sieve = bytearray(b'\x01') * sieve_size

    # Mark odd multiples of odd primes as composite
    for p in small_primes[1:]:
        # Find next odd multiple of p >= start
        next_odd_multiple = start + (p - start) % (2*p)
        if p*p > next_odd_multiple:
            next_odd_multiple = p*p

        # Mark multiples of p in the odd sieve
        index = (next_odd_multiple - start) // 2
        count = (sieve_size - index + p - 1) // p
        if count > 0:
            sieve[index::p] = bytearray(b'\x00') * count

    return itertools.compress(range(start, start + 2 * sieve_size, 2), sieve)

@cache
def _meissel_lehmer(x: int, k: int = 15, c: float = 0.003) -> int:
    """
    Lagarias-Miller-Odlyzko (LMO) extension of the Meissel-Lehmer algorithm.
    Returns the value of the prime counting function π(x), i.e. the number of
    primes less than or equal to x.

    See: https://www.ams.org/journals/mcom/1985-44-170/
    S0025-5718-1985-0777285-5/S0025-5718-1985-0777285-5.pdf
    """
    if x <= 0:
        return 0

    # Set y = cx^(1/3) log^2(x) such that x^(1/3) <= y <= x^(2/5)
    y = int(c * iroot(x, 3) * (log(x) ** 2))
    y = min(max(y, iroot(x, 3)), iroot(x * x, 5))

    # Count primes up to y
    small_primes = _primes_up_to_at_least(y)
    a = bisect.bisect(small_primes, y)

    # Set other variables
    k = min(k, a)
    sqrt_x = isqrt(x)

    # Compute P2(x, a) from the LMO algorithm
    # Find the sum of pi(x // p) for all primes in the interval (y, x/y]
    limit = x // y
    if small_primes[-1] >= limit:
        # If we already have all primes in the interval,
        # directly compute pi(n) for n = 1 ... x/y
        sieve = bytearray(limit + 1)
        for p in small_primes:
            if p > limit:
                break
            sieve[p] = True

        pi = list(itertools.accumulate(sieve))
        P2 = comb(a, 2) - comb(pi[sqrt_x], 2) + sum(
            pi[x // p] for p in small_primes[a:pi[sqrt_x]])
    else:
        # Otherwise, sieve the interval in segments of size y
        P2 = 0
        prime_counts = [a]
        pi_sqrt_x = 0
        for low in range(y + 1, limit + 1, y):
            # Get prime counts for the interval [low, high)
            high = min(low + y, limit + 1)
            sieve = _meissel_lehmer_sieve_segment(
                low, high - low, small_primes, max_prime=isqrt(high))
            prime_counts = itertools.accumulate(sieve, initial=prime_counts[-1])
            prime_counts = list(prime_counts)[1:]
            if low <= sqrt_x < high:
                pi_sqrt_x = prime_counts[sqrt_x - low]

            # Find all primes p ∈ (y, sqrt(x)] such that low <= x // p < high
            # by sieving the inverse interval (x // high, x // low]
            low_ = max(x // high, y) + 1
            high_ = min(x // low, sqrt_x)
            sieve_size_ = high_ - low_ + 1
            sieve_ = _meissel_lehmer_sieve_segment(
                low_, sieve_size_, small_primes, max_prime=isqrt(high_))

            # Accumulate pi(x // p) for all x // p in our main interval [low, high)
            primes_ = list(itertools.compress(range(low_, high_ + 1), sieve_))
            P2 += sum(prime_counts[x // p - low] for p in primes_)

        P2 += comb(a, 2) - comb(pi_sqrt_x, 2)

    # Compute the least prime factor (lpf) and Mobius (μ) functions
    # for integers 1 ... y by iterating over the primes in reverse order
    lpf, mu = [0] * (y + 1), [1] * (y + 1)
    for p in reversed(small_primes[:a]):
        p_squared = p * p
        mu[p_squared::p_squared] = [0] * ((y - p_squared) // p_squared + 1)
        mu[p::p] = [-x for x in mu[p::p]]
        lpf[p::p] = [p] * ((y - p) // p + 1)

    # Compute S1 (sum over ordinary leaves)
    S1 = _phi_legendre(x, k, primes=small_primes[:k])
    leaves = [(i + 1, small_primes[i]) for i in range(k, a)]
    while leaves:
        b, n = leaves.pop()
        S1 += mu[n] * _phi_legendre(x // n, k, primes=small_primes[:k])
        for i in range(b, a):
            m = n * small_primes[i]
            if m > y:
                break
            leaves.append((i + 1, m))

    if k >= a:
        return a - 1 - P2 + S1

    # Compute S2 (sum over special leaves)
    S2 = 0
    phi = [0] * a
    limit = x // y
    sieve_size = 2**((isqrt(limit) - 1).bit_length())
    tree_size = sieve_size // 2

    for low in range(1, limit, sieve_size):
        # Sieve the segment [low, high) with the first k primes
        high = min(low + sieve_size, limit)
        sieve = _meissel_lehmer_sieve_segment(low, sieve_size, small_primes[:k])

        # Initialize a Binary Indexed Tree
        # Only odd numbers are stored in the tree (tree[i] corresponds to sieve[2i])
        odd_sieve = sieve[::2]
        tree = _fenwick_tree_init(odd_sieve)

        # Sieve the segment [low, high) with the remaining primes
        for b in range(k, a):
            p = small_primes[b]
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

def _meissel_lehmer_sieve_segment(
    start: int,
    sieve_size: int,
    small_primes: Sequence[int],
    max_prime: int = None,
) -> bytearray:
    """
    Sieve the interval [start, start + sieve_size) using the given list of primes.
    Will also sieve out primes themselves if they fall within the interval.
    """
    sieve = bytearray(b'\x01') * sieve_size
    if not small_primes:
        return sieve
    else:
        max_prime = max_prime or small_primes[-1]

    for p in small_primes:
        if p > max_prime:
            break

        offset = (-start) % p
        if offset < sieve_size:
            num_prime_multiples = ((sieve_size - offset + p - 1) // p)
            sieve[offset::p] = bytearray(b'\x00') * num_prime_multiples # mark false

    return sieve

@cache
def _phi_legendre(x: int, a: int, primes: tuple[int, ...] = None) -> int:
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

@cache
def _get_phi_legendre_offsets(d: int) -> tuple[int, ...]:
    """
    Compute values for Legendre's formula φ(0, a), φ(1, a), ..., φ(d - 1, a)
    where d is the product of the first a primes, and φ(d) is Euler's totient function.
    """
    return tuple(itertools.accumulate(_coprime_range(d)))

@cache
def _primorial(n: int) -> int:
    """
    Calculate the product of the first n primes.
    """
    return prod(primes(num=n))

def _primes_up_to_at_least(N: int = None) -> tuple[int, ...]:
    """
    Ensure the cache includes all primes <= N (inclusive).
    Returns the entire cache; may include primes > N if the cache was previously grown.
    No recomputation or shrinking when N is smaller than any prior request.
    """
    with count_primes._cache_lock:
        cached_primes = count_primes._cached_primes
        if N is None or N <= cached_primes[-1]:
            return cached_primes

        if N > cached_primes[-1]:
            low = cached_primes[-1] + 1
            count_primes._cached_primes += tuple(primes(low=low, high=N))

        return count_primes._cached_primes

def _clear_prime_cache() -> None:
    """
    Clear cached primes.
    """
    with count_primes._cache_lock:
        count_primes._cached_primes = (2, 3)

count_primes.cache_primes = _primes_up_to_at_least
count_primes.clear_prime_cache = _clear_prime_cache
count_primes._cache_lock = threading.Lock()
count_primes._cached_primes = (2, 3)



### Factorization

@cache
def prime_factors(n: int) -> tuple[int, ...]:
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

    factors = []

    # Trial division over first few primes
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47):
        if p * p > n: break
        while n % p == 0:
            factors.append(p)
            n //= p

    # Use Brent's algorithm to find a nontrivial factor
    if n == 1:
        pass
    elif is_prime(n):
        factors.append(n)
    else:
        d = _brent(n)
        factors += prime_factors(d)
        factors += prime_factors(n // d)

    return tuple(factors)

def prime_factorization(n: int) -> dict[int, int]:
    """
    Get the prime factorization of n as a dictionary of {prime: exponent}.
    Uses Pollard's rho factorization method.

    Parameters
    ----------
    n : int
        Integer to factor
    """
    pf = defaultdict(int)

    if n < 2:
        return pf

    # Trial division over first few primes
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47):
        if p * p > n: break
        while n % p == 0:
            pf[p] += 1
            n //= p

    # Use Brent's algorithm for remaining factors
    if n == 1:
        pass
    elif is_prime(n):
        pf[n] += 1
    else:
        stack = deque([n])
        while stack:
            n = stack.pop()
            if is_prime(n):
                pf[n] += 1
            else:
                d = _brent(n)
                stack.append(d)
                stack.append(n // d)

    return pf

def divisors(n: int) -> tuple[int, ...]:
    """
    Get all divisors of n (in no particular order, and including both 1 and n).
    """
    # Build divisors from the prime factorization,
    # starting from [1], and for each p^e, multiplying existing factors
    # by the prime powers p, p^2, ..., p^e
    factors = [1]
    for p, e in prime_factorization(n).items():
        current_factors, prime_power = factors[:], 1
        for _ in range(e):
            prime_power *= p
            factors += [d * prime_power for d in current_factors]

    return tuple(factors)

@cache
def _brent(n: int, seed: int = None) -> int:
    """
    Brent's variant of Pollard's rho factorization method.
    Returns an integer factor of n.
    """
    rng = random.Random(seed)
    while True:
        y = rng.randrange(2, n - 1)
        c = rng.randrange(1, n - 1) | 1 # ensure c is odd
        G, q, r = 1, 1, 1

        while G == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n

            k, m = 0, 64
            while k < r and G == 1:
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n
                    q = (q * abs(x - y)) % n

                G = gcd(q, n)
                k += m

            r *= 2

        if G == n:
            G = 1
            while G == 1:
                y = (y * y + c) % n
                G = gcd(abs(x - y), n)

        if G < n:
            return G



### Multiplicative Functions

def totient(n: int) -> int:
    """
    Compute Euler's totient function φ(n) for an integer n.
    """
    return prod(p**(k - 1) * (p - 1) for p, k in prime_factorization(n).items())

def jacobi(a: int, n: int) -> int:
    """
    Return the Jacobi symbol (a | n), where n is an odd positive integer.
    """
    if n <= 0 or n % 2 == 0:
        raise ValueError("n must be a positive odd integer.")

    J = 1
    while (a := a % n) != 0:
        # Extract factors of 2 from a
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                J = -J

        # Apply quadratic reciprocity
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            J = -J

    return J if n == 1 else 0

def divisor_count_range(N: int) -> list[int]:
    """
    Find the number of divisors d(n) for each n = 0, 1, 2, ..., N - 1.
    Includes dummy value d(0) = 1.
    """
    # Use the multiplicative property of the divisor count function
    # exp[n] = exponent of small_prime_factor[n] in n
    divisor_counts = [1] * N
    exp = [0] * N
    small_prime_factor = _small_prime_factor_range(N)
    for n in range(2, N):
        p = small_prime_factor[n]
        m = n // p
        if small_prime_factor[m] == p:
            e = exp[m] + 1
            exp[n], divisor_counts[n] = e, (divisor_counts[m] // e) * (e + 1)
        else:
            exp[n], divisor_counts[n] = 1, divisor_counts[m] * 2

    return divisor_counts

def divisor_function_range(N: int, k: int = 1) -> list[int]:
    """
    Find the values of the divisor function σ_k(n) for each n = 0, 1, 2, ..., N - 1,
    where σ_k(n) = ∑_{d|n} d^k. Includes dummy value σ_k(0) = 0.
    """
    if k == 0:
        return divisor_count_range(N)
    elif k < 0:
        raise ValueError("k must be a non-negative integer.")

    # Use the multiplicative property of the divisor sum function
    # power[n] = p^(ke) for the largest prime power p^e | n,
    # where p = small_prime_factor[n]
    # sum_of_powers[n] = 1 + p^k + p^(2k) + ... + p^(ke)
    divisor_sums = [1] * N
    power, sum_of_powers = [0] * N, [0] * N
    small_prime_factor = _small_prime_factor_range(N)
    for n in range(2, N):
        p = small_prime_factor[n]
        m = n // p
        if small_prime_factor[m] == p:
            power[n] = power[m] * p**k
            sum_of_powers[n] = sum_of_powers[m] + power[n]
            divisor_sums[n] = divisor_sums[m] // sum_of_powers[m] * sum_of_powers[n]
        else:
            power[n] = p**k
            sum_of_powers[n] = 1 + power[n]
            divisor_sums[n] = divisor_sums[m] * sum_of_powers[n]

    divisor_sums[0] = 0
    return divisor_sums

def aliquot_sum_range(N: int) -> list[int]:
    """
    Find the value of the aliquot sum s(n) = σ(n) - n
    for each n = 0, 1, 2, ..., N - 1. Includes dummy value s(0) = 0.
    """
    divisor_sums = divisor_function_range(N)
    return [d - i for i, d in enumerate(divisor_sums)]

def totient_range(N: int) -> list[int]:
    """
    Find the value of Euler's totient function φ(n) for each n = 0, 1, 2, ..., N - 1.
    Includes dummy value φ(0) = 1.
    """
    # Use the multiplicative property of the totient function
    phi = [1] * N
    small_prime_factor = _small_prime_factor_range(N)
    for n in range(2, N):
        if (p := small_prime_factor[n]) == n:
            phi[n] = n - 1
        else:
            m = n // p
            if m % p == 0:
                phi[n] = phi[m] * p
            else:
                phi[n] = phi[m] * (p - 1)

    return phi

def mobius_range(N: int) -> list[int]:
    """
    Find the value of the Mobius function μ(n) for each n = 0, 1, 2, ..., N - 1.
    Includes dummy value μ(0) = 1.
    """
    # Use the multiplicative property of the Mobius function
    mu = [1] * N
    small_prime_factor = _small_prime_factor_range(N)
    for n in range(2, N):
        p = small_prime_factor[n]
        m = n // p
        if small_prime_factor[m] == p:
            mu[n] = 0
        else:
            mu[n] = -mu[m]

    return mu

def _small_prime_factor_range(N: int) -> list[int]:
    """
    Find a prime factor for each n = 0, 1, 2, ..., N - 1.
    """
    small_prime_factor = list(range(N))
    if N >= 1:
        for p in primes(high=isqrt(N-1)):
            small_prime_factor[p::p] = [p] * ((N - 1 - p) // p + 1)

    return small_prime_factor

def _coprime_range(N: int) -> bytearray:
    """
    Return whether each integer from 0, 1, 2, ... N - 1 is coprime to N.
    """
    is_coprime = bytearray(b'\x01') * N
    is_coprime[0] = (N == 1)
    for p in set(prime_factors(N)):
        is_coprime[p::p] = bytearray(b'\x00') * ((N - 1) // p)

    return is_coprime



### Modular Arithmetic

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

    while r:
        quotient = d // r
        d, r = r, d - quotient * r
        x, s = s, x - quotient * s

    if d < 0:
        d, x = -d, -x

    y = (d - a*x) // b if b != 0 else 0
    return d, x, y

def crt(residues: Iterable[int], moduli: Iterable[int]) -> tuple[int, int]:
    """
    Solve a system of linear congruences x ≡ a[i] (mod n[i])
    via the Chinese Remainder Theorem.

    Parameters
    ----------
    residues : Iterable[int]
        Sequence of residues
    moduli : Iterable[int]
        Sequence of moduli

    Returns
    -------
    x : int
        Solution to the system of congruences
    mod : int
        Least common multiple of the moduli
    """
    return reduce(_crt_two_congruences, zip(residues, moduli), (0, 1))

def hensel(
    p: int,
    k: int,
    a: Sequence[int],
    initial: Iterable[int] = None,
) -> Iterator[int]:
    """
    Use Hensel lifting to find a solution to the polynomial congruence
    f(x) = a[0] + a[1]x + a[2]x^2 + ... = 0 (mod p^k).

    Parameters
    ----------
    p : int
        Prime base of modulus
    k : int
        Exponent of modulus
    a : Sequence[int]
        Polynomial coefficients, where a[i] is the coefficient for x^i
    initial : list[int]
        Initial solutions to f(x) = 0 (mod p)
    """
    f, df = polynomial(a), polynomial([i * a[i] for i in range(1, len(a))])

    # Find initial solutions to f(x) = 0 (mod p)
    if initial is None:
        solutions = {x for x in range(p) if f(x) % p == 0}
    else:
        solutions = {x % p for x in initial if f(x) % p == 0}

    # Exit early if no solutions or k = 1
    if k <= 0 or not solutions:
        return
    if k == 1:
        yield from solutions
        return

    # Hensel lifting to find solutions to f(x) = 0 (mod p^k)
    mod = p
    for _ in range(k - 1):
        new_solutions, new_mod = set(), mod * p
        for root in solutions:
            base = root % mod
            f_val = f(base) % new_mod
            if f_val % mod != 0:
                continue

            f_coeff, df_mod = (f_val // mod) % p, df(base) % p
            if df_mod != 0:
                # Simple root, unique lift
                t = (-f_coeff * pow(df_mod, -1, p)) % p
                new_solutions.add((base + t * mod) % new_mod)
            elif f_coeff == 0:
                # Multiple root, p (potential) lifts
                new_solutions.update((base + t * mod) % new_mod for t in range(p))

        solutions, mod = new_solutions, new_mod
        if not solutions:
            break

    for root in solutions:
        yield root % mod

def multiplicative_order(a: int, n: int) -> int | None:
    """
    Return the smallest integer k such that a^k ≡ 1 (mod n).
    """
    if gcd(a, n) != 1:
        return None

    for k in sorted(divisors(totient(n))):
        if pow(a, k, n) == 1:
            return k

def _crt_two_congruences(
    congruence_1: tuple[int, int],
    congruence_2: tuple[int, int],
) -> tuple[int, int]:
    """
    Solve a system of two linear congruences x ≡ a1 (mod n1) and x ≡ a2 (mod n2)
    via the Chinese remainder theorem.
    """
    a1, n1 = congruence_1
    a2, n2 = congruence_2
    d = gcd(n1, n2)
    diff = a2 - a1
    if diff % d != 0:
        raise ValueError("No solution exists for the given system of congruences.")

    # Reduce to coprime moduli and compute modular inverse
    n1_, n2_ = n1 // d, n2 // d
    k = diff // d
    inv = pow(n1_, -1, n2_)

    # Compute solution
    x = a1 + n1 * ((k * inv) % n2_)
    mod = n1 * n2_ # n1 * n2 // d
    return x % mod, mod



### Combinatorics

def pascal(num_rows: int = None) -> Iterator[tuple[tuple[int, int], int]]:
    """
    Generate values in Pascal's triangle, row by row, left to right.

    Parameters
    ----------
    num_rows : int
        Number of rows to generate (infinite by default)

    Yields
    ------
    (n, k) : tuple[int, int]
        Index of binomial coefficient
    a : int
        Binomial coefficient a = (n choose k)
    """
    row = [1]
    for n in itertools.count() if num_rows is None else range(num_rows):
        yield from (((n, k), v) for k, v in enumerate(row)) # current row
        row = [1, *map(int.__add__, row, row[1:]), 1] # next row

def partition_numbers(mod: int = None) -> Iterator[int]:
    """
    Generate the values of the partition function.
    """
    yield 1
    n, k = 0, 1
    partitions, euler_pentagonal = [1], deque()

    while True:
        n += 1

        # Extend generalized pentagonal numbers to cover offsets up to n
        while not euler_pentagonal or euler_pentagonal[-1][1] <= n:
            sign = 1 if k % 2 == 1 else -1
            euler_pentagonal.append((sign, k * (3 * k - 1) // 2))
            euler_pentagonal.append((sign, k * (3 * k + 1) // 2))
            k += 1

        # Euler's recurrence: p(n) = Σ sign * p(n - offset)
        p = 0
        for sign, off in euler_pentagonal:
            if off > n: break
            p += sign * partitions[n - off]

        p = p % mod if mod else p
        yield p
        partitions.append(p)

def count_partitions(n: int, restrict: Callable[[int], bool] | None = None) -> int:
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

@cache
def euler_transform(a: Callable[[int], int]) -> Callable[[int], int]:
    """
    Return the Euler transform of integer sequence a.

    Parameters
    ----------
    a : Callable(int) -> int
        Integer sequence to transform
    """
    a = cache(a)
    b_values = [1]
    c_values = [0]

    @cache
    def c(n: int) -> int:
        return sum(d * a(d) for d in divisors(n))

    def b(n: int) -> int:
        while len(b_values) <= n:
            i = len(b_values)
            total = c(i)
            for k in range(1, i):
                total += c(k) * b_values[i - k]

            b_values.append(total // i)

        return b_values[n]

    return b



### Pell Equations

def pell(D: int, N: int = 1) -> Iterator[tuple[int, int]]:
    """
    Generate solutions to the generalized Pell equation x^2 - Dy^2 = N.
    Yields positive integer solutions (x, y) in order of increasing x.
    Uses the Lagrange-Matthews-Mollin (LMM) algorithm.

    See: https://cjhb.site/Files.php/Books/math/B3.4/pell.pdf

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
    if D <= 0:
        raise ValueError("D must be a positive integer.")

    # Handle special case where D is a perfect square
    if is_square(D):
        root = isqrt(D)

        # Infinitely many solutions if N = 0
        if N == 0:
            yield from map(lambda y: (root * y, y), itertools.count(start=1))

        # There are only finitely many solutions if N != 0
        else:
            d = 2 * root
            factors = sorted(divisors(abs(N)))
            for i in range(len(factors) // 2):
                a, b = factors[i], factors[-i - 1]
                if N > 0 and (b - a) % d == 0:
                    yield (a + b) // 2, (b - a) // d
                elif N < 0 and (a + b) % d == 0:
                    yield (b - a) // 2, (a + b) // d

        return

    # Exit early if N = 0 has only the trivial solution
    if N == 0: return

    # Get convergents for continued fraction of sqrt(D)
    coefficients, initial, period = periodic_continued_fraction(D)
    pell_convergents = list(convergents(coefficients, num=initial+2*period))

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
                a, initial, period = periodic_continued_fraction(D, P=z, Q=abs(m))
                a = [next(a) for _ in range(initial + period)]
                i = next((i for i in range(1, len(a)) if abs(a[i]) > sqrt(D)), None)
                if i is not None:
                    A, B = zip(*list(convergents(a[:-1])))
                    x, y = f*(abs(m)*A[i-1] - z*B[i-1]), f*B[i-1]
                    if x*x - D*y*y == N:
                        fundamental_solutions.append((x, y))
                    elif (t, u) != (None, None):
                        fundamental_solutions.append(((x*t + y*u*D), (x*u + y*t)))

    # Find minimal solution to x^2 - Dy^2 = 1
    t0, u0 = next((x, y) for x, y in pell_convergents if x*x - D*y*y == 1)

    # Find minimal positive solutions to x^2 - Dy^2 = N
    minimal_positive_solutions = []
    for x, y in fundamental_solutions:
        if x > 0 and y > 0:
            minimal_positive_solutions.append((x, y))
        elif x < 0 and y < 0:
            minimal_positive_solutions.append((-x, -y))
        else:
            minimal_positive_solutions.append((-x*t0 + -y*u0*D, -x*u0 + -y*t0))

    # Yield minimal positive solutions to x^2 - Dy^2 = N
    minimal_positive_solutions = sorted(minimal_positive_solutions)
    yield from minimal_positive_solutions
    if not minimal_positive_solutions:
        return

    # Yield additional solutions to x^2 - Dy^2 = N
    t, u = t0, u0
    while True:
        for r, s in minimal_positive_solutions:
            yield r*t + s*u*D, r*u + s*t

        t, u = t0*t + D*u0*u, t0*u + u0*t

def periodic_continued_fraction(
    D: int,
    P: int = 0,
    Q: int = 1,
) -> tuple[Iterator[int], int, int]:
    """
    Compute coefficients for the periodic continued fraction
    (P + sqrt(D)) / Q = a0 + 1 / (a1 + 1 / (a2 + ...)).

    Returns
    -------
    coefficients : Iterator[int]
        Coefficients of the continued fraction
    initial_length : int
        Length of the initial non-repeating block
    period_length : int
        Length of the repeating period
    """
    if is_square(D) or D <= 0:
        raise ValueError("D must be a non-square positive integer.")

    coefficients, index, sqrt_D = [], {}, isqrt(D)
    a = (sqrt_D + P) // Q
    while (P, Q, a) not in index:
        index[P, Q, a] = len(coefficients)
        coefficients.append(a)
        P = a*Q - P
        Q = (D - P*P) // Q
        a = (sqrt_D + P) // Q

    period_length = len(coefficients) - index[P, Q, a]
    initial_length = len(coefficients) - period_length
    coefficients = itertools.chain(
        coefficients[:initial_length],
        itertools.cycle(coefficients[initial_length:])
    )

    return coefficients, initial_length, period_length

def convergents(
    coefficients: Iterable[int],
    num: int = None,
) -> Iterator[tuple[int, int]]:
    """
    Return convergents of the continued fraction with the given coefficients.

    Parameters
    ----------
    coefficients : Iterable[int]
        Coefficients of the continued fraction
    num : int
        Maximum number of convergents to generate (infinite by default)

    Yields
    ------
    numerator : int
        Numerator of the convergent
    denominator : int
        Denominator of the convergent
    """
    A, A_prev = 1, 0
    B, B_prev = 0, 1
    for a in itertools.islice(coefficients, num):
        A, A_prev = a * A + A_prev, A
        B, B_prev = a * B + B_prev, B
        yield A, B



### Pythagorean Triples

def pythagorean_triples(
    max_c: float = None,
    max_sum: float = None,
) -> Iterator[tuple[int, int, int]]:
    """
    Generate Pythagorean triples (a, b, c) with Euclid's formula.
    Returns unique triples (a, b, c) where a <= b <= c.

    If no bounds are specified, infinitely generates triples in order of increasing c.

    Parameters
    ----------
    max_c : float
        Upper bound for c in generated triples, where c <= max_c
    max_sum : float
        Upper bound for the sum of generated triples, where a + b + c <= max_sum
    """
    max_m = None
    if max_c is not None:
        max_c = int(max_c)
        max_m = min(max_m or float('inf'), isqrt(max_c))
    if max_sum is not None:
        max_sum = int(max_sum)
        max_m = min(max_m or float('inf'), isqrt(max_sum // 2))

    # Bounded case
    if max_m is not None:
        for a, b, c in _euclid(max_m=max_m):
            # Generate multiples of primitive triple
            if max_c is not None and max_sum is not None:
                max_k = min(max_c // c, max_sum // (a + b + c))
            elif max_sum is not None:
                max_k = max_sum // (a + b + c)
            else:
                max_k = max_c // c
            for k in range(1, int(max_k) + 1):
                yield (k*a, k*b, k*c)

        return

    # Unbounded case
    queue = [] # (current_c, k, a0, b0, c0)
    primitive_triples = _berggren()
    a0, b0, c0 = next(primitive_triples)
    while True:
        # Queue primitive triples (a0, b0, c0)
        while not queue or c0 <= queue[0][0]:
            heappush(queue, (c0, 1, a0, b0, c0))
            a0, b0, c0 = next(primitive_triples)

        # Yield the next triple (ka, kb, kc)
        _, k, a, b, c = heappop(queue)
        yield (k*a, k*b, k*c)

        # Queue the next multiple of (a, b, c)
        k += 1
        heappush(queue, (k*c, k, a, b, c))

def _euclid(max_m: int = None) -> Iterator[tuple[int, int, int]]:
    """
    Generate unique primitive Pythagorean triples (a, b, c) with Euclid's formula,
    where a <= b <= c.
    """
    for m in (itertools.count(start=2) if max_m is None else range(2, max_m + 1)):
        for n in itertools.compress(range(m), _coprime_range(m)):
            if (m + n) % 2 == 1:
                m_squared, n_squared = m*m, n*n
                a, b, c = m_squared - n_squared, 2*m*n, m_squared + n_squared
                if a > b:
                    a, b = b, a
                yield (a, b, c)

def _berggren() -> Iterator[tuple[int, int, int]]:
    """
    Generate primitive Pythagorean triples (a, b, c) with Berggren's tree method,
    where a <= b <= c, and triples are generated in order of increasing c.    
    """
    triples = [(5, 3, 4)]
    while triples:
        c, a, b = heappop(triples)
        if a > b:
            a, b = b, a
        yield (a, b, c)

        # Apply Berggren's transformations
        heappush(triples, (2*a - 2*b + 3*c, a - 2*b + 2*c, 2*a - b + 2*c))
        heappush(triples, (2*a + 2*b + 3*c, a + 2*b + 2*c, 2*a + b + 2*c))
        heappush(triples, (-2*a + 2*b + 3*c, -a + 2*b + 2*c, -2*a + b + 2*c))



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
    if i < 0:
        f = (-1)**((i % 2) + 1) * fibonacci(-i, mod)
    elif i <= 70:
        phi = (1 + sqrt(5)) / 2
        f = round(phi**i / sqrt(5))
    elif i % 2 == 0:
        i = i // 2
        f = fibonacci(i + 1, mod)**2 - fibonacci(i - 1, mod)**2
    else:
        i = (i + 1) // 2
        f = fibonacci(i, mod)**2 + fibonacci(i - 1, mod)**2

    return f % mod if mod else f

def fibonacci_index(base: int, exp: int = 1) -> int:
    """
    Find the index of base^exp in the Fibonacci sequence.
    Returns the largest integer i such that F(i) <= base^exp.

    Parameters
    ----------
    base : int
        Base of the Fibonacci number
    exp : int
        Exponent of the Fibonacci number
    """
    assert base > 1 and exp > 0
    phi = (1 + sqrt(5)) / 2 # golden ratio
    i = int(log(sqrt(5), phi) + exp * log(base, phi))
    n = pow(base, exp)
    while fibonacci(i) > n:
        i -= 1
    while fibonacci(i + 1) <= n:
        i += 1

    return i

def fibonacci_numbers(a: int = 0, b: int = 1, mod: int = None) -> Iterator[int]:
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
    a = a % mod if mod else a
    b = b % mod if mod else b
    while True:
        yield a
        a, b = b, a + b
        b = b % mod if mod else b



### Polygonal Numbers

def triangle(i: int) -> int:
    """
    Return the i-th triangular number.
    """
    return i * (i + 1) // 2

def polygonal(s: int, i: int) -> int:
    """
    Return the i-th s-gonal number.
    """
    return (s - 2) * i * (i - 1) // 2 + i

def polygonal_index(s: int, n: int) -> int:
    """
    Find the index of n in the s-gonal numbers.
    Returns the largest integer i such that P(s, i) <= n.
    """
    if s == 2:
        return n
    else:
        return (isqrt(8 * n * (s - 2) + (s - 4) * (s - 4)) + s - 4) // (2 * (s - 2))

def polygonal_numbers(s: int, low: int = 1, high: int = None) -> Iterator[int]:
    """
    Generate all s-gonal numbers in the range [low, high].
    """
    i = polygonal_index(s, low - 1) + 1
    n = polygonal(s, i)
    while high is None or n <= high:
        yield n
        n += (s - 2) * i + 1
        i += 1

def is_polygonal(s: int, n: int) -> bool:
    """
    Check if n is an s-gonal number.
    """
    if s == 2:
        return True

    D = 8 * n * (s - 2) + (s - 4) * (s - 4)
    sqrt_D = isqrt(D)
    return sqrt_D*sqrt_D == D and (sqrt_D + s - 4) % (2*s - 4) == 0

def is_square(n: int) -> bool:
    """
    Check if an integer n is a square.
    """
    return n >= 0 and (n & 0xF) in (0, 1, 4, 9) and (sqrt_n := isqrt(n)) * sqrt_n == n

def non_squares(N: int) -> Iterator[int]:
    """
    Return all non-square positive integers <= N.
    """
    return (n for n in range(2, N + 1) if not is_square(n))

def squares(low: int = 0, high: int = None) -> Iterator[int]:
    """
    Generate square numbers in the range [low, high].
    """
    low, high = max(low, 0), high if high is not None else float('inf')
    i = isqrt(low)
    while (n := i*i) < low:
        i += 1
    while n <= high:
        yield n
        n += 2*i + 1
        i += 1

def cubes(low: int = 0, high: int = None) -> Iterator[int]:
    """
    Generate cube numbers in the range [low, high].
    """
    high = high if high is not None else float('inf')
    i = iroot(low, 3)
    while (n := i*i*i) < low:
        i += 1
    while n <= high:
        yield n
        n += 3*i*i + 3*i + 1
        i += 1



### Graphs

Node = Hashable

def dijkstra(
    source: Node,
    neighbors_fn: Callable[[Node], Iterable[Node]],
    edge_weight_fn: Callable[[Node, Node], float],
) -> tuple[dict[Node, float], dict[Node, Node]]:
    """
    Use Dijkstra's algorithm to find the shortest path from a source node
    to all other nodes in a graph.

    Parameters
    ----------
    source : Node
        Source node
    neighbors_fn : Callable(Node) -> Iterable[Node]
        Function that returns all neighbors of a given node.
    edge_weight_fn : Callable(Node, Node) -> float
        Function that returns the weight of the edge between two nodes.

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
        dist_u, u = heappop(queue)
        if dist_u > dist[u]:
            continue
        for v in neighbors_fn(u):
            alt = dist[u] + edge_weight_fn(u, v)
            if alt < dist[v]:
                dist[v], prev[v] = alt, u
                heappush(queue, (alt, v))

    return dist, prev

def bron_kerbosch(
    graph: dict[Node, set[Node]],
    R: set[Node] = None,
    P: set[Node] = None,
    X: set[Node] = None,
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
    P : set[Node]
        Nodes that can be added to clique
    X : set[Node]
        Nodes to be excluded from clique

    Returns
    -------
    maximal_cliques : list[set[Node]]
        List of maximal cliques in the graph
    """
    R = set() if R is None else R
    P = set(graph.keys()) if P is None else P
    X = set() if X is None else X

    maximal_cliques = []
    if not P and not X:
        maximal_cliques.append(R)

    # Choose pivot node u to maximize |P ∩ N(u)|
    u = max(P | X, key=lambda v: len(graph[v]), default=None)
    candidates = P - (graph[u] if u is not None else set())

    # Explore candidates
    for v in candidates:
        maximal_cliques += bron_kerbosch(graph, R | {v}, P & graph[v], X & graph[v])
        P.remove(v); X.add(v)

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
    parent, rank = {v: v for v in nodes}, defaultdict(int)

    # Path compression
    def find(x):
        if parent[x] != x:
            parent[x] = find(parent[x])
        return parent[x]

    # Union by rank
    def union(x, y):
        root_x, root_y = find(x), find(y)
        if root_x == root_y:
            return False
        if rank[root_x] < rank[root_y]:
            parent[root_x] = root_y
        elif rank[root_x] > rank[root_y]:
            parent[root_y] = root_x
        else:
            parent[root_y] = root_x
            rank[root_x] += 1
        return True

    minimum_spanning_tree = []
    for u, v in sorted(edges, key=lambda edge: get_edge_weight(*edge)):
        if union(u, v):
            minimum_spanning_tree.append((u, v))

    return minimum_spanning_tree

def topological_sort(graph: dict[Node, Iterable[Node]]) -> list[Node]:
    """
    Perform a topological sort on a directed acyclic graph (DAG).
    Uses depth-first search.

    Parameters
    ----------
    graph : dict[Node, Iterable[Node]]
        Graph represented as an adjacency list
    """
    visited, current_path, order = set(), set(), []
    nodes = set(graph.keys()).union(*(set(neighbors) for neighbors in graph.values()))
    for start in nodes:
        if start in visited:
            continue

        # Maintain a stack of (node, state) tuples
        # where state takes on values: 0 = enter, 1 = exit
        stack = [(start, 0)]
        while stack:
            v, state = stack.pop()
            if state == 0:
                # Skip visited nodes and detect cycles
                if v in visited:
                    continue
                if v in current_path:
                    raise ValueError("Detected cycle in graph.")

                # Schedule exit and push neighbors
                current_path.add(v)
                stack.append((v, 1))
                for u in graph.get(v, ()):
                    if u not in visited:
                        stack.append((u, 0))
            else:
                # Add node to topological ordering
                current_path.remove(v)
                visited.add(v)
                order.append(v)

    order.reverse()
    return order

def find_cycles(
    find_next: Callable[[list[Node]], Iterable[Node]] = lambda path: [],
    current_path: list[Node] = None,
) -> Iterator[list[Node]]:
    """
    Use DFS to find cycles in a graph.

    Parameters
    ----------
    find_next : Callable(list[Node]) -> Iterable[Node]
        Function that returns all candidates for the next node in the path
    current_path : list[Node]
        Current path in the graph
    """
    current_path = current_path or []
    for v in find_next(current_path):
        if v in current_path:
            yield current_path[current_path.index(v):]
        else:
            for cycle in find_cycles(find_next, current_path + [v]):
                yield cycle

def find_functional_cycles(
    f: Callable[[int], int],
    search: Iterable[int],
    domain: range,
    on_cycle: Callable[[int, int], None],
):
    """
    Find cycles in the functional graph defined by f(n).

    Parameters
    ----------
    f : Callable(int) -> int
        Function defining the graph
    search : Iterable[int]
        Starting points to search for cycles
    domain : range
        Range of valid nodes in the graph
    on_cycle : Callable(cycle_start: int, cycle_node: int)
        Callback function to call when a cycle is found
    """
    assert domain.step == 1, "domain must have step size 1"
    cycle_id, low = [None] * len(domain), domain.start

    for start in search:
        # Advance until we find a cycle
        x, i = start, start - low
        while x in domain and cycle_id[i] is None:
            cycle_id[i], x = start, f(x)
            i = x - low

        # If this is a new cycle, walk through it
        if x in domain and cycle_id[i] == start:
            y = x
            on_cycle(x, y)
            while (y := f(y)) != x:
                on_cycle(x, y)



### Linear Algebra

Matrix = list[list[Number]]
Vector = list[Number]

def linear_solve(A: Matrix, b: Vector) -> Vector:
    """
    Solve the system of linear equations given by Ax = b.

    Parameters
    ----------
    A : Matrix
        M × N matrix of coefficients
    b : Vector
        List of M values
    """
    assert len(A) == len(b)
    A = [[*coefs, value] for coefs, value in zip(A, b)]
    solutions = [row[-1] for row in _gauss_jordan(A)]
    return solutions

def identity_matrix(n: int) -> Matrix:
    """
    Return the n × n identity matrix.
    """
    return [[int(i == j) for j in range(n)] for i in range(n)]

def matrix_apply(function: Callable[[Number], Number], A: Matrix) -> Matrix:
    """
    Apply a function elementwise to a matrix A.
    """
    return [[function(x) for x in row] for row in A]

def matrix_transpose(A: Matrix) -> Matrix:
    """
    Return the transpose of matrix A.
    """
    return [list(col) for col in zip(*A)]

def matrix_sum(A: Matrix, B: Matrix) -> Matrix:
    """
    Return A + B.
    """
    return _matrix_binary_op(A, B, op=lambda a, b: a + b)

def matrix_difference(A: Matrix, B: Matrix) -> Matrix:
    """
    Return A - B.
    """
    return _matrix_binary_op(A, B, op=lambda a, b: a - b)

def matrix_product(A: Matrix, B: Matrix) -> Matrix:
    """
    Return the product of two matrices A and B.
    """
    assert len(A[0]) == len(B), "Matrix dimensions do not match"
    return [[sum(a*b for a, b in zip(row, col)) for col in zip(*B)] for row in A]

def _matrix_binary_op(
    A: Matrix,
    B: Matrix,
    op: Callable[[Number, Number], Number],
) -> Matrix:
    """
    Apply a binary operation elementwise to two matrices A and B.
    """
    assert len(A) == len(B) and len(A[0]) == len(B[0]), "Matrix dimensions do not match"
    return [[op(a, b) for a, b in zip(row_a, row_b)] for row_a, row_b in zip(A, B)]

def _gauss_jordan(A: Matrix) -> Matrix:
    """
    Gauss-Jordan elimination. Returns the given matrix in reduced row-echelon form.
    """
    num_rows, num_cols = len(A), len(A[0])
    row = col = 0
    while row < num_rows and col < num_cols - 1:
        # Find pivot in current column
        pivot_row = max(range(row, num_rows), key=lambda r: abs(A[r][col]))
        if A[pivot_row][col] == 0:
            col += 1
            continue

        # Move pivot row into position and normalize it
        A[row], A[pivot_row] = A[pivot_row], A[row]
        pivot = A[row][col]
        A[row] = [value / pivot for value in A[row]]

        # Eliminate the current column from all other rows
        for r in range(num_rows):
            if r == row: continue
            if (k := A[r][col]) == 0: continue
            A[r] = [value - k * pivot_value for value, pivot_value in zip(A[r], A[row])]

        row += 1
        col += 1

    return A



### Constraint Satisfaction

def csp(
    variables: dict[Hashable, Any | None],
    values_fn: Callable[[Hashable, dict[Hashable, Any | None]], Sequence],
    *,
    all_solutions: bool = False,
) -> (
    dict[Hashable, Any | None]
    | list[dict[Hashable, Any | None]]
    | None
):
    """
    Find a solution to the given constraint satisfaction problem.
    Uses backtracking with minimum remaining values heuristic.

    Parameters
    ----------
    variables : dict[Hashable, Any | None]
        Dictionary mapping variable keys to their assigned values
        (or None if unassigned)
    values_fn : Callable(Hashable, dict) -> Sequence
        Function that returns the possible values for a given variable key given
        the current variable assignments (i.e. `values = values_fn(key, variables)`)
    all_solutions : bool
        When True, return all possible solutions instead of the first solution
    """
    variables = variables.copy()
    solutions: list[dict[Hashable, Any | None]] | None = [] if all_solutions else None

    def backtrack():
        # Select variable with minimum remaining values
        best_key = best_values = None
        for key in variables:
            if variables[key] is not None:
                continue
            if not (values := values_fn(key, variables)):
                return False
            if best_key is None or len(values) < len(best_values):
                best_key, best_values = key, values
                if len(best_values) == 1:
                    break

        # Check if all variables are assigned
        if best_key is None:
            if all_solutions:
                assert solutions is not None
                solutions.append(variables.copy())
                return False
            return True

        # Try each possible value for the selected variable
        for value in best_values:
            variables[best_key] = value
            if backtrack(): return True
            variables[best_key] = None

        return False

    solved = backtrack()
    if all_solutions:
        return solutions
    return variables if solved else None



### Digits

def digit_sum(n: int) -> int:
    """
    Return the sum of the digits in the decimal integer n.
    """
    n = abs(n)
    mod = _int_str_mod()
    total = 0
    while n > 0:
        n, r = divmod(n, mod)
        total += sum(map(int, str(r)))

    return total

def digit_count(n: int) -> int:
    """
    Return the number of digits in the decimal integer n.
    """
    n = abs(n)
    if n < _int_str_mod(): return len(str(n))
    return ilog(n, 10) + 1 if n != 0 else 1

def digit_combinations(max_digits: int) -> Iterator[tuple[int, int]]:
    """
    Generate unique digit combinations as integers.

    Parameters
    ----------
    max_digits : int
        Maximum number of digits in the combinations

    Yields
    ------
    a : int
        Digit combination as an integer
    count : int
        Number of unique permutations of the digit combination
    """
    factorials = [factorial(i) for i in range(max_digits + 1)]
    for d in range(1, max_digits + 1):
        for digits in itertools.combinations_with_replacement(string.digits, d):
            i = next((i for i, ch in enumerate(digits) if ch != '0'), None)
            if i is None: continue # skip all-zero case
            digit_counts = Counter(digits)
            count = factorials[d - 1] * (d - digit_counts['0'])
            count //= prod(map(factorials.__getitem__, digit_counts.values()))
            yield int(''.join(digits[i:] + digits[:i])), count

def digit_permutations(n: int) -> Iterator[int]:
    """
    Generate all unique permutations of the digits in integer n.

    Parameters
    ----------
    n : int
        Integer whose digit to permute
    """
    digits = f'{abs(n)}'
    sign = -1 if n < 0 else 1

    # Fast path: all digits distinct -> just use permutations
    if len(set(digits)) == len(digits):
        for p in itertools.permutations(digits):
            if p[0] != '0':
                yield sign * int(''.join(p))
        return

    # General path: multiset permutations via digit counts
    counts, length = Counter(map(int, digits)), len(digits)

    def backtrack(pos: int, cur: int) -> Iterator[int]:
        if pos == length:
            yield sign * cur
            return
        for d in counts:
            if counts[d] and (pos or d): # no leading zero
                counts[d] -= 1
                yield from backtrack(pos + 1, cur * 10 + d)
                counts[d] += 1

    yield from backtrack(0, 0)

def digits_in_base(n: int, b: int) -> tuple[int, ...]:
    """
    Return the digits of integer n in base b,
    from least significant digit to most significant digit.
    """
    if n == 0:
        return (0,)

    # Long division to extract digits
    digits, abs_b, abs_n = [], abs(b), abs(n)
    while abs_n > 0:
        abs_n, r = divmod(abs_n, abs_b)
        digits.append(r)

    # Handle negative base
    if b < 0:
        for i in range(len(digits)):
            if digits[i] != 0 and i % 2 == 1:
                digits[i] = abs_b - digits[i]
                if i + 1 == len(digits):
                    digits.append(1)
                else:
                    digits[i + 1] += 1

    return tuple(digits)

def is_palindrome(n: int) -> bool:
    """
    Check if an integer is a palindrome.
    """
    return (s := f'{n}') == s[::-1]

def is_permutation(a: int, b: int) -> bool:
    """
    Check if two integers are permutations of each other.
    """
    return sorted(f'{a}') == sorted(f'{b}')

def has_repeated_digits(n: int) -> bool:
    """
    Check if an integer has any repeated digits.
    """
    return len(set(s := f'{n}')) < len(s)



### Miscellaneous

def nth(iterable: Iterable, n: int, default: Any = None) -> Any:
    """
    Return the n-th item from an iterable (1-based index).
    If the iterable has fewer than n items, return default.
    """
    return next(itertools.islice(iterable, n - 1, None), default)

def group_by_key(
    iterable: Iterable,
    key: Callable[[Any], Hashable],
) -> dict[Hashable, list]:
    """
    Group items in an iterable by a given key function.
    Returns a dictionary mapping each key to a list of items with that same key.

    Parameters
    ----------
    iterable : Iterable
        Items to group
    key : Callable(item) -> key
        Function that returns the key for each item
    """
    groups = defaultdict(list)
    for item in iterable:
        groups[key(item)].append(item)

    return groups

def group_permutations(iterable: Iterable[Sequence]) -> Iterable[list[Sequence]]:
    """
    Group permutations together.

    Returns a collection of lists of permutations, where for any given list,
    all its items are permutations of each other.

    Parameters
    ----------
    iterable : Iterable[Sequence]
        Sequences to group
    """
    key = lambda sequence: tuple(sorted(sequence))
    return iter(group_by_key(iterable, key=key).values())

def powerset(iterable: Iterable) -> Iterable[tuple]:
    """
    Generate all subsets of the given iterable as tuples, in order of increasing size.
    """
    iterable = list(iterable)
    return itertools.chain.from_iterable(
        itertools.combinations(iterable, n)
        for n in range(len(iterable) + 1)
    )

def disjoint_subset_pairs(
    iterable: Iterable,
    include_empty: bool = False,
    equal_size_only: bool = False,
) -> Iterable[tuple[tuple, tuple]]:
    """
    Generate all pairs of disjoint subsets from the given iterable.

    Parameters
    ----------
    iterable : Iterable
        Items to form subsets from
    include_empty : bool
        Whether to include the empty set as a valid subset
    equal_size_only : bool
        Whether to only include pairs of subsets with the same size
    """
    items = list(iterable)
    idx = range(len(items))
    n = len(items)
    yield from (
        (tuple(items[i] for i in A_idx), tuple(items[i] for i in B_idx))
        for i in range(0 if include_empty else 1, n // 2 + 1)
        for j in range(i, i + 1 if equal_size_only else n + 1)
        for A_idx in itertools.combinations(idx, i)
        for A_idx_set in (set(A_idx),)
        for B_idx in itertools.combinations((x for x in idx if x not in A_idx_set), j)
        if i != j or i == 0 or A_idx[0] <= B_idx[0]
    )

def polynomial(coefficients: Sequence[Number]) -> Callable[[Number], Number]:
    """
    Create a polynomial function with the given coefficients (a_0, ..., a_n).
    Uses Horner's method for polynomial evaluation.
    """
    def horner(x: Number) -> Number:
        b = 0
        for a in reversed(coefficients): b = a + b*x
        return b

    return horner

def iroot(x: float, n: int = 2) -> int:
    """
    Find the integer n-th root of x.
    Returns the largest integer a such that a^n <= x.
    Uses Newton's method.
    """
    if x < 0:
        if n % 2 == 0:
            raise ValueError("Cannot compute even root of negative number")
        return -iroot(-x - 1, n) - 1
    elif x == 0:
        return 0

    x = int(x)
    a, b = x, x + 1
    while a < b:
        b = a
        t = (n - 1) * b + x // pow(b, n - 1)
        a = t // n

    return b

def ilog(a: int, b: int = 2) -> int:
    """
    Find the integer logarithm of a with base b.
    Returns the largest integer n such that b^n <= a.
    Uses repeated squaring and binary search.
    """
    if a < 1 or b < 2:
        raise ValueError("Invalid input for integer logarithm")

    # Find upper bound
    exp, power = 1, b
    while power <= a:
        exp, power = exp * 2, power * power

    # Binary search for exact exponent
    low, high = 0, exp
    while low < high:
        mid = (low + high) // 2
        power = pow(b, mid)
        if power <= a:
            low = mid + 1
        else:
            high = mid

    return low - 1

def binary_search(
    f: Callable[[int], int],
    threshold: int,
    low: int = 0,
    high: int = None,
) -> int:
    """
    Given a monotonically increasing function f, find where it crosses a threshold.
    Returns the smallest integer n in [low, high] such that f(n) >= threshold.
    """
    if high is None:
        span = 1
        while f(low + span) < threshold: span *= 2
        high = low + span

    return low + bisect.bisect_left(range(low, high + 1), threshold, key=f)



### Fenwick Trees

def _fenwick_tree_init(values: Iterable[Number]) -> list[Number]:
    """
    Create a Binary Indexed Tree (Fenwick Tree) from the given values.
    """
    tree = list(values)
    for index, parent_index in _fenwick_tree_edges(len(tree)):
        tree[parent_index] += tree[index]

    return tree

def _fenwick_tree_query(tree: list[Number], index: int) -> Number:
    """
    Query the prefix sum for the tree at the given index.
    """
    count = 0
    for i in _fenwick_tree_query_path(index):
        count += tree[i]

    return count

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
def _fenwick_tree_edges(tree_size: int) -> list[tuple[int, int]]:
    """
    Get all (index, parent_index) pairs for a Binary Indexed Tree (Fenwick Tree).
    """
    return [
        (index, index | (index + 1))
        for index in range(tree_size - 1)
        if index | (index + 1) < tree_size
    ]

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
    num_digits = getattr(sys, 'get_int_max_str_digits', lambda: 0)()
    return 10**min(num_digits or 10000, 10000)

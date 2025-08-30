import functools
import itertools
import math
import string
import util

from collections import Counter, defaultdict
from functools import cache
from heapq import heappop, heappush
from itertools import combinations, permutations
from math import ceil, comb, factorial, floor, gcd, isqrt, lcm, log, prod, sqrt



def problem_1(N=1000, divisors=(3, 5)):
    """
    Find the sum of all multiples below N of any of the given divisors.

    Notes
    -----
    The sum of the first n multiples of k is equal to k * T_n,
    where T_n is the n-th triangular number.

    From there we can use the principle of inclusion-exclusion to find the sum
    of all multiples of the given divisors below N.
    """
    sum_of_multiples = lambda k: k * util.polygonal(3, (N - 1) // k)
    return sum(
        (-1)**(i + 1) * sum_of_multiples(lcm(*subset))
        for i in range(1, len(divisors) + 1)
        for subset in itertools.combinations(divisors, i)
    )

def problem_2(N=int(4e6)):
    """
    Find the sum of all even Fibonacci numbers below N.

    Notes
    -----
    F(n) is even if and only if n is a multiple of 3.
    The sum of F(3i) from i = 1 ... n = (F(3n+2) - 1) / 2.
    """
    n = int(util.fibonacci_index(N - 1)) // 3
    return (util.fibonacci(3*n + 2) - 1) // 2

def problem_3(n=600851475143):
    """
    Find the largest prime factor of n.
    """
    return max(util.prime_factors(n))

def problem_4(n=3, num_leading_nines=None):
    """
    Find the largest palindrome that is the product of two n-digit numbers.

    Notes
    -----
    Assume that the solution x * y is a palindrome with 2n digits.

    Let k <= n be a lower bound on the # of consecutive digits of 9 that start and end
    the palindrome. This implies the following:

        * both x, y > (10^k - 1) * 10^(n-k) (since x, y must each also start with k 9s)
        * xy = -1 mod 10^k (since xy ends with k 9s)
        * one of x, y is divisible by 11 (xy is a palindrome with even # of digits)

    We use the heuristic lower bound k = ⌊n / 2⌋ (provably holds when n is even).
    """
    # Special case
    if n == 1:
        return 9

    best_palindrome = None
    k = num_leading_nines or n // 2 # lower bound on # of leading / trailing 9s
    mod = 10**k # modulus for finding modular inverse
    min_palindrome = 10**(2*n) - 10**(2*n-k) + 10**k - 1 # starts & ends with k 9s
    max_factor = 10**n - 1 # largest n-digit number

    # Iterate x over odd multiples of 11
    x_min = min_palindrome // max_factor
    x_max = util.round_down(max_factor - 11, 22) + 11
    for x in range(x_max, x_min - 1, -22):
        # Find modular inverse of x mod 10^k
        if x % 5 == 0:
            continue # no inverse exists if gcd(x, 10^k) != 1
        else:
            x_inv = pow(x, -1, mod=mod)

        # Iterate y over integers such that xy = -1 mod 10^k (i.e. xy ends with k 9s)
        y_min = (best_palindrome or min_palindrome) // x
        y_max = max_factor + 1 - x_inv
        for y in range(y_max, y_min - 1, -mod):
            if util.is_palindrome(product := x * y):
                best_palindrome = product
                break

        if x * max_factor < (best_palindrome or min_palindrome):
            break

    if best_palindrome is None and k > 0:
        return problem_4(n, num_leading_nines=k-1)
    else:
        return best_palindrome

def problem_5(n=20):
    """
    Find the smallest number that is evenly divisible by all numbers from 1 to n.

    Notes
    -----
    LCM(1, ... n) = product of p^⌊log_p(n)⌋ for p <= n.
    """
    return prod(p**int(log(n, p)) for p in util.primes(high=n))

def problem_6(n=100):
    """
    Find the difference (1 + 2 + ... + n)^2 - (1^2 + 2^2 + ... + n^2).

    Notes
    -----
    We can apply Faulhaber's formula for k = 1 and k = 2.
    The sum of the first n natural numbers is n * (n + 1) / 2.
    The sum of the first n squares is n * (n + 1) * (2n + 1) / 6.
    """
    square_of_sums = (n * (n + 1) // 2) ** 2
    sum_of_squares = n * (n + 1) * (2*n + 1) // 6
    return square_of_sums - sum_of_squares

def problem_7(n=10001):
    """
    Find the n-th prime number.
    """
    return list(util.primes(num=n))[-1]

def problem_8(n=13, path='data/problem_8.txt'):
    """
    Given a string of digits, find the largest product of n consecutive digits.

    Notes
    -----
    We can ignore any subsequence containing a zero.
    """
    with open(path) as file:
        digits = ''.join(line.strip() for line in file.readlines())

    # Split into subsequences of nonzero digits of length at least n
    sub_seqs = [list(map(int, s)) for s in digits.split('0') if len(s) >= n]
    if len(sub_seqs) == 0:
        return 0

    # Find the maximum of the max products in each subsequence
    return max(max([prod(s[i:i+n]) for i in range(len(s) - n + 1)]) for s in sub_seqs)

def problem_9(n=1000):
    """
    Find the product abc of a Pythagorean triple (a, b, c) where a + b + c = n.

    Notes
    -----
    Euclid's formula generates all primitive Pythagorean triples:
    a = x^2 - y^2, b = 2xy, c = x^2 + y^2, for all x > y > 0 where gcd(x, y) = 1
    and exactly one of x, y is even.

    Thus for any Pythagorean triple (ka, kb, kc) with perimeter n,
    we have n = ka + kb + kc = 2kx(x + y), with x, y satisfying the above conditions.

    This implies that n must be even, and x, (x + y) must be factors of n/2.
    """
    if n % 2 != 0:
        return None

    factors = sorted(util.divisors(n // 2))
    for i in range(1, len(factors) // 2):
        for j in range(i + 1, len(factors) - 1):
            x, y = factors[i], factors[j] - factors[i]
            if x > y and (x + y) % 2 == 1 and gcd(x, y) == 1: # primitive conditions
                a, b, c = x*x - y*y, 2*x*y, x*x + y*y # primitive triple
                k = n // (a + b + c)
                return k*a * k*b * k*c

def problem_10(N=int(2e6)):
    """
    Find the sum of all primes below N.
    """
    return sum(util.primes(high=N-1))

def problem_11(n=4, path='data/problem_11.txt'):
    """
    Find the largest product of k consecutive numbers in a grid.
    """
    # Load grid
    with open(path) as file:
        grid = [[int(i) for i in line.strip().split()] for line in file.readlines()]
        H, W = len(grid), len(grid[0])

    # Generate rows, columns, diagonals, and antidiagonals
    rows, cols = [[] for _ in range(H)], [[] for _ in range(W)]
    diagonals = [[] for _ in range(H + W - 1)]
    anti_diagonals = [[] for _ in range(H + W - 1)]
    for r in range(H):
        for c in range(W):
            rows[r].append(grid[r][c])
            cols[c].append(grid[r][c])
            diagonals[r + c].append(grid[r][c])
            anti_diagonals[H - r + c - 1].append(grid[r][c])

    # Find max product of sub-segment of length k
    segments = rows + cols + diagonals + anti_diagonals
    return max(
        prod(segment[i:i+n])
        for segment in segments
        for i in range(len(segment) - n)
    )

def problem_12(D=500):
    """
    Find the smallest triangle number with more than D divisors.

    Notes
    -----
    If gcd(a, b) = 1, then d(ab) = d(a)d(b), where d(n) is the # of divisors of n.
    For all positive integers n we have gcd(n, n + 1) = 1.
    """
    i, divisor_counts = 0, util.get_divisor_counts(2)
    while True:
        # Add more divisor counts if necessary
        if i >= len(divisor_counts) - 1:
            divisor_counts = util.get_divisor_counts(2 * i)

        # Calculate the number of divisors for the i-th triangle number
        if i % 2 == 0:
            num_divisors = divisor_counts[i // 2] * divisor_counts[i + 1]
        else:
            num_divisors = divisor_counts[(i + 1) // 2] * divisor_counts[i]

        # Check if the number of divisors exceeds n
        if num_divisors > D:
            return util.polygonal(3, i)
        else:
            i += 1

def problem_13(n=10, path='data/problem_13.txt'):
    """
    Find the first n digits of the sum of the given numbers.
    """
    with open(path) as file:
        return str(sum(map(int, file.readlines())))[:n]

def problem_14(N=int(1e6)):
    """
    Find the number below N that produces the longest Collatz sequence.

    Notes
    ----
    If n < N/2, then 2n has a longer sequence than n, so we need only look for n >= N/2.
    """
    @functools.cache
    def collatz(n):
        if n <= 2:
            return n
        elif n % 4 == 0:
            return collatz(n // 4) + 2
        elif n % 4 == 1 or n % 4 == 2:
            return collatz(n - n // 4) + 3
        else:
            return collatz(9 * (n - 3) // 4 + 8) + 4

    return max(range(N // 2 + 1, N), key=collatz)

def problem_15(H=20, W=20):
    """
    Find the number of paths from the top-left to bottom-right corner of a grid.

    Notes
    -----
    We need to make H + W moves in total, H of which are down and W of which are right.
    The number of different ways we can do this is (H + W) choose H.
    """
    return comb(H + W, H)

def problem_16(n=1000):
    """
    Find the sum of the digits of 2^n.
    """
    return util.get_digit_sum(2**n)

def problem_17(N=1000):
    """
    Find the number of letters used to write out the numbers 1 to N in words.
    """
    digits = {
        0: '', 1: 'one', 2: 'two', 3: 'three', 4: 'four',
        5: 'five', 6: 'six', 7: 'seven', 8: 'eight', 9: 'nine',
    }
    teens = {
        10: 'ten', 11: 'eleven', 12: 'twelve', 13: 'thirteen', 14: 'fourteen',
        15: 'fifteen', 16: 'sixteen', 17: 'seventeen', 18: 'eighteen', 19: 'nineteen',
    }
    tens = {
        2: 'twenty', 3: 'thirty', 4: 'forty', 5: 'fifty',
        6: 'sixty', 7: 'seventy', 8: 'eighty', 9: 'ninety',
    }

    def int_to_words(n: int) -> str:
        if n in digits:
            return digits[n]
        elif n in teens:
            return teens[n]
        elif n < 100:
            return tens[n // 10] + digits[n % 10]
        elif n < 1000:
            return digits[n // 100] + 'hundred' + (
                'and' + int_to_words(n % 100) if n % 100 > 0 else '')
        elif n < int(1e6):
            return int_to_words(n // 1000) + 'thousand' + int_to_words(n % 1000)

    return sum(len(int_to_words(n)) for n in range(1, N + 1))

def problem_18(path='data/problem_18.txt'):
    """
    Find the maximum sum of a path from the top to the bottom of a triangle.
    """
    with open(path) as file:
        pyramid = [list(map(int, line.strip().split(' '))) for line in file.readlines()]

    # Calculate path sums via dynamic programming
    # where pyramid[i][j] is max sum from (i, j) to bottom
    for i in range(len(pyramid) - 2, -1, -1):
        for j in range(len(pyramid[i])):
            pyramid[i][j] += max(pyramid[i + 1][j], pyramid[i + 1][j + 1])

    return pyramid[0][0]

def problem_19(start_year=1901, end_year=2000):
    """
    How many Sundays fell on the first of the month during the 20th century?
    """
    import datetime
    dates = [
        datetime.date(year, month=month, day=1)
        for year in range(start_year, end_year + 1)
        for month in range(1, 12 + 1)
    ]

    return len([date for date in dates if date.weekday() == 6]) # Sunday

def problem_20(n=100):
    """
    Find the sum of the digits in the number n!.
    """
    return util.get_digit_sum(factorial(n))

def problem_21(N=10000):
    """
    Find the sum of all amicable numbers below N.
    """
    d = util.get_divisor_sums(N, proper=True)
    return sum(n for n in range(N) if d[n] < N and n != d[n] and d[d[n]] == n)

def problem_22(path='data/problem_22.txt'):
    """
    Find the sum of the name scores in the given file,
    where the score of the n-th name is n times the sum of its character values
    ('a' = 1, 'b' = 2, etc).
    """
    with open(path) as file:
        names = [name.strip('"') for name in ''.join(file.readlines()).split(',')]
        names = sorted(names)

    char_values = {c: ord(c) - ord('A') + 1 for c in string.ascii_uppercase}
    name_values = [sum(map(char_values.__getitem__, name)) for name in names]
    return sum((i + 1) * value for i, value in enumerate(name_values))

def problem_23(N=28123):
    """
    Find the sum of all the positive integers below N which cannot be written
    as the sum of two abundant numbers.

    Notes
    -----
    Every multiple of 6 above 6 is abundant (since 6 is a perfect number).

    Then if a_k is the smallest abundant number congruent to k mod 6, it follows that
    a_k + 6i is abundant for all integers i > 1.

    We can also verify that all abundant numbers below 28123 are 0, 2, 3, or 4 mod 6.

    Then if n = 1 mod 6 is an abundant sum, the two summands must 3 and 4 mod 6,
    and if n = 5 mod 6 is an abundant sum, the two summands must be 3 and 2 mod 6.
    """
    N = min(N, 28123) # all numbers above 28123 are abundant sums

    # Calculate the sum of proper divisors for n = 1 ... N
    proper_divisor_sum = util.get_divisor_sums(N, proper=True)

    # Get abundant numbers (grouped mod 6)
    is_abundant = lambda n: n > 0 and proper_divisor_sum[n] > n
    abundant_numbers = [n for n in range(12, N) if is_abundant(n)]
    abundant_numbers = {
        i: [n for n in abundant_numbers if n % 6 == i]
        for i in range(6)
    }

    # Find abundant sums (0, 2, 3, or 4 mod 6)
    abundant_sums = {
        *range(12 + min(abundant_numbers[0]), N, 6), # 0 mod 6
        *range(12 + min(abundant_numbers[2]), N, 6), # 2 mod 6
        *range(12 + min(abundant_numbers[3]), N, 6), # 3 mod 6
        *range(12 + min(abundant_numbers[4]), N, 6), # 4 mod 6
        *([40] if N > 40 else []) # edge case (40 = 20 + 20)
    }

    # Find abundant sums (1 or 5 mod 6)
    for n in range(N):
        if n % 6 in (1, 5):
            if any(is_abundant(n - a) for a in abundant_numbers[3]):
                abundant_sums.add(n)

    return sum(n for n in range(N) if n not in abundant_sums)

def problem_24(n=int(1e6)):
    """
    Find the n-th lexicographic permutation of the digits 0-9.

    Notes
    -----
    There are 9! permutations starting with 0, another 9! starting with 1, etc.
    Within each group of 9! permutations, there are 8! permutations where the next
    digit is 0, another 8! permutations where the next digit is 1, etc.
    """
    a, remaining_digits, permutation = n - 1, list(range(10)), []
    while remaining_digits:
        i, a = divmod(a, factorial(len(remaining_digits) - 1))
        permutation.append(remaining_digits.pop(i))

    return ''.join(map(str, permutation))

def problem_25(n=1000000):
    """
    Find the index of the smallest n-digit Fibonacci number.
    """
    return ceil(util.fibonacci_index(10, n - 1))

def problem_26(N=1000):
    """
    Find the integer reciprocal 1/n with the longest decimal repetend.

    Notes
    -----
    The length L(n) of the decimal repetend of 1/n always divides φ(n),
    where φ is the totient function, with equality if and only if
    10 is a primitive root mod n.

    The totient function is maximized for primes, where φ(p) = p - 1.
    """
    def is_primitive_root(g: int, n: int) -> bool:
        """
        Check if g is a primitive root modulo n.
        """
        k = util.totient(n)
        return all(pow(g, k // p, mod=n) != 1 for p in set(util.prime_factors(k)))

    # Check primes in descending order
    for n in range(N, 1, -1):
        if util.is_prime(n) and is_primitive_root(10, n):
            return n

def problem_27(N=1000):
    """
    Find the product of coefficients a, b where |a|, |b| <= N such that the
    quadratic expression f(x) = x^2 + ax + b produces the maximum number of primes
    for consecutive integer values of x, starting with x = 0.

    Notes
    -----
    We know that f(0) = b must be prime, and f(1) = 1 + a + b must be prime.
    We can also infer the bounds f(0) <= N and f(1) <= 2N + 1.
    """
    f = lambda a, b, x: x*x + a*x + b
    prime_list = list(util.primes(high=2*N+1))

    # Iterate over a, b such that f(0) and f(1) are prime by construction
    max_x, best_a, best_b = 0, 0, 0
    for f0 in prime_list:
        if f0 > N: break
        for f1 in prime_list:
            a, b = f1 - f0 - 1, f0
            x = 2 # start with f(2), since we already know f(0) and f(1) must be prime
            while util.is_prime(f(a, b, x)):
                x += 1
            if x > max_x:
                max_x, best_a, best_b = x, a, b

    return best_a * best_b

def problem_28(n=1001):
    """
    Find the sum of the numbers on the diagonals of the n x n Ulam spiral.

    Notes
    -----
    We can represent the sum for an n x n spiral via recurrence S(n),
    where S(1) = 1 and S(2n + 1) = S(2n - 1) + 4n^2 + 10n + 10.

    Solving the recurrence: S(2n + 1) = (16n^3 + 30n^2 + 26n + 3) / 3
    Or alternatively: S(n) = (4n^3 + 3n^2 + 8n - 9) / 6
    """
    assert n % 2 == 1
    return (4*n**3 + 3*n**2 + 8*n - 9) // 6

def problem_29(n=100):
    """
    Given integers 2 <= a,b <= n, find the number of distinct values of a^b.

    Notes
    -----
    We will say that a ∈ ℕ has "exponential order k" if k is the largest integer
    for which there exists some c ∈ ℕ such that a = c^k.

    Thus k <= 2, the order-k integers are 2^k, 3^k, 5^k, 6^k, 7^k, 10^k, etc.
    Instances like 4^k or 8^k are of order 2k and 3k respectively.

    Notice that for each a of order k, the number of distinct values of a^b
    is the same (e.g. 2^k, 3^k, 5^k, 6^k, ... all have the same count).

    It suffices to calculate the number of distinct values of a^b for each order k.

    Let a be an order-k integer. Then the duplicates are of the form a^b,
    where b = m * lcm(j, k) / k for j = 1 ... k - 1 and m = 1 ... n * j / lcm(j, k).
    """
    # Store the number of duplicates for each exponential order k
    num_duplicates = {1: 0}
    for k in range(2, floor(log(n, 2)) + 1):
        is_duplicate = [False] * n
        for j in range(1, k):
            stop, step = (n * j) // k + 1, lcm(j, k) // k
            is_duplicate[0:stop:step] = [True] * len(is_duplicate[0:stop:step])

        num_duplicates[k] = sum(is_duplicate[2:])

    # Calculate exponential order of each base integer a
    exp_order = {}
    for a in range(2, n + 1):
        for k in range(1, round(log(n, a)) + 1):
            x = a**k
            if x not in exp_order:
                exp_order[x] = k

    # Get total number of distinct powers
    total_num_duplicates = sum([num_duplicates[exp_order[a]] for a in range(2, n + 1)])
    return (n - 1) * (n - 1) - total_num_duplicates

def problem_30(n=5):
    """
    Find the sum of all numbers (>= 2 digits) that can be written as the sum of the
    n-th powers of their digits.

    Notes
    -----
    A k-digit number is at least 10^(k-1), and the sum of n-th powers of
    a k-digit number is at most k * 9^n. This means we can upper bound the
    number of digits by the largest k satisfying 10^(k-1) <= k * 9^n.

    Notice that there are at most ((10 + k - 1) choose k) unique digit power sums,
    as the order of the digits doesn't matter.
    """
    digit_powers = {str(d): d**n for d in range(10)}
    digit_power_sum = lambda digits: sum(map(digit_powers.__getitem__, digits))

    # Find upper bound on number of digits
    k = 2
    while 10**k <= (k + 1) * 9**n:
        k += 1

    # Find numbers that satisfy the condition
    values = set()
    for digits in itertools.combinations_with_replacement(string.digits, k):
        a = digit_power_sum(digits)
        b = digit_power_sum(str(a))
        if a == b and a >= 10:
            values.add(a)

    return sum(values)

def problem_31(total=200, coin_values=[1, 2, 5, 10, 20, 50, 100, 200]):
    """
    How many different ways can the specified total be made using
    any number of coins from the given denominations?
    """
    return util.get_partition_numbers(total, values=coin_values)[-1]

def problem_32():
    """
    Find the sum of all products c = a * b such that abc is a 1-9 pandigital number.

    Notes
    -----
    Given a * b = c, if the total # of digits across a, b, c is 9,
    then c must have exactly 4 digits.

    Without loss of generality, assume a < b. Then a must have 1 or 2 digits,
    and b must have 3 or 4 digits.
    """
    digits = set('123456789')
    is_pandigital = lambda s: len(s) == len(digits) and set(s) == digits
    return sum({
        a * b
        for a in range(1, 98 + 1)
        for b in range(123, 9876 // a + 1)
        if is_pandigital(f'{a}{b}{a*b}')
    })

def problem_33():
    """
    Find the denominator of the product of all fractions that can be reduced
    by cancelling a nonzero digit from a 2-digit numerator & denominator.

    Notes
    -----
    We are looking for fractions of the form (10a + x) / (10x + b) = a / b,
    where 0 < a < b < 10 and 0 < x < 10.
    """
    fractions = [
        (10 * a + x, 10 * x + b)
        for a in range(1, 10)
        for b in range(a + 1, 10)
        for x in range(1, 10)
        if (10*a + x) * b == (10*x + b) * a
    ]

    numerator, denominator = (prod(group) for group in zip(*fractions))
    return denominator // gcd(numerator, denominator)

def problem_34():
    """
    Find the sum of all numbers that are equal to the
    sum of the factorial of their digits.

    Notes
    -----
    The sum of the factorial of the digits of a k-digit number is at most k * 9!.
    We have 10^(k-1) > k * 9! for k > 8, so we only need to check up to 7-digit numbers.

    Notice that there are at most ((10 + k - 1) choose k) unique digit factorial sums,
    as the order of the digits doesn't matter.
    """
    digit_factorials = {str(d): factorial(d) for d in range(10)}
    digit_factorial_sum = lambda digits: sum(map(digit_factorials.__getitem__, digits))

    values = set()
    for k in range(2, 7):
        for digits in itertools.combinations_with_replacement(string.digits, k):
            a = digit_factorial_sum(digits)
            b = digit_factorial_sum(str(a))
            if a == b and a >= 10:
                values.add(a)
    
    return sum(values)

def problem_35(N=int(1e6)):
    """
    Find the number of circular primes below N.

    Notes
    -----
    For k >= 2, all k-digit circular primes contain only the digits 1, 3, 7, 9.
    """
    to_integers = lambda iterable: map(int, map(''.join, iterable))

    # Get candidate primes with digits 1, 3, 7, 9
    prime_list = list(util.primes(high=min(9, N))) # single-digit primes
    for k in range(2, ceil(log(N, 10)) + 2):
        for n in to_integers(itertools.product('1379', repeat=k)):
            if n <= N and util.is_prime(n):
                prime_list.append(n)

    # Find circular primes
    circular_primes = []
    for p in prime_list:
        rotations = (int(str(p)[i:] + str(p)[:i]) for i in range(len(str(p))))
        if all(map(util.is_prime, rotations)):
            circular_primes.append(p)

    return len(circular_primes)

def problem_36(N=int(1e6)):
    """
    Find the sum of all numbers less than N which are palindromic in
    both base 2 and base 10.
    """
    max_num_digits = int(log(N - 1, 10)) + 1
    is_binary_palindrome = lambda n: bin(n)[2:] == bin(n)[2:][::-1]

    # Generate even-length decimal palindromes
    even_limit = 10**(max_num_digits // 2)
    palindromes = [int(f'{n}{str(n)[::-1]}') for n in range(1, even_limit)]

    # Generate odd-length decimal palindromes
    odd_limit = 10**((max_num_digits - 1) // 2)
    palindromes += list(range(1, 10))
    palindromes += [
        int(f'{n}{d}{str(n)[::-1]}')
        for n in range(1, odd_limit) for d in range(10)
    ]

    # Filter for binary palindromes
    return sum(n for n in palindromes if n < N and is_binary_palindrome(n))

def problem_37():
    """
    Find the sum of all primes that are both left-truncatable and right-truncatable.

    Notes
    -----
    If k-digit prime q is right-truncatable, then q = 10*p + d,
    where d is 1, 3, 7, or 9 and p is a (k-1)-digit right-truncatable prime.
    """
    is_left_truncatable = lambda p: all(
        util.is_prime(int(str(p)[i:]))
        for i in range(1, len(str(p)))
    )

    # Generate all right-truncatable primes
    right_truncatable_primes = list(util.primes(high=9)) # single-digit primes
    for k in itertools.count(start=1):
        k_digit_primes = [p for p in right_truncatable_primes if len(str(p)) == k]
        if len(k_digit_primes) == 0:
            break

        for p in k_digit_primes:
            for d in (1, 3, 7, 9): # cannot end in even digit or 5
                if util.is_prime(q := 10 * p + d):
                    right_truncatable_primes.append(q)

    # Filter for primes that are also left-truncatable
    truncatable_primes = [p for p in right_truncatable_primes if is_left_truncatable(p)]
    return sum(truncatable_primes) - sum(util.primes(high=9))

def problem_38():
    """
    What is the largest 1-9 pandigital number that can be formed as the
    concatenated product concat(a, 2a, ..., na) for some integer n > 1?
    """
    digits = set('123456789')
    concat_prod = lambda a, n: ''.join(str(a * i) for i in range(1, n + 1))
    is_pandigital = lambda s: len(s) == len(digits) and set(s) == digits
    has_repeated_digits = lambda n: len(set(str(n))) < len(str(n))

    # Find the largest pandigital concatenated product
    max_concat_prod = int(concat_prod(9, 5))
    for a in range(10000):
        # Skip numbers that cannot form a larger pandigital number
        num_digits = len(str(a))
        if a < max_concat_prod // 10**(9 - num_digits):
            continue
        if has_repeated_digits(a) or '0' in str(a):
            continue

        # Generate concatenated products
        for n in range(2, 9 // num_digits + 1):
            if is_pandigital(concat_prod(a, n)):
                max_concat_prod = max(max_concat_prod, int(concat_prod(a, n)))

    return max_concat_prod

def problem_39(N=1000):
    """
    Find p <= N that produces the most Pythagorean triples (a, b, c)
    with a + b + c = p.
    """
    counts = Counter(map(sum, util.pythagorean_triples(max_sum=N)))
    return max(range(N + 1), key=counts.__getitem__)

def problem_40(idx=(10**i for i in range(7))):
    """
    Find the product of the digits at the specified indices
    in Champernowne's constant.
    """
    idx, digits = sorted(idx), []
    n, current_index = 1, 0
    while idx:
        # Find the n-digit number containing the next desired index
        num, i = divmod(idx[0] - current_index - 1, n)
        num += 10**(n - 1)
        if num < 10**n:
            # Store the i-th digit of this number
            digits.append(int(str(num)[i]))
            idx.pop(0)
        else:
            # Update the current Champernowne index (i.e. append all n-digit numbers)
            current_index += 9 * 10**(n - 1) * n
            n += 1

    return prod(digits)

def problem_41():
    """
    Find the largest pandigital prime.

    Notes
    -----
    All n-digit pandigital numbers are divisible by 3 for n = 2, 3, 5, 6, 8, 9.
    """
    # Iterate over candidates in descending order
    for n in (7, 4):
        for digits in permutations(range(n, 0, -1)):
            a = int(''.join(map(str, digits)))
            if util.is_prime(a):
                return a

def problem_42(path='data/problem_42.txt'):
    """
    Find the number of words in a file for which the sum of their character values
    is a triangle number ('a' = 1, 'b' = 2, etc).
    """
    with open(path) as file:
        words = (word.strip('"') for word in ','.join(file.readlines()).split(','))

    char_values = {c: ord(c) - ord('A') + 1 for c in string.ascii_uppercase}
    word_values = [sum(map(char_values.__getitem__, word)) for word in words]
    triangle_numbers = set(util.polygonal_numbers(3, high=max(word_values)))
    return sum(x in triangle_numbers for x in word_values)

def problem_43():
    """
    Find the sum of all 10-digit pandigital numbers where the number from 
    digits 2-4 is divisible by 2, digits 3-5 divisible by 3,
    digits 4-6 are divisible by 5, etc.

    Notes
    -----
    We know that digit 6 is 0 or 5, and it being 0 would imply digits 7 = digit 8,
    which is impossible.
    """
    digits = set(map(str, range(10)))
    has_repeated_digits = lambda s: len(set(s)) < len(s)
    candidates = {f'{n:03d}' for n in range(17, 1000, 17)}
    candidates = {n for n in candidates if not has_repeated_digits(n)}

    # Construct numbers from right to left
    for p in (13, 11, 7, 5, 3, 2):
        candidates = {
            f'{d}{n}' # prepend digit d
            for n in candidates # existing candidates
            for d in digits - set(n) # remaining digits
            if int(f'{d}{n[:2]}') % p == 0 # check divisibility
        }

    return sum([int(n) for n in candidates])

def problem_44():
    """
    Find the smallest difference between a pair of pentagonal numbers for which
    their sum and difference are both pentagonal.
    """
    pentagonal_numbers = set()
    for p_j in util.polygonal_numbers(5):
        for p_k in pentagonal_numbers:
            if (p_j - p_k) in pentagonal_numbers and util.is_polygonal(5, p_j + p_k):
                return p_j - p_k

        pentagonal_numbers.add(p_j)

def problem_45(N=40755):
    """
    Find the next triangle number above N that is also pentagonal and hexagonal.

    Notes
    -----
    All hexagonal numbers are also triangular.

    From the closed-form expressions for pentagonal and hexagonal numbers,
    we have that n is pentagonal if x^2 = 24n + 1 = 5 mod 6 is a perfect square,
    and that n is hexagonal if y^2 = 8n + 1 = 3 mod 4 is a perfect square.

    This reduces to the Pell equation x^2 - 3y^2 = -2.
    """
    for x, y in util.pell(D=3, N=-2):
        if x % 6 == 5 and y % 4 == 3:
            n = (y*y + 1) // 8
            if n > N:
                return n

def problem_46():
    """
    Find the smallest odd composite number that cannot be written as
    n = p + 2a^2, where p is prime and a is a positive integer.
    """
    for n in itertools.count(start=9, step=2):
        if util.is_prime(n):
            continue
        if not any(util.is_prime(n - 2*a*a) for a in range(1, isqrt(n) + 1)):
            return n

def problem_47(n=4, k=4, upper_bound=None):
    """
    Find the first n consecutive integers to have k distinct prime factors each.
    """
    # Count the number of prime factors for each integer below the upper bound
    upper_bound = upper_bound or 200000
    max_factor = upper_bound // prod(util.primes(num=k-1))
    num_prime_factors = [0] * upper_bound
    for p in util.primes(high=max_factor):
        num_prime_factors[p::p] = [count + 1 for count in num_prime_factors[p::p]]

    # Search for consecutive integers with k prime factors
    num_consecutive = 0
    for i in range(prod(util.primes(num=k)), upper_bound):
        if num_prime_factors[i] == k:
            num_consecutive += 1
        else:
            num_consecutive = 0
        if num_consecutive == n:
            return i - n + 1

    # Increase the upper bound and try again
    return problem_47(n=n, k=k, upper_bound=10*upper_bound)

def problem_48(n=1000, k=10):
    """
    Find the k trailing digits of the series 1^1 + 2^2 + ... + n^n.
    """
    mod = 10**k
    return sum([pow(i, i, mod=mod) for i in range(1, n + 1)]) % mod

def problem_49(n=4, k=3, exclude=(1487, 4817, 8147)):
    """
    Find an arithmetic sequence of k n-digit primes, each of which are permutations.
    """
    seen = set()
    prime_set = set(util.primes(low=10**(n-1), high=10**n)) # n-digit primes
    for p in prime_set:
        if p in seen:
            continue

        # Generate all prime permutations of p
        prime_permutations = {int(''.join(digits)) for digits in permutations(str(p))}
        prime_permutations = prime_set.intersection(prime_permutations)
        seen.update(prime_permutations)

        # Find arithmetic sequence
        for sequence in combinations(sorted(prime_permutations), k):
            diffs = [a - b for a, b in zip(sequence[1:], sequence)]
            if diffs == [diffs[0]] * (k - 1) and sequence != exclude:
                return ''.join(map(str, sequence))

def problem_50(N=int(1e6)):
    """
    Which prime below N can be written as the sum of the most consecutive primes?
    """
    # Calculate an upper bound on the number of consecutive primes to consider
    prime_list = list(util.primes(high=N))
    prime_cumsum = itertools.accumulate(prime_list)
    max_chain_length = next(i for i, s in enumerate(prime_cumsum) if s > N)

    # Calculate sums via DP, where sums[i, j] stores the sum of prime_list[i:j]
    sums = {}
    longest_chain = []
    for i in range(len(prime_list) - max_chain_length):
        for j in range(i + len(longest_chain), i + max_chain_length):
            if (i - 1, j - 1) in sums:
                sums[i, j] = sums[i - 1, j - 1] - prime_list[i - 1] + prime_list[j - 1]
            else:
                sums[i, j] = sum(prime_list[i:j])

            if sums[i, j] >= N:
                break
            elif util.is_prime(sums[i, j]):
                longest_chain = prime_list[i:j]

    return sum(longest_chain)

def problem_51(n=8):
    """
    Find the smallest prime which, by replacing part of the number
    with the same digit, is part of a family of exactly n primes.

    Notes
    -----
    For a family of k-digit primes, they differ by multiples of step size Δ
    which contains 1 at the digit positions to be replaced, and 0 everywhere else.

    For example, the family (56003, 56113, 56333, 56443, 56663, 56773, 56993)
    differs by multiples of 00110.

    If n > 4, then the last digit cannot be replaced, since the last digit must be
    1, 3, 7, or 9 to be prime.

    If n > 7, then the number of digits to be replaced must be a multiple of 3, as
    otherwise there are at least 3 multiples of 3 among the 10 potential family members.
    """
    for k in itertools.count(start=1):
        prime_list = list(util.primes(low=10**(k-1), high=10**k)) # k-digit primes
        prime_set = set(prime_list)
        for p in prime_list:
            digits = str(p)
            for d in set(digits):
                if n > 4 and digits[-1] == d: continue
                if n > 7 and digits.count(d) % 3 != 0: continue
                step = int(''.join(['1' if digits[i] == d else '0' for i in range(k)]))
                start, stop = p - int(d) * step, p + (10 - int(d)) * step
                family = [q for q in range(start, stop, step) if q in prime_set]
                if len(family) == n:
                    return family[0]

def problem_52(k=6):
    """
    Find the smallest positive integer n such that 2n, 3n, ..., kn
    all have the same digits in some order.

    Notes
    -----
    If 2n, 3n, ... kn all have the same digits, then they have the same digital
    sum s, and thus are all congruent to s mod 9. If k > 2, this implies n = 0 mod 9.
    """
    if k <= 2:
        return 1

    for i in itertools.count(start=1):
        start, stop = 10**i // 2, 10**(i + 1) // k + 1
        start = ((start + 9 - 1) // 9) * 9 # round up to nearest multiple of 9
        for x in range(start, stop, 9):
            digits = sorted(str(2 * x))
            if all(sorted(str(k * x)) == digits for k in range(3, k + 1)):
                return x

def problem_53(N=100, T=int(1e6)):
    """
    Find the number of pairs (n, k) such that (n choose k) > T, for n = 1, 2, ..., N.

    Notes
    -----
    For each n, let k_n <= ⌊n/2⌋ be the smallest k such that (n choose k) > T.
    Then for each n there are (n + 1 - 2k_n) total pairs that exceed the threshold T.

    We can also infer that k_n <= k_{n-1}, since (n choose k) must be greater than
    ((n - 1) choose k).

    In addition, we can iteratively calculate the binomial coefficient 
    via the following identities:

        (n choose (k - 1)) = (n choose k) * k / (n - k + 1)

        ((n + 1) choose k) = (n choose k) * (n + 1) / (n + 1 - k)

    Finally, given threshold T > 1, it can be shown that (n choose k) <= T
    for all n <= log_2(T) + 1 (proof omitted).
    """
    # Find lower bound on n
    n_min = int(log(T, 2)) + 2
    n_min = next(n for n in itertools.count(start=n_min) if comb(n, n // 2) > T)

    # Count the total number of values that exceed the threshold
    k, count = n_min // 2, 0
    binomial_coefficient = comb(n_min - 1, k - 1)
    for n in range(n_min, N + 1):
        # Update binomial coefficient
        binomial_coefficient *= n / (n - k + 1)

        # Decrement k until (n choose (k - 1)) falls below threshold
        while binomial_coefficient > T:
            k -= 1
            binomial_coefficient *= k / (n - k + 1)

        # Update count
        count += n + 1 - 2 * k

    return count

def problem_54(path='data/problem_54.txt'):
    """
    Given a list of poker hands, find the number of hands won by player 1.
    """
    CARD_VALUES = {
        **{str(i): i for i in range(2, 10)},
        'T': 10, 'J': 11, 'Q': 12, 'K': 13, 'A': 14,
    }

    def get_rank(hand):
        values = sorted([CARD_VALUES[card[0]] for card in hand], reverse=True)
        suits = {card[1] for card in hand}
        is_straight = (values == list(range(values[0], values[0] - 5, -1)))
        is_flush = (len(suits) == 1)
        pairs = sorted({v for v in values if values.count(v) == 2}, reverse=True)
        triples = sorted({v for v in values if values.count(v) == 3}, reverse=True)
        quads = sorted({v for v in values if values.count(v) == 4}, reverse=True)

        if is_straight and is_flush:
            return (8, *values) # straight flush
        elif quads:
            return (7, *quads, *values) # four of a kind
        elif triples and pairs:
            return (6, *triples, *pairs, *values) # full house
        elif is_flush:
            return (5, *values) # flush
        elif is_straight:
            return (4, *values) # straight
        elif triples:
            return (3, *triples, *values) # three of a kind
        elif pairs:
            return (len(pairs), *pairs, *values) # one or two pair
        else:
            return (0, *values) # high card

    with open(path) as file:
        hands = [line.strip().split(' ') for line in file.readlines()]
        hands = [(hand[:5], hand[5:]) for hand in hands]

    return sum(get_rank(player_1) > get_rank(player_2) for player_1, player_2 in hands)

def problem_55(N=10000, max_iterations=50):
    """
    Find the number of Lychrel numbers below N.

    Notes
    -----
    If a non-Lychrel number has sequence a_1, a_2, ..., a_n, then
    all of a_1, ..., a_{n-1} are also non-Lychrel numbers.
    """
    non_lychrel = set()
    for n in range(N):
        sequence = [n]
        for _ in range(max_iterations):
            # Extend the sequence
            sequence.append(sequence[-1] + int(str(sequence[-1])[::-1]))

            # Check if new element is a palindrome (or leads to one)
            if sequence[-1] in non_lychrel or util.is_palindrome(sequence[-1]):
                non_lychrel.update(sequence[:-1])
                break

    return sum(n not in non_lychrel for n in range(N))

def problem_56(N=100):
    """
    Considering natural numbers of the form a^b with a, b < N,
    find the maximum digital sum.
f
    Notes
    -----
    The exponential a^b has log_10(a^b) = ⌊b * log_10(a) + 1⌋ digits,
    with a digital sum no greater than 9 * ⌊b * log_10(a) + 1⌋.
    """
    max_digit_sum = 0
    for a in range(N - 1, 0, -1):
        for b in range(N - 1, 0, -1):
            if 9 * int(b * math.log10(a) + 1) < max_digit_sum: break
            max_digit_sum = max(max_digit_sum, util.get_digit_sum(a**b))

    return max_digit_sum

def problem_57(N=1000):
    """
    For the fractions a/b at each of the first N iterations of Babylonian method
    approximation of sqrt(2), how many have more digits in the numerator than
    the denominator?
    """
    a, b, count = 1, 1, 0
    for _ in range(N):
        a, b = a + 2*b, a + b
        count += (int(math.log10(a)) > int(math.log10(b)))

    return count

def problem_58(ratio=0.1):
    """
    Find the side length of the Ulam spiral for which the ratio of primes
    along both diagonals first falls below the given ratio.
    """
    num_primes, total = 0, 1
    for n in itertools.count(start=3, step=2):
        num_primes += sum(util.is_prime(n*n - i*(n - 1)) for i in range(1, 4))
        total += 4
        if num_primes / total < ratio:
            return n

def problem_59(path='data/problem_59.txt'):
    """
    Decrypt the message in the given file using a simple XOR cipher.
    Find the sum of the ASCII values of the decrypted text.
    """
    common_characters = (' ', 'e', 'a', 'r', 'i', 'o', 't', 'n', 's', 'l', 'c')
    printable_codes = set(map(ord, string.printable))

    def decrypt(data, key):
        m = len(key)
        for i, encrypted_code in enumerate(data):
            decrypted_code = encrypted_code ^ key[i % m]
            if decrypted_code in printable_codes:
                yield decrypted_code
            else:
                raise ValueError

    # Load encrypted data
    with open(path) as file:
        data = list(map(int, file.read().split(',')))

    # Get most frequent encrypted code at each key offset
    most_frequent_encrypted_codes = [
        Counter(data[offset::3]).most_common(1)[0][0]
        for offset in range(3)
    ]

    # Generate possible key codes at each offset
    # Match most frequent encrypted code to most frequent English characters
    key_codes = [
        [code ^ ord(char) for char in common_characters]
        for code in most_frequent_encrypted_codes
    ]

    # Attempt to decrypt data with each key
    for key in itertools.product(*key_codes):
        try:
            return sum(decrypt(data, key))
        except ValueError:
            pass

def problem_60(n=5, upper_bound=None):
    """
    Find the lowest sum for a set of n primes for which
    any pair of primes concatenate to produce another prime.

    Notes
    -----
    Note that every positive integer is congruent to the sum of its digits mod 3.
    Then 3 divides the concatenation of p and q if and only if 3 divides p + q.
    """
    upper_bound = upper_bound or 10000
    is_prime = util.is_prime
    is_prime_concat = lambda p, q: is_prime(int(f'{q}{p}')) and is_prime(int(f'{p}{q}'))

    # Create a graph of primes with edges indicating concatenatable pairs
    primes = util.primes(high=upper_bound)
    graph = {p: set() for p in primes if n == 1 or p not in (2, 5)}
    for p, q in combinations(graph.keys(), 2):
        if (p + q) % 3 == 0: continue
        if is_prime_concat(p, q):
            graph[p].add(q)
            graph[q].add(p)

    # Find cliques of size n and n - 1
    maximal_cliques = util.bron_kerbosch(graph)
    cliques = {
        k: [c for mc in maximal_cliques for c in combinations(mc, k)]
        for k in (n - 1, n)
    }

    # Increase upper bound if no n-cliques are found
    # or if our (n-1)-cliques are not guaranteed to contain a minimal sum
    if not cliques[n] or min(map(sum, cliques[n - 1])) > upper_bound:
        return problem_60(n, upper_bound=2*upper_bound)

    # Try to construct additional n-cliques from (n-1)-cliques by
    # adding a new prime p, where upper_bound < p < clique_sum_bound
    clique_sum_bound = min(map(sum, cliques[n]))
    prime_list = list(util.primes(low=upper_bound+1, high=clique_sum_bound))
    for clique in cliques[n - 1]:
        for p in prime_list:
            if sum(clique) + p >= clique_sum_bound: break
            if (p + clique[0]) % 3 == 0: continue
            if all(is_prime_concat(p, q) for q in clique):
                cliques[n].append((*clique, p))

    return min(map(sum, cliques[n]))

def problem_61(n=8, k=4):
    """
    Find the sum of an ordered set of cyclic k-digit numbers where in
    each consecutive pair (x, y) the last k/2 digits of x match the first k/2
    digits of y, and each s-gonal type from s = 3 ... n, is represented by a
    different number in the set.
    """
    # Generate k-digit figurate numbers
    figurate_numbers = {
        s: list(util.polygonal_numbers(s, low=10**(k - 1), high=10**k - 1))
        for s in range(3, n + 1)
    }

    # Create a graph with edges (i, x) -> (j, y) if the last k/2 digits of
    # i-gonal number x match the first k/2 digits of j-gonal number y
    graph = defaultdict(set)
    for i, j in permutations(figurate_numbers, 2):
        for x, y in itertools.product(figurate_numbers[i], figurate_numbers[j]):
            if str(x)[-k//2:] == str(y)[:k//2]:
                graph[(i, x)].add((j, y))

    def find_next(path):
        if not path:
            return list(graph.keys())

        # No repeated figure types (unless we have already used them all)
        figures, values = zip(*path)
        if len(path) == len(figurate_numbers):
            return [node for node in graph[path[-1]] if node[0] not in figures[1:]]
        else:
            return [node for node in graph[path[-1]] if node[0] not in figures]

    # Find cycles in the graph
    cycle = next(util.find_cycles(find_next=find_next), None)
    return sum(value for figure, value in cycle) if cycle else None

def problem_62(n=5):
    """
    Find the smallest cube for which exactly n permutations of its digits are cubes.
    """
    for k in itertools.count(start=1):
        # Generate all k-digit cubes
        low, high = ceil((10**(k - 1)) ** (1/3)), floor((10**k - 1) ** (1/3))
        cubes = (str(i*i*i) for i in range(low, high + 1))

        # Check for a permutation group of size n
        permutations = [
            group for group in util.group_permutations(cubes) if len(group) == n]
        if permutations:
            return min(min(group) for group in permutations)

def problem_63():
    """
    Find the number of n-digit positive integers that are n-th powers.

    Notes
    -----
    Any such number a^n must satisfy 10^(n-1) <= a^n < 10^n.
    This implies that a < 10 and n < 22.
    """
    has_n_digits = lambda x, n: 10**(n - 1) <= x < 10**n
    return len([a**n for a in range(10) for n in range(22) if has_n_digits(a**n, n)])

def problem_64(N=10000):
    """
    Find the number of continued fractions for sqrt(n) for which the period is odd.
    """
    get_period_length = lambda n: util.continued_fraction(n)[-1]
    return sum(get_period_length(n) % 2 == 1 for n in util.non_squares(N))

def problem_65(n=100):
    """
    Find the sum of digits in the numerator of the n-th convergent for e.
    """
    coefficients = [2, 1]
    for k in range(1, n // 3 + 1):
        coefficients += (2 * k, 1, 1)

    return util.get_digit_sum(util.convergents(coefficients)[n - 1][0])

def problem_66(N=1000):
    """
    Find the value of D <= N that maximizes x in the fundamental solution
    to Pell's equation x^2 - Dy^2 = 1.
    """
    return max(util.non_squares(N), key=lambda D: next(util.pell(D))[0])

def problem_67(path='data/problem_67.txt'):
    """
    Find the maximum sum of a path from the top to the bottom of a triangle.
    """
    return problem_18(path=path)

def problem_68(n=5):
    """
    Find the maximum solution for an n-gon ring as a concatenated string, where:

        * Each number from 1 ... 2n is used exactly once
        * The sum of the numbers in each group of three is the same
        * The first group of three has the numerically lowest external node
        * Groups are ordered clockwise

    Notes
    -----
    Given group (a, b, c), the next group is of the form (a + i, c, b - i),
    where max(1 - a, b - 2n) < i < min(b - 1, 2n - a).

    If n is odd, then the maximal solution has n + 1 ... 2n in the outer ring,
    and has 1 ... n in the inner ring.

    Here the initial groups are (n + 1, n, (n + 1) / 2) and (2n, (n + 1) / 2, 1),
    followed by the rule (a, b, c) -> (a - 1, c, b + 1).

    If n is even, then the maximal solution has n ... 2n (except 3n/2) in the
    outer ring, and has 3n/2 and 1 ... n - 1 in the inner ring.

    Here the initial group is (n, 3n/2, 2).
    """
    # Closed form solution for odd n
    if n % 2 == 1:
        external = [n + 1, *range(2*n, n + 1, -1)]
        internal = [(n - i * (n - 1) // 2 - 1) % n + 1 for i in range(n)]
        solution = zip(external, internal, (*internal[1:], internal[0]))
        return ''.join(map(str, sum(solution, ())))

    has_repeated_values = cache(lambda a: len(set(a)) < len(a))
    all_values = set(range(1, 2*n + 1))

    def find_next(path):
        # Go back to start if possible when there are no remaining values
        remaining_values = all_values - {value for group in path for value in group}
        if not remaining_values and path[0][1] == path[-1][-1]:
            return [path[0]]

        # Otherwise extend the path
        a, b, c = path[-1]
        min_offset, max_offset = max(path[0][0] + 1 - a, b - 2*n), min(b - 1, 2*n - a)
        external, internal = remaining_values, remaining_values | {path[0][1]}
        return [
            (a + i, c, b - i)
            for i in reversed(range(min_offset, max_offset + 1))
            if a + i in external
            if b - i in internal
            if not has_repeated_values((a + i, c, b - i))
        ]

    solution = next(util.find_cycles(find_next=find_next))
    return ''.join(map(str, sum(solution, ())))

def problem_69(N=int(1e6)):
    """
    Find the value of n <= N for which n / φ(n) is a maximum,
    where φ is Euler's totient function.

    Notes
    -----
    From Euler's product formula, we see that n / φ(n) is maximized
    when n is a product of as many different small primes as possible.

    The solution is the largest primorial less than or equal to N.
    """
    primorial = 1
    for p in util.primes():
        if (next_primorial := primorial * p) > N: break
        primorial = next_primorial

    return primorial

def problem_70(N=int(1e7)):
    """
    Find the value of n with 1 < n < N for which φ(n) is a permutation of n
    and the ratio n / φ(n) produces a minimum, where φ is Euler's totient function.

    Notes
    -----
    From Euler's product formula, we see that n / φ(n) is minimized
    when n is a product of as few different large primes as possible.

    It can be shown that φ(p^k) cannot be a permutation of p^k, so
    we need to consider the product of at least two primes.

    If 2817 < N <= 2991, then the optimal solution is n = 2817 = 3 * 3 * 313.

    Conjecture: All other optimal solutions are semiprimes n = pq
    with p, q < 2 * sqrt(N) (verified by brute force for N <= 10^8).

    Also note that if n = pq and φ(n) = (p - 1)(q - 1) are permutations,
    then they have the same digital sum, and thus must be congruent mod 9.
    Therefore we must have n - φ(n) = p + q - 1 = 0 mod 9, or p + q = 1 mod 9.
    """
    # Special case that needs product of 3 primes
    if 2817 < N <= 2991:
        return 2817 # 3 * 3 * 313

    prime_list = list(util.primes(high=2*isqrt(N)))
    is_permutation = lambda a, b: sorted(str(a)) == sorted(str(b))

    best_n, best_ratio = 0, float('inf')
    for p in reversed(prime_list[:util.count_primes(sqrt(N), prime_list)]):
        for q in reversed(prime_list[:util.count_primes(N // p, prime_list)]):
            n, totient_n = p * q, (p - 1) * (q - 1)
            if (ratio := n / totient_n) >= best_ratio:
                break
            if (p + q) % 9 == 1 and is_permutation(n, totient_n):
                best_n, best_ratio = n, ratio
                break

    return best_n

def problem_71(N=int(1e6), a=3, b=7):
    """
    Given proper fraction a/b such that a < b, find the numerator of
    the largest reduced proper fraction c/d less than a/b, where c < d <= N
    and gcd(c, d) = 1.

    Notes
    -----
    For positive integers a, b, c, d, given that gcd(a, b) = 1, the difference
    a/b - c/d = (ad - bc) / bd will be minimized when ad - bc = 1.

    Then we have 1 = ad - bc = ad mod b, so our denominator d
    must be congruent to modular inverse d = a^(-1) mod b.
    """
    a, b = a // gcd(a, b), b // gcd(a, b) # reduce fraction
    offset = N - b + 1
    denominator = (pow(a, -1, b) - offset) % b + offset
    numerator = (denominator * a - 1) // b
    return numerator

def problem_72(N=int(1e6)):
    """
    Find the number of reduced proper fractions a/b for b <= N.

    Notes
    -----
    We know a/b is a proper reduced fraction if and only if a < b and gcd(a, b) = 1.
    Given b, the number of coprime integers below b is given by the totient function.
    """
    return sum(util.get_totients(N)[2:])

def problem_73(N=12000, low=1/3, high=1/2):
    """
    Find the number of reduced proper fractions low < a/b < high with b <= N.
    """
    start = lambda n: floor(n * low) + 1
    stop = lambda n: ceil(n * high)
    return sum(sum(util.coprime_range(n)[start(n):stop(n)]) for n in range(2, N + 1))

def problem_74(N=int(1e6), k=60):
    """
    TODO
    """
    digit_values = {str(d): factorial(d) for d in range(10)}
    base_chains = {
        1: (1,), 2: (2,), 145: (145,), 40585: (40585,),
        169: (169, 363601, 1454),
        363601: (169, 363601, 1454), 
        1454: (169, 363601, 1454),
        871: (871, 45361), 45361: (871, 45361),
        872: (872, 45362), 45362: (872, 45362),
    }

    @functools.cache
    def chain(n):
        if n in base_chains:
            return base_chains[n]
        else:
            n = sum(map(digit_values.__getitem__, str(n)))
            return (n,) + chain(n)

    return sum(len(chain(n)) == k for n in range(N))

def problem_75(N=1500000):
    """
    Find the number of n <= N such that a + b + c = n for exactly one
    Pythagorean triple (a, b, c).
    """
    counts = Counter(map(sum, util.pythagorean_triples(max_sum=N)))
    return list(counts.values()).count(1)

def problem_76(n=100):
    """
    Return the number of non-trivial partitions of integer n.
    """
    return util.num_partitions(n) - 1

def problem_77(N=5000):
    """
    Find the smallest integer n that can be written as the sum of primes in
    more than N different ways.
    """
    for n in itertools.count():
        if util.num_partitions(n, restrict=util.is_prime) > N:
            return n

def problem_78(N=int(1e6)):
    """
    Find the smallest positive integer n for which the value of partition function
    p(n) is divisible by N.
    """
    for n, p in enumerate(util.partition_numbers(mod=N)):
        if p == 0:
            return n 

def problem_79(path='data/problem_79.txt'):
    """
    TODO: handle repeat characters
    """
    with open(path) as file:
        lines = [line.strip() for line in file.readlines()]
        characters = {c for line in lines for c in line}

    solution = []
    while characters:
        first = {line[-3] for line in lines if len(line) > 2}
        second = {line[-2] for line in lines if len(line) > 1}
        third = {line[-1] for line in lines if len(line) > 0}
        for c in third - first - second:
            characters.remove(c)
            solution.insert(0, c)
            lines = {line.strip(c) for line in lines} - {''}

    return ''.join(solution)

def problem_80(N=100, k=10000):
    """
    Find the sum of the first k digits in the decimal expansion for the
    irrational square roots of integers 1, 2, ..., N.
    """
    # Rationally approximate square roots with Newton's method
    total = 0
    for n in util.non_squares(N):
        a, b = ceil(sqrt(n)), 1
        while math.log10(b) < k:
            a, b = a*a + b*b*n, 2*a*b

        # Convert to a k-digit integer and get digital sum
        total += util.get_digit_sum(a * 10**(k - int(math.log10(a // b)) - 1) // b)

    return total

def problem_81(
    path='data/problem_81.txt',
    allowed_moves=('right', 'down'),
    start_nodes={(0, 0)},
    end_nodes={(79, 79)},
):
    """
    Find the minimum path sum from any start node to any end node.
    """
    moves = {'left': (0, -1), 'right': (0, 1), 'up': (-1, 0), 'down': (1, 0)}
    deltas = [moves[move] for move in allowed_moves]

    # Load matrix
    with open(path) as file:
        matrix = [[*map(int, line.strip().split(','))] for line in file.readlines()]
        height, width = len(matrix), len(matrix[0])

    # Modify graph to include 'source' node connected to start nodes
    # and 'sink' node connected to end nodes
    def get_neighbors(node):
        if node == 'source':
            return start_nodes
        elif node == 'sink':
            return []

        r, c = node
        neighbors = [
            (r + dr, c + dc)
            for dr, dc in deltas
            if 0 <= r + dr < height and 0 <= c + dc < width
        ]

        return neighbors + ['sink'] if node in end_nodes else neighbors

    # Edge weights given by matrix values
    def get_edge_weight(u, v):
        return 0 if v == 'sink' else matrix[v[0]][v[1]]

    # Find shortest path from 'source' to 'sink'
    dist, _ = util.dijkstra('source', get_neighbors, get_edge_weight)
    return dist['sink']

def problem_82(
    path='data/problem_81.txt',
    allowed_moves=('right', 'up', 'down'),
    start_nodes={(r, 0) for r in range(80)},
    end_nodes={(r, 79) for r in range(80)},
):
    """
    Find the minimum path sum from any start node to any end node.
    """
    return problem_81(path, allowed_moves, start_nodes, end_nodes)

def problem_83(
    path='data/problem_81.txt',
    allowed_moves=('right', 'left', 'up', 'down'),
    start_nodes={(0, 0)},
    end_nodes={(79, 79)},
):
    """
    Find the minimum path sum from any start node to any end node.
    """
    return problem_81(path, allowed_moves, start_nodes, end_nodes)

def problem_84(n=4):
    """
    Return the three most likely squares landed on in a game of Monopoly
    with two n-sided dice.

    Notes
    -----
    We ignore the fact that each CH or CC card is returned to the bottom of
    the pile after it is used, and instead assume each draw is independent.

    This should not significantly affect the probabilities, and our relative
    probability ordering should (hopefully) be the same.
    """
    GO, JAIL, G2J = 0, 10, 30 # special squares
    CH1, CH2, CH3 = 7, 22, 36 # chance
    CC1, CC2, CC3 = 2, 17, 33 # community chest
    C1, E3, H2 = 11, 24, 39 # properties
    R1, R2, R3 = 5, 15, 25 # railway
    U1, U2 = 12, 28 # utility
    next_railway = {CH1: R2, CH2: R3, CH3: R1}
    next_utility = {CH1: U1, CH2: U2, CH3: U1}

    # Create transition matrix T, where T[i][j] is the probability of
    # moving from square i to square j after a single turn
    T = [[0] * 40 for _ in range(40)]
    for i in range(40):
        # Roll dice
        for roll_1, roll_2 in itertools.product(range(1, n + 1), repeat=2):
            T[i][(i + roll_1 + roll_2) % 40] += 1/(n*n)

        # Go to jail
        T[i][JAIL], T[i][G2J] = T[i][JAIL] + T[i][G2J], 0

        # Chance
        for j in (CH1, CH2, CH3):
            p, T[i][j] = T[i][j], 0
            T[i][j] += p * (6/16) # stay
            T[i][next_railway[j]] += p * (2/16)
            for k in (GO, JAIL, C1, E3, H2, R1, next_utility[j], (j - 3) % 40):
                T[i][k] += p * (1/16)

        # Community chest
        for j in (CC1, CC2, CC3):
            p, T[i][j] = T[i][j], 0
            for k, count in ((GO, 1), (JAIL, 1), (j, 14)):
                T[i][k] += p * (count / 16)

        # Roll 3 consecutive doubles
        p = (1/6)**3
        for j in range(40): T[i][j] *= (1 - p)
        T[i][JAIL] += p

    # Find stationary distribution
    probs = [0] * 40
    probs[GO] = 1
    for _ in range(100):
        probs = util.matrix_product([probs], T)[0]

    # Get the three most likely squares
    argsort = sorted(range(40), key=probs.__getitem__)
    return f'{argsort[-1]:02}{argsort[-2]:02}{argsort[-3]:02}'

def problem_85(n=int(2e6)):
    """
    Find the area of the grid containing the number of rectangles nearest to n.

    Notes
    -----
    The number of rectangles in an H x W grid is given by T_H * T_W,
    where T_n is the n-th triangular number.
    """
    best_area, best_diff = 0, float('inf')
    for h, T_h in enumerate(util.polygonal_numbers(3, high=isqrt(n)), start=1):
        w = round(util.polygonal_index(3, n / T_h))
        T_w = util.polygonal(3, w)
        diff = abs(T_h * T_w - n)
        if diff < best_diff:
            best_area, best_diff = h * w, diff

    return best_area

def problem_86(N=int(1e6)):
    """
    Find the least value of M such there exist at least N distinct cuboids,
    ignoring rotations, with integer dimensions (x, y, z), where x, y, z <= M,
    for which the shortest path between opposite corners has integral length.

    Notes
    -----
    For any cuboid with dimensions (x, y, z) where x <= y <= z,
    the shortest path from one corner to the opposite corner has integral length
    if and only if (x + y, z) form the legs of a Pythagorean triple.

    Say we are given a Pythagorean triple (a, b, c) with a <= b.
    If z = a, we have satisfying dimensions (b - i, i, a) for i = ⌈b/2⌉ ... a.
    If z = b, we have satisfying dimensions (a - i, i, b) for i = ⌈a/2⌉ ... a - 1.

    TODO: derive upper bound for Pythagorean triples
    """
    # Generate Pythagorean triples
    triples = list(util.pythagorean_triples(max_sum=10000))
    triples_1 = iter(sorted(triples, key=lambda t: t[0]))
    triples_2 = iter(sorted(triples, key=lambda t: t[1]))

    # Count solutions
    a1, b1, _ = next(triples_1)
    a2, b2, _ = next(triples_2)
    count = 0
    while count <= N:
        if a1 < b2:
            if ceil(b1 / 2) <= a1: count += a1 - ceil(b1 / 2) + 1
            M, (a1, b1, _) = a1, next(triples_1)
        else:
            count += a2 // 2
            M, (a2, b2, _) = b2, next(triples_2)

    return M

def problem_87(N=int(5e7)):
    """
    Find the number of positive integers below N such that n = p^2 + q^3 + r^4
    for prime p, q, r.
    """
    values = set()
    prime_list = list(util.primes(high=isqrt(N)))

    for r in prime_list:
        if (a := r*r*r*r) >= N: break
        for q in prime_list:
            if (b := a + q*q*q) >= N: break
            for p in prime_list:
                if (c := b + p*p) >= N: break
                values.add(c)

    return len(values)

def problem_88(N=12000):
    """
    Find the sum of all positive integers n <= N that can be written as the
    sum of a product set, where the product set is the minimal set of positive
    integers whose product is n.

    Notes
    -----
    If n = a_1 * ... * a_k, then ...
    TODO: complete notes + optimize
    """
    @cache
    def factorizations(n):
        if n == 1:
            return set()

        results = {(n,)}
        for d in util.divisors(n)[1:]:
            for factors in factorizations(n // d):
                results.add(tuple(sorted((d, *factors))))

        return results

    product_sum_numbers = defaultdict(set)
    for n in range(2, 2*N + 1):
        if util.is_prime(n): continue
        for factors in factorizations(n):
            k = n - sum(factors) + len(factors)
            if 2 <= k <= N:
                product_sum_numbers[k].add(n)

    minimal_product_sum_numbers = set(map(min, product_sum_numbers.values()))
    return sum(minimal_product_sum_numbers)

def problem_89(path='data/problem_89.txt'):
    """
    Find the total number of characters saved by writing the given
    Roman numerals in their minimal form.
    """
    def to_minimal(roman: str):
        roman = roman.replace('DCCCC', 'CM')
        roman = roman.replace('CCCC', 'CD')
        roman = roman.replace('LXXXX', 'XC')
        roman = roman.replace('XXXX', 'XL')
        roman = roman.replace('VIIII', 'IX')
        roman = roman.replace('IIII', 'IV')
        return roman

    with open(path) as file:
        roman_numerals = file.read()
        return len(roman_numerals) - len(to_minimal(roman_numerals))

def problem_90(numbers=[1, 4, 9, 16, 25, 36, 49, 64, 81]):
    """
    Consider a cube with a different digit on each face. Given a set of n-digit
    numbers, find the number of distinct arrangements of n such cubes allow for
    all the numbers to be displayed (with digits 6 and 9 being interchangeable).

    Notes
    -----
    We can ignore the 6/9 ambiguity by replacing all 9's with 6's.
    """
    n = len(str(max(numbers)))
    numbers = {str(x).zfill(n).replace('9', '6') for x in numbers} # to n-length strings
    numbers = {''.join(sorted(str(x))) for x in numbers} # ignore digit order

    def all_in(items, collections):
        for item, collection in zip(items, collections):
            if item not in collection:
                return False
        return True

    # Check if all numbers can be displayed by a given set of cubes
    def is_valid(cubes):
        for digits in numbers:
            if not any(map(lambda order: all_in(digits, order), permutations(cubes))):
                return False
        return True

    # Count how many cube arrangements can display all numbers
    faces = string.digits.replace('9', '6')
    return sum(is_valid(cubes) for cubes in combinations(combinations(faces, 6), n))

def problem_91(n=50):
    """
    How many right triangles with integer coordinates (0, 0), (x1, y1), (x2, y2)
    exist such that 0 <= x1, y1, x2, y2 <= n?

    Notes
    -----
    There are n^2 right triangles with the right angle at the origin.

    Let P = (x1, y1) and Q = (x2, y2) be the other two points, where x1 >= x2.

    If the right angle is at P, then the slope from P to Q (-x1/y1) is the negative
    reciprocal of the slope from the origin to P (y1/x1).

    Then the number of right triangles is the number of integer coordinates
    (x1 - y1 * k/d, y1 + x1 * k/d) within the bounds, where k is a positive integer
    and d = gcd(x1, y1). Of these, exactly n^2 of these triangles have y1 = 0.

    This same analysis gives us the number of right triangles with right angle at Q.
    """
    count = 0
    for x1 in range(1, n + 1):
        for y1 in range(1, n + 1):
            d = gcd(x1, y1)
            count += 2 * min(d * (n - y1) // x1, d * x1 // y1)

    return count + 3*n*n

def problem_92(n=7):
    """
    Given chains of integers where each term is followed by the sum of the squares
    of its digits, find the number of starting numbers with at most n digits
    that end in 89.

    Notes
    -----
    Every integer with the same digits is followed by the same chain.
    If the digit counts are a_1, ..., a_k, then there are
    (a_1 + ... + a_k)! / (a_1! * ... * a_k!) such integers.
    """
    digit_values = {str(d): d*d for d in range(10)}
    base_chains = {0: (0,), 1: (1,), 89: (89,)}

    @functools.cache
    def chain(k):
        if k in base_chains:
            return base_chains[k]
        else:
            k = sum(map(digit_values.__getitem__, str(k)))
            return (k,) + chain(k)

    count = 0
    for digits in itertools.combinations_with_replacement(string.digits, n):
        k = int(''.join(digits))
        if chain(k)[-1] == 89:
            digit_counts = Counter(digits).values()
            count += factorial(sum(digit_counts)) // prod(map(factorial, digit_counts))

    return count

def problem_93(n=4):
    """
    Find the set of n digits for which the longest sequence of consecutive
    target values 1 ... n can be generated using each digit exactly once
    and the operations (+, -, *, /).

    TODO: generalize to arbitrary number of digits
    """
    from operator import add, sub, mul, truediv
    operations = (cache(add), cache(sub), cache(mul), cache(truediv))
    best_group, best_sequence = None, []

    # Iterate through all subsets of n digits
    for group in combinations(range(1, 10), n):
        # Generate all possible target values
        targets = set()
        for a, b, c, d in permutations(group):
            for op1, op2, op3 in itertools.product(operations, repeat=n-1):
                targets.add(op3(op2(op1(a, b), c), d))
                targets.add(op3(op1(a, b), op2(c, d)))

        # Get sequence of consecutive target values, starting from 1
        sequence = range(1, next(i for i in itertools.count(1) if i not in targets))
        if len(sequence) > len(best_sequence):
            best_group, best_sequence = group, sequence

    return ''.join(map(str, best_group))

def problem_94(N=int(1e9)):
    """
    Find the number of triangles with side lengths of the form
    (a, a, a ± 1) with integer area and perimeter not exceeding N.

    Notes
    -----
    From Heron's formula, a triangle with sides (a, a, a + 1) has integer area
    if and only if (3a^2 - 2a - 1) / 4 = y^2 is a perfect square.

    Let a = 2k - 1 and x = 3k - 2 (perimeter = 3a + 1 = 2x + 2).
    Then this reduces to the Pell equation x^2 - 3y^2 = 1.

    Similarly, a triangle with sides (a, a, a - 1) has integer area
    if and only if (3a^2 + 2a - 1) / 4 = y^2 is a perfect square.

    Let a = 2k + 1 and x = 3k + 2 (perimeter = 3a - 1 = 2x - 2).
    This also reduces to the same Pell equation x^2 - 3y^2 = 1.
    """
    total = 0
    for x, y in util.pell(3):
        if 2*x - 2 > N:
            break
        if x % 3 == 1 and 3 <= (perimeter := 2*x + 2) <= N:
            total += perimeter
        if x % 3 == 2 and 3 <= (perimeter := 2*x - 2) <= N:
            total += perimeter

    return total

def problem_95(N=int(1e6)):
    """
    Find the smallest member of the longest aliquot cycle with no element exceeding N.
    """
    divisor_sums = util.get_divisor_sums(N, proper=True)
    aliquot_cycles = {}

    for n in range(1, N):
        # Generate chain
        chain = [n]
        while (k := chain[-1]) not in chain[:-1] and k <= N and k not in aliquot_cycles:
            chain.append(divisor_sums[chain[-1]])

        # Check for cycle
        i = chain.index(chain[-1])
        for k in chain[:i]:
            aliquot_cycles[k] = []
        for k in chain[i:-1]:
            aliquot_cycles[k] = chain[i:-1]

    return min(max(aliquot_cycles.values(), key=len))

def problem_96(path='data/problem_96.txt'):
    """
    Find the sum of the first three digits of the solutions
    to the given sudoku puzzles.
    """
    # Get indices of all cells in the same row, column, or box as the cell at (r, c)
    eliminate_idx = {}
    for r, c in itertools.product(range(9), range(9)):
        idx = {(3*(r//3) + i, 3*(c//3) + j) for i in range(3) for j in range(3)} # box
        idx |= {(i, c) for i in range(9)} # row
        idx |= {(r, j) for j in range(9)} # column
        eliminate_idx[r, c] = list(idx)

    def solve_sudoku(grid: list[list[int]]) -> list[list[int]]:
        # Find the empty cell with the fewest possible options
        all_options = set(range(1, 10))
        best_cell, best_options = None, all_options
        for (r, c) in itertools.product(range(9), range(9)):
            if grid[r][c] == 0:
                options = all_options - {grid[i][j] for i, j in eliminate_idx[r, c]}
                if len(options) < len(best_options):
                    best_cell, best_options = (r, c), options
                if len(options) <= 1:
                    break

        # Check if puzzle is already solved
        if not best_cell: return grid

        # Try each option
        r, c = best_cell
        for option in best_options:
            grid[r][c] = option
            if solve_sudoku(grid):
                return grid

        grid[r][c] = 0
        return None

    # Read sudoku puzzles from file
    with open(path, 'r') as file:
        lines = [line.strip() for line in file.readlines()]
        puzzles = [lines[i:i+9] for i in range(1, len(lines), 10)]
        puzzles = [[list(map(int, line)) for line in puzzle] for puzzle in puzzles]

    # Solve puzzles
    total = 0
    for puzzle in puzzles:
        solution = solve_sudoku(puzzle)
        total += int(''.join(map(str, solution[0][:3])))

    return total

def problem_97(a=28433, n=7830457, k=10):
    """
    Find the last k digits of a * 2^n + 1.
    """
    m = 10**k
    return (a * pow(2, n, mod=m) + 1) % m

def problem_98(path='data/problem_98.txt'):
    """
    Given a list of words, consider a pair of perfect square anagrams that
    correspond to a pair of word anagrams by replacing letters with digits.
    Find the largest square in such a pair.

    Notes
    -----
    Each pair (a, b) of n-length anagrams can be represented by an n-length
    mapping of indices such that a[mapping[i]] = b[i] for i = 0, 1, ..., n - 1.

    We simply need to find such a mapping that appears in both
    word anagrams and square anagrams.
    """
    def get_anagram_mappings(iterable) -> dict[tuple, tuple[str, str]]:
        mappings = defaultdict(list)
        for group in util.group_permutations(map(str, iterable)):
            for a, b in permutations(group, 2):
                index = {value: i for i, value in enumerate(a)}
                key = tuple(map(index.__getitem__, b))
                mappings[key].append((a, b))

        return mappings

    # Find word anagram mappings
    with open(path) as file:
        words = [s.strip('"') for s in file.read().split(',')]
        word_mappings = get_anagram_mappings(words)

    # Find square anagram mappings
    squares = (i*i for i in range(isqrt(10**max(map(len, word_mappings)))))
    square_mappings = get_anagram_mappings(squares)

    # Filter square anagram pairs whose mapping also forms word anagram pair
    square_anagrams = [
        pairs for key, pairs in square_mappings.items()
        if key in word_mappings
    ]

    # Find the largest square
    return max(int(x) for pairs in square_anagrams for pair in pairs for x in pair)

def problem_99(path='data/problem_99.txt'):
    """
    Given a sequence of (x, y) pairs, find the index that maximizes x^y.

    Notes
    -----
    For any positive x, y we have x > y if and only if log(x) > log(y).
    """
    with open(path) as file:
        numbers = [map(int, line.split(',')) for line in file.readlines()]
        logs = [b * log(a) for a, b in numbers]
        return max(range(len(logs)), key=logs.__getitem__) + 1

def problem_100(N=int(1e12)):
    """
    Consider a set of n discs, b of which are blue.
    Find the smallest n > N such that there exists some b < n where the
    probability of drawing two blue discs without replacement is exactly 1/2.

    Notes
    -----
    If n is total number of discs and b is number of blue discs,
    then we want integer solutions to n^2 - n - 2b^2 + 2b = 0.

    Let x = 2n - 1 and y = 2b - 1. Then this reduces to the negative
    Pell equation x^2 - 2y^2 = -1.
    """
    for x, y in util.pell(2, N=-1):
        if (x + 1) // 2 > N:
            return (y + 1) // 2

def problem_101(coefficients=[1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1]):
    """
    Find the sum of OP(k, k + 1) such that OP(k, k + 1) != f(k),
    where f(n) is the polynomial defined by the given coefficients,
    and OP(k, n) is the (k-1)-th order polynomial approximation.
    """
    f = util.polynomial(coefficients)
    values = [f(n) for n in range(1, len(coefficients) + 2)]

    def OP(k, n):
        A = [[i**j for j in range(k)] for i in range(1, k + 1)]
        coefs = list(map(int, util.linear_solve(A, values[:k])))
        return util.polynomial(coefs)(n)

    terms = [OP(k, k + 1) for k in range(1, len(coefficients) + 1)]
    return sum(term for term, value in zip(terms, values[1:]) if term != value)

def problem_102(path='data/problem_102.txt'):
    """
    Given a list of triangles defined by their vertices, find the number of
    triangles that contain the origin.

    Notes
    -----
    A triangle contains the point (x, y) if and only if the area of the triangle
    is equal to the total area of the triangles formed by each pair of vertices
    and the point (x, y).
    """
    with open(path) as file:
        triangles = [list(map(int, line.split(','))) for line in file.readlines()]

    def area(x1, y1, x2, y2, x3, y3):
        return abs((x1*(y2 - y3) + x2*(y3 - y1) + x3*(y1 - y2)) / 2)

    count = 0
    for x1, y1, x2, y2, x3, y3 in triangles:
        p0, p1, p2, p3 = (0, 0), (x1, y1), (x2, y2), (x3, y3)
        A = area(*p0, *p1, *p2) + area(*p0, *p2, *p3) + area(*p0, *p1, *p3)
        count += (A == area(*p1, *p2, *p3))

    return count

def problem_103():
    """
    Sum of any 2 elements is greater than the 3rd.

    Given a < b < c, we must have:

    b < c < a + b < 2b



    a, b, c, d, e

    a + b > e

    a + b + c > d + e

    4, 5, 6

    


    a + b > c, d, e, etc

    2b > a + b > max element

    ...

    1, 2, 3 ... doesn't work
    2, 3, 4 got it

    2 + 3 > 5 nope
    3 + 4 > 5 ok
    3, 4, 5, 6 ... 3 + 6 = 4 + 5 ... doesn't work
    3, 5, 6, 7 ok

    3 + 5 = 8 ... so go to 4
    4, 5, 6, 7, 8 ... but 4 + 5 + 6 = 7 + 8 ... doesn't work
    4, 6, 7, 8, 9 ... but 4 + 6 + 7 = 8 + 9 ... doesn't work
    5, 

    11, 17, 20, 22, 23, 24

    can we do better?

    1 zero shot combo
    62 one shot combos
    (63 choose 2) two shot combos
    21 doubles (final shot)

    total: (1 + 62 + (63 choose 2)) * 21
    
    number of ways to get 21

    82 other scores
    """
    pass

def problem_109(threshold=100):
    values = [
        50,
        *range(1, 21),
        *(2*i for i in range(1, 21)),
        *(3*i for i in range(1, 21)),
    ]

    doubles = [50, *(2*i for i in range(1, 21))]
    print(doubles)
    print(values)

def problem_104(digits=123456789):
    """
    Find the index of the first Fibonacci number that both begins and ends
    with a permutation of the given digits.

    Notes
    -----
    The k-th Fibonacci number is approximately F(k) ≈ ϕ^k / sqrt(5),
    where ϕ is golden ratio.

    Its first n digits are given by int(10**(n - 1 + log10(F(k)) % 1)),
    where log10(F(k)) ≈ k * log10(ϕ) - log10(sqrt(5)).
    """
    digits = sorted(str(digits))
    num_digits = len(digits)
    mod = 10**num_digits
    log_phi = log((1 + sqrt(5)) / 2, 10)
    log_sqrt_5 = log(sqrt(5), 10)
    is_permutation = lambda x: sorted(str(x)) == digits

    for k in itertools.count():
        # Check leading digits
        log_F = k * log_phi - log_sqrt_5
        leading_digits = int(10**(num_digits - 1 + log_F % 1))
        if not is_permutation(leading_digits):
            continue

        # Check trailing digits
        trailing_digits = util.fibonacci(k, mod=mod)
        if is_permutation(trailing_digits):
            return k

def problem_107(path='data/problem_107.txt'):
    """
    Find the weight difference between a graph and its and minimum spanning tree.
    """
    # Load adjacency matrix
    with open(path) as file:
        graph = [line.replace('-', '0').split(',') for line in file.readlines()]
        graph = [list(map(int, row)) for row in graph]

    # Find minimum spanning tree
    nodes = range(len(graph))
    edges = [(u, v) for u, v in itertools.combinations(nodes, 2) if graph[u][v] != 0]
    minimum_spanning_tree = util.kruskal(nodes, edges, lambda u, v: graph[u][v])

    # Calculate weight difference
    initial_weight = sum(graph[u][v] for u, v in edges)
    final_weight = sum(graph[u][v] for u, v in minimum_spanning_tree)
    return initial_weight - final_weight

def problem_108(K=1000):
    """
    Find the smallest value of n such that the number of distinct solutions
    to 1/x + 1/y = 1/n exceeds K.

    Notes
    -----
    The number of distinct solutions is given by k = (d(n^2) + 1) / 2,
    where d(n) is the divisor function.

    It also follows that ⌈log(2k - 1) / log(3)⌉ is an upper bound on the
    number of unique prime factors.
    """
    prime_list = list(util.primes(num=ceil(log(2*K - 1, 3))))
    prev_k = 0
    heap = [(1, 1, [0] * len(prime_list))]
    while True:
        n, k, exponents = heappop(heap)
        if k > K: return n
        if k <= prev_k: continue
        prev_k = k
        for i in range(len(prime_list)):
            if i == 0 or exponents[i] < exponents[i - 1]:
                new_n = n * prime_list[i]
                new_k = k + (2*k - 1) // (2 * exponents[i] + 1)
                new_exponents = exponents.copy()
                new_exponents[i] += 1
                heappush(heap, (new_n, new_k, new_exponents))

def problem_110(K=int(4e6)):
    """
    Find the smallest value of n such that the number of distinct solutions
    to 1/x + 1/y = 1/n exceeds K.
    """
    return problem_108(K)

def problem_118(digits=range(1, 10)):
    """
    How many distinct sets of decimal integers containing each of the
    given digits exactly once, contain only prime elements?

    Notes
    -----
    If (A_1, A_2, ..., A_n) is a partition of the digits set, and P_i is the set of
    primes formed by permuting the elements of A_i, then the prime sets contributed
    by this partition are given by the Cartesian product P_1 * P_2 * ... * P_n.
    """
    def get_partitions(iterable):
        """
        Generate all possible partitions of an iterable.
        """
        iterable = iter(iterable)

        try:
            item = next(iterable)
            for partition in get_partitions(iterable):
                yield ((item,), *partition)
                for i, subset in enumerate(partition):
                    yield ((item, *subset), *partition[:i], *partition[i+1:])

        except StopIteration:
            yield () # empty partition

    prime_sets = []
    for partition in get_partitions(map(str, digits)):
        prime_permutations = []
        for subset in partition:
            perms = permutations(subset) # get digit permutations
            perms = map(int, map(''.join, perms)) # convert to integers
            perms = filter(util.is_prime, perms) # filter for primes
            prime_permutations.append(perms)

        prime_sets += itertools.product(*prime_permutations)

    return len(prime_sets)

def problem_119(n=30):
    """
    Find the n-th integer that is a power of its digital sum.

    Notes
    -----
    A k-digit integer has a digital sum of at most 9k.
    """
    digit_power_sums = []
    for k in itertools.count(start=2):
        # Iterate over k-digit powers base^exp
        for base in range(2, 9*k + 1):
            min_exp = ceil((k - 1) / math.log10(base))
            max_exp = floor(k / math.log10(base))
            for exp in range(min_exp, max_exp + 1):
                power = base**exp
                if base == util.get_digit_sum(power):
                    digit_power_sums.append(power)

        # Check if we have generated enough digit power sums
        if len(digit_power_sums) >= n:
            return sorted(digit_power_sums)[n - 1]

def problem_120(N=1000):
    """
    Let r_a be the maximum residue (a - 1)^n + (a + 1)^n mod a^2 over all n.
    Find the sum r_3 + r_4 + ... + r_N.

    Notes
    -----
    We can ignore all terms quadratic or higher in the binomial expansion of
    (a - 1)^n and (a + 1)^n, as they will all be divisible by a^2.

    If n is even we have r = (a - 1)^n + (a + 1)^n = 2 (mod a^2),
    and if n is odd we have r = (a - 1)^n + (a + 1)^n = 2an (mod a^2).

    Then given a > 2, it follows that the maximal residue is
    r = a(a - 1) for odd a, and r = a(a - 2) for even a.
    """
    return sum(a * (a - gcd(a, 2)) for a in range(3, N + 1))

def problem_121(n=15):
    """
    Find the inverse probability of winning more than half of n total turns,
    when the probability of winning the i-th turn is given by 1 / (i + 1).
    """
    # Use dynamic programming to store probabilities after each turn
    # P[i, j] / i! is the probability of j wins after i turns
    P = defaultdict(int, {(0, 0): 1})
    for i in range(1, n + 1):
        for j in range(i + 1):
            P[i, j] = P[i - 1, j - 1] + i * P[i - 1, j]

    numerator = sum(P[n, j] for j in range(n//2 + 1, n + 1))
    denominator = factorial(n + 1)
    return denominator // numerator

def problem_122(N=200):
    """
    Let m(k) be the length of the shortest addition chain for k.
    Find the sum m(1) + m(2) + ... m(N).

    Notes
    -----
    TODO: star chains, pruning, DFS, what not
    """
    # num_multiplications = {1: 0}
    # seen = set()

    # MAX_DEPTH = 2 * ceil(log(N, 2))
    # def DFS(path=(1,)):
    #     if path in seen or len(path) > MAX_DEPTH:
    #         return
    #     else:
    #         seen.add(path)

    #     for a in path:
    #         for b in reversed(path):
    #             if a + b <= path[-1]: break
    #             if a + b <= N and a + b not in path:
    #                 if (a + b not in num_multiplications
    #                     or len(path) < num_multiplications[a + b]):
    #                     num_multiplications[a + b] = len(path)
    #                 DFS((*path, a + b))

    # DFS()
    # for i in range(1, N + 1):
    #     print(i, num_multiplications[i])

    num_multiplications = {1: 0}
    addition_chains = {(1,)}
    for i in itertools.count(start=1):
        #print(i, len(addition_chains))
        bound = next(i for i in range(1, N + 1) if i not in num_multiplications)

        # Generate new addition chains of length i + 1
        new_addition_chains = {
            (*chain, a + b)
            for chain in addition_chains
            for a, b in itertools.product(chain, chain)
            if chain[-1] < a + b <= N
            and a + b >= bound
        }

        # Update number of multiplications needed for new chains
        for chain in new_addition_chains:
            if chain[-1] not in num_multiplications:
                num_multiplications[chain[-1]] = i

        # Check if we have generated all k <= N
        addition_chains = new_addition_chains
        if all(k in num_multiplications for k in range(1, N + 1)):
            break

    # print(num_multiplications[12509])
    return sum(num_multiplications[n] for n in range(1, N + 1))

def problem_123(N=int(1e14)):
    """
    Find the smallest index n for which the residue
    (p_n - 1)^n + (p_n + 1)^n mod (p_n)^2 exceeds N.

    Notes
    -----
    For any integer a, the residue (a - 1)^n + (a + 1)^n) mod a^2 is
    r = 2 (mod a^2) when n is even, and r = 2an (mod a^2) when n is odd.

    Also note that for all x >= 17, we have π(x) > x / log(x), where π is the
    prime counting function.
    """
    # Find prime upper bound (such that 2 * p_n * n > N)
    p_max = 17
    while 2 * p_max * p_max / log(p_max) <= N:
        p_max *= 2

    # Find residue exceeding N
    for n, p in enumerate(util.primes(high=p_max), start=1):
        r = 2 if n % 2 == 0 else 2 * n * p
        if r > N:
            return n

def problem_124(N=100000, k=10000):
    """
    Find the k-th positive integer not exceeding N when sorted by rad(n),
    where rad(n) is the product of distinct prime factors of n.
    """
    rad = lambda n: prod(set(util.prime_factors(n)))
    return sorted(range(N // 2, N + 1), key=rad)[k - 1]

def problem_125(N=int(1e8)):
    """
    Find the sum of all the numbers less than N that are both palindromic
    and can be written as the sum of consecutive squares.
    """
    values = set()
    for i in range(1, isqrt(N)):
        sum_of_squares = i*i
        for j in range(i + 1, isqrt(N)):
            sum_of_squares += j*j
            if sum_of_squares >= N: break
            if util.is_palindrome(sum_of_squares):
                values.add(sum_of_squares)

    return sum(values)

def problem_138(n=12):
    """
    Find the sum of L for the n smallest (L, L, b) isosceles triangles
    with height h = b ± 1, where b, L are positive integers.

    Notes
    -----
    We are looking for Pythagorean triples of the form (b/2, b ± 1, L).
    Expanding the Pythagorean formula, we have L^2 - (5/4)b^2 ± 2b - 1 = 0.

    Let x = (5/2)b ± 2. Then this reduces to the negative Pell equation
    x^2 - 5L^2 = -1.
    """
    generator = util.pell(5, N=-1)
    solutions = [next(generator) for _ in range(n + 1)]
    return sum(L for _, L in solutions[1:]) # skip trivial solution

def problem_139(N=int(1e8)):
    """
    Find the number of Pythagorean triples (a, b, c) such that
    a + b + c < N and a - b divides c.

    Notes
    -----
    TODO: optimize
    """
    count = 0
    for m in range(ceil(sqrt(N / 2))):
        for n in range(1 + (m % 2), m, 2):
            if gcd(m, n) == 1:
                a, b, c = m**2 - n**2, 2*m*n, m**2 + n**2
                if c % (a - b) == 0:
                    count += N // (a + b + c)

    return count

def problem_142(n=3):
    """
    Find the smallest set of n integers such that for any two elements x and y,
    x + y and x - y are both perfect squares.

    TODO: clean up

    Notes
    -----
    Given squares a^2 > b^2 of the same parity, set integers
    x = (a^2 + b^2) / 2 and y = (a^2 - b^2) / 2.
    Then x + y = a^2 and x - y = b^2.

    If a^2 = (x + y) and b^2 = (x - y), then a^2 + b^2 = 2x and a^2 - b^2 = 2y.

    x + y is square
    x + z is square
    x - z is square

    Case: n = 2
    -----------
    We want x + y and x - y to both be squares

    a^2 = x + y
    b^2 = x - y

    x = (a^2 + b^2) / 2
    y = (a^2 - b^2) / 2

    So just pick two squares, 1, 9.
    Then x = 5, y = 4.

    Case: n = 3
    -----------
    a^2 = x + y
    b^2 = x - y
    c^2 = y + z
    d^2 = y - z
    e^2 = x + z
    f^2 = x - z

    2x = a^2 + b^2 = e^2 + f^2
    2y = a^2 - b^2 = c^2 + d^2
    2z = c^2 - d^2 = e^2 - f^2

    2a^2 = c^2 + d^2 + e^2 + f^2


    a^2 = e^2 + f^2 - b^2
    a^2 = c^2 + d^2 + b^2

    e^2 + f^2 - b^2 = c^2 + d^2 + b^2

    
    """
    def make_graph(k):
        graph = defaultdict(set)
        squares = [i*i for i in range(1, k + 1)]
        for i, b in enumerate(squares):
            for a in squares[i+2::2]:
                x, y = (a + b) // 2, (a - b) // 2
                graph[x].add(y)
                graph[y].add(x)
        # for b, a in itertools.combinations(squares, 2):
        #     if (a - b) % 2 == 0:
        #         x, y = (a + b) // 2, (a - b) // 2
        #         graph[x].add(y)
        #         graph[y].add(x)
        
        #print("Graph", k, len(graph), sum(len(v) for v in graph.values()))
        return graph

    k = 1000
    best_clique = []
    while len(best_clique) < n:
        graph = make_graph(k)
        cliques = [clique for clique in util.bron_kerbosch(graph) if len(clique) >= n]
        #print(k, cliques)
        if cliques:
            best_clique = min(cliques, key=lambda c: sum(sorted(c)[:n]))
            #print(best_clique)
            return sum(best_clique)
        else:
            k *= 2

def problem_145(N=int(1e9)):
    """
    Find the number of integers n < N such that the sum [n + reverse(n)]
    consists entirely of odd (decimal) digits.

    TODO: optimize
    """
    ODD_DIGITS = set('13579')
    count = 0
    for i in range(N):
        #if i % 1000000 == 0: print(i)
        if i % 10 == 0:
            continue
        a = str(i + int(str(i)[::-1]))
        if set(a).issubset(ODD_DIGITS):
            count += 1

    return count

def problem_146(N=int(1.5e8)):
    """
    Find the sum of all integers n < N such that n^2 + k forms a 
    run of consecutive primes for k in {1, 3, 7, 9, 13, 27}.

    Notes
    -----
    We can infer that n^2 = 0 mod 10, which implies that n = 0 mod 10.

    Given this and also that all primes p > 3 are of the form 6a ± 1,
    for the prime run to be consecutive we also need to check that
    n^2 + 19 and n^2 + 21 are composite.
    """
    offsets = (1, 3, 7, 9, 13, 27)
    residues = {}
    for p in util.primes(high=100):
        if p in (2, 5): continue
        residues[p] = {
            i for i in range(p)
            if not any((i*i + k) % p == 0 for k in offsets)
        }

    def is_valid(n):
        for p in residues:
            if n % p not in residues[p]:
                return False

        for k in offsets:
            if not util.is_prime(n*n + k):
                return False

        if util.is_prime(n*n + 19) or util.is_prime(n*n + 21):
            return False

        return True

    return sum(n for n in range(10, N, 10) if is_valid(n))

def problem_147(w=47, h=43):
    """
    Find the number of rectangles in a w x h grid that can be formed
    by connecting four distinct points on the grid.

    TODO: UNFINISHED

    Notes
    -----
    The number of vertical / horizontal rectangles in a H x W grid is given by
    T_H * T_W, where T_n is the n-th triangular number (see problem 85).

    The number of diagonal rectangles is 

    1 x 1 = T(1)T(1) + 0 = 1
    1 x 2 = T(1)T(2) + 1 = 4
    1 x 3 = T(1)T(3) + 2 = 8
    1 x 4 = T(1)T(4) + 3 = 13
    1 x 5 = T(1)T(5) + 4 = 19

    2 x 2 : T(2)T(2) + 9 = 9 + 9 = 18
    2 x 3 : T(2)T(3) + 19 = 18 + 19 = 37
    2 x 4 : T(2)T(4) + 29 = 30 + 29 = 59
    2 x 5 : T(2)T(5) + 39 = 45 + 39 = 84

    3 x 3 : T(3)T(3) + 51 = 36 + 51 = 87
    """
    pass

def problem_148(N=int(1e9), p=7):
    """
    Find the number of entries in the first N rows of Pascal's triangle
    that are not divisible by prime p.

    Notes
    -----
    By Lucas's Theorem, a binomial coefficient C(n, k) is divisible by prime p
    if and only if at least one of the base p digits of n is greater than the
    corresponding digit of k.

    Thus the number of binomial coefficients C(n, k) not divisible by p
    is given by prod_i (a_i + 1), where a_i are the digits of n in base p.
    """
    T = lambda n: util.polygonal(3, n)
    assert util.is_prime(p)
    power = 1 # power of T(p) = (1 + 2 + ... + p)^i
    count = 0
    while N > 0:
        N, digit = divmod(N, p)
        count *= (digit + 1)
        count += T(digit) * power
        power *= T(p)

    return count

def problem_179(N=int(1e7)):
    """
    Find the number of integers 1 < n < N such that d(n) = d(n + 1).
    """
    num_divisors = util.get_divisor_counts(N)
    return sum(num_divisors[n] == num_divisors[n + 1] for n in range(2, N))

def problem_188(a=1777, b=1855, n=8):
    """
    Find the last 8 digits of the tetration a ↑↑ b.
    """
    mod = 10**n
    for _ in range(b - 1):
        a = pow(1777, a, mod=mod)

    return a

def problem_206():
    """
    Find unique positive integer whose square has the form 1_2_3_4_5_6_7_8_9_0,
    where each '_' is a single digit.

    TODO: clean up

    1_2_3_4_5_6_7_8_900

    _ _ _ _ _ _ _ _ 3 0

    30 or 70
    03, 43, 53, 83 or None
    
    043
                    
    Notes
    -----
    We know 
        * n must be a 10-digit number where sqrt(1e18) <= n < sqrt(2e18)
        * n must be a multiple of 10
    We know n

    1010101010 < n < 1389026623

    1,929,374,254,627,488,900

    """
    low, high = 1020304050607080900, 1929394959697989900
    low, high = util.round_up(isqrt(low), 10), isqrt(high)
    loop = iter(range(low, high + 1, 10))
    last = False
    for n in loop:
        # print(n*n)
        digits = str(n*n)
        if digits[::2] == '1234567890':
            return n
        # for i in range(2, 4):
        #     if digits[2*i - 2] != str(i):
        #         delta = float(f'8.9e{20 - 2*i}')
        #         delta = int(sqrt(n*n + delta)) - n
        #         next(itertools.islice(loop, delta // 10, delta // 10 + 1))
        #         print("Skipping on digit", i)
        #         break
            # elif digits[2] != '2':
            #     delta = int(sqrt(n*n+8.99999999e16)) - n
            #     next(itertools.islice(loop, delta // 100, delta // 100 + 1))
            #     break
            # elif digits[4] != '3':
            #     delta = int(sqrt(n*n+8.99999999e14)) - n
            #     next(itertools.islice(loop, delta // 100, delta // 100 + 1))
            #     break

def problem_218(N=int(1e16)):
    """
    Find the number of primitive Pythagorean triples (a, b, c) such that
    c is a perfect square and the area ab/2 is not divisible by 6 or 28.

    Notes
    -----
    Let (a, b, c) be a primitive Pythagorean triple:
    
        a = x^2 - y^2, b = 2xy, c = x^2 + y^2

    If c is square, then (x, y, sqrt(c)) is also a primitive Pythagorean triple:

        x = m^2 - n^2, y = 2mn, c = m^2 + n^2

    Then the area of the triangle is:

        A = ab / 2 = 2(m^7)(n) - 14(m^5)(n^3) + 14(m^3)(n^5) - 2(m)(n^7).

    By Fermat's little theorem:

        A mod 7 = (2mn - 2mn) mod 7 = 0
        A mod 3 = (2mn - 14mn + 14mn - 2mn) = 0

    And since one of m, n is even, A mod 4 = 0.

    It follows that A mod 6 = 0 and A mod 28 = 0 for every such triple.
    """
    return 0

def problem_243(threshold=15499/94744):
    """
    Find the smallest integer d such that R(d) = φ(d) / (d - 1) is less than
    the given threshold, where φ is Euler's totient function.

    Notes
    -----
    The function R(d) reaches a new minimimum exactly when d is a multiple of the
    largest primorial less than or equal to d.
    """
    def next_prime(n):
        for a in itertools.count(start=n+1):
            if util.is_prime(a):
                return a

    # Find the largest primorial n such that R(n) >= threshold
    primorial, p = 1, 2
    while util.totient(primorial * p) / (primorial * p - 1) >= threshold:
        primorial *= p
        p = next_prime(p)

    # Increment multiples of the primorial until R(d) < threshold
    for n in itertools.count(start=primorial, step=primorial):
        if util.totient(n) / (n - 1) < threshold:
            return n

def problem_268(N=int(1e16), M=100, k=4):
    """
    Find how many positive integers less than N are divisible by at least
    k distinct primes less than M.

    Notes
    -----
    By the inclusion-exclusion principle, this is the number divisible by k primes,
    minus the number divisible by k + 1 primes, plus the number divisible by
    k + 2 primes, etc.

    Every number that is divisible by k + a primes is divisible by 
    ((k + a) choose k) products of k primes.
    """
    prime_list = list(util.primes(high=M-1))
    count = 0
    for i in range(k, len(prime_list) + 1):
        s = sum(N // prod(factors) for factors in combinations(prime_list, i))
        count += (-1)**(i - k) * comb(i - 1, k - 1) * s

    return count

def problem_277(N=int(1e15), sequence='UDDDUdddDDUDDddDdDddDDUDDdUUDd'):
    """
    Find the smallest positive integer n > N such that the sequence of operations
    "U" (multiply by 3), "D" (divide by 2), and "d" (decrement by 1) on n
    produces the given sequence.

    Notes
    -----
    Any two integers whose sequences begin with the same k elements
    must be equivalent mod 3^k.

    We can reverse-engineer the sequence by starting with the final value and
    working backwards, obtaining a rational number a/b.

    Then the smallest integer that produces our sequence is n = a * b^(-1) mod 3^k,
    where b^(-1) is the modular inverse of b mod 3^k.
    """
    a, b = 1, 1
    for step in reversed(sequence):
        if step == 'D':
            a *= 3
        elif step == 'U':
            a, b = 3*a - 2*b, 4*b
        elif step == 'd':
            a, b = 3*a + b, 2*b

    mod = 3**len(sequence)
    n = a * pow(b, -1, mod=mod)
    return N + (n - N) % mod

def problem_304(N=100000, k=int(1e14), m=1234567891011):
    """
    Find the sum of F(p) for the first N primes greater than k,
    where F(i) is the i-th Fibonacci number.

    Notes
    -----
    By the prime number theorem, the number of primes between k and k + x is
    approximately x / log(k).
    """
    # Get the first N primes greater than k
    prime_list = list(util.primes(low=k, num=N))

    # Calculate Fibonacci numbers mod m
    p_min, p_max = prime_list[0], prime_list[-1]
    prime_list = set(prime_list)
    fib = util.fibonacci_numbers(
        util.fibonacci(p_min, m), util.fibonacci(p_min + 1, m), mod=m)
    fib = zip(range(p_min, p_max + 1), fib)

    return sum(F for i, F in fib if i in prime_list) % m

def problem_407(N=int(1e7)):
    """
    TODO: write problem description and optimize
    """
    def M(n):
        prime_factorization = Counter(util.prime_factors(n))
        prime_powers = [p**e for p, e in prime_factorization.items()]
        # roots = list(itertools.product(*(
        #     hensel(p, e, (0, -1, 1)) for p, e in prime_factorization.items())))
        

        roots = itertools.product((0, 1), repeat=len(prime_powers))
        
        solutions = [
            util.crt(list(zip(tuple(a), prime_powers)))
            for a in roots
        ]
        x = max(solutions)
        return x

    total = 0
    for n in range(2, N + 1):
        if n % 1000 == 0: print(n)
        total += M(n)
    
    return total
    # # return sum(M(n) for n in range(2, N + 1))
    
    # for n in range(2, 100):
    #     print(n, M(n), M(n)**2 % n)

def problem_451(N=int(2e7)):
    """
    Let I(n) be the largest integer x < n - 1 such that x^2 = 1 mod n.
    Find the sum of I(3) + I(4) + ... + I(N).

    TODO: clean up

    Notes
    -----
    We are looking for non-trivial solutions to x^2 - 1 = (x - 1)(x + 1) = 0 mod n.
    One way to do this is to iterate over divisors.

    If n has a primitive root, then the only solutions to x^2 = 1 mod n
    are x = ±1, and thus I(n) = 1.

    Otherwise, we can decompose n as a product of prime powers,
    and use the Chinese remainder theorem to find solutions to x = ±1 mod p^e.
    """
    def I2(n):
        return next((x for x in range(n - 2, 0, -1) if x*x % n == 1))

    def has_primitive_root(prime_factorization):
        if len(prime_factorization) == 1:
            return 2 not in prime_factorization or prime_factorization[2] <= 2
        elif len(prime_factorization) == 2:
            return 2 in prime_factorization and prime_factorization[2] == 1

        return False

    prime_factorizations = util.get_prime_factorizations(N)


    roots = [[()] for _ in range(N + 1)]
    for p in util.primes(high=N):
        for e in range(1, int(log(N, p)) + 1):
            power = p**e
            p_roots = (1, -1)
            for i in range(power, N + 1, power):
                roots[i] = [
                    (*x, root)
                    for x in roots[i]
                    for root in p_roots
                ]

    print(list(roots[24]))

    def I(n):
        prime_factorization = dict(prime_factorizations[n])
        if has_primitive_root(prime_factorization):
            return 1

        if n % 8 == 0:
            prime_factorization[2] -= 1

        prime_powers = [p**e for p, e in prime_factorization.items()]
        solutions = [
            util.crt(list(zip(tuple(a), prime_powers)))
            for a in itertools.product((-1, 1), repeat=len(prime_powers))
        ]

        x = sorted(set(solutions))[:-1][-1]
        return x + n // 2 if n % 8 == 0 else x

    total = 0
    for n in range(3, N + 1):
        # print(n, I(n))
        # assert I(n) == I2(n), (n, I(n), I2(n))
        if n % 10000 == 0: print(n)
        total += I(n)

    return total
    return sum(I(n) for n in range(3, N + 1))

def problem_500(n=500500, m=500500507):
    """
    Find the smallest number (mod m) with exactly 2^500500 divisors.

    Notes
    -----
    The smallest number with at least 2^n divisors is the product of the
    first n Fermi-Dirac primes.
    """
    prime_generator = util.primes()
    heap = [next(prime_generator)]
    next_prime = next(prime_generator)
    count, product = 0, 1

    while count < n:
        p = heappop(heap)
        product = (product * p) % m
        count += 1

        heappush(heap, p*p)
        while next_prime < heap[0]:
            heappush(heap, next_prime)
            next_prime = next(prime_generator)

    return product

def problem_501(N=int(1e12)):
    """
    Find the number of integers n <= N such that n has exactly 8 divisors.

    Notes
    -----
    Either n = pqr, n = p^3 * q, or n = p^7, where p, q, r are prime.
    """
    initial_primes = tuple(util.primes(high=2*util.iroot(N*N, 3)))
    pi = cache(lambda n: util.count_primes(n, initial_primes=initial_primes))

    # Count primes p such that p^7 <= N
    count = pi(util.iroot(N, 7))

    # Count primes p, q such that p != q and p^3 * q <= N
    for p in util.primes(high=util.iroot(N//2, 3)):
        n = N // (p*p*p)
        count += pi(n) - (p <= n)

    # Count primes p, q, r such that p < q < r and pqr <= N
    for p in util.primes(high=util.iroot(N, 3)):
        for q in util.primes(low=p+1, high=isqrt(N//p)-1):
            n = N // (p*q)
            print(p, q, n)
            count += pi(n) - pi(q)

    return count

def problem_668(N=int(1e10)):
    """
    Find the number of "smooth" integers n <= N, numbers where
    all of its prime factors are strictly less than its square root.

    Notes
    -----
    For each prime p, we have non-smooth numbers: p, 2p, ..., (p - 1)p, p^2.
    Then this is equivalent to the sum of min(p, N // p) over primes p <= N.
    """
    initial_primes = tuple(util.primes(high=2*util.iroot(N*N, 3)))
    pi = cache(lambda n: util.count_primes(n, initial_primes=initial_primes))

    # Direct sum for primes less than sqrt(N)
    count = sum(util.primes(high=isqrt(N)))

    # Use prime counting for primes greater than sqrt(N)
    for n in range(1, isqrt(N) + 1):
        count += n * (pi(N // n) - pi(N // (n + 1)))

    return N - count


def problem_800(base=800800, exp=800800):
    """
    Find the number of integers p^q * q^p < N, where p and q are prime
    and N = base^exp.

    Notes
    -----
    Without loss of generality, assume p < q.
    Then 2^q < p^q * q^p < N, which implies upper bound p < q < log_2(N).
    """
    import bisect
    count = 0
    log_N = exp * log(base)
    prime_list = tuple(util.primes(high=int(log_N/log(2))))
    for i, p in enumerate(prime_list):
        # Find the number of primes q > p such that qlog(p) + plog(q) >= log(N)
        log_p = log(p)
        key = lambda j: prime_list[j] * log_p + p * log(prime_list[j])
        num_primes = bisect.bisect_right(range(i + 1, len(prime_list)), log_N, key=key)
        count += num_primes
        if num_primes == 0:
            break

    return count

def problem_836():
    """
    April Fools!
    """
    return 'aprilfoolsjoke'



if __name__ == '__main__':
    import argparse
    import cProfile

    parser = argparse.ArgumentParser()
    parser.add_argument('--problem', type=int)
    parser.add_argument('--profile', action='store_true')
    parser.add_argument('config', nargs='*', default=[], type=int)
    args = parser.parse_args()

    problem = eval(f'problem_{args.problem}')
    compute_answer = lambda: print(problem(*args.config))
    # compute_answer()
    # def compute_answer():
    #     for i in range(10):
    #         problem(*args.config)
    if args.profile:
        cProfile.run('compute_answer()', sort='cumtime')
    else:
        compute_answer()

# # # # TODO: get #14 under 0.1s, get #60 under 1s


# import timeit
# for i in range(1, 900):
#     try:
#         problem = eval(f'problem_{i}')
#         t = timeit.timeit('problem()', number=1, globals=globals())
#         print(i, f'{t:.6f}', 'seconds')
#     except:
#         pass

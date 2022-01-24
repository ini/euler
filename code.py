import itertools
import math
import random

import misc
import primes



def problem_1(upto=1000):
    # Sum of first n multiples of k is equal to k * n * (n+1) / 2
    def sum_multiples(k, upto=upto):
        num_multiples = (upto - 1) // k
        return k * num_multiples * (num_multiples + 1) // 2

    return sum_multiples(3) + sum_multiples(5) - sum_multiples(3 * 5)


def problem_2(upto=int(4e6)):
    # Binet's closed-form formula for the n-th Fibonacci number
    phi, psi = (1 + 5**0.5) / 2, (1 - 5**0.5) / 2 # golden ratio (and negative reciprocal)
    fib = lambda n: int((phi**n - psi**n) / (phi - psi))

    # The even Fibonacci numbers are F_{3i} for integers i
    # Find index of largest even Fibonacci number not exceeding `upto`
    n = int(math.log(upto * 2 * 5**0.5 + 0.5, phi))
    n -= n % 3

    # The sum of F_{3i} from i = 1 ... n = (F_{3n+2} - 1) / 2
    return (fib(n + 2) - 1) // 2


def problem_3(n=600851475143):
    return max(primes.prime_factors(n))


def problem_4(digits=3):
    n_min, n_max = 10**(digits - 1), 10**digits - 1
    is_palindrome = lambda n: str(n) == str(n)[::-1]
    max_palindrome = 0

    for a in range(n_max, n_min - 1, -1):
        # Assuming the max palindrome has length 2*digits, 
        # either a or b must be divisible by 11
        k = -1 if a % 11 == 0 else -11 # decrement value
        for b in range(a - (a % 11), n_min - 1, k):
            if a * b <= max_palindrome:
                break
            if is_palindrome(a * b) and a * b > max_palindrome:
                max_palindrome = a * b

    return max_palindrome


def problem_5(upto=20):
    # LCM(1, ... N) = product of {p^(log_p N) : p <= N}
    prime_powers = [p ** int(math.log(upto, p)) for p in primes.sieve(upto)]
    return misc.prod(prime_powers)
    

def problem_6(upto=100):
    # Apply Faulhaber's formula for k = 1 and k = 2
    square_of_sums = (upto * (upto + 1) // 2) ** 2
    sum_of_squares = upto * (upto + 1) * (2*upto + 1) // 6
    return square_of_sums - sum_of_squares


def problem_7(n=10001):
    # By the prime number theorem, the n-th prime is roughly n * ln(n)
    x = n * int(math.log(n))
    sieve = primes.sieve(x)
    while len(sieve) < n:
        x *= 2
        sieve = primes.sieve(x)

    return sieve[n - 1]


def problem_8(path='data/problem_8.txt', k=13):
    with open(path) as file:
        number = ''.join([line.strip() for line in file.readlines()])

    number = [int(d) for d in number] # convert to a list of digits (as integers)
    return max([misc.prod(number[i : i + k]) for i in range(len(number) - k)])


def problem_9(s=1000):
    # Use Euclid's algorithm to generate primitive triples
    for m in range(int(s**0.5)):
        for n in range(1, m):
            if math.gcd(m, n) == 1 and not (m & 1 and n & 1): # coprime, not both odd
                a, b, c = (m**2 - n**2), (2 * m * n), (m**2 + n**2)
                if s % (a + b + c) == 0:
                    k = s // (a + b + c)
                    return k**3 * a * b * c
                

def problem_10(n=int(2e6)):
    return sum(primes.sieve(n))


def problem_11(path='data/problem_11.txt', k=4):
    with open(path) as file:
        grid = [[int(i) for i in line.strip().split(' ')] for line in file.readlines()]

    H, W = len(grid), len(grid[0])
    rows, cols = [[] for _ in range(H)], [[] for _ in range(W)]
    diagonals, anti_diagonals = [[] for _ in range(H + W - 1)], [[] for _ in range(H + W - 1)]

    # Generate rows, columns, diagonals, and antidiagonals
    for r in range(H):
        for c in range(W):
            rows[r].append(grid[r][c])
            cols[c].append(grid[r][c])
            diagonals[r + c].append(grid[r][c])
            anti_diagonals[H - r + c - 1].append(grid[r][c])

    # Find max product of sub-segment of length k
    segments = rows + cols + diagonals + anti_diagonals
    products = [misc.prod(segment[i : i + k]) for segment in segments for i in range(len(segment) - k)]
    return max(products)


def problem_12(k=500):
    # of divisors for integer n
    cache = {}
    def D(n):
        if n not in cache:
            factorization = primes.prime_factors(n, return_counts=True)
            cache[n] = misc.prod([k + 1 for k in factorization.values()])
        return cache[n]

    for n in itertools.count(1):
        if n & 1: # n is odd
            d = D((n + 1) // 2) * D(n)
        else: # n is even
            d = D(n // 2) * D(n + 1)
        
        if d > k:
            return n * (n + 1) // 2 # the n-th triangle number


def problem_13(path='data/problem_13.txt', digits=10):
    with open(path) as file:
        numbers = [int(line.strip()) for line in file.readlines()]
        return str(sum(numbers))[:digits]


def problem_14(k=int(1e6)):
    cache = {1: 1}
    def collatz(n):
        if not n in cache:
            next_n = (n // 2) if n % 2 == 0 else (3 * n + 1)
            cache[n] = 1 + collatz(next_n) 
        return cache[n]

    return max(range(1, k), key=collatz)
    

def problem_15(H=20, W=20):
    return misc.choose(H + W, H) # calculates (H + W) choose H


def problem_16(n=1000):
    return sum(map(int, str(2**n)))


def problem_17():
    sum_1_to_9 = len('onetwothreefourfivesixseveneightnine')
    sum_10_to_19 = len('teneleventwelvethirteenfourteenfifteensixteenseventeeneighteennineteen')
    sum_20_to_99 = 10 * len('twentythirtyfortyfiftysixtyseventyeightyninety') + 8 * sum_1_to_9
    sum_1_to_99 = sum_1_to_9 + sum_10_to_19 + sum_20_to_99
    sum_100_to_999 = (100 * sum_1_to_9) + 9 * (100 * len('hundred') + 99 * len('and') + sum_1_to_99)
    return sum_1_to_99 + sum_100_to_999 + len('onethousand')


def problem_18(path='data/problem_18.txt'):
    with open(path) as file:
        pyramid = [[int(i) for i in line.strip().split(' ')] for line in file.readlines()]

    for i in range(len(pyramid) - 2, -1, -1):
        for j in range(len(pyramid[i])):
            pyramid[i][j] += max(pyramid[i + 1][j], pyramid[i + 1][j + 1])

    return pyramid[0][0]


def problem_19():
    import datetime
    count = 0
    for year in range(1901, 2001):
        for month in range(1, 13):
            if datetime.date(year, month, 1).weekday() == 6: # Sunday
                count += 1
    return count


def problem_20(n=100):
    return sum(map(int, str(math.factorial(n))))


def problem_21(upto=10000):
    # Calculate sum of *proper* divisors for each n
    d = [0] + [sum(primes.divisors(n)) - n for n in range(1, upto)]
    d += [sum(primes.divisors(n)) - n for n in range(upto, max(d) + 1)] 

    total = 0
    for n in range(upto):
        if n == d[d[n]] and n != d[n]: # n is an "amicable" number 
            total += n
            print(n, d[n])

    return total


def problem_22(path='data/problem_22.txt'):
    with open(path) as file:
        names = sorted([name.strip('"') for name in ''.join(file.readlines()).split(',')])

    char_value = lambda c: ord(c.upper()) - ord('A') + 1
    return sum([(i + 1) * sum([char_value(c) for c in names[i]]) for i in range(len(names))])

def problem_25(digits=1000):
    # Find index of largest Fibonacci number not exceeding `10**(digits - 1)`
    phi = (1 + 5**0.5) / 2 # golden ratio
    n = (digits - 1) * math.log(10, phi) + math.log(2 * 5**0.5 + 0.5 * 10**(-digits + 1), phi)
    print(n)
    return int(n)


def problem_67(path='data/problem_67.txt'):
    return problem_18(path=path)


#print(problem_21())


import cProfile
#cProfile.run('for i in range(1): problem_22()')

cProfile.run('problem_12(k=1000)')



#print(problem_12(k=5000))


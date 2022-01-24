import decimal
from decimal import Decimal
decimal.getcontext().prec = 100



from misc import choose, prod
import primes


def divisors(n):
    factors = primes.prime_factors(n, return_counts=True)
    div = [1]
    for p, r in factors.items():
        div = [d * p**e for d in div for e in range(r + 1)]
    return sorted(div)

def base_coefs(n, b):
    coefs = []
    while n != 0:
        coefs.append(n % b)
        n //= b
    return coefs

def alpha(n, x):
    if not primes.is_prime(x):
        return sum([pow(7, k//2, x) * (choose(n, k) % x) for k in range(0, n + 1, 2)])
        return (round(Decimal(0.5) * ((Decimal(1) + Decimal(7)**Decimal(0.5))**n + (Decimal(1) - Decimal(7)**Decimal(0.5))**n))) % x
    
    a = 1
    n_coefs = base_coefs(n, x)
    for k in range(2, n + 1, 2):
        k_coefs = base_coefs(k, x)
        a += pow(7, k//2, x) * prod([choose(n_i, k_i) for n_i, k_i in zip(n_coefs, k_coefs)], x)
    return a % x

def beta(n, x):
    if not primes.is_prime(x):
        return (round(Decimal(0.5) * ((Decimal(1) + Decimal(7)**Decimal(0.5))**n - (Decimal(1) - Decimal(7)**Decimal(0.5))**n) / Decimal(7)**Decimal(0.5))) % x

    b = n % x
    n_coefs = base_coefs(n, x)
    for k in range(3, n + 1, 2):
        k_coefs = base_coefs(k, x)
        b += pow(7, k//2, x) * prod([choose(n_i, k_i) for n_i, k_i in zip(n_coefs, k_coefs)], x)
    return b % x



alpha_0 = lambda n: (round(Decimal(0.5) * ((Decimal(1) + Decimal(7)**Decimal(0.5))**n + (Decimal(1) - Decimal(7)**Decimal(0.5))**n)))
beta_0 = lambda n: (round(Decimal(0.5) * ((Decimal(1) + Decimal(7)**Decimal(0.5))**n - (Decimal(1) - Decimal(7)**Decimal(0.5))**n) / Decimal(7)**Decimal(0.5)))
f = lambda n: (Decimal(1) + Decimal(7)**Decimal(0.5))**n


import math
def g(x):
    if primes.is_prime(x):
        for n in divisors(x**2 - 1):
            if alpha(n, x) == 1 and beta(n, x) == 0:
                return n
    else:
        for n in range(1, x**4):
            if alpha(n, x) == 1 and beta(n, x) == 0:
                return n
    return 0


def G(N):
    return sum([g(x) for x in range(2, N+1)])


#i, x = 4, 3
#print(i, x, alpha(i) % x, alpha_0(i, x))
#'''
#for x in primes.sieve(10**3):
'''
x = 11**2
for k in range(1, x**2):
    n = 60 * k
    if k % 100 == 0: print(k)
    if alpha(n, x) == 1 and beta(n, x) == 0:
        print("test", k, alpha(n, x), beta(n, x))
'''

print(alpha(78660, 121), beta(78660, 121))

for n in divisors(78660):
    print(n, alpha(n, 121), beta(n, 121))


#print(g(x))
'''
for x in range(2, 100):
    z = g(x)
    print(x, z)
'''

#'''



'''
print(alpha(3), beta(3), alpha(12), beta(12))
print(g(49))
for x in range(30):
    if g(x) > 0:
        print(x, g(x))
'''

# g(2^n) = 27
# 

'''
print(g(27), "eelenv")
for i in range(1, 30):
    print(i, alpha(i), beta(i), f(i) - alpha(i) - beta(i) * Decimal(7)**Decimal(0.5))

print()
for x in range(3, 50, 2):
    print(x, g(x))
print()
'''


"""
alpha(0) = 1
alpha(1) = 1
alpha(2) = 8
alpha(3) = 22

beta(0) = 0
beta(1) = 1
beta(2) = 2
beta(3) = 10

 

For n > 2, alpha(n) and beta(n) must both be even, i.e. alpha(n) != 1 mod 2
and since beta(1) != 0 mod 2, we know g(2) != 1, which implies g(2) = 0.

Also, alpha(n) != 1 mod 2 => alpha(n) != 1 mod x for any even x,
which implies g(x) = 0 for all even x.

We can show that for all n, alpha(n) = 1 mod 7 and beta(n) = n mod 7,
which implies g(7) = 7.

What about g(9)? Well we know that g(3) = 0, i.e. there exists no n 
such that alpha(n) = 1 mod 3 and beta(n) = 0 mod 3. 
It follows that g(9) = 0 (and more generally, g(x) = 0 when 3 | x). 

So what's interesting now is:
    1) what is g(p) for the rest of the primes?
    2) what is g(p^k)?    g(25)? g(49)? g(125)?
    3) what is g(pq)?    g(35)? g(55)? g(29 * 37)?
    4) what is g(n)?

My hunch is that g is multiplicative, so we only need to answer 1) and 2) 

If the code is to be believed, g(25) = 60, and g(49) = 49.
This suggests that g(p^k) = g(p) * p^{k-1}.
??? Prove this ??? We'll assume it for now.

If the code is to be believed, g(35) = 84.

So now all that remains is to find 

# g(2) = 0
# g(3) = 0
# g(4) = 0
# g(5) = 12 = 2^2 * 3    or 12 % 7 = 5    or g(5) = (5^2 - 1) / 2
# g(6) = 0
# g(7) = 7
# g(8) = 0
# g(9) = 0
# g(10) = 0
# g(11) = 60 = 2^2 * 3 * 5    or 60 % 49 = 11    or g(11) = (11^2 - 1) / 2
# g(12) = 0
# g(13) = 168 = 2^3 * 3 * 7    or g(13) = 13^2 - 1
# g(14) = 0
# g(15) = 0
# g(16) = 0
# g(17) = 288 = 2^5 * 3^2    or g(17) = 17^2 - 1
# g(18) = 0
# g(19) = 18 = 2 * 3^2    or g(19) = (19^2 - 1) / 20
# g(20) = 0



# g(23) = 176    or g(23) = (23^2 - 1) / 3          
# g(29) = 7      or g(29) = (29^2 - 1) / 120
# g(31) = 30     or g(31) = (31^2 - 1) / 32
# g(37) = 12     or g(37) = (37^2 - 1) / 114
# g(41) = 560    or g(41) = (41^2 - 1) / 3
# g(43) = 264    or g(43) = (43^2 - 1) / 7
# g(47) = 46     or g(47) = (47^2 - 1) / 48
# g(53) = 52     or g(53) = (53^2 - 1) / 54
# g(59) = 29     or g(59) = (59^2 - 1) / 120
# g(61) = 3720   or g(61) = (61^2 - 1) / 1
# g(67) = 4488   or g(67) = (67^2 - 1) / 1

5 -> 3
11 -> 6
23 -> 8
41 -> 14


what the hell is the pattern?

g(p) divides p^2 - 1                 (except for p = 7)
if g(p) < p then g(p) divides p-1    (and not p+1)


p^2 - 1 = k * g(p)
p^2 = k * g(p) + 1

k * g(p) = -1 mod p^2

g(19), g(31), g(47), g(53), g(109), g(113), g(137), g(139), g(149) all have g(p) = p - 1


g(13), g(17), g(61), g(67), g(71), g(89), g(157) all have g(p) = p^2 - 1 = (p - 1)(p + 1)


others
g(11), g(23), g(29), g(37), g(41), g(43), g(59), g()





which ones are the same?
g(5), g(11), g(73), g(127), g(151) all use d=2
g(23), g(41) both use d=3
g(29), g(59) both use d=120


11, 2
13, 1
17, 1
19, 20
23, 3
29, 120
31, 32


f

1
2
3
7
8 = 2^3
20 = 2^2 * 5




g(25) = 60





"""
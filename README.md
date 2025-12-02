# Euler

`euler.py` is a single-file, zero-dependency toolkit for primes, factorization, modular arithmetic, combinatorics, Diophantine equations, graphs, and more. It is tuned for speed and readability, and you can drop it anywhere you have Python 3.10+. `solve.py` is a gallery of my Project Euler solutions that show the toolkit in action and provide a CLI. Everything below is grouped exactly as in `euler.py`.

### Quick use (REPL)
```python
>>> import euler as e
>>> e.is_prime(1_000_000_007)
True
>>> list(e.primes(high=30))
[2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
>>> e.count_primes(10**10)
455052511
>>> e.sum_primes(10**10)
2220822432581729238
>>> e.prime_factorization(987654321)
defaultdict(<class 'int'>, {3: 2, 17: 2, 379721: 1})
>>> e.multiplicative_order(10, 97)
96
>>> next(e.pell(13))
(649, 180)
```

## API reference (`euler.py`)

### Primes
`is_prime(n)` uses deterministic Miller-Rabin through 2^64 and Baillie-PSW beyond (no known pseudoprimes), after a small-wheel trial division. Complexity is O(log^3 n) for the Miller-Rabin rounds with an O(log n) Lucas step.

`next_prime(n)` simply advances odd candidates through `is_prime()`; the expected work is one primality test plus the local prime gap.

`primes(low=2, high=inf, num=inf)` runs a segmented sieve of Eratosthenes, generating at most `num` primes over the inclusive interval `[low, high]`. This also supports unbounded generation when `high` and `num` are left infinite. Complexity is O((high-low) log log high) when bounded, or O(n log log n) to emit n primes; memory tracks the current segment.

`count_primes(x)` uses the Lagarias-Miller-Odlyzko (Meissel-Lehmer) algorithm for π(x), combining Legendre's φ recursion with partial summation. Complexity is about O(x^(2/3) / log x) time and O(x^(2/3)) space.

`sum_primes(x, f=None, f_prefix_sum=None, intermediate_sums=False)` applies Lucy/LMO-style prime summation to a completely multiplicative f (default f(n)=n), yielding ∑_{p≤x} f(p) with the same ~O(x^(2/3)) time/space as LMO; `intermediate_sums` can expose the partial sums.

### Factorization
`prime_factors(n)` mixes trial division over tiny primes with Pollard-Brent rho until only primes remain; expected time is about O(n^(1/4)) on random composites, governed by the smallest factor.

`prime_factorization(n)` collects the exponents from `prime_factors()` into a Counter.

`divisors(n)` enumerates all divisors by expanding each prime power against the current divisor list; time is proportional to the number of divisors times the number of prime factors.

### Multiplicative Functions
`totient(n)` multiplies p^(k-1)*(p-1) from the factorization; O(ω(n)).

`jacobi(a, n)` iteratively applies quadratic reciprocity with 2-adic reductions; O(log n).

`divisor_count_range(N)` builds smallest prime factors once, then updates divisor counts with exponent tracking; O(N) memory and near-linear time.

`divisor_function_range(N, k=1)` generalizes σ_k with multiplicative recurrences on the SPF table; O(N) time and memory, with a fast path for k=0.

`aliquot_sum_range(N)` derives σ(n)-n from the σ table.

`totient_range(N)` uses SPF and multiplicative rules φ(p^k)=p^(k-1)(p-1) and φ(p*m)=φ(m)*(p-1) when p does not divide m; O(N).

`mobius_range(N)` computes μ(n), flagging square factors via SPF; O(N).

`radical_range(N)` accumulates the product of distinct primes via SPF; O(N).

### Modular Arithmetic
`egcd(a, b)` is an iterative extended Euclid; O(log min(a, b)).

`crt(residues, moduli)` folds congruences two at a time, reducing by gcd to detect inconsistency and multiplying moduli; O(k log M) where k is the count of congruences and M is the product of moduli.

`hensel(p, k, a, initial=None)` lifts roots of a polynomial modulo p up to p^k, distinguishing simple roots (unique lift) from multiple roots (branching up to p lifts); roughly O(k * deg * branches).

`multiplicative_order(a, n)` factors φ(n) implicitly via its divisors and tests powers with modular exponentiation; O(τ(φ(n)) * log n * log φ(n)) in practice.

### Combinatorics
`pascal(num_rows=None)` streams rows with O(1) extra memory beyond the current row; total time O(n^2) for n rows.

`partition_numbers(mod=None)` uses the Euler pentagonal recurrence; time O(n^(3/2)) for the first n terms and O(n) memory, optionally reduced modulo `mod`.

`count_partitions(n, restrict=None)` either plugs a restriction into the Euler transform or indexes into the generated partition stream; same complexity as above for unrestricted counts.

`euler_transform(a)` wraps a sequence with cached transforms and divisor sums; time O(n * d(n)) for the first n terms.

### Pell Equations
`pell(D, N=1)` follows the Lagrange-Matthews-Mollin method: it builds the periodic continued fraction for sqrt(D), finds fundamental solutions, and generates all solutions by composition with the fundamental unit. Each step is polynomial in the period length; generation after setup is linear in the number of solutions produced.

`periodic_continued_fraction(D, P=0, Q=1)` computes the preperiod and period for (P + sqrt(D))/Q via the standard recurrence; time linear in the period length.

`convergents(coefficients, num=None)` runs the classic numerator/denominator recurrence; O(num).

### Pythagorean Triples
`pythagorean_triples(max_c=None, max_sum=None)` uses Euclid's formula on coprime, opposite-parity (m, n) pairs to generate primitive triples, then scales by k within bounds. In the unbounded case it walks Berggren's tree with a heap keyed by c to stay ordered; generation is linear in the number of triples emitted.

### Fibonacci Numbers
`fibonacci(i, mod=None)` uses Binet for small i and fast-doubling identities for large or negative i; each call is O(log |i|) time and O(1) space, with optional modular reductions.

`fibonacci_index(base, exp=1)` estimates via logs (φ), then adjusts with nearby Fibonacci evaluations; dominated by a few O(log n) Fibonacci calls.

`fibonacci_numbers(a=0, b=1, mod=None)` is a simple generator with O(1) state per yield.

### Polygonal Numbers
`triangle`, `polygonal`, and `polygonal_index` are direct formulas. `polygonal_numbers` increments through the sequence with O(1) state. `is_polygonal` checks a discriminant and an integer-square test. `is_square` uses quick residue filters plus integer sqrt. `non_squares`, `squares`, and `cubes` stream values with O(1) state; the square/cube generators use difference-of-squares/-cubes updates.

### Graphs
`search` is a generic DFS over an explicit stack. `dijkstra` is the standard binary-heap implementation; O((V + E) log V). `bron_kerbosch` is the recursive pivoting variant; worst case exponential in clique size. `kruskal` uses union-find with path compression and union by rank; O(E log E). `topological_sort` is DFS-based with cycle detection; O(V + E). `find_cycles` builds on `search` to report directed cycles. `find_functional_cycles` walks a functional graph marking first-visit nodes to recover cycles in O(n) over the explored domain.

### Linear Algebra
`linear_solve` performs Gauss-Jordan elimination in-place; O(m n^2) for an m x n system (square reduces to O(n^3)). `identity_matrix`, `matrix_apply`, `matrix_transpose`, `matrix_sum`, `matrix_difference`, and `matrix_product` are straightforward, with `matrix_product` in O(n^3) for dense matrices.

### Constraint Satisfaction
`csp` is a backtracking search with the minimum-remaining-values heuristic; worst case exponential in variable count, but MRV prunes heavily when domains shrink.

### Digits
`digit_sum` chunks by a power-of-ten modulus to keep string conversions bounded; linear in digit count. `digit_count` uses string length for small numbers and integer log otherwise. `digit_combinations` enumerates digit multisets via combinations-with-replacement and counts permutations combinatorially. `digit_permutations` runs a backtracking permutation generator with leading-zero checks. `digits_in_base` does repeated division and handles negative bases by carrying; all are linear in digit count. `is_palindrome`, `is_permutation`, and `has_repeated_digits` are string/set checks.

### Miscellaneous
`nth` fetches the 1-based nth element via `islice`. `group_by_key` and `group_permutations` bucket elements by key. `powerset` yields combinations in increasing size; total time O(2^n). `disjoint_subset_pairs` enumerates disjoint pairs with optional size constraints; exponential in input size. `polynomial` builds a Horner evaluator (O(deg) per call). `iroot` uses Newton iteration to the integer floor (O(log n) iterations). `ilog` grows powers by squaring to find bounds, then binary searches (O(log n)). `binary_search` wraps bisect over a monotone predicate, expanding bounds geometrically.

### Fenwick Trees
- Internal helpers (`_fenwick_tree_*`) used by the prime-summing internals; no public entry points here. All are O(log n) per query/update with O(n) build time.

### Constants
- Internal `_int_str_mod()` sets the chunk size used when converting very large ints to strings for digit sums.

## Project Euler solutions (`solve.py`)
- Functions `problem_<n>()` with brief notes/docstrings.
- Minimal CLI:
  ```bash
  python solve.py --problem 1
  python solve.py --problem 8 13         # positional ints forwarded to the function
  python solve.py --problem 19 --profile # cProfile the run
  python solve.py --problem 1 --num 100  # repeat N times
  ```
- Some problems read inputs from `data/` (e.g., 8, 22, 54). Keep those files in place or adjust paths.

## Repo layout
- `euler.py` - the drop-in toolkit.
- `solve.py` - Project Euler implementations + CLI runner.
- `data/` - input files for certain problems.

## Requirements
- Python 3.10+.
- No external dependencies.

## License
MIT with attribution to Ini Oguntola. Use, copy, modify, redistribute-keep the credit.

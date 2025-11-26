# Euler

`euler.py` is a single-file, zero-dependency toolkit for primes, factorization, modular arithmetic, combinatorics, Diophantine equations, graphs, and more. It’s tuned for speed and readability, and you can drop it anywhere you have Python 3.10+. `solve.py` is a gallery of Project Euler solutions that show the toolkit in action and provide a CLI.

## Why you’ll want to explore this
- **One file, no strings attached** — pure Python, no installs. Copy `euler.py` into a repo, notebook, or contest folder and go.
- **Uncommon depth in Python**  
  - LMO prime counting (`count_primes`) and prime summation (`sum_primes`), extending Lucy’s algorithm to arbitrary completely multiplicative functions, accelerated with Fenwick trees.  
  - Deterministic Miller–Rabin to 2^64 + Baillie–PSW fallback (`is_prime`); segmented sieve (`primes`).  
  - Pollard–Brent rho factorization; Legendre φ helpers; cached primes with a thread-safe growth lock.  
  - Hensel lifting for polynomial congruences; multiplicative order, CRT, Jacobi; totient/Möbius/divisor/aliquot sieves.  
  - Generalized Pell solver via Lagrange–Matthews–Mollin (LMM) using periodic continued fractions and convergents.  
  - Partitions and Euler transform; Fibonacci/polygonal sequences; combinatorics utilities.  
  - Graph algorithms (Dijkstra, Kruskal, topological sort, Bron–Kerbosch), functional cycle finder, Fenwick trees, CSP backtracker, digit/base utilities.
- **Living examples** — dozens of Euler problems in `solve.py` double as tests and recipes.

## Feature tour (`euler.py`)
- **Primes**: `is_prime`, `primes` (segmented sieve), `count_primes` (LMO), `sum_primes` (Lucy/LMO generalized), `next_prime`.
- **Factorization**: `prime_factors`, `prime_factorization`, divisors, Pollard–Brent rho helper.
- **Modular arithmetic**: CRT, extended GCD, Hensel lifting, multiplicative order, Jacobi symbol.
- **Multiplicative functions**: totient, Möbius, divisor functions, aliquot sums, sieved ranges.
- **Continued fractions & Diophantine**: periodic CFs, convergents, Pell solver (LMM), integer roots/logs.
- **Sequences & combinatorics**: Fibonacci, polygonal numbers, partitions, Pascal, Euler transform, power sets.
- **Graphs & data structures**: Dijkstra, Kruskal, topological sort, clique finder, Fenwick trees, CSP backtracking helper.
- **Digits & misc**: palindromes, permutations, digit sums/counts, base conversion, grouping utilities.

Functions are grouped by topic inside `euler.py` with docstrings.

### Quick use
```python
import euler as e

e.is_prime(1_000_000_007)
list(e.primes(high=1000))
e.count_primes(10**10)
e.sum_primes(10**9)
e.prime_factorization(987654321)
e.multiplicative_order(10, 97)
next(e.pell(13))  # first solution to x^2 - 13y^2 = 1
```

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
- `euler.py` — the drop-in toolkit (star of the show).
- `solve.py` — Project Euler implementations + CLI runner.
- `working.py` — scratch space (ignored by git).
- `data/` — input files for certain problems.
- `.gitignore` — keeps local data/scratch out of version control.
- `LICENSE` — MIT with attribution.

## Requirements
- Python 3.10+.
- No external dependencies.

## License
MIT with attribution to Ini Oguntola. Use, copy, modify, redistribute—keep the credit.

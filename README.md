# The greatest density of a set in the square lattice whose points have few neighbours

A point of `ℤ²` has eight neighbours. Let `δ(n)` be the greatest density of a set `S` such that every point of `S` has at most `n`
neighbours in `S`. This project proves in Lean 4 that `δ(3) = 1/2`, `δ(4) = 3/5` and `δ(5) = 9/13`.

| Theorem | Statement |
|---|---|
| `LatticeDensity.isGreatest_upperDensity_three` | `δ(3) = 1/2` |
| `LatticeDensity.isGreatest_upperDensity_stillLife` | the greatest density of a still Life of Conway's Game of Life is `1/2` |
| `LatticeDensity.isGreatest_upperDensity_four` | `δ(4) = 3/5` |
| `LatticeDensity.isGreatest_upperDensity_five` | `δ(5) = 9/13` |

Each one says that no set exceeds the value and that some set attains it. All use only the axioms `propext`, `Classical.choice` and
`Quot.sound`; there is no `native_decide`.

Registered in Palomar as [PALOMAR-2026-11-26-000025](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-26-000025)
(commit `1b031db3`, Lean and Mathlib 4.35.0).

## What was known

* Elkies ([arXiv:math/9905194](https://arxiv.org/abs/math/9905194)) introduced `δ(n)` and proved `δ(3) = 1/2`, which is the still-Life
  conjecture. Chu and Stuckey (*Artificial Intelligence* 184-185 (2012), Theorem 1) give a much shorter proof, which is the one used
  here for `n = 3`.
* Ionascu, Pritikin and Wright (*Amer. Math. Monthly* 115 (2008), [arXiv:math/0608140](https://arxiv.org/abs/math/0608140)) study the
  limit of the densities of `n`-dependent sets in finite kings graphs. They list the values for `n = 0, 1, 2, 3, 6, 7, 8`, prove
  `3/5 ≤ τ₄ ≤ 0.608956` and `9/13 ≤ τ₅ ≤ 0.693943`, and conjecture that the lower bounds are the values. The patterns that attain
  them were already known.
* Elkies reports that Marcus Moore announced `δ(5) = 9/13` in 1995 and that, to his knowledge, the result had not yet appeared.

We have not found a published proof of `δ(4) = 3/5` or of `δ(5) = 9/13`. Whether they are new is unknown to us: if you know of one,
please open an issue.

## The proof

For `n = 3` each live point sends tokens to its orthogonal neighbours, as in Chu and Stuckey. For `n = 4` and `n = 5` the upper bound is
a linear-programming form of the discharging method, as in Stolee's
*Automated Discharging Arguments for Density Problems in Grids* ([arXiv:1409.5922](https://arxiv.org/abs/1409.5922)).
In every window of four rows of five cells (`n = 4`) or three rows of five cells (`n = 5`), the number of points, plus `f` of the left
part minus `f` of the right part, plus `g` of the upper part minus `g` of the lower part, is at most 12 (`n = 4`) or 135/13 (`n = 5`),
where `f` and `g` are two fixed functions. Summing over all the windows in a large box, the terms with `f` and `g` telescope.

The functions were found by a linear program outside Lean. Lean does not rely on it: the table of the functions is in the source, and
the kernel checks the inequality in every window (535 494 windows for `n = 4` and 27 631 for `n = 5`), with `decide +kernel`.

The lower bounds come from the points with `2x + y ∈ {0, 1, 2}` modulo 5 and those with `5x + y ∈ {0, 1, 2, 3, 4, 5, 6, 8, 11}`
modulo 13.

## Definitions

As in Elkies's paper, the upper density of `S` is the limit superior of the proportion of the box `|x|, |y| < r` that lies in `S`.
`N S x` is the number of points of `S`, other than `x`, among the eight around `x`.

## Files

| Path | What |
|---|---|
| `Challenge.lean` | the four statements, with the definitions they use |
| `Solution.lean` | the same statements, proved |
| `LatticeDensity/Defs.lean` | definitions |
| `LatticeDensity/Three.lean` | `n = 3` and still Lifes; in an `m × n` rectangle, `2 |S| ≤ m n + m + n` |
| `LatticeDensity/Local.lean` | from an inequality in windows to a density |
| `LatticeDensity/Periodic.lean` | the density of a periodic set |
| `LatticeDensity/Check4.lean`, `LatticeDensity/Check5.lean` | the finite checks and the tables |
| `LatticeDensity/Four.lean`, `LatticeDensity/Five.lean` | `n = 4` and `n = 5` |

## Build

```sh
lake exe cache get
lake build
```

The check for `n = 4` takes a few minutes.

## Credits and license

The Lean code was written with Claude Code (Claude Opus 5.5), which also found the functions; `formalization.yaml` gives the details.
License: Apache 2.0.

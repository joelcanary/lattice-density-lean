/-
Copyright 2026 Joel Cruz Cabrera.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib

/-!
# The greatest density of a set in the square lattice whose points have few neighbours

A point of `ℤ²` has eight neighbours. Let `δ(n)` be the greatest density of a set `S` such that every point of `S` has
at most `n` neighbours in `S`. Elkies [E] studied it because a still Life, a fixed set of Conway's Game of Life, has
`n = 3`; he proved that `δ(3) = 1/2`, and with it the still-Life conjecture: no still Life has density greater than
`1/2`. A shorter proof is in Chu and Stuckey [CS].

Ionascu, Pritikin and Wright [IPW] study the limit of the densities of `n`-dependent sets in finite kings graphs. They
list the values for `n = 0, 1, 2, 3, 6, 7, 8`, and for the other two they prove that the limits are between `3/5` and
`0.608956` and between `9/13` and `0.693943`, and conjecture that the lower bounds are the values. Elkies reports that
M. Moore announced `δ(5) = 9/13` in 1995 and that, to his knowledge, the result had not yet appeared.

Here the two values are proved, with those of `n = 3` and of still Lifes. The upper density is the one of [E], with the
boxes `|x₁|, |x₂| < r`. We have not found a published proof of `δ(4) = 3/5` or of `δ(5) = 9/13`; whether they are new
is unknown to us.

## References

* [E] N. D. Elkies, *The still-Life density problem and its generalizations*, arXiv:math/9905194.
* [IPW] E. J. Ionascu, D. Pritikin and S. E. Wright, *k-Dependence and domination in kings graphs*, Amer. Math.
  Monthly 115 (2008), 820-836, arXiv:math/0608140.
* [CS] G. Chu and P. J. Stuckey, *A complete solution to the Maximum Density Still Life Problem*, Artificial
  Intelligence 184-185 (2012), 1-16.
-/

@[expose] public section

open Filter

namespace LatticeDensity

/-- The square lattice. -/
abbrev Cell := ℤ × ℤ

/-- The number of neighbours of `x` in `S`: the points of `S`, other than `x`, among the eight around `x`. -/
noncomputable def N (S : Set Cell) (x : Cell) : ℕ :=
  {y : Cell | y ∈ S ∧ y ≠ x ∧ |y.1 - x.1| ≤ 1 ∧ |y.2 - x.2| ≤ 1}.ncard

/-- The box of the lattice points with both coordinates less than `r` in absolute value. -/
def box (r : ℕ) : Set Cell := {x | |x.1| < r ∧ |x.2| < r}

/-- The proportion of the box that lies in `S`. -/
noncomputable def ratio (S : Set Cell) (r : ℕ) : ℝ := ((box r ∩ S).ncard : ℝ) / ((box r).ncard : ℝ)

/-- The upper density of `S`. -/
noncomputable def upperDensity (S : Set Cell) : ℝ := limsup (ratio S) atTop

/-- One generation of Conway's Game of Life. -/
def life (S : Set Cell) : Set Cell := {x | (x ∈ S ∧ 2 ≤ N S x ∧ N S x ≤ 3) ∨ (x ∉ S ∧ N S x = 3)}

/-- **`δ(3) = 1/2`** (Elkies): `1/2` is the greatest upper density of a set whose points have at most three
neighbours in it. -/
theorem isGreatest_upperDensity_three :
    IsGreatest {d : ℝ | ∃ S : Set Cell, (∀ x ∈ S, N S x ≤ 3) ∧ upperDensity S = d} (1 / 2) := by
  sorry

/-- **The still-Life conjecture** (proved by Elkies): `1/2` is the greatest upper density of a still Life. -/
theorem isGreatest_upperDensity_stillLife :
    IsGreatest {d : ℝ | ∃ S : Set Cell, life S = S ∧ upperDensity S = d} (1 / 2) := by
  sorry

/-- **`δ(4) = 3/5`**: `3/5` is the greatest upper density of a set whose points have at most four neighbours
in it. -/
theorem isGreatest_upperDensity_four :
    IsGreatest {d : ℝ | ∃ S : Set Cell, (∀ x ∈ S, N S x ≤ 4) ∧ upperDensity S = d} (3 / 5) := by
  sorry

/-- **`δ(5) = 9/13`**: `9/13` is the greatest upper density of a set whose points have at most five neighbours
in it. -/
theorem isGreatest_upperDensity_five :
    IsGreatest {d : ℝ | ∃ S : Set Cell, (∀ x ∈ S, N S x ≤ 5) ∧ upperDensity S = d} (9 / 13) := by
  sorry

end LatticeDensity

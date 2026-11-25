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
# Definitions

Neighbours, boxes and upper density are those of Section 1 of Elkies [E].
-/

@[expose] public section

open Filter Topology

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

end LatticeDensity

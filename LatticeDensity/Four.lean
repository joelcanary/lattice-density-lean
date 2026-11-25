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

public import LatticeDensity.Local
public import LatticeDensity.Periodic
public import LatticeDensity.Check4

/-!
# At most four neighbours

The upper bound `3/5`, from the check in windows of four rows of five cells, and the set of the points with
`2 x₁ + x₂ ∈ {0, 1, 2}` modulo 5, which attains it.
-/

@[expose] public section

open Filter Topology

namespace LatticeDensity

theorem pc4_mk {a0 a1 a2 a3 a4 : ℕ} (h0 : a0 ≤ 1) (h1 : a1 ≤ 1) (h2 : a2 ≤ 1) (h3 : a3 ≤ 1)
    (h4 : a4 ≤ 1) :
    Check4.pc (mk a0 a1 a2 a3 a4) = a0 + a1 + a2 + a3 + a4 := by
  interval_cases a0 <;> interval_cases a1 <;> interval_cases a2 <;> interval_cases a3 <;> interval_cases a4 <;> rfl

/-! ### At most four neighbours -/

theorem spec4_mk {a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 : ℕ}
    (ha0 : a0 ≤ 1) (ha1 : a1 ≤ 1) (ha2 : a2 ≤ 1) (ha3 : a3 ≤ 1) (ha4 : a4 ≤ 1)
    (hb0 : b0 ≤ 1) (hb1 : b1 ≤ 1) (hb2 : b2 ≤ 1) (hb3 : b3 ≤ 1) (hb4 : b4 ≤ 1)
    (hc0 : c0 ≤ 1) (hc1 : c1 ≤ 1) (hc2 : c2 ≤ 1) (hc3 : c3 ≤ 1) (hc4 : c4 ≤ 1)
    (h0 : b0 = 0 ∨ a0 + a1 + b1 + c0 + c1 ≤ 4) (h1 : b1 = 0 ∨ a0 + a1 + a2 + b0 + b2 + c0 + c1 + c2 ≤ 4)
    (h2 : b2 = 0 ∨ a1 + a2 + a3 + b1 + b3 + c1 + c2 + c3 ≤ 4)
    (h3 : b3 = 0 ∨ a2 + a3 + a4 + b2 + b4 + c2 + c3 + c4 ≤ 4) (h4 : b4 = 0 ∨ a3 + a4 + b3 + c3 + c4 ≤ 4) :
    Check4.spec (mk a0 a1 a2 a3 a4) (mk b0 b1 b2 b3 b4) (mk c0 c1 c2 c3 c4) = true := by
  simp only [Check4.spec, Check4.cnt, mk_b0 ha0 ha1 ha2 ha3 ha4, mk_b1 ha0 ha1 ha2 ha3 ha4, mk_b2 ha0 ha1 ha2 ha3 ha4,
    mk_b3 ha0 ha1 ha2 ha3 ha4, mk_b4 ha0 ha1 ha2 ha3 ha4, mk_b0 hb0 hb1 hb2 hb3 hb4, mk_b1 hb0 hb1 hb2 hb3 hb4,
    mk_b2 hb0 hb1 hb2 hb3 hb4, mk_b3 hb0 hb1 hb2 hb3 hb4, mk_b4 hb0 hb1 hb2 hb3 hb4, mk_b0 hc0 hc1 hc2 hc3 hc4,
    mk_b1 hc0 hc1 hc2 hc3 hc4, mk_b2 hc0 hc1 hc2 hc3 hc4, mk_b3 hc0 hc1 hc2 hc3 hc4, mk_b4 hc0 hc1 hc2 hc3 hc4,
    Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Nat.ble_eq]
  exact ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩

theorem ok4 {S : Set Cell} (h : ∀ x ∈ S, N S x ≤ 4) (i j : ℤ) :
    Check4.ok (row5 S (i - 1) j) (row5 S i j) (row5 S (i + 1) j) = true ∧
    Check4.ok 0 (row5 S i j) (row5 S (i + 1) j) = true ∧ Check4.ok (row5 S (i - 1) j) (row5 S i j) 0 = true := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := five_cells h i j
  refine ⟨Check4.ok_of_spec (row5_lt ..) (row5_lt ..) (row5_lt ..) ?_,
    Check4.ok_of_spec (by norm_num) (row5_lt ..) (row5_lt ..) ?_,
    Check4.ok_of_spec (row5_lt ..) (row5_lt ..) (by norm_num) ?_⟩
  · exact spec4_mk (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..)
      (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..)
      h0 h1 h2 h3 h4
  · rw [← mk_zero]
    exact spec4_mk zero_le_one zero_le_one zero_le_one zero_le_one zero_le_one (t_le_one ..) (t_le_one ..)
      (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [← mk_zero]
    exact spec4_mk (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..)
      (t_le_one ..) (t_le_one ..) (t_le_one ..) zero_le_one zero_le_one zero_le_one zero_le_one zero_le_one
      (by omega) (by omega) (by omega) (by omega) (by omega)

/-- If every point of `S` has at most four neighbours in `S`, then `S` has upper density at most `3/5`. -/
theorem upperDensity_le_four (S : Set Cell) (h : ∀ x ∈ S, N S x ≤ 4) : upperDensity S ≤ 3 / 5 := by
  have key := upperDensity_le_of_local S 4 5 52 624 512 (by norm_num)
    (fun i j => (Check4.fv (row4 S i j + 16 * row4 S (i + 1) j + 256 * row4 S (i + 2) j + 4096 * row4 S (i + 3) j) : ℤ))
    (fun i j => (Check4.gv (row5 S i j + 32 * row5 S (i + 1) j + 1024 * row5 S (i + 2) j) : ℤ))
    (fun i j => ⟨by positivity, by unfold Check4.fv; omega⟩) (fun i j => ⟨by positivity, by unfold Check4.gv; omega⟩) ?_
  · refine key.trans (le_of_eq ?_); norm_num
  · intro i j
    have o1 := (ok4 h i j).2.1
    have o2 := (ok4 h (i + 1) j).1
    have o3 := (ok4 h (i + 2) j).1
    have o4 := (ok4 h (i + 3) j).2.2
    rw [show i + 1 - 1 = i by ring, show i + 1 + 1 = i + 2 by ring] at o2
    rw [show i + 2 - 1 = i + 1 by ring, show i + 2 + 1 = i + 3 by ring] at o3
    rw [show i + 3 - 1 = i + 2 by ring] at o4
    have g := Check4.good_of_ok (row5_lt ..) (row5_lt ..) (row5_lt ..) (row5_lt ..) o1 o2 o3 o4
    simp only [Check4.good, Nat.ble_eq, row5_mod, row5_div] at g
    have p : ∀ k, Check4.pc (row5 S k j) = t S k j + t S k (j + 1) + t S k (j + 2) + t S k (j + 3) + t S k (j + 4) :=
      fun k => pc4_mk (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..)
    rw [p, p, p, p] at g
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero,
      zero_add]
    rw [show i + 1 + 1 = i + 2 by ring, show i + 1 + 2 = i + 3 by ring]
    zify at g
    linarith

/-- **`δ(4) = 3/5`**: `3/5` is the greatest upper density of a set whose points have at most four neighbours
in it. -/
theorem isGreatest_upperDensity_four :
    IsGreatest {d : ℝ | ∃ S : Set Cell, (∀ x ∈ S, N S x ≤ 4) ∧ upperDensity S = d} (3 / 5) := by
  have := isGreatest_of_periodic 4 5 3 (by norm_num) 2 {0, 1, 2} (by decide)
    (N_periodic_le 4 5 2 {0, 1, 2} (by decide)) (fun S h => by simpa using upperDensity_le_four S h)
  simpa using this

end LatticeDensity

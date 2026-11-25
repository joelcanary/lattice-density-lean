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

public import LatticeDensity.Three

/-!
# From a local inequality to a density

`upperDensity_le_of_local`: if the number of points of `S` in every window of `a` rows of `b` cells, corrected with two
potentials whose sums telescope, is at most a constant, then the density is bounded. Finding the potentials is a linear
program; this is the linear form of the discharging method.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Filter Topology

namespace LatticeDensity

/-! ### From a local inequality to a density -/

theorem upperDensity_le_of_ncard_le (S : Set Cell) (α K : ℝ)
    (h : ∀ r : ℕ, 1 ≤ r → ((box r ∩ S).ncard : ℝ) ≤
      α * ((2 * (r : ℝ) - 1) * (2 * (r : ℝ) - 1)) + K * (2 * (r : ℝ) - 1)) : upperDensity S ≤ α := by
  have hb : IsBoundedUnder (· ≥ ·) atTop (ratio S) := isBoundedUnder_of ⟨0, ratio_nonneg S⟩
  have hlim : Tendsto (fun r : ℕ => α + K * (2 * (r : ℝ) - 1)⁻¹) atTop (𝓝 α) := by
    simpa using (tendsto_const_nhds (x := α)).add (tendsto_side.inv_tendsto_atTop.const_mul K)
  have hle : ∀ r : ℕ, 1 ≤ r → ratio S r ≤ α + K * (2 * (r : ℝ) - 1)⁻¹ := by
    intro r hr
    have hpos := side_pos r hr
    unfold ratio
    rw [ncard_box r hr, Nat.cast_mul, cast_side r hr, div_le_iff₀ (by positivity)]
    refine (h r hr).trans (le_of_eq ?_)
    have := hpos.ne'
    field_simp
  calc upperDensity S ≤ limsup (fun r : ℕ => α + K * (2 * (r : ℝ) - 1)⁻¹) atTop :=
        limsup_le_limsup (eventually_atTop.mpr ⟨1, hle⟩) hb.isCoboundedUnder_le hlim.isBoundedUnder_le
    _ = α := hlim.limsup_eq

theorem t_le_one (S : Set Cell) (i j : ℤ) : t S i j ≤ 1 := by unfold t; split <;> omega

theorem sum_shift_ge (g : ℕ → ℤ) (C : ℤ) (n r : ℕ) (h0 : ∀ i, 0 ≤ g i) (hC : ∀ i, g i ≤ C) :
    ∑ i ∈ Finset.range n, g i - r * C ≤ ∑ i ∈ Finset.range n, g (i + r) := by
  have h1 : ∑ i ∈ Finset.range n, g i ≤ ∑ i ∈ Finset.range (r + n), g i :=
    Finset.sum_le_sum_of_subset_of_nonneg (by intro x; simp only [Finset.mem_range]; omega) fun i _ _ => h0 i
  have h2 : ∑ i ∈ Finset.range (r + n), g i = ∑ i ∈ Finset.range r, g i + ∑ i ∈ Finset.range n, g (r + i) :=
    Finset.sum_range_add g r n
  have h3 : ∑ i ∈ Finset.range r, g i ≤ r * C := by
    calc _ ≤ ∑ i ∈ Finset.range r, C := Finset.sum_le_sum fun i _ => hC i
      _ = r * C := by simp
  have h4 : ∑ i ∈ Finset.range n, g (i + r) = ∑ i ∈ Finset.range n, g (r + i) :=
    Finset.sum_congr rfl fun i _ => by rw [add_comm]
  linarith

theorem sum_sum_shift_ge (S : Set Cell) (a b : ℤ) (n r c : ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (t S (a + i) (b + j) : ℤ) - (r + c) * n ≤
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (t S (a + i + r) (b + j + c) : ℤ) := by
  have h0 : ∀ i j, (0 : ℤ) ≤ t S i j := fun i j => by positivity
  have h1 : ∀ i j, (t S i j : ℤ) ≤ 1 := fun i j => by exact_mod_cast t_le_one S i j
  have hr := sum_shift_ge (fun i => ∑ j ∈ Finset.range n, (t S (a + i) (b + j) : ℤ)) n n r
    (fun i => Finset.sum_nonneg fun j _ => h0 _ _) (fun i => by
      calc _ ≤ ∑ j ∈ Finset.range n, (1 : ℤ) := Finset.sum_le_sum fun j _ => h1 _ _
        _ = n := by simp)
  have hc : ∀ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (t S (a + (i + r : ℕ)) (b + j) : ℤ) - c ≤
      ∑ j ∈ Finset.range n, (t S (a + i + r) (b + j + c) : ℤ) := by
    intro i _
    have := sum_shift_ge (fun j => (t S (a + (i + r : ℕ)) (b + j) : ℤ)) 1 n c (fun j => h0 _ _) (fun j => h1 _ _)
    rw [mul_one] at this
    refine this.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    push_cast; rw [add_assoc a, add_assoc b]
  have hs := Finset.sum_le_sum hc
  rw [Finset.sum_sub_distrib] at hs
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have : ((r : ℤ) + c) * n = r * n + n * c := by ring
  linarith

/-- A local inequality in windows of `a` rows of `b` cells, with potentials `F` and `G`, bounds the density. -/
theorem upperDensity_le_of_local (S : Set Cell) (a b D M C : ℕ) (hD : 0 < D * (a * b)) (F G : ℤ → ℤ → ℤ)
    (hF : ∀ i j, 0 ≤ F i j ∧ F i j ≤ C) (hG : ∀ i j, 0 ≤ G i j ∧ G i j ≤ C)
    (h : ∀ i j, (D : ℤ) * (∑ r ∈ Finset.range a, ∑ c ∈ Finset.range b, (t S (i + r) (j + c) : ℤ)) + F i j + G i j ≤
      M + F i (j + 1) + G (i + 1) j) :
    upperDensity S ≤ (M : ℝ) / (D * (a * b) : ℕ) := by
  have hint : ∀ (x y : ℤ) (n : ℕ), (D * (a * b) : ℤ) * (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (t S (x + i) (y + j) : ℤ)) ≤
      M * (n * n) + (D * (a * b * (a + b)) + 2 * C) * n := by
    intro x y n
    set L := ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (t S (x + i) (y + j) : ℤ) with hL
    have h1 : (a * b : ℤ) * L - a * b * (a + b) * n ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        ∑ r ∈ Finset.range a, ∑ c ∈ Finset.range b, (t S (x + i + r) (y + j + c) : ℤ) := by
      have e : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∑ r ∈ Finset.range a, ∑ c ∈ Finset.range b,
          (t S (x + i + r) (y + j + c) : ℤ) = ∑ r ∈ Finset.range a, ∑ c ∈ Finset.range b, ∑ i ∈ Finset.range n,
          ∑ j ∈ Finset.range n, (t S (x + i + r) (y + j + c) : ℤ) := by
        rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
      rw [e]
      calc (a * b : ℤ) * L - a * b * (a + b) * n = ∑ r ∈ Finset.range a, ∑ c ∈ Finset.range b, (L - (a + b) * n) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
        _ ≤ _ := by
            refine Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun c hc => ?_
            refine le_trans ?_ (sum_sum_shift_ge S x y n r c)
            rw [← hL]
            have hr' : (r : ℤ) ≤ a := by exact_mod_cast (Finset.mem_range.mp hr).le
            have hc' : (c : ℤ) ≤ b := by exact_mod_cast (Finset.mem_range.mp hc).le
            have : ((r : ℤ) + c) * n ≤ (a + b) * n := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            linarith
    have h2 : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ((D : ℤ) * (∑ r ∈ Finset.range a, ∑ c ∈ Finset.range b,
        (t S (x + i + r) (y + j + c) : ℤ))) ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        ((M : ℤ) + (F (x + i) (y + j + 1) - F (x + i) (y + j)) + (G (x + i + 1) (y + j) - G (x + i) (y + j))) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by have := h (x + i) (y + j); linarith
    have tele : ∀ (f : ℤ → ℤ) (z : ℤ), (∀ k, 0 ≤ f k ∧ f k ≤ C) →
        ∑ k ∈ Finset.range n, (f (z + k + 1) - f (z + k)) ≤ C := by
      intro f z hf
      have := Finset.sum_range_sub (fun k : ℕ => f (z + k)) n
      have e : ∑ k ∈ Finset.range n, (f (z + k + 1) - f (z + k)) =
          ∑ k ∈ Finset.range n, (f (z + (k + 1 : ℕ)) - f (z + k)) :=
        Finset.sum_congr rfl fun k _ => by push_cast; rw [add_assoc z]
      rw [e, this]
      have h3 := (hf (z + n)).2
      have h4 := (hf (z + (0 : ℕ))).1
      linarith
    have h3 : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (F (x + i) (y + j + 1) - F (x + i) (y + j)) ≤ n * C := by
      calc _ ≤ ∑ i ∈ Finset.range n, (C : ℤ) := Finset.sum_le_sum fun i _ => tele (fun k => F (x + i) k) y fun k => hF _ _
        _ = n * C := by simp
    have h4 : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (G (x + i + 1) (y + j) - G (x + i) (y + j)) ≤ n * C := by
      rw [Finset.sum_comm]
      calc _ ≤ ∑ j ∈ Finset.range n, (C : ℤ) := Finset.sum_le_sum fun j _ => tele (fun k => G k (y + j)) x fun k => hG _ _
        _ = n * C := by simp
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    have h5 := mul_le_mul_of_nonneg_left h1 (show (0 : ℤ) ≤ D by positivity)
    nlinarith [h2, h3, h4, h5]
  refine upperDensity_le_of_ncard_le S _ ((D * (a * b * (a + b)) + 2 * C : ℕ) / (D * (a * b) : ℕ)) fun r hr => ?_
  have hn := hint (-(r : ℤ) + 1) (-(r : ℤ) + 1) (2 * r - 1)
  have hc := ncard_rect S (-(r : ℤ) + 1) (-(r : ℤ) + 1) (2 * r - 1) (2 * r - 1)
  rw [← box_eq r hr] at hc
  have hn' : D * (a * b) * (box r ∩ S).ncard ≤
      M * ((2 * r - 1) * (2 * r - 1)) + (D * (a * b * (a + b)) + 2 * C) * (2 * r - 1) := by
    rw [hc]; exact_mod_cast hn
  have hpos : (0 : ℝ) < (D * (a * b) : ℕ) := by exact_mod_cast hD
  have hr' : ((D * (a * b) : ℕ) : ℝ) * ((box r ∩ S).ncard : ℝ) ≤ M * (((2 * r - 1 : ℕ) : ℝ) * ((2 * r - 1 : ℕ) : ℝ)) +
      (D * (a * b * (a + b)) + 2 * C : ℕ) * ((2 * r - 1 : ℕ) : ℝ) := by exact_mod_cast hn'
  rw [cast_side r hr] at hr'
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, le_div_iff₀ hpos]
  linarith

/-! ### Rows of five cells as numbers -/

/-- Five cells as a number. -/
def mk (a0 a1 a2 a3 a4 : ℕ) : ℕ := a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4

/-- Four cells as a number. -/
def mk4 (a0 a1 a2 a3 : ℕ) : ℕ := a0 + 2 * a1 + 4 * a2 + 8 * a3

theorem mk_zero : mk 0 0 0 0 0 = 0 := rfl

section
variable {a0 a1 a2 a3 a4 : ℕ} (h0 : a0 ≤ 1) (h1 : a1 ≤ 1) (h2 : a2 ≤ 1) (h3 : a3 ≤ 1) (h4 : a4 ≤ 1)
include h0 h1 h2 h3 h4

theorem mk_lt : mk a0 a1 a2 a3 a4 < 32 := by unfold mk; omega
theorem mk_mod : mk a0 a1 a2 a3 a4 % 16 = mk4 a0 a1 a2 a3 := by unfold mk mk4; omega
theorem mk_div : mk a0 a1 a2 a3 a4 / 2 = mk4 a1 a2 a3 a4 := by unfold mk mk4; omega
theorem mk_b0 : mk a0 a1 a2 a3 a4 % 2 = a0 := by unfold mk; omega
theorem mk_b1 : mk a0 a1 a2 a3 a4 / 2 % 2 = a1 := by unfold mk; omega
theorem mk_b2 : mk a0 a1 a2 a3 a4 / 4 % 2 = a2 := by unfold mk; omega
theorem mk_b3 : mk a0 a1 a2 a3 a4 / 8 % 2 = a3 := by unfold mk; omega
theorem mk_b4 : mk a0 a1 a2 a3 a4 / 16 % 2 = a4 := by unfold mk; omega

end

/-- The row of five cells of `S` that starts at `(i, j)`. -/
noncomputable def row5 (S : Set Cell) (i j : ℤ) : ℕ :=
  mk (t S i j) (t S i (j + 1)) (t S i (j + 2)) (t S i (j + 3)) (t S i (j + 4))

/-- The row of four cells of `S` that starts at `(i, j)`. -/
noncomputable def row4 (S : Set Cell) (i j : ℤ) : ℕ := mk4 (t S i j) (t S i (j + 1)) (t S i (j + 2)) (t S i (j + 3))

theorem row5_lt (S : Set Cell) (i j : ℤ) : row5 S i j < 32 :=
  mk_lt (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..)

theorem row5_mod (S : Set Cell) (i j : ℤ) : row5 S i j % 16 = row4 S i j :=
  mk_mod (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..) (t_le_one ..)

theorem row5_div (S : Set Cell) (i j : ℤ) : row5 S i j / 2 = row4 S i (j + 1) := by
  have := mk_div (t_le_one S i j) (t_le_one S i (j + 1)) (t_le_one S i (j + 2)) (t_le_one S i (j + 3))
    (t_le_one S i (j + 4))
  unfold row5 row4
  rw [this, add_assoc, add_assoc, add_assoc]; norm_num

theorem le_of_t {S : Set Cell} {K : ℕ} (h : ∀ x ∈ S, N S x ≤ K) {i j : ℤ} (ht : t S i j ≠ 0) : N S (i, j) ≤ K := by
  refine h _ ?_
  unfold t at ht
  by_contra hn
  simp [hn] at ht

/-- The condition at the five cells of a row, for a spec function given by its counts. -/
theorem five_cells {S : Set Cell} {K : ℕ} (h : ∀ x ∈ S, N S x ≤ K) (i j : ℤ) :
    (t S i j = 0 ∨ t S (i - 1) j + t S (i - 1) (j + 1) + t S i (j + 1) + t S (i + 1) j + t S (i + 1) (j + 1) ≤ K) ∧
    (t S i (j + 1) = 0 ∨ t S (i - 1) j + t S (i - 1) (j + 1) + t S (i - 1) (j + 2) + t S i j + t S i (j + 2) +
      t S (i + 1) j + t S (i + 1) (j + 1) + t S (i + 1) (j + 2) ≤ K) ∧
    (t S i (j + 2) = 0 ∨ t S (i - 1) (j + 1) + t S (i - 1) (j + 2) + t S (i - 1) (j + 3) + t S i (j + 1) +
      t S i (j + 3) + t S (i + 1) (j + 1) + t S (i + 1) (j + 2) + t S (i + 1) (j + 3) ≤ K) ∧
    (t S i (j + 3) = 0 ∨ t S (i - 1) (j + 2) + t S (i - 1) (j + 3) + t S (i - 1) (j + 4) + t S i (j + 2) +
      t S i (j + 4) + t S (i + 1) (j + 2) + t S (i + 1) (j + 3) + t S (i + 1) (j + 4) ≤ K) ∧
    (t S i (j + 4) = 0 ∨ t S (i - 1) (j + 3) + t S (i - 1) (j + 4) + t S i (j + 3) + t S (i + 1) (j + 3) +
      t S (i + 1) (j + 4) ≤ K) := by
  have e : ∀ k : ℤ, t S i k = 0 ∨ N S (i, k) ≤ K := fun k => by
    by_cases hk : t S i k = 0
    · exact Or.inl hk
    · exact Or.inr (le_of_t h hk)
  have h0 := e j
  have h1 := e (j + 1)
  have h2 := e (j + 2)
  have h3 := e (j + 3)
  have h4 := e (j + 4)
  rw [N_eq] at h0 h1 h2 h3 h4
  rw [show j + 1 - 1 = j by ring, show j + 1 + 1 = j + 2 by ring] at h1
  rw [show j + 2 - 1 = j + 1 by ring, show j + 2 + 1 = j + 3 by ring] at h2
  rw [show j + 3 - 1 = j + 2 by ring, show j + 3 + 1 = j + 4 by ring] at h3
  rw [show j + 4 - 1 = j + 3 by ring] at h4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases h0 with h | h
    · exact Or.inl h
    · right; omega
  · rcases h1 with h | h
    · exact Or.inl h
    · right; omega
  · rcases h2 with h | h
    · exact Or.inl h
    · right; omega
  · rcases h3 with h | h
    · exact Or.inl h
    · right; omega
  · rcases h4 with h | h
    · exact Or.inl h
    · right; omega

end LatticeDensity

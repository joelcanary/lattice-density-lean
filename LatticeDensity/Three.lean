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

public import LatticeDensity.Defs

/-!
# At most three neighbours

The argument is the one of Chu and Stuckey [CS, Theorem 1], written as a flow on the edges between orthogonal
neighbours. A live cell `u` gives one token to a dead neighbour `v`, unless the two neighbours of `v` across the
direction of the edge are both live; and if the two neighbours of `u` across the direction of the edge are live, then
`u` gives one token to a live neighbour `v`. If every live cell has at most three live neighbours, then a live cell
gives at least two tokens net and a dead cell receives at most two.
-/

@[expose] public section

open Filter Topology

namespace LatticeDensity

/-! ### Counting neighbours -/

/-- The eight offsets. -/
def offs : Finset Cell := {(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)}

open Classical in
/-- The indicator of `S`. -/
noncomputable def t (S : Set Cell) (i j : ℤ) : ℕ := if (i, j) ∈ S then 1 else 0

theorem mem_offs (p : Cell) : p ∈ offs ↔ p ≠ 0 ∧ |p.1| ≤ 1 ∧ |p.2| ≤ 1 := by
  obtain ⟨a, b⟩ := p
  simp only [offs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq, Prod.mk_eq_zero, abs_le]
  omega

theorem N_eq (S : Set Cell) (i j : ℤ) :
    N S (i, j) = t S (i - 1) (j - 1) + t S (i - 1) j + t S (i - 1) (j + 1) + t S i (j - 1) + t S i (j + 1) +
      t S (i + 1) (j - 1) + t S (i + 1) j + t S (i + 1) (j + 1) := by
  classical
  have hset : {y : Cell | y ∈ S ∧ y ≠ (i, j) ∧ |y.1 - i| ≤ 1 ∧ |y.2 - j| ≤ 1} =
      ((offs.filter fun p => ((i, j) : Cell) + p ∈ S).image fun p => ((i, j) : Cell) + p : Finset Cell) := by
    ext y
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter, mem_offs]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨y - (i, j), ⟨⟨sub_ne_zero.mpr h2, h3, h4⟩, ?_⟩, ?_⟩ <;> simp [h1]
    · rintro ⟨p, ⟨⟨h1, h2, h3⟩, h4⟩, rfl⟩
      exact ⟨h4, by simpa using h1, by simpa using h2, by simpa using h3⟩
  unfold N
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ (add_right_injective _), Finset.card_filter]
  simp [-Finset.sum_boole, offs, t, sub_eq_add_neg, add_assoc]

/-! ### The tokens -/

/-- The tokens that `u` gives to its neighbour `v`; `a`, `b` are the neighbours of `u` across the direction of the
edge, and `c`, `d` are those of `v`. -/
def give (u v a b c d : Bool) : ℤ := if u && ((!v && !(c && d)) || (v && (a && b))) then 1 else 0

/-- The net flow from `u` to `v`. -/
def flow (u v a b c d : Bool) : ℤ := give u v a b c d - give v u c d a b

theorem flow_le (u v a b c d : Bool) : flow u v a b c d ≤ 1 := by revert u v a b c d; decide

theorem neg_one_le_flow (u v a b c d : Bool) : -1 ≤ flow u v a b c d := by revert u v a b c d; decide

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2000 in
set_option maxRecDepth 100000 in
/-- The finite check: a live cell gives at least two tokens net, and a dead cell receives at most two. -/
theorem local_check : ∀ nw n ne w c e sw s se : Bool,
    (c = true → nw.toNat + n.toNat + ne.toNat + w.toNat + e.toNat + sw.toNat + s.toNat + se.toNat ≤ 3) →
    (n = true → nw.toNat + ne.toNat + w.toNat + c.toNat + e.toNat ≤ 3) →
    (s = true → w.toNat + c.toNat + e.toNat + sw.toNat + se.toNat ≤ 3) →
    (w = true → nw.toNat + n.toNat + c.toNat + sw.toNat + s.toNat ≤ 3) →
    (e = true → n.toNat + ne.toNat + c.toNat + s.toNat + se.toNat ≤ 3) →
    4 * (c.toNat : ℤ) - 2 ≤
      flow c e n s ne se - flow w c nw sw n s + (flow c s w e sw se - flow n c nw ne w e) := by
  decide

open Classical in
/-- `S` as a function to the Booleans. -/
noncomputable def bit (S : Set Cell) (i j : ℤ) : Bool := decide ((i, j) ∈ S)

theorem bit_toNat (S : Set Cell) (i j : ℤ) : (bit S i j).toNat = t S i j := by
  unfold bit t; split <;> simp_all

/-- The net flow from `(i, j)` to `(i, j + 1)`. -/
noncomputable def hf (S : Set Cell) (i j : ℤ) : ℤ :=
  flow (bit S i j) (bit S i (j + 1)) (bit S (i - 1) j) (bit S (i + 1) j) (bit S (i - 1) (j + 1))
    (bit S (i + 1) (j + 1))

/-- The net flow from `(i, j)` to `(i + 1, j)`. -/
noncomputable def vf (S : Set Cell) (i j : ℤ) : ℤ :=
  flow (bit S i j) (bit S (i + 1) j) (bit S i (j - 1)) (bit S i (j + 1)) (bit S (i + 1) (j - 1))
    (bit S (i + 1) (j + 1))

theorem le_three (S : Set Cell) (h : ∀ x ∈ S, N S x ≤ 3) (i j : ℤ) (hb : bit S i j = true) : N S (i, j) ≤ 3 :=
  h _ (by simpa [bit] using hb)

theorem net (S : Set Cell) (h : ∀ x ∈ S, N S x ≤ 3) (i j : ℤ) :
    4 * (t S i j : ℤ) - 2 ≤ hf S i j - hf S i (j - 1) + (vf S i j - vf S (i - 1) j) := by
  have key := local_check (bit S (i - 1) (j - 1)) (bit S (i - 1) j) (bit S (i - 1) (j + 1)) (bit S i (j - 1))
    (bit S i j) (bit S i (j + 1)) (bit S (i + 1) (j - 1)) (bit S (i + 1) j) (bit S (i + 1) (j + 1))
  simp only [bit_toNat] at key
  have h0 := le_three S h i j
  have h1 := le_three S h (i - 1) j
  have h2 := le_three S h (i + 1) j
  have h3 := le_three S h i (j - 1)
  have h4 := le_three S h i (j + 1)
  simp only [N_eq, sub_add_cancel, add_sub_cancel_right] at h0 h1 h2 h3 h4
  have := key (fun hb => by have := h0 hb; omega) (fun hb => by have := h1 hb; omega)
    (fun hb => by have := h2 hb; omega) (fun hb => by have := h3 hb; omega) (fun hb => by have := h4 hb; omega)
  simpa only [hf, vf, sub_add_cancel] using this

/-! ### Rectangles -/

theorem sum_Ico_int {M : Type*} [AddCommMonoid M] (f : ℤ → M) (a : ℤ) (m : ℕ) :
    ∑ i ∈ Finset.Ico a (a + m), f i = ∑ k ∈ Finset.range m, f (a + k) := by
  refine Finset.sum_nbij' (fun i => (i - a).toNat) (fun k => a + k) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [Finset.mem_Ico] at hi; simp only [Finset.mem_range]; omega
  · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Ico]; omega
  · intro i hi; simp only [Finset.mem_Ico] at hi; omega
  · intro k hk; simp
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    congr 1; omega

theorem ncard_rect (S : Set Cell) (a b : ℤ) (m n : ℕ) :
    ((Set.Ico a (a + m) ×ˢ Set.Ico b (b + n)) ∩ S).ncard =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, t S (a + i) (b + j) := by
  classical
  have : (Set.Ico a (a + m) ×ˢ Set.Ico b (b + n)) ∩ S =
      ((Finset.Ico a (a + m) ×ˢ Finset.Ico b (b + n)).filter (· ∈ S) : Finset Cell) := by
    ext x; simp
  rw [this, Set.ncard_coe_finset, Finset.card_filter, Finset.sum_product, sum_Ico_int]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_Ico_int]
  rfl

theorem telescope (f : ℤ → ℤ) (b : ℤ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (f (b + j) - f (b + j - 1)) = f (b + n - 1) - f (b - 1) := by
  have := Finset.sum_range_sub (fun k : ℕ => f (b + k - 1)) n
  simp only [Nat.cast_zero, add_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2; push_cast; ring

theorem hf_telescope_le (S : Set Cell) (i b : ℤ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (hf S i (b + j) - hf S i (b + j - 1)) ≤ 2 := by
  rw [telescope (fun k => hf S i k)]
  have h1 : hf S i (b + n - 1) ≤ 1 := flow_le _ _ _ _ _ _
  have h2 : -1 ≤ hf S i (b - 1) := neg_one_le_flow _ _ _ _ _ _
  linarith

theorem vf_telescope_le (S : Set Cell) (j a : ℤ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (vf S (a + i) j - vf S (a + i - 1) j) ≤ 2 := by
  rw [telescope (fun k => vf S k j)]
  have h1 : vf S (a + m - 1) j ≤ 1 := flow_le _ _ _ _ _ _
  have h2 : -1 ≤ vf S (a - 1) j := neg_one_le_flow _ _ _ _ _ _
  linarith

/-- **Explicit form.** If every point of `S` has at most three neighbours in `S`, then twice the number of points of
`S` in an `m × n` rectangle is at most `m n + m + n`. -/
theorem two_mul_ncard_rect_le (S : Set Cell) (h : ∀ x ∈ S, N S x ≤ 3) (a b : ℤ) (m n : ℕ) :
    2 * ((Set.Ico a (a + m) ×ˢ Set.Ico b (b + n)) ∩ S).ncard ≤ m * n + m + n := by
  rw [ncard_rect]
  have hsum : ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, (4 * (t S (a + i) (b + j) : ℤ) - 2) ≤
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n,
        ((hf S (a + i) (b + j) - hf S (a + i) (b + j - 1)) + (vf S (a + i) (b + j) - vf S (a + i - 1) (b + j))) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => net S h _ _
  have hl : ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, (4 * (t S (a + i) (b + j) : ℤ) - 2) =
      4 * ((∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, t S (a + i) (b + j) : ℕ) : ℤ) - 2 * (m * n) := by
    push_cast
    simp only [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have h1 : ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, (hf S (a + i) (b + j) - hf S (a + i) (b + j - 1)) ≤ m * 2 := by
    calc _ ≤ ∑ i ∈ Finset.range m, (2 : ℤ) := Finset.sum_le_sum fun i _ => hf_telescope_le S _ _ _
      _ = m * 2 := by simp
  have h2 : ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, (vf S (a + i) (b + j) - vf S (a + i - 1) (b + j)) ≤ n * 2 := by
    rw [Finset.sum_comm]
    calc _ ≤ ∑ j ∈ Finset.range n, (2 : ℤ) := Finset.sum_le_sum fun j _ => vf_telescope_le S _ _ _
      _ = n * 2 := by simp
  simp only [Finset.sum_add_distrib] at hsum
  rw [hl] at hsum
  zify
  push_cast at hsum ⊢
  linarith

/-! ### Density -/

theorem box_eq (r : ℕ) (hr : 1 ≤ r) :
    box r = Set.Ico (-(r : ℤ) + 1) (-(r : ℤ) + 1 + (2 * r - 1 : ℕ)) ×ˢ
      Set.Ico (-(r : ℤ) + 1) (-(r : ℤ) + 1 + (2 * r - 1 : ℕ)) := by
  ext x
  simp only [box, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Ico, abs_lt]
  omega

theorem ncard_box (r : ℕ) (hr : 1 ≤ r) : (box r).ncard = (2 * r - 1) * (2 * r - 1) := by
  have := ncard_rect Set.univ (-(r : ℤ) + 1) (-(r : ℤ) + 1) (2 * r - 1) (2 * r - 1)
  rw [← box_eq r hr, Set.inter_univ] at this
  rw [this]; simp [t]

theorem ratio_nonneg (S : Set Cell) (r : ℕ) : 0 ≤ ratio S r := by unfold ratio; positivity

theorem cast_side (r : ℕ) (hr : 1 ≤ r) : ((2 * r - 1 : ℕ) : ℝ) = 2 * (r : ℝ) - 1 := by
  rw [Nat.cast_sub (by omega)]; push_cast; ring

theorem side_pos (r : ℕ) (hr : 1 ≤ r) : (0 : ℝ) < 2 * (r : ℝ) - 1 := by
  rw [← cast_side r hr]; exact_mod_cast (by omega : 0 < 2 * r - 1)

theorem ratio_le (S : Set Cell) (h : ∀ x ∈ S, N S x ≤ 3) (r : ℕ) (hr : 1 ≤ r) :
    ratio S r ≤ 1 / 2 + 1 / (2 * (r : ℝ) - 1) := by
  have h1 := two_mul_ncard_rect_le S h (-(r : ℤ) + 1) (-(r : ℤ) + 1) (2 * r - 1) (2 * r - 1)
  rw [← box_eq r hr] at h1
  have hk := cast_side r hr
  have hpos := side_pos r hr
  have h2 : 2 * ((box r ∩ S).ncard : ℝ) ≤
      (2 * (r : ℝ) - 1) * (2 * (r : ℝ) - 1) + (2 * (r : ℝ) - 1) + (2 * (r : ℝ) - 1) := by
    rw [← hk]; exact_mod_cast h1
  unfold ratio
  rw [ncard_box r hr, Nat.cast_mul, hk, div_le_iff₀ (by positivity)]
  have : (1 / 2 + 1 / (2 * (r : ℝ) - 1)) * ((2 * (r : ℝ) - 1) * (2 * (r : ℝ) - 1)) =
      (2 * (r : ℝ) - 1) * (2 * (r : ℝ) - 1) / 2 + (2 * (r : ℝ) - 1) := by
    have := hpos.ne'
    field_simp
  rw [this]; linarith

theorem tendsto_side : Tendsto (fun r : ℕ => 2 * (r : ℝ) - 1) atTop atTop :=
  tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))

theorem tendsto_bound : Tendsto (fun r : ℕ => (1 : ℝ) / 2 + 1 / (2 * (r : ℝ) - 1)) atTop (𝓝 (1 / 2)) := by
  simpa using (tendsto_const_nhds (x := (1 : ℝ) / 2)).add tendsto_side.inv_tendsto_atTop

/-- **Elkies's theorem.** If every point of `S` has at most three neighbours in `S`, then `S` has upper density at
most `1/2`. -/
theorem upperDensity_le_three (S : Set Cell) (h : ∀ x ∈ S, N S x ≤ 3) : upperDensity S ≤ 1 / 2 := by
  have hb : IsBoundedUnder (· ≥ ·) atTop (ratio S) := isBoundedUnder_of ⟨0, ratio_nonneg S⟩
  calc upperDensity S ≤ limsup (fun r : ℕ => (1 : ℝ) / 2 + 1 / (2 * (r : ℝ) - 1)) atTop :=
        limsup_le_limsup (eventually_atTop.mpr ⟨1, fun r hr => ratio_le S h r hr⟩) hb.isCoboundedUnder_le
          tendsto_bound.isBoundedUnder_le
    _ = 1 / 2 := tendsto_bound.limsup_eq

/-- **The still-Life conjecture** (Elkies): a still Life has upper density at most `1/2`. -/
theorem upperDensity_le_of_life_eq (S : Set Cell) (h : life S = S) : upperDensity S ≤ 1 / 2 := by
  refine upperDensity_le_three S fun x hx => ?_
  have hx' : x ∈ life S := h.symm ▸ hx
  rcases hx' with ⟨_, _, h3⟩ | ⟨hn, _⟩
  · exact h3
  · exact absurd hx hn

/-! ### The bound is attained -/

/-- Alternate rows. -/
def rows : Set Cell := {x | 2 ∣ x.1}

theorem mem_rows (i j : ℤ) : (i, j) ∈ rows ↔ 2 ∣ i := Iff.rfl

theorem t_rows (i j : ℤ) : t rows i j = if 2 ∣ i then 1 else 0 := by unfold t rows; simp

theorem N_rows (i j : ℤ) : N rows (i, j) = if 2 ∣ i then 2 else 6 := by
  rw [N_eq]; simp only [t_rows]
  by_cases h : 2 ∣ i
  · have h1 : ¬ 2 ∣ i - 1 := by omega
    have h2 : ¬ 2 ∣ i + 1 := by omega
    simp [h, h1, h2]
  · have h1 : 2 ∣ i - 1 := by omega
    have h2 : 2 ∣ i + 1 := by omega
    simp [h, h1, h2]

theorem N_rows_le : ∀ x ∈ rows, N rows x ≤ 3 := by
  rintro ⟨i, j⟩ hx
  have : (2 : ℤ) ∣ i := hx
  simp [N_rows, this]

/-- Alternate rows are a still Life. -/
theorem life_rows : life rows = rows := by
  ext ⟨i, j⟩
  simp only [life, Set.mem_ofPred_eq, N_rows, mem_rows]
  by_cases h : 2 ∣ i <;> simp [h]

theorem sum_even (a : ℤ) (m : ℕ) :
    2 * ∑ k ∈ Finset.range m, (if (2 : ℤ) ∣ a + k then 1 else 0) + (if (2 : ℤ) ∣ a + m then 1 else 0) =
      m + (if (2 : ℤ) ∣ a then 1 else 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add]
    push_cast
    by_cases h : (2 : ℤ) ∣ a + m
    · have h' : ¬ (2 : ℤ) ∣ a + (m + 1) := by omega
      simp only [h, h', ite_true, ite_false] at ih ⊢
      omega
    · have h' : (2 : ℤ) ∣ a + (m + 1) := by omega
      simp only [h, h', ite_true, ite_false] at ih ⊢
      omega

theorem le_ratio_rows (r : ℕ) (hr : 1 ≤ r) : 1 / 2 - 1 / (2 * (r : ℝ) - 1) ≤ ratio rows r := by
  have h1 := ncard_rect rows (-(r : ℤ) + 1) (-(r : ℤ) + 1) (2 * r - 1) (2 * r - 1)
  rw [← box_eq r hr] at h1
  simp only [t_rows, Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum] at h1
  have h2 := sum_even (-(r : ℤ) + 1) (2 * r - 1)
  set s := ∑ k ∈ Finset.range (2 * r - 1), (if (2 : ℤ) ∣ -(r : ℤ) + 1 + k then 1 else 0) with hs
  have h3 : 2 * r - 1 ≤ 2 * s + 1 := by
    have : (if (2 : ℤ) ∣ -(r : ℤ) + 1 + (2 * r - 1 : ℕ) then 1 else 0) ≤ 1 := by split_ifs <;> omega
    omega
  have hk := cast_side r hr
  have hpos := side_pos r hr
  have h4 : 2 * (r : ℝ) - 1 ≤ 2 * (s : ℝ) + 1 := by rw [← hk]; exact_mod_cast h3
  unfold ratio
  rw [ncard_box r hr, h1, Nat.cast_mul, Nat.cast_mul, hk, le_div_iff₀ (by positivity)]
  have : (1 / 2 - 1 / (2 * (r : ℝ) - 1)) * ((2 * (r : ℝ) - 1) * (2 * (r : ℝ) - 1)) =
      (2 * (r : ℝ) - 1) * ((2 * (r : ℝ) - 1) / 2 - 1) := by
    have := hpos.ne'
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left (by linarith) hpos.le

/-- Alternate rows have density exactly `1/2`. -/
theorem tendsto_ratio_rows : Tendsto (ratio rows) atTop (𝓝 (1 / 2)) := by
  have hlow : Tendsto (fun r : ℕ => (1 : ℝ) / 2 - 1 / (2 * (r : ℝ) - 1)) atTop (𝓝 (1 / 2)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ) / 2)).sub tendsto_side.inv_tendsto_atTop
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_bound
    (eventually_atTop.mpr ⟨1, fun r hr => le_ratio_rows r hr⟩)
    (eventually_atTop.mpr ⟨1, fun r hr => ratio_le rows N_rows_le r hr⟩)

/-- **`δ(3) = 1/2`** (Elkies): `1/2` is the greatest upper density of a set whose points have at most three
neighbours in it. -/
theorem isGreatest_upperDensity_three :
    IsGreatest {d : ℝ | ∃ S : Set Cell, (∀ x ∈ S, N S x ≤ 3) ∧ upperDensity S = d} (1 / 2) := by
  refine ⟨⟨rows, N_rows_le, tendsto_ratio_rows.limsup_eq⟩, ?_⟩
  rintro d ⟨S, h, rfl⟩
  exact upperDensity_le_three S h

/-- **The still-Life conjecture** (proved by Elkies): `1/2` is the greatest upper density of a still Life. -/
theorem isGreatest_upperDensity_stillLife :
    IsGreatest {d : ℝ | ∃ S : Set Cell, life S = S ∧ upperDensity S = d} (1 / 2) := by
  refine ⟨⟨rows, life_rows, tendsto_ratio_rows.limsup_eq⟩, ?_⟩
  rintro d ⟨S, h, rfl⟩
  exact upperDensity_le_of_life_eq S h

end LatticeDensity

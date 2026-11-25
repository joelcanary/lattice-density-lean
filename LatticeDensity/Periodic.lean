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
# Periodic sets

The set of the points whose class `m x₁ + x₂` modulo `q` lies in a set `R`, and its density.
-/

@[expose] public section

open Filter Topology

namespace LatticeDensity

/-- A periodic set: the points whose class `m x₁ + x₂` modulo `q` lies in `R`. -/
def periodic (q : ℕ) (m : ZMod q) (R : Finset (ZMod q)) : Set Cell := {x | m * (x.1 : ZMod q) + (x.2 : ZMod q) ∈ R}

theorem t_periodic (q : ℕ) (m : ZMod q) (R : Finset (ZMod q)) (i j : ℤ) :
    t (periodic q m R) i j = if m * (i : ZMod q) + (j : ZMod q) ∈ R then 1 else 0 := by
  unfold t periodic; simp

theorem sum_period (q k : ℕ) (R : Finset (ZMod q))
    (hk : ∀ c : ZMod q, ∑ j ∈ Finset.range q, (if c + (j : ZMod q) ∈ R then 1 else 0) = k) (c : ZMod q) (s : ℕ) :
    ∑ j ∈ Finset.range (q * s), (if c + (j : ZMod q) ∈ R then 1 else 0) = k * s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have := hk c
    simp only [Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero, zero_mul, zero_add]
    rw [this, Nat.mul_succ]

theorem le_sum_period (q k : ℕ) (hq : 0 < q) (R : Finset (ZMod q))
    (hk : ∀ c : ZMod q, ∑ j ∈ Finset.range q, (if c + (j : ZMod q) ∈ R then 1 else 0) = k) (c : ZMod q) (n : ℕ) :
    k * n ≤ q * ∑ j ∈ Finset.range n, (if c + (j : ZMod q) ∈ R then 1 else 0) + k * q := by
  have h1 := sum_period q k R hk c (n / q)
  have h2 : ∑ j ∈ Finset.range (q * (n / q)), (if c + (j : ZMod q) ∈ R then 1 else 0) ≤
      ∑ j ∈ Finset.range n, (if c + (j : ZMod q) ∈ R then 1 else 0) :=
    Finset.sum_le_sum_of_subset (by
      intro x; simp only [Finset.mem_range]; have := Nat.mul_div_le n q; omega)
  rw [h1] at h2
  have h3 : n ≤ q * (n / q) + q := by have := Nat.div_add_mod n q; have := Nat.mod_lt n hq; omega
  calc k * n ≤ k * (q * (n / q) + q) := Nat.mul_le_mul_left _ h3
    _ = q * (k * (n / q)) + k * q := by ring
    _ ≤ _ := by have := Nat.mul_le_mul_left q h2; omega

/-- The density of a periodic set is at least `k / q` if `k` classes of every `q` consecutive ones are in it. -/
theorem le_ratio_periodic (q k : ℕ) (hq : 0 < q) (m : ZMod q) (R : Finset (ZMod q))
    (hk : ∀ c : ZMod q, ∑ j ∈ Finset.range q, (if c + (j : ZMod q) ∈ R then 1 else 0) = k) (r : ℕ) (hr : 1 ≤ r) :
    (k : ℝ) / q - k * (2 * (r : ℝ) - 1)⁻¹ ≤ ratio (periodic q m R) r := by
  have hc := ncard_rect (periodic q m R) (-(r : ℤ) + 1) (-(r : ℤ) + 1) (2 * r - 1) (2 * r - 1)
  rw [← box_eq r hr] at hc
  have hrow : ∀ i ∈ Finset.range (2 * r - 1), k * (2 * r - 1) ≤
      q * ∑ j ∈ Finset.range (2 * r - 1), t (periodic q m R) (-(r : ℤ) + 1 + i) (-(r : ℤ) + 1 + j) + k * q := by
    intro i _
    have := le_sum_period q k hq R hk (m * ((-(r : ℤ) + 1 + i : ℤ) : ZMod q) + ((-(r : ℤ) + 1 : ℤ) : ZMod q)) (2 * r - 1)
    refine this.trans (le_of_eq ?_)
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [t_periodic]
    push_cast
    simp only [add_assoc]
  have hsum := Finset.sum_le_sum hrow
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  rw [← Finset.mul_sum, ← hc] at hsum
  have hpos := side_pos r hr
  have hk' := cast_side r hr
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hR : (2 * (r : ℝ) - 1) * (k * (2 * (r : ℝ) - 1)) ≤
      q * ((box r ∩ periodic q m R).ncard : ℝ) + (2 * (r : ℝ) - 1) * (k * q) := by
    rw [← hk']; exact_mod_cast hsum
  unfold ratio
  rw [ncard_box r hr, Nat.cast_mul, hk', le_div_iff₀ (by positivity)]
  have e : ((k : ℝ) / q - k * (2 * (r : ℝ) - 1)⁻¹) * ((2 * (r : ℝ) - 1) * (2 * (r : ℝ) - 1)) =
      ((2 * (r : ℝ) - 1) * (k * (2 * (r : ℝ) - 1)) - (2 * (r : ℝ) - 1) * (k * q)) / q := by
    have := hpos.ne'
    field_simp
  rw [e, div_le_iff₀ hq']
  linarith

theorem isGreatest_of_periodic (K q k : ℕ) (hq : 0 < q) (m : ZMod q) (R : Finset (ZMod q))
    (hk : ∀ c : ZMod q, ∑ j ∈ Finset.range q, (if c + (j : ZMod q) ∈ R then 1 else 0) = k)
    (hdeg : ∀ x ∈ periodic q m R, N (periodic q m R) x ≤ K)
    (hup : ∀ S : Set Cell, (∀ x ∈ S, N S x ≤ K) → upperDensity S ≤ (k : ℝ) / q) :
    IsGreatest {d : ℝ | ∃ S : Set Cell, (∀ x ∈ S, N S x ≤ K) ∧ upperDensity S = d} ((k : ℝ) / q) := by
  refine ⟨⟨periodic q m R, hdeg, le_antisymm (hup _ hdeg) ?_⟩, ?_⟩
  · have hlim : Tendsto (fun r : ℕ => (k : ℝ) / q - k * (2 * (r : ℝ) - 1)⁻¹) atTop (𝓝 ((k : ℝ) / q)) := by
      simpa using (tendsto_const_nhds (x := (k : ℝ) / q)).sub (tendsto_side.inv_tendsto_atTop.const_mul (k : ℝ))
    have hb : IsBoundedUnder (· ≤ ·) atTop (ratio (periodic q m R)) := by
      refine isBoundedUnder_of ⟨1, fun r => ?_⟩
      unfold ratio
      refine div_le_one_of_le₀ ?_ (by positivity)
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0
        have : box 0 = ∅ := by ext x; simp [box]
        simp [this]
      · have hfin : (box r).Finite := by
          rw [box_eq r h0]; exact (Set.finite_Ico _ _).prod (Set.finite_Ico _ _)
        exact_mod_cast Set.ncard_le_ncard Set.inter_subset_left hfin
    rw [← hlim.limsup_eq]
    exact limsup_le_limsup (eventually_atTop.mpr ⟨1, fun r hr => le_ratio_periodic q k hq m R hk r hr⟩)
      hlim.isBoundedUnder_ge.isCoboundedUnder_le hb
  · rintro d ⟨S, h, rfl⟩
    exact hup S h

theorem N_periodic_le (K q : ℕ) (m : ZMod q) (R : Finset (ZMod q))
    (h : ∀ v ∈ R, (if v - m - 1 ∈ R then 1 else 0) + (if v - m ∈ R then 1 else 0) + (if v - m + 1 ∈ R then 1 else 0) +
      (if v - 1 ∈ R then 1 else 0) + (if v + 1 ∈ R then 1 else 0) + (if v + m - 1 ∈ R then 1 else 0) +
      (if v + m ∈ R then 1 else 0) + (if v + m + 1 ∈ R then 1 else 0) ≤ K) :
    ∀ x ∈ periodic q m R, N (periodic q m R) x ≤ K := by
  rintro ⟨i, j⟩ hx
  have hv : m * (i : ZMod q) + (j : ZMod q) ∈ R := hx
  have := h _ hv
  rw [N_eq]
  simp only [t_periodic]
  convert this using 1
  push_cast
  have e1 : m * ((i : ZMod q) - 1) + ((j : ZMod q) - 1) = m * i + j - m - 1 := by ring
  have e2 : m * ((i : ZMod q) - 1) + (j : ZMod q) = m * i + j - m := by ring
  have e3 : m * ((i : ZMod q) - 1) + ((j : ZMod q) + 1) = m * i + j - m + 1 := by ring
  have e4 : m * (i : ZMod q) + ((j : ZMod q) - 1) = m * i + j - 1 := by ring
  have e5 : m * (i : ZMod q) + ((j : ZMod q) + 1) = m * i + j + 1 := by ring
  have e6 : m * ((i : ZMod q) + 1) + ((j : ZMod q) - 1) = m * i + j + m - 1 := by ring
  have e7 : m * ((i : ZMod q) + 1) + (j : ZMod q) = m * i + j + m := by ring
  have e8 : m * ((i : ZMod q) + 1) + ((j : ZMod q) + 1) = m * i + j + m + 1 := by ring
  rw [e1, e2, e3, e4, e5, e6, e7, e8]

end LatticeDensity

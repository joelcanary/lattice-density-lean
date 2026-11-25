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

public import LatticeDensity.Check4.Rows0
public import LatticeDensity.Check4.Rows1
public import LatticeDensity.Check4.Rows2
public import LatticeDensity.Check4.Rows3

/-!
# The finite check for at most four neighbours, put together
-/

@[expose] public section

namespace LatticeDensity.Check4

theorem rows (x : Nat) (hx : x < 32) : row x = true := by
  match x, hx with
  | 0, _ => exact row_0
  | 1, _ => exact row_1
  | 2, _ => exact row_2
  | 3, _ => exact row_3
  | 4, _ => exact row_4
  | 5, _ => exact row_5
  | 6, _ => exact row_6
  | 7, _ => exact row_7
  | 8, _ => exact row_8
  | 9, _ => exact row_9
  | 10, _ => exact row_10
  | 11, _ => exact row_11
  | 12, _ => exact row_12
  | 13, _ => exact row_13
  | 14, _ => exact row_14
  | 15, _ => exact row_15
  | 16, _ => exact row_16
  | 17, _ => exact row_17
  | 18, _ => exact row_18
  | 19, _ => exact row_19
  | 20, _ => exact row_20
  | 21, _ => exact row_21
  | 22, _ => exact row_22
  | 23, _ => exact row_23
  | 24, _ => exact row_24
  | 25, _ => exact row_25
  | 26, _ => exact row_26
  | 27, _ => exact row_27
  | 28, _ => exact row_28
  | 29, _ => exact row_29
  | 30, _ => exact row_30
  | 31, _ => exact row_31
  | n + 32, h => exact absurd h (by omega)

theorem good_of_ok {x y z w : Nat} (hx : x < 32) (hy : y < 32) (hz : z < 32) (hw : w < 32) (h0 : ok 0 x y = true)
    (h1 : ok x y z = true) (h2 : ok y z w = true) (h3 : ok z w 0 = true) : good x y z w = true := by
  have h := all_spec (rows x hx) y hy
  simp only [h0, Bool.not_true, Bool.false_or] at h
  have h := all_spec h z hz
  simp only [h1, Bool.not_true, Bool.false_or] at h
  have h := all_spec h w hw
  simpa [h2, h3] using h

end LatticeDensity.Check4

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

/-!
# The rows 8 to 15 of the check for at most four neighbours
-/

@[expose] public section

namespace LatticeDensity.Check4

theorem row_8 : row 8 = true := by decide +kernel

theorem row_9 : row 9 = true := by decide +kernel

theorem row_10 : row 10 = true := by decide +kernel

theorem row_11 : row 11 = true := by decide +kernel

theorem row_12 : row 12 = true := by decide +kernel

theorem row_13 : row 13 = true := by decide +kernel

theorem row_14 : row 14 = true := by decide +kernel

theorem row_15 : row 15 = true := by decide +kernel

end LatticeDensity.Check4

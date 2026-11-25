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

public import LatticeDensity.Check4.Table

/-!
# The rows 16 to 23 of the check for at most four neighbours
-/

@[expose] public section

namespace LatticeDensity.Check4

theorem row_16 : row 16 = true := by decide +kernel

theorem row_17 : row 17 = true := by decide +kernel

theorem row_18 : row 18 = true := by decide +kernel

theorem row_19 : row 19 = true := by decide +kernel

theorem row_20 : row 20 = true := by decide +kernel

theorem row_21 : row 21 = true := by decide +kernel

theorem row_22 : row 22 = true := by decide +kernel

theorem row_23 : row 23 = true := by decide +kernel

end LatticeDensity.Check4

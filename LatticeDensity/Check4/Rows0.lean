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
# The rows 0 to 7 of the check for at most four neighbours
-/

@[expose] public section

namespace LatticeDensity.Check4

theorem row_0 : row 0 = true := by decide +kernel

theorem row_1 : row 1 = true := by decide +kernel

theorem row_2 : row 2 = true := by decide +kernel

theorem row_3 : row 3 = true := by decide +kernel

theorem row_4 : row 4 = true := by decide +kernel

theorem row_5 : row 5 = true := by decide +kernel

theorem row_6 : row 6 = true := by decide +kernel

theorem row_7 : row 7 = true := by decide +kernel

end LatticeDensity.Check4

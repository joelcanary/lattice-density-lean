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
# The rows 24 to 31 of the check for at most four neighbours
-/

@[expose] public section

namespace LatticeDensity.Check4

theorem row_24 : row 24 = true := by decide +kernel

theorem row_25 : row 25 = true := by decide +kernel

theorem row_26 : row 26 = true := by decide +kernel

theorem row_27 : row 27 = true := by decide +kernel

theorem row_28 : row 28 = true := by decide +kernel

theorem row_29 : row 29 = true := by decide +kernel

theorem row_30 : row 30 = true := by decide +kernel

theorem row_31 : row 31 = true := by decide +kernel

end LatticeDensity.Check4

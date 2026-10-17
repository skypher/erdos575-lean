import JustinSun.Erdos575.Asm.Item29
import JustinSun.Erdos575.Assembly

/-!
# Erdős 575: final assembly

`Stmt_erdos575` from the upper bound `ex(n, 𝓕) ≤ 32 n^{21/16}` (blueprint items 13–17, lane575U)
and the lower bound of item 29 for every member, with the family of items 1–3.
-/

namespace A575

open L575U L575G JustinSun.Erdos575

/-- The upper bound of blueprint item 17 for the forbidden family. -/
def Stmt_upper : Prop :=
  ∀ n : ℕ, 1 ≤ n → (exFamily n forbiddenFamily : ℝ) ≤ 32 * (n : ℝ) ^ ((21 : ℝ) / 16)

/-- **Erdős 575**, conditional on the upper bound. -/
theorem erdos575_of_upper (hU : Stmt_upper) : Stmt_erdos575 :=
  erdos575_of_bounds ⟨forbiddenFamily, forbiddenFamily_nonempty, forbiddenFamily_members_structural,
    32, cLow, 80, cLow_pos, hU, forbidden_lower⟩

end A575

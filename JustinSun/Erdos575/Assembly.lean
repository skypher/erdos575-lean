import JustinSun.Erdos575.Statement
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Erdős 575 from the two bounds of Theorem 1.1

`Stmt_erdos575` follows from a finite nonempty family of bipartite graphs with cycles whose
extremal number is `O(n^{21/16})` while each member has extremal number `Ω(n^{4/3})`
(source: `sources/oai_ch10_erdos575.txt`, Theorem 1.1, with `21/16 = 4/3 - 1/48`).
-/

open Filter Topology

namespace JustinSun.Erdos575

/-- The two bounds of Theorem 1.1, with explicit constants. -/
def Stmt_575_bounds : Prop :=
  ∃ F : Finset FinGraph, F.Nonempty ∧ (∀ A ∈ F, A.2.IsBipartite ∧ ¬ A.2.IsAcyclic) ∧
    ∃ C₀ c : ℝ, ∃ n₀ : ℕ, 0 < c ∧
      (∀ n : ℕ, 1 ≤ n → (exFamily n F : ℝ) ≤ C₀ * (n : ℝ) ^ ((21 : ℝ) / 16)) ∧
      ∀ A ∈ F, ∀ n : ℕ, n₀ ≤ n →
        c * (n : ℝ) ^ ((4 : ℝ) / 3) ≤ (SimpleGraph.extremalNumber n A.2 : ℝ)

/-- A function bounded below by `c n^{4/3}` is not eventually bounded by a multiple of a function
bounded above by `C₀ n^{21/16}`. -/
theorem not_eventually_le_of_bounds {X E : ℕ → ℝ} {C₀ c : ℝ} {n₀ : ℕ} (hc : 0 < c)
    (hE : ∀ n : ℕ, 1 ≤ n → E n ≤ C₀ * (n : ℝ) ^ ((21 : ℝ) / 16)) (hE0 : ∀ n, 0 ≤ E n)
    (hX : ∀ n : ℕ, n₀ ≤ n → c * (n : ℝ) ^ ((4 : ℝ) / 3) ≤ X n) :
    ¬ ∃ C : ℝ, ∀ᶠ n in atTop, X n ≤ C * E n := by
  rintro ⟨C, hC⟩
  set K := (max C 0 * max C₀ 0 + 1) / c with hK
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 48)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, K < (n : ℝ) ^ ((1 : ℝ) / 48) ∧ 1 ≤ n ∧ n₀ ≤ n ∧
      X n ≤ C * E n :=
    (hpow.eventually_gt_atTop K).and ((eventually_ge_atTop 1).and
      ((eventually_ge_atTop n₀).and hC))
  obtain ⟨n, hKn, hn1, hn0, hXn⟩ := hev.exists
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsplit : (n : ℝ) ^ ((4 : ℝ) / 3) = (n : ℝ) ^ ((21 : ℝ) / 16) * (n : ℝ) ^ ((1 : ℝ) / 48) := by
    rw [← Real.rpow_add hnpos]; norm_num
  have h21 : 0 < (n : ℝ) ^ ((21 : ℝ) / 16) := Real.rpow_pos_of_pos hnpos _
  have hlow := hX n hn0
  have hup := hE n hn1
  have hE0n := hE0 n
  -- C * E n ≤ max C 0 * (max C₀ 0 * n^{21/16})
  have hCE : C * E n ≤ max C 0 * max C₀ 0 * (n : ℝ) ^ ((21 : ℝ) / 16) := by
    have h1 : C * E n ≤ max C 0 * E n := mul_le_mul_of_nonneg_right (le_max_left _ _) hE0n
    have h2 : E n ≤ max C₀ 0 * (n : ℝ) ^ ((21 : ℝ) / 16) :=
      hup.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h21.le)
    calc C * E n ≤ max C 0 * E n := h1
      _ ≤ max C 0 * (max C₀ 0 * (n : ℝ) ^ ((21 : ℝ) / 16)) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = _ := by ring
  have hmain : c * (n : ℝ) ^ ((1 : ℝ) / 48) ≤ max C 0 * max C₀ 0 := by
    have := hlow.trans (hXn.trans hCE)
    rw [hsplit] at this
    have h' : (n : ℝ) ^ ((21 : ℝ) / 16) * (c * (n : ℝ) ^ ((1 : ℝ) / 48)) ≤
        (n : ℝ) ^ ((21 : ℝ) / 16) * (max C 0 * max C₀ 0) := by nlinarith
    exact le_of_mul_le_mul_left h' h21
  have hKc : c * K = max C 0 * max C₀ 0 + 1 := by rw [hK]; field_simp
  nlinarith [mul_lt_mul_of_pos_left hKn hc]

/-- **Erdős 575 from Theorem 1.1's bounds.** -/
theorem erdos575_of_bounds (h : Stmt_575_bounds) : Stmt_erdos575 := by
  obtain ⟨F, hFne, hF, C₀, c, n₀, hc, hup, hlow⟩ := h
  refine ⟨F, hFne, hF, fun A hA => ?_⟩
  exact not_eventually_le_of_bounds hc hup (fun n => by positivity) (hlow A hA)

end JustinSun.Erdos575

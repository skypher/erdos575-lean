import JustinSun.Erdos575.Asm.Item26
import JustinSun.Erdos575.Geometry.Padding
import JustinSun.Erdos575.Padding
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Erdős 575, blueprint item 29: every forbidden graph has extremal number `Ω(n^{4/3})`

For a member `A` of the forbidden family and `n ≥ 80`, choose `p = 2` (for `C₄`, `C₆` and the J
family) or `p = 3` (for the K family), the largest `q = p^j` with `n_q ≤ n`, and pad the incidence
graph of `W(q)` with isolated vertices.
-/

namespace A575

open L575U L575G

/-- Every vertex of `C₄`, `C₆`, or a quotient of the templates lies on an edge. -/
theorem cycle4_noIsolated : ∀ w : Fin 4, ∃ w', (SimpleGraph.cycleGraph 4).Adj w w' := by
  intro w; exact ⟨w + 1, by fin_cases w <;> decide⟩

theorem cycle6_noIsolated : ∀ w : Fin 6, ∃ w', (SimpleGraph.cycleGraph 6).Adj w w' := by
  intro w; exact ⟨w + 1, by fin_cases w <;> decide⟩

theorem j0_noIsolated : ∀ a : J0Vert, ∃ b, J0Graph.Adj a b := by
  intro a
  have cp : ∀ copy (u v : SVert 2), (SGraph 2).Adj u v → J0Graph.Adj (jCopy copy u) (jCopy copy v) :=
    fun copy u v h => (jCopyHom copy).map_adj h
  cases a with
  | x => exact ⟨.lam, by simp [J0Graph, J0Adj]⟩
  | xp => exact ⟨.lam, by simp [J0Graph, J0Adj]⟩
  | y => exact ⟨.s 0 1 0, cp 0 (.base 1) (.sub 1 0) (sAdj_base_sub 1 0)⟩
  | z => exact ⟨.s 0 2 0, cp 0 (.base 2) (.sub 2 0) (sAdj_base_sub 2 0)⟩
  | lam => exact ⟨.x, by simp [J0Graph, J0Adj]⟩
  | c copy j => exact ⟨.s copy 0 j, cp copy (.center j) (.sub 0 j) (sAdj_center_sub 0 j)⟩
  | s copy b j => exact ⟨.c copy j, cp copy (.sub b j) (.center j) (sAdj_center_sub b j).symm⟩

theorem k0_noIsolated : ∀ a : K0Vert, ∃ b, K0Graph.Adj a b := by
  rintro ⟨copy, w⟩
  have cp : ∀ (u v : SVert 3), (SGraph 3).Adj u v → K0Graph.Adj (kCopy copy u) (kCopy copy v) :=
    fun u v h => (kCopyHom copy).map_adj h
  cases w with
  | base i => exact ⟨kCopy copy (.sub i 0), cp _ _ (sAdj3_base_sub i 0)⟩
  | center j => exact ⟨kCopy copy (.sub 0 j), cp _ _ (sAdj3_center_sub 0 j)⟩
  | sub i j => exact ⟨kCopy copy (.center j), cp _ _ (sAdj3_center_sub i j).symm⟩

set_option maxRecDepth 8192 in
theorem jMember_noIsolated : ∀ A ∈ J, ∀ w, ∃ w', A.2.Adj w w' := by
  classical
  intro A hA w
  simp only [J, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hA
  obtain ⟨p, hp, rfl⟩ := hA
  obtain ⟨a, rfl⟩ := hp.1 w
  obtain ⟨b, hab⟩ := j0_noIsolated a
  refine ⟨p.2 b, fun h => jAdj_oppositeColors hab (hp.2.1 a b h), a, b, rfl, rfl, hab⟩

set_option maxRecDepth 8192 in
theorem kMember_noIsolated : ∀ A ∈ K, ∀ w, ∃ w', A.2.Adj w w' := by
  classical
  intro A hA w
  simp only [K, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hA
  obtain ⟨p, hp, rfl⟩ := hA
  obtain ⟨a, rfl⟩ := hp.1 w
  obtain ⟨b, hab⟩ := k0_noIsolated a
  refine ⟨p.2 b, fun h => kAdj_oppositeColors hab (hp.2.1 a b h), a, b, rfl, rfl, hab⟩

/-- The lower-bound constant `2^{-4/3} · 3^{-4}`. -/
noncomputable def cLow : ℝ := (2 : ℝ) ^ (-4 / 3 : ℝ) * (3 : ℝ) ^ (-4 : ℝ)

theorem cLow_pos : 0 < cLow := by unfold cLow; positivity

/-- One padding step: an `A`-free incidence graph with `n_q ≤ n < p³ n_q`, `p ≤ 3`. -/
theorem step_bound {F : Type} [Field F] [Fintype F] [DecidableEq F] {W : Type*}
    {A : SimpleGraph W} (hA : ∀ w, ∃ w', A.Adj w w') (hfree : A.Free (Iq F)) {n p : ℕ}
    (hp : p ≤ 3) (hn : n_q F ≤ n) (hlt : n < p ^ 3 * n_q F) :
    cLow * (n : ℝ) ^ (4 / 3 : ℝ) ≤ SimpleGraph.extremalNumber n A := by
  classical
  have h1 : (e_q F : ℝ) ≤ SimpleGraph.extremalNumber n A := by
    have := JustinSun.Erdos575.card_edgeFinset_le_extremalNumber_of_card_le (G := Iq F) hA hfree
      (by simpa [n_q] using hn)
    unfold e_q
    exact_mod_cast (by convert this)
  have h2 := e_q_density F
  have hp3 : p ^ 3 ≤ 27 := by
    have : p ^ 3 ≤ 3 ^ 3 := Nat.pow_le_pow_left hp 3
    simpa using this
  have hlt' : (n : ℝ) / 27 ≤ n_q F := by
    have : n ≤ 27 * n_q F := le_trans hlt.le (Nat.mul_le_mul_right _ hp3)
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 27)]
    exact_mod_cast (by linarith : n ≤ n_q F * 27)
  have h3 : ((n : ℝ) / 27) ^ (4 / 3 : ℝ) ≤ (n_q F : ℝ) ^ (4 / 3 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hlt' (by norm_num)
  have e27 : ((n : ℝ) / 27) ^ (4 / 3 : ℝ) = (n : ℝ) ^ (4 / 3 : ℝ) * (3 : ℝ) ^ (-4 : ℝ) := by
    rw [Real.div_rpow (by positivity) (by norm_num)]
    have : (27 : ℝ) ^ (4 / 3 : ℝ) = (3 : ℝ) ^ (4 : ℝ) := by
      rw [show (27 : ℝ) = (3 : ℝ) ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [this, Real.rpow_neg (by norm_num), div_eq_mul_inv]
  unfold cLow
  have h2' : (2 : ℝ) ^ (-4 / 3 : ℝ) * (n_q F : ℝ) ^ (4 / 3 : ℝ) ≤ e_q F := h2
  have hpos : 0 < (2 : ℝ) ^ (-4 / 3 : ℝ) := by positivity
  calc (2 : ℝ) ^ (-4 / 3 : ℝ) * (3 : ℝ) ^ (-4 : ℝ) * (n : ℝ) ^ (4 / 3 : ℝ)
      = (2 : ℝ) ^ (-4 / 3 : ℝ) * ((n : ℝ) / 27) ^ (4 / 3 : ℝ) := by rw [e27]; ring
    _ ≤ (2 : ℝ) ^ (-4 / 3 : ℝ) * (n_q F : ℝ) ^ (4 / 3 : ℝ) := mul_le_mul_of_nonneg_left h3 hpos.le
    _ ≤ e_q F := h2'
    _ ≤ _ := h1

/-- Bound for a graph avoided by the incidence graphs of all fields `GF(p^j)`, `p ∈ {2, 3}`. -/
theorem lower_of_free (p : ℕ) [Fact p.Prime] (hp2 : 2 ≤ p) (hp3 : p ≤ 3) {W : Type*}
    {A : SimpleGraph W} (hA : ∀ w, ∃ w', A.Adj w w')
    (hfree : ∀ j, 1 ≤ j → ∀ [Fintype (GaloisField p j)] [DecidableEq (GaloisField p j)],
      A.Free (Iq (GaloisField p j))) {n : ℕ} (hn : incidenceOrder p ≤ n) :
    cLow * (n : ℝ) ^ (4 / 3 : ℝ) ≤ SimpleGraph.extremalNumber n A := by
  classical
  obtain ⟨j, hj, hjn, hjlt⟩ := incidenceOrder_padding p n hp2 hn
  letI : Fintype (GaloisField p j) := Fintype.ofFinite _
  have hcard : q (GaloisField p j) = p ^ j := by
    unfold q
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card p j (by omega)
  have hnq : n_q (GaloisField p j) = incidenceOrder (p ^ j) := by
    rw [n_q_eq, hcard]; rfl
  exact step_bound hA (hfree j hj) hp3 (by rw [hnq]; exact hjn) (by rw [hnq]; exact hjlt)

set_option maxRecDepth 8192 in
/-- **Item 29.** Every member of the forbidden family has `ex(n, A) ≥ c n^{4/3}` for `n ≥ 80`. -/
theorem forbidden_lower : ∀ A ∈ forbiddenFamily, ∀ n : ℕ, 80 ≤ n →
    cLow * (n : ℝ) ^ (4 / 3 : ℝ) ≤ SimpleGraph.extremalNumber n A.2 := by
  classical
  intro A hA n hn
  have h30 : incidenceOrder 2 ≤ n := by unfold incidenceOrder; omega
  have h80 : incidenceOrder 3 ≤ n := by unfold incidenceOrder; omega
  have char2 : ∀ j, ringChar (GaloisField 2 j) = 2 := fun j => ringChar.eq (GaloisField 2 j) 2
  have char3 : ∀ j, ringChar (GaloisField 3 j) ≠ 2 := fun j => by
    rw [ringChar.eq (GaloisField 3 j) 3]; norm_num
  simp only [forbiddenFamily, Finset.mem_insert, Finset.mem_union] at hA
  rcases hA with rfl | rfl | hJ | hK
  · exact lower_of_free 2 le_rfl (by norm_num) cycle4_noIsolated
      (by intro j _ _ _; exact Iq_cycle4_free _) h30
  · exact lower_of_free 2 le_rfl (by norm_num) cycle6_noIsolated
      (by intro j _ _ _; exact Iq_cycle6_free _) h30
  · exact lower_of_free 2 le_rfl (by norm_num) (jMember_noIsolated A hJ)
      (by intro j _ _ _ hc; exact iq_jFree (char2 j) ⟨A, hJ, hc⟩) h30
  · exact lower_of_free 3 (by norm_num) le_rfl (kMember_noIsolated A hK)
      (by intro j _ _ _ hc; exact iq_kFree (char3 j) ⟨A, hK, hc⟩) h80

end A575

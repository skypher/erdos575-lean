import JustinSun.Erdos575.Item16.Item16
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring

/-! The final upper-bound assembly, with the vertex-cover claim supplied by lane 575K. -/

namespace L575U

local notation "𝓕" => forbiddenFamily

private theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- Blueprint item 17 as a statement conditional on the vertex-cover result. -/
def Item17UpperBoundClaim (h16 : L575K.Item16Claim) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (JustinSun.Erdos575.exFamily n 𝓕 : ℝ) ≤
      32 * (n : ℝ) ^ ((21 : ℝ) / 16)

/-- The explicit threshold contradicts the final degree inequality in item 17. -/
theorem item17_constants_contradiction {N d : ℕ} (hN : 1 ≤ N)
    (hthreshold : 16 * Real.rpow (N : ℝ) ((5 : ℝ) / 16) ≤ d)
    (hupper : d ^ 16 ≤ 2 ^ 17 * N ^ 5) : False := by
  let x : ℝ := N
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast hN
  have hd : 16 * Real.rpow x ((5 : ℝ) / 16) ≤ (d : ℝ) := by
    exact_mod_cast hthreshold
  have hpowid : (16 * x ^ ((5 : ℝ) / 16)) ^ 16 =
      16 ^ 16 * x ^ 5 := by
    rw [mul_pow]
    have hxpow : (x ^ ((5 : ℝ) / 16)) ^ 16 = x ^ 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hxpow]
  have hpow : (16 * x ^ ((5 : ℝ) / 16)) ^ 16 ≤ (d : ℝ) ^ 16 := by
    have hxpos : 0 < x := by linarith
    have hbasepos : 0 < 16 * x ^ ((5 : ℝ) / 16) := by
      exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hxpos _)
    have h := Real.rpow_le_rpow (le_of_lt hbasepos) hd
      (by norm_num : (0 : ℝ) ≤ 16)
    convert h using 1 <;> norm_num [Real.rpow_natCast]
  have hup0 : (d : ℝ) ^ 16 ≤ (2 : ℝ) ^ 17 * (N : ℝ) ^ 5 := by
    exact_mod_cast hupper
  have hup : (d : ℝ) ^ 16 ≤ (2 : ℝ) ^ 17 * x ^ 5 := by simpa [x] using hup0
  rw [hpowid] at hpow
  have hx5 : 0 < x ^ 5 := by positivity
  nlinarith [mul_pos (by norm_num : (0 : ℝ) < 2 ^ 64 - 2 ^ 17) hx5]

/-- Item 17's final count and radius bounds contradict its degree threshold. -/
theorem item17_pruned_arithmetic {N d u Δ : ℕ} (hN : 1 ≤ N) (hd : 2 ≤ d)
    (hthreshold : 16 * Real.rpow (N : ℝ) ((5 : ℝ) / 16) ≤ d)
    (hU : (u : ℝ) ≤ 16384 * (N : ℝ) ^ 5 / (d : ℝ) ^ 13)
    (hRadius : Δ * (d - 1) ^ 2 ≤ N)
    (hEdges : N * d ≤ 2 * u * Δ) : False := by
  let n : ℝ := N
  let r : ℝ := d
  let ur : ℝ := u
  let dr : ℝ := Δ
  have hn : 0 < n := by dsimp [n]; exact_mod_cast (by omega : 0 < N)
  have hr : 0 < r := by dsimp [r]; exact_mod_cast (by omega : 0 < d)
  have hUscaled : ur * r ^ 13 ≤ 16384 * n ^ 5 := by
    have hU' : (u : ℝ) * (d : ℝ) ^ 13 ≤ 16384 * (N : ℝ) ^ 5 :=
      (le_div_iff₀ (by positivity : 0 < (d : ℝ) ^ 13)).mp hU
    simpa [n, r, ur] using hU'
  have hRadiusR : dr * (r - 1) ^ 2 ≤ n := by
    have hRnat : (Δ : ℝ) * ((d - 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) := by
      exact_mod_cast hRadius
    have hd1 : 1 ≤ d := by omega
    have hR := hRnat
    rw [Nat.cast_sub hd1] at hR
    simpa [n, r, dr] using hR
  have hhalf : r / 2 ≤ r - 1 := by
    dsimp [r]
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hsquare : (r / 2) ^ 2 ≤ (r - 1) ^ 2 := by
    have hsum : 0 ≤ (r - 1) + r / 2 := by nlinarith [hhalf, hr]
    nlinarith [mul_nonneg (sub_nonneg.mpr hhalf) hsum]
  have hRadiusScaled : dr * r ^ 2 ≤ 4 * n := by
    calc
      dr * r ^ 2 = 4 * (dr * (r / 2) ^ 2) := by ring
      _ ≤ 4 * (dr * (r - 1) ^ 2) := by
        have hdr : 0 ≤ dr := by dsimp [dr]; positivity
        have hmul := mul_le_mul_of_nonneg_left hsquare hdr
        nlinarith [hmul]
      _ ≤ 4 * n := by nlinarith [hRadiusR]
  have hEdgesR : n * r ≤ 2 * ur * dr := by
    have hE : (N : ℝ) * (d : ℝ) ≤ 2 * (u : ℝ) * Δ := by exact_mod_cast hEdges
    simpa [n, r, ur, dr] using hE
  have hScaled : n * r ^ 16 ≤ 2 ^ 17 * n ^ 6 := by
    calc
      n * r ^ 16 = (n * r) * r ^ 15 := by ring
      _ ≤ (2 * ur * dr) * r ^ 15 := by
        exact mul_le_mul_of_nonneg_right hEdgesR (by positivity)
      _ = 2 * (ur * r ^ 13) * (dr * r ^ 2) := by ring
      _ ≤ 2 * (16384 * n ^ 5) * (4 * n) := by
        calc
          _ ≤ 2 * (16384 * n ^ 5) * (dr * r ^ 2) := by
            gcongr
          _ ≤ 2 * (16384 * n ^ 5) * (4 * n) := by
            gcongr
      _ = 2 ^ 17 * n ^ 6 := by ring
  have hScaled' : n * r ^ 16 ≤ n * (2 ^ 17 * n ^ 5) := by
    nlinarith [hScaled]
  have hPower : r ^ 16 ≤ 2 ^ 17 * n ^ 5 := by
    exact (mul_le_mul_iff_right₀ hn).mp hScaled'
  have hPowerR : (d : ℝ) ^ 16 ≤ (2 : ℝ) ^ 17 * (N : ℝ) ^ 5 := by
    simpa [r, n] using hPower
  have hPowerNat : d ^ 16 ≤ 2 ^ 17 * N ^ 5 := by exact_mod_cast hPowerR
  exact item17_constants_contradiction hN hthreshold hPowerNat

/-- The item 16 claim turns every edge into an incidence with the exceptional set. -/
theorem item17_edge_covered_by_U {V : Type} [Fintype V] [DecidableEq V]
    (h16 : L575K.Item16Claim) (G : SimpleGraph V) [DecidableRel G.Adj]
    (χ : G.Coloring (Fin 2)) (hfree4 : C4Free G) (hfree6 : C6Free G)
    (hK : ∀ A ∈ K, A.2.Free G) (S0 S1 : Finset V)
    (h0 : ∀ x ∈ S0, χ x = 0) (h1 : ∀ x ∈ S1, χ x = 1)
    (hpartition : ∀ x, x ∈ S0 ∨ x ∈ S1) :
    ∀ e ∈ G.edgeFinset, ∃ v, v ∈ U_S G S0 ∪ U_S G S1 ∧ v ∈ e := by
  classical
  intro e he
  revert he
  refine Sym2.inductionOn e ?_
  intro a b he
  have hab : G.Adj a b := G.mem_edgeSet.mp (G.mem_edgeFinset.mp he)
  have hcolors := χ.valid hab
  rcases fin2_cases (χ a) with hca | hca
  · have hcb : χ b = 1 := by
      rcases fin2_cases (χ b) with hzero | hone
      · exact False.elim (hcolors (hca.trans hzero.symm))
      · exact hone
    have ha0 : a ∈ S0 := (hpartition a).resolve_right (by
      intro ha1
      exact (by decide : (0 : Fin 2) ≠ 1) (hca.symm.trans (h1 a ha1)))
    have hb0 : b ∉ S0 := by
      intro hbS
      exact hcolors ((h0 a ha0).trans (h0 b hbS).symm)
    have hb1 : b ∈ S1 := (hpartition b).resolve_left hb0
    have hcover : a ∈ U_S G S0 ∨ b ∈ U_S G S1 := by
      by_contra hnot
      exact h16 G χ hfree4 hfree6 hK S0 S1 h0 h1 a b hab ha0
        (by intro hu; exact hnot (Or.inl hu)) hb1
        (by intro hu; exact hnot (Or.inr hu))
    rcases hcover with hu | hu
    · exact ⟨a, Finset.mem_union.mpr (Or.inl hu), by simp⟩
    · exact ⟨b, Finset.mem_union.mpr (Or.inr hu), by simp⟩
  · have hcb : χ b = 0 := by
      rcases fin2_cases (χ b) with hzero | hone
      · exact hzero
      · exact False.elim (hcolors (hca.trans hone.symm))
    have ha0 : a ∉ S0 := by
      intro haS
      exact (by decide : (1 : Fin 2) ≠ 0) (hca.symm.trans (h0 a haS))
    have ha1 : a ∈ S1 := (hpartition a).resolve_left ha0
    have hb1 : b ∈ S0 := (hpartition b).resolve_right (by
      intro hbS
      exact (by decide : (0 : Fin 2) ≠ 1) (hcb.symm.trans (h1 b hbS)))
    have hcover : b ∈ U_S G S0 ∨ a ∈ U_S G S1 := by
      by_contra hnot
      exact h16 G χ hfree4 hfree6 hK S0 S1 h0 h1 b a hab.symm hb1
        (by intro hu; exact hnot (Or.inl hu)) ha1
        (by intro hu; exact hnot (Or.inr hu))
    rcases hcover with hu | hu
    · exact ⟨b, Finset.mem_union.mpr (Or.inl hu), by simp⟩
    · exact ⟨a, Finset.mem_union.mpr (Or.inr hu), by simp⟩

/-- A vertex cover bounds the edge count by maximum degree times cover size. -/
theorem item17_edges_le_cover_degree {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hcover : ∀ e ∈ G.edgeFinset, ∃ v, v ∈ U ∧ v ∈ e) :
    G.edgeFinset.card ≤ G.maxDegree * U.card := by
  classical
  let incidences : Finset (Sym2 V) := U.biUnion (fun v => G.incidenceFinset v)
  have hsubset : G.edgeFinset ⊆ incidences := by
    intro e he
    obtain ⟨v, hv, hve⟩ := hcover e he
    apply Finset.mem_biUnion.mpr
    refine ⟨v, hv, ?_⟩
    rw [SimpleGraph.mem_incidenceFinset]
    change e ∈ G.incidenceSet v
    simp only [SimpleGraph.incidenceSet]
    exact ⟨G.mem_edgeFinset.mp he, hve⟩
  calc
    G.edgeFinset.card ≤ incidences.card := Finset.card_le_card hsubset
    _ ≤ ∑ v ∈ U, (G.incidenceFinset v).card := Finset.card_biUnion_le
    _ = ∑ v ∈ U, G.degree v := by simp
    _ ≤ ∑ _v ∈ U, G.maxDegree := by
      apply Finset.sum_le_sum
      intro v hv
      exact G.degree_le_maxDegree v
    _ = G.maxDegree * U.card := by simp [Nat.mul_comm]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem graph_edge_bound_of_free (h16 : L575K.Item16Claim)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : ∀ A ∈ forbiddenFamily, A.2.Free G) (hn : 1 ≤ n) :
    (G.edgeFinset.card : ℝ) ≤ 32 * (n : ℝ) ^ ((21 : ℝ) / 16) := by
  classical
  by_contra hnot
  have hlt : 32 * (n : ℝ) ^ ((21 : ℝ) / 16) < (G.edgeFinset.card : ℝ) := lt_of_not_ge hnot
  let m := G.edgeFinset.card
  have hmpos : 0 < m := by
    by_contra h
    have : m = 0 := by omega
    have hnonneg : (0 : ℝ) ≤ 32 * (n : ℝ) ^ ((21 : ℝ) / 16) := by positivity
    simp [m, this] at hlt
    linarith
  have hfree4 : C4Free G := by
    intro c
    exact hfree C4Graph (by simp [forbiddenFamily]) c
  have hfree6 : C6Free G := by
    intro c
    exact hfree C6Graph (by simp [forbiddenFamily]) c
  obtain ⟨X, T, hT, hmred, hbi, hB4, hB6, hrad, hTn⟩ :=
    item11_minimum_degree_reduction G m n hmpos (by rfl) (by simp) hfree4 hfree6
  let Vb := {x : Fin n // x ∈ T}
  let B : SimpleGraph Vb := (cutGraph G X).induce (↑T : Set (Fin n))
  have hBfree {A : FinGraph} (hA : A ∈ forbiddenFamily) : A.2.Free B := by
    intro c
    apply hfree A hA
    rcases c with ⟨c⟩
    exact ⟨(SimpleGraph.Copy.ofLE (cutGraph G X) G (cutGraph_le G X)).comp
      ((SimpleGraph.Copy.induce (cutGraph G X) (↑T : Set (Fin n))).comp c)⟩
  have hJ : ∀ A ∈ J, A.2.Free B := fun A hA => hBfree (A := A) (by
    simp [forbiddenFamily, hA])
  have hK : ∀ A ∈ K, A.2.Free B := fun A hA => hBfree (A := A) (by
    simp [forbiddenFamily, hA])
  obtain ⟨χ⟩ := hbi
  let S0 : Finset Vb := Finset.univ.filter (fun v => χ v = 0)
  let S1 : Finset Vb := Finset.univ.filter (fun v => χ v = 1)
  have hS0 : ∀ v ∈ S0, χ v = 0 := by intro v hv; exact (Finset.mem_filter.mp hv).2
  have hS1 : ∀ v ∈ S1, χ v = 1 := by intro v hv; exact (Finset.mem_filter.mp hv).2
  have hpartition : ∀ v : Vb, v ∈ S0 ∨ v ∈ S1 := by
    intro v
    rcases fin2_cases (χ v) with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  let d := B.minDegree
  let N := T.card
  have hN : 1 ≤ N := by
    have := hT
    simpa [N] using this.card_pos
  have hd : 2 ≤ d := by
    by_contra h
    have hdle : d ≤ 1 := by omega
    have hmle : m ≤ 2 * n * d := by simpa [d, B] using hmred
    have hmreal : (m : ℝ) ≤ 2 * n * d := by exact_mod_cast hmle
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hexp : (21 : ℝ) / 16 = 1 + (5 : ℝ) / 16 := by norm_num
    have hnpow : n ≤ (n : ℝ) ^ ((21 : ℝ) / 16) := by
      rw [hexp, Real.rpow_add (by positivity), Real.rpow_one]
      have hq : 1 ≤ Real.rpow (n : ℝ) ((5 : ℝ) / 16) :=
        Real.one_le_rpow hnreal (by norm_num)
      calc
        (n : ℝ) = n * 1 := by ring
        _ ≤ n * Real.rpow (n : ℝ) ((5 : ℝ) / 16) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
    have hdleR : (d : ℝ) ≤ 1 := by exact_mod_cast hdle
    have : (m : ℝ) ≤ 2 * n := by nlinarith
    nlinarith
  have hthreshold : 16 * Real.rpow (N : ℝ) ((5 : ℝ) / 16) ≤ d := by
    have hmle : m ≤ 2 * n * d := by simpa [d, B] using hmred
    have hmreal : (m : ℝ) ≤ 2 * n * d := by exact_mod_cast hmle
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hNle : N ≤ n := hTn
    have hNleR : (N : ℝ) ≤ n := by exact_mod_cast hNle
    have hmono : Real.rpow (N : ℝ) ((5 : ℝ) / 16) ≤
        Real.rpow (n : ℝ) ((5 : ℝ) / 16) :=
      Real.rpow_le_rpow (by positivity) hNleR (by norm_num)
    have hexp : (21 : ℝ) / 16 = 1 + (5 : ℝ) / 16 := by norm_num
    have hnexp : Real.rpow (n : ℝ) ((21 : ℝ) / 16) =
        (n : ℝ) * Real.rpow (n : ℝ) ((5 : ℝ) / 16) := by
      calc
        Real.rpow (n : ℝ) ((21 : ℝ) / 16) = Real.rpow (n : ℝ) (1 + (5 : ℝ) / 16) := by rw [hexp]
        _ = Real.rpow (n : ℝ) 1 * Real.rpow (n : ℝ) ((5 : ℝ) / 16) :=
          Real.rpow_add (by positivity) _ _
        _ = (n : ℝ) * Real.rpow (n : ℝ) ((5 : ℝ) / 16) := by simp
    have hltm : 32 * Real.rpow (n : ℝ) ((21 : ℝ) / 16) < (m : ℝ) := by
      change 32 * Real.rpow (n : ℝ) ((21 : ℝ) / 16) < (m : ℝ)
      simpa [m] using hlt
    have hstrict : 32 * (n : ℝ) * Real.rpow (n : ℝ) ((5 : ℝ) / 16) <
        2 * n * d := by
      rw [hnexp] at hltm
      have hltm' : 32 * (n : ℝ) * Real.rpow (n : ℝ) ((5 : ℝ) / 16) < (m : ℝ) := by
        nlinarith [hltm]
      exact lt_of_lt_of_le hltm' hmreal
    have hnpos : (0 : ℝ) < n := by linarith
    have hlarge : 16 * Real.rpow (n : ℝ) ((5 : ℝ) / 16) ≤ d := by
      have hmul : n * (16 * Real.rpow (n : ℝ) ((5 : ℝ) / 16)) < n * d := by
        nlinarith [hstrict]
      exact le_of_lt ((mul_lt_mul_iff_of_pos_left hnpos).mp hmul)
    have hdreal : 16 * Real.rpow (N : ℝ) ((5 : ℝ) / 16) ≤ (d : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left hmono (by norm_num)) hlarge
    exact_mod_cast hdreal
  have hmin : ∀ v : Vb, d ≤ B.degree v := by
    intro v
    exact B.minDegree_le_degree v
  have hcardVb : Fintype.card Vb = N := by simp [Vb, N]
  have hthreshold' : 16 * Real.rpow (Fintype.card Vb : ℝ) ((5 : ℝ) / 16) ≤ d := by
    simpa [hcardVb] using hthreshold
  have hbound0 := item15_bound_claim B χ hB4 hB6 hJ S0
    (by intro v; exact ⟨fun hv => hS0 v hv, fun hv => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩)
    d hthreshold' hmin
  let χ' : B.Coloring (Fin 2) := SimpleGraph.Coloring.mk
    (fun v => Equiv.swap 0 1 (χ v)) (by
      intro v w hadj
      intro heq
      exact χ.valid hadj (Equiv.injective (Equiv.swap 0 1) heq))
  have hS1side : ∀ v : Vb, v ∈ S1 ↔ χ' v = 0 := by
    intro v
    simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and]
    change χ v = 1 ↔ Equiv.swap 0 1 (χ v) = 0
    rcases fin2_cases (χ v) with hc | hc
    · simp [hc, Equiv.swap_apply_left]
    · simp [hc, Equiv.swap_apply_right]
  have hbound1 := item15_bound_claim B χ' hB4 hB6 hJ S1 hS1side d hthreshold' hmin
  let U := U_S B S0 ∪ U_S B S1
  have hU : (U.card : ℝ) ≤ 16384 * (N : ℝ)^5 / (d : ℝ)^13 := by
    have hcards := Finset.card_union_le (U_S B S0) (U_S B S1)
    have hreal : ((U_S B S0).card : ℝ) + (U_S B S1).card ≤
        8192 * (N : ℝ)^5 / (d : ℝ)^13 + 8192 * (N : ℝ)^5 / (d : ℝ)^13 := by
      exact add_le_add (by simpa [hcardVb] using hbound0) (by simpa [hcardVb] using hbound1)
    have hcardR : (U.card : ℝ) ≤ ((U_S B S0).card : ℝ) + (U_S B S1).card := by
      exact_mod_cast hcards
    calc
      (U.card : ℝ) ≤ (U_S B S0).card + (U_S B S1).card := hcardR
      _ ≤ 8192 * (N : ℝ)^5 / (d : ℝ)^13 + 8192 * (N : ℝ)^5 / (d : ℝ)^13 := hreal
      _ = 16384 * (N : ℝ)^5 / (d : ℝ)^13 := by ring
  have hcover := item17_edge_covered_by_U h16 B χ hB4 hB6 hK S0 S1 hS0 hS1 hpartition
  have hEdgeCover := item17_edges_le_cover_degree B U hcover
  have hEdges : N * d ≤ 2 * U.card * B.maxDegree := by
    have hdegree : N * d ≤ ∑ v : Vb, B.degree v := by
      calc
        N * d = ∑ _x : Vb, d := by simp [N, Vb, Nat.mul_comm]
        _ ≤ ∑ x : Vb, B.degree x := Finset.sum_le_sum (fun x _ => hmin x)
    have htwice := B.sum_degrees_eq_twice_card_edges
    have hle : N * d ≤ 2 * B.edgeFinset.card := hdegree.trans_eq htwice
    have hEdgeR : B.edgeFinset.card ≤ B.maxDegree * U.card := hEdgeCover
    calc
      N * d ≤ 2 * B.edgeFinset.card := hle
      _ ≤ 2 * (B.maxDegree * U.card) := Nat.mul_le_mul_left 2 hEdgeR
      _ = 2 * U.card * B.maxDegree := by ring
  have hrad' : B.maxDegree * (d - 1)^2 ≤ N := by
    simpa [d, N, B, Vb] using hrad
  have hfalse := item17_pruned_arithmetic (N := N) (d := d) (u := U.card)
    (Δ := B.maxDegree) hN hd hthreshold hU hrad' hEdges
  exact False.elim hfalse

theorem exFamily_le_of_item16 (h16 : L575K.Item16Claim) (n : ℕ) (hn : 1 ≤ n) :
    (JustinSun.Erdos575.exFamily n forbiddenFamily : ℝ) ≤
      32 * (n : ℝ) ^ ((21 : ℝ) / 16) := by
  classical
  let R : ℝ := 32 * (n : ℝ) ^ ((21 : ℝ) / 16)
  have hnat : JustinSun.Erdos575.exFamily n forbiddenFamily ≤ Nat.floor R := by
    unfold JustinSun.Erdos575.exFamily
    rw [Finset.sup_le_iff]
    intro G hG
    have hG' : ∀ A ∈ forbiddenFamily, A.2.Free G := by simpa using hG
    have hreal := graph_edge_bound_of_free h16 G hG' hn
    exact (Nat.le_floor_iff (by dsimp [R]; positivity)).2 (by simpa [R] using hreal)
  have hcast : (JustinSun.Erdos575.exFamily n forbiddenFamily : ℝ) ≤ (Nat.floor R : ℝ) := by
    exact_mod_cast hnat
  have hfloor : (Nat.floor R : ℝ) ≤ R := Nat.floor_le (by positivity : 0 ≤ R)
  exact hcast.trans (by simpa [R] using hfloor)

theorem exFamily_le (n : ℕ) (hn : 1 ≤ n) :
    (JustinSun.Erdos575.exFamily n forbiddenFamily : ℝ) ≤
      32 * (n : ℝ) ^ ((21 : ℝ) / 16) :=
  exFamily_le_of_item16 L575K.item16 n hn

end L575U

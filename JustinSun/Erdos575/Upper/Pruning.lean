import JustinSun.Erdos575.Upper.CommonNeighbor
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite cut and pruning notation for the upper-bound argument. -/

namespace L575U

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph consisting of the edges crossing a vertex set and its complement. -/
noncomputable def cutGraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph V :=
  G.between (S : Set V) ((S : Set V)ᶜ)

instance (G : SimpleGraph V) (S : Finset V) [DecidableRel G.Adj] :
    DecidableRel (cutGraph G S).Adj := by
  intro v w
  change Decidable (G.Adj v w ∧ (v ∈ (S : Set V) ∧ w ∈ (S : Set V)ᶜ ∨
    v ∈ (S : Set V)ᶜ ∧ w ∈ (S : Set V)))
  infer_instance

theorem cutGraph_le (G : SimpleGraph V) (S : Finset V) : cutGraph G S ≤ G :=
  SimpleGraph.between_le

theorem cutGraph_bipartite (G : SimpleGraph V) (S : Finset V) :
    (cutGraph G S).IsBipartite := by
  apply SimpleGraph.between_isBipartite
  simpa [Set.disjoint_left]

theorem cutGraph_edges_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    (cutGraph G S).edgeFinset.card ≤ G.edgeFinset.card := by
  classical
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono (cutGraph_le G S))

/-- A cut with at least half the edges of a finite graph. -/
def HasLargeCut (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ S : Finset V, 2 * (cutGraph G S).edgeFinset.card ≥ G.edgeFinset.card

/-- The maximum-cut assertion used before pruning. -/
def MaximumCutClaim (G : SimpleGraph V) [DecidableRel G.Adj] : Prop := HasLargeCut G

/-- Flip one color in a two-coloring. -/
def flipColor (a : V) (χ : V → Bool) : V → Bool :=
  Function.update χ a (!χ a)

@[simp] theorem flipColor_at (a : V) (χ : V → Bool) :
    flipColor a χ a = !χ a := by simp [flipColor]

theorem flipColor_at_ne (a x : V) (h : x ≠ a) (χ : V → Bool) :
    flipColor a χ x = χ x := by simp [flipColor, h]

theorem flipColor_involutive (a : V) : Function.Involutive (flipColor a) := by
  intro χ
  funext x
  by_cases h : x = a
  · subst x
    simp [flipColor]
  · simp [flipColor, h]

/-- Colorings that agree at two distinct vertices are paired with those that disagree. -/
noncomputable def flipColoringEquiv (a b : V) (hab : a ≠ b) :
    {χ : V → Bool // χ a = χ b} ≃ {χ : V → Bool // χ a ≠ χ b} where
  toFun χ := ⟨flipColor a χ.1, by
    have hb := flipColor_at_ne a b hab.symm χ.1
    have heq : χ.1 a = χ.1 b := χ.2
    cases h : χ.1 a <;> cases h' : χ.1 b <;> simp_all [flipColor_at, hb]⟩
  invFun χ := ⟨flipColor a χ.1, by
    have hb := flipColor_at_ne a b hab.symm χ.1
    cases h : χ.1 a with
    | false =>
      cases h' : χ.1 b with
      | false => exact False.elim (χ.2 (by rw [h, h']))
      | true => simp [flipColor_at, h, h', hb]
    | true =>
      cases h' : χ.1 b with
      | false => simp [flipColor_at, h, h', hb]
      | true => exact False.elim (χ.2 (by rw [h, h']))⟩
  left_inv χ := by
    apply Subtype.ext
    exact flipColor_involutive a χ.1
  right_inv χ := by
    apply Subtype.ext
    exact flipColor_involutive a χ.1

theorem card_colorings_equal_eq_disagree (a b : V) (hab : a ≠ b) :
    Fintype.card {χ : V → Bool // χ a = χ b} =
      Fintype.card {χ : V → Bool // χ a ≠ χ b} :=
  Fintype.card_congr (flipColoringEquiv a b hab)

noncomputable def coloringsByAgreementEquiv (a b : V) :
    Sum {χ : V → Bool // χ a = χ b} {χ : V → Bool // χ a ≠ χ b} ≃ (V → Bool) where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun χ := if h : χ a = χ b then Sum.inl ⟨χ, h⟩ else Sum.inr ⟨χ, h⟩
  left_inv := by
    intro χ
    cases χ with
    | inl χ => simp [χ.2]
    | inr χ => simp [χ.2]
  right_inv := by
    intro χ
    by_cases h : χ a = χ b
    · simp [h]
    · simp [h]

theorem two_mul_card_disagreeColorings (a b : V) (hab : a ≠ b) :
    2 * Fintype.card {χ : V → Bool // χ a ≠ χ b} = Fintype.card (V → Bool) := by
  have hs := Fintype.card_congr (coloringsByAgreementEquiv a b)
  rw [Fintype.card_sum, card_colorings_equal_eq_disagree a b hab] at hs
  omega

/-- The number of oriented edges crossing a coloring. -/
noncomputable def orderedCrossCount (G : SimpleGraph V) (χ : V → Bool) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter fun p : V × V => G.Adj p.1 p.2 ∧ χ p.1 ≠ χ p.2).card

theorem orderedCrossCount_eq_two_mul_cut (G : SimpleGraph V) (χ : V → Bool)
    [DecidableRel G.Adj] :
    orderedCrossCount G χ = 2 * (cutGraph G {v | χ v = true}).edgeFinset.card := by
  classical
  unfold orderedCrossCount
  have heq :
      (Finset.univ.filter fun p : V × V => G.Adj p.1 p.2 ∧ χ p.1 ≠ χ p.2) =
        (Finset.univ.filter fun p : V × V =>
          (cutGraph G {v | χ v = true}).Adj p.1 p.2) := by
    ext p
    simp [cutGraph, SimpleGraph.between_adj]
    cases χ p.1 <;> cases χ p.2 <;> simp
  rw [heq]
  exact (SimpleGraph.two_mul_card_edgeFinset (G := cutGraph G {v | χ v = true})).symm

theorem sum_orderedCrossCount (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ χ : V → Bool, orderedCrossCount G χ) =
      Fintype.card (V → Bool) * G.edgeFinset.card := by
  classical
  unfold orderedCrossCount
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have hcolor (a b : V) (hab : a ≠ b) :
      2 * (∑ χ : V → Bool, if χ a ≠ χ b then 1 else 0) =
        Fintype.card (V → Bool) := by
    rw [Finset.sum_boole, ← Fintype.card_subtype]
    exact two_mul_card_disagreeColorings a b hab
  have hterm (p : V × V) :
      2 * (∑ χ : V → Bool,
        if G.Adj p.1 p.2 ∧ χ p.1 ≠ χ p.2 then 1 else 0) =
        if G.Adj p.1 p.2 then Fintype.card (V → Bool) else 0 := by
    by_cases hadj : G.Adj p.1 p.2
    · have hp : p.1 ≠ p.2 := G.ne_of_adj hadj
      simpa [hadj, Nat.mul_comm] using hcolor p.1 p.2 hp
    · simp [hadj]
  have hsum2 :
      2 * (∑ p : V × V, ∑ χ : V → Bool,
        if G.Adj p.1 p.2 ∧ χ p.1 ≠ χ p.2 then 1 else 0) =
          (∑ p : V × V, if G.Adj p.1 p.2 then Fintype.card (V → Bool) else 0) := by
    calc
      _ = ∑ p : V × V, 2 * (∑ χ : V → Bool,
          if G.Adj p.1 p.2 ∧ χ p.1 ≠ χ p.2 then 1 else 0) := by rw [Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hterm p
  have hAdjCount :
      (∑ p : V × V, if G.Adj p.1 p.2 then (1 : ℕ) else 0) =
        2 * G.edgeFinset.card := by
    simpa [Finset.sum_boole, Nat.mul_comm] using
      (SimpleGraph.two_mul_card_edgeFinset (G := G)).symm
  have hR :
      (∑ p : V × V, if G.Adj p.1 p.2 then Fintype.card (V → Bool) else 0) =
        2 * (Fintype.card (V → Bool) * G.edgeFinset.card) := by
    calc
      _ = ∑ p : V × V, (if G.Adj p.1 p.2 then (1 : ℕ) else 0) *
            Fintype.card (V → Bool) := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases h : G.Adj p.1 p.2 <;> simp [h]
      _ = (∑ p : V × V, if G.Adj p.1 p.2 then (1 : ℕ) else 0) *
            Fintype.card (V → Bool) := by rw [Finset.sum_mul]
      _ = 2 * (Fintype.card (V → Bool) * G.edgeFinset.card) := by
        rw [hAdjCount]
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hR] at hsum2
  omega

theorem maximumCut_exists (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasLargeCut G := by
  classical
  obtain ⟨χ, hχ⟩ : ∃ χ : V → Bool, G.edgeFinset.card ≤ orderedCrossCount G χ := by
    by_contra hnone
    have hlt (χ : V → Bool) : orderedCrossCount G χ < G.edgeFinset.card := by
      exact Nat.lt_of_not_ge (fun hh => hnone ⟨χ, hh⟩)
    have hsumlt :
        (∑ χ : V → Bool, orderedCrossCount G χ) <
          ∑ χ : V → Bool, G.edgeFinset.card := by
      have hne : (Finset.univ : Finset (V → Bool)).Nonempty := Finset.univ_nonempty
      obtain ⟨χ₀, hχ₀⟩ := hne
      apply Finset.sum_lt_sum
      · intro χ hχ
        exact (hlt χ).le
      · exact ⟨χ₀, hχ₀, hlt χ₀⟩
    rw [sum_orderedCrossCount G] at hsumlt
    have hconst : (∑ χ : V → Bool, G.edgeFinset.card) =
        Fintype.card (V → Bool) * G.edgeFinset.card := by simp
    rw [hconst] at hsumlt
    omega
  refine ⟨Finset.univ.filter (fun v => χ v = true), ?_⟩
  have hcross := orderedCrossCount_eq_two_mul_cut G χ
  simpa [hcross] using hχ

/-- The minimum-degree conclusion of the vertex deletion step. -/
noncomputable def Item9PruningClaim (H : SimpleGraph V) [DecidableRel H.Adj]
    (m n : ℕ) : Prop := by
  classical
  exact 0 < m → m ≤ 2 * H.edgeFinset.card → Fintype.card V ≤ n →
    ∃ S : Finset V, S.Nonempty ∧
      m ≤ 2 * n * (H.induce (fun v : V => v ∈ S)).minDegree

/-- The finite edge set induced by a vertex set. -/
noncomputable def edgesInside (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => e.toFinset ⊆ S)

theorem edgesInside_erase_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) (hv : v ∈ S) :
    edgesInside G S = edgesInside G (S.erase v) ∪
      (edgesInside G S).filter (fun e => v ∈ e) := by
  classical
  ext e
  simp only [edgesInside, Finset.mem_filter, Finset.mem_union]
  rw [Finset.subset_erase]
  simp only [Sym2.mem_toFinset]
  constructor
  · rintro ⟨he, hsub⟩
    by_cases hve : v ∈ e
    · exact Or.inr ⟨⟨he, hsub⟩, hve⟩
    · exact Or.inl ⟨he, hsub, hve⟩
  · rintro (⟨he, hsub, hnv⟩ | ⟨⟨he, hsub⟩, hve⟩)
    · exact ⟨he, hsub⟩
    · exact ⟨he, hsub⟩

theorem edgesInside_erase_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) (hv : v ∈ S) :
    (edgesInside G S).card = (edgesInside G (S.erase v)).card +
      ((edgesInside G S).filter (fun e => v ∈ e)).card := by
  have hd : Disjoint (edgesInside G (S.erase v))
      ((edgesInside G S).filter (fun e => v ∈ e)) := by
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    rw [Finset.mem_filter] at he₂
    unfold edgesInside at he₁
    rw [Finset.mem_filter] at he₁
    have hnot := (Finset.subset_erase.mp he₁.2).2
    exact hnot (Sym2.mem_toFinset.mpr he₂.2)
  calc
    _ = (edgesInside G (S.erase v) ∪
        (edgesInside G S).filter (fun e => v ∈ e)).card :=
          congrArg Finset.card (edgesInside_erase_partition G S v hv)
    _ = _ := Finset.card_union_of_disjoint hd

def induce_erase_iso (G : SimpleGraph V) (S : Finset V) (v : V) :
    ((G.induce (↑S : Set V)).induce {x | x.1 ≠ v}) ≃g
      G.induce (↑(S.erase v) : Set V) := by
  let e : ({x : {y // y ∈ (↑S : Set V)} // x.1 ≠ v} ≃
      {y // y ∈ (↑(S.erase v) : Set V)}) := {
    toFun := fun x => ⟨x.1.1, Finset.mem_erase.mpr ⟨x.2, x.1.2⟩⟩
    invFun := fun y => ⟨⟨y.1, (Finset.mem_erase.mp y.2).2⟩, (Finset.mem_erase.mp y.2).1⟩
    left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro y; apply Subtype.ext; rfl }
  refine { toEquiv := e, map_rel_iff' := ?_ }
  intro a b
  simp [SimpleGraph.induce_adj, e]

theorem edgesInside_erase_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) (hv : v ∈ S) :
    (edgesInside G S).card = (edgesInside G (S.erase v)).card +
      (G.induce (↑S : Set V)).degree ⟨v, hv⟩ := by
  classical
  have hS : (edgesInside G S).card = ((G.induce (↑S : Set V)).edgeFinset).card := by
    simpa [edgesInside] using
      (SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := G) S)
  have hErase : (edgesInside G (S.erase v)).card =
      ((G.induce (↑(S.erase v) : Set V)).edgeFinset).card := by
    simpa [edgesInside] using
      (SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := G) (S.erase v))
  let H := G.induce (↑S : Set V)
  let x : {y // y ∈ (↑S : Set V)} := ⟨v, hv⟩
  have hdel := H.card_edgeFinset_deleteIncidenceSet x
  have hcompl := H.card_edgeFinset_induce_compl_singleton x
  have hsets : ({x}ᶜ : Set {y // y ∈ (↑S : Set V)}) = {y | y.1 ≠ v} := by
    ext y
    change y ≠ ⟨v, hv⟩ ↔ y.1 ≠ v
    constructor
    · intro h hval
      apply h
      exact Subtype.ext hval
    · intro h heq
      apply h
      exact congrArg Subtype.val heq
  have hdel' : (H.induce {y | y.1 ≠ v}).edgeFinset.card =
      H.edgeFinset.card - H.degree x := by
    have hbij : Set.BijOn (id : {y // y ∈ (↑S : Set V)} → _) ({x}ᶜ)
        {y | y.1 ≠ v} := by
      rw [← hsets]
      exact Set.bijOn_id _
    have hIsoSub := SimpleGraph.Iso.induce (SimpleGraph.Iso.refl (G := H)) hbij
    calc
      _ = (H.induce ({x}ᶜ)).edgeFinset.card := hIsoSub.card_edgeFinset_eq.symm
      _ = _ := hcompl.trans hdel
  have hIso := (induce_erase_iso G S v).card_edgeFinset_eq
  rw [hS, hErase]
  rw [← hIso]
  change H.edgeFinset.card = (H.induce {y | y.1 ≠ v}).edgeFinset.card + H.degree x
  rw [hdel']
  exact (Nat.sub_add_cancel (H.degree_le_card_edgeFinset x)).symm

/-- An integer potential used to choose a dense induced subgraph. -/
noncomputable def pruningPotential (G : SimpleGraph V) [DecidableRel G.Adj]
    (m n : ℕ) (S : Finset V) : ℤ :=
  ((2 * n * (edgesInside G S).card : ℕ) : ℤ) - ((m * S.card : ℕ) : ℤ)

theorem item9_minimum_degree (H : SimpleGraph V) [DecidableRel H.Adj]
    (m n : ℕ) (hmpos : 0 < m) (hm : m ≤ 2 * H.edgeFinset.card)
    (hn : Fintype.card V ≤ n) :
    ∃ S : Finset V, S.Nonempty ∧
      m ≤ 2 * n * (H.induce (↑S : Set V)).minDegree := by
  classical
  let candidates : Finset (Finset V) := Finset.univ.filter Finset.Nonempty
  have hVpos : 0 < Fintype.card V := by
    by_contra h
    have hz : Fintype.card V = 0 := Nat.eq_zero_of_not_pos h
    haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hz
    have hsym : Fintype.card (Sym2 V) = 0 := by simp
    have hle : H.edgeFinset.card ≤ Fintype.card (Sym2 V) := Finset.card_le_univ _
    have hzero : H.edgeFinset.card = 0 := by rw [hsym] at hle; omega
    omega
  have hfull : candidates.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hVpos)
  let potential := pruningPotential H m n
  obtain ⟨S, hScand, hSmax⟩ := Finset.exists_max_image candidates potential hfull
  have hS : S.Nonempty := (Finset.mem_filter.mp hScand).2
  have hfullPotential : 0 ≤ potential Finset.univ := by
    have heq : edgesInside H Finset.univ = H.edgeFinset := by
      ext e
      simp [edgesInside]
    have hm' : (m : ℤ) ≤ 2 * (H.edgeFinset.card : ℤ) := by exact_mod_cast hm
    have hn' : (Fintype.card V : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    have hnMul : (m : ℤ) * (Fintype.card V : ℤ) ≤ (m : ℤ) * n :=
      mul_le_mul_of_nonneg_left hn' (by positivity)
    have hmMul : (m : ℤ) * n ≤
        (2 * (H.edgeFinset.card : ℤ)) * n :=
      mul_le_mul_of_nonneg_right hm' (by positivity)
    dsimp [potential, pruningPotential]
    rw [heq]
    have hmul := hnMul.trans hmMul
    nlinarith [hmul]
  have hSnonemptyPotential : 0 ≤ potential S := by
    have hmaxfull := hSmax Finset.univ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hVpos)⟩)
    exact hfullPotential.trans hmaxfull
  have hdegree (v : V) (hv : v ∈ S) :
      m ≤ 2 * n * (H.induce (↑S : Set V)).degree ⟨v, hv⟩ := by
    by_contra hbad
    have hlt : 2 * n * (H.induce (↑S : Set V)).degree ⟨v, hv⟩ < m :=
      Nat.lt_of_not_ge hbad
    have hdelta : potential (S.erase v) = potential S + (m : ℤ) -
        (2 * n * (H.induce (↑S : Set V)).degree ⟨v, hv⟩ : ℕ) := by
      dsimp [potential, pruningPotential]
      rw [edgesInside_erase_degree H S v hv, Finset.card_erase_of_mem hv]
      have hScard : 1 ≤ S.card := Finset.card_pos.mpr hS
      rw [Nat.cast_sub hScard]
      push_cast
      ring_nf
    have hpotlt : potential S < potential (S.erase v) := by
      rw [hdelta]
      have : (2 * n * (H.induce (↑S : Set V)).degree ⟨v, hv⟩ : ℕ) < m := hlt
      have hpos : (0 : ℤ) < (m : ℤ) -
          (2 * n * (H.induce (↑S : Set V)).degree ⟨v, hv⟩ : ℕ) := by
        omega
      omega
    by_cases hsingle : S.card = 1
    · have hpotnegative : potential S < 0 := by
        have hdeg0 : (H.induce (↑S : Set V)).degree ⟨v, hv⟩ = 0 := by
          apply Nat.eq_zero_of_not_pos
          intro hdpos
          let Gs := H.induce (↑S : Set V)
          have hpos : 0 < Gs.degree ⟨v, hv⟩ := hdpos
          obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
          have hadj : Gs.Adj ⟨v, hv⟩ w := (Gs.mem_neighborFinset ⟨v, hv⟩ w).mp hw
          have hwS : w.1 ∈ S := w.2
          have hwne : w.1 ≠ v := by
            intro heq
            have heq' : (⟨v, hv⟩ : {x // x ∈ (↑S : Set V)}) = w :=
              Subtype.ext heq.symm
            exact (Gs.ne_of_adj hadj) heq'
          have hvw : v ∈ S := hv
          have hcard : 2 ≤ S.card :=
            Finset.one_lt_card.mpr ⟨v, hvw, w.1, hwS, hwne.symm⟩
          omega
        have hzero : (edgesInside H S).card = 0 := by
          have hempty : edgesInside H S = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro e he
            have he' : e ∈ H.edgeFinset ∧ e.toFinset ⊆ S := by
              simpa [edgesInside] using he
            have hcard2 : e.toFinset.card = 2 :=
              Sym2.card_toFinset_of_not_isDiag e
                (H.not_isDiag_of_mem_edgeFinset he'.1)
            have hle : e.toFinset.card ≤ S.card := Finset.card_le_card he'.2
            omega
          rw [hempty]
          simp
        simp [potential, pruningPotential, hzero, hsingle]
        exact hmpos
      omega
    · have herase : (S.erase v).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem hv]
        have hScard : 0 < S.card := Finset.card_pos.mpr hS
        omega
      have hmaxerase := hSmax (S.erase v) (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, herase⟩)
      omega
  haveI : Nonempty {v // v ∈ (↑S : Set V)} := hS.to_subtype
  obtain ⟨v, hvmin⟩ := (H.induce (↑S : Set V)).exists_minimal_degree_vertex
  refine ⟨S, hS, ?_⟩
  have hvbound := hdegree v.1 v.2
  rw [← hvmin] at hvbound
  exact hvbound

/-- A nonbacktracking path of length three from a fixed root. -/
structure RadiusPath3 (G : SimpleGraph V) (u : V) where
  a : V
  b : V
  c : V
  edge₁ : G.Adj u a
  edge₂ : G.Adj a b
  edge₃ : G.Adj b c
  noBack₁ : u ≠ b
  noBack₂ : a ≠ c

theorem radiusPath3_endpoint_injective {G : SimpleGraph V} {u : V}
    (χ : G.Coloring (Fin 2)) (hfree4 : C4Free G) (hfree6 : C6Free G) :
    Function.Injective (fun p : RadiusPath3 G u => p.c) := by
  intro p q hpq
  cases p with
  | mk a b c e1 e2 e3 nb1 nb2 =>
    cases q with
    | mk a' b' c' f1 f2 f3 nb1' nb2' =>
      dsimp at hpq
      subst c'
      have hrootNeA : χ u ≠ χ a := χ.valid e1
      have hrootNeA' : χ u ≠ χ a' := χ.valid f1
      have hAneB : χ a ≠ χ b := χ.valid e2
      have hAneB' : χ a' ≠ χ b' := χ.valid f2
      have hBneC : χ b ≠ χ c := χ.valid e3
      have hBneC' : χ b' ≠ χ c := χ.valid f3
      have hrootEqB : χ u = χ b := by
        apply Fin.ext
        have h₁ : (χ u).val ≠ (χ a).val := fun h => hrootNeA (Fin.ext h)
        have h₂ : (χ a).val ≠ (χ b).val := fun h => hAneB (Fin.ext h)
        omega
      have hrootEqB' : χ u = χ b' := by
        apply Fin.ext
        have h₁ : (χ u).val ≠ (χ a').val := fun h => hrootNeA' (Fin.ext h)
        have h₂ : (χ a').val ≠ (χ b').val := fun h => hAneB' (Fin.ext h)
        omega
      have hrootNeC : χ u ≠ χ c := by
        intro h
        exact hBneC (hrootEqB.symm.trans h)
      by_cases haa : a = a'
      · subst a'
        by_cases hbb : b = b'
        · subst b'
          simp
        · have hle := commonNeighbors_card_le_one_of_C4Free hfree4 hbb
          have hma : a ∈ CommonNeighbors G b b' := by
            apply commonNeighbors_mem.mpr
            exact ⟨e2.symm, f2.symm⟩
          have hmc : c ∈ CommonNeighbors G b b' := by
            apply commonNeighbors_mem.mpr
            exact ⟨e3, f3⟩
          have heq : a = c := (Finset.card_le_one_iff.mp hle) hma hmc
          exact (nb2 heq).elim
      · by_cases hbb : b = b'
        · subst b'
          have hle := commonNeighbors_card_le_one_of_C4Free hfree4 nb1
          have hma : a ∈ CommonNeighbors G u b := by
            apply commonNeighbors_mem.mpr
            exact ⟨e1, e2.symm⟩
          have hma' : a' ∈ CommonNeighbors G u b := by
            apply commonNeighbors_mem.mpr
            exact ⟨f1, f2.symm⟩
          have heq : a = a' := (Finset.card_le_one_iff.mp hle) hma hma'
          exact (haa heq).elim
        · have hAu : a ≠ u := (G.ne_of_adj e1).symm
          have hA'u : a' ≠ u := (G.ne_of_adj f1).symm
          have hAB : a ≠ b := G.ne_of_adj e2
          have hBC : b ≠ c := G.ne_of_adj e3
          have hA'B' : a' ≠ b' := G.ne_of_adj f2
          have hB'C : b' ≠ c := G.ne_of_adj f3
          have hAb' : a ≠ b' := by
            intro h
            apply hrootNeA
            calc
              χ u = χ b' := hrootEqB'
              _ = χ a := congrArg χ h.symm
          have hBA' : b ≠ a' := by
            intro h
            apply hrootNeA'
            calc
              χ u = χ b := hrootEqB
              _ = χ a' := congrArg χ h
          have hcB' : c ≠ b' := by
            intro h
            apply hrootNeC
            calc
              χ u = χ b' := hrootEqB'
              _ = χ c := congrArg χ h.symm
          have hCu : c ≠ u := by
            intro h
            apply hrootNeC
            simpa [h]
          have hCa' : c ≠ a' := nb2'.symm
          have htail : [a, b, c, b', a', u].Nodup := by
            simp [List.nodup_cons, haa, hbb, nb1, nb1', nb2, hCa',
              hAu, hA'u, hAB, hBC, hA'B', hB'C, hAb', hBA', hcB',
              hCu, ne_comm]
          have hcycle := copy_cycleGraph_six_of_edges htail e1 e2 e3
            f3.symm f2.symm f1.symm
          exact (hfree6 hcycle).elim

set_option maxHeartbeats 800000 in
theorem radius_three_bound {G : SimpleGraph V} [DecidableRel G.Adj]
    (χ : G.Coloring (Fin 2)) (hfree4 : C4Free G) (hfree6 : C6Free G)
    (d : ℕ) (hd : 2 ≤ d) (hmin : ∀ v, d ≤ G.degree v) :
    G.maxDegree * (d - 1) ^ 2 ≤ Fintype.card V := by
  classical
  by_cases hV : IsEmpty V
  · haveI := hV
    simp [SimpleGraph.maxDegree]
  · letI : Nonempty V := not_isEmpty_iff.mp hV
    let Δ := G.maxDegree
    obtain ⟨root, hroot⟩ := G.exists_maximal_degree_vertex
    have hAcard : Δ ≤ (G.neighborFinset root).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact hroot.le
    let A := finsetSelection (G.neighborFinset root) Δ hAcard
    have hAadj (i : Fin Δ) : G.Adj root (A i) := by
      exact (G.mem_neighborFinset root (A i)).mp
        (finsetSelection_mem (G.neighborFinset root) Δ hAcard i)
    have hBcard (i : Fin Δ) : d - 1 ≤
        (otherNeighbors G (A i) root).card := by
      rw [card_otherNeighbors (hAadj i).symm]
      have := hmin (A i)
      omega
    let B (i : Fin Δ) : Fin (d - 1) → V :=
      finsetSelection (otherNeighbors G (A i) root) (d - 1) (hBcard i)
    have hBspec (i : Fin Δ) (j : Fin (d - 1)) :
        G.Adj (A i) (B i j) ∧ B i j ≠ root :=
      mem_otherNeighbors.mp
        (finsetSelection_mem (otherNeighbors G (A i) root) (d - 1) (hBcard i) j)
    have hCcard (i : Fin Δ) (j : Fin (d - 1)) : d - 1 ≤
        (otherNeighbors G (B i j) (A i)).card := by
      rw [card_otherNeighbors (hBspec i j).1.symm]
      have := hmin (B i j)
      omega
    let C (i : Fin Δ) (j : Fin (d - 1)) : Fin (d - 1) → V :=
      finsetSelection (otherNeighbors G (B i j) (A i)) (d - 1) (hCcard i j)
    have hCspec (i : Fin Δ) (j k : Fin (d - 1)) :
        G.Adj (B i j) (C i j k) ∧ C i j k ≠ A i :=
      mem_otherNeighbors.mp
        (finsetSelection_mem (otherNeighbors G (B i j) (A i)) (d - 1)
          (hCcard i j) k)
    let pathFn (z : Fin Δ × Fin (d - 1) × Fin (d - 1)) : RadiusPath3 G root := by
      let i := z.1
      let j := z.2.1
      let k := z.2.2
      exact ⟨A i, B i j, C i j k, hAadj i, (hBspec i j).1, (hCspec i j k).1,
        (hBspec i j).2.symm, (hCspec i j k).2.symm⟩
    have hinj : Function.Injective (fun z : Fin Δ × Fin (d - 1) × Fin (d - 1) =>
        (pathFn z).c) := by
      intro p q hpq
      have hpq' := radiusPath3_endpoint_injective χ hfree4 hfree6 hpq
      have hi : p.1 = q.1 := by
        apply finsetSelection_injective (G.neighborFinset root) Δ hAcard
        exact congrArg RadiusPath3.a hpq'
      have hj : p.2.1 = q.2.1 := by
        have hbeq : B p.1 p.2.1 = B q.1 q.2.1 := by
          simpa [pathFn] using congrArg RadiusPath3.b hpq'
        have hbeq' : B p.1 p.2.1 = B p.1 q.2.1 := by simpa [hi] using hbeq
        apply finsetSelection_injective (otherNeighbors G (A p.1) root)
          (d - 1) (hBcard p.1)
        exact hbeq'
      have hk : p.2.2 = q.2.2 := by
        have hceq : C p.1 p.2.1 p.2.2 = C q.1 q.2.1 q.2.2 := by
          simpa [pathFn] using congrArg RadiusPath3.c hpq'
        have hceq' : C p.1 p.2.1 p.2.2 = C p.1 p.2.1 q.2.2 := by
          simpa [hi, hj] using hceq
        apply finsetSelection_injective (otherNeighbors G (B p.1 p.2.1) (A p.1))
          (d - 1) (hCcard p.1 p.2.1)
        exact hceq'
      cases p with
      | mk i jk => cases jk with
        | mk j k => cases q with
          | mk i' jk' => cases jk' with
            | mk j' k' => simp_all
    have hcard := Fintype.card_le_of_injective
      (fun z : Fin Δ × Fin (d - 1) × Fin (d - 1) => (pathFn z).c) hinj
    simpa [Fintype.card_prod, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcard

set_option maxHeartbeats 800000 in
theorem item11_minimum_degree_reduction (G : SimpleGraph V) [DecidableRel G.Adj]
    (m n : ℕ) (hmpos : 0 < m) (hm : m ≤ G.edgeFinset.card)
    (hn : Fintype.card V ≤ n) (hfree4 : C4Free G) (hfree6 : C6Free G) :
    ∃ X T : Finset V, T.Nonempty ∧
      m ≤ 2 * n * (((cutGraph G X).induce (↑T : Set V)).minDegree) ∧
      ((cutGraph G X).induce (↑T : Set V)).IsBipartite ∧
      C4Free ((cutGraph G X).induce (↑T : Set V)) ∧
      C6Free ((cutGraph G X).induce (↑T : Set V)) ∧
      ((cutGraph G X).induce (↑T : Set V)).maxDegree *
        (((cutGraph G X).induce (↑T : Set V)).minDegree - 1) ^ 2 ≤ T.card ∧
      T.card ≤ n := by
  classical
  obtain ⟨X, hcut⟩ := maximumCut_exists G
  have hmcut : m ≤ 2 * (cutGraph G X).edgeFinset.card := by omega
  obtain ⟨T, hT, hmin⟩ := item9_minimum_degree (cutGraph G X) m n hmpos hmcut hn
  let B := (cutGraph G X).induce (↑T : Set V)
  have hbi : B.IsBipartite := by
    rcases cutGraph_bipartite G X with ⟨χ⟩
    exact ⟨Coloring.mk (fun v : {x // x ∈ (↑T : Set V)} => χ v.1)
      (by intro v w hadj; exact χ.valid hadj)⟩
  have hfreeB4 : C4Free B := by
    intro c
    apply hfree4
    rcases c with ⟨c⟩
    exact ⟨(SimpleGraph.Copy.ofLE (cutGraph G X) G (cutGraph_le G X)).comp
      ((SimpleGraph.Copy.induce (cutGraph G X) (↑T : Set V)).comp c)⟩
  have hfreeB6 : C6Free B := by
    intro c
    apply hfree6
    rcases c with ⟨c⟩
    exact ⟨(SimpleGraph.Copy.ofLE (cutGraph G X) G (cutGraph_le G X)).comp
      ((SimpleGraph.Copy.induce (cutGraph G X) (↑T : Set V)).comp c)⟩
  have hrad : B.maxDegree * (B.minDegree - 1) ^ 2 ≤ Fintype.card {x // x ∈ (↑T : Set V)} := by
    by_cases hd : 2 ≤ B.minDegree
    · rcases hbi with ⟨χ⟩
      exact radius_three_bound χ hfreeB4 hfreeB6 B.minDegree hd B.minDegree_le_degree
    · have hd' : B.minDegree ≤ 1 := by omega
      simp [Nat.sub_eq_zero_of_le hd']
  refine ⟨X, T, hT, ?_, hbi, ?_, ?_, ?_, ?_⟩
  · exact hmin
  · exact hfreeB4
  · exact hfreeB6
  · simpa [B] using hrad
  · calc
      T.card ≤ Fintype.card V := by simpa using (Finset.card_le_univ T)
      _ ≤ n := hn

end L575U

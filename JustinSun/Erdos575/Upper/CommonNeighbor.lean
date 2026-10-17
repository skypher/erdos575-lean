import JustinSun.Erdos575.Upper.Templates
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.BigOperators

/-! Common-neighbor notation and the local hypotheses for the short-cycle argument. -/

namespace L575U

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two vertices are related when they are distinct and have a common neighbor. -/
def Related (G : SimpleGraph V) (u v : V) : Prop :=
  u ≠ v ∧ ∃ w, G.Adj u w ∧ G.Adj v w

/-- The common-neighbor set of two vertices. -/
noncomputable def CommonNeighbors (G : SimpleGraph V) (u v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w

/-- A host graph has no four-cycle. -/
def C4Free (G : SimpleGraph V) : Prop := (SimpleGraph.cycleGraph 4).Free G

/-- A host graph has no six-cycle. -/
def C6Free (G : SimpleGraph V) : Prop := (SimpleGraph.cycleGraph 6).Free G

theorem related_symm {G : SimpleGraph V} {u v : V} (h : Related G u v) : Related G v u := by
  rcases h with ⟨hne, w, huw, hvw⟩
  exact ⟨hne.symm, w, hvw, huw⟩

theorem not_related_self {G : SimpleGraph V} (u : V) : ¬ Related G u u := by
  rintro ⟨hne, _⟩
  exact hne rfl

theorem commonNeighbors_mem {G : SimpleGraph V} {u v w : V} :
    w ∈ CommonNeighbors G u v ↔ G.Adj u w ∧ G.Adj v w := by
  simp [CommonNeighbors]

theorem related_iff_commonNeighbors_nonempty {G : SimpleGraph V} {u v : V} :
    Related G u v ↔ u ≠ v ∧ (CommonNeighbors G u v).Nonempty := by
  constructor
  · rintro ⟨hne, w, huw, hvw⟩
    exact ⟨hne, ⟨w, commonNeighbors_mem.mpr ⟨huw, hvw⟩⟩⟩
  · rintro ⟨hne, ⟨w, hw⟩⟩
    exact ⟨hne, w, (commonNeighbors_mem.mp hw).1, (commonNeighbors_mem.mp hw).2⟩

/-- The exact uniqueness statement used in the girth-eight common-neighbor argument. -/
def UniqueCommonNeighbor (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v →
    (CommonNeighbors G u v).card = 1

/-- The triangle conclusion used to define the centers of a base triple. -/
def RelatedTripleHasCommonNeighbor (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃a b c : V⦄, a ∈ S → b ∈ S → c ∈ S → a ≠ b → b ≠ c → a ≠ c →
    Related G a b → Related G b c → Related G a c →
      (CommonNeighbors G a b ∩ CommonNeighbors G b c ∩ CommonNeighbors G a c).Nonempty

/-- A cyclic chain on four distinct vertices is a four-cycle subgraph. -/
theorem copy_cycleGraph_four_of_edges {G : SimpleGraph V} {u a v b : V}
    (huv : u ≠ v) (hua : u ≠ a) (hub : u ≠ b)
    (hav : a ≠ v) (hab : a ≠ b) (hvb : v ≠ b)
    (hua_adj : G.Adj u a) (hav_adj : G.Adj a v)
    (hvb_adj : G.Adj v b) (hbu_adj : G.Adj b u) :
    SimpleGraph.cycleGraph 4 ⊑ G := by
  let p : G.Walk u u := Walk.cons hua_adj (Walk.cons hav_adj
    (Walk.cons hvb_adj (Walk.cons hbu_adj Walk.nil)))
  apply (SimpleGraph.cycleGraph_isContained_iff (by omega)).2
  refine ⟨u, p, ?_, ?_⟩
  · rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · rw [Walk.isPath_def]
      simp [p, List.nodup_cons, ne_comm, huv, hua, hub, hav, hab, hvb]
    · simp [p]
  · simp [p]

/-- In a graph without a four-cycle, distinct vertices have at most one common neighbor. -/
theorem commonNeighbors_card_le_one_of_C4Free {G : SimpleGraph V}
    (hfree : C4Free G) {u v : V} (huv : u ≠ v) :
    (CommonNeighbors G u v).card ≤ 1 := by
  classical
  by_contra hcard
  have hlarge : 1 < (CommonNeighbors G u v).card := by omega
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp hlarge
  have hua : u ≠ a := G.ne_of_adj (commonNeighbors_mem.mp ha).1
  have hub : u ≠ b := G.ne_of_adj (commonNeighbors_mem.mp hb).1
  have hav : a ≠ v := G.ne_of_adj (commonNeighbors_mem.mp ha).2.symm
  have hvb : v ≠ b := G.ne_of_adj (commonNeighbors_mem.mp hb).2
  have hcycle := copy_cycleGraph_four_of_edges huv hua hub hav hab hvb
    (commonNeighbors_mem.mp ha).1 (commonNeighbors_mem.mp ha).2.symm
    (commonNeighbors_mem.mp hb).2 (commonNeighbors_mem.mp hb).1.symm
  exact hfree hcycle

/-- A related pair in a four-cycle-free graph has exactly one common neighbor. -/
theorem commonNeighbors_card_eq_one_of_related {G : SimpleGraph V}
    (hfree : C4Free G) {u v : V} (hrel : Related G u v) :
    (CommonNeighbors G u v).card = 1 := by
  have hpos : 0 < (CommonNeighbors G u v).card := by
    rw [Finset.card_pos]
    exact (related_iff_commonNeighbors_nonempty.mp hrel).2
  have hle := commonNeighbors_card_le_one_of_C4Free hfree hrel.1
  omega

/-- Six distinct vertices joined in cyclic order give a six-cycle subgraph. -/
theorem copy_cycleGraph_six_of_edges {G : SimpleGraph V} {u a v b w c : V}
    (htail : [a, v, b, w, c, u].Nodup)
    (hua : G.Adj u a) (hav : G.Adj a v) (hvb : G.Adj v b)
    (hbw : G.Adj b w) (hwc : G.Adj w c) (hcu : G.Adj c u) :
    SimpleGraph.cycleGraph 6 ⊑ G := by
  let p : G.Walk u u := Walk.cons hua (Walk.cons hav (Walk.cons hvb
    (Walk.cons hbw (Walk.cons hwc (Walk.cons hcu Walk.nil)))))
  apply (SimpleGraph.cycleGraph_isContained_iff (by omega)).2
  refine ⟨u, p, ?_, ?_⟩
  · rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · rw [Walk.isPath_def]
      simpa [p] using htail
    · simp [p]
  · simp [p]

/-- A related triangle in one color class has a common neighbor when four- and six-cycles are absent. -/
theorem relatedTriple_has_commonNeighbor {G : SimpleGraph V} {S : Finset V}
    (χ : G.Coloring (Fin 2))
    (hside : ∀ x ∈ S, χ x = 0)
    (hfree4 : C4Free G) (hfree6 : C6Free G) :
    RelatedTripleHasCommonNeighbor G S := by
  classical
  intro a b c ha hb hc hab hbc hac habRel hbcRel hacRel
  obtain ⟨x, hxa, hxb⟩ := habRel.2
  obtain ⟨y, hyb, hyc⟩ := hbcRel.2
  obtain ⟨z, hza, hzc⟩ := hacRel.2
  have hmemABx : x ∈ CommonNeighbors G a b := commonNeighbors_mem.mpr ⟨hxa, hxb⟩
  have hxyOrxz : x = y ∨ x = z ∨ (x ≠ y ∧ x ≠ z) := by
    by_cases hxy : x = y
    · exact Or.inl hxy
    by_cases hxz : x = z
    · exact Or.inr (Or.inl hxz)
    · exact Or.inr (Or.inr ⟨hxy, hxz⟩)
  rcases hxyOrxz with hxy | hxz | ⟨hxy, hxz⟩
  · subst y
    refine ⟨x, ?_⟩
    simp only [Finset.mem_inter, commonNeighbors_mem]
    exact ⟨⟨⟨hxa, hxb⟩, ⟨hxb, hyc⟩⟩, ⟨hxa, hyc⟩⟩
  · subst z
    refine ⟨x, ?_⟩
    simp only [Finset.mem_inter, commonNeighbors_mem]
    exact ⟨⟨⟨hxa, hxb⟩, ⟨hxb, hzc⟩⟩, ⟨hxa, hzc⟩⟩
  · have hyz : y ≠ z := by
      intro hyz
      subst z
      have hmemABy : y ∈ CommonNeighbors G a b :=
        commonNeighbors_mem.mpr ⟨hza, hyb⟩
      have hxyEq := (Finset.card_le_one_iff.mp
        (commonNeighbors_card_le_one_of_C4Free hfree4 hab)) hmemABx hmemABy
      exact hxy hxyEq
    have hxaSide := hside a ha
    have hxbSide := hside b hb
    have hxcSide := hside c hc
    have hχx : χ x = 1 := Fin.eq_one_of_ne_zero (χ x) (by
      intro hx0
      exact (χ.valid hxa) (hxaSide.trans hx0.symm))
    have hχy : χ y = 1 := Fin.eq_one_of_ne_zero (χ y) (by
      intro hy0
      exact (χ.valid hyb) (hxbSide.trans hy0.symm))
    have hχz : χ z = 1 := Fin.eq_one_of_ne_zero (χ z) (by
      intro hz0
      exact (χ.valid hza) (hxaSide.trans hz0.symm))
    have hcross : ∀ p ∈ ({a, b, c} : Finset V), ∀ q ∈ ({x, y, z} : Finset V), p ≠ q := by
      intro p hp q hq hEq
      have hpS : p ∈ S := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with hp | hp | hp
        · rw [hp]; exact ha
        · rw [hp]; exact hb
        · rw [hp]; exact hc
      have hpside : χ p = 0 := hside p hpS
      have hqColor : χ q = 1 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with hq | hq | hq
        · simpa [hq] using hχx
        · simpa [hq] using hχy
        · simpa [hq] using hχz
      rw [← hEq] at hqColor
      rw [hpside] at hqColor
      norm_num at hqColor
    have htail : [b, y, c, z, a, x].Nodup := by
      simp [List.nodup_cons, ne_comm, hcross, hab, hbc, hac, hyz, hxy, hxz]
    have hcycle := copy_cycleGraph_six_of_edges htail
      hxb.symm hyb hyc.symm hzc hza.symm hxa
    exact (hfree6 hcycle).elim

/-- Related vertices lie in the same color class of a bipartition. -/
theorem related_color_eq {G : SimpleGraph V} (χ : G.Coloring (Fin 2))
    {u v : V} (h : Related G u v) : χ u = χ v := by
  obtain ⟨_, w, huw, hvw⟩ := h
  have h₁ := χ.valid huw
  have h₂ := χ.valid hvw
  have h₁' : (χ u).val ≠ (χ w).val := fun hh => h₁ (Fin.ext hh)
  have h₂' : (χ v).val ≠ (χ w).val := fun hh => h₂ (Fin.ext hh)
  apply Fin.ext
  omega

/-- The vertices of the zero color class. -/
noncomputable def SideZero {G : SimpleGraph V} (χ : G.Coloring (Fin 2)) : Finset V :=
  Finset.univ.filter fun x => χ x = 0

/-- Vertices related to both endpoints, used as the set `Z_uv`. -/
noncomputable def ZSet (G : SimpleGraph V) (u v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun w => Related G u w ∧ Related G v w

theorem mem_sideZero {G : SimpleGraph V} {χ : G.Coloring (Fin 2)} {x : V} :
    x ∈ SideZero χ ↔ χ x = 0 := by
  simp [SideZero]

theorem mem_zSet {G : SimpleGraph V} {u v w : V} :
    w ∈ ZSet G u v ↔ Related G u w ∧ Related G v w := by
  simp [ZSet]

/-- A common-neighbor pair set `Z_uv` is independent in the relatedness graph. -/
theorem zSet_independent {G : SimpleGraph V} (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G) {u v : V}
    (huColor : χ u = 0) (huv : u ≠ v) (hnot : ¬ Related G u v) :
    ∀ ⦃w w' : V⦄, w ∈ ZSet G u v → w' ∈ ZSet G u v → w ≠ w' →
      ¬ Related G w w' := by
  classical
  intro w w' hw hw' hww' hrel
  rcases mem_zSet.mp hw with ⟨huw, hvw⟩
  rcases mem_zSet.mp hw' with ⟨huw', hvw'⟩
  have hwColor : χ w = 0 := (related_color_eq χ huw).symm.trans huColor
  have hw'Color : χ w' = 0 := (related_color_eq χ huw').symm.trans huColor
  have hvColor : χ v = 0 := (related_color_eq χ hvw).trans hwColor
  let S := SideZero χ
  have huS : u ∈ S := mem_sideZero.mpr huColor
  have hvS : v ∈ S := mem_sideZero.mpr hvColor
  have hwS : w ∈ S := mem_sideZero.mpr hwColor
  have hw'S : w' ∈ S := mem_sideZero.mpr hw'Color
  have hside : ∀ x ∈ S, χ x = 0 := by
    intro x hx
    exact mem_sideZero.mp hx
  have htri := relatedTriple_has_commonNeighbor χ hside hfree4 hfree6
  have hα := htri huS hwS hw'S huw.1 hww' huw'.1 huw hrel huw'
  have hβ := htri hvS hwS hw'S hvw.1 hww' hvw'.1 hvw hrel hvw'
  obtain ⟨α, hα⟩ := hα
  obtain ⟨β, hβ⟩ := hβ
  have hαww' : α ∈ CommonNeighbors G w w' := by
    have := hα
    simp only [Finset.mem_inter, commonNeighbors_mem] at this
    exact commonNeighbors_mem.mpr this.1.2
  have hβww' : β ∈ CommonNeighbors G w w' := by
    have := hβ
    simp only [Finset.mem_inter, commonNeighbors_mem] at this
    exact commonNeighbors_mem.mpr this.1.2
  have hαβ := (Finset.card_le_one_iff.mp
    (commonNeighbors_card_le_one_of_C4Free hfree4 hrel.1)) hαww' hβww'
  have hαu : G.Adj u α := by
    have := hα
    simp only [Finset.mem_inter, commonNeighbors_mem] at this
    exact this.1.1.1
  have hβv : G.Adj v β := by
    have := hβ
    simp only [Finset.mem_inter, commonNeighbors_mem] at this
    exact this.1.1.1
  exact hnot ⟨huv, α, hαu, hαβ ▸ hβv⟩

/-- Two common centers of an unrelated pair cannot be related to each other. -/
theorem two_centers_not_related {G : SimpleGraph V} (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G) {a b u v : V}
    (haColor : χ a = 0) (hbColor : χ b = 0)
    (huColor : χ u = 0) (hvColor : χ v = 0)
    (hab : a ≠ b) (huv : u ≠ v) (hnotAB : ¬ Related G a b)
    (hua : Related G u a) (hub : Related G u b)
    (hva : Related G v a) (hvb : Related G v b) :
    ¬ Related G u v := by
  intro huvRel
  let S := SideZero χ
  have hside : ∀ x ∈ S, χ x = 0 := fun x hx => mem_sideZero.mp hx
  have htri := relatedTriple_has_commonNeighbor χ hside hfree4 hfree6
  have huS : u ∈ S := mem_sideZero.mpr huColor
  have hvS : v ∈ S := mem_sideZero.mpr hvColor
  have haS : a ∈ S := mem_sideZero.mpr haColor
  have hbS : b ∈ S := mem_sideZero.mpr hbColor
  have hα := htri huS hvS haS huvRel.1 hva.1 hua.1 huvRel hva hua
  have hβ := htri huS hvS hbS huvRel.1 hvb.1 hub.1 huvRel hvb hub
  obtain ⟨α, hα⟩ := hα
  obtain ⟨β, hβ⟩ := hβ
  have hαuv : α ∈ CommonNeighbors G u v := by
    have h := hα
    simp only [Finset.mem_inter, commonNeighbors_mem] at h
    exact commonNeighbors_mem.mpr h.1.1
  have hβuv : β ∈ CommonNeighbors G u v := by
    have h := hβ
    simp only [Finset.mem_inter, commonNeighbors_mem] at h
    exact commonNeighbors_mem.mpr h.1.1
  have hαβ := (Finset.card_le_one_iff.mp
    (commonNeighbors_card_le_one_of_C4Free hfree4 huvRel.1)) hαuv hβuv
  have hαa : G.Adj a α := by
    have h := hα
    simp only [Finset.mem_inter, commonNeighbors_mem] at h
    exact h.2.2
  have hβb : G.Adj b β := by
    have h := hβ
    simp only [Finset.mem_inter, commonNeighbors_mem] at h
    exact h.2.2
  exact hnotAB ⟨hab, α, hαa, hαβ ▸ hβb⟩

/-- Centers of an independent base triple are disjoint from the bases and independent. -/
theorem triple_centers_independent {G : SimpleGraph V} (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G) {a b c : V}
    (haColor : χ a = 0) (hbColor : χ b = 0) (hcColor : χ c = 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habNot : ¬ Related G a b) (hacNot : ¬ Related G a c)
    (hbcNot : ¬ Related G b c) :
    (∀ u, Related G u a → Related G u b → Related G u c →
        u ≠ a ∧ u ≠ b ∧ u ≠ c) ∧
      (∀ ⦃u v⦄, Related G u a → Related G u b → Related G u c →
        Related G v a → Related G v b → Related G v c → u ≠ v →
        ¬ Related G u v) := by
  constructor
  · intro u hua hub huc
    refine ⟨?_, ?_, ?_⟩
    · intro h; subst u; exact not_related_self (G := G) a hua
    · intro h; subst u; exact not_related_self (G := G) b hub
    · intro h; subst u; exact not_related_self (G := G) c huc
  · intro u v hua hub huc hva hvb hvc huv hrel
    have huColor : χ u = 0 := (related_color_eq (G := G) χ hua).trans haColor
    have hvColor : χ v = 0 := (related_color_eq (G := G) χ hva).trans haColor
    exact two_centers_not_related (G := G) χ hfree4 hfree6 haColor hbColor
      huColor hvColor hab huv habNot hua hub hva hvb hrel

/-- A related pair supplies a subdivision vertex. -/
noncomputable def relatedWitness {G : SimpleGraph V} {u v : V}
    (h : Related G u v) : V := Classical.choose h.2

theorem relatedWitness_spec {G : SimpleGraph V} {u v : V} (h : Related G u v) :
    G.Adj u (relatedWitness h) ∧ G.Adj v (relatedWitness h) :=
  Classical.choose_spec h.2

/-- The forced subdivision vertices for distinct base-center pairs are distinct. -/
theorem pairWitnesses_injective {G : SimpleGraph V} {k : ℕ}
    (base : Fin 3 → V) (center : Fin k → V)
    (hbaseInj : Function.Injective base) (hcenterInj : Function.Injective center)
    (hbase : ∀ i i', i ≠ i' → ¬ Related G (base i) (base i'))
    (hcenter : ∀ j j', j ≠ j' → ¬ Related G (center j) (center j'))
    (hrel : ∀ i j, Related G (base i) (center j)) :
    Function.Injective (fun p : Fin 3 × Fin k =>
      relatedWitness (hrel p.1 p.2)) := by
  classical
  intro p q hpq
  rcases p with ⟨i, j⟩
  rcases q with ⟨i', j'⟩
  have hw : relatedWitness (hrel i j) = relatedWitness (hrel i' j') := hpq
  simp only [Prod.mk.injEq]
  have hi : i = i' ∨ i ≠ i' := em (i = i')
  have hj : j = j' ∨ j ≠ j' := em (j = j')
  rcases hi with rfl | hii
  · rcases hj with rfl | hjj
    · exact ⟨rfl, rfl⟩
    · have hs := relatedWitness_spec (hrel i j)
      have hs' := relatedWitness_spec (hrel i j')
      have hccne : center j ≠ center j' := fun heq => hjj (hcenterInj heq)
      have hadj : G.Adj (center j) (relatedWitness (hrel i j')) := by
        rw [← hw]
        exact hs.2
      have hcc : Related G (center j) (center j') :=
        ⟨hccne, relatedWitness (hrel i j'), hadj, hs'.2⟩
      exact (hcenter j j' hjj hcc).elim
  · rcases hj with rfl | hjj
    · have hs := relatedWitness_spec (hrel i j)
      have hs' := relatedWitness_spec (hrel i' j)
      have hbne : base i ≠ base i' := fun heq => hii (hbaseInj heq)
      have hadj : G.Adj (base i) (relatedWitness (hrel i' j)) := by
        rw [← hw]
        exact hs.1
      have hbb : Related G (base i) (base i') :=
        ⟨hbne, relatedWitness (hrel i' j), hadj, hs'.1⟩
      exact (hbase i i' hii hbb).elim
    · have hs := relatedWitness_spec (hrel i j)
      have hs' := relatedWitness_spec (hrel i' j')
      have hbne : base i ≠ base i' := fun heq => hii (hbaseInj heq)
      have hadj : G.Adj (base i) (relatedWitness (hrel i' j')) := by
        rw [← hw]
        exact hs.1
      have hbb : Related G (base i) (base i') :=
        ⟨hbne, relatedWitness (hrel i' j'), hadj, hs'.1⟩
      exact (hbase i i' hii hbb).elim

/-- Independent bases and centers with all cross pairs related contain the subdivision graph. -/
noncomputable def subdivision_copy_of_related_triples {G : SimpleGraph V} {k : ℕ}
    (χ : G.Coloring (Fin 2)) (base : Fin 3 → V) (center : Fin k → V)
    (hbInj : Function.Injective base) (hcInj : Function.Injective center)
    (hbaseColor : ∀ i, χ (base i) = 0) (hcenterColor : ∀ j, χ (center j) = 0)
    (hbase : ∀ i i', i ≠ i' → ¬ Related G (base i) (base i'))
    (hcenter : ∀ j j', j ≠ j' → ¬ Related G (center j) (center j'))
    (hrel : ∀ i j, Related G (base i) (center j)) :
    SimpleGraph.Copy (SGraph k) G := by
  classical
  let f : SVert k → V
    | .base i => base i
    | .center j => center j
    | .sub i j => relatedWitness (hrel i j)
  have hsubInj : Function.Injective (fun p : Fin 3 × Fin k =>
      relatedWitness (hrel p.1 p.2)) := pairWitnesses_injective base center hbInj hcInj
        hbase hcenter hrel
  have hsubColor : ∀ i j, χ (relatedWitness (hrel i j)) = 1 := by
    intro i j
    have hv := (relatedWitness_spec (hrel i j)).1
    have hne : χ (relatedWitness (hrel i j)) ≠ 0 := by
      intro heq
      exact (χ.valid hv) (by rw [hbaseColor i, heq])
    exact Fin.eq_one_of_ne_zero _ hne
  refine { toHom := { toFun := f, map_rel' := ?_ }, injective' := ?_ }
  · intro x y hxy
    change sAdj x y at hxy
    rcases hxy with ⟨i, j, rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩ |
        ⟨i, j, rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩
    · exact (relatedWitness_spec (hrel i j)).1
    · exact (relatedWitness_spec (hrel i j)).1.symm
    · exact (relatedWitness_spec (hrel i j)).2
    · exact (relatedWitness_spec (hrel i j)).2.symm
  · intro x y hxy
    change f x = f y at hxy
    cases x with
    | base i => cases y with
      | base i' =>
        simp only [f] at hxy
        exact congrArg SVert.base (hbInj hxy)
      | center j =>
        simp only [f] at hxy
        exact False.elim ((hrel i j).1 hxy)
      | sub i' j =>
        simp only [f] at hxy
        have hcol := hbaseColor i
        have hsubcol := hsubColor i' j
        rw [hxy] at hcol
        rw [hcol] at hsubcol
        exact False.elim (by norm_num at hsubcol)
    | center j => cases y with
      | base i =>
        simp only [f] at hxy
        exact False.elim ((hrel i j).1 hxy.symm)
      | center j' =>
        simp only [f] at hxy
        exact congrArg SVert.center (hcInj hxy)
      | sub i j' =>
        simp only [f] at hxy
        have hcol := hcenterColor j
        have hsubcol := hsubColor i j'
        rw [hxy] at hcol
        rw [hcol] at hsubcol
        exact False.elim (by norm_num at hsubcol)
    | sub i j => cases y with
      | base i' =>
        simp only [f] at hxy
        have hcol := hbaseColor i'
        have hsubcol := hsubColor i j
        rw [← hxy] at hcol
        rw [hcol] at hsubcol
        exact False.elim (by norm_num at hsubcol)
      | center j' =>
        simp only [f] at hxy
        have hcol := hcenterColor j'
        have hsubcol := hsubColor i j
        rw [← hxy] at hcol
        rw [hcol] at hsubcol
        exact False.elim (by norm_num at hsubcol)
      | sub i' j' =>
        simp only [f] at hxy
        have hp : (i, j) = (i', j') := hsubInj hxy
        cases hp
        rfl

/-- A specified independent base triple and its common independent centers give S_k. -/
noncomputable def subdivision_copy_of_independent_triple {G : SimpleGraph V} {k : ℕ}
    (χ : G.Coloring (Fin 2)) (base : Fin 3 → V) (center : Fin k → V)
    (hfree4 : C4Free G) (hfree6 : C6Free G)
    (hbInj : Function.Injective base) (hcInj : Function.Injective center)
    (hbaseColor : ∀ i, χ (base i) = 0) (hcenterColor : ∀ j, χ (center j) = 0)
    (hbase : ∀ i i', i ≠ i' → ¬ Related G (base i) (base i'))
    (hrel : ∀ i j, Related G (base i) (center j)) :
    SimpleGraph.Copy (SGraph k) G := by
  have hcenters : ∀ j j', j ≠ j' → ¬ Related G (center j) (center j') := by
    intro j j' hj hrelJJ
    let i₀ : Fin 3 := ⟨0, by omega⟩
    let i₁ : Fin 3 := ⟨1, by omega⟩
    have hi : i₀ ≠ i₁ := by decide
    have hab : base i₀ ≠ base i₁ := fun heq => hi (hbInj heq)
    have hjv : center j ≠ center j' := fun heq => hj (hcInj heq)
    exact two_centers_not_related (G := G) χ hfree4 hfree6
      (hbaseColor i₀) (hbaseColor i₁) (hcenterColor j) (hcenterColor j')
      hab hjv (hbase i₀ i₁ hi)
      (related_symm (hrel i₀ j)) (related_symm (hrel i₁ j))
      (related_symm (hrel i₀ j')) (related_symm (hrel i₁ j')) hrelJJ
  exact subdivision_copy_of_related_triples χ base center hbInj hcInj
    hbaseColor hcenterColor hbase hcenters hrel

/-- Vertices related to each member of a specified base triple. -/
noncomputable def TripleCenterCandidates {G : SimpleGraph V}
    (base : Fin 3 → V) : Finset V := by
  classical
  exact Finset.univ.filter fun u => ∀ i, Related G (base i) u

theorem mem_tripleCenterCandidates {G : SimpleGraph V} {base : Fin 3 → V} {u : V} :
    u ∈ TripleCenterCandidates (G := G) base ↔ ∀ i, Related G (base i) u := by
  simp [TripleCenterCandidates]

/-- The center-count criterion yields an actual subdivision copy. -/
theorem subdivision_copy_of_center_count {G : SimpleGraph V} {k : ℕ}
    (χ : G.Coloring (Fin 2)) (base : Fin 3 → V)
    (hfree4 : C4Free G) (hfree6 : C6Free G)
    (hbInj : Function.Injective base)
    (hbaseColor : ∀ i, χ (base i) = 0)
    (hbase : ∀ i i', i ≠ i' → ¬ Related G (base i) (base i'))
    (hcard : k ≤ (TripleCenterCandidates (G := G) base).card) :
    ∃ copy : SimpleGraph.Copy (SGraph k) G, ∀ j,
      (copy.toHom (.center j)) ∈ TripleCenterCandidates (G := G) base := by
  classical
  obtain ⟨s, hs, hscard⟩ := Finset.exists_subset_card_eq
    (s := TripleCenterCandidates (G := G) base) hcard
  let e : s ≃ Fin k := Finset.equivFinOfCardEq hscard
  let center : Fin k → V := fun j => (e.symm j).val
  have hcInj : Function.Injective center := by
    intro j j' h
    have he : e.symm j = e.symm j' := Subtype.ext h
    have hfin := congrArg e he
    simpa using hfin
  have hrel : ∀ i j, Related G (base i) (center j) := by
    intro i j
    exact (mem_tripleCenterCandidates.mp (hs (e.symm j).property)) i
  have hcenterColor : ∀ j, χ (center j) = 0 := by
    intro j
    exact (related_color_eq (G := G) χ (hrel 0 j)).symm.trans (hbaseColor 0)
  have hcenter : ∀ j j', j ≠ j' → ¬ Related G (center j) (center j') := by
    intro j j' hj hrelJJ
    have hi : (0 : Fin 3) ≠ 1 := by decide
    have hab : base 0 ≠ base 1 := fun heq => hi (hbInj heq)
    have hjv : center j ≠ center j' := fun heq => hj (hcInj heq)
    exact two_centers_not_related (G := G) χ hfree4 hfree6
      (hbaseColor 0) (hbaseColor 1) (hcenterColor j) (hcenterColor j')
      hab hjv (hbase 0 1 hi)
      (related_symm (hrel 0 j)) (related_symm (hrel 1 j))
      (related_symm (hrel 0 j')) (related_symm (hrel 1 j')) hrelJJ
  let copy := subdivision_copy_of_related_triples χ base center hbInj hcInj
    hbaseColor hcenterColor hbase hcenter hrel
  refine ⟨copy, ?_⟩
  intro j
  exact hs (e.symm j).property

/-- A specified common center can be included in a three-center subdivision copy. -/
theorem subdivision_copy_of_center_mem {G : SimpleGraph V}
    (χ : G.Coloring (Fin 2)) (base : Fin 3 → V)
    (hfree4 : C4Free G) (hfree6 : C6Free G)
    (hbInj : Function.Injective base)
    (hbaseColor : ∀ i, χ (base i) = 0)
    (hbase : ∀ i i', i ≠ i' → ¬ Related G (base i) (base i'))
    {u : V} (hu : u ∈ TripleCenterCandidates (G := G) base)
    (hcard : 3 ≤ (TripleCenterCandidates (G := G) base).card) :
    ∃ copy : SimpleGraph.Copy (SGraph 3) G, copy.toHom (.center 0) = u := by
  classical
  let C := TripleCenterCandidates (G := G) base
  have hErase : 2 ≤ (C.erase u).card := by
    have hcardErase := Finset.card_erase_of_mem hu
    dsimp [C] at hcardErase ⊢
    omega
  obtain ⟨s, hs, hscard⟩ := Finset.exists_subset_card_eq (s := C.erase u) hErase
  let e : s ≃ Fin 2 := Finset.equivFinOfCardEq hscard
  let center : Fin 3 → V := fun j =>
    if j.val = 0 then u else if j.val = 1 then (e.symm 0).val else (e.symm 1).val
  have hnotu0 : (e.symm 0).val ≠ u := by
    have he := Finset.mem_erase.mp (hs (e.symm 0).property)
    exact he.1
  have hnotu1 : (e.symm 1).val ≠ u := by
    have he := Finset.mem_erase.mp (hs (e.symm 1).property)
    exact he.1
  have h01 : (e.symm 0).val ≠ (e.symm 1).val := by
    intro heq
    have he : e.symm 0 = e.symm 1 := Subtype.ext heq
    have hfin := congrArg e he
    norm_num at hfin
  have hcInj : Function.Injective center := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [center, hnotu0, hnotu1, h01]
  have hcenterMem : ∀ j, center j ∈ C := by
    intro j
    fin_cases j
    · exact hu
    · exact (Finset.mem_erase.mp (hs (e.symm 0).property)).2
    · exact (Finset.mem_erase.mp (hs (e.symm 1).property)).2
  have hcenterColor : ∀ j, χ (center j) = 0 := by
    intro j
    have hj := mem_tripleCenterCandidates.mp (hcenterMem j)
    exact (related_color_eq χ (hj 0)).symm.trans (hbaseColor 0)
  have hrel : ∀ i j, Related G (base i) (center j) := by
    intro i j
    exact (mem_tripleCenterCandidates.mp (hcenterMem j)) i
  refine ⟨subdivision_copy_of_independent_triple χ base center hfree4 hfree6
    hbInj hcInj hbaseColor hcenterColor hbase hrel, ?_⟩
  simp [subdivision_copy_of_independent_triple,
    subdivision_copy_of_related_triples, center]

/-- A copy with at least one center has an independent set of bases. -/
theorem subdivision_copy_base_independent {G : SimpleGraph V} {k : ℕ}
    (χ : G.Coloring (Fin 2)) (hfree4 : C4Free G) (hfree6 : C6Free G)
    (hk : 0 < k) (copy : SimpleGraph.Copy (SGraph k) G) :
    ∀ i i', i ≠ i' →
      ¬ Related G (copy.toHom (.base i)) (copy.toHom (.base i')) := by
  classical
  intro i i' hii hrel
  let j : Fin k := ⟨0, by omega⟩
  let a := copy.toHom (.base i)
  let b := copy.toHom (.base i')
  let p := copy.toHom (.sub i j)
  let q := copy.toHom (.sub i' j)
  let c := copy.toHom (.center j)
  obtain ⟨w, haw, hbw⟩ := hrel.2
  have injNe {x y : SVert k} (hxy : x ≠ y) : copy.toHom x ≠ copy.toHom y :=
    fun heq => hxy (copy.injective' heq)
  have hab : a ≠ b := injNe (by simp [a, b, hii])
  have hbp : b ≠ p := injNe (by simp [b, p])
  have hbc : b ≠ c := injNe (by simp [b, c])
  have hcp : c ≠ p := injNe (by simp [c, p])
  have hca : c ≠ a := injNe (by simp [c, a])
  have hqa : q ≠ a := injNe (by simp [q, a])
  have hap : a ≠ p := injNe (by simp [a, p])
  have hcb : c ≠ b := hbc.symm
  have hqcb : q ≠ c := injNe (by simp [q, c])
  have hqb : q ≠ b := injNe (by simp [q, b])
  have hqp : q ≠ p := injNe (by simp [q, p, hii, ne_comm])
  have hba : b ≠ a := hab.symm
  have hadjP : G.Adj a p := by
    apply copy.toHom.map_rel
    simp [SGraph, sAdj, a, p]
  have hadjQ : G.Adj b q := by
    apply copy.toHom.map_rel
    simp [SGraph, sAdj, b, q]
  have hqC : G.Adj q c := by
    apply copy.toHom.map_rel
    simp [SGraph, sAdj, q, c]
  have hcP : G.Adj c p := by
    apply copy.toHom.map_rel
    simp [SGraph, sAdj, c, p]
  have hColorAC : χ a = χ c := by
    have hrelAC : Related G a c := ⟨hca.symm, p, hadjP, hcP⟩
    exact related_color_eq χ hrelAC
  have hColorAB : χ a = χ b := related_color_eq χ hrel
  have hwc : w ≠ c := by
    intro heq
    have hneColor : χ a ≠ χ w := by
      intro he
      exact (χ.valid haw) he
    apply hneColor
    rw [heq]
    exact hColorAC
  have hwp : w ≠ p := by
    intro heq
    subst w
    have hfour := copy_cycleGraph_four_of_edges hbc hqb.symm hbp hqcb hqp hcp
      hadjQ hqC hcP hbw.symm
    exact hfree4 hfour
  have hwq : w ≠ q := by
    intro heq
    subst w
    have hfour := copy_cycleGraph_four_of_edges hca.symm hap hqa.symm
      hcp.symm hqp.symm hqcb.symm hadjP hcP.symm hqC.symm haw.symm
    exact hfree4 hfour
  have hwb : w ≠ b := (G.ne_of_adj hbw).symm
  have hwa : w ≠ a := (G.ne_of_adj haw).symm
  have hbq : b ≠ q := G.ne_of_adj hadjQ
  have hTail : [w, b, q, c, p, a].Nodup := by
    simp [List.nodup_cons, hab, hbp, hbc, hcp, hap, hwp, hwq, hwc,
      hwb, hwa, hbq, ne_comm, hqcb, hqb, hqp, hca, hba, hqa, hcb]
  have hcycle := copy_cycleGraph_six_of_edges hTail haw hbw.symm hadjQ hqC hcP hadjP.symm
  exact hfree6 hcycle

/-- A subdivision copy gives independent bases and at least k common centers. -/
theorem subdivision_copy_converse {G : SimpleGraph V} {k : ℕ}
    (χ : G.Coloring (Fin 2)) (hfree4 : C4Free G) (hfree6 : C6Free G)
    (hk : 0 < k) (copy : SimpleGraph.Copy (SGraph k) G) :
    (∀ i i', i ≠ i' →
      ¬ Related G (copy.toHom (.base i)) (copy.toHom (.base i'))) ∧
    k ≤ (TripleCenterCandidates (G := G) (fun i => copy.toHom (.base i))).card := by
  refine ⟨subdivision_copy_base_independent χ hfree4 hfree6 hk copy, ?_⟩
  classical
  let base : Fin 3 → V := fun i => copy.toHom (.base i)
  let center : Fin k → V := fun j => copy.toHom (.center j)
  change k ≤ (TripleCenterCandidates (G := G) base).card
  have hcenterInj : Function.Injective center := by
    intro j j' hj
    have hdom := copy.injective' hj
    injection hdom
  have hmem : ∀ j, center j ∈ TripleCenterCandidates (G := G) base := by
    intro j
    apply mem_tripleCenterCandidates.mpr
    intro i
    have hne : base i ≠ center j := by
      intro heq
      have hdom := copy.injective' heq
      cases hdom
    have hleft : G.Adj (base i) (copy.toHom (.sub i j)) := by
      apply copy.toHom.map_rel
      simp [SGraph, sAdj]
    have hright : G.Adj (center j) (copy.toHom (.sub i j)) := by
      apply copy.toHom.map_rel
      simp [SGraph, sAdj]
    exact ⟨hne, copy.toHom (.sub i j), hleft, hright⟩
  let g : Fin k → {v // v ∈ TripleCenterCandidates (G := G) base} :=
    fun j => ⟨center j, hmem j⟩
  have hg : Function.Injective g := by
    intro j j' h
    exact hcenterInj (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective g hg
  simpa [g] using hcard

/-- Nonbacktracking four-edge walks have distinct, unrelated endpoints. -/
theorem fourEdgeWalk_endpoints_unrelated {G : SimpleGraph V}
    (χ : G.Coloring (Fin 2)) (hfree4 : C4Free G) (hfree6 : C6Free G)
    {u a w b v : V}
    (h₁ : G.Adj u a) (h₂ : G.Adj a w) (h₃ : G.Adj w b) (h₄ : G.Adj b v)
    (huw : u ≠ w) (hab : a ≠ b) (hwv : w ≠ v) :
    v ≠ u ∧ ¬ Related G u v := by
  have hvu : v ≠ u := by
    intro hvu
    subst v
    have hcycle := copy_cycleGraph_four_of_edges huw (G.ne_of_adj h₁)
      (G.ne_of_adj h₄).symm (G.ne_of_adj h₂) hab (G.ne_of_adj h₃)
      h₁ h₂ h₃ h₄
    exact hfree4 hcycle
  have hColorUW : χ u = χ w := by
    have hrelUW : Related G u w := ⟨huw, a, h₁, h₂.symm⟩
    exact related_color_eq χ hrelUW
  have hColorWV : χ w = χ v := by
    have hrelWV : Related G w v := ⟨hwv, b, h₃, h₄.symm⟩
    exact related_color_eq χ hrelWV
  have hColorUV : χ u = χ v := hColorUW.trans hColorWV
  have hColorAUV : χ a ≠ χ u := (χ.valid h₁).symm
  refine ⟨hvu, ?_⟩
  intro hrelUV
  obtain ⟨z, huz, hvz⟩ := hrelUV.2
  have hza : z ≠ a := by
    intro hEq
    subst z
    have hva : v ≠ a := by
      intro heq
      apply hColorAUV
      exact (congrArg χ heq.symm).trans hColorUV.symm
    have hcycle := copy_cycleGraph_four_of_edges hwv (G.ne_of_adj h₃)
      (G.ne_of_adj h₂).symm (G.ne_of_adj h₄) hab.symm hva
      h₃ h₄ hvz h₂
    exact hfree4 hcycle
  have hzb : z ≠ b := by
    intro hEq
    subst z
    have hcycle := copy_cycleGraph_four_of_edges huw.symm (G.ne_of_adj h₂).symm
      (G.ne_of_adj h₃) (G.ne_of_adj h₁).symm hab (G.ne_of_adj huz)
      h₂.symm h₁.symm huz h₃.symm
    exact hfree4 hcycle
  have hColorAB : χ a = χ b := by
    apply Fin.ext
    have h₁' := χ.valid h₁
    have h₃' := χ.valid h₃
    have h₃'' : χ w ≠ χ b := h₃'
    rw [← hColorUW] at h₃''
    omega
  have hColorAZ : χ a = χ z := by
    apply Fin.ext
    have h₁' := χ.valid h₁
    have hz' := χ.valid huz
    omega
  have hColorBZ : χ b = χ z := hColorAB.symm.trans hColorAZ
  have hColorBUV : χ b ≠ χ u := by
    have hb : χ b ≠ χ w := (χ.valid h₃).symm
    rw [hColorUW]
    exact hb
  have hColorZUV : χ z ≠ χ u := (χ.valid huz).symm
  have hva : a ≠ v := by
    intro heq
    exact hColorAUV ((congrArg χ heq).trans hColorUV.symm)
  have hbu : b ≠ u := by
    intro heq
    exact hColorBUV (congrArg χ heq)
  have hzw : z ≠ w := by
    intro heq
    apply hColorZUV
    calc
      χ z = χ w := congrArg χ heq
      _ = χ u := hColorUW.symm
  have haw : a ≠ w := G.ne_of_adj h₂
  have hbw : b ≠ w := (G.ne_of_adj h₃).symm
  have hbu' : b ≠ v := G.ne_of_adj h₄
  have hzu : z ≠ u := (G.ne_of_adj huz).symm
  have hzv : z ≠ v := (G.ne_of_adj hvz).symm
  have hau : a ≠ u := (G.ne_of_adj h₁).symm
  have hwu : w ≠ u := huw.symm
  have hvu' : v ≠ u := hvu
  have hTail : [a, w, b, v, z, u].Nodup := by
    simp [List.nodup_cons, hab, hza.symm, hzb.symm, huw, hwv, hvu, haw, hva, hau,
      hbw.symm, hbu', hbu, hzw.symm, hzv.symm, hzu, ne_comm]
  have hcycle := copy_cycleGraph_six_of_edges hTail h₁ h₂ h₃ h₄ hvz huz.symm
  exact hfree6 hcycle

/-- A nonbacktracking four-edge walk with a fixed start. -/
structure FourEdgeWalk (G : SimpleGraph V) (u : V) where
  a : V
  w : V
  b : V
  v : V
  edge₁ : G.Adj u a
  edge₂ : G.Adj a w
  edge₃ : G.Adj w b
  edge₄ : G.Adj b v
  noBack₁ : u ≠ w
  noBack₂ : a ≠ b
  noBack₃ : w ≠ v

noncomputable instance fourEdgeWalkFintype (G : SimpleGraph V) (u : V) :
    Fintype (FourEdgeWalk G u) := by
  classical
  let f : FourEdgeWalk G u → V × V × V × V := fun p => (p.a, p.w, p.b, p.v)
  have hf : Function.Injective f := by
    intro p q hpq
    cases p
    cases q
    simp_all [f]
  letI : Finite (FourEdgeWalk G u) := Finite.of_injective f hf
  exact Fintype.ofFinite _

/-- Endpoint and middle-vertex pairs that arise from these walks. -/
def FourEdgeWalkPairs (G : SimpleGraph V) (u : V) :=
  {p : V × V // p.1 ≠ u ∧ ¬ Related G u p.1 ∧ p.2 ∈ ZSet G u p.1}

noncomputable instance fourEdgeWalkPairsFintype (G : SimpleGraph V) (u : V) :
    Fintype (FourEdgeWalkPairs G u) := by
  classical
  letI : Finite (FourEdgeWalkPairs G u) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- A walk is sent to its endpoint and middle vertex. -/
def fourEdgeWalkPair {G : SimpleGraph V} {u : V}
    (χ : G.Coloring (Fin 2)) (hfree4 : C4Free G) (hfree6 : C6Free G)
    (p : FourEdgeWalk G u) : FourEdgeWalkPairs G u := by
  have hend := fourEdgeWalk_endpoints_unrelated χ hfree4 hfree6
    p.edge₁ p.edge₂ p.edge₃ p.edge₄ p.noBack₁ p.noBack₂ p.noBack₃
  have hrelUW : Related G u p.w := ⟨p.noBack₁, p.a, p.edge₁, p.edge₂.symm⟩
  have hrelVW : Related G p.v p.w := ⟨p.noBack₃.symm, p.b, p.edge₄.symm, p.edge₃⟩
  exact ⟨(p.v, p.w), hend.1, hend.2, mem_zSet.mpr ⟨hrelUW, hrelVW⟩⟩

/-- The endpoint/middle-vertex map injects the walk set into the pair set. -/
theorem fourEdgeWalkPair_injective {G : SimpleGraph V} {u : V}
    (χ : G.Coloring (Fin 2)) (hfree4 : C4Free G) (hfree6 : C6Free G) :
    Function.Injective (fun p : FourEdgeWalk G u =>
      fourEdgeWalkPair (G := G) (u := u) χ hfree4 hfree6 p) := by
  intro p q hpq
  have hpv : p.v = q.v := congrArg (fun x : FourEdgeWalkPairs G u => x.val.1) hpq
  have hpw : p.w = q.w := congrArg (fun x : FourEdgeWalkPairs G u => x.val.2) hpq
  have hpa : p.a = q.a := by
    have hmem : p.a ∈ CommonNeighbors G u p.w :=
      commonNeighbors_mem.mpr ⟨p.edge₁, p.edge₂.symm⟩
    have hmem' : q.a ∈ CommonNeighbors G u p.w := by
      apply commonNeighbors_mem.mpr
      refine ⟨q.edge₁, ?_⟩
      rw [hpw]
      exact q.edge₂.symm
    have hcard := commonNeighbors_card_le_one_of_C4Free hfree4 p.noBack₁
    exact (Finset.card_le_one_iff.mp hcard) hmem hmem'
  have hpb : p.b = q.b := by
    have hmem : p.b ∈ CommonNeighbors G p.v p.w :=
      commonNeighbors_mem.mpr ⟨p.edge₄.symm, p.edge₃⟩
    have hmem' : q.b ∈ CommonNeighbors G p.v p.w := by
      apply commonNeighbors_mem.mpr
      constructor
      · rw [hpv]
        exact q.edge₄.symm
      · rw [hpw]
        exact q.edge₃
    have hcard := commonNeighbors_card_le_one_of_C4Free hfree4 p.noBack₃.symm
    exact (Finset.card_le_one_iff.mp hcard) hmem hmem'
  cases p
  cases q
  simp_all

/-- A finite set of size at least n admits an injective selection indexed by Fin n. -/
noncomputable def finsetSelectionSubset {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (n : ℕ) (hn : n ≤ s.card) : Finset α :=
  Classical.choose (Finset.exists_subset_card_eq (s := s) hn)

theorem finsetSelectionSubset_subset {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (n : ℕ) (hn : n ≤ s.card) :
    finsetSelectionSubset s n hn ⊆ s :=
  (Classical.choose_spec (Finset.exists_subset_card_eq (s := s) hn)).1

theorem finsetSelectionSubset_card {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (n : ℕ) (hn : n ≤ s.card) :
    (finsetSelectionSubset s n hn).card = n :=
  (Classical.choose_spec (Finset.exists_subset_card_eq (s := s) hn)).2

noncomputable def finsetSelection {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (n : ℕ) (hn : n ≤ s.card) : Fin n → α := by
  classical
  let t := finsetSelectionSubset s n hn
  have hcard := finsetSelectionSubset_card s n hn
  let e : t ≃ Fin n := Finset.equivFinOfCardEq hcard
  exact fun i => (e.symm i).val

theorem finsetSelection_injective {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (n : ℕ) (hn : n ≤ s.card) :
    Function.Injective (finsetSelection s n hn) := by
  classical
  unfold finsetSelection
  intro i j hij
  let e : finsetSelectionSubset s n hn ≃ Fin n :=
    Finset.equivFinOfCardEq (finsetSelectionSubset_card s n hn)
  have he : e.symm i = e.symm j := Subtype.ext hij
  have h := congrArg e he
  simpa [e] using h

theorem finsetSelection_mem {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (n : ℕ) (hn : n ≤ s.card) (i : Fin n) :
    finsetSelection s n hn i ∈ s := by
  classical
  unfold finsetSelection
  let e : finsetSelectionSubset s n hn ≃ Fin n :=
    Finset.equivFinOfCardEq (finsetSelectionSubset_card s n hn)
  exact finsetSelectionSubset_subset s n hn (e.symm i).property

/-- Neighbors of v other than a specified predecessor. -/
def otherNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (v prev : V) : Finset V :=
  (G.neighborFinset v).erase prev

theorem card_otherNeighbors {G : SimpleGraph V} [DecidableRel G.Adj] {v prev : V}
    (h : G.Adj v prev) :
    (otherNeighbors G v prev).card = G.degree v - 1 := by
  classical
  rw [otherNeighbors, Finset.card_erase_of_mem
    ((SimpleGraph.mem_neighborFinset (G := G) v prev).mpr h),
    SimpleGraph.card_neighborFinset_eq_degree]

theorem mem_otherNeighbors {G : SimpleGraph V} [DecidableRel G.Adj] {v prev w : V} :
    w ∈ otherNeighbors G v prev ↔ G.Adj v w ∧ w ≠ prev := by
  simp [otherNeighbors, Finset.mem_erase, SimpleGraph.mem_neighborFinset, and_comm]

noncomputable def firstWalkStep {G : SimpleGraph V} [DecidableRel G.Adj]
    (u : V) (d : ℕ) (hd : ∀ v, d ≤ G.degree v) : Fin d → V :=
  finsetSelection (G.neighborFinset u) d (by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hd u)

theorem firstWalkStep_adj {G : SimpleGraph V} [DecidableRel G.Adj]
    (u : V) (d : ℕ) (hd : ∀ v, d ≤ G.degree v) (i : Fin d) :
    G.Adj u (firstWalkStep u d hd i) := by
  exact (SimpleGraph.mem_neighborFinset (G := G) u _).mp
    (finsetSelection_mem (G.neighborFinset u) d (by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact hd u) i)

noncomputable def secondWalkStep {G : SimpleGraph V} [DecidableRel G.Adj]
    (u : V) (d : ℕ) (hd : ∀ v, d ≤ G.degree v) (i : Fin d) : Fin (d - 1) → V :=
  finsetSelection (otherNeighbors G (firstWalkStep u d hd i) u) (d - 1) (by
    rw [card_otherNeighbors (G := G) (firstWalkStep_adj u d hd i).symm]
    have hdeg := hd (firstWalkStep u d hd i)
    omega)

theorem secondWalkStep_spec {G : SimpleGraph V} [DecidableRel G.Adj]
    (u : V) (d : ℕ) (hd : ∀ v, d ≤ G.degree v) (i : Fin d) (j : Fin (d - 1)) :
    G.Adj (firstWalkStep u d hd i) (secondWalkStep u d hd i j) ∧
      secondWalkStep u d hd i j ≠ u := by
  exact mem_otherNeighbors.mp (finsetSelection_mem
    (otherNeighbors G (firstWalkStep u d hd i) u) (d - 1)
    (by
      rw [card_otherNeighbors (G := G) (firstWalkStep_adj u d hd i).symm]
      have hdeg := hd (firstWalkStep u d hd i)
      omega) j)

noncomputable def thirdWalkStep {G : SimpleGraph V} [DecidableRel G.Adj]
    (u : V) (d : ℕ) (hd : ∀ v, d ≤ G.degree v) (i : Fin d) (j : Fin (d - 1)) :
    Fin (d - 1) → V :=
  finsetSelection
    (otherNeighbors G (secondWalkStep u d hd i j) (firstWalkStep u d hd i))
    (d - 1) (by
      have hadj := (secondWalkStep_spec u d hd i j).1
      rw [card_otherNeighbors (G := G) hadj.symm]
      have hdeg := hd (secondWalkStep u d hd i j)
      omega)

theorem thirdWalkStep_spec {G : SimpleGraph V} [DecidableRel G.Adj]
    (u : V) (d : ℕ) (hd : ∀ v, d ≤ G.degree v) (i : Fin d) (j r : Fin (d - 1)) :
    G.Adj (secondWalkStep u d hd i j) (thirdWalkStep u d hd i j r) ∧
      thirdWalkStep u d hd i j r ≠ firstWalkStep u d hd i := by
  exact mem_otherNeighbors.mp (finsetSelection_mem
    (otherNeighbors G (secondWalkStep u d hd i j) (firstWalkStep u d hd i))
    (d - 1) (by
      have hadj := (secondWalkStep_spec u d hd i j).1
      rw [card_otherNeighbors (G := G) hadj.symm]
      have hdeg := hd (secondWalkStep u d hd i j)
      omega) r)

noncomputable def fourthWalkStep {G : SimpleGraph V} [DecidableRel G.Adj]
    (u : V) (d : ℕ) (hd : ∀ v, d ≤ G.degree v) (i : Fin d) (j r : Fin (d - 1)) :
    Fin (d - 1) → V :=
  finsetSelection
    (otherNeighbors G (thirdWalkStep u d hd i j r) (secondWalkStep u d hd i j))
    (d - 1) (by
      have hadj := (thirdWalkStep_spec u d hd i j r).1
      rw [card_otherNeighbors (G := G) hadj.symm]
      have hdeg := hd (thirdWalkStep u d hd i j r)
      omega)

theorem fourthWalkStep_spec {G : SimpleGraph V} [DecidableRel G.Adj]
    (u : V) (d : ℕ) (hd : ∀ v, d ≤ G.degree v) (i : Fin d) (j r s : Fin (d - 1)) :
    G.Adj (thirdWalkStep u d hd i j r) (fourthWalkStep u d hd i j r s) ∧
      fourthWalkStep u d hd i j r s ≠ secondWalkStep u d hd i j := by
  exact mem_otherNeighbors.mp (finsetSelection_mem
    (otherNeighbors G (thirdWalkStep u d hd i j r) (secondWalkStep u d hd i j))
    (d - 1) (by
      have hadj := (thirdWalkStep_spec u d hd i j r).1
      rw [card_otherNeighbors (G := G) hadj.symm]
      have hdeg := hd (thirdWalkStep u d hd i j r)
      omega) s)

noncomputable def fourWalkOfChoice {G : SimpleGraph V} [DecidableRel G.Adj]
    (u : V) (d : ℕ) (hd : ∀ v, d ≤ G.degree v)
    (i : Fin d) (j r s : Fin (d - 1)) : FourEdgeWalk G u where
  a := firstWalkStep u d hd i
  w := secondWalkStep u d hd i j
  b := thirdWalkStep u d hd i j r
  v := fourthWalkStep u d hd i j r s
  edge₁ := firstWalkStep_adj u d hd i
  edge₂ := (secondWalkStep_spec u d hd i j).1
  edge₃ := (thirdWalkStep_spec u d hd i j r).1
  edge₄ := (fourthWalkStep_spec u d hd i j r s).1
  noBack₁ := (secondWalkStep_spec u d hd i j).2.symm
  noBack₂ := (thirdWalkStep_spec u d hd i j r).2.symm
  noBack₃ := (fourthWalkStep_spec u d hd i j r s).2.symm

abbrev FourWalkChoice (d : ℕ) := Fin d × (Fin (d - 1) × (Fin (d - 1) × Fin (d - 1)))

noncomputable def fourWalkOfChoiceTuple {G : SimpleGraph V} [DecidableRel G.Adj]
    (u : V) (d : ℕ) (hd : ∀ v, d ≤ G.degree v) (x : FourWalkChoice d) :
    FourEdgeWalk G u :=
  fourWalkOfChoice u d hd x.1 x.2.1 x.2.2.1 x.2.2.2

theorem fourWalkOfChoiceTuple_injective {G : SimpleGraph V} [DecidableRel G.Adj]
    (u : V) (d : ℕ) (hd : ∀ v, d ≤ G.degree v) :
    Function.Injective (fourWalkOfChoiceTuple u d hd) := by
  intro x y hxy
  rcases x with ⟨i, j, r, s⟩
  rcases y with ⟨i', j', r', s'⟩
  have hi : firstWalkStep u d hd i = firstWalkStep u d hd i' :=
    congrArg FourEdgeWalk.a hxy
  have hii : i = i' := finsetSelection_injective (G.neighborFinset u) d
    (by rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hd u) hi
  subst i'
  have hj : secondWalkStep u d hd i j = secondWalkStep u d hd i j' :=
    congrArg FourEdgeWalk.w hxy
  have hjj : j = j' := finsetSelection_injective
    (otherNeighbors G (firstWalkStep u d hd i) u) (d - 1)
    (by
      rw [card_otherNeighbors (G := G) (firstWalkStep_adj u d hd i).symm]
      have hdeg := hd (firstWalkStep u d hd i)
      omega) hj
  subst j'
  have hr : thirdWalkStep u d hd i j r = thirdWalkStep u d hd i j r' :=
    congrArg FourEdgeWalk.b hxy
  have hrr : r = r' := finsetSelection_injective
    (otherNeighbors G (secondWalkStep u d hd i j) (firstWalkStep u d hd i)) (d - 1)
    (by
      have hadj := (secondWalkStep_spec u d hd i j).1
      rw [card_otherNeighbors (G := G) hadj.symm]
      have hdeg := hd (secondWalkStep u d hd i j)
      omega) hr
  subst r'
  have hs : fourthWalkStep u d hd i j r s = fourthWalkStep u d hd i j r s' :=
    congrArg FourEdgeWalk.v hxy
  have hss : s = s' := finsetSelection_injective
    (otherNeighbors G (thirdWalkStep u d hd i j r) (secondWalkStep u d hd i j)) (d - 1)
    (by
      have hadj := (thirdWalkStep_spec u d hd i j r).1
      rw [card_otherNeighbors (G := G) hadj.symm]
      have hdeg := hd (thirdWalkStep u d hd i j r)
      omega) hs
  subst s'
  rfl

/-- Minimum degree d gives at least d(d-1)^3 nonbacktracking four-edge walks. -/
theorem fourEdgeWalk_card_lower {G : SimpleGraph V} [DecidableRel G.Adj]
    (u : V) (d : ℕ) (hd : ∀ v, d ≤ G.degree v) :
    d * (d - 1) ^ 3 ≤ Fintype.card (FourEdgeWalk G u) := by
  have hcard := Fintype.card_le_of_injective
    (fourWalkOfChoiceTuple u d hd) (fourWalkOfChoiceTuple_injective u d hd)
  calc
    d * (d - 1) ^ 3 = Fintype.card (FourWalkChoice d) := by
      simp [FourWalkChoice, pow_succ, mul_assoc]
    _ ≤ Fintype.card (FourEdgeWalk G u) := hcard

/-- Endpoints unrelated to u in the walk count. -/
abbrev ValidWalkEndpoint (G : SimpleGraph V) (u : V) :=
  {v : V // v ≠ u ∧ ¬ Related G u v}

noncomputable instance validWalkEndpointFintype (G : SimpleGraph V) (u : V) :
    Fintype (ValidWalkEndpoint G u) := by
  classical
  letI : Finite (ValidWalkEndpoint G u) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable def fourEdgeWalkPairsEquivSigma {G : SimpleGraph V} {u : V} :
    FourEdgeWalkPairs G u ≃
      Σ v : ValidWalkEndpoint G u, {w // w ∈ ZSet G u v.1} where
  toFun p := ⟨⟨p.1.1, p.2.1, p.2.2.1⟩, ⟨p.1.2, p.2.2.2⟩⟩
  invFun p := ⟨(p.1.1, p.2.1), p.1.2.1, p.1.2.2, p.2.2⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; rcases p with ⟨⟨v, hv⟩, ⟨w, hw⟩⟩; rfl

/-- The walk-pair count is the unlabelled sum of the Z_uv cardinalities. -/
theorem fourEdgeWalkPairs_card_eq_sum {G : SimpleGraph V} {u : V} :
    Fintype.card (FourEdgeWalkPairs G u) =
      ∑ v : ValidWalkEndpoint G u, (ZSet G u v.1).card := by
  rw [Fintype.card_congr fourEdgeWalkPairsEquivSigma, Fintype.card_sigma]
  simp

/-- Four-edge walks prove the lower bound for the unlabelled Z_uv sum. -/
theorem fourEdgeWalk_sum_lower {G : SimpleGraph V} [DecidableRel G.Adj]
    (χ : G.Coloring (Fin 2)) (hfree4 : C4Free G) (hfree6 : C6Free G)
    (u : V) (d : ℕ) (hd : ∀ v, d ≤ G.degree v) :
    d * (d - 1) ^ 3 ≤ ∑ v : ValidWalkEndpoint G u, (ZSet G u v.1).card := by
  calc
    d * (d - 1) ^ 3 ≤ Fintype.card (FourEdgeWalk G u) := fourEdgeWalk_card_lower u d hd
    _ ≤ Fintype.card (FourEdgeWalkPairs G u) := Fintype.card_le_of_injective
      (fourEdgeWalkPair χ hfree4 hfree6) (fourEdgeWalkPair_injective χ hfree4 hfree6)
    _ = ∑ v : ValidWalkEndpoint G u, (ZSet G u v.1).card := fourEdgeWalkPairs_card_eq_sum

end L575U

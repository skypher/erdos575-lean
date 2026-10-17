import JustinSun.Erdos575.Upper.CommonNeighbor
import JustinSun.Erdos575.Geometry.LineSide

/-!
# Erdős 575, blueprint item 26: the incidence graphs avoid the forbidden families

A copy of a member of the J family in a 2-coloured graph without 4- and 6-cycles yields a J-pattern
on the common-neighbour relation (`JPatternIn`); in the incidence graph `Iq F` this is a point-side or
line-side J-pattern, excluded for even `q`.
-/

namespace A575

open L575U L575G

section Generic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A J-pattern on the common-neighbour relation of `G`. -/
def JPatternIn (G : SimpleGraph V) : Prop :=
  ∃ x y z x' C D C' D' : V,
    x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x' ≠ y ∧ x' ≠ z ∧ x' ≠ x ∧
    ¬ Related G x y ∧ ¬ Related G x z ∧ ¬ Related G y z ∧
    ¬ Related G x' y ∧ ¬ Related G x' z ∧
    C ≠ D ∧ Related G x C ∧ Related G y C ∧ Related G z C ∧
      Related G x D ∧ Related G y D ∧ Related G z D ∧
    C' ≠ D' ∧ Related G x' C' ∧ Related G y C' ∧ Related G z C' ∧
      Related G x' D' ∧ Related G y D' ∧ Related G z D' ∧
    Related G x x'

theorem sAdj_base_sub (i : Fin 3) (j : Fin 2) : (SGraph 2).Adj (.base i) (.sub i j) := by
  simp [SGraph, sAdj]

theorem sAdj_center_sub (i : Fin 3) (j : Fin 2) : (SGraph 2).Adj (.center j) (.sub i j) := by
  simp [SGraph, sAdj]

/-- A template map of the J family gives a J-pattern. -/
theorem jPatternIn_of_templateMap {G : SimpleGraph V} (χ : G.Coloring (Fin 2))
    (h4 : C4Free G) (h6 : C6Free G) (f : J0Vert → V)
    (hedge : ∀ a b, J0Graph.Adj a b → G.Adj (f a) (f b))
    (hinj : ∀ copy, Function.Injective (fun w : SVert 2 => f (jCopy copy w)))
    (hxx : f .x ≠ f .xp) : JPatternIn G := by
  -- the two subdivision copies
  let cp : Fin 2 → SimpleGraph.Copy (SGraph 2) G := fun copy =>
    ⟨⟨fun w => f (jCopy copy w), fun {u v} huv => hedge _ _ ((jCopyHom copy).map_adj huv)⟩,
      hinj copy⟩
  have ind := fun copy => subdivision_copy_base_independent χ h4 h6 (by norm_num) (cp copy)
  have cpb : ∀ copy i, (cp copy).toHom (.base i) = f (jCopy copy (.base i)) := fun _ _ => rfl
  -- distinct images within a copy
  have dist : ∀ copy (u v : SVert 2), u ≠ v → f (jCopy copy u) ≠ f (jCopy copy v) :=
    fun copy u v huv h => huv (hinj copy h)
  -- a base and a center of the same copy are related
  have rel : ∀ copy i j, Related G (f (jCopy copy (.base i))) (f (jCopy copy (.center j))) := by
    intro copy i j
    refine ⟨dist copy _ _ (by simp), f (jCopy copy (.sub i j)), ?_, ?_⟩
    · exact hedge _ _ ((jCopyHom copy).map_adj (sAdj_base_sub i j))
    · exact hedge _ _ ((jCopyHom copy).map_adj (sAdj_center_sub i j))
  have nrel : ∀ copy (i i' : Fin 3), i ≠ i' →
      ¬ Related G (f (jCopy copy (.base i))) (f (jCopy copy (.base i'))) := by
    intro copy i i' hii
    have := ind copy i i' hii
    simpa only [cpb] using this
  have bx : jCopy 0 (.base 0) = .x := rfl
  have bxp : jCopy 1 (.base 0) = .xp := rfl
  have by0 : jCopy 0 (.base 1) = .y := rfl
  have by1 : jCopy 1 (.base 1) = .y := rfl
  have bz0 : jCopy 0 (.base 2) = .z := rfl
  have bz1 : jCopy 1 (.base 2) = .z := rfl
  have hlamx : J0Graph.Adj .lam .x := by simp [J0Graph, J0Adj]
  have hlamxp : J0Graph.Adj .lam .xp := by simp [J0Graph, J0Adj]
  refine ⟨f .x, f .y, f .z, f .xp, f (.c 0 0), f (.c 0 1), f (.c 1 0), f (.c 1 1), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hxx.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← bx, ← by0]; exact dist 0 _ _ (by simp)
  · rw [← bx, ← bz0]; exact dist 0 _ _ (by simp)
  · rw [← by0, ← bz0]; exact dist 0 _ _ (by simp)
  · rw [← bxp, ← by1]; exact dist 1 _ _ (by simp)
  · rw [← bxp, ← bz1]; exact dist 1 _ _ (by simp)
  · rw [← bx, ← by0]; exact nrel 0 0 1 (by decide)
  · rw [← bx, ← bz0]; exact nrel 0 0 2 (by decide)
  · rw [← by0, ← bz0]; exact nrel 0 1 2 (by decide)
  · rw [← bxp, ← by1]; exact nrel 1 0 1 (by decide)
  · rw [← bxp, ← bz1]; exact nrel 1 0 2 (by decide)
  · exact dist 0 (.center 0) (.center 1) (by simp)
  · rw [← bx]; exact rel 0 0 0
  · rw [← by0]; exact rel 0 1 0
  · rw [← bz0]; exact rel 0 2 0
  · rw [← bx]; exact rel 0 0 1
  · rw [← by0]; exact rel 0 1 1
  · rw [← bz0]; exact rel 0 2 1
  · exact dist 1 (.center 0) (.center 1) (by simp)
  · rw [← bxp]; exact rel 1 0 0
  · rw [← by1]; exact rel 1 1 0
  · rw [← bz1]; exact rel 1 2 0
  · rw [← bxp]; exact rel 1 0 1
  · rw [← by1]; exact rel 1 1 1
  · rw [← bz1]; exact rel 1 2 1
  · exact ⟨hxx, f .lam, hedge _ _ hlamx.symm, hedge _ _ hlamxp.symm⟩

end Generic

section Incidence

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The bipartition colouring of the incidence graph. -/
def iqColoring : (Iq F).Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk (fun v => match v with | Sum.inl _ => 0 | Sum.inr _ => 1)
    (by intro u v h; cases u <;> cases v <;> simp_all [Iq])

theorem related_inl_iff {P Q : Points F} :
    Related (Iq F) (Sum.inl P) (Sum.inl Q) ↔ PointRelated F P Q := by
  constructor
  · rintro ⟨hne, w, hPw, hQw⟩
    cases w with
    | inl _ => simp [Iq] at hPw
    | inr M => exact ⟨fun h => hne (by rw [h]), M, hPw, hQw⟩
  · rintro ⟨hne, M, hPM, hQM⟩
    exact ⟨fun h => hne (Sum.inl_injective h), Sum.inr M, hPM, hQM⟩

theorem related_inr_iff {M N : Lines F} :
    Related (Iq F) (Sum.inr M) (Sum.inr N) ↔ LineRelated F M N := by
  constructor
  · rintro ⟨hne, w, hMw, hNw⟩
    cases w with
    | inr _ => simp [Iq] at hMw
    | inl P => exact ⟨fun h => hne (by rw [h]), P, hMw, hNw⟩
  · rintro ⟨hne, P, hPM, hPN⟩
    exact ⟨fun h => hne (Sum.inr_injective h), Sum.inl P, hPM, hPN⟩

theorem inl_of_related {P : Points F} {v : Points F ⊕ Lines F}
    (h : Related (Iq F) (Sum.inl P) v) : ∃ Q, v = Sum.inl Q := by
  obtain ⟨-, w, hPw, hvw⟩ := h
  cases w with
  | inl _ => simp [Iq] at hPw
  | inr M =>
    cases v with
    | inl Q => exact ⟨Q, rfl⟩
    | inr _ => simp [Iq] at hvw

theorem inr_of_related {M : Lines F} {v : Points F ⊕ Lines F}
    (h : Related (Iq F) (Sum.inr M) v) : ∃ N, v = Sum.inr N := by
  obtain ⟨-, w, hMw, hvw⟩ := h
  cases w with
  | inr _ => simp [Iq] at hMw
  | inl P =>
    cases v with
    | inr N => exact ⟨N, rfl⟩
    | inl _ => simp [Iq] at hvw

theorem related_symm' {G : SimpleGraph (Points F ⊕ Lines F)} {u v : Points F ⊕ Lines F}
    (h : Related G u v) : Related G v u := related_symm h

/-- A J-pattern in the incidence graph lies on one side. -/
theorem point_or_line_jPattern (h : JPatternIn (Iq F)) : PointJPattern F ∨ LineJPattern F := by
  obtain ⟨x, y, z, x', C, D, C', D', hxy, hxz, hyz, hx'y, hx'z, hx'x, nxy, nxz, nyz, nx'y, nx'z,
    hCD, hxC, hyC, hzC, hxD, hyD, hzD, hCD', hx'C', hyC', hzC', hx'D', hyD', hzD', hxx'⟩ := h
  cases x with
  | inl P =>
    obtain ⟨C₀, rfl⟩ := inl_of_related hxC
    obtain ⟨D₀, rfl⟩ := inl_of_related hxD
    obtain ⟨X', rfl⟩ := inl_of_related hxx'
    obtain ⟨Y, rfl⟩ := inl_of_related (related_symm hyC)
    obtain ⟨Z, rfl⟩ := inl_of_related (related_symm hzC)
    obtain ⟨C₁, rfl⟩ := inl_of_related hx'C'
    obtain ⟨D₁, rfl⟩ := inl_of_related hx'D'
    left
    simp only [related_inl_iff, ne_eq, Sum.inl.injEq] at *
    exact ⟨P, Y, Z, X', hxy, hxz, hyz, hx'y, hx'z, hx'x, nxy, nxz, nyz, nx'y, nx'z,
      ⟨C₀, D₀, hCD, hxC, hyC, hzC, hxD, hyD, hzD⟩, ⟨C₁, D₁, hCD', hx'C', hyC', hzC', hx'D', hyD', hzD'⟩,
      hxx'⟩
  | inr M =>
    obtain ⟨C₀, rfl⟩ := inr_of_related hxC
    obtain ⟨D₀, rfl⟩ := inr_of_related hxD
    obtain ⟨X', rfl⟩ := inr_of_related hxx'
    obtain ⟨Y, rfl⟩ := inr_of_related (related_symm hyC)
    obtain ⟨Z, rfl⟩ := inr_of_related (related_symm hzC)
    obtain ⟨C₁, rfl⟩ := inr_of_related hx'C'
    obtain ⟨D₁, rfl⟩ := inr_of_related hx'D'
    right
    simp only [related_inr_iff, ne_eq, Sum.inr.injEq] at *
    exact ⟨M, Y, Z, X', hxy, hxz, hyz, hx'y, hx'z, hx'x, nxy, nxz, nyz, nx'y, nx'z,
      ⟨C₀, D₀, hCD, hxC, hyC, hzC, hxD, hyD, hzD⟩, ⟨C₁, D₁, hCD', hx'C', hyC', hzC', hx'D', hyD', hzD'⟩,
      hxx'⟩

/-- **Item 26, J part.** For even `q`, the incidence graph contains no member of the J family. -/
theorem iq_jFree (hchar : ringChar F = 2) : ¬ ∃ A ∈ J, SimpleGraph.IsContained A.2 (Iq F) := by
  intro h
  obtain ⟨f, hedge, hinj, -, hxx⟩ := (jFamily_interface (Iq F)).1 h
  rcases point_or_line_jPattern (jPatternIn_of_templateMap iqColoring (Iq_cycle4_free (F := F))
    (Iq_cycle6_free (F := F)) f hedge hinj hxx) with hP | hL
  · exact noPointJPattern (F := F) hP
  · exact noEvenLineJPattern (F := F) hchar hL

end Incidence

section KPart

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem sAdj3_base_sub (i : Fin 3) (j : Fin 3) : (SGraph 3).Adj (.base i) (.sub i j) := by
  simp [SGraph, sAdj]

theorem sAdj3_center_sub (i : Fin 3) (j : Fin 3) : (SGraph 3).Adj (.center j) (.sub i j) := by
  simp [SGraph, sAdj]

/-- Three pairwise unrelated lines with three distinct common centres contradict the odd-`q` triad
count. -/
theorem no_line_triad_three (hchar : ringChar F ≠ 2) {x y z C₁ C₂ C₃ : Lines F}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (nxy : ¬ LineRelated F x y) (nxz : ¬ LineRelated F x z) (nyz : ¬ LineRelated F y z)
    (h12 : C₁ ≠ C₂) (h13 : C₁ ≠ C₃) (h23 : C₂ ≠ C₃)
    (hC : ∀ C ∈ ({C₁, C₂, C₃} : Set (Lines F)),
      LineRelated F x C ∧ LineRelated F y C ∧ LineRelated F z C) : False := by
  classical
  have hcount := oddLineTriadCenters (F := F) hchar x y z hxy hxz hyz nxy nxz nyz
  have h3 : 3 ≤ Fintype.card { C : Lines F // C ∈ LineTriadCenters F x y z } := by
    let g : Fin 3 → { C : Lines F // C ∈ LineTriadCenters F x y z } := fun i =>
      ⟨![C₁, C₂, C₃] i, by
        have hmem : ![C₁, C₂, C₃] i ∈ ({C₁, C₂, C₃} : Set (Lines F)) := by
          fin_cases i <;> simp
        exact hC _ hmem⟩
    have hg : Function.Injective g := by
      intro i j hij
      have := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> simp_all [g] <;> tauto
    simpa using Fintype.card_le_of_injective g hg
  rcases hcount with h | h <;> omega

/-- **Item 26, K part.** For odd `q`, the incidence graph contains no member of the K family. -/
theorem iq_kFree (hchar : ringChar F ≠ 2) : ¬ ∃ A ∈ K, SimpleGraph.IsContained A.2 (Iq F) := by
  intro h
  obtain ⟨f, hedge, hinj, -⟩ := (kFamily_interface (Iq F)).1 h
  let cp : Fin 2 → SimpleGraph.Copy (SGraph 3) (Iq F) := fun copy =>
    ⟨⟨fun w => f (kCopy copy w), fun {u v} huv => hedge _ _ ((kCopyHom copy).map_adj huv)⟩,
      hinj copy⟩
  have ind := fun copy => subdivision_copy_base_independent iqColoring (Iq_cycle4_free (F := F))
    (Iq_cycle6_free (F := F)) (by norm_num) (cp copy)
  have dist : ∀ copy (u v : SVert 3), u ≠ v → f (kCopy copy u) ≠ f (kCopy copy v) :=
    fun copy u v huv h => huv (hinj copy h)
  have rel : ∀ copy i j, Related (Iq F) (f (kCopy copy (.base i))) (f (kCopy copy (.center j))) := by
    intro copy i j
    refine ⟨dist copy _ _ (by simp), f (kCopy copy (.sub i j)), ?_, ?_⟩
    · exact hedge _ _ ((kCopyHom copy).map_adj (sAdj3_base_sub i j))
    · exact hedge _ _ ((kCopyHom copy).map_adj (sAdj3_center_sub i j))
  -- a copy whose centres are lines
  have key : ∀ copy, (∃ M, f (kCopy copy (.center 0)) = Sum.inr M) → False := by
    intro copy ⟨M, hM⟩
    -- bases and centres of this copy are lines
    have hbase : ∀ i, ∃ N, f (kCopy copy (.base i)) = Sum.inr N := by
      intro i
      have := rel copy i 0
      rw [hM] at this
      exact inr_of_related (related_symm this)
    have hcent : ∀ j, ∃ N, f (kCopy copy (.center j)) = Sum.inr N := by
      intro j
      obtain ⟨N, hN⟩ := hbase 0
      have := rel copy 0 j
      rw [hN] at this
      exact inr_of_related this
    choose b hb using hbase
    choose c hc using hcent
    have nrel : ∀ i i', i ≠ i' → ¬ LineRelated F (b i) (b i') := by
      intro i i' hii
      have := ind copy i i' hii
      simp only [cp] at this
      change ¬ Related (Iq F) (f (kCopy copy (.base i))) (f (kCopy copy (.base i'))) at this
      rwa [hb, hb, related_inr_iff] at this
    have bne : ∀ i i', i ≠ i' → b i ≠ b i' := by
      intro i i' hii h
      apply dist copy (.base i) (.base i') (by simpa using hii)
      rw [hb, hb, h]
    have cne : ∀ j j', j ≠ j' → c j ≠ c j' := by
      intro j j' hjj h
      apply dist copy (.center j) (.center j') (by simpa using hjj)
      rw [hc, hc, h]
    have crel : ∀ i j, LineRelated F (b i) (c j) := by
      intro i j
      have := rel copy i j
      rwa [hb, hc, related_inr_iff] at this
    exact no_line_triad_three hchar (bne 0 1 (by decide)) (bne 0 2 (by decide))
      (bne 1 2 (by decide)) (nrel 0 1 (by decide)) (nrel 0 2 (by decide)) (nrel 1 2 (by decide))
      (cne 0 1 (by decide)) (cne 0 2 (by decide)) (cne 1 2 (by decide))
      (by
        intro C hC
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
        rcases hC with rfl | rfl | rfl
        · exact ⟨crel 0 0, crel 1 0, crel 2 0⟩
        · exact ⟨crel 0 1, crel 1 1, crel 2 1⟩
        · exact ⟨crel 0 2, crel 1 2, crel 2 2⟩)
  -- the two copies' first centres are adjacent, hence on opposite sides
  have hcross : K0Graph.Adj (kCopy 0 (.center 0)) (kCopy 1 (.center 0)) := by
    simp [K0Graph, K0Adj]
  have hadj := hedge _ _ hcross
  cases h0 : f (kCopy 0 (.center 0)) with
  | inr M => exact key 0 ⟨M, h0⟩
  | inl P =>
    cases h1 : f (kCopy 1 (.center 0)) with
    | inr N => exact key 1 ⟨N, h1⟩
    | inl Q => rw [h0, h1] at hadj; simp [Iq] at hadj

end KPart

end A575

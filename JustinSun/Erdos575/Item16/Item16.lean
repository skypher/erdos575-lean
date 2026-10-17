import JustinSun.Erdos575.Upper.Counting

namespace L575K

open SimpleGraph

/-- Item 16: the uncovered-edge contradiction in the vertex-cover claim of §3. -/
def Item16Claim : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (χ : G.Coloring (Fin 2)) (hfree4 : L575U.C4Free G) (hfree6 : L575U.C6Free G)
    (hK : ∀ A ∈ L575U.K, A.2.Free G) (S₀ S₁ : Finset V)
    (h₀ : ∀ x ∈ S₀, χ x = 0) (h₁ : ∀ x ∈ S₁, χ x = 1) (u v : V),
    G.Adj u v → u ∈ S₀ → u ∉ L575U.U_S G S₀ → v ∈ S₁ → v ∉ L575U.U_S G S₁ → False

private theorem prescribed_s3_copy {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (χ : G.Coloring (Fin 2))
    (hfree4 : L575U.C4Free G) (hfree6 : L575U.C6Free G)
    (S : Finset V) (hside : ∀ x ∈ S, χ x = 0)
    (T : Finset V) (hT : T ∈ L575U.T_S G S)
    (u : V) (hu : u ∈ L575U.tripleCenters G S T)
    (hlarge : 3 ≤ (L575U.tripleCenters G S T).card) :
    ∃ copy : SimpleGraph.Copy (L575U.SGraph 3) G,
      copy.toHom (.center 0) = u ∧ ∀ i, copy.toHom (.base i) ∈ S := by
  classical
  have hT' := (Finset.mem_filter.mp hT).2
  have hTcard : T.card = 3 := hT'.1
  have hTsub : T ⊆ S := hT'.2.1
  have hTind : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ L575U.Related G x y := hT'.2.2.1
  let eT : T ≃ Fin 3 := Finset.equivFinOfCardEq hTcard
  let base : Fin 3 → V := fun i => (eT.symm i).val
  have hbInj : Function.Injective base := by
    intro i j hij
    apply eT.symm.injective
    exact Subtype.ext hij
  have hbaseColor : ∀ i, χ (base i) = 0 := fun i => hside _ (hTsub (eT.symm i).property)
  have hbase : ∀ i i', i ≠ i' → ¬ L575U.Related G (base i) (base i') := by
    intro i i' hii hrel
    apply hTind (base i) (eT.symm i).property (base i') (eT.symm i').property
    · intro heq
      exact hii (hbInj heq)
    · exact hrel
  let C := L575U.tripleCenters G S T
  have huC : u ∈ C := hu
  change 3 ≤ C.card at hlarge
  have hCerase : 2 ≤ (C.erase u).card := by
    rw [Finset.card_erase_of_mem huC]
    omega
  obtain ⟨c₁, c₂, hc₁, hc₂, hcne⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < (C.erase u).card)
  have hc₁C : c₁ ∈ C := Finset.mem_of_mem_erase hc₁
  have hc₂C : c₂ ∈ C := Finset.mem_of_mem_erase hc₂
  have hcu₁ : c₁ ≠ u := (Finset.mem_erase.mp hc₁).1
  have hcu₂ : c₂ ≠ u := (Finset.mem_erase.mp hc₂).1
  let center : Fin 3 → V := ![u, c₁, c₂]
  have hcInj : Function.Injective center := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [center]
  have hcenterColor : ∀ j, χ (center j) = 0 := by
    intro j
    fin_cases j
    · exact hside _ ((Finset.mem_filter.mp hu).2.1)
    · exact hside _ ((Finset.mem_filter.mp hc₁C).2.1)
    · exact hside _ ((Finset.mem_filter.mp hc₂C).2.1)
  have hrel : ∀ i j, L575U.Related G (base i) (center j) := by
    intro i j
    have hjC : center j ∈ C := by
      fin_cases j
      · exact huC
      · exact hc₁C
      · exact hc₂C
    exact (Finset.mem_filter.mp hjC).2.2 _ (eT.symm i).property
  have hcenter : ∀ j j', j ≠ j' → ¬ L575U.Related G (center j) (center j') := by
    intro j j' hjj hrelJJ
    let i₀ : Fin 3 := 0
    let i₁ : Fin 3 := 1
    have hi : i₀ ≠ i₁ := by decide
    have hab : base i₀ ≠ base i₁ := fun heq => hi (hbInj heq)
    have hjv : center j ≠ center j' := fun heq => hjj (hcInj heq)
    exact L575U.two_centers_not_related (G := G) χ hfree4 hfree6
      (hbaseColor i₀) (hbaseColor i₁) (hcenterColor j) (hcenterColor j')
      hab hjv (hbase i₀ i₁ hi)
      (L575U.related_symm (hrel i₀ j)) (L575U.related_symm (hrel i₁ j))
      (L575U.related_symm (hrel i₀ j')) (L575U.related_symm (hrel i₁ j')) hrelJJ
  let copy := L575U.subdivision_copy_of_related_triples χ base center hbInj hcInj
    hbaseColor hcenterColor hbase hcenter hrel
  refine ⟨copy, ?_, ?_⟩
  · rfl
  · intro i
    change base i ∈ S
    exact hTsub (eT.symm i).property

private theorem copy_coloring {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (χ : G.Coloring (Fin 2))
    (copy : SimpleGraph.Copy (L575U.SGraph 3) G)
    (hbase : ∀ i, χ (copy.toHom (.base i)) = 0) :
    ∀ w, χ (copy.toHom w) = if L575U.sColor w then 1 else 0 := by
  intro w
  cases w with
  | base i => rw [hbase i]; simp [L575U.sColor]
  | center j =>
      have hrel : L575U.Related G (copy.toHom (.base 0)) (copy.toHom (.center j)) := by
        refine ⟨?_, copy.toHom (.sub 0 j), ?_, ?_⟩
        · intro heq
          have h := copy.injective' heq
          cases h
        · exact copy.toHom.map_rel (by simp [L575U.SGraph, L575U.sAdj])
        · exact (copy.toHom.map_rel (by simp [L575U.SGraph, L575U.sAdj])).symm
      have hc := L575U.related_color_eq (G := G) χ hrel
      calc
        χ (copy.toHom (.center j)) = χ (copy.toHom (.base 0)) := hc.symm
        _ = 0 := hbase 0
        _ = if L575U.sColor (.center j) then 1 else 0 := by simp [L575U.sColor]
  | sub i j =>
      have hadj : G.Adj (copy.toHom (.base i)) (copy.toHom (.sub i j)) :=
        copy.toHom.map_rel (by simp [L575U.SGraph, L575U.sAdj])
      have hne : χ (copy.toHom (.sub i j)) ≠ 0 := by
        intro heq
        exact (χ.valid hadj) ((hbase i).trans heq.symm)
      have hone : χ (copy.toHom (.sub i j)) = 1 := Fin.eq_one_of_ne_zero _ hne
      simpa [L575U.sColor] using hone

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem item16 : Item16Claim := by
  classical
  intro V _ _ G _ χ hfree4 hfree6 hK S₀ S₁ h₀ h₁ u v huv hu hnotU hv hnotV
  have huBad : ¬ (∀ T ∈ L575U.T_S G S₀, u ∈ L575U.tripleCenters G S₀ T →
      (L575U.tripleCenters G S₀ T).card < 3) := by
    intro h
    exact hnotU (Finset.mem_filter.mpr ⟨hu, h⟩)
  push_neg at huBad
  obtain ⟨T₀, hT₀, huT₀, hT₀large⟩ := huBad
  have hvBad : ¬ (∀ T ∈ L575U.T_S G S₁, v ∈ L575U.tripleCenters G S₁ T →
      (L575U.tripleCenters G S₁ T).card < 3) := by
    intro h
    exact hnotV (Finset.mem_filter.mpr ⟨hv, h⟩)
  push_neg at hvBad
  obtain ⟨T₁, hT₁, hvT₁, hT₁large⟩ := hvBad
  obtain ⟨copy₀, hcopy₀, hbaseS₀⟩ := prescribed_s3_copy χ hfree4 hfree6 S₀ h₀ T₀ hT₀ u huT₀ hT₀large
  let χ' : G.Coloring (Fin 2) := ⟨fun x => Equiv.swap 0 1 (χ x), by
    intro a b hab heq
    apply χ.valid hab
    exact Equiv.injective (Equiv.swap 0 1) heq⟩
  have h₁' : ∀ x ∈ S₁, χ' x = 0 := by
    intro x hx
    simp [χ', h₁ x hx, Equiv.swap_apply_right]
  obtain ⟨copy₁, hcopy₁, hbaseS₁⟩ := prescribed_s3_copy χ' hfree4 hfree6 S₁ h₁' T₁ hT₁ v hvT₁ hT₁large
  have hbase₀ : ∀ i, χ (copy₀.toHom (.base i)) = 0 := fun i => h₀ _ (hbaseS₀ i)
  have hbase₁ : ∀ i, χ' (copy₁.toHom (.base i)) = 0 := by
    intro i
    exact h₁' _ (hbaseS₁ i)
  have hcol₀ := copy_coloring χ copy₀ hbase₀
  have hcol₁ := copy_coloring χ' copy₁ hbase₁
  let f : L575U.K0Vert → V := fun a => if a.1 = 0 then copy₀.toHom a.2 else copy₁.toHom a.2
  have hf0 : ∀ w, f (L575U.kCopy 0 w) = copy₀.toHom w := by intro w; simp [f, L575U.kCopy]
  have hf1 : ∀ w, f (L575U.kCopy 1 w) = copy₁.toHom w := by intro w; simp [f, L575U.kCopy]
  have hedge : ∀ a b, L575U.K0Graph.Adj a b → G.Adj (f a) (f b) := by
    intro a b hab
    change L575U.K0Adj a b at hab
    rcases hab with ⟨i, x, y, hxy, rfl, rfl⟩ | hcross
    · fin_cases i
      · simpa [hf0] using copy₀.toHom.map_rel hxy
      · simpa [hf1] using copy₁.toHom.map_rel hxy
    · rcases hcross with hcross | hcross
      · rcases hcross with ⟨rfl, rfl⟩
        simpa [hf0, hf1, hcopy₀, hcopy₁] using huv
      · rcases hcross with ⟨rfl, rfl⟩
        simpa [hf0, hf1, hcopy₀, hcopy₁] using huv.symm
  have hinj : ∀ c, Function.Injective (fun w : L575U.SVert 3 => f (L575U.kCopy c w)) := by
    intro c
    fin_cases c
    · intro x y hxy
      apply copy₀.injective'
      calc
        copy₀.toHom x = f (L575U.kCopy 0 x) := (hf0 x).symm
        _ = f (L575U.kCopy 0 y) := hxy
        _ = copy₀.toHom y := hf0 y
    · intro x y hxy
      apply copy₁.injective'
      calc
        copy₁.toHom x = f (L575U.kCopy 1 x) := (hf1 x).symm
        _ = f (L575U.kCopy 1 y) := hxy
        _ = copy₁.toHom y := hf1 y
  have hmapColor : ∀ a, χ (f a) = if L575U.kColor a then 1 else 0 := by
    intro a
    rcases a with ⟨c, w⟩
    fin_cases c
    · change χ (f (L575U.kCopy 0 w)) =
        (if L575U.kColor (L575U.kCopy 0 w) then 1 else 0)
      rw [hf0]
      simpa [L575U.kColor, L575U.kCopy] using hcol₀ w
    · change χ (f (L575U.kCopy 1 w)) =
        (if L575U.kColor (L575U.kCopy 1 w) then 1 else 0)
      rw [hf1]
      have hx : χ (copy₁.toHom w) = Equiv.swap 0 1 (χ' (copy₁.toHom w)) := by
        simp [χ']
      rw [hx, hcol₁ w]
      cases w <;>
        simp [L575U.kColor, L575U.kCopy, L575U.sColor,
          Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hcolor : ∀ a b, f a = f b → L575U.kColor a = L575U.kColor b := by
    intro a b hab
    have hχ := congrArg χ hab
    rw [hmapColor a, hmapColor b] at hχ
    by_cases ha : L575U.kColor a <;> by_cases hb : L575U.kColor b <;> simp_all
  obtain ⟨A, hAmem, hcontain⟩ := L575U.kFamily_templateMap_to_containment G f hedge hinj hcolor
  exact (hK A hAmem) hcontain

end L575K

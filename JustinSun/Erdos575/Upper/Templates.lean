import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Fintype.EquivFin
import JustinSun.Erdos575.Statement

/-! Template carriers for the subdivision patterns used in the upper-bound proof. -/

namespace L575U

abbrev FinGraph := JustinSun.Erdos575.FinGraph

inductive SVert (k : ℕ) where
  | base : Fin 3 → SVert k
  | center : Fin k → SVert k
  | sub : Fin 3 → Fin k → SVert k
  deriving DecidableEq

def sEquiv {k : ℕ} : SVert k ≃ Fin 3 ⊕ Fin k ⊕ (Fin 3 × Fin k) where
  toFun := fun
    | .base i => Sum.inl i
    | .center j => Sum.inr (Sum.inl j)
    | .sub i j => Sum.inr (Sum.inr (i, j))
  invFun := fun
    | Sum.inl i => .base i
    | Sum.inr (Sum.inl j) => .center j
    | Sum.inr (Sum.inr (i, j)) => .sub i j
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x with
    | inl i => rfl
    | inr x => cases x with
      | inl j => rfl
      | inr p => rfl

noncomputable instance (k : ℕ) : Fintype (SVert k) :=
  Fintype.ofEquiv (Fin 3 ⊕ Fin k ⊕ (Fin 3 × Fin k)) sEquiv.symm

def sColor {k : ℕ} : SVert k → Bool
  | .base _ => false
  | .center _ => false
  | .sub _ _ => true

def sAdj {k : ℕ} (u v : SVert k) : Prop :=
  (∃ i j, u = .base i ∧ v = .sub i j) ∨
  (∃ i j, v = .base i ∧ u = .sub i j) ∨
  (∃ i j, u = .center j ∧ v = .sub i j) ∨
  (∃ i j, v = .center j ∧ u = .sub i j)

instance (k : ℕ) : DecidableRel (@sAdj k) := by
  intro u v
  unfold sAdj
  infer_instance

theorem card_sVert (k : ℕ) : Fintype.card (SVert k) = 3 + 4 * k := by
  rw [Fintype.card_congr sEquiv]
  simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

theorem sAdj_oppositeColors {k : ℕ} {u v : SVert k} (h : sAdj u v) :
    sColor u ≠ sColor v := by
  rcases h with h | h | h | h
  · rcases h with ⟨i,j,rfl,rfl⟩; simp [sColor]
  · rcases h with ⟨i,j,rfl,rfl⟩; simp [sColor]
  · rcases h with ⟨i,j,rfl,rfl⟩; simp [sColor]
  · rcases h with ⟨i,j,rfl,rfl⟩; simp [sColor]

def SGraph (k : ℕ) : SimpleGraph (SVert k) where
  Adj := sAdj
  symm := by
    constructor
    intro a b h
    simp only [sAdj] at *
    aesop
  loopless := by
    constructor
    intro a h
    simp only [sAdj] at h
    aesop

instance (k : ℕ) : DecidableRel (SGraph k).Adj := by
  intro u v
  exact inferInstanceAs (Decidable (sAdj u v))

theorem sGraph_bipartite (k : ℕ) : (SGraph k).IsBipartite := by
  apply SimpleGraph.IsBipartiteWith.isBipartite
    (s := {v : SVert k | sColor v = false})
    (t := {v : SVert k | sColor v = true})
  refine ⟨?_, ?_⟩
  · simp only [Set.disjoint_left, Set.mem_setOf_eq]
    intro v hv ht
    cases sColor v <;> simp_all
  · intro a b hab
    have hc := sAdj_oppositeColors hab
    by_cases ha : sColor a = false
    · have hb : sColor b = true := by
        cases h : sColor b <;> simp_all
      exact Or.inl ⟨ha, hb⟩
    · have ha' : sColor a = true := by
        cases h : sColor a <;> simp_all
      have hb : sColor b = false := by
        cases h : sColor b <;> simp_all
      exact Or.inr ⟨ha', hb⟩

inductive J0Vert where
  | x
  | xp
  | y
  | z
  | lam
  | c : Fin 2 → Fin 2 → J0Vert
  | s : Fin 2 → Fin 3 → Fin 2 → J0Vert
  deriving DecidableEq

def jEquiv : J0Vert ≃ Fin 5 ⊕ (Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 3 × Fin 2) where
  toFun := fun
    | .x => Sum.inl 0
    | .xp => Sum.inl 1
    | .y => Sum.inl 2
    | .z => Sum.inl 3
    | .lam => Sum.inl 4
    | .c i j => Sum.inr (Sum.inl (i,j))
    | .s c b j => Sum.inr (Sum.inr (c,b,j))
  invFun := fun
    | Sum.inl i => if i.val = 0 then .x else if i.val = 1 then .xp else
        if i.val = 2 then .y else if i.val = 3 then .z else .lam
    | Sum.inr (Sum.inl (c,b)) => .c c b
    | Sum.inr (Sum.inr (c,b,j)) => .s c b j
  left_inv := by intro v; cases v <;> rfl
  right_inv := by intro x; cases x with
    | inl i => fin_cases i <;> rfl
    | inr x => cases x <;> rfl

noncomputable instance : Fintype J0Vert :=
  Fintype.ofEquiv (Fin 5 ⊕ (Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 3 × Fin 2)) jEquiv.symm

theorem card_s2 : Fintype.card (SVert 2) = 11 := by norm_num [card_sVert]

theorem card_s3 : Fintype.card (SVert 3) = 15 := by norm_num [card_sVert]

theorem card_j0Vert : Fintype.card J0Vert = 21 := by
  rw [Fintype.card_congr jEquiv]
  simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]

abbrev K0Vert := Fin 2 × SVert 3

theorem card_k0Vert : Fintype.card K0Vert = 30 := by
  simp [K0Vert, card_sVert]

def jCopy (copy : Fin 2) : SVert 2 → J0Vert
  | .base i => if i.val = 0 then (if copy.val = 0 then .x else .xp)
      else if i.val = 1 then .y else .z
  | .center j => .c copy j
  | .sub b j => .s copy b j

def kCopy (copy : Fin 2) (w : SVert 3) : K0Vert := (copy, w)

def jColor : J0Vert → Bool
  | .x | .xp | .y | .z | .c _ _ => false
  | .lam | .s _ _ _ => true

def kColor (v : K0Vert) : Bool :=
  if v.1.val = 0 then sColor v.2 else !(sColor v.2)

theorem jCopy_color (copy : Fin 2) (v : SVert 2) :
    jColor (jCopy copy v) = sColor v := by
  cases v with
  | base i => fin_cases i <;> by_cases hc : copy.val = 0 <;>
      simp [jCopy, jColor, sColor, hc]
  | center j => simp [jCopy, jColor, sColor]
  | sub i j => simp [jCopy, jColor, sColor]

theorem kCopy_color_zero (v : SVert 3) : kColor (kCopy 0 v) = sColor v := by
  simp [kColor, kCopy]

theorem kCopy_color_one (v : SVert 3) : kColor (kCopy 1 v) = !(sColor v) := by
  simp [kColor, kCopy]

theorem jCopy_injective (copy : Fin 2) : Function.Injective (jCopy copy) := by
  intro a b h
  cases a with
  | base i =>
    cases b with
    | base j => fin_cases i <;> fin_cases j <;> simp [jCopy] at h ⊢ <;>
        split_ifs at h <;> simp_all [jCopy]
    | center j => simp [jCopy] at h ⊢ <;> split_ifs at h <;> simp_all [jCopy]
    | sub j l => simp [jCopy] at h ⊢ <;> split_ifs at h <;> simp_all [jCopy]
  | center i =>
    cases b with
    | base j => simp [jCopy] at h ⊢ <;> split_ifs at h <;> simp_all [jCopy]
    | center j => simpa [jCopy] using h
    | sub j l => simp [jCopy] at h ⊢ <;> split_ifs at h <;> simp_all [jCopy]
  | sub i j =>
    cases b with
    | base t => simp [jCopy] at h ⊢ <;> split_ifs at h <;> simp_all [jCopy]
    | center t => simp [jCopy] at h ⊢
    | sub t l => simpa [jCopy] using h

theorem kCopy_injective (copy : Fin 2) : Function.Injective (kCopy copy) := by
  intro a b h
  exact congrArg Prod.snd h

def J0Adj (a b : J0Vert) : Prop :=
  (∃ copy u v, (SGraph 2).Adj u v ∧ a = jCopy copy u ∧ b = jCopy copy v) ∨
  ((a = .lam ∧ b = .x) ∨ (a = .x ∧ b = .lam)) ∨
  ((a = .lam ∧ b = .xp) ∨ (a = .xp ∧ b = .lam))

def K0Adj (a b : K0Vert) : Prop :=
  (∃ copy u v, (SGraph 3).Adj u v ∧ a = kCopy copy u ∧ b = kCopy copy v) ∨
  ((a = kCopy 0 (.center 0) ∧ b = kCopy 1 (.center 0)) ∨
   (a = kCopy 1 (.center 0) ∧ b = kCopy 0 (.center 0)))

theorem jAdj_oppositeColors {a b : J0Vert} (h : J0Adj a b) : jColor a ≠ jColor b := by
  rcases h with ⟨copy, u, v, hadj, rfl, rfl⟩ | h
  · have hc := sAdj_oppositeColors hadj
    intro heq
    apply hc
    rw [← jCopy_color copy u, ← jCopy_color copy v]
    exact heq
  · rcases h with ⟨h | h⟩ | ⟨h | h⟩
    · rcases h with ⟨rfl, rfl⟩; decide
    · rcases h with ⟨rfl, rfl⟩; decide
    · rcases h with ⟨rfl, rfl⟩; decide
    · rcases h with ⟨rfl, rfl⟩; decide

theorem kAdj_oppositeColors {a b : K0Vert} (h : K0Adj a b) : kColor a ≠ kColor b := by
  rcases h with ⟨copy, u, v, hadj, rfl, rfl⟩ | h
  · have hc := sAdj_oppositeColors hadj
    fin_cases copy <;> simp [kColor, kCopy] at hc ⊢ <;>
      cases hu : sColor u <;> cases hv : sColor v <;> simp_all
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩; decide
    · rcases h with ⟨rfl, rfl⟩; decide

def J0Graph : SimpleGraph J0Vert where
  Adj := J0Adj
  symm := by
    constructor
    intro a b h
    rcases h with ⟨copy, u, v, hadj, rfl, rfl⟩ | h
    · exact Or.inl ⟨copy, v, u, hadj.symm, rfl, rfl⟩
    · rcases h with h | h
      · rcases h with h | h
        · rcases h with ⟨rfl, rfl⟩; exact Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩))
        · rcases h with ⟨rfl, rfl⟩; exact Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))
      · rcases h with h | h
        · rcases h with ⟨rfl, rfl⟩; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
        · rcases h with ⟨rfl, rfl⟩; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  loopless := by
    constructor
    intro a h
    exact (jAdj_oppositeColors h) rfl

def K0Graph : SimpleGraph K0Vert where
  Adj := K0Adj
  symm := by
    constructor
    intro a b h
    rcases h with ⟨copy, u, v, hadj, rfl, rfl⟩ | h
    · exact Or.inl ⟨copy, v, u, hadj.symm, rfl, rfl⟩
    · rcases h with h | h
      · rcases h with ⟨rfl, rfl⟩; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · rcases h with ⟨rfl, rfl⟩; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  loopless := by
    constructor
    intro a h
    exact (kAdj_oppositeColors h) rfl

def jCopyHom (copy : Fin 2) : SGraph 2 →g J0Graph where
  toFun := jCopy copy
  map_rel' := by
    intro a b hab
    exact Or.inl ⟨copy, a, b, hab, rfl, rfl⟩

def jCopyCopy (copy : Fin 2) : SimpleGraph.Copy (SGraph 2) J0Graph :=
  ⟨jCopyHom copy, jCopy_injective copy⟩

def kCopyHom (copy : Fin 2) : SGraph 3 →g K0Graph where
  toFun := kCopy copy
  map_rel' := by
    intro a b hab
    exact Or.inl ⟨copy, a, b, hab, rfl, rfl⟩

def kCopyCopy (copy : Fin 2) : SimpleGraph.Copy (SGraph 3) K0Graph :=
  ⟨kCopyHom copy, kCopy_injective copy⟩

theorem j0Graph_bipartite : J0Graph.IsBipartite := by
  apply SimpleGraph.IsBipartiteWith.isBipartite
    (s := {v : J0Vert | jColor v = false}) (t := {v : J0Vert | jColor v = true})
  refine ⟨?_, ?_⟩
  · simp only [Set.disjoint_left, Set.mem_setOf_eq]
    intro v hv ht
    cases jColor v <;> simp_all
  · intro a b hab
    have hc := jAdj_oppositeColors hab
    by_cases ha : jColor a = false
    · have hb : jColor b = true := by cases h : jColor b <;> simp_all
      exact Or.inl ⟨ha, hb⟩
    · have ha' : jColor a = true := by cases h : jColor a <;> simp_all
      have hb : jColor b = false := by cases h : jColor b <;> simp_all
      exact Or.inr ⟨ha', hb⟩

theorem k0Graph_bipartite : K0Graph.IsBipartite := by
  apply SimpleGraph.IsBipartiteWith.isBipartite
    (s := {v : K0Vert | kColor v = false}) (t := {v : K0Vert | kColor v = true})
  refine ⟨?_, ?_⟩
  · simp only [Set.disjoint_left, Set.mem_setOf_eq]
    intro v hv ht
    cases kColor v <;> simp_all
  · intro a b hab
    have hc := kAdj_oppositeColors hab
    by_cases ha : kColor a = false
    · have hb : kColor b = true := by cases h : kColor b <;> simp_all
      exact Or.inl ⟨ha, hb⟩
    · have ha' : kColor a = true := by cases h : kColor a <;> simp_all
      have hb : kColor b = false := by cases h : kColor b <;> simp_all
      exact Or.inr ⟨ha', hb⟩

def s2Cycle : (SGraph 2).Walk (.base 0) (.base 0) :=
  .cons (by change sAdj _ _; exact Or.inl ⟨0, 0, rfl, rfl⟩) <|
  .cons (by change sAdj _ _; exact Or.inr (Or.inr (Or.inr ⟨0, 0, rfl, rfl⟩))) <|
  .cons (by change sAdj _ _; exact Or.inr (Or.inr (Or.inl ⟨1, 0, rfl, rfl⟩))) <|
  .cons (by change sAdj _ _; exact Or.inr (Or.inl ⟨1, 0, rfl, rfl⟩)) <|
  .cons (by change sAdj _ _; exact Or.inl ⟨1, 1, rfl, rfl⟩) <|
  .cons (by change sAdj _ _; exact Or.inr (Or.inr (Or.inr ⟨1, 1, rfl, rfl⟩))) <|
  .cons (by change sAdj _ _; exact Or.inr (Or.inr (Or.inl ⟨0, 1, rfl, rfl⟩))) <|
  .cons (by change sAdj _ _; exact Or.inr (Or.inl ⟨0, 1, rfl, rfl⟩)) .nil

def s3Cycle : (SGraph 3).Walk (.base 0) (.base 0) :=
  .cons (by change sAdj _ _; exact Or.inl ⟨0, 0, rfl, rfl⟩) <|
  .cons (by change sAdj _ _; exact Or.inr (Or.inr (Or.inr ⟨0, 0, rfl, rfl⟩))) <|
  .cons (by change sAdj _ _; exact Or.inr (Or.inr (Or.inl ⟨1, 0, rfl, rfl⟩))) <|
  .cons (by change sAdj _ _; exact Or.inr (Or.inl ⟨1, 0, rfl, rfl⟩)) <|
  .cons (by change sAdj _ _; exact Or.inl ⟨1, 1, rfl, rfl⟩) <|
  .cons (by change sAdj _ _; exact Or.inr (Or.inr (Or.inr ⟨1, 1, rfl, rfl⟩))) <|
  .cons (by change sAdj _ _; exact Or.inr (Or.inr (Or.inl ⟨0, 1, rfl, rfl⟩))) <|
  .cons (by change sAdj _ _; exact Or.inr (Or.inl ⟨0, 1, rfl, rfl⟩)) .nil

theorem s2Cycle_isCycle : s2Cycle.IsCycle := by
  simp [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def, s2Cycle]

theorem s2_hasCycle : ¬ (SGraph 2).IsAcyclic := by
  intro ha
  exact ha s2Cycle s2Cycle_isCycle

theorem s3Cycle_isCycle : s3Cycle.IsCycle := by
  simp [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def, s3Cycle]

theorem s3_hasCycle : ¬ (SGraph 3).IsAcyclic := by
  intro ha
  exact ha s3Cycle s3Cycle_isCycle

/-- Frozen cycle obligation from blueprint item 1 for the subdivision templates. -/
def subdivisionCycleFacts : Prop :=
  ¬ (SGraph 2).IsAcyclic ∧ ¬ (SGraph 3).IsAcyclic

theorem subdivisionCycleFacts_proved : subdivisionCycleFacts :=
  ⟨s2_hasCycle, s3_hasCycle⟩

def quotientAdj {V : Type*} (T : SimpleGraph V) {m : ℕ}
    (π : V → Fin m) (i j : Fin m) : Prop :=
  i ≠ j ∧ ∃ a b, π a = i ∧ π b = j ∧ T.Adj a b

def quotientGraph {V : Type*} (T : SimpleGraph V) (m : ℕ) (π : V → Fin m) :
    SimpleGraph (Fin m) where
  Adj := quotientAdj T π
  symm := by
    constructor
    intro i j h
    rcases h with ⟨hne, a, b, ha, hb, hab⟩
    exact ⟨hne.symm, b, a, hb, ha, hab.symm⟩
  loopless := by
    constructor
    intro i h
    exact h.1 rfl

abbrev JParam := Σ m : Fin (Fintype.card J0Vert + 1), J0Vert → Fin m.val
abbrev KParam := Σ m : Fin (Fintype.card K0Vert + 1), K0Vert → Fin m.val

open Classical in
def JAdmissible (p : JParam) : Prop :=
  Function.Surjective p.2 ∧
  (∀ a b, p.2 a = p.2 b → jColor a = jColor b) ∧
  (∀ copy, Function.Injective (fun w : SVert 2 => p.2 (jCopy copy w))) ∧
  p.2 .x ≠ p.2 .xp

open Classical in
def KAdmissible (p : KParam) : Prop :=
  Function.Surjective p.2 ∧
  (∀ a b, p.2 a = p.2 b → kColor a = kColor b) ∧
  ∀ copy, Function.Injective (fun w : SVert 3 => p.2 (kCopy copy w))

def jQuotient (p : JParam) : FinGraph :=
  ⟨p.1.val, quotientGraph J0Graph p.1.val p.2⟩

def kQuotient (p : KParam) : FinGraph :=
  ⟨p.1.val, quotientGraph K0Graph p.1.val p.2⟩

def jQuotientSubcopy (p : JParam) (hp : JAdmissible p) (copy : Fin 2) :
    SimpleGraph.Copy (SGraph 2) (quotientGraph J0Graph p.1.val p.2) where
  toHom := {
    toFun := fun w => p.2 (jCopy copy w)
    map_rel' := by
      intro u v huv
      have huv' : u ≠ v := by
        intro heq
        subst v
        exact (SGraph 2).loopless.irrefl _ huv
      have hneq : p.2 (jCopy copy u) ≠ p.2 (jCopy copy v) := by
        intro hEq
        exact huv' (hp.2.2.1 copy hEq)
      exact ⟨hneq, jCopy copy u, jCopy copy v, rfl, rfl,
        (jCopyHom copy).map_rel huv⟩
  }
  injective' := fun u v h => hp.2.2.1 copy h

def kQuotientSubcopy (p : KParam) (hp : KAdmissible p) (copy : Fin 2) :
    SimpleGraph.Copy (SGraph 3) (quotientGraph K0Graph p.1.val p.2) where
  toHom := {
    toFun := fun w => p.2 (kCopy copy w)
    map_rel' := by
      intro u v huv
      have huv' : u ≠ v := by
        intro heq
        subst v
        exact (SGraph 3).loopless.irrefl _ huv
      have hneq : p.2 (kCopy copy u) ≠ p.2 (kCopy copy v) := by
        intro hEq
        exact huv' (hp.2.2 copy hEq)
      exact ⟨hneq, kCopy copy u, kCopy copy v, rfl, rfl,
        (kCopyHom copy).map_rel huv⟩
  }
  injective' := fun u v h => hp.2.2 copy h

noncomputable def jQuotientColor (p : JParam) (hp : JAdmissible p) (i : Fin p.1.val) : Bool :=
  jColor (Classical.choose (hp.1 i))

theorem jQuotientColor_edge {p : JParam} (hp : JAdmissible p)
    {i j : Fin p.1.val} (hij : (quotientGraph J0Graph p.1.val p.2).Adj i j) :
    jQuotientColor p hp i ≠ jQuotientColor p hp j := by
  rcases hij with ⟨_, a, b, ha, hb, hab⟩
  have hia : jQuotientColor p hp i = jColor a := by
    unfold jQuotientColor
    apply hp.2.1
    rw [Classical.choose_spec (hp.1 i), ha]
  have hjb : jQuotientColor p hp j = jColor b := by
    unfold jQuotientColor
    apply hp.2.1
    rw [Classical.choose_spec (hp.1 j), hb]
  intro heq
  exact jAdj_oppositeColors hab (hia.symm.trans (heq.trans hjb))

noncomputable def kQuotientColor (p : KParam) (hp : KAdmissible p) (i : Fin p.1.val) : Bool :=
  kColor (Classical.choose (hp.1 i))

theorem kQuotientColor_edge {p : KParam} (hp : KAdmissible p)
    {i j : Fin p.1.val} (hij : (quotientGraph K0Graph p.1.val p.2).Adj i j) :
    kQuotientColor p hp i ≠ kQuotientColor p hp j := by
  rcases hij with ⟨_, a, b, ha, hb, hab⟩
  have hia : kQuotientColor p hp i = kColor a := by
    unfold kQuotientColor
    apply hp.2.1
    rw [Classical.choose_spec (hp.1 i), ha]
  have hjb : kQuotientColor p hp j = kColor b := by
    unfold kQuotientColor
    apply hp.2.1
    rw [Classical.choose_spec (hp.1 j), hb]
  intro heq
  exact kAdj_oppositeColors hab (hia.symm.trans (heq.trans hjb))

theorem jQuotient_bipartite (p : JParam) (hp : JAdmissible p) :
    (quotientGraph J0Graph p.1.val p.2).IsBipartite := by
  apply SimpleGraph.IsBipartiteWith.isBipartite
    (s := {i : Fin p.1.val | jQuotientColor p hp i = false})
    (t := {i : Fin p.1.val | jQuotientColor p hp i = true})
  refine ⟨?_, ?_⟩
  · simp only [Set.disjoint_left, Set.mem_setOf_eq]
    intro i hi ht
    cases jQuotientColor p hp i <;> simp_all
  · intro i j hij
    have hc := jQuotientColor_edge hp hij
    by_cases hi : jQuotientColor p hp i = false
    · have hj : jQuotientColor p hp j = true := by
        cases h : jQuotientColor p hp j <;> simp_all
      exact Or.inl ⟨hi, hj⟩
    · have hi' : jQuotientColor p hp i = true := by
        cases h : jQuotientColor p hp i <;> simp_all
      have hj : jQuotientColor p hp j = false := by
        cases h : jQuotientColor p hp j <;> simp_all
      exact Or.inr ⟨hi', hj⟩

theorem kQuotient_bipartite (p : KParam) (hp : KAdmissible p) :
    (quotientGraph K0Graph p.1.val p.2).IsBipartite := by
  apply SimpleGraph.IsBipartiteWith.isBipartite
    (s := {i : Fin p.1.val | kQuotientColor p hp i = false})
    (t := {i : Fin p.1.val | kQuotientColor p hp i = true})
  refine ⟨?_, ?_⟩
  · simp only [Set.disjoint_left, Set.mem_setOf_eq]
    intro i hi ht
    cases kQuotientColor p hp i <;> simp_all
  · intro i j hij
    have hc := kQuotientColor_edge hp hij
    by_cases hi : kQuotientColor p hp i = false
    · have hj : kQuotientColor p hp j = true := by
        cases h : kQuotientColor p hp j <;> simp_all
      exact Or.inl ⟨hi, hj⟩
    · have hi' : kQuotientColor p hp i = true := by
        cases h : kQuotientColor p hp i <;> simp_all
      have hj : kQuotientColor p hp j = false := by
        cases h : kQuotientColor p hp j <;> simp_all
      exact Or.inr ⟨hi', hj⟩

theorem jQuotient_notAcyclic (p : JParam) (hp : JAdmissible p) :
    ¬ (quotientGraph J0Graph p.1.val p.2).IsAcyclic := by
  intro ha
  let c := jQuotientSubcopy p hp 0
  have hc : (s2Cycle.map c.toHom).IsCycle :=
    (SimpleGraph.Walk.isCycle_map_iff_of_injective c.injective).mpr s2Cycle_isCycle
  exact ha (s2Cycle.map c.toHom) hc

theorem kQuotient_notAcyclic (p : KParam) (hp : KAdmissible p) :
    ¬ (quotientGraph K0Graph p.1.val p.2).IsAcyclic := by
  intro ha
  let c := kQuotientSubcopy p hp 0
  have hc : (s3Cycle.map c.toHom).IsCycle :=
    (SimpleGraph.Walk.isCycle_map_iff_of_injective c.injective).mpr s3Cycle_isCycle
  exact ha (s3Cycle.map c.toHom) hc

noncomputable def J : Finset FinGraph := by
  classical
  exact (Finset.univ.filter JAdmissible).image jQuotient

noncomputable def K : Finset FinGraph := by
  classical
  exact (Finset.univ.filter KAdmissible).image kQuotient

def C4Graph : FinGraph := ⟨4, SimpleGraph.cycleGraph 4⟩
def C6Graph : FinGraph := ⟨6, SimpleGraph.cycleGraph 6⟩

noncomputable def forbiddenFamily : Finset FinGraph := by
  classical
  exact insert C4Graph (insert C6Graph (J ∪ K))

theorem forbiddenFamily_nonempty : forbiddenFamily.Nonempty := by
  refine ⟨C4Graph, ?_⟩
  simp [forbiddenFamily]

theorem c4_bipartite : (SimpleGraph.cycleGraph 4).IsBipartite := by
  exact ⟨(SimpleGraph.cycleGraph 4).recolorOfEquiv finTwoEquiv.symm
    (SimpleGraph.cycleGraph.bicoloring_of_even 4 ⟨2, rfl⟩)⟩

theorem c6_bipartite : (SimpleGraph.cycleGraph 6).IsBipartite := by
  exact ⟨(SimpleGraph.cycleGraph 6).recolorOfEquiv finTwoEquiv.symm
    (SimpleGraph.cycleGraph.bicoloring_of_even 6 ⟨3, rfl⟩)⟩

theorem c4_notAcyclic : ¬ (SimpleGraph.cycleGraph 4).IsAcyclic := by
  intro ha
  exact ha (SimpleGraph.cycleGraph.cycle 1) SimpleGraph.cycleGraph.isCycle_cycle

theorem c6_notAcyclic : ¬ (SimpleGraph.cycleGraph 6).IsAcyclic := by
  intro ha
  exact ha (SimpleGraph.cycleGraph.cycle 3) SimpleGraph.cycleGraph.isCycle_cycle

set_option maxRecDepth 4096 in
theorem J_members_bipartite : ∀ A ∈ J, A.2.IsBipartite := by
  classical
  intro A hA
  rcases Finset.mem_image.mp hA with ⟨p, hp, rfl⟩
  exact jQuotient_bipartite p (Finset.mem_filter.mp hp).2

set_option maxRecDepth 4096 in
theorem J_members_notAcyclic : ∀ A ∈ J, ¬ A.2.IsAcyclic := by
  classical
  intro A hA
  rcases Finset.mem_image.mp hA with ⟨p, hp, rfl⟩
  exact jQuotient_notAcyclic p (Finset.mem_filter.mp hp).2

set_option maxRecDepth 4096 in
theorem K_members_bipartite : ∀ A ∈ K, A.2.IsBipartite := by
  classical
  intro A hA
  rcases Finset.mem_image.mp hA with ⟨p, hp, rfl⟩
  exact kQuotient_bipartite p (Finset.mem_filter.mp hp).2

set_option maxRecDepth 4096 in
theorem K_members_notAcyclic : ∀ A ∈ K, ¬ A.2.IsAcyclic := by
  classical
  intro A hA
  rcases Finset.mem_image.mp hA with ⟨p, hp, rfl⟩
  exact kQuotient_notAcyclic p (Finset.mem_filter.mp hp).2

set_option maxRecDepth 4096 in
theorem forbiddenFamily_members_structural : ∀ A ∈ forbiddenFamily,
    A.2.IsBipartite ∧ ¬ A.2.IsAcyclic := by
  classical
  intro A hA
  simp only [forbiddenFamily, Finset.mem_insert, Finset.mem_union] at hA
  rcases hA with hA | hA | hA | hA
  · subst A
    exact ⟨c4_bipartite, c4_notAcyclic⟩
  · subst A
    exact ⟨c6_bipartite, c6_notAcyclic⟩
  · exact ⟨J_members_bipartite A hA, J_members_notAcyclic A hA⟩
  · exact ⟨K_members_bipartite A hA, K_members_notAcyclic A hA⟩

theorem jQuotient_copy_to_templateMap {W : Type*} [Fintype W] [DecidableEq W]
    (p : JParam) (hp : JAdmissible p) (G : SimpleGraph W)
    (hcopy : SimpleGraph.IsContained (jQuotient p).2 G) :
    ∃ f : J0Vert → W,
      (∀ a b, J0Graph.Adj a b → G.Adj (f a) (f b)) ∧
      (∀ copy, Function.Injective (fun w : SVert 2 => f (jCopy copy w))) ∧
      (∀ a b, f a = f b → jColor a = jColor b) ∧ f .x ≠ f .xp := by
  rcases hcopy with ⟨c⟩
  refine ⟨fun v => c (p.2 v), ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have hcolors := jAdj_oppositeColors hab
    have hneq : p.2 a ≠ p.2 b := by
      intro heq
      apply hcolors
      exact hp.2.1 a b heq
    apply c.toHom.map_rel
    exact ⟨hneq, a, b, rfl, rfl, hab⟩
  · intro copy a b hab
    apply hp.2.2.1 copy
    exact c.injective hab
  · intro a b hab
    exact hp.2.1 a b (c.injective hab)
  · intro hab
    exact hp.2.2.2 (c.injective hab)

theorem kQuotient_copy_to_templateMap {W : Type*} [Fintype W] [DecidableEq W]
    (p : KParam) (hp : KAdmissible p) (G : SimpleGraph W)
    (hcopy : SimpleGraph.IsContained (kQuotient p).2 G) :
    ∃ f : K0Vert → W,
      (∀ a b, K0Graph.Adj a b → G.Adj (f a) (f b)) ∧
      (∀ copy, Function.Injective (fun w : SVert 3 => f (kCopy copy w))) ∧
      (∀ a b, f a = f b → kColor a = kColor b) := by
  rcases hcopy with ⟨c⟩
  refine ⟨fun v => c (p.2 v), ?_, ?_, ?_⟩
  · intro a b hab
    have hcolors := kAdj_oppositeColors hab
    have hneq : p.2 a ≠ p.2 b := by
      intro heq
      apply hcolors
      exact hp.2.1 a b heq
    apply c.toHom.map_rel
    exact ⟨hneq, a, b, rfl, rfl, hab⟩
  · intro copy a b hab
    apply hp.2.2 copy
    exact c.injective hab
  · intro a b hab
    exact hp.2.1 a b (c.injective hab)

set_option maxRecDepth 4096 in
theorem jFamily_containment_to_templateMap {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (h : ∃ A ∈ J, SimpleGraph.IsContained A.2 G) :
    ∃ f : J0Vert → W,
      (∀ a b, J0Graph.Adj a b → G.Adj (f a) (f b)) ∧
      (∀ copy, Function.Injective (fun w : SVert 2 => f (jCopy copy w))) ∧
      (∀ a b, f a = f b → jColor a = jColor b) ∧ f .x ≠ f .xp := by
  classical
  rcases h with ⟨A, hA, hcopy⟩
  rcases Finset.mem_image.mp hA with ⟨p, hp, rfl⟩
  exact jQuotient_copy_to_templateMap p (Finset.mem_filter.mp hp).2 G hcopy

set_option maxRecDepth 4096 in
theorem kFamily_containment_to_templateMap {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (h : ∃ A ∈ K, SimpleGraph.IsContained A.2 G) :
    ∃ f : K0Vert → W,
      (∀ a b, K0Graph.Adj a b → G.Adj (f a) (f b)) ∧
      (∀ copy, Function.Injective (fun w : SVert 3 => f (kCopy copy w))) ∧
      (∀ a b, f a = f b → kColor a = kColor b) := by
  classical
  rcases h with ⟨A, hA, hcopy⟩
  rcases Finset.mem_image.mp hA with ⟨p, hp, rfl⟩
  exact kQuotient_copy_to_templateMap p (Finset.mem_filter.mp hp).2 G hcopy

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem jFamily_templateMap_to_containment {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W)
    (f : J0Vert → W)
    (hedge : ∀ a b, J0Graph.Adj a b → G.Adj (f a) (f b))
    (hinj : ∀ copy, Function.Injective (fun w : SVert 2 => f (jCopy copy w)))
    (hcolor : ∀ a b, f a = f b → jColor a = jColor b)
    (hxx : f .x ≠ f .xp) :
    ∃ A ∈ J, SimpleGraph.IsContained A.2 G := by
  classical
  let R := Set.range f
  letI : Fintype R := Fintype.ofFinite R
  let m := Fintype.card R
  have hm : m ≤ Fintype.card J0Vert := Fintype.card_range_le f
  let e : R ≃ Fin m := Fintype.equivFin R
  let π : J0Vert → Fin m := fun a => e ⟨f a, ⟨a, rfl⟩⟩
  have hπ : ∀ a b, π a = π b ↔ f a = f b := by
    intro a b
    constructor
    · intro h
      change e ⟨f a, ⟨a, rfl⟩⟩ = e ⟨f b, ⟨b, rfl⟩⟩ at h
      have heq := e.injective h
      exact congrArg Subtype.val heq
    · intro h
      exact congrArg e (Subtype.ext h)
  let p : JParam := ⟨⟨m, Nat.lt_succ_of_le hm⟩, π⟩
  have hp : JAdmissible p := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      let r : R := e.symm i
      rcases r.2 with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      have hr : (⟨f a, ⟨a, rfl⟩⟩ : R) = r := Subtype.ext ha
      change e ⟨f a, ⟨a, rfl⟩⟩ = i
      rw [hr]
      exact e.apply_symm_apply i
    · intro a b hab
      exact hcolor a b (hπ a b |>.mp hab)
    · intro copy a b hab
      apply hinj copy
      exact (hπ _ _).mp hab
    · intro hab
      exact hxx ((hπ .x .xp).mp hab)
  have hπsurj := hp.1
  let rep (i : Fin m) : J0Vert := Classical.choose (hπsurj i)
  have hrep (i : Fin m) : π (rep i) = i := Classical.choose_spec (hπsurj i)
  let qhom : (quotientGraph J0Graph m π) →g G := {
    toFun := fun i => f (rep i)
    map_rel' := by
      intro i j hij
      rcases hij with ⟨hne, a, b, ha, hb, hadj⟩
      have hfa : f (rep i) = f a := (hπ _ _).mp (by rw [hrep, ha])
      have hfb : f (rep j) = f b := (hπ _ _).mp (by rw [hrep, hb])
      rw [hfa, hfb]
      exact hedge a b hadj
  }
  have qinj : Function.Injective qhom := by
    intro i j hij
    have hpeq : π (rep i) = π (rep j) := (hπ _ _).2 hij
    rw [hrep, hrep] at hpeq
    exact hpeq
  let qcopy : SimpleGraph.Copy (quotientGraph J0Graph m π) G := ⟨qhom, qinj⟩
  have hpIn : p ∈ Finset.univ.filter JAdmissible :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
  have hJ : jQuotient p ∈ J := Finset.mem_image.mpr ⟨p, hpIn, rfl⟩
  exact ⟨jQuotient p, hJ, ⟨qcopy⟩⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem kFamily_templateMap_to_containment {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W)
    (f : K0Vert → W)
    (hedge : ∀ a b, K0Graph.Adj a b → G.Adj (f a) (f b))
    (hinj : ∀ copy, Function.Injective (fun w : SVert 3 => f (kCopy copy w)))
    (hcolor : ∀ a b, f a = f b → kColor a = kColor b) :
    ∃ A ∈ K, SimpleGraph.IsContained A.2 G := by
  classical
  let R := Set.range f
  letI : Fintype R := Fintype.ofFinite R
  let m := Fintype.card R
  have hm : m ≤ Fintype.card K0Vert := Fintype.card_range_le f
  let e : R ≃ Fin m := Fintype.equivFin R
  let π : K0Vert → Fin m := fun a => e ⟨f a, ⟨a, rfl⟩⟩
  have hπ : ∀ a b, π a = π b ↔ f a = f b := by
    intro a b
    constructor
    · intro h
      change e ⟨f a, ⟨a, rfl⟩⟩ = e ⟨f b, ⟨b, rfl⟩⟩ at h
      have heq := e.injective h
      exact congrArg Subtype.val heq
    · intro h
      exact congrArg e (Subtype.ext h)
  let p : KParam := ⟨⟨m, Nat.lt_succ_of_le hm⟩, π⟩
  have hp : KAdmissible p := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      let r : R := e.symm i
      rcases r.2 with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      have hr : (⟨f a, ⟨a, rfl⟩⟩ : R) = r := Subtype.ext ha
      change e ⟨f a, ⟨a, rfl⟩⟩ = i
      rw [hr]
      exact e.apply_symm_apply i
    · intro a b hab
      exact hcolor a b (hπ a b |>.mp hab)
    · intro copy a b hab
      apply hinj copy
      exact (hπ _ _).mp hab
  have hπsurj := hp.1
  let rep (i : Fin m) : K0Vert := Classical.choose (hπsurj i)
  have hrep (i : Fin m) : π (rep i) = i := Classical.choose_spec (hπsurj i)
  let qhom : (quotientGraph K0Graph m π) →g G := {
    toFun := fun i => f (rep i)
    map_rel' := by
      intro i j hij
      rcases hij with ⟨hne, a, b, ha, hb, hadj⟩
      have hfa : f (rep i) = f a := (hπ _ _).mp (by rw [hrep, ha])
      have hfb : f (rep j) = f b := (hπ _ _).mp (by rw [hrep, hb])
      rw [hfa, hfb]
      exact hedge a b hadj
  }
  have qinj : Function.Injective qhom := by
    intro i j hij
    have hpeq : π (rep i) = π (rep j) := (hπ _ _).2 hij
    rw [hrep, hrep] at hpeq
    exact hpeq
  let qcopy : SimpleGraph.Copy (quotientGraph K0Graph m π) G := ⟨qhom, qinj⟩
  have hpIn : p ∈ Finset.univ.filter KAdmissible :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
  have hK : kQuotient p ∈ K := Finset.mem_image.mpr ⟨p, hpIn, rfl⟩
  exact ⟨kQuotient p, hK, ⟨qcopy⟩⟩

theorem jFamily_interface {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W) :
    (∃ A ∈ J, SimpleGraph.IsContained A.2 G) ↔
    ∃ f : J0Vert → W,
      (∀ a b, J0Graph.Adj a b → G.Adj (f a) (f b)) ∧
      (∀ copy, Function.Injective (fun w : SVert 2 => f (jCopy copy w))) ∧
      (∀ a b, f a = f b → jColor a = jColor b) ∧ f .x ≠ f .xp := by
  constructor
  · exact jFamily_containment_to_templateMap G
  · rintro ⟨f, hedge, hinj, hcolor, hxx⟩
    exact jFamily_templateMap_to_containment G f hedge hinj hcolor hxx

theorem kFamily_interface {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W) :
    (∃ A ∈ K, SimpleGraph.IsContained A.2 G) ↔
    ∃ f : K0Vert → W,
      (∀ a b, K0Graph.Adj a b → G.Adj (f a) (f b)) ∧
      (∀ copy, Function.Injective (fun w : SVert 3 => f (kCopy copy w))) ∧
      (∀ a b, f a = f b → kColor a = kColor b) := by
  constructor
  · exact kFamily_containment_to_templateMap G
  · rintro ⟨f, hedge, hinj, hcolor⟩
    exact kFamily_templateMap_to_containment G f hedge hinj hcolor

end L575U

import JustinSun.Erdos575.Upper.Pruning
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-! Counting estimates for the upper-bound argument. -/

namespace L575U

open Finset
open SimpleGraph

noncomputable def tripleCenters {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S T : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun c => c ∈ S ∧ ∀ x ∈ T, Related G x c

noncomputable def A_yz {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (y z : V) : Finset V := by
  classical
  exact Finset.univ.filter fun x =>
    x ∈ S ∧ x ≠ y ∧ x ≠ z ∧ ¬ Related G x y ∧ ¬ Related G x z ∧
      2 ≤ (tripleCenters G S {x, y, z}).card

/-- The unordered independent triples that have at least two common centers. -/
noncomputable def T_S {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun T =>
    T.card = 3 ∧ T ⊆ S ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ Related G x y) ∧
      2 ≤ (tripleCenters G S T).card

/-- Ordered pairs that can occur as the last two bases of a counted triple. -/
noncomputable def orderedBasePairs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Finset (V × V) := by
  classical
  exact Finset.univ.filter fun p =>
    p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2 ∧ ¬ Related G p.1 p.2

/-- Ordered versions of the triples in `T_S`. -/
noncomputable def orderedBaseTriples {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Finset (V × V × V) := by
  classical
  exact Finset.univ.filter fun q =>
    q.1 ∈ S ∧ q.2.1 ∈ S ∧ q.2.2 ∈ S ∧
    q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2 ∧ q.2.1 ≠ q.2.2 ∧
    ¬ Related G q.1 q.2.1 ∧ ¬ Related G q.1 q.2.2 ∧
    ¬ Related G q.2.1 q.2.2 ∧
    2 ≤ (tripleCenters G S {q.1, q.2.1, q.2.2}).card

/-- The bases adjacent in the relatedness graph to both `u` and `v`. -/
noncomputable def Z_uv {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (u v : V) : Finset V := by
  classical
  exact S.filter fun w => Related G u w ∧ Related G v w

/-- The total number of three-base choices over unrelated partners of `u`. -/
noncomputable def C_u {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (u : V) : ℕ := by
  classical
  exact ∑ v ∈ S.filter (fun v => v ≠ u ∧ ¬ Related G u v),
    Nat.choose (Z_uv G S u v).card 3

/-- The finite reindexing identity for the item 14 local count. -/
def Item14CuIdentityClaim : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G)
    (S : Finset V) (hside : ∀ x ∈ S, χ x = 0) (u : V), u ∈ S →
      C_u G S u =
        ∑ T ∈ (T_S G S).filter (fun T => u ∈ tripleCenters G S T),
          ((tripleCenters G S T).card - 1)

/-- A three element subset of `Z_uv` is a counted base triple with centers `u,v`. -/
theorem item14_subset_Z_spec {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G) (S : Finset V)
    (hside : ∀ x ∈ S, χ x = 0) {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (hnot : ¬ Related G u v) {T : Finset V}
    (hcard : T.card = 3) (hsub : T ⊆ Z_uv G S u v) :
    T ∈ T_S G S ∧ u ∈ tripleCenters G S T ∧ v ∈ tripleCenters G S T := by
  classical
  have huColor := hside u hu
  have hTside : ∀ x ∈ T, χ x = 0 := by
    intro x hx
    have hxsub := hsub hx
    simp [Z_uv] at hxsub
    exact (related_color_eq χ hxsub.2.1).symm.trans huColor
  have hind : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ Related G x y := by
    intro x hx y hy hxy
    have hxmem : x ∈ ZSet G u v := by
      rw [mem_zSet]
      have hxm := hsub hx
      simp [Z_uv] at hxm
      exact ⟨hxm.2.1, hxm.2.2⟩
    have hymem : y ∈ ZSet G u v := by
      rw [mem_zSet]
      have hym := hsub hy
      simp [Z_uv] at hym
      exact ⟨hym.2.1, hym.2.2⟩
    exact zSet_independent χ hfree4 hfree6 huColor huv hnot hxmem hymem hxy
  have hcenterU : u ∈ tripleCenters G S T := by
    simp only [tripleCenters, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hu, ?_⟩
    intro x hx
    have hxmem := hsub hx
    simp [Z_uv] at hxmem
    exact related_symm hxmem.2.1
  have hcenterV : v ∈ tripleCenters G S T := by
    simp only [tripleCenters, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hv, ?_⟩
    intro x hx
    have hxmem := hsub hx
    simp [Z_uv] at hxmem
    exact related_symm hxmem.2.2
  have hcenters : 2 ≤ (tripleCenters G S T).card := by
    have hlt : 1 < (tripleCenters G S T).card :=
      Finset.one_lt_card_iff.mpr ⟨u, v, hcenterU, hcenterV, huv⟩
    omega
  refine ⟨?_, hcenterU, hcenterV⟩
  simp only [T_S, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hcard, hsub.trans (Finset.filter_subset _ _), hind, hcenters⟩

/-- Distinct centers of a counted triple are unrelated. -/
theorem item14_centers_unrelated {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G) (S : Finset V)
    (hside : ∀ x ∈ S, χ x = 0) {T : Finset V}
    (hT : T ∈ T_S G S) {u v : V}
    (hu : u ∈ tripleCenters G S T) (hv : v ∈ tripleCenters G S T)
    (huv : u ≠ v) : ¬ Related G u v := by
  classical
  have hTmem := hT
  simp only [T_S, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  let e : T ≃ Fin 3 := T.equivFinOfCardEq hT.1
  let a : V := (e.symm 0).val
  let b : V := (e.symm 1).val
  let c : V := (e.symm 2).val
  have hab : a ≠ b := by
    intro heq
    have he := congrArg e (Subtype.ext heq)
    exact (show (0 : Fin 3) ≠ 1 by decide) (by simpa [a, b] using he)
  have hac : a ≠ c := by
    intro heq
    have he := congrArg e (Subtype.ext heq)
    exact (show (0 : Fin 3) ≠ 2 by decide) (by simpa [a, c] using he)
  have hbc : b ≠ c := by
    intro heq
    have he := congrArg e (Subtype.ext heq)
    exact (show (1 : Fin 3) ≠ 2 by decide) (by simpa [b, c] using he)
  have haT : a ∈ T := (e.symm 0).property
  have hbT : b ∈ T := (e.symm 1).property
  have hcT : c ∈ T := (e.symm 2).property
  have haColor := hside a (hT.2.1 haT)
  have hbColor := hside b (hT.2.1 hbT)
  have hcColor := hside c (hT.2.1 hcT)
  have habNot := hT.2.2.1 a haT b hbT hab
  have hacNot := hT.2.2.1 a haT c hcT hac
  have hbcNot := hT.2.2.1 b hbT c hcT hbc
  have hu' := hu
  have hv' := hv
  simp only [tripleCenters, Finset.mem_filter, Finset.mem_univ, true_and] at hu' hv'
  have hua : Related G u a := related_symm (hu'.2 a haT)
  have hub : Related G u b := related_symm (hu'.2 b hbT)
  have huc : Related G u c := related_symm (hu'.2 c hcT)
  have hva : Related G v a := related_symm (hv'.2 a haT)
  have hvb : Related G v b := related_symm (hv'.2 b hbT)
  have hvc : Related G v c := related_symm (hv'.2 c hcT)
  exact (triple_centers_independent χ hfree4 hfree6 haColor hbColor hcColor
    hab hac hbc habNot hacNot hbcNot).2 hua hub huc hva hvb hvc huv

/-- A counted triple with two specified centers is a three element subset of `Z_uv`. -/
theorem item14_centers_to_Z_spec {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G) (S : Finset V)
    (hside : ∀ x ∈ S, χ x = 0) {T : Finset V}
    (hT : T ∈ T_S G S) {u v : V}
    (hu : u ∈ tripleCenters G S T) (hv : v ∈ tripleCenters G S T)
    (huv : u ≠ v) :
    T.card = 3 ∧ T ⊆ Z_uv G S u v := by
  classical
  have hTmem := hT
  simp only [T_S, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  have hu' := hu
  have hv' := hv
  simp only [tripleCenters, Finset.mem_filter, Finset.mem_univ, true_and] at hu' hv'
  refine ⟨hT.1, ?_⟩
  intro x hx
  simp only [Z_uv, Finset.mem_filter]
  refine ⟨hT.2.1 hx, ?_⟩
  exact ⟨related_symm (hu'.2 x hx), related_symm (hv'.2 x hx)⟩

/-- The finite reindexing identity for `C_u`. -/
theorem item14_cu_identity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G) (S : Finset V)
    (hside : ∀ x ∈ S, χ x = 0) (u : V) (hu : u ∈ S) :
    C_u G S u =
      ∑ T ∈ (T_S G S).filter (fun T => u ∈ tripleCenters G S T),
        ((tripleCenters G S T).card - 1) := by
  classical
  let leftBase := S.filter (fun v => v ≠ u ∧ ¬ Related G u v)
  let left : Finset (Σ v : V, Finset V) :=
    leftBase.sigma (fun v => (Z_uv G S u v).powersetCard 3)
  let rightBase := (T_S G S).filter (fun T => u ∈ tripleCenters G S T)
  let right : Finset (Σ T : Finset V, V) :=
    rightBase.sigma (fun T => (tripleCenters G S T).erase u)
  have hcard : left.card = right.card := by
    apply Finset.card_bij'
      (fun p _ => (⟨p.2, p.1⟩ : Σ T : Finset V, V))
      (fun p _ => (⟨p.2, p.1⟩ : Σ v : V, Finset V))
    · intro p hp
      simp only [left, Finset.mem_sigma] at hp
      rcases hp with ⟨hpv, hpT⟩
      simp only [right, Finset.mem_sigma]
      have hpow := Finset.mem_powersetCard.mp hpT
      have hspec := item14_subset_Z_spec G χ hfree4 hfree6 S hside
        hu (Finset.mem_filter.mp hpv).1
        (Finset.mem_filter.mp hpv).2.1.symm
        (Finset.mem_filter.mp hpv).2.2 hpow.2 hpow.1
      refine ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hspec.1, hspec.2.1⟩
      · simp only [Finset.mem_erase]
        exact ⟨(Finset.mem_filter.mp hpv).2.1, hspec.2.2⟩
    · intro p hp
      simp only [right, Finset.mem_sigma] at hp
      rcases hp with ⟨hpT, hpv⟩
      have huCenter := (Finset.mem_filter.mp hpT).2
      have hvCenter : p.2 ∈ tripleCenters G S p.1 :=
        (Finset.mem_erase.mp hpv).2
      have huv : u ≠ p.2 := (Finset.mem_erase.mp hpv).1.symm
      have hspec := item14_centers_to_Z_spec G χ hfree4 hfree6 S hside
        (Finset.mem_filter.mp hpT).1 huCenter hvCenter huv
      have hnot := item14_centers_unrelated G χ hfree4 hfree6 S hside
        (Finset.mem_filter.mp hpT).1 huCenter hvCenter huv
      have hvS : p.2 ∈ S := by
        have hv := hvCenter
        simp [tripleCenters] at hv
        exact hv.1
      simp only [left, Finset.mem_sigma]
      refine ⟨Finset.mem_filter.mpr ⟨hvS, huv.symm, hnot⟩, ?_⟩
      exact Finset.mem_powersetCard.mpr ⟨hspec.2, hspec.1⟩
    · intro p hp
      cases p
      rfl
    · intro p hp
      cases p
      rfl
  have hleft : left.card = C_u G S u := by
    simp [left, leftBase, C_u, Finset.card_sigma, Finset.card_powersetCard]
  have hright : right.card =
      ∑ T ∈ rightBase, ((tripleCenters G S T).card - 1) := by
    calc
      right.card = ∑ T ∈ rightBase, #((tripleCenters G S T).erase u) := by
        simp only [right, Finset.card_sigma]
      _ = _ := Finset.sum_congr (s₁ := rightBase) (s₂ := rightBase) rfl
        (by
          intro T hT
          exact Finset.card_erase_of_mem (Finset.mem_filter.mp hT).2)
  have hright' : right.card =
      ∑ T ∈ (T_S G S).filter (fun T => u ∈ tripleCenters G S T),
        ((tripleCenters G S T).card - 1) := by
    simpa [rightBase] using hright
  omega

theorem item14_cu_identity_claim : Item14CuIdentityClaim := by
  intro V _ _ G χ hfree4 hfree6 S hside u hu
  exact item14_cu_identity G χ hfree4 hfree6 S hside u hu

/-- Vertices in the side `S` that do not center any counted triple with three centers. -/
noncomputable def U_S {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Finset V := by
  classical
  exact S.filter fun u =>
    ∀ T ∈ T_S G S, u ∈ tripleCenters G S T →
      (tripleCenters G S T).card < 3

/-- The one-side conclusion in blueprint item 15. -/
def Item15BoundClaim : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G)
    (hJfree : ∀ A ∈ J, A.2.Free G) (S : Finset V)
    (hside : ∀ x, x ∈ S ↔ χ x = 0) (d : ℕ),
    (16 * Real.rpow (Fintype.card V : ℝ) ((5 : ℝ) / 16) ≤ d) →
    (∀ v, d ≤ G.degree v) →
      (U_S G S).card ≤ 8192 * (Fintype.card V : ℝ) ^ 5 / (d : ℝ) ^ 13

private def orderedIndices (i : Fin 3) (b : Fin 2) : Fin 3 × Fin 3 × Fin 3 :=
  (i, if b = 0 then i + 1 else i + 2, if b = 0 then i + 2 else i + 1)

/-- The remaining counting assertion in item 13, stated without division. -/
def Item13TripleCountClaim : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G)
    (hJfree : ∀ A ∈ J, A.2.Free G) (S : Finset V)
    (hside : ∀ v ∈ S, χ v = 0) (d : ℕ),
    0 < d → (∀ v, d ≤ G.degree v) →
      6 * d * (T_S G S).card ≤ Fintype.card V ^ 3

/-- The J-exclusion step needed to show that possible third bases are independent. -/
def Item13AyzIndependentClaim : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (hfree : ∀ A ∈ forbiddenFamily, A.2.Free G) (χ : G.Coloring (Fin 2))
    (hside : ∀ v ∈ S, χ v = 0) (y z : V),
    y ∈ S → z ∈ S → y ≠ z → ¬ Related G y z →
    ∀ x ∈ A_yz G S y z, ∀ x' ∈ A_yz G S y z, x ≠ x' → ¬ Related G x x'

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 8192 in
theorem item13_Ayz_related_contradiction {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G)
    (hJfree : ∀ A ∈ J, A.2.Free G) (S : Finset V)
    (hside : ∀ v ∈ S, χ v = 0) {y z x x' : V}
    (hy : y ∈ S) (hz : z ∈ S) (hyz : y ≠ z) (huny : ¬ Related G y z)
    (hx : x ∈ A_yz G S y z) (hx' : x' ∈ A_yz G S y z)
    (hxx' : x ≠ x') : ¬ Related G x x' := by
  classical
  simp only [A_yz, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  intro hrelxx'
  have hxcard : 1 < (tripleCenters G S {x, y, z}).card := by omega
  have hx'card : 1 < (tripleCenters G S {x', y, z}).card := by omega
  obtain ⟨a₀, a₁, ha₀, ha₁, haa⟩ := Finset.one_lt_card_iff.mp hxcard
  obtain ⟨b₀, b₁, hb₀, hb₁, hbb⟩ := Finset.one_lt_card_iff.mp hx'card
  simp only [tripleCenters, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton] at ha₀ ha₁ hb₀ hb₁
  let ba : Fin 3 → V := ![x, y, z]
  let bb : Fin 3 → V := ![x', y, z]
  have habaseA : Function.Injective ba := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [ba]
  have habaseB : Function.Injective bb := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [bb]
  have hbaseColorA : ∀ i, χ (ba i) = 0 := by
    intro i
    fin_cases i <;> simp [ba, hx.1, hy, hz, hside]
  have hbaseColorB : ∀ i, χ (bb i) = 0 := by
    intro i
    fin_cases i <;> simp [bb, hx'.1, hy, hz, hside]
  have hbaseA : ∀ i i', i ≠ i' → ¬ Related G (ba i) (ba i') := by
    intro i i' hii
    fin_cases i
    · fin_cases i'
      · exact (hii rfl).elim
      · simpa [ba] using hx.2.2.2.1
      · simpa [ba] using hx.2.2.2.2.1
    · fin_cases i'
      · exact fun h => hx.2.2.2.1 (related_symm h)
      · exact (hii rfl).elim
      · exact huny
    · fin_cases i'
      · exact fun h => hx.2.2.2.2.1 (related_symm h)
      · exact fun h => huny (related_symm h)
      · exact (hii rfl).elim
  have hbaseB : ∀ i i', i ≠ i' → ¬ Related G (bb i) (bb i') := by
    intro i i' hii
    fin_cases i
    · fin_cases i'
      · exact (hii rfl).elim
      · simpa [bb] using hx'.2.2.2.1
      · simpa [bb] using hx'.2.2.2.2.1
    · fin_cases i'
      · exact fun h => hx'.2.2.2.1 (related_symm h)
      · exact (hii rfl).elim
      · exact huny
    · fin_cases i'
      · exact fun h => hx'.2.2.2.2.1 (related_symm h)
      · exact fun h => huny (related_symm h)
      · exact (hii rfl).elim
  let ca : Fin 2 → V := ![a₀, a₁]
  let cb : Fin 2 → V := ![b₀, b₁]
  have hcaInj : Function.Injective ca := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [ca]
  have hcbInj : Function.Injective cb := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [cb]
  have hcaColor : ∀ i, χ (ca i) = 0 := by
    intro i
    fin_cases i
    · exact (related_color_eq (G := G) χ (ha₀.2 x (by simp))).symm.trans (hbaseColorA 0)
    · exact (related_color_eq (G := G) χ (ha₁.2 x (by simp))).symm.trans (hbaseColorA 0)
  have hcbColor : ∀ i, χ (cb i) = 0 := by
    intro i
    fin_cases i
    · exact (related_color_eq (G := G) χ (hb₀.2 x' (by simp))).symm.trans (hbaseColorB 0)
    · exact (related_color_eq (G := G) χ (hb₁.2 x' (by simp))).symm.trans (hbaseColorB 0)
  have hcaRel : ∀ i j, Related G (ba i) (ca j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [ba, ca, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    all_goals first
      | exact ha₀.2 x (by simp)
      | exact ha₀.2 y (by simp)
      | exact ha₀.2 z (by simp)
      | exact ha₁.2 x (by simp)
      | exact ha₁.2 y (by simp)
      | exact ha₁.2 z (by simp)
  have hcbRel : ∀ i j, Related G (bb i) (cb j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [bb, cb, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    all_goals first
      | exact hb₀.2 x' (by simp)
      | exact hb₀.2 y (by simp)
      | exact hb₀.2 z (by simp)
      | exact hb₁.2 x' (by simp)
      | exact hb₁.2 y (by simp)
      | exact hb₁.2 z (by simp)
  let pA := subdivision_copy_of_independent_triple χ ba ca hfree4 hfree6
    habaseA hcaInj hbaseColorA hcaColor hbaseA hcaRel
  let pB := subdivision_copy_of_independent_triple χ bb cb hfree4 hfree6
    habaseB hcbInj hbaseColorB hcbColor hbaseB hcbRel
  have hpABase (i : Fin 3) : pA.toHom (.base i) = ba i := by
    simp [pA, subdivision_copy_of_independent_triple, subdivision_copy_of_related_triples]
  have hpBBase (i : Fin 3) : pB.toHom (.base i) = bb i := by
    simp [pB, subdivision_copy_of_independent_triple, subdivision_copy_of_related_triples]
  have hpACenter (j : Fin 2) : pA.toHom (.center j) = ca j := by
    simp [pA, subdivision_copy_of_independent_triple, subdivision_copy_of_related_triples]
  have hpBCenter (j : Fin 2) : pB.toHom (.center j) = cb j := by
    simp [pB, subdivision_copy_of_independent_triple, subdivision_copy_of_related_triples]
  let lam := Classical.choose hrelxx'.2
  have hlamx : G.Adj x lam := Classical.choose_spec hrelxx'.2 |>.1
  have hlamxp : G.Adj x' lam := Classical.choose_spec hrelxx'.2 |>.2
  let f : J0Vert → V
    | .x => x
    | .xp => x'
    | .y => y
    | .z => z
    | .lam => lam
    | .c copy j => if copy = 0 then ca j else cb j
    | .s copy i j => if copy = 0 then pA.toHom (.sub i j) else pB.toHom (.sub i j)
  have hfcopy (copy : Fin 2) (w : SVert 2) :
      f (jCopy copy w) = if copy = 0 then pA.toHom w else pB.toHom w := by
    cases w with
    | base i => fin_cases copy <;> fin_cases i <;> simp [f, jCopy, ba, bb, hpABase, hpBBase]
    | center j => fin_cases copy <;> simp [f, jCopy, hpACenter, hpBCenter]
    | sub i j => fin_cases copy <;> simp [f, jCopy]
  have hedge : ∀ a b, J0Graph.Adj a b → G.Adj (f a) (f b) := by
    intro a b hab
    change J0Adj a b at hab
    rcases hab with ⟨copy, u, v, huv, rfl, rfl⟩ | h
    · rw [hfcopy, hfcopy]
      split_ifs with hc
      · exact pA.toHom.map_rel huv
      · exact pB.toHom.map_rel huv
    · rcases h with h | h
      · rcases h with h | h
        · rcases h with ⟨rfl, rfl⟩; exact hlamx.symm
        · rcases h with ⟨rfl, rfl⟩; exact hlamx
      · rcases h with h | h
        · rcases h with ⟨rfl, rfl⟩; exact hlamxp.symm
        · rcases h with ⟨rfl, rfl⟩; exact hlamxp
  have hinj : ∀ copy, Function.Injective (fun w : SVert 2 => f (jCopy copy w)) := by
    intro copy a b hab
    fin_cases copy
    · apply pA.injective'
      simpa [hfcopy] using hab
    · apply pB.injective'
      simpa [hfcopy] using hab
  have hcolorMap : ∀ v, χ (f v) = if jColor v then 1 else 0 := by
    intro v
    cases v with
    | x => simpa [f, jColor] using hside x hx.1
    | xp => simpa [f, jColor] using hside x' hx'.1
    | y => simpa [f, jColor] using hside y hy
    | z => simpa [f, jColor] using hside z hz
    | lam =>
      have hne : χ lam ≠ 0 := by
        intro heq
        exact (χ.valid hlamx) ((hside x hx.1).trans heq.symm)
      have hone : χ lam = 1 := Fin.eq_one_of_ne_zero _ hne
      simp [f, jColor, hone]
    | c copy j =>
      fin_cases copy
      · simpa [f, jColor] using hcaColor j
      · simpa [f, jColor] using hcbColor j
    | s copy i j =>
      fin_cases copy
      · have hedgeSub := pA.toHom.map_rel (by
          change sAdj (.base i) (.sub i j)
          simp [sAdj])
        have hbaseval : χ (pA.toHom (.base i)) = 0 := by
          rw [hpABase]
          exact hbaseColorA i
        have hnonzero : χ (pA.toHom (.sub i j)) ≠ 0 := by
          intro hz'
          exact (χ.valid hedgeSub) (hbaseval.trans hz'.symm)
        have hone := Fin.eq_one_of_ne_zero _ hnonzero
        simpa [f, jColor] using hone
      · have hedgeSub := pB.toHom.map_rel (by
          change sAdj (.base i) (.sub i j)
          simp [sAdj])
        have hbaseval : χ (pB.toHom (.base i)) = 0 := by
          rw [hpBBase]
          exact hbaseColorB i
        have hnonzero : χ (pB.toHom (.sub i j)) ≠ 0 := by
          intro hz'
          exact (χ.valid hedgeSub) (hbaseval.trans hz'.symm)
        have hone := Fin.eq_one_of_ne_zero _ hnonzero
        simpa [f, jColor] using hone
  have hcolor : ∀ a b, f a = f b → jColor a = jColor b := by
    intro a b hab
    have heq := congrArg χ hab
    rw [hcolorMap a, hcolorMap b] at heq
    cases hja : jColor a <;> cases hjb : jColor b <;>
      simp only [hja, hjb] at heq <;> norm_num at heq <;> rfl
  have hxx : f .x ≠ f .xp := by simpa [f] using hxx'
  obtain ⟨A, hA, hcopy⟩ := (jFamily_interface G).2 ⟨f, hedge, hinj, hcolor, hxx⟩
  exact hJfree A hA hcopy

theorem disjointFamily_card_bound {α β : Type*} [Fintype β] [DecidableEq β]
    (A : Finset α) (N : α → Finset β) (d : ℕ)
    (hd : ∀ a ∈ A, d ≤ (N a).card)
    (hdisj : (A : Set α).PairwiseDisjoint N) :
    d * A.card ≤ Fintype.card β := by
  classical
  calc
    d * A.card = ∑ v ∈ A, d := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ A, (N v).card := by
      apply Finset.sum_le_sum
      intro v hv
      exact hd v hv
    _ = (A.biUnion N).card := (Finset.card_biUnion hdisj).symm
    _ ≤ Fintype.card β := Finset.card_le_univ _

/-- Candidate third bases for a fixed unrelated pair have disjoint neighborhoods. -/
theorem item13_Ayz_card_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G)
    (hJfree : ∀ A ∈ J, A.2.Free G) (S : Finset V)
    (hside : ∀ v ∈ S, χ v = 0) (d : ℕ)
    (hmin : ∀ v, d ≤ G.degree v) {y z : V}
    (hy : y ∈ S) (hz : z ∈ S) (hyz : y ≠ z) (huny : ¬ Related G y z) :
    d * (A_yz G S y z).card ≤ Fintype.card V := by
  classical
  let A := A_yz G S y z
  have hindep : ∀ x ∈ A, ∀ x' ∈ A, x ≠ x' → ¬ Related G x x' := by
    intro x hx x' hx' hne
    exact item13_Ayz_related_contradiction G χ hfree4 hfree6 hJfree S hside
      hy hz hyz huny hx hx' hne
  have hdisj : (A : Set V).PairwiseDisjoint (fun v => G.neighborFinset v) := by
    intro x hx x' hx' hne
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    apply hindep x hx x' hx' hne
    exact ⟨hne, w, (G.mem_neighborFinset x w).mp hw,
      (G.mem_neighborFinset x' w).mp hw'⟩
  have hd : ∀ x ∈ A, d ≤ (G.neighborFinset x).card := by
    intro x hx
    rw [G.card_neighborFinset_eq_degree]
    exact hmin x
  simpa [A] using disjointFamily_card_bound A (fun v => G.neighborFinset v) d hd hdisj

/-- Ordered triples can be counted by their final ordered pair of bases. -/
theorem item13_orderedTriple_fiber_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (p : V × V)
    (hp : p ∈ orderedBasePairs G S) :
    #{q ∈ orderedBaseTriples G S | (q.2.1, q.2.2) = p} =
      (A_yz G S p.1 p.2).card := by
  classical
  rcases p with ⟨y, z⟩
  have hpair : y ∈ S ∧ z ∈ S ∧ y ≠ z ∧ ¬ Related G y z := by
    simpa [orderedBasePairs] using hp
  let A := A_yz G S y z
  let φ : V → V × V × V := fun x => (x, y, z)
  have hinj : Function.Injective φ := by
    intro x y h
    exact congrArg Prod.fst h
  have himage : A.image φ = {q ∈ orderedBaseTriples G S | (q.2.1, q.2.2) = (y, z)} := by
    ext q
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change x ∈ A_yz G S y z at hx
      simp only [A_yz, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rcases hx with ⟨hxs, hxy, hxz, hxyR, hxzR, hcenters⟩
      refine ⟨?_, ?_⟩
      · simp only [orderedBaseTriples, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hxs, hpair.1, hpair.2.1, hxy, hxz, hpair.2.2.1, hxyR, hxzR,
          hpair.2.2.2, ?_⟩
        have hcentEq : tripleCenters G S {x, y, z} =
            tripleCenters G S {y, x, z} := by
          ext c
          simp [tripleCenters, or_comm, or_left_comm, or_assoc,
            and_comm, and_left_comm, and_assoc]
        simpa [A_yz, tripleCenters] using hcenters
      · rfl
    · intro hq
      simp only [orderedBaseTriples, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hpairEq := hq.2
      have hy : q.2.1 = y := congrArg Prod.fst hpairEq
      have hz : q.2.2 = z := congrArg Prod.snd hpairEq
      rcases hq.1 with ⟨hxs, hys, hzs, hxy, hxz, hyz', hRxy, hRxz, hRyz, hcent⟩
      refine ⟨q.1, ?_, ?_⟩
      · change q.1 ∈ A_yz G S y z
        simp only [A_yz, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hxs, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [hy] using hxy
        · simpa [hz] using hxz
        · simpa [hy] using hRxy
        · simpa [hz] using hRxz
        · have hcentEq : tripleCenters G S {q.1, y, z} =
              tripleCenters G S {q.1, q.2.1, q.2.2} := by
            rw [hy, hz]
          rw [hcentEq]
          exact hcent
      · rcases q with ⟨x, yz⟩
        rcases yz with ⟨y', z'⟩
        simp only [Prod.mk.injEq] at hpairEq
        rcases hpairEq with ⟨rfl, rfl⟩
        rfl
  rw [← himage, Finset.card_image_of_injective _ hinj]

/-- The degree and J bounds control all ordered independent triples. -/
theorem item13_orderedTriple_card_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G)
    (hJfree : ∀ A ∈ J, A.2.Free G) (S : Finset V)
    (hside : ∀ v ∈ S, χ v = 0) (d : ℕ)
    (hmin : ∀ v, d ≤ G.degree v) :
    d * (orderedBaseTriples G S).card ≤ Fintype.card V ^ 3 := by
  classical
  let P := orderedBasePairs G S
  let Q := orderedBaseTriples G S
  have hmaps : (Q : Set (V × V × V)).MapsTo (fun q => (q.2.1, q.2.2)) P := by
    intro q hq
    change q ∈ Q at hq
    simp only [Q, orderedBaseTriples, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    change (q.2.1, q.2.2) ∈ P
    simp only [P, orderedBasePairs, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hq with ⟨hx, hy, hz, hxy, hxz, hyz, hRxy, hRxz, hRyz, hcent⟩
    exact ⟨hy, hz, hyz, hRyz⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hpairs : P.card ≤ Fintype.card V ^ 2 := by
    apply (Finset.card_le_card ?_).trans
      (show (S ×ˢ S).card ≤ Fintype.card V ^ 2 from by
        simp only [Finset.card_product]
        nlinarith [Finset.card_le_univ S])
    intro p hp
    simp only [P, orderedBasePairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_product]
    exact ⟨hp.1, hp.2.1⟩
  have hsum : d * Q.card ≤ P.card * Fintype.card V := by
    rw [hcard]
    calc
      d * (∑ p ∈ P, #{q ∈ Q | (q.2.1, q.2.2) = p}) =
          ∑ p ∈ P, d * #{q ∈ Q | (q.2.1, q.2.2) = p} := by
        simp [Finset.mul_sum]
      _ ≤ ∑ p ∈ P, Fintype.card V := by
        apply Finset.sum_le_sum
        intro p hp
        have hmem : #{q ∈ Q | (q.2.1, q.2.2) = p} =
            (A_yz G S p.1 p.2).card := by
          exact item13_orderedTriple_fiber_count G S p (by simpa [P] using hp)
        rw [hmem]
        simp only [P, orderedBasePairs, Finset.mem_filter, Finset.mem_univ,
          true_and] at hp
        exact item13_Ayz_card_bound G χ hfree4 hfree6 hJfree S hside d hmin
          hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
      _ = P.card * Fintype.card V := by simp
  calc
    d * Q.card ≤ P.card * Fintype.card V := by
      exact hsum
    _ ≤ Fintype.card V ^ 3 := by
      have hN : 0 ≤ Fintype.card V := Nat.cast_nonneg _
      nlinarith [hpairs]

/-- Every unordered counted triple contributes its six orderings. -/
theorem item13_orderedTriple_card_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) :
    6 * (T_S G S).card ≤ (orderedBaseTriples G S).card := by
  classical
  let T := {t // t ∈ T_S G S}
  let I := T × (Fin 3 × Fin 2)
  let e (t : T) : t.1 ≃ Fin 3 :=
    t.1.equivFinOfCardEq (by
      have ht := t.2
      simp only [T_S, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      exact ht.1)
  let valAt (t : T) (i : Fin 3) : V := ((e t).symm i).val
  let order (a : I) : V × V × V :=
    let ij := orderedIndices a.2.1 a.2.2
    (valAt a.1 ij.1, valAt a.1 ij.2.1, valAt a.1 ij.2.2)
  have hindices (i : Fin 3) (b : Fin 2) :
      let j := orderedIndices i b
      i ≠ j.2.1 ∧ i ≠ j.2.2 ∧ j.2.1 ≠ j.2.2 := by
    fin_cases i <;> fin_cases b <;> decide
  have hmem (a : I) : order a ∈ orderedBaseTriples G S := by
    have ht := a.1.2
    simp only [T_S, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    let ij := orderedIndices a.2.1 a.2.2
    have hidx := hindices a.2.1 a.2.2
    have hv01 : valAt a.1 ij.1 ≠ valAt a.1 ij.2.1 := by
      intro h
      have := congrArg ((e a.1)) (Subtype.ext h)
      exact hidx.1 (by simpa [valAt, ij, orderedIndices] using this)
    have hv02 : valAt a.1 ij.1 ≠ valAt a.1 ij.2.2 := by
      intro h
      have := congrArg ((e a.1)) (Subtype.ext h)
      exact hidx.2.1 (by simpa [valAt, ij, orderedIndices] using this)
    have hv12 : valAt a.1 ij.2.1 ≠ valAt a.1 ij.2.2 := by
      intro h
      have := congrArg ((e a.1)) (Subtype.ext h)
      exact hidx.2.2 (by simpa [valAt, ij, orderedIndices] using this)
    have hverts : ({valAt a.1 ij.1, valAt a.1 ij.2.1, valAt a.1 ij.2.2} : Finset V) = a.1.1 := by
      apply Finset.eq_of_subset_of_card_le
      · intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · exact ((e a.1).symm (ij.1)).property
        · exact ((e a.1).symm (ij.2.1)).property
        · exact ((e a.1).symm (ij.2.2)).property
      · have hcard : ({valAt a.1 ij.1, valAt a.1 ij.2.1,
          valAt a.1 ij.2.2} : Finset V).card = 3 := by
          simp [hv01, hv02, hv12]
        rw [hcard]
        exact ht.1.le
    have hbaseMem (i : Fin 3) : valAt a.1 i ∈ S :=
      ht.2.1 ((e a.1).symm i).property
    have hrel (i j : Fin 3) (hij : i ≠ j) :
        ¬ Related G (valAt a.1 i) (valAt a.1 j) := by
      apply ht.2.2.1
      · exact ((e a.1).symm i).property
      · exact ((e a.1).symm j).property
      · intro heq
        have hEq := congrArg (e a.1) (Subtype.ext heq)
        exact hij (by simpa [valAt] using hEq)
    have hcent : 2 ≤ (tripleCenters G S a.1.1).card := ht.2.2.2
    have hcenterEq : tripleCenters G S
        {valAt a.1 ij.1, valAt a.1 ij.2.1, valAt a.1 ij.2.2} =
          tripleCenters G S a.1.1 := by rw [hverts]
    simp only [orderedBaseTriples, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hbaseMem ij.1, hbaseMem ij.2.1, hbaseMem ij.2.2,
      hv01, hv02, hv12, hrel ij.1 ij.2.1 hidx.1,
      hrel ij.1 ij.2.2 hidx.2.1, hrel ij.2.1 ij.2.2 hidx.2.2, ?_⟩
    rw [hcenterEq]
    exact hcent
  let baseSet (q : V × V × V) : Finset V := {q.1, q.2.1, q.2.2}
  have orderSet (a : I) : baseSet (order a) = a.1.1 := by
    let ij := orderedIndices a.2.1 a.2.2
    have hidx := hindices a.2.1 a.2.2
    have hn01 : valAt a.1 ij.1 ≠ valAt a.1 ij.2.1 := by
      intro h
      have hEq := congrArg (e a.1) (Subtype.ext h)
      exact hidx.1 (by simpa [valAt, ij, orderedIndices] using hEq)
    have hn02 : valAt a.1 ij.1 ≠ valAt a.1 ij.2.2 := by
      intro h
      have hEq := congrArg (e a.1) (Subtype.ext h)
      exact hidx.2.1 (by simpa [valAt, ij, orderedIndices] using hEq)
    have hn12 : valAt a.1 ij.2.1 ≠ valAt a.1 ij.2.2 := by
      intro h
      have hEq := congrArg (e a.1) (Subtype.ext h)
      exact hidx.2.2 (by simpa [valAt, ij, orderedIndices] using hEq)
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [baseSet, order, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact ((e a.1).symm ij.1).property
      · exact ((e a.1).symm ij.2.1).property
      · exact ((e a.1).symm ij.2.2).property
    · have hc : (baseSet (order a)).card = 3 := by
        change (insert (valAt a.1 ij.1)
          (insert (valAt a.1 ij.2.1)
            ({valAt a.1 ij.2.2} : Finset V))).card = 3
        have hnot : valAt a.1 ij.1 ∉
            insert (valAt a.1 ij.2.1)
              ({valAt a.1 ij.2.2} : Finset V) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          intro h
          rcases h with h | h
          · exact hn01 h
          · exact hn02 h
        have hnot12 : valAt a.1 ij.2.1 ∉
            ({valAt a.1 ij.2.2} : Finset V) := by
          simp [hn12]
        rw [Finset.card_insert_of_notMem hnot,
          Finset.card_insert_of_notMem hnot12]
        simp
      rw [hc]
      have ht := a.1.2
      simp only [T_S, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      exact ht.1.le
  have hinj : Function.Injective order := by
    intro a b hab
    rcases a with ⟨ta, ia⟩
    rcases ia with ⟨i, ba⟩
    rcases b with ⟨tb, ib⟩
    rcases ib with ⟨j, bb⟩
    have hT : ta.1 = tb.1 := by
      calc
        ta.1 = baseSet (order (ta, i, ba)) := (orderSet (ta, i, ba)).symm
        _ = baseSet (order (tb, j, bb)) := congrArg baseSet hab
        _ = tb.1 := orderSet (tb, j, bb)
    have hteq : ta = tb := Subtype.ext hT
    subst tb
    have hfirst := congrArg Prod.fst hab
    have hi : i = j := by
      have hsub : (e ta).symm i = (e ta).symm j := Subtype.ext hfirst
      have hEq := congrArg (e ta) hsub
      simpa using hEq
    have hsecond := congrArg (fun q : V × V × V => q.2.1) hab
    have hidxEq : (orderedIndices i ba).2.1 =
        (orderedIndices j bb).2.1 := by
      have hsub : (e ta).symm (orderedIndices i ba).2.1 =
          (e ta).symm (orderedIndices j bb).2.1 := Subtype.ext hsecond
      have hEq := congrArg (e ta) hsub
      simpa using hEq
    have hb : ba = bb := by
      fin_cases ba <;> fin_cases bb <;> simp [orderedIndices, hi] at hidxEq ⊢
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact hi
      · exact hb
  let f : I → {q // q ∈ orderedBaseTriples G S} := fun a => ⟨order a, hmem a⟩
  have hf : Function.Injective f := by
    intro a b h
    exact hinj (congrArg Subtype.val h)
  have hcard : Fintype.card I ≤ (orderedBaseTriples G S).card :=
    (Fintype.card_le_of_injective f hf).trans_eq (by simp)
  have hsource : Fintype.card I = 6 * (T_S G S).card := by
    simp [I, T, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]
  omega

/-- The global triple count follows from the ordered-pair estimate. -/
theorem item13_triple_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G)
    (hJfree : ∀ A ∈ J, A.2.Free G) (S : Finset V)
    (hside : ∀ v ∈ S, χ v = 0) (d : ℕ)
    (hd : 0 < d) (hmin : ∀ v, d ≤ G.degree v) :
    6 * d * (T_S G S).card ≤ Fintype.card V ^ 3 := by
  have hupper := item13_orderedTriple_card_bound G χ hfree4 hfree6 hJfree S hside d hmin
  have hlower := item13_orderedTriple_card_lower G S
  calc
    6 * d * (T_S G S).card = d * (6 * (T_S G S).card) := by ring
    _ ≤ d * (orderedBaseTriples G S).card := Nat.mul_le_mul_left d hlower
    _ ≤ Fintype.card V ^ 3 := hupper

theorem item13_triple_count_claim : Item13TripleCountClaim := by
  intro V _ _ G _ χ hfree4 hfree6 hJfree S hside d hd hmin
  exact item13_triple_count G χ hfree4 hfree6 hJfree S hside d hd hmin

theorem jensen_choose_three {ι : Type*} (s : Finset ι) (t : ι → ℕ)
    (hM : 0 < s.card) (hs : 4 * (s.card : ℝ) ≤ ∑ i ∈ s, (t i : ℝ)) :
    (∑ i ∈ s, (t i : ℝ)) ^ 3 ≤
      48 * (s.card : ℝ) ^ 2 * ∑ i ∈ s, (Nat.choose (t i) 3 : ℝ) := by
  let x : ι → ℝ := fun i => ((t i - 2 : ℕ) : ℝ)
  have hpoint (i : ι) (hi : i ∈ s) :
      (t i : ℝ) ≤ x i + 2 := by
    dsimp [x]
    by_cases ht : 2 ≤ t i
    · have heq : ((t i - 2 : ℕ) : ℝ) + 2 = t i := by
        exact_mod_cast (Nat.sub_add_cancel ht)
      rw [heq]
    · have hsmall : t i - 2 = 0 := by omega
      simp [hsmall]
      exact_mod_cast (show t i ≤ 2 by omega)
  have hsumBound : (∑ i ∈ s, (t i : ℝ)) ≤
      (∑ i ∈ s, x i) + 2 * s.card := by
    calc
      _ ≤ ∑ i ∈ s, (x i + 2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hpoint i hi
      _ = _ := by simp [Finset.sum_add_distrib, mul_comm]
  have hhalf : (∑ i ∈ s, (t i : ℝ)) ≤ 2 * (∑ i ∈ s, x i) := by
    have hM' : 2 * (s.card : ℝ) ≤ (∑ i ∈ s, (t i : ℝ)) / 2 := by linarith
    linarith
  have hxnonneg : ∀ i ∈ s, 0 ≤ x i := by
    intro i hi
    dsimp [x]
    positivity
  have hpows := pow_sum_le_card_mul_sum_pow (s := s) (f := x) hxnonneg 2
  have hchoose (i : ι) (hi : i ∈ s) :
      x i ^ 3 ≤ 6 * (Nat.choose (t i) 3 : ℝ) := by
    dsimp [x]
    by_cases ht : 2 ≤ t i
    · have hpow := Nat.pow_le_choose (α := ℝ) 3 (t i)
      have hformula : t i + 1 - 3 = t i - 2 := by omega
      simp only [hformula, Nat.factorial] at hpow
      nlinarith
    · have hzero : t i - 2 = 0 := by omega
      simp [hzero]
  have hsumChoose : (∑ i ∈ s, x i ^ 3) ≤
      6 * ∑ i ∈ s, (Nat.choose (t i) 3 : ℝ) := by
    calc
      _ ≤ ∑ i ∈ s, (6 * (Nat.choose (t i) 3 : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hchoose i hi
      _ = _ := by simp [Finset.mul_sum]
  calc
    _ ≤ 8 * (∑ i ∈ s, x i) ^ 3 := by
      have hxsum : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hxnonneg
      calc
        _ ≤ (2 * (∑ i ∈ s, x i)) ^ 3 := by gcongr
        _ = _ := by ring
    _ ≤ 8 * (s.card : ℝ) ^ 2 * (∑ i ∈ s, x i ^ 3) := by
      calc
        _ ≤ 8 * ((s.card : ℝ) ^ 2 * ∑ i ∈ s, x i ^ 3) := by
          gcongr
        _ = _ := by ring
    _ ≤ 48 * (s.card : ℝ) ^ 2 * ∑ i ∈ s, (Nat.choose (t i) 3 : ℝ) := by
      calc
        _ ≤ 8 * (s.card : ℝ) ^ 2 *
            (6 * ∑ i ∈ s, (Nat.choose (t i) 3 : ℝ)) := by
          gcongr
        _ = _ := by ring

/-- The Jensen step in item 15, with its explicit denominator constant. -/
theorem item15_choose_lower_bound {ι : Type*} (s : Finset ι) (t : ι → ℕ)
    (d N : ℝ) (hM : 0 < s.card)
    (hmean : 4 * (s.card : ℝ) ≤ ∑ i ∈ s, (t i : ℝ))
    (hstrong : d ^ 4 ≤ 8 * ∑ i ∈ s, (t i : ℝ))
    (hMN : (s.card : ℝ) ≤ N) (hd : 0 ≤ d) :
    d ^ 12 ≤ 24576 * N ^ 2 *
      ∑ i ∈ s, (Nat.choose (t i) 3 : ℝ) := by
  have hj := jensen_choose_three s t hM hmean
  have hs : 0 ≤ ∑ i ∈ s, (t i : ℝ) := by positivity
  calc
    d ^ 12 = (d ^ 4) ^ 3 := by ring
    _ ≤ (8 * ∑ i ∈ s, (t i : ℝ)) ^ 3 := by gcongr
    _ = 512 * (∑ i ∈ s, (t i : ℝ)) ^ 3 := by ring
    _ ≤ 512 * (48 * (s.card : ℝ) ^ 2 *
        ∑ i ∈ s, (Nat.choose (t i) 3 : ℝ)) := by gcongr
    _ = 24576 * (s.card : ℝ) ^ 2 *
        ∑ i ∈ s, (Nat.choose (t i) 3 : ℝ) := by ring
    _ ≤ 24576 * N ^ 2 *
        ∑ i ∈ s, (Nat.choose (t i) 3 : ℝ) := by gcongr

/-- The final incidence and triple-count arithmetic in item 15. -/
theorem item15_aggregate_bound {ι : Type*} (U : Finset ι) (C : ι → ℝ)
    (d N : ℝ) (Tcount : ℕ)
    (hd : 0 ≤ d) (hN : 0 ≤ N)
    (hlow : ∀ u ∈ U, d ^ 12 ≤ 24576 * N ^ 2 * C u)
    (hC : ∑ u ∈ U, C u ≤ 2 * (Tcount : ℝ))
    (hT : 6 * d * Tcount ≤ N ^ 3) :
    (U.card : ℝ) * d ^ 13 ≤ 8192 * N ^ 5 := by
  have hsum : (U.card : ℝ) * d ^ 12 ≤
      24576 * N ^ 2 * ∑ u ∈ U, C u := by
    calc
      _ = ∑ u ∈ U, d ^ 12 := by simp
      _ ≤ ∑ u ∈ U, (24576 * N ^ 2 * C u) := by
        apply Finset.sum_le_sum
        intro u hu
        exact hlow u hu
      _ = _ := by simp [Finset.mul_sum, mul_assoc]
  have hsum' : (U.card : ℝ) * d ^ 12 ≤
      49152 * N ^ 2 * Tcount := by
    calc
      _ ≤ 24576 * N ^ 2 * ∑ u ∈ U, C u := hsum
      _ ≤ 24576 * N ^ 2 * (2 * Tcount) := by gcongr
      _ = 49152 * N ^ 2 * Tcount := by ring
  calc
    (U.card : ℝ) * d ^ 13 = ((U.card : ℝ) * d ^ 12) * d := by ring
    _ ≤ (49152 * N ^ 2 * Tcount) * d := by gcongr
    _ = 8192 * N ^ 2 * (6 * d * Tcount) := by ring
    _ ≤ 8192 * N ^ 2 * N ^ 3 := by gcongr
    _ = 8192 * N ^ 5 := by ring

/-- The threshold supplies the mean and fourth-power hypotheses for item 15 Jensen. -/
theorem item15_walk_moment_to_jensen {d N M s : ℕ}
    (hd : 2 ≤ d) (hthreshold : 32 * N ≤ d ^ 4)
    (hM : M ≤ N) (hwalk : d * (d - 1) ^ 3 ≤ s) :
    4 * M ≤ s ∧ d ^ 4 ≤ 8 * s := by
  have hhalf : d ≤ 2 * (d - 1) := by omega
  have hpow : d ^ 3 ≤ (2 * (d - 1)) ^ 3 := by gcongr
  have hbase : d ^ 4 ≤ 8 * d * (d - 1) ^ 3 := by
    calc
      d ^ 4 = d * d ^ 3 := by ring
      _ ≤ d * (2 * (d - 1)) ^ 3 := Nat.mul_le_mul_left d hpow
      _ = 8 * d * (d - 1) ^ 3 := by ring
  have hstrong : d ^ 4 ≤ 8 * s := by
    exact hbase.trans (by nlinarith [Nat.mul_le_mul_left 8 hwalk])
  constructor
  · have hsN : 4 * N ≤ s := by omega
    omega
  · exact hstrong

/-- Item 15's local `C_u` lower bound when the walk sum is over unrelated partners. -/
theorem item15_cu_lower_of_walk_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (u : V) (d N : ℕ)
    [DecidablePred (fun v : V => v ≠ u ∧ ¬ Related G u v)]
    (hM : 0 < (S.filter (fun v => v ≠ u ∧ ¬ Related G u v)).card)
    (hMN : (S.filter (fun v => v ≠ u ∧ ¬ Related G u v)).card ≤ N)
    (hthreshold : 32 * N ≤ d ^ 4) (hd : 2 ≤ d)
    (hwalk : d * (d - 1) ^ 3 ≤
      ∑ v ∈ S.filter (fun v => v ≠ u ∧ ¬ Related G u v),
        (Z_uv G S u v).card) :
    (d : ℝ) ^ 12 ≤ 24576 * (N : ℝ) ^ 2 * (C_u G S u : ℝ) := by
  let P := S.filter (fun v => v ≠ u ∧ ¬ Related G u v)
  let t : V → ℕ := fun v => (Z_uv G S u v).card
  have hmoment := item15_walk_moment_to_jensen hd hthreshold hMN hwalk
  have hmean : 4 * (P.card : ℝ) ≤ ∑ v ∈ P, (t v : ℝ) := by
    exact_mod_cast hmoment.1
  have hstrong : (d : ℝ) ^ 4 ≤ 8 * ∑ v ∈ P, (t v : ℝ) := by
    exact_mod_cast hmoment.2
  have hbound := item15_choose_lower_bound P t (d : ℝ) (N : ℝ)
    hM hmean hstrong (by exact_mod_cast hMN) (by positivity)
  simpa [P, t, C_u] using hbound

/-- The local counts over vertices with at most two centers sum to at most twice
the number of counted triples. -/
theorem item15_sum_Cu_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G) (S : Finset V)
    (hside : ∀ x ∈ S, χ x = 0) :
    (∑ u ∈ U_S G S, (C_u G S u : ℝ)) ≤ 2 * (T_S G S).card := by
  classical
  have hrewrite :
      (∑ u ∈ U_S G S, (C_u G S u : ℝ)) =
        ∑ u ∈ U_S G S, ∑ T ∈ T_S G S,
          if u ∈ tripleCenters G S T then
            (((tripleCenters G S T).card - 1 : ℕ) : ℝ) else (0 : ℝ) := by
    apply Finset.sum_congr rfl
    intro u hu
    have huS : u ∈ S := (Finset.mem_filter.mp hu).1
    rw [item14_cu_identity G χ hfree4 hfree6 S hside u huS]
    simp only [Nat.cast_sum]
    rw [Finset.sum_filter]
  rw [hrewrite, Finset.sum_comm]
  calc
    (∑ T ∈ T_S G S, ∑ u ∈ U_S G S,
        if u ∈ tripleCenters G S T then
          (((tripleCenters G S T).card - 1 : ℕ) : ℝ) else (0 : ℝ))
        ≤ ∑ T ∈ T_S G S, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro T hT
      have hTmem := hT
      simp only [T_S, Finset.mem_filter, Finset.mem_univ, true_and] at hT
      let C := tripleCenters G S T
      let r := C.card
      have hr : 2 ≤ r := by simpa [C] using hT.2.2.2
      by_cases hthree : 3 ≤ r
      · have hzero : ∀ u ∈ U_S G S, u ∉ C := by
          intro u hu huc
          have hu' := (Finset.mem_filter.mp hu).2
          exact (not_lt_of_ge hthree) (hu' T hTmem (by simpa [C] using huc))
        have : (∑ u ∈ U_S G S,
            if u ∈ C then ((r - 1 : ℕ) : ℝ) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro u hu
          simp [hzero u hu]
        simpa [C, r] using this.le.trans (by norm_num)
      · have hr' : r = 2 := by omega
        rw [show (∑ u ∈ U_S G S,
            if u ∈ C then ((r - 1 : ℕ) : ℝ) else 0) =
            ((U_S G S).filter (fun u => u ∈ C)).card by
          have heq :
              (∑ u ∈ U_S G S, if u ∈ C then (1 : ℕ) else 0) =
                ((U_S G S).filter (fun u => u ∈ C)).card := by
            rw [← Finset.card_filter]
          simp only [hr', Nat.reduceSub, Nat.cast_one]
          exact_mod_cast heq]
        have hsub : (U_S G S).filter (fun u => u ∈ C) ⊆ C := by
          intro u hu
          exact (Finset.mem_filter.mp hu).2
        have hcard := Finset.card_le_card hsub
        have hC : C.card = 2 := by simpa [r] using hr'
        rw [hC] at hcard
        exact_mod_cast hcard
    _ = 2 * (T_S G S).card := by simp [mul_comm]

noncomputable def item15WalkEndpoints {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (u : V) : Finset V := by
  classical
  exact S.filter (fun v => v ≠ u ∧ ¬ Related G u v)

/-- Opposite color classes contribute no common related bases to `Z_uv`. -/
theorem item15_z_uv_empty_of_opposite_color {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (χ : G.Coloring (Fin 2)) {u v : V}
    (hu : χ u = 0) (hv : χ v ≠ 0) : Z_uv G Finset.univ u v = ∅ := by
  classical
  have hnot : ∀ w, ¬ (Related G u w ∧ Related G v w) := by
    intro w ⟨huw, hvw⟩
    apply hv
    exact (related_color_eq χ hvw).trans (related_color_eq χ huw).symm ▸ hu
  ext w
  simp [Z_uv, hnot w]

/-- On the zero side, restricting common related bases to the side loses none. -/
theorem item15_z_uv_eq_zSet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (χ : G.Coloring (Fin 2)) (S : Finset V)
    (hside : ∀ x, x ∈ S ↔ χ x = 0) {u v : V} (hu : χ u = 0) :
    Z_uv G S u v = ZSet G u v := by
  classical
  ext w
  simp only [Z_uv, ZSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, huw, hvw⟩
    exact ⟨huw, hvw⟩
  · rintro ⟨huw, hvw⟩
    refine ⟨(hside w).2 ?_, huw, hvw⟩
    exact (related_color_eq χ huw).symm.trans hu

/-- The unrestricted four-walk endpoint sum is supported on the chosen side. -/
theorem item15_walk_sum_side {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G) (S : Finset V)
    (hside : ∀ v, v ∈ S ↔ χ v = 0) {u : V} (hu : u ∈ S)
    (d : ℕ) (hd : ∀ v, d ≤ G.degree v) :
    d * (d - 1) ^ 3 ≤
      ∑ v ∈ item15WalkEndpoints G S u, (Z_uv G S u v).card := by
  classical
  let E := ValidWalkEndpoint G u
  let P := item15WalkEndpoints G S u
  let f : E → ℕ := fun v => (ZSet G u v.1).card
  let g : V → ℕ := fun v => (Z_uv G S u v).card
  have hcoloru : χ u = 0 := (hside u).1 hu
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun v : E => v.1 ∈ S) f
  have houtside :
      (∑ v : {v : E // v.1 ∉ S}, f v.1) = 0 := by
    apply Fintype.sum_eq_zero
    intro v
    have hvcolor : χ v.1.1 ≠ 0 := by
      intro heq
      exact v.2 ((hside v.1.1).2 heq)
    have hempty : ZSet G u v.1.1 = ∅ := by
      have ht := item15_z_uv_empty_of_opposite_color G χ hcoloru hvcolor
      simpa [Z_uv, ZSet] using ht
    simp [f, hempty]
  let e : {v : E // v.1 ∈ S} ≃ {v : V // v ∈ P} := {
    toFun v := ⟨v.1.1, by
      simpa [P, item15WalkEndpoints] using
        (show v.1.1 ∈ S ∧ v.1.1 ≠ u ∧ ¬ Related G u v.1.1 from
          ⟨v.2, v.1.2.1, v.1.2.2⟩)⟩
    invFun v := by
      have hv : v.1 ∈ S ∧ v.1 ≠ u ∧ ¬ Related G u v.1 := by
        simpa [P, item15WalkEndpoints] using v.2
      exact ⟨⟨v.1, ⟨hv.2.1, hv.2.2⟩⟩, hv.1⟩
    left_inv := by
      intro v
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv := by
      intro v
      apply Subtype.ext
      rfl
  }
  have hsame :
      (∑ v : {v : E // v.1 ∈ S}, f v.1) = ∑ v ∈ P, g v := by
    calc
      _ = ∑ v : {v : V // v ∈ P}, g v.1 :=
        Fintype.sum_equiv e (fun v => f v.1) (fun v => g v.1) (by
          intro v
          have hz := item15_z_uv_eq_zSet G χ S hside hcoloru
            (u := u) (v := v.1.1)
          simpa [e, f, g] using congrArg Finset.card hz.symm)
      _ = ∑ v ∈ P, g v :=
        (Finset.sum_subtype P (fun _ => Iff.rfl) g).symm
  have hglobal : (∑ v : E, f v) = ∑ v ∈ P, g v := by
    calc
      _ = (∑ v : {v : E // v.1 ∈ S}, f v.1) +
          (∑ v : {v : E // v.1 ∉ S}, f v.1) := hsplit.symm
      _ = ∑ v ∈ P, g v := by rw [houtside, add_zero, hsame]
  have hwalk := fourEdgeWalk_sum_lower χ hfree4 hfree6 u d hd
  rw [← hglobal]
  exact hwalk

/-- Item 15's one-side estimate from the local four-walk lower bounds. -/
theorem item15_bound_of_walks {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G) (S : Finset V)
    (hside : ∀ x ∈ S, χ x = 0) (N d : ℕ)
    (hV : Fintype.card V ≤ N) (hd : 2 ≤ d)
    (hthreshold : 32 * N ≤ d ^ 4)
    (hwalk : ∀ u ∈ U_S G S,
      d * (d - 1) ^ 3 ≤
        ∑ v ∈ item15WalkEndpoints G S u,
          (Z_uv G S u v).card)
    (htriple : 6 * d * (T_S G S).card ≤ N ^ 3) :
    (U_S G S).card ≤
      8192 * (N : ℝ) ^ 5 / (d : ℝ) ^ 13 := by
  classical
  have hS : S.card ≤ N := by
    calc
      S.card ≤ Fintype.card V := Finset.card_le_univ S
      _ ≤ N := hV
  have hU : (U_S G S).card ≤ N := by
    have hsub : U_S G S ⊆ S := by
      intro u hu
      exact (Finset.mem_filter.mp hu).1
    exact (Finset.card_le_card hsub).trans hS
  have hthreshold' : 32 * (N : ℝ) ≤ (d : ℝ) ^ 4 := by
    exact_mod_cast hthreshold
  have hlow : ∀ u ∈ U_S G S,
      (d : ℝ) ^ 12 ≤ 24576 * (N : ℝ) ^ 2 * (C_u G S u : ℝ) := by
    intro u hu
    let P := S.filter (fun v => v ≠ u ∧ ¬ Related G u v)
    have hPpos : 0 < P.card := by
      by_contra hp
      have hPempty : P = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hp)
      have hw := hwalk u hu
      have hzero : d * (d - 1) ^ 3 = 0 := by
        simpa [P, item15WalkEndpoints, hPempty] using hw
      have hpositive : 0 < d * (d - 1) ^ 3 := by
        have : 0 < d - 1 := by omega
        positivity
      omega
    have hPsize : P.card ≤ N := by
      have hsub : P ⊆ S := Finset.filter_subset _ _
      exact (Finset.card_le_card hsub).trans hS
    exact item15_cu_lower_of_walk_sum G S u d N hPpos hPsize
      hthreshold hd (by simpa [P, item15WalkEndpoints] using hwalk u hu)
  have hC := item15_sum_Cu_bound G χ hfree4 hfree6 S hside
  have htriple' : 6 * (d : ℝ) * (T_S G S).card ≤ (N : ℝ) ^ 3 := by
    exact_mod_cast htriple
  have haggregate := item15_aggregate_bound (U_S G S)
    (fun u => (C_u G S u : ℝ)) (d : ℝ) (N : ℝ) (T_S G S).card
    (by positivity) (by positivity) hlow hC htriple'
  have hdpos : 0 < (d : ℝ) ^ 13 := by positivity
  rw [le_div_iff₀ hdpos]
  nlinarith

/-- The four-walk sum and triple count give the discrete-threshold form of item 15. -/
theorem item15_bound_discrete_threshold {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (χ : G.Coloring (Fin 2))
    (hfree4 : C4Free G) (hfree6 : C6Free G)
    (hJfree : ∀ A ∈ J, A.2.Free G) (S : Finset V)
    (hside : ∀ x, x ∈ S ↔ χ x = 0) (d : ℕ)
    (hd : 2 ≤ d) (hthreshold : 32 * Fintype.card V ≤ d ^ 4)
    (hmin : ∀ v, d ≤ G.degree v) :
    (U_S G S).card ≤
      8192 * (Fintype.card V : ℝ) ^ 5 / (d : ℝ) ^ 13 := by
  have hside' : ∀ x ∈ S, χ x = 0 := fun x hx => (hside x).1 hx
  have htriple := item13_triple_count G χ hfree4 hfree6 hJfree S hside' d
    (by omega) hmin
  exact item15_bound_of_walks G χ hfree4 hfree6 S hside' (Fintype.card V) d
    le_rfl hd hthreshold
    (by
      intro u hu
      exact item15_walk_sum_side G χ hfree4 hfree6 S hside
        (Finset.mem_filter.mp hu).1 d hmin)
    htriple

/-- The stated power threshold implies the fourth-power threshold used by Jensen. -/
theorem item15_rpow_threshold_to_discrete {N d : ℕ} (hN : 1 ≤ N)
    (hd : 16 * Real.rpow (N : ℝ) ((5 : ℝ) / 16) ≤ d) :
    32 * N ≤ d ^ 4 := by
  let x : ℝ := N
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast hN
  have hpowid : (x ^ ((5 : ℝ) / 16)) ^ 4 = x ^ ((5 : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hlarge : x ≤ x ^ ((5 : ℝ) / 4) := by
    rw [show (5 : ℝ) / 4 = 1 + 1 / 4 by norm_num, Real.rpow_add (by positivity)]
    have hquarter : 1 ≤ x ^ ((1 : ℝ) / 4) :=
      Real.one_le_rpow hx (by norm_num)
    rw [Real.rpow_one]
    nlinarith
  have hdreal : 16 * x ^ ((5 : ℝ) / 16) ≤ (d : ℝ) := by
    exact_mod_cast hd
  have hfour : (16 * x ^ ((5 : ℝ) / 16)) ^ 4 ≤ (d : ℝ) ^ 4 := by
    have h := Real.rpow_le_rpow (by positivity) hdreal (by norm_num : (0 : ℝ) ≤ 4)
    convert h using 1 <;> norm_num [Real.rpow_natCast]
  have hfactor : (16 * x ^ ((5 : ℝ) / 16)) ^ 4 =
      65536 * x ^ ((5 : ℝ) / 4) := by
    rw [mul_pow, hpowid]
    norm_num
  have hmain : 32 * x ≤ (d : ℝ) ^ 4 := by
    calc
      32 * x ≤ 65536 * x ^ ((5 : ℝ) / 4) := by nlinarith
      _ = (16 * x ^ ((5 : ℝ) / 16)) ^ 4 := hfactor.symm
      _ ≤ (d : ℝ) ^ 4 := hfour
  have hmain' : 32 * (N : ℝ) ≤ (d : ℝ) ^ 4 := by simpa [x] using hmain
  exact_mod_cast hmain'

/-- The one-side estimate in item 15. -/
theorem item15_bound_claim : Item15BoundClaim := by
  classical
  intro V _ _ G _ χ hfree4 hfree6 hJfree S hside d hd hmin
  by_cases hN : 1 ≤ Fintype.card V
  · have hdiscrete := item15_rpow_threshold_to_discrete hN hd
    have hx : 1 ≤ (Fintype.card V : ℝ) := by exact_mod_cast hN
    have hpow : 1 ≤ Real.rpow (Fintype.card V : ℝ) ((5 : ℝ) / 16) :=
      Real.one_le_rpow hx (by norm_num)
    have hd2real : (2 : ℝ) ≤ d := by nlinarith [hd, hpow]
    have hd2 : 2 ≤ d := by exact_mod_cast hd2real
    exact item15_bound_discrete_threshold G χ hfree4 hfree6 hJfree S hside d
      hd2 hdiscrete hmin
  · have hVzero : Fintype.card V = 0 := by omega
    have hUzero : (U_S G S).card = 0 := by
      have hle := Finset.card_le_univ (U_S G S)
      rw [hVzero] at hle
      omega
    simp [hVzero, hUzero]

end L575U

import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Padding a forbidden-subgraph-free graph with isolated vertices

If `A` has no isolated vertices and `G` is an `A`-free graph on at most `n` vertices, then
`ex(n, A)` is at least the number of edges of `G`: adding isolated vertices cannot create a copy of
`A`, since every vertex of `A` lies on an edge.
-/

open Finset Fintype

namespace JustinSun.Erdos575

variable {V W : Type*} [Fintype V] [DecidableEq V]

/-- **Padding.** -/
theorem card_edgeFinset_le_extremalNumber_of_card_le {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : SimpleGraph W} (hA : ∀ w, ∃ w', A.Adj w w') (hfree : A.Free G) {n : ℕ}
    (hn : card V ≤ n) : #G.edgeFinset ≤ SimpleGraph.extremalNumber n A := by
  classical
  set V' := V ⊕ Fin (n - card V)
  have hcard : card V' = n := by simp [V']; omega
  set G' : SimpleGraph V' := G.map (Function.Embedding.inl)
  have hfree' : A.Free G' := by
    rintro ⟨φ⟩
    apply hfree
    -- every vertex of `A` is sent into `V`
    have hleft : ∀ w, ∃ v, φ w = Sum.inl v := by
      intro w
      obtain ⟨w', hww'⟩ := hA w
      have hadj := φ.toHom.map_adj hww'
      simp only [G', SimpleGraph.map_adj] at hadj
      obtain ⟨u, v, huv, hu, -⟩ := hadj
      exact ⟨u, hu.symm⟩
    choose ψ hψ using hleft
    refine ⟨⟨⟨ψ, fun {a b} hab => ?_⟩, fun a b hab => ?_⟩⟩
    · have hadj := φ.toHom.map_adj hab
      have ea : φ.toHom a = Sum.inl (ψ a) := hψ a
      have eb : φ.toHom b = Sum.inl (ψ b) := hψ b
      rw [ea, eb] at hadj
      simp only [G', SimpleGraph.map_adj] at hadj
      obtain ⟨u, v, huv, hu, hv⟩ := hadj
      have hu' : u = ψ a := Sum.inl_injective hu
      have hv' : v = ψ b := Sum.inl_injective hv
      rwa [← hu', ← hv']
    · apply φ.injective
      show φ a = φ b
      rw [hψ a, hψ b]
      exact congrArg Sum.inl hab
  have h := SimpleGraph.card_edgeFinset_le_extremalNumber hfree' (G := G')
  rw [hcard] at h
  calc #G.edgeFinset = #G'.edgeFinset := by
        simp only [G']; rw [SimpleGraph.card_edgeFinset_map]
    _ ≤ _ := h

end JustinSun.Erdos575

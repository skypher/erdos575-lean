import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Erdős Problem 575 (JustinSun Prize JSP-000465): compactness for bipartite extremal problems

Erdős–Simonovits [ES82]: let `𝓕` be a finite family of finite graphs containing a bipartite graph.
Is there a bipartite `G ∈ 𝓕` with `ex(n; G) ≪_𝓕 ex(n; 𝓕)`? The corrected form of the conjecture
(families all of whose members contain cycles; see `sources/oai_ch10_erdos575.txt`, §1.1,
display (1)) asks for `G ∈ 𝓕` and `C` with `ex(n, G) ≤ C · ex(n, 𝓕)` for all large `n`.

Answer: no. OpenAI, *Counterexamples to the compactness and degeneracy conjectures for extremal
numbers* (ten-proofs-oai.pdf, ch. 10, Theorem 1.1, August 2026): a finite nonempty family of
connected bipartite graphs, each containing a cycle, with `ex(n, 𝓕) = O(n^{4/3-1/48})` and
`ex(n, G) = Ω(n^{4/3})` for every member `G`.

Representation choices.
* A finite graph is `FinGraph := Σ v, SimpleGraph (Fin v)`; a family is a `Finset FinGraph`.
* `ex(n, G)` is Mathlib's `SimpleGraph.extremalNumber n G`; `ex(n, 𝓕)` is `exFamily n 𝓕`, defined
  the same way: the largest edge count of an `𝓕`-free graph on `Fin n`. (If no graph on `Fin n` is
  `𝓕`-free the value is `0`; this cannot happen when every member has an edge, since the empty
  graph is then `𝓕`-free.)
* "contains a cycle" is `¬ IsAcyclic`; "bipartite" is Mathlib's `IsBipartite` (2-colorable).
-/

open Finset

namespace JustinSun.Erdos575

/-- A finite simple graph, on the vertex type `Fin v`. -/
abbrev FinGraph := Σ v : ℕ, SimpleGraph (Fin v)

open scoped Classical in
/-- `ex(n, 𝓕)`: the maximum number of edges of a graph on `n` vertices containing no member of `𝓕`
as a subgraph. -/
noncomputable def exFamily (n : ℕ) (F : Finset FinGraph) : ℕ :=
  sup { G : SimpleGraph (Fin n) | ∀ A ∈ F, A.2.Free G } (#·.edgeFinset)

/-- **Erdős 575, negative answer (acceptance criterion).** There is a finite nonempty family `𝓕` of
bipartite graphs, each containing a cycle, such that no member `G` satisfies
`ex(n, G) ≤ C · ex(n, 𝓕)` for all sufficiently large `n`, for any constant `C`.

Demand sheet (consumers: Erdős's question as stated, and the corrected conjecture (1)):
* `𝓕` finite (`Finset`) and nonempty — both formulations quantify over such families.
* every member bipartite — makes `𝓕` contain a bipartite graph and makes every member a candidate
  "bipartite `G ∈ 𝓕`" (Erdős's form).
* every member contains a cycle — the hypothesis of the corrected form (1); it excludes the trivial
  forest counterexamples such as `{K_{1,2}, 2K_2}`.
* `¬ ∃ C, ∀ᶠ n, ex(n, G) ≤ C · ex(n, 𝓕)` for every member — the negation of the conclusion of (1);
  it also negates `ex(n; G) ≪_𝓕 ex(n; 𝓕)`.
* connectedness of the members (part of the source's Theorem 1.1) — no consumer uses it; dropped.
* the explicit exponents `4/3` and `4/3 - 1/48` — no consumer uses them; dropped from the statement
  (the proof goes through them). -/
def Stmt_erdos575 : Prop :=
  ∃ F : Finset FinGraph, F.Nonempty ∧
    (∀ A ∈ F, A.2.IsBipartite ∧ ¬ A.2.IsAcyclic) ∧
    ∀ A ∈ F, ¬ ∃ C : ℝ, ∀ᶠ n in Filter.atTop,
      (SimpleGraph.extremalNumber n A.2 : ℝ) ≤ C * exFamily n F

end JustinSun.Erdos575

import JustinSun.Erdos575.Upper.Bound
import JustinSun.Erdos575.Asm.Final

/-!
# Erdős Problem 575 (JustinSun Prize JSP-000465)

The Erdős–Simonovits compactness question has a negative answer: there is a finite nonempty family
of bipartite graphs, each containing a cycle, such that no member `G` satisfies
`ex(n, G) ≤ C · ex(n, 𝓕)` for all large `n` (OpenAI, *Counterexamples to the compactness and
degeneracy conjectures for extremal numbers*, 2026, Theorem 1.1).
-/

namespace JustinSun.Erdos575

/-- **Erdős Problem 575.** -/
theorem erdos575 : Stmt_erdos575 :=
  A575.erdos575_of_upper L575U.exFamily_le

end JustinSun.Erdos575

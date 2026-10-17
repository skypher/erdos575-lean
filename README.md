# Erdős Problem 575 in Lean 4

A complete, kernel-checked Lean 4 (v4.33.0) / Mathlib proof of the negative answer to **Erdős Problem
575** (the Erdős–Simonovits compactness question; Justin Sun Prize catalog **JSP-000465**).

**Statement** (`JustinSun/Erdos575/Statement.lean`, `Stmt_erdos575`): there is a finite nonempty
family 𝓕 of bipartite graphs, each containing a cycle, such that for no member G and no constant C
does `ex(n, G) ≤ C · ex(n, 𝓕)` hold for all sufficiently large n.

**Theorem**: `JustinSun.Erdos575.erdos575 : Stmt_erdos575` (`JustinSun/Erdos575/Main.lean`), depending
only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

The proof formalizes Theorem 1.1 of OpenAI, *Counterexamples to the Compactness and Degeneracy
Conjectures for Extremal Numbers* (2026): the family {C₄, C₆} ∪ J ∪ K of admissible quotients of two
subdivision templates has `ex(n, 𝓕) ≤ 32 n^{21/16}` for all n ≥ 1 (`JustinSun/Erdos575/Upper/`), while
every member has `ex(n, G) ≥ 2^{-4/3}·3^{-4} n^{4/3}` for n ≥ 80, witnessed by incidence graphs of
the symplectic generalized quadrangle W(q) over GF(2^j) and GF(3^j) (`JustinSun/Erdos575/Geometry/`,
`JustinSun/Erdos575/Asm/`).

## Check

```
lake exe cache get
lake build
lake env lean Checks/Erdos575.lean
```

`Checks/` states each main theorem with its exact type and fails unless it uses only the three
standard axioms. The CI workflow runs one job per check.

Formalized by skypher with AI assistance (Claude Code, OpenAI Codex agents).

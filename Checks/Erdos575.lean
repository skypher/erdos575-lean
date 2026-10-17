import JustinSun.AxiomAudit
import JustinSun.Erdos575.Main
open JustinSun.Erdos575

/-- Erdős Problem 575: a finite nonempty family of bipartite graphs with cycles such that no member
has extremal number bounded by a constant times the family's. -/
theorem check_erdos575 : Stmt_erdos575 := erdos575

#require_standard_axioms check_erdos575
#print axioms JustinSun.Erdos575.erdos575

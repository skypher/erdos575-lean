import JustinSun.AxiomAudit
import JustinSun.Erdos575.Assembly
open JustinSun.Erdos575

/-- Conditional: Erdős 575 follows from the two bounds of Theorem 1.1 (still open in this
repository). -/
theorem check_575_reduction : Stmt_575_bounds → Stmt_erdos575 := erdos575_of_bounds

#require_standard_axioms check_575_reduction

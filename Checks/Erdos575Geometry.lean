import JustinSun.AxiomAudit
import JustinSun.Erdos575.Geometry.LineSide
open L575G

/-- The symplectic quadrangle `W(q)`: no 4- or 6-cycles, no point-side J-pattern, no line-side
J-pattern for even `q`, and every line triad has 0 or 2 common centres for odd `q`
(blueprint items 22–25 of Erdős 575, as consumed by items 26 and 29). -/
theorem check_575_geometry (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    (SimpleGraph.cycleGraph 4).Free (Iq F) ∧ (SimpleGraph.cycleGraph 6).Free (Iq F) ∧
      noPointJPattern_statement F ∧ noEvenLineJPattern_statement F ∧
      oddLineTriadCenters_statement F :=
  ⟨Iq_cycle4_free F, Iq_cycle6_free F, noPointJPattern F, noEvenLineJPattern F,
    oddLineTriadCenters F⟩

#require_standard_axioms check_575_geometry

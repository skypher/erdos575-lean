import JustinSun.Erdos575.Geometry.Patterns
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.BilinearForm.Hom
namespace L575G
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]
/-- Complementary isotropic lines with trivial intersection span the ambient space. -/
theorem LS1 {y z : Lines F} (h : y.1 ⊓ z.1 = ⊥) : IsCompl y.1 z.1 := by
  refine ⟨disjoint_iff.mpr h, codisjoint_iff.mpr ?_⟩; apply Submodule.eq_top_of_finrank_eq
  have hs := Submodule.finrank_sup_add_finrank_inf_eq y.1 z.1; rw [y.2.1, z.2.1, h, finrank_bot] at hs
  have hdim : Module.finrank F (y.1 ⊔ z.1 : Submodule F (V F)) = 4 := by omega
  simpa [finrank_top, V] using hdim
/-- A plane complementary to two transverse isotropic planes is a linear graph. -/
theorem LS2 {x y z : Lines F} (hyz : y.1 ⊓ z.1 = ⊥)
    (hxy : x.1 ⊓ y.1 = ⊥) (hxz : x.1 ⊓ z.1 = ⊥) :
    ∃ T : y.1 →ₗ[F] z.1, Function.Injective T ∧
      x.1 = LinearMap.range (y.1.subtype + z.1.subtype.comp T) := by
  let hcomp := LS1 F hyz
  let E := Submodule.prodEquivOfIsCompl y.1 z.1 hcomp
  let p : x.1 →ₗ[F] y.1 := (LinearMap.fst F y.1 z.1).comp (E.symm.toLinearMap.comp x.1.subtype)
  let s : x.1 →ₗ[F] z.1 := (LinearMap.snd F y.1 z.1).comp (E.symm.toLinearMap.comp x.1.subtype)
  have hp : Function.Injective p := by
    intro u v huv
    apply Subtype.ext
    have hzero : p (u - v) = 0 := by simp [huv]
    have hproj : (E.symm ((u - v : x.1) : V F)).1 = 0 := by change p (u-v) = 0; exact hzero
    have huvz : ((u - v : x.1) : V F) ∈ z.1 :=
      (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero (p := y.1) (q := z.1) hcomp).mp hproj
    have hmem : ((u - v : x.1) : V F) ∈ x.1 ⊓ z.1 := ⟨(u-v).property, huvz⟩; rw [hxz] at hmem
    have hz : ((u - v : x.1) : V F) = 0 := by simpa using hmem
    have huvEq : u = v := by apply Subtype.ext; exact sub_eq_zero.mp hz
    exact congrArg Subtype.val huvEq
  have hk : LinearMap.ker p = ⊥ := LinearMap.ker_eq_bot.mpr hp
  have hrank : Module.finrank F (LinearMap.range p) = 2 := by have h := LinearMap.finrank_range_add_finrank_ker p; rw [hk, finrank_bot, x.2.1] at h; exact h
  have hsurj : Function.Surjective p := by
    have htop : LinearMap.range p = ⊤ := by apply Submodule.eq_top_of_finrank_eq; simpa [y.2.1, finrank_top] using hrank
    exact LinearMap.range_eq_top.mp htop
  let e : x.1 ≃ₗ[F] y.1 := LinearEquiv.ofBijective p ⟨hp, hsurj⟩
  let T : y.1 →ₗ[F] z.1 := s.comp e.symm.toLinearMap
  let g : y.1 →ₗ[F] V F := y.1.subtype + z.1.subtype.comp T
  have hgraph (a : y.1) : g a = (e.symm a : V F) := by
    have hp' : p (e.symm a) = a := e.apply_symm_apply a
    have hs' : s (e.symm a) = T a := rfl
    have hpair : E.symm (e.symm a : V F) = (a, T a) := by apply Prod.ext <;> simp [p, s, T, E] <;> assumption
    have hv := E.apply_symm_apply (e.symm a : V F); rw [hpair] at hv
    change (a : V F) + T a = (e.symm a : V F) at hv
    change (a : V F) + T a = (e.symm a : V F); exact hv
  refine ⟨T, ?_, ?_⟩
  · intro a b hab
    have hdiff' : s (e.symm a) = s (e.symm b) := by simpa [T] using hab
    have hdiff : s (e.symm a - e.symm b) = 0 := by rw [map_sub, hdiff', sub_self]
    have hproj : (E.symm ((e.symm a - e.symm b : x.1) : V F)).2 = 0 := by change s (e.symm a - e.symm b) = 0; exact hdiff
    have hY : ((e.symm a - e.symm b : x.1) : V F) ∈ y.1 :=
      (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero (p := y.1) (q := z.1) hcomp).mp hproj
    have hmem : ((e.symm a - e.symm b : x.1) : V F) ∈ x.1 ⊓ y.1 := ⟨(e.symm a - e.symm b).property, hY⟩; rw [hxy] at hmem
    have hz : ((e.symm a - e.symm b : x.1) : V F) = 0 := by simpa using hmem
    have heq : e.symm a = e.symm b := by apply Subtype.ext; exact sub_eq_zero.mp hz
    calc a = p (e.symm a) := (e.apply_symm_apply a).symm
      _ = p (e.symm b) := congrArg p heq
      _ = b := e.apply_symm_apply b
  · apply le_antisymm
    · intro v hv
      let u : x.1 := ⟨v, hv⟩
      refine ⟨p u, ?_⟩
      have hu : e.symm (p u) = u := e.symm_apply_apply u; rw [hgraph]
      exact congrArg Subtype.val hu
    · intro v hv
      obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hv
      rw [← ha, hgraph a]
      exact (e.symm a).property
theorem LS3 {x y z : Lines F} (hcomp : IsCompl y.1 z.1)
    (T : y.1 →ₗ[F] z.1) (hT : Function.Injective T)
    (hgraph : x.1 = LinearMap.range (y.1.subtype + z.1.subtype.comp T)) :
    (∀ a b : y.1, omega F a (T b) = omega F b (T a)) ∧
    (∀ a : y.1, (∀ b : y.1, omega F a (T b) = 0) → a = 0) := by
  have hmem (a : y.1) : (a : V F) + T a ∈ x.1 := by rw [hgraph]; exact LinearMap.mem_range.mpr ⟨a, rfl⟩
  have hsurj : Function.Surjective T := by
    have hk : LinearMap.ker T = ⊥ := LinearMap.ker_eq_bot.mpr hT; have hr := LinearMap.finrank_range_add_finrank_ker T
    rw [hk, finrank_bot, y.2.1] at hr
    have htop : LinearMap.range T = ⊤ := by apply Submodule.eq_top_of_finrank_eq; simpa [z.2.1, finrank_top] using hr
    exact LinearMap.range_eq_top.mp htop
  constructor
  · intro a b
    have hx := x.2.2 _ (hmem a) _ (hmem b)
    have hy := y.2.2 a.1 a.2 b.1 b.2
    have hz := z.2.2 (T a).1 (T a).2 (T b).1 (T b).2
    change omegaForm F ((a : V F) + T a) ((b : V F) + T b) = 0 at hx
    change omegaForm F a b = 0 at hy
    change omegaForm F (T a) (T b) = 0 at hz
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right] at hx
    have ha := (omega_isAlt F).neg_eq (b : V F) (T a)
    change -omega F b (T a) = omega F (T a) b at ha
    simp only [omegaForm_apply] at hx hy hz
    rw [← ha, hy, hz] at hx
    linear_combination hx
  · intro a hzero
    have hy : (a : V F) ∈ orthogonal F y.1 := by intro b hb; have h := y.2.2 b hb a.1 a.2; change omegaForm F b a = 0 at h; simpa [omegaForm_apply] using h
    have hz : (a : V F) ∈ orthogonal F z.1 := by
      intro b hb
      obtain ⟨c, hc⟩ := hsurj ⟨b, hb⟩
      have h := hzero c
      have ha := (omega_isAlt F).neg_eq a.1 (T c).1
      change -omega F a (T c) = omega F (T c) a at ha
      rw [h] at ha
      simpa [omegaForm_apply, hc] using ha.symm
    have htop : y.1 ⊔ z.1 = ⊤ := hcomp.sup_eq_top
    have horth : (a : V F) ∈ orthogonal F (⊤ : Submodule F (V F)) := by rw [← htop, orthogonal_sup]; exact ⟨hy, hz⟩
    have hbot : (a : V F) ∈ (⊥ : Submodule F (V F)) := by
      rw [← orthogonal_top_eq_bot F]
      exact horth
    have ha0 : (a : V F) = 0 := by simpa using hbot
    exact Subtype.ext ha0
theorem LS4_root_span_finrank_two {y z : Lines F} (hcomp : IsCompl y.1 z.1)
    (T : y.1 →ₗ[F] z.1) (hT : Function.Injective T) (a : y.1) (ha : a ≠ 0) :
    Module.finrank F (Submodule.span F ({(a : V F), (T a : V F)} : Set (V F))) = 2 := by
  have hTa : (T a : V F) ≠ 0 := by
    intro hz
    have hz' : T a = 0 := Subtype.ext hz
    apply ha
    apply hT
    simpa using hz'
  have hLI : LinearIndependent F ![(a : V F), (T a : V F)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hsY : s • (a : V F) ∈ y.1 := y.1.smul_mem s a.property
    have htZ : t • (T a : V F) ∈ z.1 := z.1.smul_mem t (T a).property
    have hsZ : s • (a : V F) ∈ z.1 := by
      have heq : s • (a : V F) = -(t • (T a : V F)) := by rw [eq_neg_iff_add_eq_zero]; exact hst
      rw [heq]
      exact z.1.neg_mem htZ
    have hsbot : s • (a : V F) ∈ (⊥ : Submodule F (V F)) := by
      have hm : s • (a : V F) ∈ y.1 ⊓ z.1 := ⟨hsY, hsZ⟩
      rw [hcomp.disjoint.eq_bot] at hm
      exact hm
    have hs0 : s • (a : V F) = 0 := by simpa using hsbot
    have hs : s = 0 := (smul_eq_zero.mp hs0).resolve_right (by simpa using ha)
    have ht0 : t • (T a : V F) = 0 := by rw [hs, zero_smul, zero_add] at hst; simpa using hst
    have ht : t = 0 := (smul_eq_zero.mp ht0).resolve_right hTa
    exact ⟨hs, ht⟩
  have hrange : Set.range ![(a : V F), (T a : V F)] = {(a : V F), (T a : V F)} := by
    ext v
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all
    · rintro (h | h)
      · exact ⟨0, by simpa using h.symm⟩
      · exact ⟨1, by simpa using h.symm⟩
  rw [← hrange, finrank_span_eq_card hLI]
  simp
theorem LS4_center_to_root {x y z C : Lines F}
    (hcomp : IsCompl y.1 z.1) (T : y.1 →ₗ[F] z.1)
    (hT : Function.Injective T)
    (hgraph : x.1 = LinearMap.range (y.1.subtype + z.1.subtype.comp T))
    (hcenter : C ∈ LineTriadCenters F x y z) :
    ∃ a : y.1, a ≠ 0 ∧ omega F a (T a) = 0 ∧
      C.1 = Submodule.span F ({(a : V F), (T a : V F)} : Set (V F)) := by
  classical
  rcases hcenter with ⟨hCx, hCy, hCz⟩
  rcases (lineRelated_symm F hCy).2 with ⟨P, hPC, hPy⟩
  rcases (lineRelated_symm F hCz).2 with ⟨Q, hQC, hQz⟩
  rcases hCx.2 with ⟨R, hRx, hRC⟩
  have hPQ : P ≠ Q := by
    intro h
    have hmem : P.1 ≤ y.1 ⊓ z.1 := le_inf hPy (h ▸ hQz)
    have hzero : P.1 ≤ (⊥ : Submodule F (V F)) := le_trans hmem (le_of_eq hcomp.disjoint.eq_bot)
    have hdim := Submodule.finrank_mono hzero
    rw [P.2] at hdim
    simp at hdim
  have hspan : P.1 ⊔ Q.1 = C.1 := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le hPC hQC)
    rw [point_sup_finrank_two F hPQ, C.2.1]
  obtain ⟨r, hr0⟩ := (Module.finrank_pos_iff_exists_ne_zero.mp (by rw [R.2]; norm_num : 0 < Module.finrank F R.1))
  have hrx : r.1 ∈ x.1 := hRx r.2
  have hrc : r.1 ∈ C.1 := hRC r.2
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp (hgraph ▸ hrx)
  have hra : (r.1 : V F) = (a : V F) + T a := ha.symm
  have hrPQ : r.1 ∈ P.1 ⊔ Q.1 := hspan ▸ hrc
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hrPQ
  have heq : (a : V F) + T a = p + q := hra.symm.trans hpq.symm
  have hdiff : (a : V F) - p = q - T a := by
    apply (sub_eq_sub_iff_add_eq_add).2
    simpa [add_comm] using heq
  have hleft : (a : V F) - p ∈ y.1 := y.1.sub_mem a.2 (hPy hp)
  have hright : q - T a ∈ z.1 := z.1.sub_mem (hQz hq) (T a).2
  have hzero : (a : V F) - p = 0 := by
    have hm : (a : V F) - p ∈ y.1 ⊓ z.1 := ⟨hleft, hdiff ▸ hright⟩
    have hb := hcomp.disjoint.eq_bot
    rw [hb] at hm
    simpa using hm
  have hpa : (a : V F) = p := sub_eq_zero.mp hzero
  have hqTa : q = T a := by
    have hqt : q - T a = 0 := by rw [← hdiff, hzero]
    exact sub_eq_zero.mp hqt
  have haC : (a : V F) ∈ C.1 := hPC (hpa ▸ hp)
  have hTaC : (T a).1 ∈ C.1 := hqTa ▸ hQC hq
  have hroot := C.2.2 (a : V F) haC (T a).1 hTaC
  have ha_ne : a ≠ 0 := by
    intro he
    apply hr0
    apply Subtype.ext
    simpa [he] using hra
  have hle : Submodule.span F ({(a : V F), (T a : V F)} : Set (V F)) ≤ C.1 := by
    apply Submodule.span_le.mpr
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw
    · rw [hw]
      exact hPC (hpa ▸ hp)
    · rw [hw, ← hqTa]
      exact hQC hq
  have hrank := LS4_root_span_finrank_two F hcomp T hT a ha_ne
  have hspanEq : Submodule.span F ({(a : V F), (T a : V F)} : Set (V F)) = C.1 :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hrank, C.2.1])
  exact ⟨a, ha_ne, hroot, hspanEq.symm⟩
theorem LS4_center_graph_span {x y z C : Lines F}
    (hcomp : IsCompl y.1 z.1) (T : y.1 →ₗ[F] z.1) (hT : Function.Injective T)
    (hgraph : x.1 = LinearMap.range (y.1.subtype + z.1.subtype.comp T))
    (hcenter : C ∈ LineTriadCenters F x y z) :
    ∃ a : y.1, a ≠ 0 ∧ C.1 = Submodule.span F ({(a : V F), (T a : V F)} : Set (V F)) := by
  obtain ⟨a, ha, _, hspan⟩ := LS4_center_to_root F hcomp T hT hgraph hcenter
  exact ⟨a, ha, hspan⟩
set_option maxHeartbeats 600000 in
theorem LS4_same_root_line_centers_equal {y z : Lines F}
    (T : y.1 →ₗ[F] z.1) {C D : Lines F} {a b : y.1}
    (hC : C.1 = Submodule.span F ({(a : V F), (T a : V F)} : Set (V F)))
    (hD : D.1 = Submodule.span F ({(b : V F), (T b : V F)} : Set (V F)))
    (hline : Submodule.span F {(a : V F)} = Submodule.span F {(b : V F)}) : C = D := by
  have hamem : (a : V F) ∈ Submodule.span F {(b : V F)} := by
    rw [← hline]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hamem
  have hbmem : (b : V F) ∈ Submodule.span F {(a : V F)} := by
    rw [hline]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hbmem
  have hrs : r • b = a := Subtype.ext hr
  have hss : s • a = b := Subtype.ext hs
  have hTa : (T a : V F) = r • (T b : V F) := by
    calc
      (T a : V F) = (T (r • b) : V F) := by rw [← hrs]
      _ = r • (T b : V F) := by simpa using congrArg Subtype.val (map_smul T r b)
  have hTb : (T b : V F) = s • (T a : V F) := by
    calc
      (T b : V F) = (T (s • a) : V F) := by rw [← hss]
      _ = s • (T a : V F) := by simpa using congrArg Subtype.val (map_smul T s a)
  have haPair : (a : V F) ∈ Submodule.span F ({(b : V F), (T b : V F)} : Set (V F)) := by
    rw [← hr]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hTaPair : (T a : V F) ∈ Submodule.span F ({(b : V F), (T b : V F)} : Set (V F)) := by
    rw [hTa]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hbPair : (b : V F) ∈ Submodule.span F ({(a : V F), (T a : V F)} : Set (V F)) := by
    rw [← hs]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hTbPair : (T b : V F) ∈ Submodule.span F ({(a : V F), (T a : V F)} : Set (V F)) := by
    rw [hTb]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hle : Submodule.span F ({(a : V F), (T a : V F)} : Set (V F)) ≤
      Submodule.span F ({(b : V F), (T b : V F)} : Set (V F)) := by
    apply Submodule.span_le.mpr
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw
    · rw [hw]
      exact haPair
    · rw [hw]
      exact hTaPair
  have hge : Submodule.span F ({(b : V F), (T b : V F)} : Set (V F)) ≤
      Submodule.span F ({(a : V F), (T a : V F)} : Set (V F)) := by
    apply Submodule.span_le.mpr
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw
    · rw [hw]
      exact hbPair
    · rw [hw]
      exact hTbPair
  have hspan := le_antisymm hle hge
  apply Subtype.ext
  rw [hC, hD]
  exact hspan
theorem LS4_distinct_centers_have_distinct_roots {x y z C D : Lines F}
    (hcomp : IsCompl y.1 z.1) (T : y.1 →ₗ[F] z.1) (hT : Function.Injective T)
    (hgraph : x.1 = LinearMap.range (y.1.subtype + z.1.subtype.comp T))
    (hC : C ∈ LineTriadCenters F x y z) (hD : D ∈ LineTriadCenters F x y z)
    (hCD : C ≠ D) :
    ∃ a b : y.1, a ≠ 0 ∧ b ≠ 0 ∧ omega F a (T a) = 0 ∧ omega F b (T b) = 0 ∧
      Submodule.span F {(a : V F)} ≠ Submodule.span F {(b : V F)} := by
  obtain ⟨a, ha, hrootA, hspanC⟩ := LS4_center_to_root F hcomp T hT hgraph hC
  obtain ⟨b, hb, hrootB, hspanD⟩ := LS4_center_to_root F hcomp T hT hgraph hD
  refine ⟨a, b, ha, hb, hrootA, hrootB, ?_⟩
  intro hline
  apply hCD
  exact LS4_same_root_line_centers_equal F T hspanC hspanD hline
theorem LS4_root_span_isotropic {y z : Lines F} (T : y.1 →ₗ[F] z.1)
    (a : y.1) (hroot : omega F a (T a) = 0) :
    Submodule.span F ({(a : V F), (T a : V F)} : Set (V F)) ≤
      orthogonal F (Submodule.span F ({(a : V F), (T a : V F)} : Set (V F))) := by
  let S : Submodule F (V F) := Submodule.span F ({(a : V F), (T a : V F)} : Set (V F))
  have haa : omega F a a = 0 := (omega_isAlt F).self_eq_zero a
  have hta : omega F (T a) a = 0 := by
    have h := (omega_isAlt F).neg_eq a (T a)
    change -omega F a (T a) = omega F (T a) a at h
    rw [hroot] at h
    simpa using h.symm
  have ha : (a : V F) ∈ orthogonal F S := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem b hb =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
        rcases hb with hb | hb
        · subst b; simpa [omegaForm_apply] using haa
        · subst b; simpa [omegaForm_apply] using hta
    | zero => simp [omegaForm_apply]
    | add u v hu hv hu0 hv0 =>
        change omegaForm F (u + v) a = 0
        rw [LinearMap.BilinForm.add_left, hu0, hv0]
        simp
    | smul c v hv hv0 =>
        change omegaForm F (c • v) a = 0
        rw [LinearMap.BilinForm.smul_left, hv0]
        simp
  have hTa : (T a : V F) ∈ orthogonal F S := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem b hb =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
        rcases hb with hb | hb
        · subst b; simpa [omegaForm_apply] using hroot
        · subst b; exact (omega_isAlt F).self_eq_zero (T a)
    | zero => simp [omegaForm_apply]
    | add u v hu hv hu0 hv0 =>
        change omegaForm F (u + v) (T a) = 0
        rw [LinearMap.BilinForm.add_left, hu0, hv0]
        simp
    | smul c v hv hv0 =>
        change omegaForm F (c • v) (T a) = 0
        rw [LinearMap.BilinForm.smul_left, hv0]
        simp
  change S ≤ orthogonal F S
  apply Submodule.span_le.2
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with hv | hv
  · simpa [hv] using ha
  · simpa [hv] using hTa
theorem LS4_root_line {y z : Lines F} (hcomp : IsCompl y.1 z.1)
    (T : y.1 →ₗ[F] z.1) (hT : Function.Injective T) (a : y.1)
    (ha : a ≠ 0) (hroot : omega F a (T a) = 0) :
    ∃ C : Lines F, C.1 = Submodule.span F ({(a : V F), (T a : V F)} : Set (V F)) := by
  let S : Submodule F (V F) := Submodule.span F ({(a : V F), (T a : V F)} : Set (V F))
  have hrank : Module.finrank F S = 2 := by
    simpa [S] using LS4_root_span_finrank_two F hcomp T hT a ha
  have horth := LS4_root_span_isotropic F T a hroot
  have hiso : ∀ u ∈ S, ∀ v ∈ S, omega F u v = 0 := by
    intro u hu v hv
    have huv := horth hu v hv
    have hAlt := (omega_isAlt F).neg_eq v u
    change -omega F v u = omega F u v at hAlt
    rw [show omega F v u = 0 by simpa [omegaForm_apply] using huv] at hAlt
    simpa using hAlt.symm
  refine ⟨⟨S, hrank, hiso⟩, rfl⟩
theorem LS4_root_is_center {x y z : Lines F}
    (hyz : y.1 ⊓ z.1 = ⊥) (hxy : x.1 ⊓ y.1 = ⊥) (hxz : x.1 ⊓ z.1 = ⊥)
    (T : y.1 →ₗ[F] z.1) (hT : Function.Injective T)
    (hgraph : x.1 = LinearMap.range (y.1.subtype + z.1.subtype.comp T))
    (a : y.1) (ha : a ≠ 0) (hroot : omega F a (T a) = 0) :
    ∃ C : Lines F, C ∈ LineTriadCenters F x y z ∧
      C.1 = Submodule.span F ({(a : V F), (T a : V F)} : Set (V F)) := by
  obtain ⟨C, hC⟩ := LS4_root_line F (LS1 F hyz) T hT a ha hroot
  have hTa : (T a : V F) ≠ 0 := by
    intro hz
    apply ha
    apply hT
    apply Subtype.ext
    simpa using hz
  have hsum : (a : V F) + T a ≠ 0 := by
    intro hs
    have hz : (a : V F) ∈ z.1 := by
      have he : (a : V F) = -(T a : V F) := eq_neg_iff_add_eq_zero.mpr hs
      rw [he]
      exact z.1.neg_mem (T a).property
    have hb : (a : V F) ∈ (⊥ : Submodule F (V F)) := by
      have hm : (a : V F) ∈ y.1 ⊓ z.1 := ⟨a.property, hz⟩
      rw [hyz] at hm
      exact hm
    exact ha (Subtype.ext (by simpa using hb))
  let Pa : Points F := ⟨Submodule.span F {(a : V F)}, finrank_span_singleton (by simpa using ha)⟩
  let PT : Points F := ⟨Submodule.span F {(T a : V F)}, finrank_span_singleton hTa⟩
  let Ps : Points F := ⟨Submodule.span F {(a : V F) + T a}, finrank_span_singleton hsum⟩
  have hPaY : Pa.1 ≤ y.1 := (Submodule.span_singleton_le_iff_mem _ _).mpr a.property
  have hPTZ : PT.1 ≤ z.1 := (Submodule.span_singleton_le_iff_mem _ _).mpr (T a).property
  have hPaC : Pa.1 ≤ C.1 := by
    rw [hC]
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    exact Submodule.subset_span (by simp)
  have hPTC : PT.1 ≤ C.1 := by
    rw [hC]
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    exact Submodule.subset_span (by simp)
  have hPsC : Ps.1 ≤ C.1 := by
    rw [hC]
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    exact Submodule.add_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  have hPsX : Ps.1 ≤ x.1 := by
    rw [hgraph]
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    exact LinearMap.mem_range.mpr ⟨a, by simp⟩
  have hCy : C ≠ y := by
    intro h
    have ht : (T a : V F) ∈ C.1 := (Submodule.span_singleton_le_iff_mem _ _).mp hPTC
    rw [h] at ht
    have hb : (T a : V F) ∈ (⊥ : Submodule F (V F)) := by
      have hm : (T a : V F) ∈ y.1 ⊓ z.1 := ⟨ht, (T a).property⟩
      rw [hyz] at hm
      exact hm
    exact hTa (by simpa using hb)
  have hCz : C ≠ z := by
    intro h
    have haZ : (a : V F) ∈ C.1 := (Submodule.span_singleton_le_iff_mem _ _).mp hPaC
    rw [h] at haZ
    have hb : (a : V F) ∈ (⊥ : Submodule F (V F)) := by
      have hm : (a : V F) ∈ y.1 ⊓ z.1 := ⟨a.property, haZ⟩
      rw [hyz] at hm
      exact hm
    exact ha (Subtype.ext (by simpa using hb))
  have hCx : C ≠ x := by
    intro h
    have haX : (a : V F) ∈ C.1 := (Submodule.span_singleton_le_iff_mem _ _).mp hPaC
    rw [h] at haX
    have hb : (a : V F) ∈ (⊥ : Submodule F (V F)) := by
      have hm : (a : V F) ∈ x.1 ⊓ y.1 := ⟨haX, a.property⟩
      rw [hxy] at hm
      exact hm
    exact ha (Subtype.ext (by simpa using hb))
  refine ⟨C, ?_, hC⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨Ne.symm hCx, Ps, hPsX, hPsC⟩
  · exact ⟨Ne.symm hCy, Pa, hPaY, hPaC⟩
  · exact ⟨Ne.symm hCz, PT, hPTZ, hPTC⟩
theorem LS5 {y : Lines F} (P Q : Points F) (hPQ : P ≠ Q)
    (hPy : P.1 ≤ y.1) (hQy : Q.1 ≤ y.1) (htwo : (2 : F) = 0)
    (B : LinearMap.BilinForm F y.1) (hsym : ∀ a b, B a b = B b a)
    (hP : ∀ a, ∀ ha : a ∈ P.1, B ⟨a, hPy ha⟩ ⟨a, hPy ha⟩ = 0)
    (hQ : ∀ a, ∀ ha : a ∈ Q.1, B ⟨a, hQy ha⟩ ⟨a, hQy ha⟩ = 0) :
    ∀ v : y.1, B v v = 0 := by
  have hspan : P.1 ⊔ Q.1 = y.1 := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le hPy hQy)
    rw [point_sup_finrank_two F hPQ, y.2.1]
  intro v
  have hv : (v : V F) ∈ P.1 ⊔ Q.1 := by rw [hspan]; exact v.property
  rcases Submodule.mem_sup.mp hv with ⟨a, ha, b, hb, hab⟩
  let A : y.1 := ⟨a, hPy ha⟩; let C : y.1 := ⟨b, hQy hb⟩
  have hv' : v = A + C := by apply Subtype.ext; exact hab.symm
  rw [hv']
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right]
  rw [hP a ha, hQ b hb, hsym A C]
  calc
    0 + B C A + (B C A + 0) = (2 : F) * B C A := by ring
    _ = 0 := by rw [htwo]; ring
theorem LS5_ringChar {y : Lines F} (P Q : Points F) (hPQ : P ≠ Q)
    (hPy : P.1 ≤ y.1) (hQy : Q.1 ≤ y.1) (hchar : ringChar F = 2)
    (B : LinearMap.BilinForm F y.1) (hsym : ∀ a b, B a b = B b a)
    (hP : ∀ a, ∀ ha : a ∈ P.1, B ⟨a, hPy ha⟩ ⟨a, hPy ha⟩ = 0)
    (hQ : ∀ a, ∀ ha : a ∈ Q.1, B ⟨a, hQy ha⟩ ⟨a, hQy ha⟩ = 0) :
    ∀ v : y.1, B v v = 0 := by
  have htwo : (2 : F) = 0 := by
    haveI : CharP F 2 := ringChar.of_eq hchar
    exact CharP.cast_eq_zero F 2
  exact LS5 F P Q hPQ hPy hQy htwo B hsym hP hQ
theorem LS6_alternating_of_two_roots {y : Lines F} (P Q : Points F) (hPQ : P ≠ Q)
    (hPy : P.1 ≤ y.1) (hQy : Q.1 ≤ y.1) (hchar : ringChar F = 2)
    (B : LinearMap.BilinForm F y.1) (hsym : ∀ a b, B a b = B b a)
    (hP : ∀ a, ∀ ha : a ∈ P.1, B ⟨a, hPy ha⟩ ⟨a, hPy ha⟩ = 0)
    (hQ : ∀ a, ∀ ha : a ∈ Q.1, B ⟨a, hQy ha⟩ ⟨a, hQy ha⟩ = 0) : B.IsAlt := by
  intro v
  exact LS5_ringChar F P Q hPQ hPy hQy hchar B hsym hP hQ v
theorem LS6_alternating_of_two_centers {x y z C D : Lines F}
    (hcomp : IsCompl y.1 z.1) (T : y.1 →ₗ[F] z.1) (hT : Function.Injective T)
    (hgraph : x.1 = LinearMap.range (y.1.subtype + z.1.subtype.comp T))
    (B : LinearMap.BilinForm F y.1) (hrep : ∀ a b, B a b = omega F a (T b))
    (hsym : ∀ a b, B a b = B b a) (hchar : ringChar F = 2)
    (hC : C ∈ LineTriadCenters F x y z) (hD : D ∈ LineTriadCenters F x y z)
    (hCD : C ≠ D) : B.IsAlt := by
  obtain ⟨a, b, ha, hb, hrootA, hrootB, hlines⟩ :=
    LS4_distinct_centers_have_distinct_roots F hcomp T hT hgraph hC hD hCD
  let P : Points F := ⟨Submodule.span F {(a : V F)}, finrank_span_singleton (by simpa using ha)⟩
  let Q : Points F := ⟨Submodule.span F {(b : V F)}, finrank_span_singleton (by simpa using hb)⟩
  have hPQ : P ≠ Q := by
    intro h
    apply hlines
    simpa [P, Q] using congrArg Subtype.val h
  have hPy : P.1 ≤ y.1 := (Submodule.span_singleton_le_iff_mem _ _).mpr a.property
  have hQy : Q.1 ≤ y.1 := (Submodule.span_singleton_le_iff_mem _ _).mpr b.property
  have hP : ∀ v, ∀ hv : v ∈ P.1, B ⟨v, hPy hv⟩ ⟨v, hPy hv⟩ = 0 := by
    intro v hv
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hv
    have hval : (⟨v, hPy hv⟩ : y.1) = r • a := by
      apply Subtype.ext
      exact hr.symm
    rw [hval]
    simp [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hrep, hrootA]
  have hQ : ∀ v, ∀ hv : v ∈ Q.1, B ⟨v, hQy hv⟩ ⟨v, hQy hv⟩ = 0 := by
    intro v hv
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hv
    have hval : (⟨v, hQy hv⟩ : y.1) = r • b := by
      apply Subtype.ext
      exact hr.symm
    rw [hval]
    simp [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hrep, hrootB]
  exact LS6_alternating_of_two_roots F P Q hPQ hPy hQy hchar B hsym hP hQ
theorem LS6_graph_intersection {x x' y z : Lines F} (hcomp : IsCompl y.1 z.1)
    (T T' : y.1 →ₗ[F] z.1)
    (hgraph : x.1 = LinearMap.range (y.1.subtype + z.1.subtype.comp T))
    (hgraph' : x'.1 = LinearMap.range (y.1.subtype + z.1.subtype.comp T'))
    (hne : x.1 ⊓ x'.1 ≠ ⊥) : ∃ c : y.1, c ≠ 0 ∧ T c = T' c := by
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hwx : w ∈ x.1 := hw.1
  have hwx' : w ∈ x'.1 := hw.2
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp (hgraph ▸ hwx)
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp (hgraph' ▸ hwx')
  have haW : (a : V F) + (T a : V F) = w := by
    simpa [LinearMap.add_apply, LinearMap.comp_apply] using ha
  have hbW : (b : V F) + (T' b : V F) = w := by
    simpa [LinearMap.add_apply, LinearMap.comp_apply] using hb
  have heq : (a : V F) + (T a : V F) = (b : V F) + (T' b : V F) := by
    exact haW.trans hbW.symm
  have hsub : (a : V F) - (b : V F) = (T' b : V F) - (T a : V F) := by
    linear_combination heq
  have hleft : (a : V F) - (b : V F) ∈ y.1 := y.1.sub_mem a.2 b.2
  have hright : (a : V F) - (b : V F) ∈ z.1 := by
    rw [hsub]
    exact z.1.sub_mem (T' b).2 (T a).2
  have hzero : (a : V F) - (b : V F) = 0 := by
    have hm : (a : V F) - (b : V F) ∈ y.1 ⊓ z.1 := ⟨hleft, hright⟩
    have hbot : y.1 ⊓ z.1 = ⊥ := hcomp.disjoint.eq_bot
    rw [hbot] at hm
    simpa using hm
  have hab : a = b := by
    apply Subtype.ext
    exact sub_eq_zero.mp hzero
  have hT : T a = T' b := by
    have hzero' : (T' b : V F) - (T a : V F) = 0 := by rw [← hsub, hzero]
    apply Subtype.ext
    exact (sub_eq_zero.mp hzero').symm
  have ha0 : a ≠ 0 := by
    intro hz
    apply hw0
    calc
      w = (a : V F) + (T a : V F) := haW.symm
      _ = 0 := by simp [hz]
  exact ⟨a, ha0, hT.trans (congrArg T' hab.symm)⟩
theorem LS6_alt_forms_proportional {y : Lines F} (B B' : LinearMap.BilinForm F y.1)
    (hB : B.IsAlt) (hB' : B'.IsAlt) (hBn : B.Nondegenerate) (hB'n : B'.Nondegenerate) :
    ∃ r : F, r ≠ 0 ∧ B' = r • B := by
  classical
  have hdim : Module.finrank F y.1 = 2 := y.2.1
  obtain ⟨u, hu⟩ := (Module.finrank_pos_iff_exists_ne_zero.mp
    (by rw [hdim]; norm_num : 0 < Module.finrank F y.1))
  have hv : ∃ v : y.1, B u v ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hu (hBn.1 u hn)
  obtain ⟨v, huv⟩ := hv
  have hLI : LinearIndependent F ![u, v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht0 : t * B u v = 0 := by
      have hh := congrArg (B u) hst
      simpa [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
        hB.self_eq_zero] using hh
    have ht : t = 0 := (mul_eq_zero.mp ht0).resolve_right huv
    have hs0 : s • u = 0 := by simpa [ht] using hst
    have hs : s = 0 := (smul_eq_zero.mp hs0).resolve_right hu
    exact ⟨hs, ht⟩
  let b : Module.Basis (Fin 2) F y.1 := Module.Basis.mk hLI (by
    have hspan : Module.finrank F (Submodule.span F (Set.range ![u, v])) = 2 := by
      simpa using finrank_span_eq_card hLI
    have hspanTop : Submodule.span F (Set.range ![u, v]) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [hspan, hdim]
    exact hspanTop.ge)
  have huv' : B' u v ≠ 0 := by
    intro hz
    have hrow : ∀ w : y.1, B' u w = 0 := by
      intro w
      rw [← b.sum_repr w, Fin.sum_univ_succ]
      simp [b, hB'.self_eq_zero, hz]
    exact hu (hB'n.1 u hrow)
  let r : F := B' u v / B u v
  have hcross : B' u v = r * B u v := by
    dsimp [r]
    field_simp
  have heq : B' = r • B := by
    apply LinearMap.BilinForm.ext_basis b
    intro i j
    fin_cases i <;> fin_cases j
    · simp [b, hB'.self_eq_zero, hB.self_eq_zero]
    · simpa [b] using hcross
    · have hrev' : B' v u = r * B v u := by
        calc
          B' v u = -B' u v := (hB'.neg_eq u v).symm
          _ = -(r * B u v) := by rw [hcross]
          _ = r * (-B u v) := by ring
          _ = r * B v u := by rw [hB.neg_eq u v]
      simpa [b] using hrev'
    · simp [b, hB'.self_eq_zero, hB.self_eq_zero]
  refine ⟨r, ?_, heq⟩
  intro hr
  apply huv'
  dsimp [r] at hr
  exact (div_eq_zero_iff.mp hr).resolve_right huv
theorem LS6_forms_proportional_of_two_center_pairs {x x' y z C D C' D' : Lines F}
    (hcomp : IsCompl y.1 z.1) (T T' : y.1 →ₗ[F] z.1)
    (hT : Function.Injective T) (hT' : Function.Injective T')
    (hgraph : x.1 = LinearMap.range (y.1.subtype + z.1.subtype.comp T))
    (hgraph' : x'.1 = LinearMap.range (y.1.subtype + z.1.subtype.comp T'))
    (B B' : LinearMap.BilinForm F y.1)
    (hrep : ∀ a b, B a b = omega F a (T b))
    (hrep' : ∀ a b, B' a b = omega F a (T' b))
    (hsym : ∀ a b, B a b = B b a) (hsym' : ∀ a b, B' a b = B' b a)
    (hchar : ringChar F = 2)
    (hC : C ∈ LineTriadCenters F x y z) (hD : D ∈ LineTriadCenters F x y z)
    (hCD : C ≠ D)
    (hC' : C' ∈ LineTriadCenters F x' y z) (hD' : D' ∈ LineTriadCenters F x' y z)
    (hC'D' : C' ≠ D') (hBn : B.Nondegenerate) (hB'n : B'.Nondegenerate) :
    ∃ r : F, r ≠ 0 ∧ B' = r • B := by
  have hAlt := LS6_alternating_of_two_centers F hcomp T hT hgraph B hrep hsym hchar hC hD hCD
  have hAlt' := LS6_alternating_of_two_centers F hcomp T' hT' hgraph' B' hrep' hsym' hchar hC' hD' hC'D'
  exact LS6_alt_forms_proportional F B B' hAlt hAlt' hBn hB'n
theorem LS6_forms_proportional_of_two_roots {y : Lines F}
    (P Q : Points F) (hPQ : P ≠ Q) (hPy : P.1 ≤ y.1) (hQy : Q.1 ≤ y.1)
    (hchar : ringChar F = 2) (B B' : LinearMap.BilinForm F y.1)
    (hsym : ∀ a b, B a b = B b a) (hsym' : ∀ a b, B' a b = B' b a)
    (hP : ∀ a, ∀ ha : a ∈ P.1, B ⟨a, hPy ha⟩ ⟨a, hPy ha⟩ = 0)
    (hQ : ∀ a, ∀ ha : a ∈ Q.1, B ⟨a, hQy ha⟩ ⟨a, hQy ha⟩ = 0)
    (hP' : ∀ a, ∀ ha : a ∈ P.1, B' ⟨a, hPy ha⟩ ⟨a, hPy ha⟩ = 0)
    (hQ' : ∀ a, ∀ ha : a ∈ Q.1, B' ⟨a, hQy ha⟩ ⟨a, hQy ha⟩ = 0)
    (hBn : B.Nondegenerate) (hB'n : B'.Nondegenerate) :
    ∃ r : F, r ≠ 0 ∧ B' = r • B := by
  have hAlt : B.IsAlt := LS6_alternating_of_two_roots F P Q hPQ hPy hQy hchar B hsym hP hQ
  have hAlt' : B'.IsAlt := LS6_alternating_of_two_roots F P Q hPQ hPy hQy hchar B' hsym' hP' hQ'
  exact LS6_alt_forms_proportional F B B' hAlt hAlt' hBn hB'n
theorem LS6_pairing_nonzero {y : Lines F} (B : LinearMap.BilinForm F y.1)
    (hB : B.IsAlt) (hBn : B.Nondegenerate) (c : y.1) (hc : c ≠ 0) :
    ∃ a : y.1, B a c ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply hc
  apply hBn.1 c
  intro a
  have hneg := hB.neg_eq a c
  rw [hn a] at hneg
  simpa using hneg.symm
theorem LS6_common_vector_fixes_scale {y : Lines F}
    (B B' : LinearMap.BilinForm F y.1) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (r : F) (hscale : B' = r • B) (c : y.1) (hc : c ≠ 0)
    (heq : ∀ a : y.1, B a c = B' a c) : r = 1 := by
  have hex := LS6_pairing_nonzero F B hB hBn c hc
  obtain ⟨a, ha⟩ := hex
  have hmul : B a c = r * B a c := by
    calc
      B a c = B' a c := heq a
      _ = (r • B) a c := by rw [hscale]
      _ = r * B a c := by simp [LinearMap.smul_apply, smul_eq_mul]
  have hzero : (r - 1) * B a c = 0 := by
    calc
      (r - 1) * B a c = r * B a c - B a c := by ring
      _ = 0 := by rw [← hmul]; ring
  have hr : r - 1 = 0 := (mul_eq_zero.mp hzero).resolve_right ha
  exact sub_eq_zero.mp hr
theorem LS6_graph_maps_eq_of_pairing_eq {y z : Lines F}
    (hcomp : IsCompl y.1 z.1) (T T' : y.1 →ₗ[F] z.1)
    (heq : ∀ a b : y.1, omega F a (T b) = omega F a (T' b)) : T = T' := by
  have hyorth : orthogonal F y.1 = y.1 := by
    have hle : y.1 ≤ orthogonal F y.1 := by
      intro w hw
      intro v hv
      exact y.2.2 v hv w hw
    have hdim : Module.finrank F (orthogonal F y.1) = 2 := by
      have h := finrank_add_finrank_orthogonal F y.1
      rw [y.2.1] at h
      omega
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [y.2.1]; exact hdim.symm)).symm
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  have hwz : (T b : V F) - (T' b : V F) ∈ z.1 := z.1.sub_mem (T b).property (T' b).property
  have hwy : (T b : V F) - (T' b : V F) ∈ y.1 := by
    have hwo : (T b : V F) - (T' b : V F) ∈ orthogonal F y.1 := by
      change ∀ a ∈ y.1, omega F a ((T b : V F) - (T' b : V F)) = 0
      intro a ha
      have hab := heq ⟨a, ha⟩ b
      change omegaForm F a (T b) = omegaForm F a (T' b) at hab
      change omegaForm F a ((T b : V F) - (T' b : V F)) = 0
      rw [LinearMap.BilinForm.sub_right, hab]
      ring
    simpa only [hyorth] using hwo
  have hzero : (T b : V F) - (T' b : V F) = 0 := by
    have hm : (T b : V F) - (T' b : V F) ∈ y.1 ⊓ z.1 := ⟨hwy, hwz⟩
    rw [hcomp.disjoint.eq_bot] at hm
    simpa using hm
  exact sub_eq_zero.mp hzero
theorem LS6_graph_maps_eq_of_shared_argument {y z : Lines F}
    (hcomp : IsCompl y.1 z.1) (T T' : y.1 →ₗ[F] z.1)
    (B B' : LinearMap.BilinForm F y.1) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (r : F) (hscale : B' = r • B)
    (hrep : ∀ a b : y.1, B a b = omega F a (T b))
    (hrep' : ∀ a b : y.1, B' a b = omega F a (T' b))
    (c : y.1) (hc : c ≠ 0) (hTc : T c = T' c) : T = T' := by
  have heqc : ∀ a : y.1, B a c = B' a c := by
    intro a
    rw [hrep a c, hrep' a c, hTc]
  have hr := LS6_common_vector_fixes_scale F B B' hB hBn r hscale c hc heqc
  have hforms : B' = B := by simpa [hr] using hscale
  apply LS6_graph_maps_eq_of_pairing_eq F hcomp T T'
  intro a b
  rw [← hrep a b, ← hrep' a b, hforms]
theorem LS6_equal_graphs_of_intersection {x x' y z : Lines F}
    (hcomp : IsCompl y.1 z.1) (T T' : y.1 →ₗ[F] z.1)
    (hgraph : x.1 = LinearMap.range (y.1.subtype + z.1.subtype.comp T))
    (hgraph' : x'.1 = LinearMap.range (y.1.subtype + z.1.subtype.comp T'))
    (hne : x.1 ⊓ x'.1 ≠ ⊥)
    (B B' : LinearMap.BilinForm F y.1) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (r : F) (hscale : B' = r • B)
    (hrep : ∀ a b : y.1, B a b = omega F a (T b))
    (hrep' : ∀ a b : y.1, B' a b = omega F a (T' b)) : x.1 = x'.1 := by
  obtain ⟨c, hc, hTc⟩ := LS6_graph_intersection F hcomp T T' hgraph hgraph' hne
  have hTT := LS6_graph_maps_eq_of_shared_argument F hcomp T T' B B' hB hBn r
    hscale hrep hrep' c hc hTc
  rw [← hTT] at hgraph'
  exact hgraph.trans hgraph'.symm
theorem LS6_equal_graphs_of_two_center_pairs {x x' y z C D C' D' : Lines F}
    (hcomp : IsCompl y.1 z.1) (T T' : y.1 →ₗ[F] z.1)
    (hT : Function.Injective T) (hT' : Function.Injective T')
    (hgraph : x.1 = LinearMap.range (y.1.subtype + z.1.subtype.comp T))
    (hgraph' : x'.1 = LinearMap.range (y.1.subtype + z.1.subtype.comp T'))
    (hne : x.1 ⊓ x'.1 ≠ ⊥)
    (B B' : LinearMap.BilinForm F y.1)
    (hrep : ∀ a b, B a b = omega F a (T b))
    (hrep' : ∀ a b, B' a b = omega F a (T' b))
    (hsym : ∀ a b, B a b = B b a) (hsym' : ∀ a b, B' a b = B' b a)
    (hchar : ringChar F = 2)
    (hC : C ∈ LineTriadCenters F x y z) (hD : D ∈ LineTriadCenters F x y z)
    (hCD : C ≠ D)
    (hC' : C' ∈ LineTriadCenters F x' y z) (hD' : D' ∈ LineTriadCenters F x' y z)
    (hC'D' : C' ≠ D') (hBn : B.Nondegenerate) (hB'n : B'.Nondegenerate) : x.1 = x'.1 := by
  obtain ⟨r, hr, hscale⟩ := LS6_forms_proportional_of_two_center_pairs F hcomp T T' hT hT'
    hgraph hgraph' B B' hrep hrep' hsym hsym' hchar hC hD hCD hC' hD' hC'D' hBn hB'n
  have hAlt : B.IsAlt := LS6_alternating_of_two_centers F hcomp T hT hgraph B hrep hsym hchar hC hD hCD
  exact LS6_equal_graphs_of_intersection F hcomp T T' hgraph hgraph' hne B B' hAlt hBn r hscale
    hrep hrep'
theorem noEvenLineJPattern : noEvenLineJPattern_statement F := by
  intro hchar hJ
  rcases hJ with ⟨x, y, z, x', hxy, hxz, hyz, hx'y, hx'z, hxx',
    hxyN, hxzN, hyzN, hx'yN, hx'zN, hcenters, hcenters', hxx'R⟩
  have inf_bot {M N : Lines F} (hMN : M ≠ N) (hMNrel : ¬ LineRelated F M N) :
      M.1 ⊓ N.1 = ⊥ := by
    by_contra h
    exact hMNrel ((lineRelated_iff_inf_ne_bot F hMN).2 h)
  have hxyBot := inf_bot hxy hxyN
  have hxzBot := inf_bot hxz hxzN
  have hyzBot := inf_bot hyz hyzN
  have hx'yBot := inf_bot hx'y hx'yN
  have hx'zBot := inf_bot hx'z hx'zN
  have hcomp := LS1 F hyzBot
  obtain ⟨T, hT, hgraph⟩ := LS2 F hyzBot hxyBot hxzBot
  obtain ⟨T', hT', hgraph'⟩ := LS2 F hyzBot hx'yBot hx'zBot
  let B : LinearMap.BilinForm F y.1 :=
    (omegaForm F).comp y.1.subtype (z.1.subtype.comp T)
  let B' : LinearMap.BilinForm F y.1 :=
    (omegaForm F).comp y.1.subtype (z.1.subtype.comp T')
  have hrep : ∀ a b : y.1, B a b = omega F a (T b) := by intro a b; rfl
  have hrep' : ∀ a b : y.1, B' a b = omega F a (T' b) := by intro a b; rfl
  have hLS3 := LS3 F hcomp T hT hgraph
  have hLS3' := LS3 F hcomp T' hT' hgraph'
  have hsym : ∀ a b : y.1, B a b = B b a := by
    intro a b
    simpa [B, hrep] using hLS3.1 a b
  have hsym' : ∀ a b : y.1, B' a b = B' b a := by
    intro a b
    simpa [B', hrep'] using hLS3'.1 a b
  have hBn : B.Nondegenerate := by
    refine ⟨?_, ?_⟩
    · intro a ha
      apply hLS3.2 a
      intro b
      rw [← hrep a b]
      exact ha b
    · intro a ha
      apply hLS3.2 a
      intro b
      rw [← hrep a b, ← hsym b a]
      exact ha b
  have hB'n : B'.Nondegenerate := by
    refine ⟨?_, ?_⟩
    · intro a ha
      apply hLS3'.2 a
      intro b
      rw [← hrep' a b]
      exact ha b
    · intro a ha
      apply hLS3'.2 a
      intro b
      rw [← hrep' a b, ← hsym' b a]
      exact ha b
  rcases hcenters with ⟨C, D, hCD, hxC, hyC, hzC, hxD, hyD, hzD⟩
  rcases hcenters' with ⟨C', D', hC'D', hx'C, hyC', hzC', hx'D, hyD', hzD'⟩
  have hC : C ∈ LineTriadCenters F x y z := ⟨hxC, hyC, hzC⟩
  have hD : D ∈ LineTriadCenters F x y z := ⟨hxD, hyD, hzD⟩
  have hC' : C' ∈ LineTriadCenters F x' y z := ⟨hx'C, hyC', hzC'⟩
  have hD' : D' ∈ LineTriadCenters F x' y z := ⟨hx'D, hyD', hzD'⟩
  have hplanes := LS6_equal_graphs_of_two_center_pairs F hcomp T T' hT hT' hgraph hgraph'
    (lineRelated_inf_ne_bot F hxx'R) B B' hrep hrep' hsym hsym' hchar
    hC hD hCD hC' hD' hC'D' hBn hB'n
  have hEq : x = x' := Subtype.ext hplanes
  exact hxx' hEq.symm

/-- In odd characteristic, two is nonzero in the field. -/
theorem LS7_two_ne_zero (hchar : ringChar F ≠ 2) : (2 : F) ≠ 0 := by
  intro htwo
  have hchar' : ringChar F = 2 := CharP.ringChar_of_prime_eq_zero Nat.prime_two htwo
  exact hchar hchar'

/-- A nonzero isotropic vector in a nondegenerate symmetric plane has an isotropic partner. -/
theorem LS7_isotropic_partner {y : Lines F} (B : LinearMap.BilinForm F y.1)
    (hsym : ∀ a b, B a b = B b a) (hBn : B.Nondegenerate)
    (hchar : ringChar F ≠ 2) (a : y.1) (ha : a ≠ 0) (haa : B a a = 0) :
    ∃ b : y.1, B a b ≠ 0 ∧ B b b = 0 := by
  have htwo := LS7_two_ne_zero F hchar
  have hnot : ¬ ∀ b : y.1, B a b = 0 := by
    intro hall
    exact ha (hBn.1 a hall)
  push_neg at hnot
  obtain ⟨b, hab⟩ := hnot
  let r : F := -(B b b) / (2 * B a b)
  let c : y.1 := b + r • a
  have hden : 2 * B a b ≠ 0 := mul_ne_zero htwo hab
  have hac : B a c = B a b := by
    simp [c, LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, haa]
  have hcc : B c c = 0 := by
    have hexpand : B c c = B b b + r * B b a + r * B a b + r ^ 2 * B a a := by
      simp only [c, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
        LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
      ring
    rw [hexpand, haa, hsym b a]
    dsimp [r]
    field_simp [hden]
    ring
  exact ⟨c, by rw [hac]; exact hab, hcc⟩

/-- An isotropic vector in a symmetric plane lies on one of two root lines. -/
theorem LS7_root_vector_on_one_of_two_lines {y : Lines F}
    (B : LinearMap.BilinForm F y.1) (hsym : ∀ a b, B a b = B b a)
    (hchar : ringChar F ≠ 2) (a b v : y.1) (ha : a ≠ 0) (hb : b ≠ 0)
    (haa : B a a = 0) (hbb : B b b = 0) (hab : B a b ≠ 0)
    (hv : v ≠ 0) (hvv : B v v = 0) :
    Submodule.span F {(v : V F)} = Submodule.span F {(a : V F)} ∨
      Submodule.span F {(v : V F)} = Submodule.span F {(b : V F)} := by
  have htwo := LS7_two_ne_zero F hchar
  have hLI : LinearIndependent F ![(a : V F), (b : V F)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hst' : s • a + t • b = 0 := by
      apply Subtype.ext
      exact hst
    have hmul : t * B a b = 0 := by
      have hh := congrArg (B a) hst'
      simpa [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, haa] using hh
    have ht : t = 0 := (mul_eq_zero.mp hmul).resolve_right hab
    have hs : s = 0 := by
      have hsa : s • a = 0 := by rw [ht, zero_smul, add_zero] at hst'; simpa using hst'
      exact (smul_eq_zero.mp hsa).resolve_right (by simpa using ha)
    exact ⟨hs, ht⟩
  let u : Fin 2 → V F := ![(a : V F), (b : V F)]
  have hrange : Set.range u = {(a : V F), (b : V F)} := by
    ext w
    simp only [u, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all
    · rintro (h | h)
      · exact ⟨0, by simpa using h.symm⟩
      · exact ⟨1, by simpa using h.symm⟩
  have hspanfin : Module.finrank F (Submodule.span F {(a : V F), (b : V F)}) = 2 := by
    rw [← hrange, finrank_span_eq_card hLI]
    simp
  have hspanle : Submodule.span F {(a : V F), (b : V F)} ≤ y.1 := by
    apply Submodule.span_le.mpr
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw
    · rw [hw]
      exact a.property
    · rw [hw]
      exact b.property
  have hspantop : Submodule.span F {(a : V F), (b : V F)} = y.1 :=
    Submodule.eq_of_le_of_finrank_eq hspanle (by rw [hspanfin, y.2.1])
  have hvspan : (v : V F) ∈ Submodule.span F {(a : V F), (b : V F)} := by
    rw [hspantop]
    exact v.property
  obtain ⟨r, s, hvs⟩ := Submodule.mem_span_pair.mp hvspan
  have hvs' : v = r • a + s • b := by
    apply Subtype.ext
    exact hvs.symm
  have hquad : B (r • a + s • b) (r • a + s • b) = 2 * r * s * B a b := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
    rw [haa, hbb, hsym b a]
    ring
  have hrs : r = 0 ∨ s = 0 := by
    have hprod : r * s * (2 * B a b) = 0 := by
      have h := hquad
      rw [← hvs', hvv] at h
      calc
        r * s * (2 * B a b) = 2 * r * s * B a b := by ring
        _ = 0 := h.symm
    have hcoef : 2 * B a b ≠ 0 := mul_ne_zero htwo hab
    rcases mul_eq_zero.mp hprod with hrs0 | hcoef0
    · rcases mul_eq_zero.mp hrs0 with hr | hs
      · exact Or.inl hr
      · exact Or.inr hs
    · exact False.elim (hcoef hcoef0)
  rcases hrs with hr | hs
  · right
    have hrepr : (v : V F) = s • (b : V F) := by simpa [hr] using congrArg Subtype.val hvs'
    have hsne : s ≠ 0 := by
      intro hs0
      apply hv
      apply Subtype.ext
      simpa [hs0] using hrepr
    have hback : (b : V F) = s⁻¹ • (v : V F) := by rw [hrepr]; simp [smul_smul, hsne]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro w hw
      simp only [Set.mem_singleton_iff] at hw
      rw [hw, hrepr]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · apply Submodule.span_le.mpr
      intro w hw
      simp only [Set.mem_singleton_iff] at hw
      rw [hw, hback]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · left
    have hrepr : (v : V F) = r • (a : V F) := by simpa [hs] using congrArg Subtype.val hvs'
    have hrne : r ≠ 0 := by
      intro hr0
      apply hv
      apply Subtype.ext
      simpa [hr0] using hrepr
    have hback : (a : V F) = r⁻¹ • (v : V F) := by rw [hrepr]; simp [smul_smul, hrne]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro w hw
      simp only [Set.mem_singleton_iff] at hw
      rw [hw, hrepr]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · apply Submodule.span_le.mpr
      intro w hw
      simp only [Set.mem_singleton_iff] at hw
      rw [hw, hback]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- A centre on a graph plane determines its root point on either transverse plane. -/
theorem LS7_same_center_root_lines {y z C : Lines F} (hcomp : IsCompl y.1 z.1)
    (T : y.1 →ₗ[F] z.1) (hT : Function.Injective T) (a b : y.1)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hCa : C.1 = Submodule.span F ({(a : V F), (T a : V F)} : Set (V F)))
    (hCb : C.1 = Submodule.span F ({(b : V F), (T b : V F)} : Set (V F))):
    Submodule.span F {(a : V F)} = Submodule.span F {(b : V F)} := by
  have hbC : (b : V F) ∈ C.1 := by rw [hCb]; exact Submodule.subset_span (by simp)
  rw [hCa] at hbC
  obtain ⟨r, s, hrel⟩ := Submodule.mem_span_pair.mp hbC
  have hrel' : (b : V F) = r • (a : V F) + s • (T a : V F) := hrel.symm
  have hdiff : (b : V F) - r • (a : V F) = s • (T a : V F) := by
    rw [hrel']
    abel
  have hleft : (b : V F) - r • (a : V F) ∈ y.1 := y.1.sub_mem b.property (y.1.smul_mem r a.property)
  have hright : s • (T a : V F) ∈ z.1 := z.1.smul_mem s (T a).property
  have hzero : s • (T a : V F) = 0 := by
    have hm : s • (T a : V F) ∈ y.1 ⊓ z.1 := ⟨hdiff ▸ hleft, hright⟩
    rw [hcomp.disjoint.eq_bot] at hm
    simpa using hm
  have hTa : (T a : V F) ≠ 0 := by
    intro hz
    apply ha
    apply hT
    apply Subtype.ext
    simpa using hz
  have hs : s = 0 := (smul_eq_zero.mp hzero).resolve_right hTa
  have hba : (b : V F) = r • (a : V F) := by simpa [hs] using hrel'
  have hr : r ≠ 0 := by
    intro hr0
    apply hb
    apply Subtype.ext
    simpa [hr0] using hba
  have hrecip : (a : V F) = r⁻¹ • (b : V F) := by
    rw [hba]
    calc
      (a : V F) = (1 : F) • a := by simp
      _ = (r⁻¹ * r) • a := by rw [inv_mul_cancel₀ hr]
      _ = r⁻¹ • (r • a) := by rw [mul_smul]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro w hw
    simp only [Set.mem_singleton_iff] at hw
    rw [hw, hrecip]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro w hw
    simp only [Set.mem_singleton_iff] at hw
    rw [hw, hba]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- Odd-characteristic triples have zero or two common centres. -/
theorem oddLineTriadCenters : oddLineTriadCenters_statement F := by
  classical
  intro hchar x y z hxy hxz hyz hxyN hxzN hyzN
  have inf_bot {M N : Lines F} (hMN : M ≠ N) (hMNrel : ¬ LineRelated F M N) :
      M.1 ⊓ N.1 = ⊥ := by
    by_contra h
    exact hMNrel ((lineRelated_iff_inf_ne_bot F hMN).2 h)
  have hxyBot := inf_bot hxy hxyN
  have hxzBot := inf_bot hxz hxzN
  have hyzBot := inf_bot hyz hyzN
  have hcomp := LS1 F hyzBot
  obtain ⟨T, hT, hgraph⟩ := LS2 F hyzBot hxyBot hxzBot
  let B : LinearMap.BilinForm F y.1 :=
    (omegaForm F).comp y.1.subtype (z.1.subtype.comp T)
  have hrep : ∀ a b : y.1, B a b = omega F a (T b) := by intro a b; rfl
  have hLS3 := LS3 F hcomp T hT hgraph
  have hsym : ∀ a b : y.1, B a b = B b a := by
    intro a b
    simpa [B, hrep] using hLS3.1 a b
  have hBn : B.Nondegenerate := by
    refine ⟨?_, ?_⟩
    · intro a ha
      apply hLS3.2 a
      intro b
      rw [← hrep a b]
      exact ha b
    · intro a ha
      apply hLS3.2 a
      intro b
      rw [← hrep a b, ← hsym b a]
      exact ha b
  let Cen := {C : Lines F // C ∈ LineTriadCenters F x y z}
  by_cases hnonempty : Nonempty Cen
  · obtain ⟨C⟩ := hnonempty
    obtain ⟨a, ha, haa, hCa⟩ := LS4_center_to_root F hcomp T hT hgraph C.property
    have haaB : B a a = 0 := by simpa [hrep] using haa
    obtain ⟨b, hab, hbbB⟩ := LS7_isotropic_partner F B hsym hBn hchar a ha haaB
    have hb : b ≠ 0 := by
      intro hb0
      apply hab
      simp [hb0]
    have hbb : omega F b (T b) = 0 := by simpa [hrep] using hbbB
    obtain ⟨D, hD, hDb⟩ := LS4_root_is_center F hyzBot hxyBot hxzBot T hT hgraph b hb hbb
    have hCD : C ≠ ⟨D, hD⟩ := by
      intro hEq
      have hline := LS7_same_center_root_lines F hcomp T hT a b ha hb hCa (hEq ▸ hDb)
      obtain ⟨u, hu⟩ := Submodule.span_singleton_eq_span_singleton.mp hline
      have hzero : B a b = 0 := by
        have hu' : (u : F) • a = b := by
          apply Subtype.ext
          simpa [Units.smul_def] using hu
        have he := congrArg (B a) hu'
        have he' : (u : F) * B a a = B a b := by
          simpa [LinearMap.BilinForm.smul_right] using he
        rw [haaB] at he'
        simpa using he'.symm
      exact hab hzero
    have hall : ∀ E : Cen, E = C ∨ E = ⟨D, hD⟩ := by
      intro E
      obtain ⟨c, hc, hcc, hEc⟩ := LS4_center_to_root F hcomp T hT hgraph E.property
      have hccB : B c c = 0 := by simpa [hrep] using hcc
      rcases LS7_root_vector_on_one_of_two_lines F B hsym hchar a b c ha hb haaB hbbB hab hc hccB with hline | hline
      · left
        apply Subtype.ext
        exact LS4_same_root_line_centers_equal F T hEc hCa hline
      · right
        apply Subtype.ext
        exact LS4_same_root_line_centers_equal F T hEc hDb hline
    let f : Cen → Fin 2 := fun E => if E = C then 0 else 1
    have hf : Function.Bijective f := by
      constructor
      · intro E E' he
        rcases hall E with hE | hE <;> rcases hall E' with hE' | hE'
        · exact hE.trans hE'.symm
        · have hval : f C = f ⟨D, hD⟩ := by simpa [hE, hE'] using he
          have h0 : f C = 0 := by simp [f]
          have h1 : f ⟨D, hD⟩ = 1 := by simp [f, hCD.symm]
          rw [h0, h1] at hval
          exact (Fin.zero_ne_one hval).elim
        · have hval : f ⟨D, hD⟩ = f C := by simpa [hE, hE'] using he
          have h0 : f C = 0 := by simp [f]
          have h1 : f ⟨D, hD⟩ = 1 := by simp [f, hCD.symm]
          rw [h1, h0] at hval
          exact (Fin.zero_ne_one hval.symm).elim
        · exact hE.trans hE'.symm
      · intro i
        fin_cases i
        · exact ⟨C, by simp [f]⟩
        · exact ⟨⟨D, hD⟩, by simpa [f] using hCD.symm⟩
    have hcard : Fintype.card Cen = 2 := by
      calc
        Fintype.card Cen = Fintype.card (Fin 2) := Fintype.card_congr (Equiv.ofBijective f hf)
        _ = 2 := by simp
    right
    simpa [Cen] using hcard
  · letI : IsEmpty Cen := ⟨fun C => hnonempty ⟨C⟩⟩
    left
    simp [Cen]
end L575G

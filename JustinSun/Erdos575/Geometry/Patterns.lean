import JustinSun.Erdos575.Geometry.Incidence
namespace L575G
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]
/-- Two distinct points are related when they have a common incident line. -/ def PointRelated (P Q : Points F) : Prop :=
  P ≠ Q ∧ ∃ M : Lines F, P.1 ≤ M.1 ∧ Q.1 ≤ M.1
/-- Two distinct lines are related when they have a common incident point. -/ def LineRelated (M N : Lines F) : Prop :=
  M ≠ N ∧ ∃ P : Points F, P.1 ≤ M.1 ∧ P.1 ≤ N.1
/-- The line common-neighbour relation is symmetric. -/ theorem lineRelated_symm {M N : Lines F} (h : LineRelated F M N) :
    LineRelated F N M := by
  rcases h with ⟨hMN, P, hPM, hPN⟩
  exact ⟨Ne.symm hMN, P, hPN, hPM⟩
/-- Related lines have a nonzero intersection. -/ theorem lineRelated_inf_ne_bot {M N : Lines F} (h : LineRelated F M N) :
    M.1 ⊓ N.1 ≠ ⊥ := by
  rcases h.2 with ⟨P, hPM, hPN⟩
  intro hempty
  have hle : P.1 ≤ (⊥ : Submodule F (V F)) := by
    rw [← hempty]
    exact le_inf hPM hPN
  have hdim := Submodule.finrank_mono hle
  rw [P.2] at hdim
  simp at hdim
/-- Distinct lines are related exactly when their intersection is nonzero. -/ theorem lineRelated_iff_inf_ne_bot {M N : Lines F} (hMN : M ≠ N) :
    LineRelated F M N ↔ M.1 ⊓ N.1 ≠ ⊥ := by
  constructor
  · intro h
    exact lineRelated_inf_ne_bot F h
  · intro h
    have hpos : 0 < Module.finrank F (M.1 ⊓ N.1 : Submodule F (V F)) := by
      by_contra hnot
      have hz : Module.finrank F (M.1 ⊓ N.1 : Submodule F (V F)) = 0 := by omega
      have hs : Subsingleton ↥(M.1 ⊓ N.1 : Submodule F (V F)) :=
        Module.finrank_zero_iff.mp hz
      apply h
      ext v
      constructor
      · intro hv
        have he : (⟨v, hv⟩ : ↥(M.1 ⊓ N.1)) = 0 := Subsingleton.elim _ _
        exact congrArg Subtype.val he
      · intro hv
        have : v = 0 := by simpa using hv
        subst v
        exact Submodule.zero_mem _
    obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero).mp hpos
    have hv' : (v : V F) ≠ 0 := by
      intro he
      apply hv
      exact Subtype.ext he
    let P : Points F := ⟨Submodule.span F {(v : V F)}, by
      exact finrank_span_singleton hv'⟩
    have hPM : P.1 ≤ M.1 := by
      exact (Submodule.span_singleton_le_iff_mem _ _).2 v.property.1
    have hPN : P.1 ≤ N.1 := by
      exact (Submodule.span_singleton_le_iff_mem _ _).2 v.property.2
    exact ⟨hMN, P, hPM, hPN⟩
/-- Independent lines span the ambient symplectic space. -/ theorem independent_lines_sup_eq_top {M N : Lines F}
    (hMN : M ≠ N) (h : ¬ LineRelated F M N) : M.1 ⊔ N.1 = ⊤ := by
  have hinf : M.1 ⊓ N.1 = ⊥ := by
    by_contra hn
    have hne : M.1 ⊓ N.1 ≠ ⊥ := hn
    exact h (lineRelated_iff_inf_ne_bot F hMN |>.2 hne)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq M.1 N.1
  rw [M.2.1, N.2.1, hinf, finrank_bot] at hdim
  have hV : Module.finrank F (V F) = 4 := by simp [V]
  have hsup : Module.finrank F (M.1 ⊔ N.1 : Submodule F (V F)) = 4 := by omega
  apply Submodule.eq_top_of_finrank_eq
  rw [hsup]
  exact hV.symm
/-- The underlying subspaces of independent lines form a direct decomposition. -/ theorem independent_lines_isCompl {M N : Lines F}
    (hMN : M ≠ N) (h : ¬ LineRelated F M N) : IsCompl M.1 N.1 := by
  have hi : M.1 ⊓ N.1 = ⊥ := by
    by_contra hn
    exact h ((lineRelated_iff_inf_ne_bot F hMN).2 hn)
  have hs := independent_lines_sup_eq_top F hMN h
  exact ⟨disjoint_iff.mpr hi, codisjoint_iff.mpr hs⟩
/-- The orthogonal complement of the whole space is zero. -/ theorem orthogonal_top_eq_bot :
    orthogonal F (⊤ : Submodule F (V F)) = ⊥ := by
  ext x
  constructor
  · intro hx
    apply (omega_nondegenerate F).1
    intro y
    have hy := hx y (by simp)
    have hAlt := (omega_isAlt F).neg_eq x y
    have hxy : omega F x y = 0 := by
      rw [hy] at hAlt
      exact neg_eq_zero.mp hAlt
    simpa [omegaForm_apply] using hxy
  · intro hx
    have hx0 : x = 0 := by simpa using hx
    subst x
    intro y hy
    simp [omegaForm_apply, omega]
/-- Pairing against the second member of a complementary pair separates vectors in the first. -/ theorem complementary_lines_pairing_separates {M N : Lines F}
    (hMN : M.1 ⊔ N.1 = ⊤) {x : V F} (hxM : x ∈ M.1)
    (hxN : ∀ y ∈ N.1, omega F y x = 0) : x = 0 := by
  have hxM' : ∀ y ∈ M.1, omega F y x = 0 := by
    intro y hy
    exact M.2.2 y hy x hxM
  have hxorth : x ∈ orthogonal F (M.1 ⊔ N.1) := by
    rw [orthogonal_sup]
    exact ⟨hxM', hxN⟩
  have hxorth' : x ∈ orthogonal F (⊤ : Submodule F (V F)) := by
    rwa [hMN] at hxorth
  have hxbot : x ∈ (⊥ : Submodule F (V F)) := by
    rw [← orthogonal_top_eq_bot F]
    exact hxorth'
  simpa using hxbot
/-- Related points are orthogonal in the symplectic form. -/ theorem pointRelated_le_orthogonal {P Q : Points F} (h : PointRelated F P Q) :
    P.1 ≤ orthogonal F Q.1 := by
  rcases h.2 with ⟨M, hPM, hQM⟩
  intro x hx y hy
  change omegaForm F y x = 0
  simpa [omegaForm_apply] using M.2.2 y (hQM hy) x (hPM hx)
/-- The point relation is symmetric. -/ theorem pointRelated_symm {P Q : Points F} (h : PointRelated F P Q) :
    PointRelated F Q P := by
  rcases h with ⟨hPQ, M, hPM, hQM⟩
  exact ⟨Ne.symm hPQ, M, hQM, hPM⟩
/-- Distinct projective points span a two-dimensional subspace. -/ theorem point_sup_finrank_two {P Q : Points F} (hPQ : P ≠ Q) :
    Module.finrank F (P.1 ⊔ Q.1 : Submodule F (V F)) = 2 := by
  have hInfLe : Module.finrank F (P.1 ⊓ Q.1 : Submodule F (V F)) ≤ 1 := by
    have h := Submodule.finrank_mono (inf_le_left : P.1 ⊓ Q.1 ≤ P.1)
    simpa [P.2] using h
  have hInfNe : Module.finrank F (P.1 ⊓ Q.1 : Submodule F (V F)) ≠ 1 := by
    intro hdim
    have hP : P.1 = P.1 ⊓ Q.1 :=
      (Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [P.2, hdim])).symm
    have hle : P.1 ≤ Q.1 := by rw [hP]; exact inf_le_right
    have hPQval : P.1 = Q.1 :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [P.2, Q.2])
    exact hPQ (Subtype.ext hPQval)
  have hInfZero : Module.finrank F (P.1 ⊓ Q.1 : Submodule F (V F)) = 0 := by omega
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq P.1 Q.1
  rw [P.2, Q.2, hInfZero] at hdim
  omega
/-- Three pairwise related points span a totally isotropic subspace. -/ theorem pointTriple_span_isotropic {P Q R : Points F}
    (hPQ : PointRelated F P Q) (hPR : PointRelated F P R)
    (hQR : PointRelated F Q R) :
    ((P.1 ⊔ Q.1) ⊔ R.1 : Submodule F (V F)) ≤
      orthogonal F ((P.1 ⊔ Q.1) ⊔ R.1 : Submodule F (V F)) := by
  have hPP := point_le_orthogonal F P
  have hQQ := point_le_orthogonal F Q
  have hRR := point_le_orthogonal F R
  have hPQ' := pointRelated_le_orthogonal F hPQ
  have hPR' := pointRelated_le_orthogonal F hPR
  have hQR' := pointRelated_le_orthogonal F hQR
  have hQP' : Q.1 ≤ orthogonal F P.1 := by
    rcases hPQ.2 with ⟨M, hPM, hQM⟩
    intro x hx y hy
    change omegaForm F y x = 0
    simpa [omegaForm_apply] using M.2.2 y (hPM hy) x (hQM hx)
  have hRP' : R.1 ≤ orthogonal F P.1 := by
    rcases hPR.2 with ⟨M, hPM, hRM⟩
    intro x hx y hy
    change omegaForm F y x = 0
    simpa [omegaForm_apply] using M.2.2 y (hPM hy) x (hRM hx)
  have hRQ' : R.1 ≤ orthogonal F Q.1 := by
    rcases hQR.2 with ⟨M, hQM, hRM⟩
    intro x hx y hy
    change omegaForm F y x = 0
    simpa [omegaForm_apply] using M.2.2 y (hQM hy) x (hRM hx)
  have hp : P.1 ≤ orthogonal F ((P.1 ⊔ Q.1) ⊔ R.1) := by
    rw [orthogonal_sup, orthogonal_sup]
    exact le_inf (le_inf hPP hPQ') hPR'
  have hq : Q.1 ≤ orthogonal F ((P.1 ⊔ Q.1) ⊔ R.1) := by
    rw [orthogonal_sup, orthogonal_sup]
    exact le_inf (le_inf hQP' hQQ) hQR'
  have hr : R.1 ≤ orthogonal F ((P.1 ⊔ Q.1) ⊔ R.1) := by
    rw [orthogonal_sup, orthogonal_sup]
    exact le_inf (le_inf hRP' hRQ') hRR
  exact sup_le (sup_le hp hq) hr
/-- Three pairwise related points span a subspace of dimension at most two. -/ theorem pointTriple_span_finrank_le_two {P Q R : Points F}
    (hPQ : PointRelated F P Q) (hPR : PointRelated F P R)
    (hQR : PointRelated F Q R) :
    Module.finrank F (((P.1 ⊔ Q.1) ⊔ R.1 : Submodule F (V F))) ≤ 2 :=
  isotropic_subspace_finrank_le_two F _ (pointTriple_span_isotropic F hPQ hPR hQR)
/-- Two distinct points on an isotropic line span that line. -/ theorem point_sup_eq_line {P Q : Points F} (hPQ : P ≠ Q) {M : Lines F}
    (hPM : P.1 ≤ M.1) (hQM : Q.1 ≤ M.1) : P.1 ⊔ Q.1 = M.1 := by
  have hPneq : P.1 ≠ Q.1 := by
    intro h
    exact hPQ (Subtype.ext h)
  have hle : P.1 ⊔ Q.1 ≤ M.1 := sup_le hPM hQM
  have hlow : 1 ≤ Module.finrank F (P.1 ⊔ Q.1 : Submodule F (V F)) := by
    have := Submodule.finrank_mono (le_sup_left : P.1 ≤ P.1 ⊔ Q.1)
    rw [P.2] at this
    exact this
  have hhigh : Module.finrank F (P.1 ⊔ Q.1 : Submodule F (V F)) ≤ 2 := by
    have := Submodule.finrank_mono hle
    rw [M.2.1] at this
    exact this
  have hneone : Module.finrank F (P.1 ⊔ Q.1 : Submodule F (V F)) ≠ 1 := by
    intro hrank
    have hpj : P.1 = P.1 ⊔ Q.1 :=
      Submodule.eq_of_le_of_finrank_eq le_sup_left (by rw [P.2, hrank])
    have hqj : Q.1 = P.1 ⊔ Q.1 :=
      Submodule.eq_of_le_of_finrank_eq le_sup_right (by rw [Q.2, hrank])
    exact hPneq (hpj.trans hqj.symm)
  have hdim : Module.finrank F (P.1 ⊔ Q.1 : Submodule F (V F)) = 2 := by omega
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hdim, M.2.1])
/-- A line meeting two independent lines is spanned by its two intersection points. -/ theorem common_center_span_endpoints {Y Z C : Lines F}
    (hYZ : Y ≠ Z) (hYZind : ¬ LineRelated F Y Z)
    (hYC : LineRelated F Y C) (hZC : LineRelated F Z C) :
    ∃ P Q : Points F, P.1 ≤ Y.1 ∧ P.1 ≤ C.1 ∧ Q.1 ≤ Z.1 ∧ Q.1 ≤ C.1 ∧
      P ≠ Q ∧ P.1 ⊔ Q.1 = C.1 := by
  rcases hYC.2 with ⟨P, hPY, hPC⟩
  rcases hZC.2 with ⟨Q, hQZ, hQC⟩
  have hPQ : P ≠ Q := by
    intro h
    apply hYZind
    exact ⟨hYZ, P, hPY, by simpa [h] using hQZ⟩
  have hspan : P.1 ⊔ Q.1 = C.1 := point_sup_eq_line F hPQ hPC hQC
  exact ⟨P, Q, hPY, hPC, hQZ, hQC, hPQ, hspan⟩

/-- The endpoint points of a common centre are orthogonal. -/ theorem common_center_endpoints_orthogonal {Y Z C : Lines F}
    (hYZ : Y ≠ Z) (hind : ¬ LineRelated F Y Z)
    (hYC : LineRelated F Y C) (hZC : LineRelated F Z C) :
    ∃ P Q : Points F, P.1 ≤ Y.1 ∧ P.1 ≤ C.1 ∧ Q.1 ≤ Z.1 ∧ Q.1 ≤ C.1 ∧
      P ≠ Q ∧ P.1 ⊔ Q.1 = C.1 ∧ ∀ u ∈ P.1, ∀ v ∈ Q.1, omega F u v = 0 := by
  obtain ⟨P, Q, hPY, hPC, hQZ, hQC, hPQ, hspan⟩ :=
    common_center_span_endpoints F hYZ hind hYC hZC
  refine ⟨P, Q, hPY, hPC, hQZ, hQC, hPQ, hspan, ?_⟩
  intro u hu v hv
  exact C.2.2 u (hPC hu) v (hQC hv)
/-- Two points have at least two distinct common centres in the point relation. -/ def PointPairHasTwoCenters (P Q : Points F) : Prop :=
  ∃ C D : Points F, C ≠ D ∧ PointRelated F P C ∧ PointRelated F Q C ∧
    PointRelated F P D ∧ PointRelated F Q D
/-- Two lines have at least two distinct common centres in the line relation. -/ def LinePairHasTwoCenters (M N : Lines F) : Prop :=
  ∃ C D : Lines F, C ≠ D ∧ LineRelated F M C ∧ LineRelated F N C ∧
    LineRelated F M D ∧ LineRelated F N D
/-- A point triple has at least two distinct common centres. -/ def PointTripleHasTwoCenters (P Q R : Points F) : Prop :=
  ∃ C D : Points F, C ≠ D ∧
    PointRelated F P C ∧ PointRelated F Q C ∧ PointRelated F R C ∧
    PointRelated F P D ∧ PointRelated F Q D ∧ PointRelated F R D
/-- A line triple has at least two distinct common centres. -/ def LineTripleHasTwoCenters (M N O : Lines F) : Prop :=
  ∃ C D : Lines F, C ≠ D ∧
    LineRelated F M C ∧ LineRelated F N C ∧ LineRelated F O C ∧
    LineRelated F M D ∧ LineRelated F N D ∧ LineRelated F O D
/-- A point-side J pattern, with the two independent triples sharing two bases. -/ def PointJPattern : Prop :=
  ∃ x y z x' : Points F,
    x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x' ≠ y ∧ x' ≠ z ∧ x' ≠ x ∧
    ¬ PointRelated F x y ∧ ¬ PointRelated F x z ∧ ¬ PointRelated F y z ∧
    ¬ PointRelated F x' y ∧ ¬ PointRelated F x' z ∧
    PointTripleHasTwoCenters F x y z ∧ PointTripleHasTwoCenters F x' y z ∧
    PointRelated F x x'
/-- A line-side J pattern, with the two independent triples sharing two bases. -/ def LineJPattern : Prop :=
  ∃ x y z x' : Lines F,
    x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x' ≠ y ∧ x' ≠ z ∧ x' ≠ x ∧
    ¬ LineRelated F x y ∧ ¬ LineRelated F x z ∧ ¬ LineRelated F y z ∧
    ¬ LineRelated F x' y ∧ ¬ LineRelated F x' z ∧
    LineTripleHasTwoCenters F x y z ∧ LineTripleHasTwoCenters F x' y z ∧
    LineRelated F x x'
/-- A line-side S₃ pattern is an independent line triple with three common centres. -/ def LineS3Pattern : Prop :=
  ∃ x y z : Lines F,
    x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    ¬ LineRelated F x y ∧ ¬ LineRelated F x z ∧ ¬ LineRelated F y z ∧
    ∃ C D E : Lines F, C ≠ D ∧ C ≠ E ∧ D ≠ E ∧
      LineRelated F x C ∧ LineRelated F y C ∧ LineRelated F z C ∧
      LineRelated F x D ∧ LineRelated F y D ∧ LineRelated F z D ∧
      LineRelated F x E ∧ LineRelated F y E ∧ LineRelated F z E
/-- The set of common line-side centres of a triple of lines. -/ def LineTriadCenters (x y z : Lines F) : Set (Lines F) :=
  { C | LineRelated F x C ∧ LineRelated F y C ∧ LineRelated F z C }
/-- The diagonal quadratic form associated with a symmetric two-dimensional matrix. -/ def diagonalQuadratic (a c : F) (u : Fin 2 → F) : F := a * (u 0) ^ 2 + c * (u 1) ^ 2
/-- The quadratic form associated with a symmetric two-by-two matrix. -/ def symmetricQuadratic (a b c : F) (u : Fin 2 → F) : F :=
  a * (u 0) ^ 2 + 2 * b * u 0 * u 1 + c * (u 1) ^ 2
/-- The determinant of a symmetric two-by-two matrix. -/ def symmetricDet (a b c : F) : F := a * c - b ^ 2
/-- The matrix with zero diagonal and off-diagonal entry `b`. -/ def offDiagonalMap (b : F) (u : Fin 2 → F) : Fin 2 → F := ![b * u 1, b * u 0]
/-- A nonzero off-diagonal matrix acts injectively. -/ theorem offDiagonalMap_injective {b : F} (hb : b ≠ 0) :
    Function.Injective (offDiagonalMap F b) := by
  intro u v huv
  have h0 := congrFun huv 0
  have h1 := congrFun huv 1
  simp [offDiagonalMap] at h0 h1
  have hv1 : u 1 = v 1 := h0.resolve_right hb
  have hv0 : u 0 = v 0 := h1.resolve_right hb
  funext i
  fin_cases i <;> assumption
/-- Two off-diagonal maps with a common nonzero kernel vector are equal. -/ theorem offDiagonalMap_eq_of_common_kernel {b b' : F} {u : Fin 2 → F}
    (hu : u ≠ 0) (heq : offDiagonalMap F b u = offDiagonalMap F b' u) : b = b' := by
  by_contra hbb
  have hdiff : b - b' ≠ 0 := sub_ne_zero.mpr hbb
  have h0 : b * u 1 = b' * u 1 := by simpa [offDiagonalMap] using congrFun heq 0
  have h1 : b * u 0 = b' * u 0 := by simpa [offDiagonalMap] using congrFun heq 1
  have hdu1 : (b - b') * u 1 = 0 := by
    calc
      (b - b') * u 1 = b * u 1 - b' * u 1 := by ring
      _ = 0 := by rw [h0]; ring
  have hdu0 : (b - b') * u 0 = 0 := by
    calc
      (b - b') * u 0 = b * u 0 - b' * u 0 := by ring
      _ = 0 := by rw [h1]; ring
  have heq0 : offDiagonalMap F (b - b') u = offDiagonalMap F (b - b') 0 := by
    funext i
    fin_cases i <;> simp [offDiagonalMap, hdu0, hdu1]
  exact hu ((offDiagonalMap_injective F hdiff) heq0)
/-- In characteristic two, the symmetric mixed terms cancel. -/ theorem charTwo_symmetricQuadratic_eq_diagonal (a b c : F) (htwo : (2 : F) = 0)
    (u : Fin 2 → F) :
    symmetricQuadratic F a b c u = diagonalQuadratic F a c u := by
  simp [symmetricQuadratic, diagonalQuadratic, htwo]
/-- In characteristic two, two independent zeros force a diagonal quadratic form to vanish. -/ theorem charTwo_diagonalQuadratic_eq_zero (a c : F) (htwo : (2 : F) = 0)
    (u v : Fin 2 → F) (hLI : LinearIndependent F ![u, v])
    (hu : diagonalQuadratic F a c u = 0) (hv : diagonalQuadratic F a c v = 0) :
    a = 0 ∧ c = 0 := by
  let b : Fin 2 → (Fin 2 → F) := ![u, v]
  have hspanRank : Module.finrank F (Submodule.span F (Set.range b)) = 2 := by
    rw [finrank_span_eq_card hLI]
    simp [b]
  have hspanTop : Submodule.span F (Set.range b) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hspanRank]
    simp [finrank_top]
  have hrange : Set.range b = {u, v} := by
    ext w
    simp [b]
    tauto
  have hall : ∀ w : Fin 2 → F, diagonalQuadratic F a c w = 0 := by
    intro w
    have hw : w ∈ Submodule.span F {u, v} := by
      rw [← hrange, hspanTop]
      exact Submodule.mem_top
    obtain ⟨r, s, hws⟩ := Submodule.mem_span_pair.mp hw
    have hid : diagonalQuadratic F a c (r • u + s • v) =
        r ^ 2 * diagonalQuadratic F a c u + s ^ 2 * diagonalQuadratic F a c v +
          (2 : F) * r * s * (a * u 0 * v 0 + c * u 1 * v 1) := by
      simp [diagonalQuadratic, Pi.smul_apply, Pi.add_apply]
      ring
    rw [← hws, hid, hu, hv, htwo]
    ring
  have ha := hall ![1, 0]
  have hc := hall ![0, 1]
  constructor
  · simpa [diagonalQuadratic] using ha
  · simpa [diagonalQuadratic] using hc
/-- With zero diagonal, a nonsingular symmetric matrix has nonzero off-diagonal entry. -/ theorem symmetricDet_zeroDiag_ne_zero (b : F) (hdet : symmetricDet F 0 b 0 ≠ 0) : b ≠ 0 := by
  intro hb
  apply hdet
  simp [symmetricDet, hb]
/-- Frozen point-side conclusion for blueprint item 23. -/ def noPointJPattern_statement : Prop := ¬ PointJPattern F
/-- Frozen even-characteristic line-side conclusion for blueprint item 24. -/ def noEvenLineJPattern_statement : Prop :=
  ringChar F = 2 → ¬ LineJPattern F
/-- Frozen odd-characteristic common-centre count for blueprint item 25. -/ def oddLineTriadCenters_statement : Prop := by
  classical
  exact ringChar F ≠ 2 →
    ∀ x y z : Lines F,
      x ≠ y → x ≠ z → y ≠ z →
      ¬ LineRelated F x y → ¬ LineRelated F x z → ¬ LineRelated F y z →
      (Fintype.card { C : Lines F // C ∈ LineTriadCenters F x y z } = 0 ∨
        Fintype.card { C : Lines F // C ∈ LineTriadCenters F x y z } = 2)
/-- The point-side incidence geometry has no J pattern. -/ theorem noPointJPattern : noPointJPattern_statement F := by
  classical
  intro hJ
  rcases hJ with ⟨x, y, z, x', hxy, hxz, hyz, hx'y, hx'z, hxx',
    hxyN, hxzN, hyzN, hx'yN, hx'zN, hcenters, hcenters', hxx'R⟩
  rcases hcenters with ⟨C, D, hCD, hxC, hyC, hzC, hxD, hyD, hzD⟩
  rcases hcenters' with ⟨C', D', hC'D', hx'C', hyC', hzC', hx'D', hyD', hzD'⟩
  let U : Submodule F (V F) := y.1 ⊔ z.1
  have hUdim : Module.finrank F U = 2 := by
    exact point_sup_finrank_two F hyz
  have hCU : C.1 ≤ orthogonal F U := by
    change C.1 ≤ orthogonal F (y.1 ⊔ z.1)
    rw [orthogonal_sup]
    exact le_inf
      (pointRelated_le_orthogonal F (pointRelated_symm F hyC))
      (pointRelated_le_orthogonal F (pointRelated_symm F hzC))
  have hDU : D.1 ≤ orthogonal F U := by
    change D.1 ≤ orthogonal F (y.1 ⊔ z.1)
    rw [orthogonal_sup]
    exact le_inf
      (pointRelated_le_orthogonal F (pointRelated_symm F hyD))
      (pointRelated_le_orthogonal F (pointRelated_symm F hzD))
  have hCDspan : C.1 ⊔ D.1 ≤ orthogonal F U := sup_le hCU hDU
  have hCDdim : Module.finrank F (C.1 ⊔ D.1 : Submodule F (V F)) = 2 :=
    point_sup_finrank_two F hCD
  have hUorth : Module.finrank F (orthogonal F U) = 2 := by
    have h := finrank_add_finrank_orthogonal F U
    rw [hUdim] at h
    omega
  have hCDeq : C.1 ⊔ D.1 = orthogonal F U :=
    Submodule.eq_of_le_of_finrank_eq hCDspan (by rw [hCDdim, hUorth])
  have hxU : x.1 ≤ U := by
    have hxCD : x.1 ≤ orthogonal F (C.1 ⊔ D.1) := by
      rw [orthogonal_sup]
      exact le_inf (pointRelated_le_orthogonal F hxC) (pointRelated_le_orthogonal F hxD)
    rw [hCDeq, orthogonal_orthogonal] at hxCD
    exact hxCD
  have hx'U : x'.1 ≤ U := by
    have hx'CD : x'.1 ≤ orthogonal F (C'.1 ⊔ D'.1) := by
      rw [orthogonal_sup]
      exact le_inf (pointRelated_le_orthogonal F hx'C') (pointRelated_le_orthogonal F hx'D')
    have hC'DU : C'.1 ⊔ D'.1 = orthogonal F U := by
      have hC'U : C'.1 ≤ orthogonal F U := by
        change C'.1 ≤ orthogonal F (y.1 ⊔ z.1)
        rw [orthogonal_sup]
        exact le_inf
          (pointRelated_le_orthogonal F (pointRelated_symm F hyC'))
          (pointRelated_le_orthogonal F (pointRelated_symm F hzC'))
      have hD'U : D'.1 ≤ orthogonal F U := by
        change D'.1 ≤ orthogonal F (y.1 ⊔ z.1)
        rw [orthogonal_sup]
        exact le_inf
          (pointRelated_le_orthogonal F (pointRelated_symm F hyD'))
          (pointRelated_le_orthogonal F (pointRelated_symm F hzD'))
      have hle := sup_le hC'U hD'U
      have hdim := point_sup_finrank_two F hC'D'
      exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hdim, hUorth])
    rw [hC'DU, orthogonal_orthogonal] at hx'CD
    exact hx'CD
  rcases hxx'R with ⟨hxx'ne, L, hxL, hx'L⟩
  have hjoin : x.1 ⊔ x'.1 = L.1 := point_sup_eq_line F hxx'ne hxL hx'L
  have hLUle : L.1 ≤ U := by rw [← hjoin]; exact sup_le hxU hx'U
  have hLdim : Module.finrank F L.1 = 2 := L.2.1
  have hLU : L.1 = U := Submodule.eq_of_le_of_finrank_eq hLUle (by rw [hLdim, hUdim])
  have hyL : y.1 ≤ L.1 := by rw [hLU]; exact le_sup_left
  have hzL : z.1 ≤ L.1 := by rw [hLU]; exact le_sup_right
  exact hyzN ⟨hyz, L, hyL, hzL⟩
/-- The incidence graph has no cycle of length six. -/ theorem Iq_cycle6_free : (SimpleGraph.cycleGraph 6).Free (Iq F) := by
  intro hcopy
  rcases hcopy with ⟨c⟩
  have h01 := c.toHom.map_adj (show (SimpleGraph.cycleGraph 6).Adj (0 : Fin 6) 1 by decide)
  have h12 := c.toHom.map_adj (show (SimpleGraph.cycleGraph 6).Adj (1 : Fin 6) 2 by decide)
  have h23 := c.toHom.map_adj (show (SimpleGraph.cycleGraph 6).Adj (2 : Fin 6) 3 by decide)
  have h34 := c.toHom.map_adj (show (SimpleGraph.cycleGraph 6).Adj (3 : Fin 6) 4 by decide)
  have h45 := c.toHom.map_adj (show (SimpleGraph.cycleGraph 6).Adj (4 : Fin 6) 5 by decide)
  have h50 := c.toHom.map_adj (show (SimpleGraph.cycleGraph 6).Adj (5 : Fin 6) 0 by decide)
  change (Iq F).Adj (c 0) (c 1) at h01
  change (Iq F).Adj (c 1) (c 2) at h12
  change (Iq F).Adj (c 2) (c 3) at h23
  change (Iq F).Adj (c 3) (c 4) at h34
  change (Iq F).Adj (c 4) (c 5) at h45
  change (Iq F).Adj (c 5) (c 0) at h50
  cases h0 : c 0 with
  | inl P =>
    cases h1 : c 1 with
    | inl X => rw [h0, h1] at h01; simp [Iq] at h01
    | inr M =>
      cases h2 : c 2 with
      | inl Q =>
        cases h3 : c 3 with
        | inl X => rw [h2, h3] at h23; simp [Iq] at h23
        | inr N =>
          cases h4 : c 4 with
          | inl R =>
            cases h5 : c 5 with
            | inl X => rw [h4, h5] at h45; simp [Iq] at h45
            | inr O =>
              rw [h0, h1] at h01
              rw [h1, h2] at h12
              rw [h2, h3] at h23
              rw [h3, h4] at h34
              rw [h4, h5] at h45
              rw [h5, h0] at h50
              change P.1 ≤ M.1 at h01
              change Q.1 ≤ M.1 at h12
              change Q.1 ≤ N.1 at h23
              change R.1 ≤ N.1 at h34
              change R.1 ≤ O.1 at h45
              change P.1 ≤ O.1 at h50
              have hPQ : P ≠ Q := by
                intro h
                have he : c (0 : Fin 6) = c 2 := by rw [h0, h2, h]
                exact absurd (c.injective he) (by decide)
              have hPR : P ≠ R := by
                intro h
                have he : c (0 : Fin 6) = c 4 := by rw [h0, h4, h]
                exact absurd (c.injective he) (by decide)
              have hQR : Q ≠ R := by
                intro h
                have he : c (2 : Fin 6) = c 4 := by rw [h2, h4, h]
                exact absurd (c.injective he) (by decide)
              let hpq : PointRelated F P Q := ⟨hPQ, ⟨M, h01, h12⟩⟩
              let hpr : PointRelated F P R := ⟨hPR, ⟨O, h50, h45⟩⟩
              let hqr : PointRelated F Q R := ⟨hQR, ⟨N, h23, h34⟩⟩
              have hspan := pointTriple_span_finrank_le_two F hpq hpr hqr
              have hjoinPQ : P.1 ⊔ Q.1 = M.1 := point_sup_eq_line F hPQ h01 h12
              have hjoinQR : Q.1 ⊔ R.1 = N.1 := point_sup_eq_line F hQR h23 h34
              have hPQr : Module.finrank F (P.1 ⊔ Q.1 : Submodule F (V F)) = 2 := by rw [hjoinPQ, M.2.1]
              have hQRr : Module.finrank F (Q.1 ⊔ R.1 : Submodule F (V F)) = 2 := by rw [hjoinQR, N.2.1]
              have hlePQ : P.1 ⊔ Q.1 ≤ (P.1 ⊔ Q.1) ⊔ R.1 := le_sup_left
              have hspan2 : Module.finrank F (((P.1 ⊔ Q.1) ⊔ R.1 : Submodule F (V F))) = 2 := by
                have hlo := Submodule.finrank_mono hlePQ
                omega
              have hleQR : Q.1 ⊔ R.1 ≤ (P.1 ⊔ Q.1) ⊔ R.1 :=
                sup_le (le_trans le_sup_right le_sup_left) le_sup_right
              have hQRspan : Q.1 ⊔ R.1 = (P.1 ⊔ Q.1) ⊔ R.1 :=
                Submodule.eq_of_le_of_finrank_eq hleQR (by rw [hQRr, hspan2])
              have hPQN : P.1 ≤ N.1 := by
                rw [← hjoinQR, hQRspan]
                exact le_trans le_sup_left le_sup_left
              have hMNval : M.1 = N.1 := line_unique_through_points F hPQ h01 h12 hPQN h23
              have hMN : M = N := Subtype.ext hMNval
              have he : c (1 : Fin 6) = c 3 := by rw [h1, h3, hMN]
              exact absurd (c.injective he) (by decide)
          | inr X => rw [h3, h4] at h34; simp [Iq] at h34
      | inr X => rw [h1, h2] at h12; simp [Iq] at h12
  | inr M =>
    cases h1 : c 1 with
    | inl P =>
      cases h2 : c 2 with
      | inl X => rw [h1, h2] at h12; simp [Iq] at h12
      | inr N =>
        cases h3 : c 3 with
        | inl Q =>
          cases h4 : c 4 with
          | inl X => rw [h3, h4] at h34; simp [Iq] at h34
          | inr O =>
            cases h5 : c 5 with
            | inl R =>
              rw [h0, h1] at h01
              rw [h1, h2] at h12
              rw [h2, h3] at h23
              rw [h3, h4] at h34
              rw [h4, h5] at h45
              rw [h5, h0] at h50
              change P.1 ≤ M.1 at h01
              change P.1 ≤ N.1 at h12
              change Q.1 ≤ N.1 at h23
              change Q.1 ≤ O.1 at h34
              change R.1 ≤ O.1 at h45
              change R.1 ≤ M.1 at h50
              have hPQ : P ≠ Q := by
                intro h
                have he : c (1 : Fin 6) = c 3 := by rw [h1, h3, h]
                exact absurd (c.injective he) (by decide)
              have hPR : P ≠ R := by
                intro h
                have he : c (1 : Fin 6) = c 5 := by rw [h1, h5, h]
                exact absurd (c.injective he) (by decide)
              have hQR : Q ≠ R := by
                intro h
                have he : c (3 : Fin 6) = c 5 := by rw [h3, h5, h]
                exact absurd (c.injective he) (by decide)
              let hpq : PointRelated F P Q := ⟨hPQ, ⟨N, h12, h23⟩⟩
              let hpr : PointRelated F P R := ⟨hPR, ⟨M, h01, h50⟩⟩
              let hqr : PointRelated F Q R := ⟨hQR, ⟨O, h34, h45⟩⟩
              have hspan := pointTriple_span_finrank_le_two F hpq hpr hqr
              have hjoinPQ : P.1 ⊔ Q.1 = N.1 := point_sup_eq_line F hPQ h12 h23
              have hjoinQR : Q.1 ⊔ R.1 = O.1 := point_sup_eq_line F hQR h34 h45
              have hPQr : Module.finrank F (P.1 ⊔ Q.1 : Submodule F (V F)) = 2 := by rw [hjoinPQ, N.2.1]
              have hQRr : Module.finrank F (Q.1 ⊔ R.1 : Submodule F (V F)) = 2 := by rw [hjoinQR, O.2.1]
              have hlePQ : P.1 ⊔ Q.1 ≤ (P.1 ⊔ Q.1) ⊔ R.1 := le_sup_left
              have hspan2 : Module.finrank F (((P.1 ⊔ Q.1) ⊔ R.1 : Submodule F (V F))) = 2 := by
                have hlo := Submodule.finrank_mono hlePQ
                omega
              have hleQR : Q.1 ⊔ R.1 ≤ (P.1 ⊔ Q.1) ⊔ R.1 :=
                sup_le (le_trans le_sup_right le_sup_left) le_sup_right
              have hQRspan : Q.1 ⊔ R.1 = (P.1 ⊔ Q.1) ⊔ R.1 :=
                Submodule.eq_of_le_of_finrank_eq hleQR (by rw [hQRr, hspan2])
              have hPMN : P.1 ≤ O.1 := by
                rw [← hjoinQR, hQRspan]
                exact le_trans le_sup_left le_sup_left
              have hNOval : N.1 = O.1 := line_unique_through_points F hPQ h12 h23 hPMN h34
              have hNO : N = O := Subtype.ext hNOval
              have he : c (2 : Fin 6) = c 4 := by rw [h2, h4, hNO]
              exact absurd (c.injective he) (by decide)
            | inr X => rw [h4, h5] at h45; simp [Iq] at h45
        | inr X => rw [h2, h3] at h23; simp [Iq] at h23
    | inr X => rw [h0, h1] at h01; simp [Iq] at h01
end L575G

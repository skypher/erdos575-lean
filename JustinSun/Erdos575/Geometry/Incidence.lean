import JustinSun.Erdos575.Geometry.Symplectic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Fintype.OfMap
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Projectivization.Collinear
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.Basic
namespace L575G
open scoped LinearAlgebra.Projectivization
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]
attribute [local instance] Classical.propDecidable
/-- Submodules of a finite-dimensional finite carrier form a finite type. -/ noncomputable instance submoduleFintypeOfFinite (W : Type*) [AddCommGroup W]
    [Module F W] [Fintype W] [DecidableEq W] : Fintype (Submodule F W) := by
  classical
  exact Fintype.ofInjective
    (fun S : Submodule F W => fun x => decide (x ∈ S))
    (by
      intro S T h
      apply Submodule.ext
      intro x
      have hx := congrFun h x
      simpa using hx)
/-- Every subspace of the finite coordinate space is drawn from a finite family. -/ noncomputable instance submoduleFintype : Fintype (Submodule F (V F)) := by
  classical
  exact Fintype.ofInjective
    (fun W : Submodule F (V F) => fun v => decide (v ∈ W))
    (by
      intro W W' h
      apply Submodule.ext
      intro v
      have hv := congrFun h v
      simpa using hv)
/-- Projective points in the four-dimensional symplectic space. -/ abbrev Points := {P : Submodule F (V F) // Module.finrank F P = 1}
/-- Two-dimensional totally isotropic subspaces. -/ abbrev Lines := {M : Submodule F (V F) //
  Module.finrank F M = 2 ∧ ∀ u ∈ M, ∀ v ∈ M, omega F u v = 0}
/-- The point carrier is finite because its ambient subspace type is finite. -/ noncomputable instance pointsFintype : Fintype (Points F) := Fintype.ofFinite _
/-- The isotropic line carrier is finite because its ambient subspace type is finite. -/ noncomputable instance linesFintype : Fintype (Lines F) := Fintype.ofFinite _
/-- The field order used in the incidence formulas. -/ def q : ℕ := Fintype.card F
/-- Every point lies on one more line than the field order. -/ noncomputable def PointDegreeClaim : Prop := by
  classical
  exact ∀ P : Points F, Fintype.card {M : Lines F // P.1 ≤ M.1} = q F + 1
/-- The number of projective points in the four-dimensional space. -/ theorem points_card : Fintype.card (Points F) = (q F + 1) * (q F ^ 2 + 1) := by
  have h := Projectivization.card_of_finrank F (V F) (n := 4) (by simp [V])
  have h' : Nat.card (Points F) =
      ∑ i ∈ Finset.range 4, Nat.card F ^ i := by
    rw [← Nat.card_congr (Projectivization.equivSubmodule F (V F))]
    exact h
  have hq : Nat.card F = Fintype.card F := by simp
  rw [hq] at h'
  have hs : (∑ i ∈ Finset.range 4, Fintype.card F ^ i) =
      (Fintype.card F + 1) * (Fintype.card F ^ 2 + 1) := by
    simp [Finset.sum_range_succ]
    ring
  rw [hs] at h'
  simpa [q] using h'
/-- A point is contained in its symplectic orthogonal complement. -/ theorem point_le_orthogonal (P : Points F) : P.1 ≤ orthogonal F P.1 := by
  intro x hx
  change ∀ y ∈ P.1, (omegaForm F) y x = 0
  intro y hy
  rcases (finrank_eq_one_iff'.mp P.property) with ⟨v, hv, hspan⟩
  obtain ⟨a, ha⟩ := hspan ⟨x, hx⟩
  obtain ⟨b, hb⟩ := hspan ⟨y, hy⟩
  have hx' : x = a • v := congrArg Subtype.val ha.symm
  have hy' : y = b • v := congrArg Subtype.val hb.symm
  rw [hx', hy']
  have hvv : (omegaForm F) (v : V F) v = 0 :=
    LinearMap.BilinForm.IsAlt.self_eq_zero (omega_isAlt F) v
  simp [hvv]
/-- The orthogonal complement of a projective point has dimension three. -/ theorem point_orthogonal_finrank (P : Points F) :
    Module.finrank F (orthogonal F P.1) = 3 := by
  have h := finrank_add_finrank_orthogonal F P.1
  rw [P.property] at h
  omega
/-- An isotropic line is contained in its orthogonal complement. -/ theorem line_le_orthogonal (M : Lines F) : M.1 ≤ orthogonal F M.1 := by
  intro x hx y hy
  change omegaForm F y x = 0
  simpa [omegaForm_apply] using M.2.2 y hy x hx
/-- A two-dimensional isotropic subspace equals its orthogonal complement. -/ theorem line_orthogonal_eq (M : Lines F) : orthogonal F M.1 = M.1 := by
  have h := finrank_add_finrank_orthogonal F M.1
  rw [M.2.1] at h
  have ho : Module.finrank F (orthogonal F M.1) = 2 := by omega
  have heq : Module.finrank F M.1 = Module.finrank F (orthogonal F M.1) := by
    rw [M.2.1, ho]
  exact (Submodule.eq_of_le_of_finrank_eq (line_le_orthogonal F M) heq).symm
/-- A totally isotropic subspace of the four-dimensional symplectic space has dimension at most two. -/ theorem isotropic_subspace_finrank_le_two (W : Submodule F (V F))
    (hW : W ≤ orthogonal F W) : Module.finrank F W ≤ 2 := by
  have hdim := finrank_add_finrank_orthogonal F W
  have hmono := Submodule.finrank_mono hW
  omega
/-- A plane through a point inside that point's orthogonal space is isotropic. -/ theorem isotropic_of_point_plane (P : Points F) (M : Submodule F (V F))
    (hPM : P.1 ≤ M) (hMW : M ≤ orthogonal F P.1)
    (hM : Module.finrank F M = 2) :
    ∀ x ∈ M, ∀ y ∈ M, omega F x y = 0 := by
  rcases (finrank_eq_one_iff'.mp P.2) with ⟨p, hp, hspanP⟩
  let pM : ↥M := ⟨p, hPM p.property⟩
  have hpM : pM ≠ 0 := by
    intro h
    apply hp
    apply Subtype.ext
    simpa [pM] using congrArg Subtype.val h
  obtain ⟨yM, hLI⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (by rw [hM]; omega) hpM
  let b : Fin 2 → ↥M := ![pM, yM]
  have hspanRank : Module.finrank F (Submodule.span F (Set.range b)) = 2 := by
    rw [finrank_span_eq_card hLI]
    simp [b]
  have hspanTop : Submodule.span F (Set.range b) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hspanRank]
    simp [finrank_top, hM]
  have hrange : Set.range b = {pM, yM} := by
    ext z
    simp [b]
    tauto
  have hpy : omega F p yM.val = 0 := by
    have hyorth := hMW yM.property
    have this := hyorth p p.property
    change (omegaForm F) p yM.val = 0 at this
    simpa [omegaForm_apply] using this
  have hyp : omega F yM.val p = 0 := by
    have halt := LinearMap.BilinForm.IsAlt.neg_eq (omega_isAlt F) p yM.val
    rw [omegaForm_apply, hpy] at halt
    simpa [omegaForm_apply] using halt.symm
  have hpp : omega F p p = 0 := by
    exact omega_isAlt F p
  have hyy : omega F yM.val yM.val = 0 := by
    exact omega_isAlt F yM.val
  intro x hx y hy
  have hx' : (⟨x, hx⟩ : ↥M) ∈ Submodule.span F {pM, yM} := by
    rw [← hrange]
    rw [hspanTop]
    exact Submodule.mem_top
  have hy' : (⟨y, hy⟩ : ↥M) ∈ Submodule.span F {pM, yM} := by
    rw [← hrange]
    rw [hspanTop]
    exact Submodule.mem_top
  obtain ⟨a, b', hxspan⟩ := (Submodule.mem_span_pair).mp hx'
  obtain ⟨c, d, hyspan⟩ := (Submodule.mem_span_pair).mp hy'
  have hxval : x = a • p + b' • yM.val := congrArg Subtype.val hxspan.symm
  have hyval : y = c • p + d • yM.val := congrArg Subtype.val hyspan.symm
  rw [hxval, hyval]
  change omegaForm F (a • p + b' • yM.val) (c • p + d • yM.val) = 0
  simp [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    omegaForm_apply, hpp, hpy, hyp, hyy]
/-- The point subspace viewed inside its orthogonal complement. -/ def pointInsideOrthogonal (P : Points F) :
    Submodule F (orthogonal F P.1) :=
  Submodule.comap (orthogonal F P.1).subtype P.1
/-- The quotient of a point's orthogonal complement by the point itself has dimension two. -/ theorem pointOrthogonalQuotient_finrank (P : Points F) :
    Module.finrank F (orthogonal F P.1 ⧸ pointInsideOrthogonal F P) = 2 := by
  have hsub : Module.finrank F (pointInsideOrthogonal F P) = 1 := by
    change Module.finrank F ↥(Submodule.comap (orthogonal F P.1).subtype P.1) = 1
    rw [(Submodule.comapSubtypeEquivOfLe (point_le_orthogonal F P)).finrank_eq]
    exact P.property
  have hq := Submodule.finrank_quotient_add_finrank
    (pointInsideOrthogonal F P)
  rw [hsub, point_orthogonal_finrank F P] at hq
  omega
/-- Quotienting a subspace containing the kernel reduces its dimension by that kernel. -/ theorem finrank_map_mkQ_add (W : Type*) [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (N K : Submodule F W) (hNK : N ≤ K) :
    Module.finrank F (K.map N.mkQ) + Module.finrank F N = Module.finrank F K := by
  let f : ↥K →ₗ[F] (W ⧸ N) := N.mkQ.comp K.subtype
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hrange : LinearMap.range f = K.map N.mkQ := by
    ext x
    simp [f, Submodule.mem_map]
  have hker : Module.finrank F (LinearMap.ker f) = Module.finrank F N := by
    have heq : LinearMap.ker f = Submodule.comap K.subtype N := by
      ext x
      simp [f]
    rw [heq]
    rw [(Submodule.comapSubtypeEquivOfLe hNK).finrank_eq]
  rw [hrange, hker] at hrank
  exact hrank
/-- Points contained in a subspace correspond to its one-dimensional subspaces. -/ noncomputable def pointsInsideEquiv (M : Submodule F (V F)) :
    {P : Points F // P.1 ≤ M} ≃
      {S : Submodule F ↥M // Module.finrank F S = 1} where
  toFun P := ⟨Submodule.comap M.subtype P.1.1,
    (Submodule.comapSubtypeEquivOfLe P.2).finrank_eq.trans P.1.2⟩
  invFun S := ⟨⟨Submodule.map M.subtype S.1,
      (Submodule.finrank_map_subtype_eq M S.1).trans S.2⟩,
    Submodule.map_subtype_le M S.1⟩
  left_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    simp [Submodule.map_comap_subtype, P.2]
  right_inv S := by
    apply Subtype.ext
    apply Submodule.ext
    intro x
    simp [Submodule.comap_map_eq_of_injective (show Function.Injective M.subtype from
      Subtype.coe_injective)]
/-- Every two-dimensional subspace contains `q + 1` projective points. -/ theorem pointsOnSubspace_card (M : Submodule F (V F))
    (hM : Module.finrank F M = 2) :
    Fintype.card {P : Points F // P.1 ≤ M} = q F + 1 := by
  classical
  rw [Fintype.card_congr (pointsInsideEquiv F M)]
  have hcard := Projectivization.card_of_finrank F ↥M hM
  have heq := Projectivization.equivSubmodule F ↥M
  have hnat : Fintype.card {S : Submodule F ↥M // Module.finrank F S = 1} =
      Nat.card (Projectivization F ↥M) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr heq.symm
  rw [hnat, hcard]
  have hF : Nat.card F = Fintype.card F := by simp
  rw [hF]
  simp [Finset.sum_range_succ, q]
  omega
/-- Every isotropic line contains exactly `q + 1` projective points. -/ theorem pointsOnLine_card (M : Lines F) :
    Fintype.card {P : Points F // P.1 ≤ M.1} = q F + 1 :=
  pointsOnSubspace_card F M.1 M.2.1
/-- A line through a point determines a projective point of its symplectic quotient. -/ noncomputable def lineToQuotient (P : Points F) :
    {M : Lines F // P.1 ≤ M.1} →
      {S : Submodule F (orthogonal F P.1 ⧸ pointInsideOrthogonal F P) //
        Module.finrank F S = 1} := by
  classical
  intro M
  let W := orthogonal F P.1
  let N := pointInsideOrthogonal F P
  have hMW : M.1 ≤ W := by
    intro x hx
    change ∀ y ∈ P.1, omegaForm F y x = 0
    intro y hy
    exact M.1.2.2 y (M.2 hy) x hx
  let K : Submodule F W := Submodule.comap W.subtype M.1
  have hNK : N ≤ K := by
    intro x hx
    change (x : V F) ∈ M.1.1
    exact M.2 hx
  have hK : Module.finrank F K = 2 := by
    change Module.finrank F ↥(Submodule.comap W.subtype M.1) = 2
    rw [(Submodule.comapSubtypeEquivOfLe hMW).finrank_eq]
    exact M.1.property.1
  have hN : Module.finrank F N = 1 := by
    change Module.finrank F ↥(Submodule.comap W.subtype P.1) = 1
    rw [(Submodule.comapSubtypeEquivOfLe (point_le_orthogonal F P)).finrank_eq]
    exact P.2
  refine ⟨K.map N.mkQ, ?_⟩
  have h := finrank_map_mkQ_add F W N K hNK
  rw [hK, hN] at h
  have h' : Module.finrank F (K.map N.mkQ) + 1 = 1 + 1 := by simpa using h
  exact Nat.add_right_cancel h'
/-- A projective point of the symplectic quotient determines an isotropic line. -/ noncomputable def quotientToLine (P : Points F) :
    {S : Submodule F (orthogonal F P.1 ⧸ pointInsideOrthogonal F P) //
      Module.finrank F S = 1} → {M : Lines F // P.1 ≤ M.1} := by
  classical
  intro S
  let W := orthogonal F P.1
  let N := pointInsideOrthogonal F P
  let K : Submodule F W := Submodule.comap N.mkQ S.1
  have hNK : N ≤ K := Submodule.le_comap_mkQ (p := N) S.1
  have hmap : K.map N.mkQ = S.1 := by
    dsimp [K]
    exact Submodule.map_comap_eq_self (by simp)
  have hN : Module.finrank F N = 1 := by
    change Module.finrank F ↥(Submodule.comap W.subtype P.1) = 1
    rw [(Submodule.comapSubtypeEquivOfLe (point_le_orthogonal F P)).finrank_eq]
    exact P.2
  have hK : Module.finrank F K = 2 := by
    have h := finrank_map_mkQ_add F W N K hNK
    rw [hmap, S.2, hN] at h
    omega
  let L : Submodule F (V F) := K.map W.subtype
  have hL : Module.finrank F L = 2 := by
    change Module.finrank F (K.map W.subtype) = 2
    rw [Submodule.finrank_map_subtype_eq, hK]
  have hPL : P.1 ≤ L := by
    have hNmap : N.map W.subtype = P.1 := by
      change (Submodule.comap W.subtype P.1).map W.subtype = P.1
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.mpr (point_le_orthogonal F P)
    rw [← hNmap]
    exact Submodule.map_mono hNK
  have hLW : L ≤ W := Submodule.map_subtype_le W K
  refine ⟨⟨L, hL, isotropic_of_point_plane F P L hPL hLW hL⟩, hPL⟩
/-- The quotient construction recovers its input projective point. -/ theorem lineTo_quotientTo (P : Points F)
    (S : {S : Submodule F (orthogonal F P.1 ⧸ pointInsideOrthogonal F P) //
      Module.finrank F S = 1}) :
    lineToQuotient F P (quotientToLine F P S) = S := by
  apply Subtype.ext
  dsimp [lineToQuotient, quotientToLine]
  rw [Submodule.comap_map_eq_of_injective
    (show Function.Injective (orthogonal F P.1).subtype from Subtype.coe_injective)]
  exact Submodule.map_comap_eq_self (by simp)
/-- Distinct lines through a point give distinct quotient points. -/ theorem lineToQuotient_injective (P : Points F) :
    Function.Injective (lineToQuotient F P) := by
  classical
  intro M₁ M₂ h
  apply Subtype.ext
  apply Subtype.ext
  let W := orthogonal F P.1
  let N := pointInsideOrthogonal F P
  let K₁ : Submodule F W := Submodule.comap W.subtype M₁.1.1
  let K₂ : Submodule F W := Submodule.comap W.subtype M₂.1.1
  have hMW₁ : M₁.1.1 ≤ W := by
    intro x hx
    change ∀ y ∈ P.1, omegaForm F y x = 0
    intro y hy
    exact M₁.1.2.2 y (M₁.2 hy) x hx
  have hMW₂ : M₂.1.1 ≤ W := by
    intro x hx
    change ∀ y ∈ P.1, omegaForm F y x = 0
    intro y hy
    exact M₂.1.2.2 y (M₂.2 hy) x hx
  have hNK₁ : N ≤ K₁ := by
    intro x hx
    change (x : V F) ∈ M₁.1.1
    exact M₁.2 hx
  have hNK₂ : N ≤ K₂ := by
    intro x hx
    change (x : V F) ∈ M₂.1.1
    exact M₂.2 hx
  have hQ : K₁.map N.mkQ = K₂.map N.mkQ := by
    have hv := congrArg Subtype.val h
    simpa [lineToQuotient, W, N, K₁, K₂] using hv
  have hK : K₁ = K₂ := by
    calc
      K₁ = Submodule.comap N.mkQ (K₁.map N.mkQ) := by
        rw [Submodule.comap_map_mkQ, sup_eq_right.mpr hNK₁]
      _ = Submodule.comap N.mkQ (K₂.map N.mkQ) := by rw [hQ]
      _ = K₂ := by rw [Submodule.comap_map_mkQ, sup_eq_right.mpr hNK₂]
  have hM₁ : K₁.map W.subtype = M₁.1.1 := by
    change (Submodule.comap W.subtype M₁.1.1).map W.subtype = M₁.1.1
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hMW₁]
  have hM₂ : K₂.map W.subtype = M₂.1.1 := by
    change (Submodule.comap W.subtype M₂.1.1).map W.subtype = M₂.1.1
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hMW₂]
  rw [← hM₁, hK, hM₂]
/-- Lines through a point are in bijection with points of the symplectic quotient. -/ noncomputable def pointLineQuotientEquiv (P : Points F) :
    {M : Lines F // P.1 ≤ M.1} ≃
      {S : Submodule F (orthogonal F P.1 ⧸ pointInsideOrthogonal F P) //
        Module.finrank F S = 1} :=
  Equiv.ofBijective (lineToQuotient F P)
    ⟨lineToQuotient_injective F P,
      fun S => ⟨quotientToLine F P S, lineTo_quotientTo F P S⟩⟩
/-- Every point is on exactly `q + 1` isotropic lines. -/ theorem pointDegree (P : Points F) :
    Fintype.card {M : Lines F // P.1 ≤ M.1} = q F + 1 := by
  classical
  let Q := orthogonal F P.1 ⧸ pointInsideOrthogonal F P
  let S : Type _ := {T : Submodule F Q // Module.finrank F T = 1}
  have hbij : Fintype.card {M : Lines F // P.1 ≤ M.1} = Fintype.card S :=
    Fintype.card_congr (pointLineQuotientEquiv F P)
  have hcardQ := Projectivization.card_of_finrank F Q
    (pointOrthogonalQuotient_finrank F P)
  have heq := Projectivization.equivSubmodule F Q
  have hNat : Nat.card S = Nat.card (Projectivization F Q) :=
    Nat.card_congr heq.symm
  have hS : Fintype.card S = q F + 1 := by
    rw [← Nat.card_eq_fintype_card, hNat, hcardQ]
    have hF : Nat.card F = Fintype.card F := by simp
    rw [hF]
    simp [Finset.sum_range_succ, q]
    omega
  exact hbij.trans hS
/-- Counting incident point-line pairs in either order gives equal totals. -/ theorem lines_card_of_pointDegree (hdeg : PointDegreeClaim F) :
    Fintype.card (Lines F) = Fintype.card (Points F) := by
  classical
  let A := Σ P : Points F, {M : Lines F // P.1 ≤ M.1}
  let B := Σ M : Lines F, {P : Points F // P.1 ≤ M.1}
  let e : A ≃ B :=
    { toFun := fun x => ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
      invFun := fun x => ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
      left_inv := by intro x; cases x; rfl
      right_inv := by intro x; cases x; rfl }
  have hcard : Fintype.card A = Fintype.card B := Fintype.card_congr e
  change (∀ P : Points F,
      Fintype.card {M : Lines F // P.1 ≤ M.1} = q F + 1) at hdeg
  have hA : Fintype.card A = Fintype.card (Points F) * (q F + 1) := by
    simp only [A, Fintype.card_sigma]
    calc
      _ = ∑ _P : Points F, (q F + 1) := by
        apply Finset.sum_congr rfl
        intro P hP
        exact hdeg P
      _ = _ := by simp
  have hB : Fintype.card B = Fintype.card (Lines F) * (q F + 1) := by
    simp [B, Fintype.card_sigma, pointsOnLine_card]
  rw [hA, hB] at hcard
  exact Nat.mul_right_cancel (Nat.succ_pos _) hcard.symm
/-- The number of isotropic lines equals the number of projective points. -/ theorem lines_card :
    Fintype.card (Lines F) = (q F + 1) * (q F ^ 2 + 1) := by
  rw [lines_card_of_pointDegree F (fun P => pointDegree F P), points_card]
/-- The projective point corresponding to a one-dimensional subspace. -/ noncomputable def pointProjectivization (P : Points F) : Projectivization F (V F) :=
  Projectivization.mk'' P.1 P.2
@[simp] theorem pointProjectivization_submodule (P : Points F) :
    (pointProjectivization F P).submodule = P.1 := by
  simp [pointProjectivization]
/-- Two distinct projective points determine at most one two-dimensional subspace. -/ theorem line_unique_through_points {P Q : Points F} (hPQ : P ≠ Q)
    {M N : Lines F} (hPM : P.1 ≤ M.1) (hQM : Q.1 ≤ M.1)
    (hPN : P.1 ≤ N.1) (hQN : Q.1 ≤ N.1) : M.1 = N.1 := by
  have hxy : pointProjectivization F P ≠ pointProjectivization F Q := by
    intro h
    apply hPQ
    have hs := congrArg (fun x : Projectivization F (V F) => x.submodule) h
    apply Subtype.ext
    simpa using hs
  have hxM : pointProjectivization F P ∈ Submodule.projectivization M.1 := by
    rw [Submodule.mem_projectivization_iff_submodule_le]
    simpa using hPM
  have hyM : pointProjectivization F Q ∈ Submodule.projectivization M.1 := by
    rw [Submodule.mem_projectivization_iff_submodule_le]
    simpa using hQM
  have hxN : pointProjectivization F P ∈ Submodule.projectivization N.1 := by
    rw [Submodule.mem_projectivization_iff_submodule_le]
    simpa using hPN
  have hyN : pointProjectivization F Q ∈ Submodule.projectivization N.1 := by
    rw [Submodule.mem_projectivization_iff_submodule_le]
    simpa using hQN
  exact Projectivization.line_unique hxy M.1 N.1 M.2.1 N.2.1 hxM hyM hxN hyN
/-- The incidence graph on projective points and isotropic lines. -/ def Iq : SimpleGraph (Points F ⊕ Lines F) where
  Adj x y := match x, y with
    | Sum.inl P, Sum.inr M => P.1 ≤ M.1
    | Sum.inr M, Sum.inl P => P.1 ≤ M.1
    | _, _ => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> simp_all⟩
  loopless := ⟨by
    intro x h
    cases x <;> simp at h⟩
def pointVertices : Set (Points F ⊕ Lines F) := Set.range Sum.inl
def lineVertices : Set (Points F ⊕ Lines F) := Set.range Sum.inr
/-- The two vertex classes give the bipartition of the incidence graph. -/ theorem Iq_bipartiteWith :
    (Iq F).IsBipartiteWith (pointVertices F) (lineVertices F) := by
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro x ⟨P, hP⟩ ⟨M, hM⟩
    cases hP.trans hM.symm
  · intro x y h
    cases x with
    | inl P =>
      cases y with
      | inl Q => simp [Iq] at h
      | inr M => exact Or.inl ⟨⟨P, rfl⟩, ⟨M, rfl⟩⟩
    | inr M =>
      cases y with
      | inl P => exact Or.inr ⟨⟨M, rfl⟩, ⟨P, rfl⟩⟩
      | inr N => simp [Iq] at h
@[simp] theorem adj_point_line (P : Points F) (M : Lines F) :
    (Iq F).Adj (Sum.inl P) (Sum.inr M) ↔ P.1 ≤ M.1 := Iff.rfl
@[simp] theorem adj_line_point (M : Lines F) (P : Points F) :
    (Iq F).Adj (Sum.inr M) (Sum.inl P) ↔ P.1 ≤ M.1 := Iff.rfl
@[simp] theorem not_adj_point_point (P Q : Points F) :
    ¬ (Iq F).Adj (Sum.inl P) (Sum.inl Q) := by simp [Iq]
@[simp] theorem not_adj_line_line (M N : Lines F) :
    ¬ (Iq F).Adj (Sum.inr M) (Sum.inr N) := by simp [Iq]
/-- The incidence graph has no cycle of length four. -/ theorem Iq_cycle4_free : SimpleGraph.Free (SimpleGraph.cycleGraph 4) (Iq F) := by
  intro hcopy
  rcases hcopy with ⟨c⟩
  have h01 := c.toHom.map_adj (show (SimpleGraph.cycleGraph 4).Adj (0 : Fin 4) 1 by decide)
  have h12 := c.toHom.map_adj (show (SimpleGraph.cycleGraph 4).Adj (1 : Fin 4) 2 by decide)
  have h23 := c.toHom.map_adj (show (SimpleGraph.cycleGraph 4).Adj (2 : Fin 4) 3 by decide)
  have h30 := c.toHom.map_adj (show (SimpleGraph.cycleGraph 4).Adj (3 : Fin 4) 0 by decide)
  change (Iq F).Adj (c 0) (c 1) at h01
  change (Iq F).Adj (c 1) (c 2) at h12
  change (Iq F).Adj (c 2) (c 3) at h23
  change (Iq F).Adj (c 3) (c 0) at h30
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
          have hPM : P.1 ≤ M.1 := by rw [h0, h1] at h01; exact h01
          have hQM : Q.1 ≤ M.1 := by rw [h1, h2] at h12; exact h12
          have hQN : Q.1 ≤ N.1 := by rw [h2, h3] at h23; exact h23
          have hPN : P.1 ≤ N.1 := by rw [h3, h0] at h30; exact h30
          have hPQ : P ≠ Q := by
            intro h
            have he : c (0 : Fin 4) = c 2 := by rw [h0, h2, h]
            have := c.injective he
            exact absurd this (by decide)
          have hMNval : M.1 = N.1 := line_unique_through_points F hPQ hPM hQM hPN hQN
          have hMN : M = N := Subtype.ext hMNval
          have he : c (1 : Fin 4) = c 3 := by rw [h1, h3, hMN]
          have := c.injective he
          exact absurd this (by decide)
      | inr X => rw [h1, h2] at h12; simp [Iq] at h12
  | inr M =>
    cases h1 : c 1 with
    | inl P =>
      cases h2 : c 2 with
      | inl X => rw [h1, h2] at h12; simp [Iq] at h12
      | inr N =>
        cases h3 : c 3 with
        | inl Q =>
          have hPM : P.1 ≤ M.1 := by rw [h0, h1] at h01; exact h01
          have hPN : P.1 ≤ N.1 := by rw [h1, h2] at h12; exact h12
          have hQN : Q.1 ≤ N.1 := by rw [h2, h3] at h23; exact h23
          have hQM : Q.1 ≤ M.1 := by rw [h3, h0] at h30; exact h30
          have hPQ : P ≠ Q := by
            intro h
            have he : c (1 : Fin 4) = c 3 := by rw [h1, h3, h]
            have := c.injective he
            exact absurd this (by decide)
          have hMNval : M.1 = N.1 := line_unique_through_points F hPQ hPM hQM hPN hQN
          have hMN : M = N := Subtype.ext hMNval
          have he : c (0 : Fin 4) = c 2 := by rw [h0, h2, hMN]
          have := c.injective he
          exact absurd this (by decide)
        | inr X => rw [h2, h3] at h23; simp [Iq] at h23
    | inr X => rw [h0, h1] at h01; simp [Iq] at h01
/-- Frozen finite-geometry statement for the remaining 6-cycle argument. -/ def Iq_cycle6_free_statement : Prop :=
  SimpleGraph.Free (SimpleGraph.cycleGraph 6) (Iq F)
/-- Neighbors of a point in the incidence graph are its incident lines. -/ noncomputable def pointNeighborEquiv (P : Points F) :
    {x : Points F ⊕ Lines F // x ∈ (Iq F).neighborSet (Sum.inl P)} ≃
      {M : Lines F // P.1 ≤ M.1} where
  toFun x := by
    cases x with
    | mk v hv =>
      change (Iq F).Adj (Sum.inl P) v at hv
      cases v with
      | inl Q => exact False.elim (by simpa [Iq] using hv)
      | inr M => exact ⟨M, by simpa [Iq] using hv⟩
  invFun M := ⟨Sum.inr M.1, by simpa [SimpleGraph.neighborSet, Iq] using M.2⟩
  left_inv x := by
    cases x with
    | mk v hv =>
      cases v with
      | inl Q => simp [Iq] at hv
      | inr M => rfl
  right_inv M := by
    apply Subtype.ext
    rfl
/-- Neighbors of a line in the incidence graph are its contained points. -/ noncomputable def lineNeighborEquiv (M : Lines F) :
    {x : Points F ⊕ Lines F // x ∈ (Iq F).neighborSet (Sum.inr M)} ≃
      {P : Points F // P.1 ≤ M.1} where
  toFun x := by
    cases x with
    | mk v hv =>
      change (Iq F).Adj (Sum.inr M) v at hv
      cases v with
      | inl P => exact ⟨P, by simpa [Iq] using hv⟩
      | inr N => exact False.elim (by simpa [Iq] using hv)
  invFun P := ⟨Sum.inl P.1, by simpa [SimpleGraph.neighborSet, Iq] using P.2⟩
  left_inv x := by
    cases x with
    | mk v hv =>
      cases v with
      | inl P => rfl
      | inr N => simp [Iq] at hv
  right_inv P := by
    apply Subtype.ext
    rfl
/-- Every point vertex has graph degree `q + 1`. -/ theorem degree_point (P : Points F) : (Iq F).degree (Sum.inl P) = q F + 1 := by
  classical
  rw [← (Iq F).card_neighborSet_eq_degree]
  rw [Fintype.card_congr (pointNeighborEquiv F P)]
  exact pointDegree F P
/-- Every line vertex has graph degree `q + 1`. -/ theorem degree_line (M : Lines F) : (Iq F).degree (Sum.inr M) = q F + 1 := by
  classical
  rw [← (Iq F).card_neighborSet_eq_degree]
  rw [Fintype.card_congr (lineNeighborEquiv F M)]
  exact pointsOnLine_card F M
/-- The number of vertices in the incidence graph. -/ noncomputable def n_q : ℕ := Fintype.card (Points F ⊕ Lines F)
/-- The number of edges in the incidence graph. -/ noncomputable def e_q : ℕ := (Iq F).edgeFinset.card
/-- The incidence graph has the claimed number of vertices. -/ theorem n_q_eq : n_q F = 2 * (q F + 1) * (q F ^ 2 + 1) := by
  simp [n_q, Fintype.card_sum, points_card, lines_card]
  ring
/-- The incidence graph has the claimed number of edges. -/ theorem e_q_eq : e_q F = (q F + 1) ^ 2 * (q F ^ 2 + 1) := by
  classical
  have hsum := (Iq F).sum_degrees_eq_twice_card_edges
  have hsum' : Fintype.card (Points F) * (q F + 1) +
      Fintype.card (Lines F) * (q F + 1) = 2 * e_q F := by
    simpa [e_q, Fintype.sum_sum_type, degree_point, degree_line] using hsum
  rw [points_card, lines_card, q] at hsum'
  have hmul : 2 * e_q F =
      2 * ((Fintype.card F + 1) ^ 2 * (Fintype.card F ^ 2 + 1)) := by
    calc
      2 * e_q F =
          (Fintype.card F + 1) * (Fintype.card F ^ 2 + 1) * (Fintype.card F + 1) +
          (Fintype.card F + 1) * (Fintype.card F ^ 2 + 1) * (Fintype.card F + 1) := by
            nlinarith [hsum']
      _ = 2 * ((Fintype.card F + 1) ^ 2 * (Fintype.card F ^ 2 + 1)) := by ring
  exact Nat.mul_left_cancel (by omega) hmul
/-- A numerical lower bound from the exact incidence counts. -/ theorem e_q_density :
    (e_q F : ℝ) ≥ 2 ^ (-(4 : ℝ) / 3) * (n_q F : ℝ) ^ ((4 : ℝ) / 3) := by
  let a : ℝ := (q F : ℝ) + 1
  let b : ℝ := (q F : ℝ) ^ 2 + 1
  have hn : (n_q F : ℝ) = 2 * a * b := by
    rw [n_q_eq]
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_pow]
    dsimp [a, b]
    ring
  have he : (e_q F : ℝ) = a ^ 2 * b := by
    rw [e_q_eq]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
    dsimp [a, b]
    ring
  have hbase : ((e_q F : ℝ) ^ 3) ≥ (n_q F : ℝ) ^ 4 / 16 := by
    rw [he, hn]
    dsimp [a, b]
    have hq : 0 ≤ (q F : ℝ) := Nat.cast_nonneg _
    have hab : 0 ≤ ((q F : ℝ) + 1) ^ 2 - ((q F : ℝ) ^ 2 + 1) := by nlinarith
    have hfac : 0 ≤ ((q F : ℝ) + 1) ^ 4 * ((q F : ℝ) ^ 2 + 1) ^ 3 *
        (((q F : ℝ) + 1) ^ 2 - ((q F : ℝ) ^ 2 + 1)) :=
      mul_nonneg (mul_nonneg (by positivity) (by positivity)) hab
    nlinarith [hfac]
  let c : ℝ := 2 ^ (-(4 : ℝ) / 3) * (n_q F : ℝ) ^ ((4 : ℝ) / 3)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc3 : c ^ 3 = (n_q F : ℝ) ^ 4 / 16 := by
    dsimp [c]
    rw [mul_pow]
    have h2 : ((2 : ℝ) ^ (-(4 : ℝ) / 3)) ^ 3 = 1 / 16 := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(4 : ℝ) / 3)) 3]
      rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
      norm_num
    have hn0 : 0 ≤ (n_q F : ℝ) := Nat.cast_nonneg _
    have hn3 : ((n_q F : ℝ) ^ ((4 : ℝ) / 3)) ^ 3 = (n_q F : ℝ) ^ 4 := by
      rw [← Real.rpow_natCast ((n_q F : ℝ) ^ ((4 : ℝ) / 3)) 3]
      rw [← Real.rpow_mul hn0]
      norm_num
    rw [h2, hn3]
    ring
  have hepos : 0 ≤ (e_q F : ℝ) := by rw [he]; positivity
  have hcpos : 0 < c := by
    have hnpos : 0 < n_q F := by rw [n_q_eq]; positivity
    dsimp [c]
    positivity
  have hlt : ¬ (e_q F : ℝ) < c := by
    intro h
    have hfactor : 0 < (e_q F : ℝ) ^ 2 + (e_q F : ℝ) * c + c ^ 2 := by
      positivity
    have hcube : (e_q F : ℝ) ^ 3 < c ^ 3 := by
      nlinarith [mul_pos (sub_pos.mpr h) hfactor]
    rw [hc3] at hcube
    exact not_lt_of_ge hbase hcube
  exact le_of_not_gt hlt
/-- The smallest field case has fifteen projective points. -/ theorem points_card_ZMod_two : Fintype.card (Points (ZMod 2)) = 15 := by
  norm_num [points_card, q]
/-- The smallest field case has fifteen isotropic lines. -/ theorem lines_card_ZMod_two : Fintype.card (Lines (ZMod 2)) = 15 := by
  norm_num [lines_card, points_card, q]
/-- Every point in the smallest field case lies on three lines. -/ theorem pointDegree_ZMod_two (P : Points (ZMod 2)) :
    Fintype.card {M : Lines (ZMod 2) // P.1 ≤ M.1} = 3 := by
  simpa [q] using pointDegree (ZMod 2) P
end L575G

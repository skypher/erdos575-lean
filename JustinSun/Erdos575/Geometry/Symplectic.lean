import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
namespace L575G
open LinearMap
variable (F : Type*) [Field F]
/-- The four-dimensional vector space used for the symplectic incidence geometry. -/ abbrev V := Fin 4 → F
/-- The alternating form with two standard symplectic coordinate pairs. -/ def omega (x y : V F) : F :=
  x 0 * y 2 - x 2 * y 0 + x 1 * y 3 - x 3 * y 1
/-- The bilinear form associated to `omega`. -/ def omegaForm : LinearMap.BilinForm F (V F) :=
  LinearMap.mk₂ F (omega F)
    (by intro x y z; simp [omega] <;> ring)
    (by intro a x y; simp [omega] <;> ring)
    (by intro x y z; simp [omega] <;> ring)
    (by intro a x y; simp [omega] <;> ring)
@[simp] theorem omegaForm_apply (x y : V F) : omegaForm F x y = omega F x y := rfl
/-- The coordinate form is alternating. -/ theorem omega_isAlt : (omegaForm F).IsAlt := by
  intro x
  simp [omegaForm_apply, omega]
  ring
/-- The coordinate form is nondegenerate. -/ theorem omega_nondegenerate : (omegaForm F).Nondegenerate := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have h0 := hx (fun i => if i = 2 then 1 else 0)
    have h1 := hx (fun i => if i = 3 then 1 else 0)
    have h2 := hx (fun i => if i = 0 then 1 else 0)
    have h3 := hx (fun i => if i = 1 then 1 else 0)
    have e0 : x 0 = 0 := by simpa [omegaForm_apply, omega] using h0
    have e1 : x 1 = 0 := by simpa [omegaForm_apply, omega] using h1
    have e2 : x 2 = 0 := by simpa [omegaForm_apply, omega] using h2
    have e3 : x 3 = 0 := by simpa [omegaForm_apply, omega] using h3
    funext i
    fin_cases i <;> simp [e0, e1, e2, e3]
  · intro y hy
    have h0 := hy (fun i => if i = 2 then 1 else 0)
    have h1 := hy (fun i => if i = 3 then 1 else 0)
    have h2 := hy (fun i => if i = 0 then 1 else 0)
    have h3 := hy (fun i => if i = 1 then 1 else 0)
    have e0 : y 0 = 0 := by simpa [omegaForm_apply, omega] using h0
    have e1 : y 1 = 0 := by simpa [omegaForm_apply, omega] using h1
    have e2 : y 2 = 0 := by simpa [omegaForm_apply, omega] using h2
    have e3 : y 3 = 0 := by simpa [omegaForm_apply, omega] using h3
    funext i
    fin_cases i <;> simp [e0, e1, e2, e3]
/-- The orthogonal complement is the right orthogonal for `omegaForm`. -/ def orthogonal (W : Submodule F (V F)) : Submodule F (V F) :=
  (omegaForm F).orthogonal W
/-- The orthogonal complement of a sum is the intersection of the complements. -/ theorem orthogonal_sup (A B : Submodule F (V F)) :
    orthogonal F (A ⊔ B) = orthogonal F A ⊓ orthogonal F B := by
  ext x
  simp only [orthogonal, LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_inf]
  constructor
  · intro hx
    constructor
    · intro a ha
      exact hx a (Submodule.mem_sup_left ha)
    · intro b hb
      exact hx b (Submodule.mem_sup_right hb)
  · rintro ⟨ha, hb⟩ v hv
    rcases Submodule.mem_sup.mp hv with ⟨a, hA, b, hB, rfl⟩
    simpa [ha a hA, hb b hB] using (add_apply ((omegaForm F) a) ((omegaForm F) b) x)
/-- Orthogonal complements have complementary dimensions. -/ theorem finrank_add_finrank_orthogonal (W : Submodule F (V F)) :
    Module.finrank F W + Module.finrank F (orthogonal F W) = 4 := by
  rw [orthogonal, (omegaForm F).finrank_orthogonal (omega_nondegenerate F) W]
  have hW' : Module.finrank F W ≤ Module.finrank F (⊤ : Submodule F (V F)) :=
    Submodule.finrank_mono (s := W) (t := ⊤) le_top
  have hV : Module.finrank F (V F) = 4 := by simp [V]
  have hW : Module.finrank F W ≤ 4 := by
    simpa [finrank_top, hV] using hW'
  omega
/-- Taking the orthogonal complement twice returns the original subspace. -/ theorem orthogonal_orthogonal (W : Submodule F (V F)) :
    orthogonal F (orthogonal F W) = W := by
  exact (omegaForm F).orthogonal_orthogonal (omega_nondegenerate F)
    (omega_isAlt F).isRefl W
section FiniteFields
variable (j : ℕ) (hj : 1 ≤ j)
/-- The cardinality of the degree-`j` field of characteristic two. -/ theorem galoisField_two_card (hj : 1 ≤ j) : Nat.card (GaloisField 2 j) = 2 ^ j :=
  GaloisField.card 2 j (by omega)
/-- The cardinality of the degree-`j` field of characteristic three. -/ theorem galoisField_three_card (hj : 1 ≤ j) : Nat.card (GaloisField 3 j) = 3 ^ j :=
  GaloisField.card 3 j (by omega)
/-- The degree-`j` Galois field has characteristic two. -/ theorem galoisField_two_char : CharP (GaloisField 2 j) 2 := inferInstance
/-- The degree-`j` Galois field has characteristic three. -/ theorem galoisField_three_char : CharP (GaloisField 3 j) 3 := inferInstance
end FiniteFields
end L575G

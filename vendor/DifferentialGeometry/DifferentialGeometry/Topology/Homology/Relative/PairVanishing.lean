module

public import DifferentialGeometry.Topology.Homology.Naturality
public import DifferentialGeometry.Topology.Morse.Strip.Defs

@[expose] public section

open CategoryTheory Limits
open scoped ContinuousMap

noncomputable section

universe u

namespace DifferentialGeometry.Topology

open SingularPair

def relHomologyVanishes (X : Type u) [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ n, IsZero (relativeHomology integerCoefficients (TopCat.of X) A n)

theorem relHomologyVanishes.congr {X : Type u} [TopologicalSpace X] {B B' A A' : Set X}
    (hB : B = B') (hA : A = A') (h : relHomologyVanishes B (Subtype.val ⁻¹' A)) :
    relHomologyVanishes B' (Subtype.val ⁻¹' A') := by
  subst hB hA
  exact h

def homeomorphPreimageVal {X : Type u} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    (Subtype.val ⁻¹' A : Set B) ≃ₜ A where
  toFun x := ⟨x.1.1, x.2⟩
  invFun y := ⟨⟨y.1, hAB y.2⟩, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem isHomotopyEquivInclusion.relHomologyVanishes {X : Type u} [TopologicalSpace X]
    {A B : Set X} (h : isHomotopyEquivInclusion A B) :
    relHomologyVanishes B (Subtype.val ⁻¹' A) := by
  have hAB : A ⊆ B := h.subset
  obtain ⟨e, he⟩ := h
  let e' : (Subtype.val ⁻¹' A : Set B) ≃ₕ B := (homeomorphPreimageVal hAB).toHomotopyEquiv.trans e
  have hincl : TopCat.ofHom e'.toFun = incl (TopCat.of B) (Subtype.val ⁻¹' A) := by
    ext x
    exact he _
  have hiso : ∀ n, IsIso (inclMap integerCoefficients (TopCat.of B) (Subtype.val ⁻¹' A) n) := fun n => by
    rw [inclMap_eq_singularHomologyMap, ← hincl]
    exact isIso_singularHomologyMap_of_homotopyEquiv integerCoefficients e' n
  have hπ : ∀ n, relπ integerCoefficients (TopCat.of B) (Subtype.val ⁻¹' A) n = 0 := fun n =>
    (les_exact₂ integerCoefficients _ _ n).epi_f_iff.1 (haveI := hiso n; inferInstance)
  have hδ : ∀ n, δ integerCoefficients (TopCat.of B) (Subtype.val ⁻¹' A) n = 0 := fun n =>
    (les_exact₁ integerCoefficients _ _ n).mono_g_iff.1 (haveI := hiso n; inferInstance)
  intro n
  cases n with
  | zero =>
    let : HasCoproducts.{u} (ModuleCat.{u} ℤ) := fun _ => inferInstance
    have : Epi (relπ integerCoefficients (TopCat.of B) (Subtype.val ⁻¹' A) 0) :=
      inferInstanceAs (Epi ((pair (TopCat.of B) (Subtype.val ⁻¹' A)).homologyπ integerCoefficients 0))
    exact IsZero.of_epi_eq_zero _ (hπ 0)
  | succ n => exact (les_exact₃ integerCoefficients _ _ n).isZero_X₂ (hπ (n + 1)) (hδ n)

end DifferentialGeometry.Topology

end

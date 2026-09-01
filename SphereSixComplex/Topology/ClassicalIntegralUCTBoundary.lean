module

public import SphereSixComplex.Topology.IntegralSingularCohomology
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# The integral universal coefficient theorem

This file isolates the ordinary universal coefficient theorem for singular cohomology with
integer coefficients.  The theorem is stated for every topological space and every degree.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace SphereSixComplex

/-- The first derived `Ext` group over the integers. -/
public abbrev IntegralExtOne (G : Type) [AddCommGroup G] : Type :=
  CategoryTheory.Abelian.Ext (ModuleCat.of ℤ G) (ModuleCat.of ℤ ℤ) 1

/-- A full degreewise statement of the integral universal coefficient theorem for singular
cohomology.  In degree zero it is the evaluation isomorphism.  In positive degrees it is the
standard (noncanonically) split short exact sequence
`0 → Ext¹(Hₙ₋₁(X), ℤ) → Hⁿ(X; ℤ) → Hom(Hₙ(X), ℤ) → 0`.

The `Nonempty` wrapper records that the splitting is not natural. -/
public structure IntegralSingularCohomologyUCT where
  degreeZero : ∀ (X : Type) [TopologicalSpace X],
    IntegralSingularCohomology 0 X ≃+ (IntegralSingularHomology 0 X →+ ℤ)
  positiveDegree : ∀ (X : Type) [TopologicalSpace X] (n : ℕ), 0 < n →
    Nonempty (IntegralSingularCohomology n X ≃+
      (IntegralExtOne (IntegralSingularHomology (n - 1) X) ×
        (IntegralSingularHomology n X →+ ℤ)))

/-- The classical integral universal coefficient theorem for singular cohomology, in every
degree and for every topological space. -/
public axiom classicalIntegralSingularCohomologyUCT : IntegralSingularCohomologyUCT

public def addEquivProdOfSubsingleton {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (hA : Subsingleton A) : (A × B) ≃+ B where
  toFun := Prod.snd
  invFun b := (0, b)
  left_inv x := by
    ext
    · exact @Subsingleton.elim A hA _ _
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- When the preceding homology group is free, the `Ext` term in the integral UCT vanishes and
evaluation gives an additive equivalence with the integral dual of homology. -/
public noncomputable def integralSingularCohomologyEquivDualOfPreviousFree
    (X : Type) [TopologicalSpace X] (n : ℕ) (hn : 0 < n)
    (hFree : Module.Free ℤ (IntegralSingularHomology (n - 1) X)) :
    IntegralSingularCohomology n X ≃+ (IntegralSingularHomology n X →+ ℤ) := by
  let _ : Module.Free ℤ (IntegralSingularHomology (n - 1) X) := hFree
  letI : Projective (ModuleCat.of ℤ (IntegralSingularHomology (n - 1) X)) :=
    ModuleCat.projective_of_free
      (Module.Free.chooseBasis ℤ (IntegralSingularHomology (n - 1) X))
  let hExt : Subsingleton (IntegralExtOne (IntegralSingularHomology (n - 1) X)) := by
    have h := CategoryTheory.projective_iff_subsingleton_ext_one.mp
      (show Projective (ModuleCat.of ℤ (IntegralSingularHomology (n - 1) X)) from inferInstance)
    exact h (Y := ModuleCat.of ℤ ℤ)
  exact Classical.choice (classicalIntegralSingularCohomologyUCT.positiveDegree X n hn) |>.trans
    (addEquivProdOfSubsingleton hExt)

end SphereSixComplex

end

end

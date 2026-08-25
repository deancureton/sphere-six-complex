module

public import SphereSixComplex.Topology.SimplicialSingularComparison
public import SphereSixComplex.Topology.SixSphereDegreeHomology

/-!
# Top-homology orientation from the boundary-simplex comparison

This file connects the canonical simplicial--singular comparison with the homological degree
package.  Once degree-six simplicial homology of `∂Δ[7]` is identified with `ℤ`, the integral
comparison quasi-isomorphism and realization homeomorphism transport that generator to singular
top homology of `S⁶`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

/-- An isomorphism in `AddCommGrpCat` gives the corresponding additive equivalence of its
underlying groups. -/
public noncomputable def addEquivOfAddCommGrpCatIso {X Y : AddCommGrpCat}
    (e : X ≅ Y) : X ≃+ Y where
  toFun := e.hom.hom
  invFun := e.inv.hom
  left_inv x := by
    simp
  right_inv y := by
    simp
  map_add' x y := e.hom.hom.map_add x y

/-- The remaining finite top-dimensional computation on the combinatorial sphere. -/
public def BoundarySevenSimplicialTopHomologyOrientation : Prop :=
  Nonempty (((∂Δ[7] : SSet.{0}).chainComplex
    (AddCommGrpCat.of ℤ)).homology 6 ≃+ ℤ)

/-- Integral comparison and the realization homeomorphism transport a combinatorial generator to
an additive orientation of singular top homology of the standard six-sphere. -/
public noncomputable def sixSphereTopHomologyAddEquivOfBoundaryComparison
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (e : (SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type) ≃ₜ SixSphere)
    (orientation : ((∂Δ[7] : SSet.{0}).chainComplex
      (AddCommGrpCat.of ℤ)).homology 6 ≃+ ℤ) :
    IntegralSingularHomology 6 SixSphere ≃+ ℤ := by
  let _ : QuasiIso (simplicialToRealizationSingularChainMap
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)) := hcomparison
  let comparisonIso := isoOfQuasiIsoAt
    (simplicialToRealizationSingularChainMap
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)) 6
  let homeomorphismIso :=
    ((singularHomologyFunctor AddCommGrpCat 6).obj
      (AddCommGrpCat.of ℤ)).mapIso
        (TopCat.isoOfHomeo e :
          SSet.toTop.obj (∂Δ[7] : SSet.{0}) ≅ TopCat.of SixSphere)
  exact (addEquivOfAddCommGrpCatIso
    (comparisonIso.trans homeomorphismIso)).symm.trans orientation

/-- The packaged boundary comparison inputs and finite top-homology computation supply exactly
the additive orientation used by homological degree. -/
public theorem sixSphereTopHomologyOrientation_of_boundaryComparison
    (hcomparison : BoundarySevenComparisonInputs (AddCommGrpCat.of ℤ))
    (htop : BoundarySevenSimplicialTopHomologyOrientation) :
    Nonempty (IntegralSingularHomology 6 SixSphere ≃+ ℤ) := by
  obtain ⟨hc, ⟨e⟩⟩ := hcomparison
  obtain ⟨orientation⟩ := htop
  exact ⟨sixSphereTopHomologyAddEquivOfBoundaryComparison hc e orientation⟩

/-- After the comparison inputs, the complete degree theory is reduced to the finite top-homology
generator and the single calculation that antipodal sends its transported generator to `-1`. -/
public theorem sixSphereDegreeTheory_of_boundaryComparison
    (hcomparison : BoundarySevenComparisonInputs (AddCommGrpCat.of ℤ))
    (htop : BoundarySevenSimplicialTopHomologyOrientation)
    (hantipodal : ∀ orientation : IntegralSingularHomology 6 SixSphere ≃+ ℤ,
      sixSphereHomologicalDegree orientation
        OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun = -1) :
    Nonempty OrientedMarkedSmoothHomotopySixSphere.SixSphereDegreeTheory := by
  obtain ⟨orientation⟩ :=
    sixSphereTopHomologyOrientation_of_boundaryComparison hcomparison htop
  exact ⟨SixSphereTopHomologyOrientation.toDegreeTheory
    ⟨orientation, hantipodal orientation⟩⟩

end SphereSixComplex

module

public import DifferentialGeometry.Topology.Homology.Algebra.EventualImage
public import DifferentialGeometry.Topology.Homology.Subdivision.SingularSupport
public import DifferentialGeometry.Topology.Homology.Subdivision.EventualSmallness

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v
namespace DifferentialGeometry.Homology
variable (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)

theorem quasiIso_smallChainMap
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (smallChainMap X U R) := by
  let := mono_smallChainMap X U R
  apply DifferentialGeometry.HomologicalComplex.quasiIso_of_eventually_in_image (smallChainMap X U R)
    (smallSingularSubdivision X U R) (End.of (singularSubdivision R X))
    (smallSingularSubdivision_inclusion X U R).symm
    (singularSubdivisionHomotopy R X) (smallSingularSubdivisionHomotopyMap X U R)
  · intro n
    rw [singularSubdivisionHomotopy_hom]
    exact (smallSingularSubdivisionHomotopyMap_inclusion X U R n).symm
  · exact exists_small_subdivision_power R X U hopen hcover


def smallChainHomologyIso
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    ((smallSingularSimplices X U : SSet).chainComplex R).homology n ≅
      ((TopCat.toSSet.obj X).chainComplex R).homology n := by
  letI := quasiIso_smallChainMap X U R hopen hcover
  exact isoOfQuasiIsoAt (smallChainMap X U R) n


@[simp]
theorem smallChainHomologyIso_hom
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (smallChainHomologyIso X U R hopen hcover n).hom =
      _root_.HomologicalComplex.homologyMap (smallChainMap X U R) n := rfl

end DifferentialGeometry.Homology

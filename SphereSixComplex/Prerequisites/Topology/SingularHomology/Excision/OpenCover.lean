module

public import SphereSixComplex.Prerequisites.Topology.SingularHomology.Excision.SmallChains
import DifferentialGeometry.Topology.Homology.SmallChains.QuasiIso
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex

/-!
# Small-chain approximation for open covers

The small-chain theorem over integer modules transfers to abelian groups through the
natural comparison of simplicial chain complexes with change of coefficient category.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology

namespace SphereSixComplex

variable {ι : Type} (X : TopCat) (U : ι → Set X)

/-- The cover-small inclusion is a quasi-isomorphism for every open cover. -/
public theorem coverSmallChainQuasiIsomorphism_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    QuasiIso (coverSmallIntegralSingularChainInclusion X U) := by
  let F := forget₂ (ModuleCat ℤ) AddCommGrpCat
  let R := ModuleCat.of ℤ ℤ
  have h := DifferentialGeometry.Homology.quasiIso_smallChainMap X U R hUopen (by
    intro x
    have hx : x ∈ ⋃ i, U i := by rw [hUcover]; trivial
    simpa using hx)
  let f := DifferentialGeometry.Homology.smallChainMap X U R
  have : QuasiIso ((F.mapHomologicalComplex (.down ℕ)).map f) := inferInstance
  have he := DifferentialGeometry.Homology.smallSingularSimplices_eq_iSup_range X U
  change DifferentialGeometry.Homology.smallSingularSimplices X U =
    coverSmallSingularSubcomplex X U at he
  let e := SSet.chainComplexFunctorObjCompMapIso F R
  have hq : QuasiIso (SSet.chainComplexMap
      (DifferentialGeometry.Homology.smallSingularSimplices X U).ι (AddCommGrpCat.of ℤ)) := by
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (e.app _) (e.app _) (e.hom.naturality _).symm)).mp this
  change QuasiIso (SSet.chainComplexMap
    (coverSmallSingularSubcomplex X U).ι (AddCommGrpCat.of ℤ))
  rw [← he]
  exact hq

end SphereSixComplex

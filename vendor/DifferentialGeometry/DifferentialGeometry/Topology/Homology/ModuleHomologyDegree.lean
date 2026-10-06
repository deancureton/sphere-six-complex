module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyMaps
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace DifferentialGeometry.Topology

variable {R : Type u} [Ring R] {ι : Type w} {shape : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{v} R) shape}

theorem exists_moduleCycle_map_of_eq (φ : K ⟶ L) {n t : ι} (h : n = t)
    (z : LinearMap.ker (K.sc n).g.hom) :
    ∃ z' : LinearMap.ker (L.sc t).g.hom,
      z'.val = (L.XIsoOfEq h).hom (φ.f n z.val) ∧
      moduleHomologyClass (L.sc t) z' =
        eqToHom (congrArg (fun i => L.homology i) h)
          (HomologicalComplex.homologyMap φ n (moduleHomologyClass (K.sc n) z)) := by
  subst t
  refine ⟨moduleCycleMap ((HomologicalComplex.shortComplexFunctor _ _ n).map φ) z, ?_, ?_⟩
  · rfl
  · exact (moduleHomologyClass_map ((HomologicalComplex.shortComplexFunctor _ _ n).map φ) z).symm

end DifferentialGeometry.Topology

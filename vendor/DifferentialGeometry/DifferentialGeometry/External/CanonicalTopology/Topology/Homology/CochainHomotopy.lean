module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainMaps
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology

universe u

namespace DifferentialGeometry.Topology

def integralSingularCochainsDualIso (X : Type u) [TopologicalSpace X] :
    (((linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).mapHomologicalComplex
      (.up ℕ)).obj (integralSingularChains X).op ≅ integralSingularCochains X := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n =>
    (ModuleCat.homLinearEquiv (R := ℤ) (S := ℤ)
      (M := (integralSingularChains X).X n)
      (N := integralSingularCoefficients)).toModuleIso) ?_
  intro i j _
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  rfl

theorem integralSingularCochainsDualIso_natural
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : ContinuousMap X Y) :
    (integralSingularCochainsDualIso Y).hom ≫ integralSingularCochainMap f =
      (((linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).mapHomologicalComplex
        (.up ℕ)).map ((HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ)).map
          (integralSingularChainMap f).op) ≫ (integralSingularCochainsDualIso X).hom := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  rfl

def integralSingularCochainMapHomotopy
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : ContinuousMap X Y} (H : f.Homotopy g) :
    _root_.Homotopy (integralSingularCochainMap f) (integralSingularCochainMap g) := by
  let F := (linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients
  let G := HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ)
  let h := TopCat.Homotopy.singularChainComplexFunctorObjMap
    (show TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) from H) integralSingularCoefficients
  have he (a : ContinuousMap X Y) :
      ((integralSingularCochainsDualIso Y).inv ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map
          (G.map (integralSingularChainMap a).op)) ≫
          (integralSingularCochainsDualIso X).hom = integralSingularCochainMap a := by
    ext n : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro c
    rfl
  exact (Homotopy.ofEq (he f).symm).trans
    (((F.mapHomotopy h.op).compLeft (integralSingularCochainsDualIso Y).inv).compRight
      (integralSingularCochainsDualIso X).hom |>.trans (Homotopy.ofEq (he g)))

theorem integralSingularCohomologyMap_eq_of_homotopic
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : ContinuousMap X Y} (h : f.Homotopic g) (n : ℕ) :
    integralSingularCohomologyMap n f = integralSingularCohomologyMap n g := by
  obtain ⟨H⟩ := h
  exact congrArg (fun a => a.hom) ((integralSingularCochainMapHomotopy H).homologyMap_eq n)

theorem integralSingularCohomologyMap_bijective_of_homotopyEquiv
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    Function.Bijective (integralSingularCohomologyMap n ⟨e, e.continuous⟩) := by
  have hleft : Function.LeftInverse
      (integralSingularCohomologyMap n ⟨e.symm, e.symm.continuous⟩)
      (integralSingularCohomologyMap n ⟨e, e.continuous⟩) := by
    have h := integralSingularCohomologyMap_eq_of_homotopic e.right_inv n
    rw [integralSingularCohomologyMap_comp, integralSingularCohomologyMap_id] at h
    exact fun α => LinearMap.congr_fun h α
  have hright : Function.RightInverse
      (integralSingularCohomologyMap n ⟨e.symm, e.symm.continuous⟩)
      (integralSingularCohomologyMap n ⟨e, e.continuous⟩) := by
    have h := integralSingularCohomologyMap_eq_of_homotopic e.left_inv n
    rw [integralSingularCohomologyMap_comp, integralSingularCohomologyMap_id] at h
    exact fun α => LinearMap.congr_fun h α
  exact ⟨hleft.injective, hright.surjective⟩

end DifferentialGeometry.Topology

end

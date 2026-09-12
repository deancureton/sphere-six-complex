module

public import SphereSixComplex.Paper.Topology.PaperCuspCentralFiberCWConstruction

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex SphereSixComplex.Periods
open CuspFilling CuspPeriodExpansion InfiniteA2Toric

variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

public def actualCuspCentralOrbitFillingHomologyEquiv
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) (k : ℕ) :
    IntegralSingularHomology k (ActualLocalCuspCentralOrbitQuotient W) ≃+
      IntegralSingularHomology k (ActualLocalCuspFilling W) :=
  (integralSingularHomologyEquiv k (actualLocalCuspCentralOrbitCoreHomeomorph W R)).trans
    (R.specializationHomologyEquiv W k).symm

public theorem actualCuspCentralOrbitFillingHomologyEquiv_apply
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) (k : ℕ)
    (x : IntegralSingularHomology k (ActualLocalCuspCentralOrbitQuotient W)) :
    actualCuspCentralOrbitFillingHomologyEquiv W R k x =
      integralSingularHomologyMap k
        ⟨actualLocalCuspCentralOrbitMap W, (actualLocalCuspCentralOrbitMap_isEmbedding W).continuous⟩ x := by
  change integralSingularHomologyMap k (R.quotientCentralFiberInclusion W)
    (integralSingularHomologyMap k (actualLocalCuspCentralOrbitCoreHomeomorph W R) x) = _
  have hc : ∀ {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
      (f : C(X, Y)) (g : C(Y, Z)) (x : IntegralSingularHomology k X),
      integralSingularHomologyMap k g (integralSingularHomologyMap k f x) =
        integralSingularHomologyMap k (g.comp f) x := by
    intro X Y Z _ _ _ f g z
    exact (CategoryTheory.ConcreteCategory.congr_hom
      (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map_comp
        (TopCat.ofHom f) (TopCat.ofHom g)) z).symm
  rw [hc]
  rfl

end SphereSixComplex.Geometry.CuspCollar

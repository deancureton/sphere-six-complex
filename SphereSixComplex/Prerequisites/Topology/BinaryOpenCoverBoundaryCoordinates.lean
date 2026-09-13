module

public import SphereSixComplex.Prerequisites.Topology.BinaryOpenCoverLegacyMayerVietoris

@[expose] public section

open CategoryTheory TopologicalSpace

namespace SphereSixComplex.BinaryOpenCover

theorem IntegralMayerVietorisData.legacyBoundary_unionHomeomorph_symm
    {X : TopCat} {U V : Opens X} {hcover : U ⊔ V = ⊤}
    (D : IntegralMayerVietorisData U V hcover) (n : ℕ)
    (x : IntegralSingularHomology (n + 1) X) :
    D.legacyBoundary n
        (integralSingularHomologyMap (n + 1)
          ⟨(opensUnionHomeomorph U V hcover).symm,
            (opensUnionHomeomorph U V hcover).symm.continuous⟩ x) =
      ConcreteCategory.hom
        (D.boundary n ≫ (opensIntersectionHomologyIso U V n).inv) x := by
  change ConcreteCategory.hom
      ((opensUnionHomologyIso U V hcover (n + 1)).inv ≫
        (opensUnionHomologyIso U V hcover (n + 1)).hom ≫ D.boundary n ≫
        (opensIntersectionHomologyIso U V n).inv) x = _
  simp

end SphereSixComplex.BinaryOpenCover

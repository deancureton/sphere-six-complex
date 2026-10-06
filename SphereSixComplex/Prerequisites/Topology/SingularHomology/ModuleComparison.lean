module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Cochains
public import SphereSixComplex.Prerequisites.Topology.SingularHomology.Cohomology
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Module.ULift
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Comparing integral singular chains and cochains across coefficient categories

DifferentialGeometry uses integer modules with lifted coefficients. These isomorphisms
identify its singular homology and cohomology with the additive-group models used here.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open DifferentialGeometry.Topology (integralSingularChains integralSingularCochains)

namespace SphereSixComplex.IntegralSingularComparison

def chainsIso (X : Type) [TopologicalSpace X] :
    ((forget₂ (ModuleCat ℤ) AddCommGrpCat).mapHomologicalComplex (.down ℕ)).obj (integralSingularChains X) ≅
      SphereSixComplex.integralSingularCochainSource X :=
  (SSet.chainComplexFunctorObjCompMapIso (forget₂ (ModuleCat ℤ) AddCommGrpCat) (ModuleCat.of ℤ (ULift.{0} ℤ))).app
    (TopCat.toSSet.obj (TopCat.of X)) ≪≫
    ((SSet.chainComplexFunctor AddCommGrpCat).mapIso
      ((forget₂ (ModuleCat ℤ) AddCommGrpCat).mapIso (ULift.moduleEquiv (R := ℤ) (M := ℤ)).toModuleIso)).app (TopCat.toSSet.obj (TopCat.of X))

def homologyIso (X : Type) [TopologicalSpace X] (n : ℕ) :
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).obj ((integralSingularChains X).homology n) ≅
      AddCommGrpCat.of (SphereSixComplex.IntegralSingularHomology n X) :=
  ((integralSingularChains X).sc n |>.mapHomologyIso (forget₂ (ModuleCat ℤ) AddCommGrpCat)).symm ≪≫
    HomologicalComplex.homologyMapIso (chainsIso X) n

def intLinearMapAddEquiv (A B : ModuleCat ℤ) : (A →ₗ[ℤ] B) ≃+ (A →+ B) where
  toFun := LinearMap.toAddMonoidHom
  invFun f := by
    refine { f with map_smul' := ?_ }
    intro n x
    convert! f.map_zsmul n x <;> ext <;> apply int_smul_eq_zsmul
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def cochainEquiv (X : Type) [TopologicalSpace X] (n : ℕ) :
    ((integralSingularChains X).X n →ₗ[ℤ] ULift.{0} ℤ) ≃+
      SphereSixComplex.IntegralSingularCochains n X :=
  (intLinearMapAddEquiv ((integralSingularChains X).X n) (ModuleCat.of ℤ (ULift.{0} ℤ))).trans
    ((HomologicalComplex.Hom.isoApp (chainsIso X) n).addCommGroupIsoToAddEquiv.addMonoidHomCongrLeft.trans
      (ULift.moduleEquiv (R := ℤ) (M := ℤ)).toAddEquiv.addMonoidHomCongrRight)

theorem cochainEquiv_coboundary (X : Type) [TopologicalSpace X] (n : ℕ)
    (φ : (integralSingularChains X).X n →ₗ[ℤ] ULift.{0} ℤ) :
    cochainEquiv X (n + 1) (φ.comp ((integralSingularChains X).d (n + 1) n).hom) =
      SphereSixComplex.integralSingularCoboundary X n (cochainEquiv X n φ) := by
  ext x
  change (φ ((integralSingularChains X).d (n + 1) n ((chainsIso X).inv.f (n + 1) x))).down =
    (φ ((chainsIso X).inv.f n ((SphereSixComplex.integralSingularCochainSource X).d
      (n + 1) n x))).down
  exact congrArg (fun z ↦ (φ z).down)
    (congrArg (fun f ↦ f x) ((chainsIso X).inv.comm (n + 1) n))

def cochainsIso (X : Type) [TopologicalSpace X] :
    ((forget₂ (ModuleCat ℤ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj (integralSingularCochains X) ≅
      SphereSixComplex.integralSingularCochainComplex X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (cochainEquiv X n).toAddCommGrpIso) (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      ext φ
      change ((SphereSixComplex.integralSingularCochainComplex X).d i (i + 1))
        (cochainEquiv X i φ) = cochainEquiv X (i + 1) (DifferentialGeometry.Topology.integralSingularCoboundary X i (i + 1) φ)
      dsimp only [SphereSixComplex.integralSingularCochainComplex]
      rw [CochainComplex.of_d]
      exact (cochainEquiv_coboundary X i φ).symm)

def cohomologyEquiv (X : Type) [TopologicalSpace X] (n : ℕ) :
    (integralSingularCochains X).homology n ≃+ SphereSixComplex.IntegralSingularCohomology n X :=
  (((integralSingularCochains X).sc n |>.mapHomologyIso (forget₂ (ModuleCat ℤ) AddCommGrpCat)).symm ≪≫
    HomologicalComplex.homologyMapIso (cochainsIso X) n).addCommGroupIsoToAddEquiv

end SphereSixComplex.IntegralSingularComparison

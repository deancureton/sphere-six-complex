module
public import SphereSixComplex.Topology.EstablishedFirstHurewicz
public import SphereSixComplex.Topology.EstablishedBasedVanKampen
public import SphereSixComplex.Topology.EstablishedChosenAffineFillings

@[expose] public section
noncomputable section
open CategoryTheory AlgebraicTopology
namespace SphereSixComplex.Topology.FirstHurewiczProof
open SphereSixComplex.StandardCircleHomologyLiftDegree

public theorem loopHomologyClass_whisker {X : Type} [TopologicalSpace X]
    {x y : X} (w : Path x y) (p : Path y y) :
    loopHomologyClass (w.trans (p.trans w.symm)) = loopHomologyClass p := by
  apply (AddCommGrpCat.mono_iff_injective ((IntegralChains X).homologyι 1)).mp
    (inferInstance : Mono ((IntegralChains X).homologyι 1))
  rw [homologyι_loopHomologyClass, homologyι_loopHomologyClass,
    pathOpchainClass_trans, pathOpchainClass_trans, pathOpchainClass_symm]
  abel

public theorem hurewiczFunction_basePath {X : Type} [TopologicalSpace X]
    {x y : X} (w : Path x y) (g : FundamentalGroup X x) :
    hurewiczFunction y (FundamentalGroup.fundamentalGroupMulEquivOfPath w g) =
      hurewiczFunction x g := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  change loopHomologyClass (w.symm.trans (p.trans w)) = loopHomologyClass p
  simpa only [Path.symm_symm] using loopHomologyClass_whisker w.symm p

public theorem hurewiczFunction_map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (g : FundamentalGroup X x) :
    hurewiczFunction (f x) (FundamentalGroup.map f x g) =
      integralSingularHomologyMap 1 f (hurewiczFunction x g) := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  exact (integralSingularHomologyMap_loopHomologyClass f p).symm

public theorem hurewiczFunction_baseEq {X : Type} [TopologicalSpace X]
    {x y : X} (h : x = y) (g : FundamentalGroup X x) :
    hurewiczFunction y (fundamentalGroupElementOfBaseEq h g) = hurewiczFunction x g := by
  subst y
  rfl

public theorem hurewiczFunction_eq_established {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) (g : FundamentalGroup X x) :
    hurewiczFunction x g =
      (EstablishedFirstHurewicz.establishedFirstHurewiczData X x).equiv
        (Additive.ofMul (Abelianization.of g)) := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  exact ((EstablishedFirstHurewicz.establishedFirstHurewiczData X x).equiv_loopClass p).symm

end SphereSixComplex.Topology.FirstHurewiczProof
end

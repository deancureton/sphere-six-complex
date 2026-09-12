module

public import SphereSixComplex.Prerequisites.Topology.EstablishedFirstHurewicz
public import SphereSixComplex.Prerequisites.Topology.FundamentalGroupSimplyConnected

@[expose] public section
noncomputable section

namespace SphereSixComplex.Topology

public theorem simplyConnectedSpace_of_mul_comm_of_homologyOne_subsingleton
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (b : X)
    (hcomm : ∀ x y : FundamentalGroup X b, x * y = y * x)
    [Subsingleton (IntegralSingularHomology 1 X)] : SimplyConnectedSpace X := by
  let : CommGroup (FundamentalGroup X b) :=
    { (inferInstance : Group (FundamentalGroup X b)) with mul_comm := hcomm }
  let e := Abelianization.equivOfComm.toAdditive.trans
    (Hurewicz.Chains.abelianizationComparison X b).equiv.toAddEquiv
  have : Subsingleton (FundamentalGroup X b) := ⟨fun x y ↦
    Additive.ofMul.injective (e.injective (Subsingleton.elim _ _))⟩
  exact simplyConnectedSpace_of_fundamentalGroup_subsingleton b

end SphereSixComplex.Topology

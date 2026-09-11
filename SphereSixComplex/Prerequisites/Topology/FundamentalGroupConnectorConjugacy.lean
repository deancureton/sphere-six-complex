module

public import SphereSixComplex.Prerequisites.Topology.GroupPairConjugacy
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Connector changes and simultaneous conjugacy

Changing the path used to identify two fundamental-group basepoints conjugates every
transported loop by one common element.  This is the basepoint-invariant bridge needed when a
pair of marked peripheral loops is compared using an existentially chosen based chart.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace SphereSixComplex.Topology

/-- Transporting two loops along two paths with the same endpoints changes the ordered pair by
one simultaneous conjugation. -/
public theorem fundamentalGroupPair_simultaneouslyConjugate_of_paths
    {X : Type*} [TopologicalSpace X] {x y : X}
    (p q : Path x y) (a b : FundamentalGroup X x) :
    SimultaneouslyConjugate
      (FundamentalGroup.fundamentalGroupMulEquivOfPath p a,
        FundamentalGroup.fundamentalGroupMulEquivOfPath p b)
      (FundamentalGroup.fundamentalGroupMulEquivOfPath q a,
        FundamentalGroup.fundamentalGroupMulEquivOfPath q b) := by
  let ip := (Groupoid.isoEquivHom (FundamentalGroupoid.mk x)
    (FundamentalGroupoid.mk y)).symm ⟦p⟧
  let iq := (Groupoid.isoEquivHom (FundamentalGroupoid.mk x)
    (FundamentalGroupoid.mk y)).symm ⟦q⟧
  let ic := iq.symm ≪≫ ip
  refine ⟨ic.hom, ?_, ?_⟩
  · simp only [FundamentalGroup.fundamentalGroupMulEquivOfPath, Iso.conj_apply,
      FundamentalGroup.mul_def]
    have hic : @Inv.inv (FundamentalGroup X y) inferInstance ic.hom = ic.inv := by
      change Groupoid.inv ic.hom = ic.inv
      rw [Groupoid.inv_eq_inv]
      exact (IsIso.eq_inv_of_hom_inv_id ic.hom_inv_id).symm
    rw [hic]
    change ip.inv ≫ a ≫ ip.hom = ic.inv ≫ (iq.inv ≫ a ≫ iq.hom) ≫ ic.hom
    simp [ic, Category.assoc]
  · simp only [FundamentalGroup.fundamentalGroupMulEquivOfPath, Iso.conj_apply,
      FundamentalGroup.mul_def]
    have hic : @Inv.inv (FundamentalGroup X y) inferInstance ic.hom = ic.inv := by
      change Groupoid.inv ic.hom = ic.inv
      rw [Groupoid.inv_eq_inv]
      exact (IsIso.eq_inv_of_hom_inv_id ic.hom_inv_id).symm
    rw [hic]
    change ip.inv ≫ b ≫ ip.hom = ic.inv ≫ (iq.inv ≫ b ≫ iq.hom) ≫ ic.hom
    simp [ic, Category.assoc]



end SphereSixComplex.Topology

end

end

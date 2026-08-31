module

public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeCommonGaugeGeometry

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
    have hic : (ic.hom : FundamentalGroup X y)⁻¹ = ic.inv := by
      change Groupoid.inv ic.hom = ic.inv
      rw [Groupoid.inv_eq_inv]
      exact (IsIso.eq_inv_of_hom_inv_id ic.hom_inv_id).symm
    rw [hic]
    change ip.inv ≫ a ≫ ip.hom = ic.inv ≫ (iq.inv ≫ a ≫ iq.hom) ≫ ic.hom
    simp [ic, Category.assoc]
  · simp only [FundamentalGroup.fundamentalGroupMulEquivOfPath, Iso.conj_apply,
      FundamentalGroup.mul_def]
    have hic : (ic.hom : FundamentalGroup X y)⁻¹ = ic.inv := by
      change Groupoid.inv ic.hom = ic.inv
      rw [Groupoid.inv_eq_inv]
      exact (IsIso.eq_inv_of_hom_inv_id ic.hom_inv_id).symm
    rw [hic]
    change ip.inv ≫ b ≫ ip.hom = ic.inv ≫ (iq.inv ≫ b ≫ iq.hom) ≫ ic.hom
    simp [ic, Category.assoc]

/-- For a fixed map, changing the target connector conjugates the images of any two loops by
one common element. -/
public theorem fundamentalGroupMappedPair_simultaneouslyConjugate_of_connectors
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) {y : Y} (p q : Path (f x) y)
    (a b : FundamentalGroup X x) :
    SimultaneouslyConjugate
      (FundamentalGroup.fundamentalGroupMulEquivOfPath p (FundamentalGroup.map f x a),
        FundamentalGroup.fundamentalGroupMulEquivOfPath p (FundamentalGroup.map f x b))
      (FundamentalGroup.fundamentalGroupMulEquivOfPath q (FundamentalGroup.map f x a),
        FundamentalGroup.fundamentalGroupMulEquivOfPath q (FundamentalGroup.map f x b)) :=
  fundamentalGroupPair_simultaneouslyConjugate_of_paths p q _ _

/-- Changing the point selected over a quotient-cover basepoint conjugates the deck labels of
any two loops by the single deck element relating the two selected points. -/
public theorem quotientCoverFundamentalGroupPair_simultaneouslyConjugate_of_smul
    {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [Group G] [MulAction G E] {p : C(E, X)}
    (hp : IsQuotientCoveringMap p G) [SimplyConnectedSpace E]
    {x : X} (e₁ e₂ : p ⁻¹' {x}) (c : G) (he : e₂.1 = c • e₁.1)
    (a b : FundamentalGroup X x) :
    SimultaneouslyConjugate
      (MulOpposite.unop (hp.fundamentalGroupEquiv e₂ a),
        MulOpposite.unop (hp.fundamentalGroupEquiv e₂ b))
      (MulOpposite.unop (hp.fundamentalGroupEquiv e₁ a),
        MulOpposite.unop (hp.fundamentalGroupEquiv e₁ b)) := by
  refine ⟨c, ?_, ?_⟩
  · change MulOpposite.unop (hp.fundamentalGroupToMulOpposite e₂ a) =
      c * MulOpposite.unop (hp.fundamentalGroupToMulOpposite e₁ a) * c⁻¹
    apply hp.isCancelSMul.right_cancel _ _ e₂.1
    rw [hp.unop_fundamentalGroupToMulOpposite_smul]
    rw [he, mul_smul, mul_smul, inv_smul_smul]
    rw [hp.unop_fundamentalGroupToMulOpposite_smul]
    have he' : e₂ = hp.toPermFiber x c e₁ := Subtype.ext he
    rw [he']
    exact congrArg Subtype.val
      (hp.monodromy_toPermFiber (g := c) (e := e₁) (γ := a))
  · change MulOpposite.unop (hp.fundamentalGroupToMulOpposite e₂ b) =
      c * MulOpposite.unop (hp.fundamentalGroupToMulOpposite e₁ b) * c⁻¹
    apply hp.isCancelSMul.right_cancel _ _ e₂.1
    rw [hp.unop_fundamentalGroupToMulOpposite_smul]
    rw [he, mul_smul, mul_smul, inv_smul_smul]
    rw [hp.unop_fundamentalGroupToMulOpposite_smul]
    have he' : e₂ = hp.toPermFiber x c e₁ := Subtype.ext he
    rw [he']
    exact congrArg Subtype.val
      (hp.monodromy_toPermFiber (g := c) (e := e₁) (γ := b))

end SphereSixComplex.Topology

end

end

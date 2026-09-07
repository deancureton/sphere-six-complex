module

public import SphereSixComplex.Topology.EstablishedAffineVanKampen
public import SphereSixComplex.Topology.TwicePuncturedComplexMarkedMeridians

@[expose] public section
noncomputable section

namespace SphereSixComplex

public theorem fundamentalGroupToMulOpposite_transport_endpoint
    {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [Group G] [MulAction G E] {p : C(E, X)}
    (hp : IsQuotientCoveringMap p G) {x y : X}
    (W : Path x y) (ex : p ⁻¹' {x}) (gamma : FundamentalGroup X x) :
    hp.fundamentalGroupToMulOpposite
        (hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk W) ex)
        (FundamentalGroup.fundamentalGroupMulEquivOfPath W gamma) =
      hp.fundamentalGroupToMulOpposite ex gamma := by
  let w := Path.Homotopic.Quotient.mk W
  let h := (hp.fundamentalGroupToMulOpposite ex gamma).unop
  have hx : hp.toPermFiber x h ex = hp.isCoveringMap.monodromy gamma ex := by
    apply Subtype.ext
    exact hp.unop_fundamentalGroupToMulOpposite_smul
  apply hp.fundamentalGroupToMulOpposite_apply_eq_Iff.mpr
  change h • (hp.isCoveringMap.monodromy w ex).val =
    (hp.isCoveringMap.monodromy (w.symm.trans (gamma.trans w))
      (hp.isCoveringMap.monodromy w ex)).val
  have hcancel : hp.isCoveringMap.monodromy w.symm
      (hp.isCoveringMap.monodromy w ex) = ex := by
    rw [← hp.isCoveringMap.monodromy_trans_apply]
    simp only [Path.Homotopic.Quotient.trans_symm, hp.isCoveringMap.monodromy_refl, id_eq]
  rw [hp.isCoveringMap.monodromy_trans_apply,
    hp.isCoveringMap.monodromy_trans_apply, hcancel]
  have heq := hp.monodromy_toPermFiber (γ := w) (e := ex) (g := h)
  rw [hx] at heq
  exact (congrArg Subtype.val heq).symm

public theorem fundamentalGroupToMulOpposite_change_sheet
    {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [Group G] [MulAction G E] {p : C(E, X)}
    (hp : IsQuotientCoveringMap p G) {x : X}
    (ex : p ⁻¹' {x}) (g : G) (gamma : FundamentalGroup X x) :
    hp.fundamentalGroupToMulOpposite (hp.toPermFiber x g ex) gamma =
      MulOpposite.op (g * (hp.fundamentalGroupToMulOpposite ex gamma).unop * g⁻¹) := by
  apply hp.fundamentalGroupToMulOpposite_apply_eq_Iff.mpr
  have heq := hp.monodromy_toPermFiber (γ := gamma) (e := ex) (g := g)
  change (g * (hp.fundamentalGroupToMulOpposite ex gamma).unop * g⁻¹) •
      (g • ex.val) = (hp.isCoveringMap.monodromy gamma (hp.toPermFiber x g ex)).val
  rw [heq]
  change _ = g • (hp.isCoveringMap.monodromy gamma ex).val
  rw [← hp.unop_fundamentalGroupToMulOpposite_smul]
  simp only [mul_smul, inv_smul_smul]

public theorem fundamentalGroupToMulOpposite_transport_of_endpoint_sheet
    {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [Group G] [MulAction G E] {p : C(E, X)}
    (hp : IsQuotientCoveringMap p G) {x y : X}
    (W : Path x y) (ex : p ⁻¹' {x}) (ey : p ⁻¹' {y}) (g : G)
    (hW : hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk W) ex =
      hp.toPermFiber y g ey) (gamma : FundamentalGroup X x) :
    (hp.fundamentalGroupToMulOpposite ey
      (FundamentalGroup.fundamentalGroupMulEquivOfPath W gamma)).unop =
      g⁻¹ * (hp.fundamentalGroupToMulOpposite ex gamma).unop * g := by
  have h := fundamentalGroupToMulOpposite_transport_endpoint hp W ex gamma
  rw [hW, fundamentalGroupToMulOpposite_change_sheet] at h
  have hu := congrArg MulOpposite.unop h
  change g * _ * g⁻¹ = _ at hu
  rw [← hu]
  group

public theorem quotientCover_fundamentalGroupToMulOpposite_naturality
    {E E' X X' G H : Type*}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X] [TopologicalSpace X']
    [Group G] [Group H] [MulAction G E] [MulAction H E']
    {p : C(E, X)} {q : C(E', X')}
    (hp : IsQuotientCoveringMap p G) (hq : IsQuotientCoveringMap q H)
    (D : QuotientCoverMapData (G := G) (H := H) p q) (e : E)
    (γ : FundamentalGroup X (p e)) :
    (MonoidHom.op D.deckMap) (hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩ γ) =
      hq.fundamentalGroupToMulOpposite ⟨D.lift e, rfl⟩
        (FundamentalGroup.mapOfEq D.baseMap (D.commutes e) γ) := by
  symm
  refine (hq.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr ?_
  show D.deckMap ((hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩ γ).unop) • D.lift e = _
  rw [← D.equivariant]
  rw [show (hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩ γ).unop • e
      = (hp.isCoveringMap.monodromy γ ⟨e, rfl⟩ : E) from
    hp.unop_fundamentalGroupToMulOpposite_smul]
  exact (monodromy_naturality hp.isCoveringMap hq.isCoveringMap D.lift D.baseMap D.commutes
    e γ).symm


public theorem fundamentalGroupToMulOpposite_fiberBaseEq
    {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [Group G] [MulAction G E] {p : C(E, X)}
    (hp : IsQuotientCoveringMap p G) {x y : X}
    (e : p ⁻¹' {x}) (h : x = y) (gamma : FundamentalGroup X x) :
    hp.fundamentalGroupToMulOpposite ⟨e.val, e.property.trans h⟩
      (Topology.fundamentalGroupMulEquivOfEq h gamma) =
      hp.fundamentalGroupToMulOpposite e gamma := by
  cases h
  simp only [Topology.fundamentalGroupMulEquivOfEq_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl]

public theorem IsCoveringMap.exists_path_lift_of_monodromy_eq
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : C(E, X)}
    (hp : IsCoveringMap p) {x y : X} (W : Path x y)
    (ex : p ⁻¹' {x}) (ey : p ⁻¹' {y})
    (h : hp.monodromy (Path.Homotopic.Quotient.mk W) ex = ey) :
    ∃ Q : Path ex.val ey.val,
      (Q.map p.continuous).cast ex.property.symm ey.property.symm = W := by
  let L := hp.liftPath W ex.val (W.source.trans ex.property.symm)
  have hend : L 1 = ey.val := congrArg Subtype.val h
  let Q : Path ex.val ey.val := {
    toFun := L
    continuous_toFun := L.continuous
    source' := hp.liftPath_zero W ex.val (W.source.trans ex.property.symm)
    target' := hend }
  refine ⟨Q, ?_⟩
  apply Path.ext
  funext t
  exact congrFun (hp.liftPath_lifts W ex.val (W.source.trans ex.property.symm)) t

end SphereSixComplex

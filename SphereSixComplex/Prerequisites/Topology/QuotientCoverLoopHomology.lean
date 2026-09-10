module
public import SphereSixComplex.Prerequisites.Topology.HurewiczBasepointTransport
public import SphereSixComplex.Prerequisites.Topology.QuotientCoverMonodromyTransport

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Topology
open Hurewicz Hurewicz.Chains StandardCircleHomologyLiftDegree

public def abelianCoverHomologyEquiv
    {E X G : Type} [TopologicalSpace E] [TopologicalSpace X]
    [CommGroup G] [MulAction G E] [SimplyConnectedSpace E] [PathConnectedSpace X]
    {p : C(E, X)} (hp : IsQuotientCoveringMap p G) (e : E) :
    Additive G ≃+ IntegralSingularHomology 1 X :=
  (Abelianization.equivOfComm.toAdditive).trans
    (deckHOneEquivOfFundamentalGroupEquivOpposite (p e)
      (hp.fundamentalGroupEquiv ⟨e, rfl⟩)).toAddEquiv

public theorem abelianCoverHomologyEquiv_hurewicz
    {E X G : Type} [TopologicalSpace E] [TopologicalSpace X]
    [CommGroup G] [MulAction G E] [SimplyConnectedSpace E] [PathConnectedSpace X]
    {p : C(E, X)} (hp : IsQuotientCoveringMap p G) (e : E)
    (γ : FundamentalGroup X (p e)) :
    abelianCoverHomologyEquiv hp e
      (Additive.ofMul (hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩ γ).unop) =
      hurewiczFunction (p e) γ := by
  obtain ⟨q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
  exact deckHOneEquivOfFundamentalGroupEquivOpposite_markedLoop (p e)
    (hp.fundamentalGroupEquiv ⟨e, rfl⟩)
    (fun _ : Unit ↦ (hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩
      (Path.Homotopic.Quotient.mk q)).unop) (fun _ ↦ q) (fun _ ↦ rfl) ()

public theorem abelianCoverHomologyEquiv_basepoint
    {E X G : Type} [TopologicalSpace E] [TopologicalSpace X]
    [CommGroup G] [MulAction G E] [SimplyConnectedSpace E] [PathConnectedSpace X]
    {p : C(E, X)} (hp : IsQuotientCoveringMap p G) (e f : E) :
    abelianCoverHomologyEquiv hp e = abelianCoverHomologyEquiv hp f := by
  ext g
  let L := PathConnectedSpace.somePath e f
  let W := L.map p.continuous
  let γ := (hp.fundamentalGroupEquiv ⟨e, rfl⟩).symm (MulOpposite.op g.toMul)
  have he : hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩ γ = MulOpposite.op g.toMul :=
    (hp.fundamentalGroupEquiv ⟨e, rfl⟩).apply_symm_apply _
  have hm : hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk W) ⟨e, rfl⟩ =
      ⟨f, rfl⟩ := hp.isCoveringMap.monodromy_map (Path.Homotopic.Quotient.mk L)
  have hf := fundamentalGroupToMulOpposite_transport_endpoint hp W ⟨e, rfl⟩ γ
  rw [hm, he] at hf
  have h₀ := abelianCoverHomologyEquiv_hurewicz hp e γ
  have h₁ := abelianCoverHomologyEquiv_hurewicz hp f
    (FundamentalGroup.fundamentalGroupMulEquivOfPath W γ)
  rw [he] at h₀
  rw [hf] at h₁
  exact h₀.trans ((hurewiczFunction_basePath W γ).symm.trans h₁.symm)

public theorem abelianCoverHomologyEquiv_of_lift
    {E X G : Type} [TopologicalSpace E] [TopologicalSpace X]
    [CommGroup G] [MulAction G E] [SimplyConnectedSpace E] [PathConnectedSpace X]
    {p : C(E, X)} (hp : IsQuotientCoveringMap p G) (e₀ e : E) (g : G)
    (q : Path (p e) (p e)) (L : Path e (g • e))
    (hL : ∀ t, p (L t) = q t) :
    abelianCoverHomologyEquiv hp e₀ (Additive.ofMul g) = loopHomologyClass q := by
  rw [abelianCoverHomologyEquiv_basepoint hp e₀ e]
  have hm := hp.isCoveringMap.monodromy_eq_of_map_eq
    (ex := ⟨e, rfl⟩) (ey := ⟨g • e, hp.map_smul g⟩)
    (Path.Homotopic.Quotient.mk L) (γ := Path.Homotopic.Quotient.mk q)
    (by
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      exact hL t)
  have hd : hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩
      (Path.Homotopic.Quotient.mk q) = MulOpposite.op g := by
    apply hp.fundamentalGroupToMulOpposite_apply_eq_Iff.mpr
    exact (congrArg Subtype.val hm).symm
  have h := abelianCoverHomologyEquiv_hurewicz hp e (Path.Homotopic.Quotient.mk q)
  rw [hd] at h
  exact h

end SphereSixComplex.Topology

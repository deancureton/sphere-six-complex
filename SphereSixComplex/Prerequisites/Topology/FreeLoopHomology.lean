module

public import SphereSixComplex.Prerequisites.Topology.HurewiczBasepointTransport
public import Mathlib.Topology.Homotopy.Path
public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph

/-! # First homology of freely homotopic loops -/

@[expose] public section
noncomputable section
open SphereSixComplex SphereSixComplex.Hurewicz.Chains
open SphereSixComplex.StandardCircleHomologyLiftDegree
open AlgebraicTopology CategoryTheory
namespace SphereSixComplex

theorem loopHomologyClass_eq_of_freeHomotopy
    {X : Type} [TopologicalSpace X] {x y : X}
    (p : Path x x) (q : Path y y)
    (H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap)
    (h : ∀ s : unitInterval, H (s, 0) = H (s, 1)) :
    loopHomologyClass p = loopHomologyClass q := by
  let W : Path x y := (H.evalAt 0).cast p.source.symm q.source.symm
  have ht : (H.evalAt 1).cast p.target.symm q.target.symm = W := by
    ext s
    exact (h s).symm
  have hp := (Path.Homotopic.map_trans_evalAt H Path.id).pathCast p.source.symm q.target.symm
  have hl : (((Path.id.map p.continuous).trans (H.evalAt 1)).cast
      p.source.symm q.target.symm) = p.trans W := by
    rw [← ht]
    rfl
  have hr : (((H.evalAt 0).trans (Path.id.map q.continuous)).cast
      p.source.symm q.target.symm) = W.trans q := rfl
  rw [hl, hr] at hp
  have hc := pathOpchainClass_homotopic hp
  rw [pathOpchainClass_trans, pathOpchainClass_trans] at hc
  have hc' : pathOpchainClass p = pathOpchainClass q := by
    exact add_right_cancel ((hc.trans (add_comm _ _)))
  apply (AddCommGrpCat.mono_iff_injective ((integralChains X).homologyι 1)).mp
    (inferInstance : Mono ((integralChains X).homologyι 1))
  simpa only [homologyι_loopHomologyClass] using hc'

theorem loopHomologyClass_eq_of_toContinuousMap_eq
    {X : Type} [TopologicalSpace X] {x y : X}
    (p : Path x x) (q : Path y y)
    (h : p.toContinuousMap = q.toContinuousMap) :
    loopHomologyClass p = loopHomologyClass q := by
  have hb : x = y := by
    simpa using congrArg (fun f : C(unitInterval, X) ↦ f 0) h
  subst y
  have hp : p = q := by
    apply Path.ext
    funext t
    exact congrArg (fun f : C(unitInterval, X) ↦ f t) h
  exact congrArg loopHomologyClass hp

namespace Hurewicz.Chains

theorem hurewiczFunction_homeomorphMulEquivOfEq
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {x : X} {y : Y} (h : e x = y) (g : FundamentalGroup X x) :
    hurewiczFunction y (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq e h g) =
      integralSingularHomologyMap 1 ⟨e, e.continuous⟩ (hurewiczFunction x g) := by
  subst y
  rw [TauCeti.FundamentalGroup.homeomorphMulEquivOfEq_apply,
    TauCeti.FundamentalGroup.mapOfEq_rfl]
  exact hurewiczFunction_map ⟨e, e.continuous⟩ x g

end Hurewicz.Chains
end SphereSixComplex
end

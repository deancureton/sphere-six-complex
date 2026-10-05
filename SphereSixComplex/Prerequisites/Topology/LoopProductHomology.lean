module

public import SphereSixComplex.Prerequisites.Topology.FreeLoopProductHomotopy
public import SphereSixComplex.Prerequisites.Topology.FreeLoopHomology
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

@[expose] public section
noncomputable section
open SphereSixComplex.Hurewicz.Chains
open SphereSixComplex.StandardCircleHomologyLiftDegree
open scoped ContinuousMap

namespace SphereSixComplex

theorem loopHomologyClass_prod_map
    {B T Y : Type} [TopologicalSpace B] [TopologicalSpace T] [TopologicalSpace Y]
    {b : B} {t : T} (p : Path b b) (q : Path t t) (f : C(B × T, Y)) :
    loopHomologyClass ((p.prod q).map f.continuous) =
      loopHomologyClass (((Path.refl b).prod q).map f.continuous) +
        loopHomologyClass ((p.prod (Path.refl t)).map f.continuous) := by
  obtain ⟨H⟩ := Topology.productLoop_map_homotopic_fiberThenBase p q f
  simpa only [Path.map_trans, loopHomologyClass_trans] using loopHomologyClass_homotopic H

theorem loopHomologyClass_prod_map_of_lift
    {B V T Y : Type} [TopologicalSpace B] [TopologicalSpace V]
    [TopologicalSpace T] [TopologicalSpace Y] [SimplyConnectedSpace V]
    {b : B} {v w : V} (p : Path b b) (l s : Path v w)
    (q : C(V, T)) (h : q v = q w) (f : C(B × T, Y)) :
    loopHomologyClass ((p.prod ((l.map q.continuous).cast rfl h)).map f.continuous) =
      loopHomologyClass (((Path.refl b).prod
        ((s.map q.continuous).cast rfl h)).map f.continuous) +
        loopHomologyClass ((p.prod (Path.refl (q v))).map f.continuous) := by
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic l s
  have H' := Path.Homotopic.prodHomotopy (Path.Homotopy.refl p)
    ((H.map q).pathCast rfl h)
  exact (loopHomologyClass_homotopic (H'.map f)).trans
    (loopHomologyClass_prod_map p _ f)

end SphereSixComplex

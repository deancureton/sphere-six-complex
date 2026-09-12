module

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Topology.Path

@[expose] public section
open CategoryTheory

namespace ContinuousMap

public def homotopyOfLoop {X G : Type} [TopologicalSpace X]
    [TopologicalSpace G] [One G] (a : ContinuousMap (G × X) X)
    (ha : ∀ x, a (1, x) = x) (c : Path (1 : G) 1) :
    TopCat.Homotopy (𝟙 (TopCat.of X)) (𝟙 (TopCat.of X)) where
  toFun p := a (c p.1, p.2)
  continuous_toFun := a.continuous.comp ((c.continuous.comp continuous_fst).prodMk continuous_snd)
  map_zero_left x := by
    change a (c 0, x) = x
    rw [c.source]
    exact ha x
  map_one_left x := by
    change a (c 1, x) = x
    rw [c.target]
    exact ha x

end ContinuousMap

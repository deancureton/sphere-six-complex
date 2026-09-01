module

public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeGeometricRelatorRepresentativeProof

@[expose] public section

noncomputable section

open scoped ContinuousMap

namespace SphereSixComplex.Topology

/-- Forget the endpoint-relative conditions of a path homotopy. -/
public def pathHomotopyToFreeHomotopy
    {X : Type*} [TopologicalSpace X] {x : X}
    {p q : Path x x} (H : Path.Homotopy p q) :
    ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap where
  toFun := H
  continuous_toFun := H.continuous
  map_zero_left t := H.map_zero_left t
  map_one_left t := H.map_one_left t

/-- A free homotopy obtained from an endpoint-relative loop homotopy has equal endpoint traces. -/
public theorem pathHomotopyToFreeHomotopy_trace
    {X : Type*} [TopologicalSpace X] {x : X}
    {p q : Path x x} (H : Path.Homotopy p q) :
    ((pathHomotopyToFreeHomotopy H).evalAt 0).cast p.source.symm q.source.symm =
      ((pathHomotopyToFreeHomotopy H).evalAt 1).cast p.target.symm q.target.symm := by
  apply Path.ext
  funext s
  exact (H.source s).trans (H.target s).symm

/-- A loop in a product is based-homotopic to its fibre coordinate followed by its base
coordinate.  This formulation fixes both endpoints throughout the homotopy, so its two endpoint
traces agree automatically after applying any continuous map. -/
public theorem productLoop_homotopic_fiberThenBase
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (p : Path x x) (q : Path y y) :
    Nonempty (Path.Homotopy (p.prod q)
      (((Path.refl x).prod q).trans (p.prod (Path.refl y)))) := by
  apply Path.Homotopic.Quotient.exact
  simp only [Path.Homotopic.Quotient.mk_trans]
  simp only [← Path.Homotopic.prod_lift]
  rw [Path.Homotopic.comp_prod_eq_prod_comp]
  rw [Path.Homotopic.Quotient.mk_refl,
    Path.Homotopic.Quotient.refl_trans,
    Path.Homotopic.Quotient.mk_refl,
    Path.Homotopic.Quotient.trans_refl]

/-- The product splitting remains a based homotopy after applying any continuous realization
map. -/
public theorem productLoop_map_homotopic_fiberThenBase
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {x : X} {y : Y} (p : Path x x) (q : Path y y) (f : C(X × Y, Z)) :
    Nonempty (Path.Homotopy ((p.prod q).map f.continuous)
      ((((Path.refl x).prod q).trans (p.prod (Path.refl y))).map f.continuous)) := by
  rcases productLoop_homotopic_fiberThenBase p q with ⟨H⟩
  exact ⟨H.map f⟩

end SphereSixComplex.Topology

end

end

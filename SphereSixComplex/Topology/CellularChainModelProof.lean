module

public import SphereSixComplex.Topology.CellularChainModel
public import SphereSixComplex.Topology.SingularHomologyDegreeZero

/-!
# Why the cellular chain model needs a Hausdorff hypothesis

`EstablishedCellularHomology.integralCWCellularChainModel` says that a Hausdorff `Y : Type`
carrying `Topology.CWComplex (Set.univ : Set Y)` admits an integral cellular chain model: a chain
complex whose degree-`n` term is free on the `n`-cells, together with a quasi-isomorphism to
singular chains.  This file is the regression test pinning down why the `[T2Space Y]` hypothesis
cannot be dropped.

Mathlib's `Topology.CWComplex` class carries **no separation hypothesis** — every lemma about it
that needs Hausdorffness (`isClosed_closedCell`, `skeletonLT`, ...) takes `[T2Space X]` as a
separate assumption.  So without `[T2Space Y]` the statement is not merely unproved, it is false.

`IndiscretePair` is the two-point set with the indiscrete topology.  All of its subsets other than
`∅` and `univ` fail to be closed, so the weak-topology axiom `closed'` is satisfied *vacuously* by
the two singletons, and `instCWComplex` equips it with a CW structure having two zero-cells and no
cells in positive dimension; it is even finite (`Topology.CWComplex.Finite`).  On the other hand
the space is path-connected — every function into an indiscrete space is continuous — so its
degree-zero integral singular homology is `ℤ`, not `ℤ²`.

`isEmpty_integralCWCellularChainModel_indiscretePair` turns this into a contradiction, and
`isEmpty_forall_integralCWCellularChainModel` states that the `T2Space`-free form of the axiom is
uninhabited.  `not_t2Space` records that `IndiscretePair` is exactly what the repaired hypothesis
excludes.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Set

namespace SphereSixComplex

/-- The two-point set, to be equipped with the indiscrete topology. -/
public def IndiscretePair : Type := Bool

namespace IndiscretePair

public instance : TopologicalSpace IndiscretePair := ⊤

public instance : IndiscreteTopology IndiscretePair := ⟨rfl⟩

/-- The two points. -/
public def pt (b : Bool) : IndiscretePair := b

public theorem eq_pt (x : IndiscretePair) : x = pt true ∨ x = pt false := by
  match x with
  | true => exact Or.inl rfl
  | false => exact Or.inr rfl

public theorem ball_fin_zero : ball (0 : Fin 0 → ℝ) 1 = (univ : Set (Fin 0 → ℝ)) := by
  ext x
  have hx : x = 0 := funext fun i => i.elim0
  simp [hx]

public theorem closedBall_fin_zero :
    closedBall (0 : Fin 0 → ℝ) 1 = (univ : Set (Fin 0 → ℝ)) := by
  ext x
  have hx : x = 0 := funext fun i => i.elim0
  simp [hx]

public theorem sphere_fin_zero : sphere (0 : Fin 0 → ℝ) 1 = (∅ : Set (Fin 0 → ℝ)) := by
  ext x
  have hx : x = 0 := funext fun i => i.elim0
  simp only [mem_sphere, hx, dist_self, mem_empty_iff_false, iff_false]
  exact zero_ne_one

/-- The indexing types of the cells: two zero-cells and nothing else. -/
public def cellIdx : ℕ → Type
  | 0 => Bool
  | _ + 1 => Empty

public instance instIsEmptyCellIdxSucc (n : ℕ) : IsEmpty (cellIdx (n + 1)) :=
  inferInstanceAs (IsEmpty Empty)

/-- The characteristic map of a zero-cell. -/
public def pointPartialEquiv (b : Bool) : PartialEquiv (Fin 0 → ℝ) IndiscretePair where
  toFun _ := pt b
  invFun _ := 0
  source := ball 0 1
  target := {pt b}
  map_source' _ _ := rfl
  map_target' _ _ := mem_ball_self one_pos
  left_inv' _ _ := (funext fun i => i.elim0).symm
  right_inv' _ hy := hy.symm

/-- The characteristic maps of the cell structure. -/
public def cwMap : (n : ℕ) → cellIdx n → PartialEquiv (Fin n → ℝ) IndiscretePair
  | 0, b => pointPartialEquiv b
  | _ + 1, i => i.elim

public theorem cwMap_image_ball (b : Bool) :
    cwMap 0 b '' ball 0 1 = {pt b} := by
  rw [ball_fin_zero]
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩; rfl
  · rintro rfl; exact ⟨0, mem_univ _, rfl⟩

public theorem cwMap_image_closedBall (b : Bool) :
    cwMap 0 b '' closedBall 0 1 = {pt b} := by
  rw [closedBall_fin_zero]
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩; rfl
  · rintro rfl; exact ⟨0, mem_univ _, rfl⟩

public theorem not_isClosed_singleton (b : Bool) :
    ¬ IsClosed ({pt b} : Set IndiscretePair) := by
  rw [IndiscreteTopology.isClosed_iff]
  rintro (h | h)
  · have hb : pt b ∈ ({pt b} : Set IndiscretePair) := rfl
    rw [h] at hb
    exact hb
  · have hb : pt (!b) ∈ ({pt b} : Set IndiscretePair) := h ▸ mem_univ _
    exact Bool.not_ne_self b hb

/-- `IndiscretePair` is not Hausdorff.  This is precisely the hypothesis that
`EstablishedCellularHomology.integralCWCellularChainModel` adds to exclude it. -/
public theorem not_t2Space : ¬ T2Space IndiscretePair := by
  intro _h
  exact not_isClosed_singleton true isClosed_singleton

/-- The two-point indiscrete space is a CW complex in the sense of `Topology.CWComplex`, with
two zero-cells and no cells of positive dimension. -/
public instance instCWComplex : Topology.CWComplex (univ : Set IndiscretePair) where
  cell := cellIdx
  map := cwMap
  source_eq n i := by
    match n, i with
    | 0, _ => rfl
  continuousOn n i := by
    match n, i with
    | 0, _ => exact continuousOn_const
  continuousOn_symm n i := by
    match n, i with
    | 0, _ => exact continuousOn_const
  pairwiseDisjoint' := by
    rintro ⟨n, i⟩ - ⟨m, j⟩ - hne
    match n, i, m, j with
    | 0, i, 0, j =>
      have hij : i ≠ j := fun h => hne (by subst h; rfl)
      simp only [Function.onFun]
      rw [Set.disjoint_left]
      rintro x ⟨a, -, rfl⟩ ⟨a', -, ha'⟩
      exact hij ha'.symm
    | 0, _, _ + 1, j => exact j.elim
    | _ + 1, i, _, _ => exact i.elim
  mapsTo' n i := by
    match n, i with
    | 0, _ =>
      refine ⟨fun _ => ∅, ?_⟩
      rw [sphere_fin_zero]
      exact Set.mapsTo_empty _ _
  closed' A _ h := by
    have key : ∀ b : Bool, pt b ∉ A := by
      intro b hb
      have hcl : IsClosed (A ∩ cwMap 0 b '' closedBall 0 1) := h 0 b
      rw [cwMap_image_closedBall] at hcl
      have hEq : A ∩ ({pt b} : Set IndiscretePair) = {pt b} := by
        ext y
        exact ⟨fun hy => hy.2, fun hy => ⟨by rwa [show y = pt b from hy], hy⟩⟩
      rw [hEq] at hcl
      exact not_isClosed_singleton b hcl
    have hA : A = ∅ := by
      ext x
      simp only [mem_empty_iff_false, iff_false]
      rcases eq_pt x with rfl | rfl
      · exact key true
      · exact key false
    rw [hA]
    exact isClosed_empty
  union' := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    rcases eq_pt x with rfl | rfl
    · exact ⟨0, true, 0, mem_closedBall_self zero_le_one, rfl⟩
    · exact ⟨0, false, 0, mem_closedBall_self zero_le_one, rfl⟩

public instance : PathConnectedSpace IndiscretePair where
  nonempty := ⟨pt true⟩
  joined x y := ⟨{
    toFun := fun t => if (t : ℝ) = 0 then x else y
    continuous_toFun := continuous_of_indiscreteTopology
    source' := by norm_num
    target' := by norm_num }⟩

public instance instIsEmptyCell (n : ℕ) :
    IsEmpty (Topology.CWComplex.cell (univ : Set IndiscretePair) (n + 1)) :=
  inferInstanceAs (IsEmpty Empty)

public theorem cell_zero_eq : Topology.CWComplex.cell (univ : Set IndiscretePair) 0 = Bool := rfl

public instance : Topology.CWComplex.FiniteType (univ : Set IndiscretePair) where
  finite_cell n := by
    match n with
    | 0 => exact inferInstanceAs (Finite Bool)
    | _ + 1 => exact inferInstanceAs (Finite Empty)

public instance : Topology.CWComplex.FiniteDimensional (univ : Set IndiscretePair) where
  eventually_isEmpty_cell := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    match n, hn with
    | _ + 1, _ => exact inferInstanceAs (IsEmpty Empty)

public instance : Topology.CWComplex.Finite (univ : Set IndiscretePair) :=
  Topology.CWComplex.finite_of_finiteDimensional_finiteType _

end IndiscretePair

/-- There is no cellular chain model for the two-point indiscrete space: its cell structure has
two zero-cells and no other cells, so any such model would force `ℤ² ≃+ ℤ`, whereas the space is
path-connected and hence has `H₀ ≅ ℤ`. -/
public theorem isEmpty_integralCWCellularChainModel_indiscretePair :
    IsEmpty (IntegralCWCellularChainModel IndiscretePair) := by
  constructor
  intro M
  have hz : IsZero (M.chainComplex.X 1) :=
    isZero_cellularChain_of_isEmpty_cell IndiscretePair M 1
  have hd1 : M.chainComplex.d 1 0 = 0 := hz.eq_of_src _ _
  have _hiso : IsIso (M.chainComplex.homologyMap M.comparison 0) := M.comparison_homology_isIso 0
  let eX : M.chainComplex.X 0 ≅ M.chainComplex.homology 0 :=
    M.chainComplex.pOpcyclesIso 1 0 (by simp) hd1 ≪≫ M.chainComplex.isoHomologyι₀.symm
  let eH : M.chainComplex.homology 0 ≅ (IntegralSingularChainComplex IndiscretePair).homology 0 :=
    asIso (M.chainComplex.homologyMap M.comparison 0)
  have _hSing : IsIso ((TopCat.of IndiscretePair).singularHomology₀ε (AddCommGrpCat.of ℤ)) :=
    inferInstance
  let eS := asIso ((TopCat.of IndiscretePair).singularHomology₀ε (AddCommGrpCat.of ℤ))
  have f : (Bool →₀ ℤ) ≃+ ℤ :=
    (M.cellBasis 0).trans (eX.trans (eH.trans eS)).addCommGroupIsoToAddEquiv
  have hrank : Module.finrank ℤ (Bool →₀ ℤ) = Module.finrank ℤ ℤ :=
    (f.toIntLinearEquiv).finrank_eq
  rw [Module.finrank_self, (Finsupp.linearEquivFunOnFinite ℤ ℤ Bool).finrank_eq,
    Module.finrank_fintype_fun_eq_card] at hrank
  simp at hrank

/-- Dropping `[T2Space Y]` from `EstablishedCellularHomology.integralCWCellularChainModel` makes it
false: `Topology.CWComplex` carries no separation hypothesis, so the two-point indiscrete space is
a finite CW complex with two zero-cells while having the integral singular homology of a point.

This is a permanent regression test.  If the `[T2Space Y]` binder is ever removed from that axiom,
its type becomes the one shown here and `IsEmpty` says it has no inhabitant at all. -/
public theorem isEmpty_forall_integralCWCellularChainModel :
    IsEmpty (∀ (Y : Type) [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)],
      IntegralCWCellularChainModel Y) :=
  ⟨fun h => isEmpty_integralCWCellularChainModel_indiscretePair.elim (h IndiscretePair)⟩

end SphereSixComplex

end

end

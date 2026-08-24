/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Topology.StandardSphere
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import Mathlib.Topology.CWComplex.Classical.Finite

/-!
# A finite classical CW model for the six-sphere

The one-point compactification of `Fin 6 → ℝ` has one zero-cell at infinity and one
six-cell. The open characteristic map is the inverse of the standard homeomorphism from
Euclidean space to its open unit ball. On the boundary of the closed ball it is extended by
the point at infinity.
-/

@[expose] public section

open Filter Function Metric Set Topology
open scoped OnePoint Topology

noncomputable section

namespace SphereSixComplex

private abbrev SixVector := Fin 6 → ℝ

/-- The carrier of the explicit finite CW model for the standard six-sphere. -/
public abbrev SixSphereFiniteCWCarrier := OnePoint (Fin 6 → ℝ)

private abbrev OnePointSix := SixSphereFiniteCWCarrier

private noncomputable def openUnitBall : OpenPartialHomeomorph SixVector SixVector :=
  OpenPartialHomeomorph.univUnitBall

private theorem openUnitBall_source : openUnitBall.source = Set.univ := by
  rfl

private theorem openUnitBall_target :
    openUnitBall.target = Metric.ball (0 : SixVector) 1 := by
  rfl

private noncomputable def coeOpenPartialHomeomorph :
    OpenPartialHomeomorph SixVector OnePointSix :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph
    ((↑) : SixVector → OnePointSix)

/-- The open six-cell, before extending its characteristic map across the boundary. -/
private noncomputable def openTopCell :
    OpenPartialHomeomorph SixVector OnePointSix :=
  openUnitBall.symm.trans' coeOpenPartialHomeomorph (by
    change Set.univ = Set.univ
    rfl)

private theorem openTopCell_source :
    openTopCell.source = Metric.ball (0 : SixVector) 1 := by
  rfl

private theorem openTopCell_apply (x : SixVector) :
    openTopCell x = (↑(openUnitBall.symm x) : OnePointSix) := by
  rfl

private theorem openTopCell_ne_infty (x : SixVector) : openTopCell x ≠ ∞ := by
  rw [openTopCell_apply]
  exact OnePoint.coe_ne_infty _

/-- Extend the open top-cell chart by infinity away from the open unit ball. -/
private noncomputable def topCellValue (x : SixVector) : OnePointSix :=
  by
    classical
    exact if x ∈ Metric.ball (0 : SixVector) 1 then openTopCell x else ∞

/-- The partial equivalence underlying the six-dimensional characteristic map. -/
private noncomputable def topCellCharacteristic :
    PartialEquiv SixVector OnePointSix where
  toFun := topCellValue
  invFun := openTopCell.symm
  source := Metric.ball (0 : SixVector) 1
  target := openTopCell.target
  map_source' x hx := by
    rw [topCellValue, if_pos hx]
    exact openTopCell.map_source (openTopCell_source.symm ▸ hx)
  map_target' x hx := by
    exact openTopCell_source ▸ openTopCell.map_target hx
  left_inv' x hx := by
    rw [topCellValue, if_pos hx]
    exact openTopCell.left_inv (openTopCell_source.symm ▸ hx)
  right_inv' x hx := by
    have hsource : openTopCell.symm x ∈ Metric.ball (0 : SixVector) 1 :=
      openTopCell_source ▸ openTopCell.map_target hx
    rw [topCellValue, if_pos hsource]
    exact openTopCell.right_inv hx

private theorem topCellCharacteristic_source :
    topCellCharacteristic.source = Metric.ball (0 : SixVector) 1 := by
  rfl

private theorem topCellCharacteristic_continuousOn_symm :
    ContinuousOn topCellCharacteristic.symm topCellCharacteristic.target := by
  exact openTopCell.continuousOn_symm

/-- The extended top characteristic map is continuous on the closed unit ball.

At a boundary point, compact subsets of `SixVector` are sent by `openUnitBall` to compact
subsets of the open ball. Their complements are therefore neighbourhoods of the boundary
point, which is exactly the neighbourhood criterion at infinity in `OnePoint SixVector`. -/
private theorem topCellCharacteristic_continuousOn :
    ContinuousOn topCellCharacteristic (Metric.closedBall (0 : SixVector) 1) := by
  intro x hxClosed
  by_cases hxBall : x ∈ Metric.ball (0 : SixVector) 1
  · have hOpen : ContinuousAt openTopCell x :=
      openTopCell.continuousAt (openTopCell_source.symm ▸ hxBall)
    refine hOpen.continuousWithinAt.congr_of_eventuallyEq_of_mem ?_ hxClosed
    filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hxBall)] with y hy
    simp [topCellCharacteristic, topCellValue, hy]
  · have hValue : topCellCharacteristic x = (∞ : OnePointSix) := by
      simp [topCellCharacteristic, topCellValue, hxBall]
    rw [ContinuousWithinAt, hValue]
    refine (OnePoint.hasBasis_nhds_infty (X := SixVector)).tendsto_right_iff.2 ?_
    rintro K ⟨_, hKCompact⟩
    have hImageCompact : IsCompact (openUnitBall '' K) :=
      hKCompact.image_of_continuousOn
        (openUnitBall.continuousOn.mono fun y _ ↦ by
          rw [openUnitBall_source]
          exact Set.mem_univ y)
    have hxImage : x ∉ openUnitBall '' K := by
      rintro ⟨y, _, rfl⟩
      apply hxBall
      exact openUnitBall_target ▸ openUnitBall.map_source
        (openUnitBall_source.symm ▸ Set.mem_univ y)
    have hAvoid :
        (openUnitBall '' K)ᶜ ∈ 𝓝[Metric.closedBall (0 : SixVector) 1] x :=
      mem_nhdsWithin_of_mem_nhds
        (hImageCompact.isClosed.isOpen_compl.mem_nhds hxImage)
    filter_upwards [hAvoid] with y hyAvoid
    by_cases hyBall : y ∈ Metric.ball (0 : SixVector) 1
    · left
      refine ⟨openUnitBall.symm y, ?_, ?_⟩
      · change openUnitBall.symm y ∉ K
        intro hyK
        exact hyAvoid ⟨openUnitBall.symm y, hyK,
          openUnitBall.right_inv (openUnitBall_target.symm ▸ hyBall)⟩
      · simp [topCellCharacteristic, topCellValue, hyBall, openTopCell_apply]
    · right
      simp [topCellCharacteristic, topCellValue, hyBall]

private theorem topCellCharacteristic_image_ball :
    topCellCharacteristic '' Metric.ball (0 : SixVector) 1 =
      topCellCharacteristic.target := by
  rw [← topCellCharacteristic_source]
  exact topCellCharacteristic.image_source_eq_target

private def boundaryPoint : SixVector := fun _ ↦ 1

private theorem boundaryPoint_norm : ‖boundaryPoint‖ = 1 := by
  change ‖(1 : SixVector)‖ = 1
  exact norm_one

/-- The closed top cell covers the one-point compactification. -/
private theorem topCellCharacteristic_image_closedBall :
    topCellCharacteristic '' Metric.closedBall (0 : SixVector) 1 = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro p
  refine OnePoint.rec ?_ (fun y ↦ ?_) p
  · refine ⟨boundaryPoint, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, boundaryPoint_norm]
    · have hBoundary : boundaryPoint ∉ Metric.ball (0 : SixVector) 1 := by
        rw [mem_ball_zero_iff, boundaryPoint_norm]
        exact lt_irrefl 1
      simp [topCellCharacteristic, topCellValue, hBoundary]
  · let z : SixVector := openUnitBall y
    have hySource : y ∈ openUnitBall.source :=
      openUnitBall_source.symm ▸ Set.mem_univ y
    have hzBall : z ∈ Metric.ball (0 : SixVector) 1 :=
      openUnitBall_target ▸ openUnitBall.map_source hySource
    refine ⟨z, Metric.ball_subset_closedBall hzBall, ?_⟩
    simp only [topCellCharacteristic, topCellValue, if_pos hzBall, openTopCell_apply]
    rw [show openUnitBall.symm z = y from openUnitBall.left_inv hySource]

/-- The unique zero-cell, placed at infinity. -/
private def zeroCellCharacteristic : PartialEquiv (Fin 0 → ℝ) OnePointSix :=
  PartialEquiv.single ![] ∞

private theorem zeroCellCharacteristic_source :
    zeroCellCharacteristic.source = Metric.ball (0 : Fin 0 → ℝ) 1 := by
  simp [zeroCellCharacteristic, Metric.ball, Matrix.empty_eq, Set.eq_univ_iff_forall]

private theorem zeroCellCharacteristic_continuousOn :
    ContinuousOn zeroCellCharacteristic (Metric.closedBall (0 : Fin 0 → ℝ) 1) := by
  change ContinuousOn (fun _ : Fin 0 → ℝ ↦ (∞ : OnePointSix)) _
  exact continuousOn_const

private theorem zeroCellCharacteristic_continuousOn_symm :
    ContinuousOn zeroCellCharacteristic.symm zeroCellCharacteristic.target := by
  change ContinuousOn (fun _ : OnePointSix ↦ (![] : Fin 0 → ℝ)) _
  exact continuousOn_const

private theorem disjoint_zero_top :
    Disjoint
      (zeroCellCharacteristic '' Metric.ball (0 : Fin 0 → ℝ) 1)
      (topCellCharacteristic '' Metric.ball (0 : SixVector) 1) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, _, rfl⟩ ⟨y, hy, hxy⟩
  exact openTopCell_ne_infty y (by
    simpa [zeroCellCharacteristic, topCellCharacteristic, topCellValue, hy] using hxy)

/-- There is one cell in dimensions zero and six, and no cells in other dimensions. -/
private def onePointSixCell (n : ℕ) : Type := { _u : PUnit.{0} // n = 0 ∨ n = 6 }

private instance onePointSixCell_subsingleton (n : ℕ) : Subsingleton (onePointSixCell n) where
  allEq a b := Subtype.ext (Subsingleton.elim a.1 b.1)

private def zeroCellIndex : onePointSixCell 0 :=
  ⟨PUnit.unit, Or.inl rfl⟩

private def topCellIndex : onePointSixCell 6 :=
  ⟨PUnit.unit, Or.inr rfl⟩

private noncomputable def onePointSixCellMap
    (n : ℕ) (i : onePointSixCell n) : PartialEquiv (Fin n → ℝ) OnePointSix := by
  by_cases hn : n = 0
  · subst n
    exact zeroCellCharacteristic
  · have hnSix : n = 6 := i.property.resolve_left hn
    subst n
    exact topCellCharacteristic

@[simp]
private theorem onePointSixCellMap_zero (i : onePointSixCell 0) :
    onePointSixCellMap 0 i = zeroCellCharacteristic := by
  simp [onePointSixCellMap]

@[simp]
private theorem onePointSixCellMap_six (i : onePointSixCell 6) :
    onePointSixCellMap 6 i = topCellCharacteristic := by
  simp [onePointSixCellMap]

private theorem onePointSixCell_eventuallyEmpty :
    ∀ᶠ n in Filter.atTop, IsEmpty (onePointSixCell n) := by
  refine Filter.eventually_atTop.2 ⟨7, fun n hn ↦ ?_⟩
  exact ⟨fun i ↦ by rcases i.property with h | h <;> omega⟩

private theorem onePointSixCell_finite (n : ℕ) : Finite (onePointSixCell n) :=
  inferInstance

private theorem onePointSixCellMap_source (n : ℕ) (i : onePointSixCell n) :
    (onePointSixCellMap n i).source = Metric.ball (0 : Fin n → ℝ) 1 := by
  rcases i.property with h | h
  · subst n
    simpa [onePointSixCellMap] using zeroCellCharacteristic_source
  · subst n
    simpa [onePointSixCellMap] using topCellCharacteristic_source

private theorem onePointSixCellMap_continuousOn (n : ℕ) (i : onePointSixCell n) :
    ContinuousOn (onePointSixCellMap n i) (Metric.closedBall (0 : Fin n → ℝ) 1) := by
  rcases i.property with h | h
  · subst n
    simpa [onePointSixCellMap] using zeroCellCharacteristic_continuousOn
  · subst n
    simpa [onePointSixCellMap] using topCellCharacteristic_continuousOn

private theorem onePointSixCellMap_continuousOn_symm (n : ℕ) (i : onePointSixCell n) :
    ContinuousOn (onePointSixCellMap n i).symm (onePointSixCellMap n i).target := by
  rcases i.property with h | h
  · subst n
    simpa [onePointSixCellMap] using zeroCellCharacteristic_continuousOn_symm
  · subst n
    simpa [onePointSixCellMap] using topCellCharacteristic_continuousOn_symm

private theorem onePointSixCellMap_pairwiseDisjoint :
    (Set.univ : Set (Σ n, onePointSixCell n)).PairwiseDisjoint
      (fun ni ↦ onePointSixCellMap ni.1 ni.2 ''
        Metric.ball (0 : Fin ni.1 → ℝ) 1) := by
  simp only [Set.PairwiseDisjoint, Set.pairwise_univ]
  rintro ⟨n, i⟩ ⟨m, j⟩ hne
  rcases i.property with hn | hn <;> rcases j.property with hm | hm
  · subst n
    subst m
    have hij : i = j := Subsingleton.elim _ _
    subst j
    exact (hne rfl).elim
  · subst n
    subst m
    change Disjoint
      (onePointSixCellMap 0 i '' Metric.ball (0 : Fin 0 → ℝ) 1)
      (onePointSixCellMap 6 j '' Metric.ball (0 : Fin 6 → ℝ) 1)
    simpa only [onePointSixCellMap_zero, onePointSixCellMap_six] using disjoint_zero_top
  · subst n
    subst m
    change Disjoint
      (onePointSixCellMap 6 i '' Metric.ball (0 : Fin 6 → ℝ) 1)
      (onePointSixCellMap 0 j '' Metric.ball (0 : Fin 0 → ℝ) 1)
    simpa only [onePointSixCellMap_zero, onePointSixCellMap_six] using disjoint_zero_top.symm
  · subst n
    subst m
    have hij : i = j := Subsingleton.elim _ _
    subst j
    exact (hne rfl).elim

private theorem onePointSixCellMap_mapsTo (n : ℕ) (i : onePointSixCell n) :
    MapsTo (onePointSixCellMap n i) (Metric.sphere (0 : Fin n → ℝ) 1)
      (⋃ (m < n) (j : onePointSixCell m),
        onePointSixCellMap m j '' Metric.closedBall (0 : Fin m → ℝ) 1) := by
  rcases i.property with hn | hn
  · subst n
    simp [onePointSixCellMap, Matrix.zero_empty, sphere_eq_empty_of_subsingleton]
  · subst n
    intro x hxSphere
    have hxNorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hxSphere
    have hxBall : x ∉ Metric.ball (0 : SixVector) 1 := by
      rw [mem_ball_zero_iff, hxNorm]
      exact lt_irrefl 1
    have hxValue : onePointSixCellMap 6 i x = (∞ : OnePointSix) := by
      simp [onePointSixCellMap, topCellCharacteristic, topCellValue, hxBall]
    rw [hxValue]
    refine Set.mem_iUnion.2 ⟨0, ?_⟩
    refine Set.mem_iUnion.2 ⟨by omega, ?_⟩
    refine Set.mem_iUnion.2 ⟨zeroCellIndex, ?_⟩
    refine ⟨(0 : Fin 0 → ℝ), by simp, ?_⟩
    simp [onePointSixCellMap, zeroCellCharacteristic]

private theorem onePointSixCellMap_union :
    (⋃ (n : ℕ) (j : onePointSixCell n),
      onePointSixCellMap n j '' Metric.closedBall (0 : Fin n → ℝ) 1) =
        (Set.univ : Set OnePointSix) := by
  rw [Set.eq_univ_iff_forall]
  intro p
  refine Set.mem_iUnion.2 ⟨6, ?_⟩
  refine Set.mem_iUnion.2 ⟨topCellIndex, ?_⟩
  have hp : p ∈ topCellCharacteristic '' Metric.closedBall (0 : SixVector) 1 := by
    rw [topCellCharacteristic_image_closedBall]
    exact Set.mem_univ p
  simpa [onePointSixCellMap] using hp

/-- A finite CW structure packaged together with its finiteness certificate. -/
public structure SixSphereFiniteCWModel where
  complex : Topology.CWComplex (Set.univ : Set SixSphereFiniteCWCarrier)
  finite :
    letI := complex
    Topology.CWComplex.Finite (Set.univ : Set SixSphereFiniteCWCarrier)

/-- The explicit finite two-cell CW structure on the one-point compactification of `ℝ⁶`. -/
public noncomputable opaque sixSphereFiniteCWModel : SixSphereFiniteCWModel := {
  complex := Topology.CWComplex.mkFinite
    (Set.univ : Set OnePointSix)
    (cell := onePointSixCell)
    (map := onePointSixCellMap)
    (eventually_isEmpty_cell := onePointSixCell_eventuallyEmpty)
    (finite_cell := onePointSixCell_finite)
    (source_eq := onePointSixCellMap_source)
    (continuousOn := onePointSixCellMap_continuousOn)
    (continuousOn_symm := onePointSixCellMap_continuousOn_symm)
    (pairwiseDisjoint' := onePointSixCellMap_pairwiseDisjoint)
    (mapsTo_iff_image_subset := onePointSixCellMap_mapsTo)
    (union' := onePointSixCellMap_union)
  finite := Topology.CWComplex.finite_mkFinite
    (Set.univ : Set OnePointSix)
    onePointSixCell
    onePointSixCellMap
    onePointSixCell_eventuallyEmpty
    onePointSixCell_finite
    onePointSixCellMap_source
    onePointSixCellMap_continuousOn
    onePointSixCellMap_continuousOn_symm
    onePointSixCellMap_pairwiseDisjoint
    onePointSixCellMap_mapsTo
    onePointSixCellMap_union }

/-- The finite CW structure carried by `sixSphereFiniteCWModel`. -/
@[instance_reducible]
public noncomputable def sixSphereFiniteCWComplex :
    Topology.CWComplex (Set.univ : Set SixSphereFiniteCWCarrier) :=
  sixSphereFiniteCWModel.complex

/-- The explicit CW structure on the model carrier is finite. -/
public theorem sixSphereFiniteCWComplex_finite :
    letI : Topology.CWComplex (Set.univ : Set SixSphereFiniteCWCarrier) :=
      sixSphereFiniteCWComplex
    Topology.CWComplex.Finite (Set.univ : Set SixSphereFiniteCWCarrier) :=
  sixSphereFiniteCWModel.finite

/-- The standard identification of the finite CW model with the standard six-sphere. -/
public noncomputable opaque sixSphereFiniteCWHomeomorph :
    SixSphereFiniteCWCarrier ≃ₜ SixSphere :=
  onePointEquivSphereOfFinrankEq (V := SixVector) (ι := Fin 7) (by simp)

end SphereSixComplex

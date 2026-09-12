module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CorrectedLaurentIdentity

@[expose] public section

noncomputable section

open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

namespace Construction

public def planeCorrection (v : ToricLattice) : Fin 2 → ℝ :=
  correctedPlaneCenter v - fun k ↦ (v k : ℝ)

public theorem planeCorrection_add_mem_iff
    (v : ToricLattice) (x : Fin 2 → ℝ) :
    planeCorrection v + x ∈ correctedPlaneCell v ↔
      x ∈ planeCell v := by
  simp only [correctedPlaneCell, planeCell, Set.mem_ofPred_eq]
  have hcoordinate (k : Fin 2) :
      (planeCorrection v + x) k - correctedPlaneCenter v k =
        x k - (v k : ℝ) := by
    simp only [planeCorrection, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hcoordinate, hcoordinate]
  rw [show ((planeCorrection v + x) 0 -
          (planeCorrection v + x) 1) -
          (correctedPlaneCenter v 0 -
            correctedPlaneCenter v 1) =
        ((planeCorrection v + x) 0 -
          correctedPlaneCenter v 0) -
          ((planeCorrection v + x) 1 -
            correctedPlaneCenter v 1) by ring,
      hcoordinate, hcoordinate]
  ring_nf

public noncomputable def planeCellCorrectionHomeomorph (v : ToricLattice) :
    planeCell v ≃ₜ correctedPlaneCell v where
  toFun x := ⟨planeCorrection v + x.1,
    (planeCorrection_add_mem_iff v x.1).mpr x.2⟩
  invFun y := ⟨y.1 - planeCorrection v,
    (planeCorrection_add_mem_iff v _).mp (by
      convert y.2 using 1
      ext k
      simp only [Pi.add_apply, Pi.sub_apply]
      ring)⟩
  left_inv x := by
    apply Subtype.ext
    ext k
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  right_inv y := by
    apply Subtype.ext
    ext k
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  continuous_toFun :=
    (continuous_const.add continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.sub continuous_const).subtype_mk _

public def correctedPlaneSquareProjection (v : ToricLattice) :
    Fin 6 × CellSquare → correctedPlaneCell v :=
  fun a ↦ ⟨correctedPlaneTile v a.1 a.2,
    correctedPlaneTile_mem v a.1 a.2⟩

public theorem correctedPlaneSquareProjection_eq
    (v : ToricLattice) (a : Fin 6 × CellSquare) :
    correctedPlaneSquareProjection v a =
      planeCellCorrectionHomeomorph v
        (planeSquareProjection v a) := by
  rfl

public theorem continuous_correctedPlaneSquareProjection
    (v : ToricLattice) :
    Continuous (correctedPlaneSquareProjection v) := by
  apply Continuous.subtype_mk
  change Continuous (fun a : Fin 6 × CellSquare ↦
    planeCorrection v + planeTile v a.1 a.2)
  exact continuous_const.add
    (continuous_prod_of_discrete_left.mpr (continuous_planeTile v))

public theorem surjective_correctedPlaneSquareProjection
    (v : ToricLattice) :
    Function.Surjective (correctedPlaneSquareProjection v) := by
  intro x
  obtain ⟨a, ha⟩ := surjective_planeSquareProjection v
    ((planeCellCorrectionHomeomorph v).symm x)
  refine ⟨a, ?_⟩
  rw [correctedPlaneSquareProjection_eq, ha]
  exact (planeCellCorrectionHomeomorph v).apply_symm_apply x

public theorem isQuotientMap_correctedPlaneSquareProjection
    (v : ToricLattice) :
    Topology.IsQuotientMap (correctedPlaneSquareProjection v) :=
  Topology.IsQuotientMap.of_surjective_continuous
    (surjective_correctedPlaneSquareProjection v)
    (continuous_correctedPlaneSquareProjection v)

public noncomputable def correctedFiniteQuotientCellHomeomorph
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) :
    correctedPlaneCell v ≃ₜ constructedPositiveCentralCell r v :=
  _root_.Topology.IsQuotientMap.homeomorphOfSameFibers
    (isQuotientMap_correctedPlaneSquareProjection v)
    (isQuotientMap_cellSquareProjection hr v)
    (fun a b ↦ by
      rcases a with ⟨i, p⟩
      rcases b with ⟨j, q⟩
      simpa only [correctedPlaneSquareProjection, Subtype.ext_iff] using
        correctedPlaneTile_eq_iff_cellSquareProjection hr v v i j p q)

public theorem correctedFiniteQuotientCellHomeomorph_apply
    {r : ℝ} (hr : 0 < r) (v : ToricLattice)
    (a : Fin 6 × CellSquare) :
    correctedFiniteQuotientCellHomeomorph hr v
        (correctedPlaneSquareProjection v a) =
      cellSquareProjection hr v a :=
  _root_.Topology.IsQuotientMap.homeomorphOfSameFibers_apply
    (isQuotientMap_correctedPlaneSquareProjection v)
    (isQuotientMap_cellSquareProjection hr v)
    (fun x y ↦ by
      rcases x with ⟨i, p⟩
      rcases y with ⟨j, q⟩
      simpa only [correctedPlaneSquareProjection, Subtype.ext_iff] using
        correctedPlaneTile_eq_iff_cellSquareProjection hr v v i j p q) a

public theorem correctedFiniteQuotientCellHomeomorph_compatible
    {r : ℝ} (hr : 0 < r) (v w : ToricLattice)
    (x : correctedPlaneCell v)
    (y : correctedPlaneCell w) :
    (x : Fin 2 → ℝ) = (y : Fin 2 → ℝ) ↔
      ((correctedFiniteQuotientCellHomeomorph hr v x :
          constructedPositiveCentralCell r v) : constructedPositiveCentralFiber r) =
        correctedFiniteQuotientCellHomeomorph hr w y := by
  obtain ⟨a, rfl⟩ := surjective_correctedPlaneSquareProjection v x
  obtain ⟨b, rfl⟩ := surjective_correctedPlaneSquareProjection w y
  rw [correctedFiniteQuotientCellHomeomorph_apply hr,
    correctedFiniteQuotientCellHomeomorph_apply hr]
  rcases a with ⟨i, p⟩
  rcases b with ⟨j, q⟩
  simpa only [correctedPlaneSquareProjection] using
    correctedPlaneTile_eq_iff_cellSquareProjection hr v w i j p q

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end

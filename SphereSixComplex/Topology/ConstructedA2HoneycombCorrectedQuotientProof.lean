module

public import SphereSixComplex.Topology.ConstructedA2HoneycombCorrectedGlobalProof

@[expose] public section

noncomputable section

open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

public def constructedA2PlaneCorrection (v : ToricLattice) : Fin 2 → ℝ :=
  constructedA2CorrectedPlaneCenter v - fun k ↦ (v k : ℝ)

public theorem constructedA2PlaneCorrection_add_mem_iff
    (v : ToricLattice) (x : Fin 2 → ℝ) :
    constructedA2PlaneCorrection v + x ∈ constructedA2CorrectedPlaneCell v ↔
      x ∈ constructedA2PlaneCell v := by
  simp only [constructedA2CorrectedPlaneCell, constructedA2PlaneCell, Set.mem_ofPred_eq]
  have hcoordinate (k : Fin 2) :
      (constructedA2PlaneCorrection v + x) k - constructedA2CorrectedPlaneCenter v k =
        x k - (v k : ℝ) := by
    simp only [constructedA2PlaneCorrection, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hcoordinate, hcoordinate]
  rw [show ((constructedA2PlaneCorrection v + x) 0 -
          (constructedA2PlaneCorrection v + x) 1) -
          (constructedA2CorrectedPlaneCenter v 0 -
            constructedA2CorrectedPlaneCenter v 1) =
        ((constructedA2PlaneCorrection v + x) 0 -
          constructedA2CorrectedPlaneCenter v 0) -
          ((constructedA2PlaneCorrection v + x) 1 -
            constructedA2CorrectedPlaneCenter v 1) by ring,
      hcoordinate, hcoordinate]
  ring_nf

public noncomputable def constructedA2PlaneCellCorrectionHomeomorph (v : ToricLattice) :
    constructedA2PlaneCell v ≃ₜ constructedA2CorrectedPlaneCell v where
  toFun x := ⟨constructedA2PlaneCorrection v + x.1,
    (constructedA2PlaneCorrection_add_mem_iff v x.1).mpr x.2⟩
  invFun y := ⟨y.1 - constructedA2PlaneCorrection v,
    (constructedA2PlaneCorrection_add_mem_iff v _).mp (by
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

public def constructedA2CorrectedPlaneSquareProjection (v : ToricLattice) :
    Fin 6 × ConstructedA2CellSquare → constructedA2CorrectedPlaneCell v :=
  fun a ↦ ⟨constructedA2CorrectedPlaneTile v a.1 a.2,
    constructedA2CorrectedPlaneTile_mem v a.1 a.2⟩

public theorem constructedA2CorrectedPlaneSquareProjection_eq
    (v : ToricLattice) (a : Fin 6 × ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneSquareProjection v a =
      constructedA2PlaneCellCorrectionHomeomorph v
        (constructedA2PlaneSquareProjection v a) := by
  rfl

public theorem constructedA2CorrectedPlaneSquareProjection_continuous
    (v : ToricLattice) :
    Continuous (constructedA2CorrectedPlaneSquareProjection v) := by
  apply Continuous.subtype_mk
  change Continuous (fun a : Fin 6 × ConstructedA2CellSquare ↦
    constructedA2PlaneCorrection v + constructedA2PlaneTile v a.1 a.2)
  exact continuous_const.add
    (continuous_prod_of_discrete_left.mpr (constructedA2PlaneTile_continuous v))

public theorem constructedA2CorrectedPlaneSquareProjection_surjective
    (v : ToricLattice) :
    Function.Surjective (constructedA2CorrectedPlaneSquareProjection v) := by
  intro x
  obtain ⟨a, ha⟩ := constructedA2PlaneSquareProjection_surjective v
    ((constructedA2PlaneCellCorrectionHomeomorph v).symm x)
  refine ⟨a, ?_⟩
  rw [constructedA2CorrectedPlaneSquareProjection_eq, ha]
  exact (constructedA2PlaneCellCorrectionHomeomorph v).apply_symm_apply x

public theorem constructedA2CorrectedPlaneSquareProjection_isQuotientMap
    (v : ToricLattice) :
    Topology.IsQuotientMap (constructedA2CorrectedPlaneSquareProjection v) :=
  Topology.IsQuotientMap.of_surjective_continuous
    (constructedA2CorrectedPlaneSquareProjection_surjective v)
    (constructedA2CorrectedPlaneSquareProjection_continuous v)

public noncomputable def constructedA2CorrectedFiniteQuotientCellHomeomorph
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) :
    constructedA2CorrectedPlaneCell v ≃ₜ constructedPositiveCentralCell r v :=
  constructedA2HomeomorphOfQuotientMaps
    (constructedA2CorrectedPlaneSquareProjection_isQuotientMap v)
    (constructedA2CellSquareProjection_isQuotientMap hr v)
    (fun a b ↦ by
      rcases a with ⟨i, p⟩
      rcases b with ⟨j, q⟩
      simpa only [constructedA2CorrectedPlaneSquareProjection, Subtype.ext_iff] using
        constructedA2CorrectedPlaneTile_eq_iff_cellSquareProjection hr v v i j p q)

public theorem constructedA2CorrectedFiniteQuotientCellHomeomorph_apply
    {r : ℝ} (hr : 0 < r) (v : ToricLattice)
    (a : Fin 6 × ConstructedA2CellSquare) :
    constructedA2CorrectedFiniteQuotientCellHomeomorph hr v
        (constructedA2CorrectedPlaneSquareProjection v a) =
      constructedA2CellSquareProjection hr v a :=
  constructedA2HomeomorphOfQuotientMaps_apply
    (constructedA2CorrectedPlaneSquareProjection_isQuotientMap v)
    (constructedA2CellSquareProjection_isQuotientMap hr v)
    (fun x y ↦ by
      rcases x with ⟨i, p⟩
      rcases y with ⟨j, q⟩
      simpa only [constructedA2CorrectedPlaneSquareProjection, Subtype.ext_iff] using
        constructedA2CorrectedPlaneTile_eq_iff_cellSquareProjection hr v v i j p q) a

public theorem constructedA2CorrectedFiniteQuotientCellHomeomorph_compatible
    {r : ℝ} (hr : 0 < r) (v w : ToricLattice)
    (x : constructedA2CorrectedPlaneCell v)
    (y : constructedA2CorrectedPlaneCell w) :
    (x : Fin 2 → ℝ) = (y : Fin 2 → ℝ) ↔
      ((constructedA2CorrectedFiniteQuotientCellHomeomorph hr v x :
          constructedPositiveCentralCell r v) : constructedPositiveCentralFiber r) =
        constructedA2CorrectedFiniteQuotientCellHomeomorph hr w y := by
  obtain ⟨a, rfl⟩ := constructedA2CorrectedPlaneSquareProjection_surjective v x
  obtain ⟨b, rfl⟩ := constructedA2CorrectedPlaneSquareProjection_surjective w y
  rw [constructedA2CorrectedFiniteQuotientCellHomeomorph_apply hr,
    constructedA2CorrectedFiniteQuotientCellHomeomorph_apply hr]
  rcases a with ⟨i, p⟩
  rcases b with ⟨j, q⟩
  simpa only [constructedA2CorrectedPlaneSquareProjection] using
    constructedA2CorrectedPlaneTile_eq_iff_cellSquareProjection hr v w i j p q

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end

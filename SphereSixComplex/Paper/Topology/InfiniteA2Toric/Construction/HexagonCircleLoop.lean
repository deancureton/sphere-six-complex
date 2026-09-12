module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.HexagonRadialBoundary
public import SphereSixComplex.Prerequisites.Topology.PathOpchainSubdivision

@[expose] public section
noncomputable section
open Set Topology CategoryTheory
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex Hurewicz.Chains
open SphereSixComplex.StandardCircleHomologyLiftDegree

namespace Construction

public theorem hexagonBoundaryLoop_opchain_eq_circle :
    pathOpchainClass (hexagonBoundaryLoop.map
      hexagonBoundaryToPunctured.continuous) =
    pathOpchainClass ((Path.segment (0 : ℝ) 1).map
      (planeCirclePuncturedPoint (2 / 3) (by norm_num)).continuous) := by
  have h₀ := pathOpchainClass_homotopic (hexagonPuncturedQuarterPath_homotopic 0)
  have h₁ := pathOpchainClass_homotopic (hexagonPuncturedQuarterPath_homotopic 1)
  have h₂ := pathOpchainClass_homotopic (hexagonPuncturedQuarterPath_homotopic 2)
  have h₃ := pathOpchainClass_homotopic (hexagonPuncturedQuarterPath_homotopic 3)
  have h₀' := (pathOpchainClass_map_trans hexagonBoundaryToPunctured
    (hexagonBoundarySidePath 0) (hexagonBoundarySidePath 1)).symm.trans h₀
  have h₂' := (pathOpchainClass_map_trans hexagonBoundaryToPunctured
    (hexagonBoundarySidePath 3) (hexagonBoundarySidePath 4)).symm.trans h₂
  have hs := pathOpchainClass_map_six hexagonBoundaryToPunctured
    (hexagonBoundarySidePath 0) (hexagonBoundarySidePath 1)
    (hexagonBoundarySidePath 2) (hexagonBoundarySidePath 3)
    (hexagonBoundarySidePath 4) (hexagonBoundarySidePath 5)
  have hc := pathOpchainClass_map_segment_four
    (planeCirclePuncturedPoint (2 / 3) (by norm_num)) 0 (1 / 4) (1 / 2) (3 / 4) 1
  let s := fun i : Fin 6 ↦ pathOpchainClass ((hexagonBoundarySidePath i).map
    hexagonBoundaryToPunctured.continuous)
  let c := fun a b : ℝ ↦ pathOpchainClass ((Path.segment a b).map
    (planeCirclePuncturedPoint (2 / 3) (by norm_num)).continuous)
  change s 0 + s 1 = c (((0 : Fin 4) : ℝ) / 4) ((((0 : Fin 4) : ℝ) + 1) / 4) at h₀'
  change s 2 = c (((1 : Fin 4) : ℝ) / 4) ((((1 : Fin 4) : ℝ) + 1) / 4) at h₁
  change s 3 + s 4 = c (((2 : Fin 4) : ℝ) / 4) ((((2 : Fin 4) : ℝ) + 1) / 4) at h₂'
  change s 5 = c (((3 : Fin 4) : ℝ) / 4) ((((3 : Fin 4) : ℝ) + 1) / 4) at h₃
  norm_num at h₀' h₁ h₂' h₃
  have hsum : ((((s 0 + s 1) + s 2) + s 3) + s 4) + s 5 =
      ((c 0 (1 / 4) + c (1 / 4) (1 / 2)) + c (1 / 2) (3 / 4)) + c (3 / 4) 1 := by
    calc
      _ = (((s 0 + s 1) + s 2) + (s 3 + s 4)) + s 5 := by abel
      _ = _ := by rw [h₀', h₁, h₂', h₃]
  exact hs.trans (hsum.trans hc.symm)

end Construction

public theorem planeCirclePuncturedPoint_one (r : ℝ) (hr : r ≠ 0) :
    planeCirclePuncturedPoint r hr 1 = planeCirclePuncturedPoint r hr 0 := by
  apply Subtype.ext
  have h₀ := planeCirclePoint_quarter r 0
  have h₄ := planeCirclePoint_quarter r 4
  norm_num at h₀ h₄
  exact h₄.trans h₀.symm

public def planeCirclePuncturedLoop (r : ℝ) (hr : r ≠ 0) :
    Path (planeCirclePuncturedPoint r hr 0) (planeCirclePuncturedPoint r hr 0) :=
  ((Path.segment (0 : ℝ) 1).map (planeCirclePuncturedPoint r hr).continuous).cast
    rfl (planeCirclePuncturedPoint_one r hr).symm

namespace Construction

public theorem hexagonBoundaryLoop_homology_eq_circle :
    loopHomologyClass (hexagonBoundaryLoop.map
      hexagonBoundaryToPunctured.continuous) =
      loopHomologyClass (planeCirclePuncturedLoop (2 / 3) (by norm_num)) := by
  apply (AddCommGrpCat.mono_iff_injective ((integralChains PuncturedRealPlane).homologyι 1)).mp
    (inferInstance : Mono ((integralChains PuncturedRealPlane).homologyι 1))
  calc
    _ = pathOpchainClass (hexagonBoundaryLoop.map
      hexagonBoundaryToPunctured.continuous) := homologyι_loopHomologyClass _
    _ = pathOpchainClass (planeCirclePuncturedLoop (2 / 3) (by norm_num)) :=
      hexagonBoundaryLoop_opchain_eq_circle
    _ = _ := (homologyι_loopHomologyClass _).symm

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

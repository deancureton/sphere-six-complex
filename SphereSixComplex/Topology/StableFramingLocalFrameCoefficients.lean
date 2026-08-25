module

public import SphereSixComplex.Topology.StableFramingHomotopySixSphereClutching
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth coefficients in a smooth local frame

The coefficient functions of a smooth section in an arbitrary smooth finite local frame are
smooth.  The proof trivializes the bundle near each point, packages the frame vectors as an
invertible continuous linear map, and differentiates its inverse.
-/

@[expose] public section

noncomputable section

open Bundle ContinuousMap Module
open scoped Bundle Classical ContDiff Manifold

namespace SphereSixComplex

section GenericLocalFrame

variable
    {𝕜 E H M F ι : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {n : ℕ∞ω} [IsManifold I n M]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)]
    [FiberBundle F V] [VectorBundle 𝕜 F V]
    [ContMDiffVectorBundle n F V I]
    [Fintype ι]

private def localFrameCoordinateMap
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    (s : ι → (x : M) → V x) (y : M) : (ι → 𝕜) →L[𝕜] F :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (e ((T% (s i)) y)).2

set_option linter.unusedSectionVars false in
private theorem localFrameCoordinateMap_apply
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    (s : ι → (x : M) → V x) (y : M) (c : ι → 𝕜) :
    localFrameCoordinateMap e s y c =
      ∑ i, c i • (e ((T% (s i)) y)).2 := by
  simp [localFrameCoordinateMap]

set_option linter.unusedSectionVars false in
private theorem localFrameCoordinateMap_contMDiffAt
    {u : Set M} {s : ι → (x : M) → V x}
    (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u)
    {x : M} (hx : x ∈ u)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] (hxe : x ∈ e.baseSet) :
    ContMDiffAt I 𝓘(𝕜, (ι → 𝕜) →L[𝕜] F) n
      (localFrameCoordinateMap (𝕜 := 𝕜) e s) x := by
  unfold localFrameCoordinateMap
  apply ContMDiffAt.sum
  intro i _
  apply ContDiff.comp_contMDiffAt
    (g := ContinuousLinearMap.smulRightL 𝕜 (ι → 𝕜) F
      (ContinuousLinearMap.proj i))
    (ContinuousLinearMap.contDiff _)
  simpa using
    (e.contMDiffAt_section_iff hxe).mp
      (hs.contMDiffAt hu hx i)

private def localFrameCoordinateEquivAt
    {u : Set M} {s : ι → (x : M) → V x}
    (hs : IsLocalFrameOn I F n s u) {x : M} (hx : x ∈ u)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] (hxe : x ∈ e.baseSet) :
    (ι → 𝕜) ≃L[𝕜] F :=
  ((hs.toBasisAt hx).equivFun.symm.trans
    (e.linearEquivAt 𝕜 x hxe)).toContinuousLinearEquiv

set_option linter.unusedSectionVars false in
private theorem localFrameCoordinateMap_eq_equivAt
    {u : Set M} {s : ι → (x : M) → V x}
    (hs : IsLocalFrameOn I F n s u) {x : M} (hx : x ∈ u)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] (hxe : x ∈ e.baseSet) :
    localFrameCoordinateMap (𝕜 := 𝕜) e s x =
      (localFrameCoordinateEquivAt hs hx e hxe : (ι → 𝕜) →L[𝕜] F) := by
  apply ContinuousLinearMap.ext
  intro c
  rw [localFrameCoordinateMap_apply]
  change
    (∑ i, c i • (e ((T% (s i)) x)).2) =
      e.linearEquivAt 𝕜 x hxe ((hs.toBasisAt hx).equivFun.symm c)
  rw [Basis.equivFun_symm_apply, map_sum]
  simp only [map_smul, hs.toBasisAt_coe hx]
  congr

/-- A coefficient of a smooth section in a smooth finite local frame is smooth at every point of
the frame domain. -/
public theorem localFrame_coeff_contMDiffAt
    {u : Set M} {s : ι → (x : M) → V x}
    (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u)
    {x : M} (hx : x ∈ u) {t : (x : M) → V x}
    (ht : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (T% t) x)
    (i : ι) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) n (fun y ↦ hs.coeff i y (t y)) x := by
  let e := trivializationAt F V x
  let hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hA :
      ContMDiffAt I 𝓘(𝕜, (ι → 𝕜) →L[𝕜] F) n
        (localFrameCoordinateMap (𝕜 := 𝕜) e s) x :=
    localFrameCoordinateMap_contMDiffAt hs hu hx e hxe
  have hAinv : (localFrameCoordinateMap (𝕜 := 𝕜) e s x).IsInvertible := by
    rw [localFrameCoordinateMap_eq_equivAt hs hx e hxe]
    exact ContinuousLinearMap.isInvertible_equiv
  have hInv :
      ContMDiffAt I 𝓘(𝕜, F →L[𝕜] (ι → 𝕜)) n
        (ContinuousLinearMap.inverse ∘
          localFrameCoordinateMap (𝕜 := 𝕜) e s) x :=
    hAinv.contDiffAt_map_inverse.comp_contMDiffAt hA
  have htCoord :
      ContMDiffAt I 𝓘(𝕜, F) n (fun y ↦ (e ((T% t) y)).2) x := by
    simpa using (e.contMDiffAt_section_iff hxe).mp ht
  have hCoeffVec :
      ContMDiffAt I 𝓘(𝕜, ι → 𝕜) n
        (fun y ↦ ContinuousLinearMap.inverse
          (localFrameCoordinateMap (𝕜 := 𝕜) e s y)
          (e ((T% t) y)).2) x :=
    hInv.clm_apply htCoord
  have hCoeff :
      ContMDiffAt I 𝓘(𝕜, 𝕜) n
        ((ContinuousLinearMap.proj i) ∘
          (fun y ↦ ContinuousLinearMap.inverse
            (localFrameCoordinateMap (𝕜 := 𝕜) e s y)
            (e ((T% t) y)).2)) x :=
    (ContinuousLinearMap.proj i).contDiff.comp_contMDiffAt hCoeffVec
  apply hCoeff.congr_of_eventuallyEq
  filter_upwards
    [Filter.inter_mem (hu.mem_nhds hx) (e.open_baseSet.mem_nhds hxe)] with y hy
  have hyu : y ∈ u := hy.1
  have hye : y ∈ e.baseSet := hy.2
  simp only [Function.comp_apply, ContinuousLinearMap.proj_apply]
  rw [localFrameCoordinateMap_eq_equivAt hs hyu e hye]
  simp only [ContinuousLinearMap.inverse_equiv]
  rw [hs.coeff_apply_of_mem hyu]
  change
    (hs.toBasisAt hyu).repr (t y) i =
      ((localFrameCoordinateEquivAt hs hyu e hye).symm
        (e ((T% t) y)).2) i
  simp [localFrameCoordinateEquivAt, hye]

/-- A coefficient of a smooth section in a smooth finite local frame is smooth throughout the
frame domain. -/
public theorem localFrame_coeff_contMDiffOn
    {u : Set M} {s : ι → (x : M) → V x}
    (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u)
    {t : (x : M) → V x}
    (ht : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (T% t) u)
    (i : ι) :
    ContMDiffOn I 𝓘(𝕜, 𝕜) n (fun y ↦ hs.coeff i y (t y)) u := by
  intro x hx
  exact
    (localFrame_coeff_contMDiffAt hs hu hx
      ((ht x hx).contMDiffAt (hu.mem_nhds hx)) i).contMDiffWithinAt

end GenericLocalFrame

namespace SmoothRankSevenClutchingPresentationSix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace RealModel M]
  [IsManifold 𝓘(ℝ, RealModel) ∞ M]

/-- A scalar coefficient of the north-to-south transition, defined without pointwise overlap
membership proofs. -/
public noncomputable def coordinateTransitionCoeff
    (p : SmoothRankSevenClutchingPresentationSix M) (i j : Fin 7) (x : M) : ℝ :=
  (p.southFrame.mono
    (show p.north ∩ p.south ⊆ p.south from Set.inter_subset_right)).coeff j x
      (p.northSections i x)

/-- Each coordinate transition coefficient is smooth on the frame overlap. -/
public theorem contMDiffOn_coordinateTransitionCoeff
    (p : SmoothRankSevenClutchingPresentationSix M) (i j : Fin 7) :
    ContMDiffOn 𝓘(ℝ, RealModel) 𝓘(ℝ, ℝ) ∞
      (p.coordinateTransitionCoeff i j) (p.north ∩ p.south) := by
  apply localFrame_coeff_contMDiffOn
    (p.southFrame.mono
      (show p.north ∩ p.south ⊆ p.south from Set.inter_subset_right))
    (p.north_isOpen.inter p.south_isOpen)
    ((p.northFrame.contMDiffOn i).mono Set.inter_subset_left)

/-- On the overlap, the proof-independent coefficient agrees with the corresponding coefficient
of `coordinateTransition`. -/
public theorem coordinateTransition_apply_basis_eq_coeff
    (p : SmoothRankSevenClutchingPresentationSix M)
    (x : M) (hxN : x ∈ p.north) (hxS : x ∈ p.south)
    (i j : Fin 7) :
    p.coordinateTransition x hxN hxS ((Pi.basisFun ℝ (Fin 7)) i) j =
      p.coordinateTransitionCoeff i j x := by
  unfold coordinateTransitionCoeff
  rw [IsLocalFrameOn.coeff_apply_of_mem
    (hx := show x ∈ p.north ∩ p.south from ⟨hxN, hxS⟩)]
  simp [coordinateTransition, IsLocalFrameOn.toBasisAt]

end SmoothRankSevenClutchingPresentationSix

end SphereSixComplex

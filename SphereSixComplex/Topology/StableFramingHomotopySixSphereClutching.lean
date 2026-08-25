module

public import SphereSixComplex.Topology.StableFramingHomotopySixSphere
public import Mathlib.LinearAlgebra.StdBasis

/-!
# A clutching reduction for stable framings of homotopy six-spheres

This file isolates the classical rank-seven clutching calculation in a geometric form that can be
used by the smooth vector-bundle API currently present in Mathlib.

A `SmoothRankSevenClutchingPresentationSix` consists of two open sets covering a six-manifold and
a smooth local frame of `TM ⊕ ε¹` on each set.  On the overlap, the two bases determine a
canonical transition automorphism of `ℝ⁷`.  A `SmoothRankSevenClutchingExtensionSix` is a smooth
extension of this transition automorphism across the second patch.  Applying that extension as a
gauge transformation to the second frame makes the two frames agree on the overlap, and hence they
glue to a global stable frame.

For a hemispherical presentation, existence of the extension is exactly the concrete geometric
form of vanishing of the clutching class in `π₅(GL₇(ℝ))` (equivalently, after orthogonalization
and orientation, in `π₅(SO(7))`).  Mathlib does not currently supply the required Bott-periodicity
calculation or the smooth clutching classification, so that final existence statement remains a
named proposition rather than an axiom.
-/

@[expose] public section

noncomputable section

open Bundle ContinuousMap Module
open scoped Bundle Classical ContDiff Manifold

namespace SphereSixComplex

universe u

/-- The coordinate space in which the rank-seven transition functions are written. -/
public abbrev StableFrameCoordinatesSix := Fin 7 → ℝ

/-- The standard five-sphere which models the equator of a hemispherical six-sphere cover. -/
public abbrev StableClutchingEquatorFiveSphere : Type :=
  ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 6)) 1)

/-- Two smooth local stable frames on an open two-set cover.

The transition between `northSections` and `southSections` is the rank-seven clutching function.
No assertion about a preferred hemispherical cover is hidden in this definition. -/
public structure SmoothRankSevenClutchingPresentationSix
    (M : Type u) [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M] where
  north : Set M
  south : Set M
  north_isOpen : IsOpen north
  south_isOpen : IsOpen south
  cover : north ∪ south = Set.univ
  northSections : Fin 7 → (x : M) → StabilizedTangentFiberSix M x
  southSections : Fin 7 → (x : M) → StabilizedTangentFiberSix M x
  northFrame :
    IsLocalFrameOn 𝓘(ℝ, RealModel) (RealModel × ℝ) ∞ northSections north
  southFrame :
    IsLocalFrameOn 𝓘(ℝ, RealModel) (RealModel × ℝ) ∞ southSections south

namespace SmoothRankSevenClutchingPresentationSix

variable {M : Type u} [TopologicalSpace M] [ChartedSpace RealModel M]
  [IsManifold 𝓘(ℝ, RealModel) ∞ M]

/-- The coordinate transition from the north frame to the south frame at a point of the overlap.

Thus applying this map to north-frame coordinates and then interpreting the result in the south
frame gives the same vector in the stabilized tangent fiber. -/
public def coordinateTransition
    (p : SmoothRankSevenClutchingPresentationSix M) (x : M)
    (hxN : x ∈ p.north) (hxS : x ∈ p.south) :
    StableFrameCoordinatesSix ≃ₗ[ℝ] StableFrameCoordinatesSix :=
  (p.northFrame.toBasisAt hxN).equivFun.symm.trans
    (p.southFrame.toBasisAt hxS).equivFun

end SmoothRankSevenClutchingPresentationSix

/-- A smooth extension, across the south patch, of the rank-seven clutching transition.

The scalar coordinate functions are required to be smooth; this is precisely what is needed to
apply the gauge to a smooth local frame.  Values of `gauge` outside the south patch are junk.
For a genuine hemispherical presentation this is an explicit disk extension of the equatorial
transition map, and hence an explicit null-clutching witness. -/
public structure SmoothRankSevenClutchingExtensionSix
    {M : Type u} [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M]
    (p : SmoothRankSevenClutchingPresentationSix M) where
  gauge : (x : M) → StableFrameCoordinatesSix ≃ₗ[ℝ] StableFrameCoordinatesSix
  contMDiffOn_coeff (i j : Fin 7) :
    ContMDiffOn 𝓘(ℝ, RealModel) 𝓘(ℝ, ℝ) ∞
      (fun x ↦ gauge x ((Pi.basisFun ℝ (Fin 7)) i) j) p.south
  agrees_transition (x : M) (hxN : x ∈ p.north) (hxS : x ∈ p.south) :
    gauge x = p.coordinateTransition x hxN hxS

namespace SmoothRankSevenClutchingExtensionSix

variable {M : Type u} [TopologicalSpace M] [ChartedSpace RealModel M]
  [IsManifold 𝓘(ℝ, RealModel) ∞ M]
  {p : SmoothRankSevenClutchingPresentationSix M}

/-- Gauge-transform the south local frame using the extended transition. -/
public def adjustedSouthSections (c : SmoothRankSevenClutchingExtensionSix p) :
    Fin 7 → (x : M) → StabilizedTangentFiberSix M x :=
  fun i x ↦ ∑ j, (c.gauge x ((Pi.basisFun ℝ (Fin 7)) i)) j • p.southSections j x

/-- The gauge-transformed south sections are again a smooth local frame. -/
public theorem adjustedSouthFrame (c : SmoothRankSevenClutchingExtensionSix p) :
    IsLocalFrameOn 𝓘(ℝ, RealModel) (RealModel × ℝ) ∞
      c.adjustedSouthSections p.south := by
  refine
    { linearIndependent := ?_
      generating := ?_
      contMDiffOn := ?_ }
  · intro x hx
    let b : Basis (Fin 7) ℝ (StabilizedTangentFiberSix M x) :=
      (Pi.basisFun ℝ (Fin 7)).map
        ((c.gauge x).trans (p.southFrame.toBasisAt hx).equivFun.symm)
    have hb (i : Fin 7) : b i = c.adjustedSouthSections i x := by
      simp only [b, Basis.map_apply, LinearEquiv.trans_apply, Basis.equivFun_symm_apply,
        adjustedSouthSections, p.southFrame.toBasisAt_coe hx]
    have hfun : (b : Fin 7 → StabilizedTangentFiberSix M x) =
        fun i ↦ c.adjustedSouthSections i x := funext hb
    rw [← hfun]
    exact b.linearIndependent
  · intro x hx
    let b : Basis (Fin 7) ℝ (StabilizedTangentFiberSix M x) :=
      (Pi.basisFun ℝ (Fin 7)).map
        ((c.gauge x).trans (p.southFrame.toBasisAt hx).equivFun.symm)
    have hb (i : Fin 7) : b i = c.adjustedSouthSections i x := by
      simp only [b, Basis.map_apply, LinearEquiv.trans_apply, Basis.equivFun_symm_apply,
        adjustedSouthSections, p.southFrame.toBasisAt_coe hx]
    have hfun : (b : Fin 7 → StabilizedTangentFiberSix M x) =
        fun i ↦ c.adjustedSouthSections i x := funext hb
    rw [← hfun]
    exact b.span_eq.ge
  · intro i
    exact ContMDiffOn.sum_section fun j _ ↦
      (c.contMDiffOn_coeff i j).smul_section (p.southFrame.contMDiffOn j)

/-- On the overlap, the adjusted south frame agrees pointwise with the north frame. -/
public theorem adjustedSouthSections_eq_northSections
    (c : SmoothRankSevenClutchingExtensionSix p) (i : Fin 7) (x : M)
    (hxN : x ∈ p.north) (hxS : x ∈ p.south) :
    c.adjustedSouthSections i x = p.northSections i x := by
  rw [adjustedSouthSections, c.agrees_transition x hxN hxS]
  simp only [SmoothRankSevenClutchingPresentationSix.coordinateTransition,
    LinearEquiv.trans_apply, Basis.equivFun_apply]
  rw [← p.northFrame.toBasisAt_coe hxN]
  simp_rw [← p.southFrame.toBasisAt_coe hxS]
  rw [(p.southFrame.toBasisAt hxS).sum_repr]
  simp

/-- The global sections obtained by using the north frame on the north patch and the adjusted
south frame elsewhere. -/
public def gluedSections (c : SmoothRankSevenClutchingExtensionSix p) :
    Fin 7 → (x : M) → StabilizedTangentFiberSix M x :=
  fun i x ↦ if _hx : x ∈ p.north then p.northSections i x else c.adjustedSouthSections i x

/-- A smooth extension of the clutching transition glues the two local frames to a concrete
global stable framing. -/
public def toSmoothStableFraming (c : SmoothRankSevenClutchingExtensionSix p) :
    SmoothStableFramingSix (M := M) where
  sections := c.gluedSections
  isFrame := by
    refine
      { linearIndependent := ?_
        generating := ?_
        contMDiffOn := ?_ }
    · intro x _
      by_cases hxN : x ∈ p.north
      · simpa only [gluedSections, dif_pos hxN] using p.northFrame.linearIndependent hxN
      · have hxS : x ∈ p.south := by
          have hx : x ∈ p.north ∪ p.south := by rw [p.cover]; exact Set.mem_univ x
          exact hx.resolve_left hxN
        simpa only [gluedSections, dif_neg hxN] using c.adjustedSouthFrame.linearIndependent hxS
    · intro x _
      by_cases hxN : x ∈ p.north
      · simpa only [gluedSections, dif_pos hxN] using p.northFrame.generating hxN
      · have hxS : x ∈ p.south := by
          have hx : x ∈ p.north ∪ p.south := by rw [p.cover]; exact Set.mem_univ x
          exact hx.resolve_left hxN
        simpa only [gluedSections, dif_neg hxN] using c.adjustedSouthFrame.generating hxS
    · intro i
      have hN : ContMDiffOn 𝓘(ℝ, RealModel)
          (𝓘(ℝ, RealModel).prod 𝓘(ℝ, RealModel × ℝ)) ∞
          (fun x ↦ TotalSpace.mk' (RealModel × ℝ) x (c.gluedSections i x)) p.north :=
        (p.northFrame.contMDiffOn i).congr fun x hx ↦ by simp [gluedSections, hx]
      have hS : ContMDiffOn 𝓘(ℝ, RealModel)
          (𝓘(ℝ, RealModel).prod 𝓘(ℝ, RealModel × ℝ)) ∞
          (fun x ↦ TotalSpace.mk' (RealModel × ℝ) x (c.gluedSections i x)) p.south :=
        (c.adjustedSouthFrame.contMDiffOn i).congr fun x hxS ↦ by
          by_cases hxN : x ∈ p.north
          · simp only [gluedSections, dif_pos hxN]
            exact congrArg (TotalSpace.mk' (RealModel × ℝ) x)
              (c.adjustedSouthSections_eq_northSections i x hxN hxS).symm
          · simp [gluedSections, hxN]
      rw [← p.cover]
      exact hN.union_of_isOpen hS p.north_isOpen p.south_isOpen

end SmoothRankSevenClutchingExtensionSix

/-- The topological part of a hemispherical two-patch presentation.

Keeping this data separate from the local stable frames lets the standard stereographic cover be
constructed and tested independently of the bundle-theoretic clutching calculation.  For an
arbitrary homotopy sphere, existence of such a cover is the twisted-sphere/two-disk input. -/
public structure SmoothHemisphericalOpenCoverSix
    (M : Type u) [TopologicalSpace M] where
  north : Set M
  south : Set M
  north_isOpen : IsOpen north
  south_isOpen : IsOpen south
  cover : north ∪ south = Set.univ
  north_contractible : ContractibleSpace north
  south_contractible : ContractibleSpace south
  equatorMarking :
    {x : M // x ∈ north ∩ south} ≃ₕ StableClutchingEquatorFiveSphere

/-- A genuinely hemispherical form of the two-patch clutching presentation.

The two patches are contractible and their overlap is marked by the standard five-sphere.  This
extra topology prevents the clutching obligation below from degenerating to the tautological cover
by two copies of `Set.univ`.  Producing such a presentation for an arbitrary smooth homotopy
six-sphere is the geometric (Morse-theoretic/twisted-sphere) part of a clutching proof. -/
public structure SmoothHemisphericalRankSevenClutchingPresentationSix
    (M : Type u) [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M] where
  toClutchingPresentation : SmoothRankSevenClutchingPresentationSix M
  north_contractible : ContractibleSpace toClutchingPresentation.north
  south_contractible : ContractibleSpace toClutchingPresentation.south
  equatorMarking :
    {x : M // x ∈ toClutchingPresentation.north ∩ toClutchingPresentation.south} ≃ₕ
      StableClutchingEquatorFiveSphere

namespace SmoothHemisphericalRankSevenClutchingPresentationSix

variable {M : Type u} [TopologicalSpace M] [ChartedSpace RealModel M]
  [IsManifold 𝓘(ℝ, RealModel) ∞ M]

/-- Forget the local stable frames while retaining the hemispherical open-cover geometry. -/
public def toOpenCover
    (p : SmoothHemisphericalRankSevenClutchingPresentationSix M) :
    SmoothHemisphericalOpenCoverSix M where
  north := p.toClutchingPresentation.north
  south := p.toClutchingPresentation.south
  north_isOpen := p.toClutchingPresentation.north_isOpen
  south_isOpen := p.toClutchingPresentation.south_isOpen
  cover := p.toClutchingPresentation.cover
  north_contractible := p.north_contractible
  south_contractible := p.south_contractible
  equatorMarking := p.equatorMarking

end SmoothHemisphericalRankSevenClutchingPresentationSix

/-- The precise hemispherical rank-seven clutching obligation.

It separates the remaining classical proof into (1) a two-disk presentation of a smooth homotopy
sphere and its stabilized tangent bundle and (2) extension of the resulting `GL₇(ℝ)` transition
over one disk.  The latter is the geometric content of the vanishing of its class in
`π₅(GL₇(ℝ))`, or in `π₅(SO(7))` after choosing a metric and orientation. -/
public def HomotopySixSphereHemisphericalRankSevenClutchingVanishing : Prop :=
  ∀ S : OrientedMarkedSmoothHomotopySixSphere.{0},
    ∃ p : SmoothHemisphericalRankSevenClutchingPresentationSix S.carrier,
      Nonempty (SmoothRankSevenClutchingExtensionSix p.toClutchingPresentation)

/-- The precise remaining rank-seven clutching obligation for marked homotopy six-spheres.

It asks for a two-patch stable tangent presentation together with an actual smooth extension of
its transition automorphism.  For hemispherical patches this is the geometric representative of
the statement `π₅(SO(7)) = 0`; no homotopy-group computation is postulated here. -/
public def HomotopySixSphereRankSevenClutchingExtension : Prop :=
  ∀ S : OrientedMarkedSmoothHomotopySixSphere.{0},
    ∃ p : SmoothRankSevenClutchingPresentationSix S.carrier,
      Nonempty (SmoothRankSevenClutchingExtensionSix p)

/-- Forgetting the hemispherical topology gives the bare extension obligation. -/
public theorem homotopySixSphereRankSevenClutchingExtension_of_hemispherical
    (h : HomotopySixSphereHemisphericalRankSevenClutchingVanishing) :
    HomotopySixSphereRankSevenClutchingExtension := by
  intro S
  obtain ⟨p, hc⟩ := h S
  exact ⟨p.toClutchingPresentation, hc⟩

/-- The rank-seven clutching extension obligation supplies the project's concrete stable framing
obligation. -/
public theorem homotopySixSpheresStablyParallelizable_of_rankSevenClutchingExtension
    (h : HomotopySixSphereRankSevenClutchingExtension) :
    HomotopySixSpheresStablyParallelizable := by
  intro S
  obtain ⟨p, ⟨c⟩⟩ := h S
  exact ⟨c.toSmoothStableFraming⟩

/-- The clutching extension also supplies the intrinsic smooth stabilized-tangent
trivialization used by the bundle-theoretic reduction. -/
public theorem homotopySixSphereStableTangentTriviality_of_rankSevenClutchingExtension
    (h : HomotopySixSphereRankSevenClutchingExtension) :
    HomotopySixSphereStableTangentTriviality :=
  homotopySixSphereStableTangentTriviality_iff_stablyParallelizable.mpr
    (homotopySixSpheresStablyParallelizable_of_rankSevenClutchingExtension h)

end SphereSixComplex

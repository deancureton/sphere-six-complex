module

public import SphereSixComplex.Paper.Geometry.CuspPeriodExpansion
public import SphereSixComplex.Paper.Geometry.GlobalTorusFamily

/-!
# The classical separated Fuchsian cusp neighbourhood: definitions

This module contains the data structures used to state the classical cusp-neighbourhood theorem.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.FuchsianCuspNeighborhood

open Set SphereSixComplex.TriangleGroup SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.GlobalTorusFamily

/-- The open source horodisc selected by the normalized coordinate and a strict `q`-radius. -/
public def normalizedCuspRegion
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (r : ℝ) : Set UpperHalfPlane :=
  N.lift '' {s : ℂ | s ∈ cuspHalfPlane N.height ∧ ‖cuspQ s‖ < r}

/-- Exact classical data for a sufficiently deep horodisc at the parabolic end. -/
public structure Data
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (upperRadius : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_le : radius ≤ cuspRadius N.height
  radius_le_upper : radius ≤ upperRadius
  region_open : IsOpen (normalizedCuspRegion N radius)
  region_regular : normalizedCuspRegion N radius ⊆
    {z | IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) z}
  orbitClosure_region_regular : closure (⋃ g : Delta,
      (fun z : UpperHalfPlane ↦
        E.modularParameter.toTriangleUniformization.sourceAction g • z) ''
          normalizedCuspRegion N radius) ⊆
    {z | IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) z}
  translates_meet_only_parabolic : ∀ g : Delta,
    ((fun z : UpperHalfPlane ↦
        E.modularParameter.toTriangleUniformization.sourceAction g • z) ''
        normalizedCuspRegion N radius ∩ normalizedCuspRegion N radius).Nonempty →
      ∃ k : ℤ, g = g₀ ^ k

/-- A compact set of source representatives for the complement of a selected normalized
horodisc. -/
public structure CompactTruncationData
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {upperRadius : ℝ}
    (H : Data N upperRadius) where
  core : Set UpperHalfPlane
  core_isCompact : IsCompact core
  orbit_covers : ∀ z : UpperHalfPlane, ∃ g : Delta,
    fuchsianSourceAction g • z ∈ normalizedCuspRegion N H.radius ∨
      fuchsianSourceAction g • z ∈ core

end SphereSixComplex.Geometry.FuchsianCuspNeighborhood

end

end

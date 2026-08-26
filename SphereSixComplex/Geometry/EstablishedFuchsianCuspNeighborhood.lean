module

public import SphereSixComplex.Geometry.CuspPeriodExpansion
public import SphereSixComplex.Geometry.GlobalTorusFamily

/-!
# The classical separated Fuchsian cusp neighbourhood

This module isolates the standard horodisc theorem for the normalized parabolic end of the
explicit Fuchsian triangle-group action.  It contains no toric, filling, quotient-embedding, or
collar conclusion.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.EstablishedFuchsianCuspNeighborhood

open Set SphereSixComplex.TriangleGroup SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.GlobalTorusFamily

/-- The open source horodisc selected by the normalized coordinate and a strict `q`-radius. -/
public def normalizedCuspRegion
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (r : ℝ) : Set UpperHalfPlane :=
  N.lift '' {s : ℂ | s ∈ cuspHalfPlane N.height ∧ ‖cuspQ s‖ < r}

/-- Exact classical data for a sufficiently deep horodisc at the parabolic end. -/
public structure Data
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
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

namespace Data

public theorem closure_region_regular
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {upperRadius : ℝ}
    (H : Data N upperRadius) : closure (normalizedCuspRegion N H.radius) ⊆
      {z | IsRegularBasePoint
        (U := E.modularParameter.toTriangleUniformization) z} := by
  have hsub : normalizedCuspRegion N H.radius ⊆ ⋃ g : Delta,
      (fun z : UpperHalfPlane ↦
        E.modularParameter.toTriangleUniformization.sourceAction g • z) ''
          normalizedCuspRegion N H.radius := by
    apply Set.subset_iUnion_of_subset (1 : Delta)
    intro z hz
    exact ⟨z, hz, by simp⟩
  intro z hz
  exact H.orbitClosure_region_regular (closure_mono hsub hz)

end Data

/-- A compact set of source representatives for the complement of a selected normalized
horodisc. -/
public structure CompactTruncationData
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {upperRadius : ℝ}
    (H : Data N upperRadius) where
  core : Set UpperHalfPlane
  core_isCompact : IsCompact core
  orbit_covers : ∀ z : UpperHalfPlane, ∃ g : Delta,
    fuchsianSourceAction g • z ∈ normalizedCuspRegion N H.radius ∨
      fuchsianSourceAction g • z ∈ core

namespace Established

/-- A sufficiently deep normalized horodisc is regular and precisely invariant under the
parabolic cyclic subgroup.  This is the standard cusp-neighbourhood theorem for a cofinite
Fuchsian group.
Reference: the standard cusp-neighbourhood theorem for a cofinite Fuchsian group -- a
sufficiently deep horodisc at a cusp is precisely invariant under the parabolic stabilizer.  This
is Shimizu's lemma together with the horocyclic neighbourhood construction; see [Bea83]. -/
public axiom data
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (upperRadius : ℝ)
    (hupper : 0 < upperRadius) : Nonempty (Data N upperRadius)

/-- Removing a precisely invariant horodisc from the explicit cofinite Fuchsian quotient leaves
a compact truncated quotient. 
Reference: a cofinite Fuchsian group has finite-area quotient which is compact after removing
finitely many precisely invariant horocyclic cusp neighbourhoods; see [Bea83, Chapter 10]. -/
public axiom compactTruncation
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {upperRadius : ℝ}
    (H : Data N upperRadius) : Nonempty (CompactTruncationData H)

end Established

end SphereSixComplex.Geometry.EstablishedFuchsianCuspNeighborhood

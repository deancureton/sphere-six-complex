module

public import SphereSixComplex.Periods.OrbifoldAffineTorsorLocalCechReduction

/-!
# Existence boundary for local orbifold affine-torsor Cech data

This file proves that the local Cech presentation isolated in
`OrbifoldAffineTorsorLocalCechReduction` is exactly the remaining analytic input.  A global
equivariant cusp-regular section gives a canonical local presentation on the finite chart and
the punctured infinity chart.  Conversely, the proved projective-line Cech vanishing glues any
local presentation to such a global section.

The final definition states the general classical affine-chart triviality theorem still absent
from Mathlib.  It is a proposition, not an axiom, and is quantified over every affine torsor on
the exact orbifold; acyclicity is needed only later, when the overlap cocycle is split.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open Set
open SphereSixComplex.TriangleGroup

namespace OrbifoldAffineLineTorsorDescentProblem

open HolomorphicAffineTorsorHOne

/-- The source preimage of the punctured infinity chart. -/
@[expose] public def canonicalInfinityRegion
    (P : OrbifoldAffineLineTorsorDescentProblem) : Set UpperHalfPlane :=
  {z | P.quotient.coordinate z ≠ 0}

public theorem canonicalInfinityRegion_open
    (P : OrbifoldAffineLineTorsorDescentProblem) :
    IsOpen P.canonicalInfinityRegion := by
  exact isOpen_compl_singleton.preimage P.quotient.coordinate_holomorphic.continuous

public theorem canonicalInfinityRegion_invariant
    (P : OrbifoldAffineLineTorsorDescentProblem) (g : Delta) (z : UpperHalfPlane) :
    fuchsianSourceAction g • z ∈ P.canonicalInfinityRegion ↔
      z ∈ P.canonicalInfinityRegion := by
  simp only [canonicalInfinityRegion, Set.mem_ofPred_eq]
  rw [P.quotient.coordinate_invariant]

/-- A global equivariant cusp-regular section restricts to a canonical local Cech
presentation.  Its overlap cocycle is zero because the same section is used on both charts. -/
@[expose] public def localCechPresentationOfEquivariantSection
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (s : UpperHalfPlane → ℂ) (hs : MDiff s)
    (hone : ∀ z, s (fuchsianSourceAction g₁ • z) = P.affineOne z (s z))
    (htwo : ∀ z, s (fuchsianSourceAction g₂ • z) = P.affineTwo z (s z))
    (hcusp : BoundedOn (fun z ↦ s z - P.cuspSection z) fuchsianCuspRegion) :
    P.LocalCechPresentation where
  zeroRegion := Set.univ
  infinityRegion := P.canonicalInfinityRegion
  zeroRegion_open := isOpen_univ
  infinityRegion_open := P.canonicalInfinityRegion_open
  regions_cover := Set.univ_union _
  zeroRegion_invariant := by simp
  infinityRegion_invariant := P.canonicalInfinityRegion_invariant
  sectionZero := s
  sectionInfinity := s
  sectionZero_holomorphic := fun z _ ↦ hs z
  sectionInfinity_holomorphic := fun z _ ↦ hs z
  sectionZero_one := fun z _ ↦ hone z
  sectionZero_two := fun z _ ↦ htwo z
  sectionInfinity_one := fun z _ ↦ hone z
  sectionInfinity_two := fun z _ ↦ htwo z
  overlapCocycle := fun _ ↦ 0
  overlapCocycle_holomorphic :=
    holomorphicOnPuncturedPlane_of_mdiff _ mdifferentiable_const
  infinity_coordinate_ne_zero := fun _ hz ↦ hz
  section_mismatch := by
    intro z _
    simp
  cusp_subset_infinity := fun z hz ↦ P.cusp_coordinate_ne_zero z hz
  sectionInfinity_sub_cusp_bounded := hcusp

/-- A global equivariant cusp-regular section yields local Cech data. -/
public theorem nonempty_localCechPresentation_of_hasCuspBoundedEquivariantSection
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (hP : P.HasCuspBoundedEquivariantSection) :
    Nonempty P.LocalCechPresentation := by
  obtain ⟨s, hs, hone, htwo, hcusp⟩ := hP
  exact ⟨P.localCechPresentationOfEquivariantSection s hs hone htwo hcusp⟩

/-- For either acyclic projective-line frame, local Cech existence is equivalent to the global
Cartan--B conclusion. -/
public theorem nonempty_localCechPresentation_iff_hasCuspBoundedEquivariantSection
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (frame : AcyclicProjectiveLineFrame)
    (hframe : P.frameTransition = frame.transition) :
    Nonempty P.LocalCechPresentation ↔ P.HasCuspBoundedEquivariantSection := by
  constructor
  · rintro ⟨D⟩
    obtain ⟨S⟩ :=
      (D.projectiveLineTorsor frame).nonempty_splitting_of_hOne_vanishes frame.hOne_vanishes
    exact D.hasCuspBoundedEquivariantSection frame hframe S
  · exact P.nonempty_localCechPresentation_of_hasCuspBoundedEquivariantSection

/-- The exact general classical theorem still needed: every holomorphic affine torsor on the
exact `(3, 4, ∞)` orbifold is trivial on the two affine quotient charts, with the supplied
completed-cusp primitive as its bounded normalization.

This is the local Cartan--B/finite-orbifold-descent/removable-singularity statement.  All Cech
splitting and gluing after this statement are already theorems. -/
@[expose] public def OrbifoldAffineTorsorChartTriviality : Prop :=
  ∀ P : OrbifoldAffineLineTorsorDescentProblem, Nonempty P.LocalCechPresentation

/-- The general local-triviality theorem specializes to any one descent problem. -/
public theorem nonempty_localCechPresentation_of_chartTriviality
    (hlocal : OrbifoldAffineTorsorChartTriviality)
    (P : OrbifoldAffineLineTorsorDescentProblem) :
    Nonempty P.LocalCechPresentation :=
  hlocal P

/-- The general local-triviality theorem and the proved projective-line `H¹` vanishing produce
the exact cusp-bounded Cousin correction used by the construction. -/
public theorem nonempty_cuspBoundedEllipticOneCorrection_of_chartTriviality
    (hlocal : OrbifoldAffineTorsorChartTriviality)
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (frame : AcyclicProjectiveLineFrame)
    (hframe : P.frameTransition = frame.transition) :
    Nonempty P.CuspBoundedEllipticOneCorrection := by
  obtain ⟨D⟩ := hlocal P
  exact P.nonempty_cuspBoundedEllipticOneCorrection_of_localCechPresentation D frame hframe

end OrbifoldAffineLineTorsorDescentProblem

end SphereSixComplex.Periods

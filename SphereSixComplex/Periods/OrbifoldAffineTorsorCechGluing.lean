module

public import SphereSixComplex.Periods.HolomorphicAffineTorsorHOneSplitting
import all SphereSixComplex.Periods.Functions

/-!
# Cech gluing for orbifold affine torsors

This file proves the formal gluing step from two affine chart sections to one global equivariant
section.  The only additional cusp input is that an entire infinity-chart coefficient times the
infinity frame is bounded on the distinguished cusp region.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

namespace OrbifoldAffineLineTorsorDescentProblem

open HolomorphicAffineTorsorHOne

/-- Exact comparison data between an orbifold affine-torsor descent problem and the standard
two-chart Cech presentation of `O(-1)` or `O` on the projective line. -/
public structure CechGluingData (P : OrbifoldAffineLineTorsorDescentProblem) where
  descent : P.AnalyticDescentData
  frame : AcyclicProjectiveLineFrame
  frameTransition_eq : P.frameTransition = frame.transition
  infinityCorrection_cusp_bounded : ∀ f : ℂ → ℂ, MDiff f →
    BoundedOn
      (fun z ↦ f ((P.quotient.coordinate z)⁻¹) * P.frameInfinity z)
      fuchsianCuspRegion

/-- The projective-line affine torsor represented by the descended chart mismatch. -/
@[expose] public def CechGluingData.projectiveLineTorsor
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.CechGluingData) :
    ProjectiveLineAffineTorsor D.frame.transition where
  cocycle := D.descent.mismatch_descent.coefficient
  cocycle_holomorphic := D.descent.mismatch_descent.coefficient_holomorphic

/-- Correct the finite-chart section by the zero-chart part of a Cech splitting. -/
@[expose] public def CechGluingData.adjustedZero
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.CechGluingData)
    (S : D.projectiveLineTorsor.Splitting) (z : UpperHalfPlane) : ℂ :=
  D.descent.charts.sectionZero z -
    S.sectionZero (P.quotient.coordinate z) * P.frameZero z

/-- Correct the cusp-chart section by the infinity-chart part of a Cech splitting. -/
@[expose] public def CechGluingData.adjustedInfinity
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.CechGluingData)
    (S : D.projectiveLineTorsor.Splitting) (z : UpperHalfPlane) : ℂ :=
  D.descent.charts.sectionInfinity z -
    S.sectionInfinity ((P.quotient.coordinate z)⁻¹) * P.frameInfinity z

/-- The two corrected affine sections agree wherever the infinity chart is defined. -/
public theorem CechGluingData.adjustedZero_eq_adjustedInfinity
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.CechGluingData)
    (S : D.projectiveLineTorsor.Splitting) (z : UpperHalfPlane)
    (hz : P.quotient.coordinate z ≠ 0) :
    D.adjustedZero S z = D.adjustedInfinity S z := by
  have hmismatch := D.descent.mismatch_descent.factorization z hz
  have hsplit := S.coboundary (P.quotient.coordinate z) hz
  have hframe := P.frame_transition z hz
  rw [D.frameTransition_eq] at hframe
  change D.descent.charts.sectionZero z - D.descent.charts.sectionInfinity z =
    D.projectiveLineTorsor.cocycle (P.quotient.coordinate z) * P.frameZero z at hmismatch
  change D.projectiveLineTorsor.cocycle (P.quotient.coordinate z) =
    S.sectionZero (P.quotient.coordinate z) -
      D.frame.transition (P.quotient.coordinate z) *
        S.sectionInfinity ((P.quotient.coordinate z)⁻¹) at hsplit
  unfold adjustedZero adjustedInfinity
  rw [hframe]
  linear_combination hmismatch + P.frameZero z * hsplit

/-- The corrected finite-chart section is holomorphic on the whole upper half-plane. -/
public theorem CechGluingData.adjustedZero_holomorphic
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.CechGluingData)
    (S : D.projectiveLineTorsor.Splitting) :
    MDiff (D.adjustedZero S) := by
  exact D.descent.charts.sectionZero_holomorphic.sub
    ((S.sectionZero_holomorphic.comp P.quotient.coordinate_holomorphic).mul
      P.frameZero_holomorphic)

/-- The corrected finite-chart section obeys the first affine generator law. -/
public theorem CechGluingData.adjustedZero_one
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.CechGluingData)
    (S : D.projectiveLineTorsor.Splitting) (z : UpperHalfPlane) :
    D.adjustedZero S (fuchsianSourceAction g₁ • z) =
      P.affineOne z (D.adjustedZero S z) := by
  unfold adjustedZero
  rw [D.descent.charts.sectionZero_one, P.quotient.coordinate_invariant,
    P.frameZero_one]
  have h := P.affineOne_sub z (D.descent.charts.sectionZero z)
    (D.descent.charts.sectionZero z -
      S.sectionZero (P.quotient.coordinate z) * P.frameZero z)
  linear_combination h

/-- The corrected finite-chart section obeys the second affine generator law. -/
public theorem CechGluingData.adjustedZero_two
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.CechGluingData)
    (S : D.projectiveLineTorsor.Splitting) (z : UpperHalfPlane) :
    D.adjustedZero S (fuchsianSourceAction g₂ • z) =
      P.affineTwo z (D.adjustedZero S z) := by
  unfold adjustedZero
  rw [D.descent.charts.sectionZero_two, P.quotient.coordinate_invariant,
    P.frameZero_two]
  have h := P.affineTwo_sub z (D.descent.charts.sectionZero z)
    (D.descent.charts.sectionZero z -
      S.sectionZero (P.quotient.coordinate z) * P.frameZero z)
  linear_combination h

private theorem boundedOn_sub
    {f g : UpperHalfPlane → ℂ} {s : Set UpperHalfPlane}
    (hf : BoundedOn f s) (hg : BoundedOn g s) :
    BoundedOn (fun z ↦ f z - g z) s := by
  unfold BoundedOn at hf hg ⊢
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨Cf + Cg, add_nonneg hCf hCg, ?_⟩
  intro z hz
  exact (norm_sub_le (f z) (g z)).trans (add_le_add (hf z hz) (hg z hz))

/-- The corrected global section differs boundedly from the supplied regular cusp primitive. -/
public theorem CechGluingData.adjustedZero_sub_cusp_bounded
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.CechGluingData)
    (S : D.projectiveLineTorsor.Splitting) :
    BoundedOn (fun z ↦ D.adjustedZero S z - P.cuspSection z)
      fuchsianCuspRegion := by
  have hinfinity :
      BoundedOn (fun z ↦ D.adjustedInfinity S z - P.cuspSection z)
        fuchsianCuspRegion := by
    convert boundedOn_sub D.descent.charts.sectionInfinity_sub_cusp_bounded
      (D.infinityCorrection_cusp_bounded S.sectionInfinity
        S.sectionInfinity_holomorphic) using 1
    funext z
    unfold adjustedInfinity
    ring
  unfold BoundedOn at hinfinity ⊢
  obtain ⟨C, hC, hbound⟩ := hinfinity
  refine ⟨C, hC, ?_⟩
  intro z hz
  change ‖D.adjustedZero S z - P.cuspSection z‖ ≤ C
  rw [D.adjustedZero_eq_adjustedInfinity S z (P.cusp_coordinate_ne_zero z hz)]
  exact hbound z hz

/-- A Cech splitting produces the single global, equivariant, cusp-bounded section. -/
public theorem CechGluingData.hasCuspBoundedEquivariantSection
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.CechGluingData)
    (S : D.projectiveLineTorsor.Splitting) :
    P.HasCuspBoundedEquivariantSection :=
  ⟨D.adjustedZero S, D.adjustedZero_holomorphic S, D.adjustedZero_one S,
    D.adjustedZero_two S, D.adjustedZero_sub_cusp_bounded S⟩

/-- The comparison data give the abstract Cech reduction isolated in
`HolomorphicAffineTorsorHOneSplitting`. -/
@[expose] public noncomputable def CechGluingData.toCuspCorrectionCechReduction
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.CechGluingData) :
    P.CuspCorrectionCechReduction where
  frame := D.frame
  torsor := D.projectiveLineTorsor
  correctionOfSplitting := fun S ↦ Classical.choice
    (P.nonempty_correction_of_hasCuspBoundedEquivariantSection
      (D.hasCuspBoundedEquivariantSection S))

/-- Exact Cech comparison data suffice for the original cusp-bounded Cousin correction. -/
public theorem nonempty_cuspBoundedEllipticOneCorrection_of_cechGluingData
    (P : OrbifoldAffineLineTorsorDescentProblem) (D : P.CechGluingData) :
    Nonempty P.CuspBoundedEllipticOneCorrection :=
  P.nonempty_cuspBoundedEllipticOneCorrection_of_cechReduction
    D.toCuspCorrectionCechReduction

end OrbifoldAffineLineTorsorDescentProblem

end SphereSixComplex.Periods

module

public import SphereSixComplex.Periods.OrbifoldAffineTorsorCuspFrameBounds
import all SphereSixComplex.Periods.Functions

/-!
# Local Cech reduction for orbifold affine torsors

The projective-line Cech calculation only needs local affine sections on the two quotient
charts.  This file states that genuinely local input and proves all subsequent gluing,
equivariance, and cusp estimates.  In particular, the local package contains no global
equivariant section.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open Set
open SphereSixComplex.TriangleGroup

namespace OrbifoldAffineLineTorsorDescentProblem

open HolomorphicAffineTorsorHOne

/-- Local analytic trivializations of an orbifold affine torsor on the finite and cusp charts.
The overlap mismatch has already been descended to the punctured quotient plane. -/
public structure LocalCechPresentation
    (P : OrbifoldAffineLineTorsorDescentProblem) where
  zeroRegion : Set UpperHalfPlane
  infinityRegion : Set UpperHalfPlane
  zeroRegion_open : IsOpen zeroRegion
  infinityRegion_open : IsOpen infinityRegion
  regions_cover : zeroRegion ∪ infinityRegion = Set.univ
  zeroRegion_invariant : ∀ g z,
    fuchsianSourceAction g • z ∈ zeroRegion ↔ z ∈ zeroRegion
  infinityRegion_invariant : ∀ g z,
    fuchsianSourceAction g • z ∈ infinityRegion ↔ z ∈ infinityRegion
  sectionZero : UpperHalfPlane → ℂ
  sectionInfinity : UpperHalfPlane → ℂ
  sectionZero_holomorphic : ∀ z, z ∈ zeroRegion → MDiffAt sectionZero z
  sectionInfinity_holomorphic : ∀ z, z ∈ infinityRegion → MDiffAt sectionInfinity z
  sectionZero_one : ∀ z, z ∈ zeroRegion →
    sectionZero (fuchsianSourceAction g₁ • z) = P.affineOne z (sectionZero z)
  sectionZero_two : ∀ z, z ∈ zeroRegion →
    sectionZero (fuchsianSourceAction g₂ • z) = P.affineTwo z (sectionZero z)
  sectionInfinity_one : ∀ z, z ∈ infinityRegion →
    sectionInfinity (fuchsianSourceAction g₁ • z) = P.affineOne z (sectionInfinity z)
  sectionInfinity_two : ∀ z, z ∈ infinityRegion →
    sectionInfinity (fuchsianSourceAction g₂ • z) = P.affineTwo z (sectionInfinity z)
  overlapCocycle : ℂ → ℂ
  overlapCocycle_holomorphic : HolomorphicOnPuncturedPlane overlapCocycle
  infinity_coordinate_ne_zero : ∀ z, z ∈ infinityRegion →
    P.quotient.coordinate z ≠ 0
  section_mismatch : ∀ z, z ∈ zeroRegion ∩ infinityRegion →
    sectionZero z - sectionInfinity z =
      overlapCocycle (P.quotient.coordinate z) * P.frameZero z
  cusp_subset_infinity : fuchsianCuspRegion ⊆ infinityRegion
  sectionInfinity_sub_cusp_bounded :
    BoundedOn (fun z ↦ sectionInfinity z - P.cuspSection z) fuchsianCuspRegion

/-- The projective-line affine torsor represented by the local overlap mismatch. -/
@[expose] public def LocalCechPresentation.projectiveLineTorsor
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    (frame : AcyclicProjectiveLineFrame) :
    ProjectiveLineAffineTorsor frame.transition where
  cocycle := D.overlapCocycle
  cocycle_holomorphic := D.overlapCocycle_holomorphic

/-- Correct the local finite-chart section by a Cech zero-cochain. -/
@[expose] public def LocalCechPresentation.adjustedZero
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    (fZero : ℂ → ℂ) (z : UpperHalfPlane) : ℂ :=
  D.sectionZero z - fZero (P.quotient.coordinate z) * P.frameZero z

/-- Correct the local cusp-chart section by a Cech zero-cochain. -/
@[expose] public def LocalCechPresentation.adjustedInfinity
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    (fInfinity : ℂ → ℂ) (z : UpperHalfPlane) : ℂ :=
  D.sectionInfinity z -
    fInfinity ((P.quotient.coordinate z)⁻¹) * P.frameInfinity z

public theorem LocalCechPresentation.adjustedZero_eq_adjustedInfinity
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    (frame : AcyclicProjectiveLineFrame)
    (hframe : P.frameTransition = frame.transition)
    (S : (D.projectiveLineTorsor frame).Splitting) (z : UpperHalfPlane)
    (hz : z ∈ D.zeroRegion ∩ D.infinityRegion) :
    D.adjustedZero S.sectionZero z = D.adjustedInfinity S.sectionInfinity z := by
  have hq := D.infinity_coordinate_ne_zero z hz.2
  have hmismatch := D.section_mismatch z hz
  have hsplit := S.coboundary (P.quotient.coordinate z) hq
  have hframe' := P.frame_transition z hq
  rw [hframe] at hframe'
  change D.overlapCocycle (P.quotient.coordinate z) =
    S.sectionZero (P.quotient.coordinate z) -
      frame.transition (P.quotient.coordinate z) *
        S.sectionInfinity ((P.quotient.coordinate z)⁻¹) at hsplit
  unfold adjustedZero adjustedInfinity
  rw [hframe']
  linear_combination hmismatch + P.frameZero z * hsplit

public theorem LocalCechPresentation.adjustedZero_holomorphicAt
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    {fZero : ℂ → ℂ} (hfZero : MDiff fZero) {z : UpperHalfPlane}
    (hz : z ∈ D.zeroRegion) : MDiffAt (D.adjustedZero fZero) z := by
  exact (D.sectionZero_holomorphic z hz).sub
    (((hfZero _).comp z (P.quotient.coordinate_holomorphic z)).mul
      P.frameZero_holomorphic.mdifferentiableAt)

public theorem LocalCechPresentation.adjustedInfinity_holomorphicAt
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    {fInfinity : ℂ → ℂ} (hfInfinity : MDiff fInfinity) {z : UpperHalfPlane}
    (hz : z ∈ D.infinityRegion) : MDiffAt (D.adjustedInfinity fInfinity) z := by
  have hq := D.infinity_coordinate_ne_zero z hz
  have hinv : MDiffAt (fun w ↦ (P.quotient.coordinate w)⁻¹) z :=
    (P.quotient.coordinate_holomorphic z).inv hq
  exact (D.sectionInfinity_holomorphic z hz).sub
    (((hfInfinity _).comp z hinv).mul (P.frameInfinity_holomorphic z hq))

public theorem LocalCechPresentation.adjustedZero_one
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    (fZero : ℂ → ℂ) (z : UpperHalfPlane) (hz : z ∈ D.zeroRegion) :
    D.adjustedZero fZero (fuchsianSourceAction g₁ • z) =
      P.affineOne z (D.adjustedZero fZero z) := by
  unfold adjustedZero
  rw [D.sectionZero_one z hz, P.quotient.coordinate_invariant, P.frameZero_one]
  have h := P.affineOne_sub z (D.sectionZero z)
    (D.sectionZero z - fZero (P.quotient.coordinate z) * P.frameZero z)
  linear_combination h

public theorem LocalCechPresentation.adjustedZero_two
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    (fZero : ℂ → ℂ) (z : UpperHalfPlane) (hz : z ∈ D.zeroRegion) :
    D.adjustedZero fZero (fuchsianSourceAction g₂ • z) =
      P.affineTwo z (D.adjustedZero fZero z) := by
  unfold adjustedZero
  rw [D.sectionZero_two z hz, P.quotient.coordinate_invariant, P.frameZero_two]
  have h := P.affineTwo_sub z (D.sectionZero z)
    (D.sectionZero z - fZero (P.quotient.coordinate z) * P.frameZero z)
  linear_combination h

public theorem LocalCechPresentation.adjustedInfinity_one
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    (fInfinity : ℂ → ℂ) (z : UpperHalfPlane) (hz : z ∈ D.infinityRegion) :
    D.adjustedInfinity fInfinity (fuchsianSourceAction g₁ • z) =
      P.affineOne z (D.adjustedInfinity fInfinity z) := by
  have hq := D.infinity_coordinate_ne_zero z hz
  unfold adjustedInfinity
  rw [D.sectionInfinity_one z hz, P.quotient.coordinate_invariant,
    P.frameInfinity_one z hq]
  have h := P.affineOne_sub z (D.sectionInfinity z)
    (D.sectionInfinity z -
      fInfinity ((P.quotient.coordinate z)⁻¹) * P.frameInfinity z)
  linear_combination h

public theorem LocalCechPresentation.adjustedInfinity_two
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    (fInfinity : ℂ → ℂ) (z : UpperHalfPlane) (hz : z ∈ D.infinityRegion) :
    D.adjustedInfinity fInfinity (fuchsianSourceAction g₂ • z) =
      P.affineTwo z (D.adjustedInfinity fInfinity z) := by
  have hq := D.infinity_coordinate_ne_zero z hz
  unfold adjustedInfinity
  rw [D.sectionInfinity_two z hz, P.quotient.coordinate_invariant,
    P.frameInfinity_two z hq]
  have h := P.affineTwo_sub z (D.sectionInfinity z)
    (D.sectionInfinity z -
      fInfinity ((P.quotient.coordinate z)⁻¹) * P.frameInfinity z)
  linear_combination h

private theorem LocalCechPresentation.mem_infinityRegion_of_not_mem_zeroRegion
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    {z : UpperHalfPlane} (hz : z ∉ D.zeroRegion) : z ∈ D.infinityRegion := by
  have hcover : z ∈ D.zeroRegion ∪ D.infinityRegion := by
    rw [D.regions_cover]
    exact Set.mem_univ z
  exact hcover.resolve_left hz

/-- The global section obtained by gluing compatible corrected local sections. -/
@[expose] public def LocalCechPresentation.gluedSection
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    (fZero fInfinity : ℂ → ℂ) (z : UpperHalfPlane) : ℂ := by
  classical
  exact if z ∈ D.zeroRegion then D.adjustedZero fZero z
    else D.adjustedInfinity fInfinity z

public theorem LocalCechPresentation.gluedSection_holomorphic
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    {fZero fInfinity : ℂ → ℂ} (hfZero : MDiff fZero) (hfInfinity : MDiff fInfinity)
    (hcompat : ∀ z, z ∈ D.zeroRegion ∩ D.infinityRegion →
      D.adjustedZero fZero z = D.adjustedInfinity fInfinity z) :
    MDiff (D.gluedSection fZero fInfinity) := by
  classical
  intro z
  by_cases hz : z ∈ D.zeroRegion
  · have heq : D.gluedSection fZero fInfinity =ᶠ[nhds z] D.adjustedZero fZero := by
      filter_upwards [D.zeroRegion_open.mem_nhds hz] with w hw
      simp [gluedSection, hw]
    exact heq.mdifferentiableAt_iff.mpr (D.adjustedZero_holomorphicAt hfZero hz)
  · have hzInfinity := D.mem_infinityRegion_of_not_mem_zeroRegion hz
    have heq : D.gluedSection fZero fInfinity =ᶠ[nhds z] D.adjustedInfinity fInfinity := by
      filter_upwards [D.infinityRegion_open.mem_nhds hzInfinity] with w hw
      by_cases hwZero : w ∈ D.zeroRegion
      · simpa [gluedSection, hwZero] using hcompat w ⟨hwZero, hw⟩
      · simp [gluedSection, hwZero]
    exact heq.mdifferentiableAt_iff.mpr
      (D.adjustedInfinity_holomorphicAt hfInfinity hzInfinity)

public theorem LocalCechPresentation.gluedSection_one
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    (fZero fInfinity : ℂ → ℂ) (z : UpperHalfPlane) :
    D.gluedSection fZero fInfinity (fuchsianSourceAction g₁ • z) =
      P.affineOne z (D.gluedSection fZero fInfinity z) := by
  classical
  by_cases hz : z ∈ D.zeroRegion
  · have hgz := (D.zeroRegion_invariant g₁ z).mpr hz
    simpa only [gluedSection, hgz, hz, ite_true] using D.adjustedZero_one fZero z hz
  · have hzInfinity := D.mem_infinityRegion_of_not_mem_zeroRegion hz
    have hgz : fuchsianSourceAction g₁ • z ∉ D.zeroRegion :=
      fun h ↦ hz ((D.zeroRegion_invariant g₁ z).mp h)
    simpa only [gluedSection, hgz, hz, ite_false] using
      D.adjustedInfinity_one fInfinity z hzInfinity

public theorem LocalCechPresentation.gluedSection_two
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    (fZero fInfinity : ℂ → ℂ) (z : UpperHalfPlane) :
    D.gluedSection fZero fInfinity (fuchsianSourceAction g₂ • z) =
      P.affineTwo z (D.gluedSection fZero fInfinity z) := by
  classical
  by_cases hz : z ∈ D.zeroRegion
  · have hgz := (D.zeroRegion_invariant g₂ z).mpr hz
    simpa only [gluedSection, hgz, hz, ite_true] using D.adjustedZero_two fZero z hz
  · have hzInfinity := D.mem_infinityRegion_of_not_mem_zeroRegion hz
    have hgz : fuchsianSourceAction g₂ • z ∉ D.zeroRegion :=
      fun h ↦ hz ((D.zeroRegion_invariant g₂ z).mp h)
    simpa only [gluedSection, hgz, hz, ite_false] using
      D.adjustedInfinity_two fInfinity z hzInfinity

private theorem boundedOn_sub
    {f g : UpperHalfPlane → ℂ} {s : Set UpperHalfPlane}
    (hf : BoundedOn f s) (hg : BoundedOn g s) :
    BoundedOn (fun z ↦ f z - g z) s := by
  rw [SphereSixComplex.Periods.BoundedOn.eq_def] at hf hg ⊢
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨Cf + Cg, add_nonneg hCf hCg, ?_⟩
  intro z hz
  exact (norm_sub_le (f z) (g z)).trans (add_le_add (hf z hz) (hg z hz))

public theorem LocalCechPresentation.adjustedInfinity_sub_cusp_bounded
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    {fInfinity : ℂ → ℂ} (hfInfinity : MDiff fInfinity) :
    BoundedOn (fun z ↦ D.adjustedInfinity fInfinity z - P.cuspSection z)
      fuchsianCuspRegion := by
  have h := boundedOn_sub D.sectionInfinity_sub_cusp_bounded
    (P.infinityCorrection_cusp_bounded fInfinity hfInfinity)
  convert h using 1
  funext z
  unfold adjustedInfinity
  ring

public theorem LocalCechPresentation.gluedSection_eq_infinity_on_cusp
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    {fZero fInfinity : ℂ → ℂ}
    (hcompat : ∀ z, z ∈ D.zeroRegion ∩ D.infinityRegion →
      D.adjustedZero fZero z = D.adjustedInfinity fInfinity z)
    {z : UpperHalfPlane} (hz : z ∈ fuchsianCuspRegion) :
    D.gluedSection fZero fInfinity z = D.adjustedInfinity fInfinity z := by
  classical
  have hzInfinity := D.cusp_subset_infinity hz
  by_cases hzZero : z ∈ D.zeroRegion
  · simpa [gluedSection, hzZero] using hcompat z ⟨hzZero, hzInfinity⟩
  · simp [gluedSection, hzZero]

public theorem LocalCechPresentation.gluedSection_sub_cusp_bounded
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    {fZero fInfinity : ℂ → ℂ} (hfInfinity : MDiff fInfinity)
    (hcompat : ∀ z, z ∈ D.zeroRegion ∩ D.infinityRegion →
      D.adjustedZero fZero z = D.adjustedInfinity fInfinity z) :
    BoundedOn (fun z ↦ D.gluedSection fZero fInfinity z - P.cuspSection z)
      fuchsianCuspRegion := by
  rw [SphereSixComplex.Periods.BoundedOn.eq_def] at *
  obtain ⟨C, hC, hbound⟩ := D.adjustedInfinity_sub_cusp_bounded hfInfinity
  refine ⟨C, hC, ?_⟩
  intro z hz
  rw [D.gluedSection_eq_infinity_on_cusp hcompat hz]
  exact hbound z hz

/-- A Cech splitting of the local presentation produces the required global affine section. -/
public theorem LocalCechPresentation.hasCuspBoundedEquivariantSection
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    (frame : AcyclicProjectiveLineFrame)
    (hframe : P.frameTransition = frame.transition)
    (S : (D.projectiveLineTorsor frame).Splitting) :
    P.HasCuspBoundedEquivariantSection := by
  have hcompat := D.adjustedZero_eq_adjustedInfinity frame hframe S
  exact ⟨D.gluedSection S.sectionZero S.sectionInfinity,
    D.gluedSection_holomorphic S.sectionZero_holomorphic
      S.sectionInfinity_holomorphic hcompat,
    D.gluedSection_one S.sectionZero S.sectionInfinity,
    D.gluedSection_two S.sectionZero S.sectionInfinity,
    D.gluedSection_sub_cusp_bounded S.sectionInfinity_holomorphic hcompat⟩

/-- Local quotient-chart trivializations are the only remaining input after the proved
projective-line Cech vanishing. -/
@[expose] public noncomputable def LocalCechPresentation.toCuspCorrectionCechReduction
    {P : OrbifoldAffineLineTorsorDescentProblem} (D : P.LocalCechPresentation)
    (frame : AcyclicProjectiveLineFrame)
    (hframe : P.frameTransition = frame.transition) : P.CuspCorrectionCechReduction where
  frame := frame
  torsor := D.projectiveLineTorsor frame
  correctionOfSplitting := fun S ↦ Classical.choice
    (P.nonempty_correction_of_hasCuspBoundedEquivariantSection
      (D.hasCuspBoundedEquivariantSection frame hframe S))

/-- The full cusp-bounded Cousin correction follows from genuinely local Cech data. -/
public theorem nonempty_cuspBoundedEllipticOneCorrection_of_localCechPresentation
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (D : P.LocalCechPresentation) (frame : AcyclicProjectiveLineFrame)
    (hframe : P.frameTransition = frame.transition) :
    Nonempty P.CuspBoundedEllipticOneCorrection :=
  P.nonempty_cuspBoundedEllipticOneCorrection_of_cechReduction
    (D.toCuspCorrectionCechReduction frame hframe)

end OrbifoldAffineLineTorsorDescentProblem

end SphereSixComplex.Periods

module

public import SphereSixComplex.Periods.OrbifoldAffineTorsorLocalCover
public import SphereSixComplex.Periods.OrbifoldAffineTorsorCuspGermBounds
public import SphereSixComplex.Periods.OrbifoldAffineTorsorCocycle
public import SphereSixComplex.Analysis.HolomorphicCocycle

@[expose] public section
noncomputable section
open Filter Set SphereSixComplex.TriangleGroup
open scoped Manifold
namespace SphereSixComplex.Periods.OrbifoldAffineLineTorsorDescentProblem

public theorem hasCuspBoundedEquivariantSection_of_standard_transition
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (hframe : P.frameTransition = (fun q ↦ q⁻¹) ∨ P.frameTransition = (fun _ ↦ 1)) :
    P.HasCuspBoundedEquivariantSection := by
  obtain ⟨U, s, hU, hcover, hs, heqs, hzero, hone, ⟨R, hR, hRU⟩, hscusp⟩ :=
    P.exists_local_equivariant_cover
  have hcov : ∀ q, ∃ i, q ∈ U i := fun q ↦ ⟨some q, hcover q⟩
  obtain ⟨f, hf, hfcoc, hfdiff⟩ := P.exists_local_section_cocycle U hU
    (fun i j hij ↦ distinct_overlap_regular hzero hone hij) s hs heqs
  obtain ⟨c, g, hc, hg, hcdiff, hcInfinity⟩ :=
    Analysis.CauchyGreen.exists_negativeOne_holomorphic_cocycle_solution
      hU hcov hf hfcoc none hR hRU
  obtain ⟨t, ht, heqt, hglue⟩ := P.glue_local_sections U hU hcov s hs heqs c hc (by
    intro i j z hi hj
    rw [hfdiff i j z hi hj, hcdiff i j (P.quotient.coordinate z) hi hj])
  have htCusp : ∀ z, t (fuchsianSourceAction g₀ • z) = P.affineCusp z (t z) := by
    intro z
    rw [heqt, P.affineTransport_cusp]
  have hg0 : ContinuousAt g 0 :=
    (hg 0 (by simpa using inv_pos.mpr hR)).continuousAt
  have hhigh : ∀ᶠ z in upperHalfPlaneAtInfinity, 1 < z.im :=
    (eventually_gt_atTop (1 : ℝ)).comap UpperHalfPlane.im
  have hlarge : ∀ᶠ z in upperHalfPlaneAtInfinity, R < ‖P.quotient.coordinate z‖ := by
    have hinv := P.quotient.inverse_coordinate_tendsto_zero.eventually
      (Metric.ball_mem_nhds (0 : ℂ) (inv_pos.mpr hR))
    filter_upwards [hinv, hhigh] with z hz hh
    have hq : P.quotient.coordinate z ≠ 0 := P.cusp_coordinate_ne_zero z hh.le
    have hi : ‖P.quotient.coordinate z‖⁻¹ < R⁻¹ := by
      simpa only [Metric.mem_ball, dist_zero_right, norm_inv] using hz
    exact (inv_lt_inv₀ (norm_pos_iff.mpr hq) hR).mp hi
  have hformula : ∀ᶠ z in upperHalfPlaneAtInfinity,
      t z - P.cuspSection z =
        -((P.quotient.coordinate z)⁻¹ * g (P.quotient.coordinate z)⁻¹ * P.frameZero z) := by
    filter_upwards [hlarge, hhigh] with z hz hh
    have hzi : P.quotient.coordinate z ∈ U none := hRU (by
      simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hz.le)
    rw [hglue none z hzi, hscusp z hh, hcInfinity _ hz]
    ring
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · intro z
    simpa [affineOnePerm, affineOneSkew] using heqt g₁ z
  · intro z
    simpa [affineTwoPerm, affineTwoSkew] using heqt g₂ z
  · rcases hframe with hframe | hframe
    · apply P.cusp_difference_bounded_of_infinity_germ t ht htCusp (fun u ↦ -g u) hg0.neg
      filter_upwards [hformula, hhigh] with z hz hh
      have hfr := P.frame_transition z (P.cusp_coordinate_ne_zero z hh.le)
      rw [hframe] at hfr
      rw [hz, hfr]
      ring
    · apply P.cusp_difference_bounded_of_infinity_germ t ht htCusp
        (fun u ↦ -u * g u) (continuousAt_id.neg.mul hg0)
      filter_upwards [hformula, hhigh] with z hz hh
      have hfr := P.frame_transition z (P.cusp_coordinate_ne_zero z hh.le)
      rw [hframe] at hfr
      rw [hz, hfr]
      ring

end SphereSixComplex.Periods.OrbifoldAffineLineTorsorDescentProblem

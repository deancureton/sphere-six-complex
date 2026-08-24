module

public import SphereSixComplex.Periods.Uniformization.CuspExponentialJordan
import all SphereSixComplex.Periods.Uniformization.CuspExponentialJordan
public import SphereSixComplex.Periods.Uniformization.InverseBoundaryCluster
import all SphereSixComplex.Periods.Uniformization.InverseBoundaryCluster
public import SphereSixComplex.Periods.Uniformization.JordanFilledHullSeparation
import all SphereSixComplex.Periods.Uniformization.JordanFilledHullSeparation
public import TauCeti.Analysis.Complex.Conformal.Caratheodory
import all TauCeti.Analysis.Complex.Conformal.Caratheodory

@[expose] public section

open Complex Filter Metric Set Topology

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.Periods.JordanFilledHullSeparation

theorem sourceBoundedChamber_isPreconnectedApproachAt
    {q : ℂ} (hq : q ∈ frontier sourceBoundedChamber) :
    TauCeti.IsPreconnectedApproachAt sourceBoundedChamber q := by
  by_cases hq0 : q = 0
  · subst q
    exact sourceBoundedChamber_isPreconnectedApproachAt_zero
  rw [frontier_sourceBoundedChamber_eq_cuspPolar_boundary] at hq
  obtain ⟨⟨x, t⟩, hp, rfl⟩ := hq
  have hp' := (mem_cuspRectangleBoundary_iff
    (show -Real.sqrt 2 / 2 ≤ (1 / 2 : ℝ) by
      have hs := Real.sqrt_nonneg 2
      linarith) (x, t)).mp hp
  have ht0 : 0 ≤ t := hp'.1.2.1
  have htne : t ≠ 0 := by
    intro ht
    apply hq0
    simp [cuspPolar, ht]
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htne)
  let y₀ : ℝ :=
    semicircleHeight x - (1 + Real.sqrt 2) * Real.log t / (2 * Real.pi)
  let z₀ : ℂ := (x : ℂ) + (y₀ : ℂ) * I
  have hpolar : cuspPolar (1 + Real.sqrt 2) semicircleHeight (x, t) =
      cuspExponential (1 + Real.sqrt 2) z₀ := by
    simpa [z₀, y₀] using cuspPolar_eq_cuspExponential (1 + Real.sqrt 2)
      (show (1 + Real.sqrt 2 : ℝ) ≠ 0 by positivity) semicircleHeight x htpos
  rw [hpolar, sourceBoundedChamber]
  apply TauCeti.isPreconnectedApproachAt_cuspExponential_image
    (1 + Real.sqrt 2) z₀ (show (1 + Real.sqrt 2 : ℝ) ≠ 0 by positivity)
    (g := verticalShear semicircleHeight continuous_semicircleHeight)
  · apply TauCeti.subset_cuspExponentialLocalChart_source_of_re_mem_Ioo_Icc
      (show 0 < (1 + Real.sqrt 2 : ℝ) by positivity)
      (l := -Real.sqrt 2 / 2) (r := 1 / 2)
    · ring_nf
      exact le_rfl
    · intro z hz
      exact ⟨hz.1, hz.2.1⟩
    · have hz₀re : z₀.re = x := by
        simp [z₀]
      rw [hz₀re]
      exact hp'.1.1
  · rw [verticalShear_image_sourceOpenChamber]
    exact flatOpenChamber_convex

theorem targetBoundedChamber_isPreconnectedApproachAt
    {q : ℂ} (hq : q ∈ frontier targetBoundedChamber) :
    TauCeti.IsPreconnectedApproachAt targetBoundedChamber q := by
  by_cases hq0 : q = 0
  · subst q
    exact targetBoundedChamber_isPreconnectedApproachAt_zero
  rw [frontier_targetBoundedChamber_eq_cuspPolar_boundary] at hq
  obtain ⟨⟨x, t⟩, hp, rfl⟩ := hq
  have hp' := (mem_cuspRectangleBoundary_iff (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (x, t)).mp hp
  have ht0 : 0 ≤ t := hp'.1.2.1
  have htne : t ≠ 0 := by
    intro ht
    apply hq0
    simp [cuspPolar, ht]
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htne)
  let y₀ : ℝ := semicircleHeight x - Real.log t / (2 * Real.pi)
  let z₀ : ℂ := (x : ℂ) + (y₀ : ℂ) * I
  have hpolar : cuspPolar 1 semicircleHeight (x, t) = cuspExponential 1 z₀ := by
    simpa [z₀, y₀] using cuspPolar_eq_cuspExponential 1 one_ne_zero
      semicircleHeight x htpos
  rw [hpolar, targetBoundedChamber]
  apply TauCeti.isPreconnectedApproachAt_cuspExponential_image 1 z₀ one_ne_zero
    (g := verticalShear semicircleHeight continuous_semicircleHeight)
  · apply TauCeti.subset_cuspExponentialLocalChart_source_of_re_mem_Ioo_Icc
      (show (0 : ℝ) < 1 by norm_num) (l := 0) (r := 1 / 2)
    · norm_num
    · intro z hz
      exact ⟨hz.1, hz.2.1⟩
    · have hz₀re : z₀.re = x := by
        simp [z₀]
      rw [hz₀re]
      exact hp'.1.1
  · rw [verticalShear_image_targetOpenChamber]
    exact targetFlatOpenChamber_convex

/-- A Riemann map from the disc onto the compactified source chamber, injective up to the
boundary. -/
theorem exists_sourceChamber_caratheodoryMap :
    ∃ g : ℂ → ℂ, ContinuousOn g (closedBall 0 1) ∧
      DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn g (ball 0 1) sourceBoundedChamber ∧
      InjOn g (closedBall 0 1) := by
  obtain ⟨g, hgc, hgd, hgbij⟩ :=
    TauCeti.exists_continuousOn_closedBall_bijOn_ball_of_isJordanCurve_frontier
      sourceBoundedChamber_isOpen sourceBoundedChamber_isSimplyConnected
      sourceBoundedChamber_isBounded sourceBoundedChamber_frontier_isJordanCurve
      (fun _ hJ ↦ isJordanCurve_subset_closure_filledHull_diff_complex hJ)
  have hloc : ∀ a ∈ frontier (g '' ball 0 1),
      TauCeti.IsPreconnectedApproachAt (g '' ball 0 1) a := by
    intro a ha
    rw [hgbij.image_eq] at ha ⊢
    exact sourceBoundedChamber_isPreconnectedApproachAt ha
  have hginj : InjOn g (closedBall 0 1) :=
    TauCeti.injOn_closedBall_of_isPreconnected_image_approach one_pos hgd hgbij.injOn
      hgc (fun _ _ ↦ rfl) hloc
  exact ⟨g, hgc, hgd, hgbij, hginj⟩

/-- A Riemann map from the disc onto the compactified target chamber, injective up to the
boundary. -/
theorem exists_targetChamber_caratheodoryMap :
    ∃ g : ℂ → ℂ, ContinuousOn g (closedBall 0 1) ∧
      DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn g (ball 0 1) targetBoundedChamber ∧
      InjOn g (closedBall 0 1) := by
  obtain ⟨g, hgc, hgd, hgbij⟩ :=
    TauCeti.exists_continuousOn_closedBall_bijOn_ball_of_isJordanCurve_frontier
      targetBoundedChamber_isOpen targetBoundedChamber_isSimplyConnected
      targetBoundedChamber_isBounded targetBoundedChamber_frontier_isJordanCurve
      (fun _ hJ ↦ isJordanCurve_subset_closure_filledHull_diff_complex hJ)
  have hloc : ∀ a ∈ frontier (g '' ball 0 1),
      TauCeti.IsPreconnectedApproachAt (g '' ball 0 1) a := by
    intro a ha
    rw [hgbij.image_eq] at ha ⊢
    exact targetBoundedChamber_isPreconnectedApproachAt ha
  have hginj : InjOn g (closedBall 0 1) :=
    TauCeti.injOn_closedBall_of_isPreconnected_image_approach one_pos hgd hgbij.injOn
      hgc (fun _ _ ↦ rfl) hloc
  exact ⟨g, hgc, hgd, hgbij, hginj⟩

/-- The source Carathéodory map packaged as a homeomorphism of closures. -/
theorem exists_sourceChamber_closureHomeomorph :
    ∃ (g : ℂ → ℂ) (e : closedBall (0 : ℂ) 1 ≃ₜ closure sourceBoundedChamber),
      DifferentiableOn ℂ g (ball 0 1) ∧ BijOn g (ball 0 1) sourceBoundedChamber ∧
      ∀ z, (e z : ℂ) = g z := by
  obtain ⟨g, hgc, hgd, hgbij, hginj⟩ := exists_sourceChamber_caratheodoryMap
  have himage : g '' closedBall 0 1 = closure sourceBoundedChamber := by
    rw [← closure_ball (0 : ℂ) one_ne_zero]
    exact (TauCeti.image_closure_eq_closure_image isBounded_ball
      (by simpa [closure_ball (0 : ℂ) one_ne_zero] using hgc)
      (fun _ _ ↦ rfl)).trans (congrArg closure hgbij.image_eq)
  have hclosedBij : BijOn g (closedBall 0 1) (closure sourceBoundedChamber) :=
    himage ▸ hginj.bijOn_image
  letI : CompactSpace (closedBall (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  let e : closedBall (0 : ℂ) 1 ≃ₜ closure sourceBoundedChamber :=
    Continuous.homeoOfEquivCompactToT2 (f := hclosedBij.equiv g)
      (hgc.mapsToRestrict hclosedBij.mapsTo)
  exact ⟨g, e, hgd, hgbij, fun _ ↦ rfl⟩

/-- The target Carathéodory map packaged as a homeomorphism of closures. -/
theorem exists_targetChamber_closureHomeomorph :
    ∃ (g : ℂ → ℂ) (e : closedBall (0 : ℂ) 1 ≃ₜ closure targetBoundedChamber),
      DifferentiableOn ℂ g (ball 0 1) ∧ BijOn g (ball 0 1) targetBoundedChamber ∧
      ∀ z, (e z : ℂ) = g z := by
  obtain ⟨g, hgc, hgd, hgbij, hginj⟩ := exists_targetChamber_caratheodoryMap
  have himage : g '' closedBall 0 1 = closure targetBoundedChamber := by
    rw [← closure_ball (0 : ℂ) one_ne_zero]
    exact (TauCeti.image_closure_eq_closure_image isBounded_ball
      (by simpa [closure_ball (0 : ℂ) one_ne_zero] using hgc)
      (fun _ _ ↦ rfl)).trans (congrArg closure hgbij.image_eq)
  have hclosedBij : BijOn g (closedBall 0 1) (closure targetBoundedChamber) :=
    himage ▸ hginj.bijOn_image
  letI : CompactSpace (closedBall (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  let e : closedBall (0 : ℂ) 1 ≃ₜ closure targetBoundedChamber :=
    Continuous.homeoOfEquivCompactToT2 (f := hclosedBij.equiv g)
      (hgc.mapsToRestrict hclosedBij.mapsTo)
  exact ⟨g, e, hgd, hgbij, fun _ ↦ rfl⟩


end SphereSixComplex.Periods.SourceChamberTopology

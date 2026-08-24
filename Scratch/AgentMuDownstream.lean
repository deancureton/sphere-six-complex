import SphereSixComplex.Periods.EstablishedFuchsianTorsorDescent

/-!
# Audit of the repaired affine-torsor descent contract in the actual period pipeline

This file does not use `establishedOrbifoldAffineLineTorsorTwoChartDescent` (which is the
statement under repair).  It records the cusp-normalization laws needed to exclude the known
counterexample, proves those laws for both concrete callers (`mu` and `beta`), and below checks
that a descent theorem with this strengthened input has exactly the output consumed by the
period construction.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods.AgentMuDownstream

open SphereSixComplex.TriangleGroup

/-- The normalization is an honest holomorphic affine trivialization at the cusp.  The first
field is the fibre-affine law, the second is the analytic law, and the third says that it
conjugates the parabolic affine substitution to invariance. -/
structure SoundCuspNormalization
    (P : OrbifoldAffineLineTorsorDescentProblem) : Prop where
  sub : ∀ z u v,
    P.cuspNormalize z u - P.cuspNormalize z v = u - v
  holomorphic : ∀ s : UpperHalfPlane → ℂ, MDiff s →
    MDiff (fun z ↦ P.cuspNormalize z (s z))
  equivariant : ∀ z u,
    P.cuspNormalize (fuchsianSourceAction g₀ • z) (P.affineCusp z u) =
      P.cuspNormalize z u

/-- Difference preservation forces the normalizer to be a translation in every fibre; hence the
adversarial value-dependent normalizer from the counterexample is excluded. -/
theorem SoundCuspNormalization.eq_add_origin
    {P : OrbifoldAffineLineTorsorDescentProblem}
    (h : SoundCuspNormalization P) (z : UpperHalfPlane) (u : ℂ) :
    P.cuspNormalize z u = u + P.cuspNormalize z 0 := by
  have hsub := h.sub z u 0
  linear_combination hsub

/-- The repaired fields turn the supplied cusp primitive into an invariant holomorphic
normalized section—the precise local datum needed before removable-singularity descent. -/
theorem SoundCuspNormalization.normalized_cuspSection_spec
    {P : OrbifoldAffineLineTorsorDescentProblem}
    (h : SoundCuspNormalization P) :
    MDiff (fun z ↦ P.cuspNormalize z (P.cuspSection z)) ∧
      (∀ z, P.cuspNormalize (fuchsianSourceAction g₀ • z)
          (P.cuspSection (fuchsianSourceAction g₀ • z)) =
        P.cuspNormalize z (P.cuspSection z)) := by
  refine ⟨h.holomorphic P.cuspSection P.cuspSection_holomorphic, ?_⟩
  intro z
  rw [P.cuspSection_equivariant]
  exact h.equivariant z (P.cuspSection z)

variable (E : EstablishedFuchsianModularParameter)
variable (F : ExactLiftedModularNegOneFrame E)

/-- The concrete `mu` normalizer is the identity, so it satisfies the repaired contract. -/
theorem fuchsianMu_soundCuspNormalization :
    SoundCuspNormalization (fuchsianMuDescentProblem E F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z u v
    simp [fuchsianMuDescentProblem]
  · intro s hs
    simpa [fuchsianMuDescentProblem] using hs
  · intro z u
    simp [fuchsianMuDescentProblem]

/-- The concrete `beta` normalizer `beta + tau` is holomorphic and turns the cusp translation
`beta ↦ beta + 1` into an invariant quantity. -/
theorem fuchsianBeta_soundCuspNormalization (Dmu : MuTorsorCechLocalData E) :
    SoundCuspNormalization (fuchsianBetaDescentProblem E F Dmu) := by
  have htau : MDiff (fun z ↦ (E.modularParameter.tau z : ℂ)) := by
    intro z
    exact (E.modularParameter.tau z).mdifferentiable_coe.comp z
      (E.modularParameter.tau_holomorphic z)
  refine ⟨?_, ?_, ?_⟩
  · intro z u v
    simp [fuchsianBetaDescentProblem]
  · intro s hs
    simp only [fuchsianBetaDescentProblem]
    change MDiff (s + fun z ↦ (E.modularParameter.tau z : ℂ))
    exact hs.add htau
  · intro z u
    have ht := congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
      (E.modularParameter.equivariant g₀ z)
    rw [rhoTauReal_g0_smul] at ht
    simp only [fuchsianBetaDescentProblem]
    rw [ht]
    ring

/-- Candidate repaired theorem signature.  This is deliberately a proposition in the audit:
the file checks the signature's concrete callers without postulating the analytic theorem. -/
def SoundTwoChartDescentPrinciple : Prop :=
  ∀ P : OrbifoldAffineLineTorsorDescentProblem,
    SoundCuspNormalization P → Nonempty P.TwoChartSections

/-- The exact conversion performed by the first downstream caller.  Keeping this conversion in
the audit ensures the repaired theorem still supplies every field consumed by the `mu` Cech
splitter. -/
noncomputable def muAffineCechSectionsOfTwoChart
    (S : (fuchsianMuDescentProblem E F).TwoChartSections) :
    MuAffineCechSections E F where
  sectionZero := S.sectionZero
  sectionInfinity := S.sectionInfinity
  sectionZero_holomorphic := S.sectionZero_holomorphic
  sectionInfinity_holomorphic := S.sectionInfinity_holomorphic
  sectionZero_one := by
    intro z
    exact S.sectionZero_one z
  sectionZero_two := by
    intro z
    exact S.sectionZero_two z
  sectionInfinity_one := by
    intro z hz
    exact S.sectionInfinity_one z hz
  sectionInfinity_two := by
    intro z hz
    exact S.sectionInfinity_two z hz
  overlapCocycle := S.overlapCocycle
  overlapCocycle_holomorphic := S.overlapCocycle_holomorphic
  section_mismatch := S.section_mismatch
  sectionInfinity_cusp_bounded := S.sectionInfinity_normalized_cusp_bounded

/-- The exact conversion performed by the second downstream caller. -/
noncomputable def betaAffineCechSectionsOfTwoChart
    (Dmu : MuTorsorCechLocalData E)
    (S : (fuchsianBetaDescentProblem E F Dmu).TwoChartSections) :
    BetaAffineCechSections E (descendedFuchsianMu E Dmu) := by
  refine ⟨{
    zeroRegion := Set.univ
    infinityRegion := liftedInfinityRegion E
    zeroRegion_open := isOpen_univ
    infinityRegion_open := liftedInfinityRegion_open E
    regions_cover := Set.univ_union _
    zeroRegion_invariant := by simp
    infinityRegion_invariant := liftedInfinityRegion_invariant E
    sectionZero := S.sectionZero
    sectionInfinity := S.sectionInfinity
    sectionZero_holomorphic := fun z _ ↦ S.sectionZero_holomorphic z
    sectionInfinity_holomorphic := S.sectionInfinity_holomorphic
    sectionZero_one := ?_
    sectionZero_two := ?_
    sectionInfinity_one := ?_
    sectionInfinity_two := ?_
    overlapCocycle := S.overlapCocycle
    overlapCocycle_holomorphic := S.overlapCocycle_holomorphic
    infinity_coordinate_ne_zero := fun _ hz ↦ hz
    section_mismatch := ?_
    cusp_subset_infinity := fuchsianCuspRegion_subset_liftedInfinityRegion E F
    sectionInfinity_add_tau_cusp_bounded := S.sectionInfinity_normalized_cusp_bounded
    infinity_coordinate_cusp_bounded := F.infinity_coordinate_cusp_bounded E }⟩
  · intro z _
    convert S.sectionZero_one z using 1
    simp [fuchsianBetaDescentProblem, fuchsianBetaAffineOne, fuchsianBetaParameter,
      betaCocycleOne]
    ring
  · intro z _
    convert S.sectionZero_two z using 1
    simp [fuchsianBetaDescentProblem, fuchsianBetaAffineTwo, fuchsianBetaParameter,
      betaCocycleTwo]
    ring
  · intro z hz
    convert S.sectionInfinity_one z hz using 1
    simp [fuchsianBetaDescentProblem, fuchsianBetaAffineOne, fuchsianBetaParameter,
      betaCocycleOne]
    ring
  · intro z hz
    convert S.sectionInfinity_two z hz using 1
    simp [fuchsianBetaDescentProblem, fuchsianBetaAffineTwo, fuchsianBetaParameter,
      betaCocycleTwo]
    ring
  · intro z hz
    simpa [fuchsianBetaDescentProblem] using S.section_mismatch z hz.2

/-- End-to-end downstream check.  If the analytic theorem is proved with the repaired cusp
contract, then the concrete `mu` call produces its Cech data; the selected descended `mu` then
defines the concrete `beta` call; and that output produces precisely the local-period package
consumed by the rest of the construction. -/
theorem soundTwoChartDescent_reaches_actualPeriodLocalData
    (F : ExactLiftedModularNegOneFrame E)
    (hdescent : SoundTwoChartDescentPrinciple) :
    Nonempty (FuchsianPeriodLocalData E) := by
  obtain ⟨SmuRaw⟩ := hdescent (fuchsianMuDescentProblem E F)
    (fuchsianMu_soundCuspNormalization E F)
  let Smu : MuAffineCechSections E F :=
    muAffineCechSectionsOfTwoChart E F SmuRaw
  let Dmu : MuTorsorCechLocalData E := Smu.toLocalData E F
  obtain ⟨SbetaRaw⟩ := hdescent (fuchsianBetaDescentProblem E F Dmu)
    (fuchsianBeta_soundCuspNormalization E F Dmu)
  let Sbeta : BetaAffineCechSections E (descendedFuchsianMu E Dmu) :=
    betaAffineCechSectionsOfTwoChart E F Dmu SbetaRaw
  exact ⟨{
    muLocal := Dmu
    betaLocal := Sbeta.data }⟩

/-- The downstream check continues through the already-proved Cech splitters and period
assembly, all the way to the nondegenerate period family used by `PaperAnalyticData`. -/
theorem soundTwoChartDescent_reaches_actualPeriodFunctions
    (F : ExactLiftedModularNegOneFrame E)
    (hdescent : SoundTwoChartDescentPrinciple) :
    Nonempty (PeriodFunctions E.modularParameter.toTriangleUniformization) := by
  obtain ⟨D⟩ := soundTwoChartDescent_reaches_actualPeriodLocalData E F hdescent
  exact exists_assembledFuchsianPeriodFunctions E D

#print axioms fuchsianMu_soundCuspNormalization
#print axioms fuchsianBeta_soundCuspNormalization
#print axioms SoundCuspNormalization.eq_add_origin
#print axioms SoundCuspNormalization.normalized_cuspSection_spec
#print axioms soundTwoChartDescent_reaches_actualPeriodLocalData
#print axioms soundTwoChartDescent_reaches_actualPeriodFunctions

end SphereSixComplex.Periods.AgentMuDownstream

import SphereSixComplex.Periods.EstablishedFuchsianTorsorDescent

/-!
# Downstream audit for the concrete `beta` affine torsor

This file uses only authoritative project modules.  It checks that the normalization repair
suggested for general affine-torsor descent is genuinely available for the concrete `beta`
problem, and that the unchanged `TwoChartSections` output is exactly sufficient for the actual
period construction.  The disputed general descent axiom is never invoked.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods.AgentBetaDownstream

open SphereSixComplex.TriangleGroup

/-- A cusp normalization is affine with linear part one and is invariant under the combined
parabolic fibre substitution.  These are necessary hypotheses missing from the original general
descent statement. -/
structure HasCompatibleCuspNormalization
    (P : OrbifoldAffineLineTorsorDescentProblem) : Prop where
  sub : ∀ z u v,
    P.cuspNormalize z u - P.cuspNormalize z v = u - v
  cusp : ∀ z u,
    P.cuspNormalize (fuchsianSourceAction g₀ • z) (P.affineCusp z u) =
      P.cuspNormalize z u

/-- Holomorphic sections remain holomorphic after cusp normalization.  This is a natural
analytic companion to the two algebraic normalization laws. -/
def CuspNormalizationPreservesHolomorphicSections
    (P : OrbifoldAffineLineTorsorDescentProblem) : Prop :=
  ∀ s : UpperHalfPlane → ℂ, MDiff s →
    MDiff (fun z ↦ P.cuspNormalize z (s z))

variable (E : EstablishedFuchsianModularParameter)

private theorem tau_coe_holomorphic :
    MDiff (fun z ↦ (E.modularParameter.tau z : ℂ)) := by
  intro z
  exact (E.modularParameter.tau z).mdifferentiable_coe.comp z
    (E.modularParameter.tau_holomorphic z)

/-- The concrete beta normalization `beta + tau` preserves differences. -/
theorem fuchsianBeta_normalize_sub
    (F : ExactLiftedModularNegOneFrame E) (Dmu : MuTorsorCechLocalData E)
    (z : UpperHalfPlane) (u v : ℂ) :
    (fuchsianBetaDescentProblem E F Dmu).cuspNormalize z u -
        (fuchsianBetaDescentProblem E F Dmu).cuspNormalize z v = u - v := by
  simp only [fuchsianBetaDescentProblem]
  ring

/-- The concrete beta normalization is invariant under the inverse-parabolic substitution:
`(beta + 1) + (tau - 1) = beta + tau`. -/
theorem fuchsianBeta_normalize_cusp
    (F : ExactLiftedModularNegOneFrame E) (Dmu : MuTorsorCechLocalData E)
    (z : UpperHalfPlane) (u : ℂ) :
    (fuchsianBetaDescentProblem E F Dmu).cuspNormalize
        (fuchsianSourceAction g₀ • z)
        ((fuchsianBetaDescentProblem E F Dmu).affineCusp z u) =
      (fuchsianBetaDescentProblem E F Dmu).cuspNormalize z u := by
  have htau := congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
    (E.modularParameter.equivariant g₀ z)
  rw [rhoTauReal_g0_smul] at htau
  simp only [fuchsianBetaDescentProblem]
  rw [htau]
  ring

/-- Thus the beta call site can discharge the complete algebraic normalization repair. -/
theorem fuchsianBeta_hasCompatibleCuspNormalization
    (F : ExactLiftedModularNegOneFrame E) (Dmu : MuTorsorCechLocalData E) :
    HasCompatibleCuspNormalization (fuchsianBetaDescentProblem E F Dmu) :=
  ⟨fuchsianBeta_normalize_sub E F Dmu,
    fuchsianBeta_normalize_cusp E F Dmu⟩

/-- The same concrete normalization also preserves holomorphic sections. -/
theorem fuchsianBeta_normalization_preserves_holomorphic
    (F : ExactLiftedModularNegOneFrame E) (Dmu : MuTorsorCechLocalData E) :
    CuspNormalizationPreservesHolomorphicSections
      (fuchsianBetaDescentProblem E F Dmu) := by
  intro s hs z
  simp only [fuchsianBetaDescentProblem]
  exact (hs z).add (tau_coe_holomorphic E z)

/-- In the beta application the homogeneous torsor is the structure sheaf: both linear parts and
both chosen frames are identically one, and the transition coefficient is identically one. -/
theorem fuchsianBeta_structureSheaf_fields
    (F : ExactLiftedModularNegOneFrame E) (Dmu : MuTorsorCechLocalData E) :
    (∀ z, (fuchsianBetaDescentProblem E F Dmu).linearOne z = 1) ∧
      (∀ z, (fuchsianBetaDescentProblem E F Dmu).linearTwo z = 1) ∧
      (∀ z, (fuchsianBetaDescentProblem E F Dmu).frameZero z = 1) ∧
      (∀ z, (fuchsianBetaDescentProblem E F Dmu).frameInfinity z = 1) ∧
      (∀ q, (fuchsianBetaDescentProblem E F Dmu).frameTransition q = 1) ∧
      (fuchsianBetaDescentProblem E F Dmu).frameOrderOne = 0 ∧
      (fuchsianBetaDescentProblem E F Dmu).frameOrderTwo = 0 := by
  simp [fuchsianBetaDescentProblem]

/-- The concrete `mu` problem satisfies the same candidate repair, so a repaired general theorem
can be applied at both successive call sites in the actual construction. -/
theorem fuchsianMu_hasCompatibleCuspNormalization
    (F : ExactLiftedModularNegOneFrame E) :
    HasCompatibleCuspNormalization (fuchsianMuDescentProblem E F) := by
  constructor <;> simp [fuchsianMuDescentProblem]

theorem fuchsianMu_normalization_preserves_holomorphic
    (F : ExactLiftedModularNegOneFrame E) :
    CuspNormalizationPreservesHolomorphicSections
      (fuchsianMuDescentProblem E F) := by
  intro s hs
  simpa only [fuchsianMuDescentProblem] using hs

/-- Candidate normalization-only repair of the general theorem.  This is merely a proposition,
not an axiom or a claimed proof. -/
def NormalizationCompatibleAffineDescent : Prop :=
  ∀ P : OrbifoldAffineLineTorsorDescentProblem,
    HasCompatibleCuspNormalization P →
      CuspNormalizationPreservesHolomorphicSections P →
      Nonempty P.TwoChartSections

/-- If the repaired theorem is supplied, the concrete beta problem is a valid application. -/
theorem betaTwoChartSections_of_normalizationCompatibleDescent
    (hdescent : NormalizationCompatibleAffineDescent)
    (F : ExactLiftedModularNegOneFrame E) (Dmu : MuTorsorCechLocalData E) :
    Nonempty (fuchsianBetaDescentProblem E F Dmu).TwoChartSections :=
  hdescent _ (fuchsianBeta_hasCompatibleCuspNormalization E F Dmu)
    (fuchsianBeta_normalization_preserves_holomorphic E F Dmu)

/-- Convert a general two-chart witness for the concrete `mu` problem into the exact finite and
infinity chart package used to define `MuTorsorCechLocalData`. -/
noncomputable def muCechSectionsOfTwoChartSections
    (F : ExactLiftedModularNegOneFrame E)
    (S : (fuchsianMuDescentProblem E F).TwoChartSections) :
    MuAffineCechSections E F where
  sectionZero := S.sectionZero
  sectionInfinity := S.sectionInfinity
  sectionZero_holomorphic := S.sectionZero_holomorphic
  sectionInfinity_holomorphic := S.sectionInfinity_holomorphic
  sectionZero_one := S.sectionZero_one
  sectionZero_two := S.sectionZero_two
  sectionInfinity_one := S.sectionInfinity_one
  sectionInfinity_two := S.sectionInfinity_two
  overlapCocycle := S.overlapCocycle
  overlapCocycle_holomorphic := S.overlapCocycle_holomorphic
  section_mismatch := S.section_mismatch
  sectionInfinity_cusp_bounded := S.sectionInfinity_normalized_cusp_bounded

/-- Convert the general two-chart output into the exact concrete beta Cech local data consumed by
`exists_globalFuchsianBeta`.  This is the downstream body of the authoritative conversion, made
explicit here so the audit does not call the disputed theorem. -/
noncomputable def betaLocalDataOfTwoChartSections
    (F : ExactLiftedModularNegOneFrame E) (Dmu : MuTorsorCechLocalData E)
    (S : (fuchsianBetaDescentProblem E F Dmu).TwoChartSections) :
    BetaTorsorCechLocalData E (descendedFuchsianMu E Dmu) where
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
  sectionZero_one := by
    intro z _
    convert S.sectionZero_one z using 1
    simp [fuchsianBetaDescentProblem, fuchsianBetaAffineOne, fuchsianBetaParameter,
      betaCocycleOne]
    ring
  sectionZero_two := by
    intro z _
    convert S.sectionZero_two z using 1
    simp [fuchsianBetaDescentProblem, fuchsianBetaAffineTwo, fuchsianBetaParameter,
      betaCocycleTwo]
    ring
  sectionInfinity_one := by
    intro z hz
    convert S.sectionInfinity_one z hz using 1
    simp [fuchsianBetaDescentProblem, fuchsianBetaAffineOne, fuchsianBetaParameter,
      betaCocycleOne]
    ring
  sectionInfinity_two := by
    intro z hz
    convert S.sectionInfinity_two z hz using 1
    simp [fuchsianBetaDescentProblem, fuchsianBetaAffineTwo, fuchsianBetaParameter,
      betaCocycleTwo]
    ring
  overlapCocycle := S.overlapCocycle
  overlapCocycle_holomorphic := S.overlapCocycle_holomorphic
  infinity_coordinate_ne_zero := fun _ hz ↦ hz
  section_mismatch := by
    intro z hz
    simpa [fuchsianBetaDescentProblem] using S.section_mismatch z hz.2
  cusp_subset_infinity := fuchsianCuspRegion_subset_liftedInfinityRegion E F
  sectionInfinity_add_tau_cusp_bounded := S.sectionInfinity_normalized_cusp_bounded
  infinity_coordinate_cusp_bounded := F.infinity_coordinate_cusp_bounded E

/-- A beta two-chart witness immediately supplies the global holomorphic equivariant beta used by
the paper, through the already-proved structure-sheaf Cech splitting. -/
theorem exists_globalBeta_of_twoChartSections
    (F : ExactLiftedModularNegOneFrame E) (Dmu : MuTorsorCechLocalData E)
    (S : (fuchsianBetaDescentProblem E F Dmu).TwoChartSections) :
    ∃ beta : UpperHalfPlane → ℂ,
      MDiff beta ∧
      (∀ z, beta (fuchsianSourceAction g₁ • z) =
        beta z + 2 - 6 * (1 - descendedFuchsianMu E Dmu z) ^ 2 /
          E.modularParameter.tau z) ∧
      (∀ z, beta (fuchsianSourceAction g₂ • z) =
        beta z - 3 - 6 * descendedFuchsianMu E Dmu z ^ 2 /
          E.modularParameter.tau z) ∧
      BoundedOn (fun z ↦ beta z + E.modularParameter.tau z)
        fuchsianCuspRegion :=
  exists_globalFuchsianBeta E (betaLocalDataOfTwoChartSections E F Dmu S)

/-- The concrete repaired-interface application reaches the same global beta conclusion without
calling the original general descent axiom. -/
theorem exists_globalBeta_of_normalizationCompatibleDescent
    (hdescent : NormalizationCompatibleAffineDescent)
    (F : ExactLiftedModularNegOneFrame E) (Dmu : MuTorsorCechLocalData E) :
    ∃ beta : UpperHalfPlane → ℂ,
      MDiff beta ∧
      (∀ z, beta (fuchsianSourceAction g₁ • z) =
        beta z + 2 - 6 * (1 - descendedFuchsianMu E Dmu z) ^ 2 /
          E.modularParameter.tau z) ∧
      (∀ z, beta (fuchsianSourceAction g₂ • z) =
        beta z - 3 - 6 * descendedFuchsianMu E Dmu z ^ 2 /
          E.modularParameter.tau z) ∧
      BoundedOn (fun z ↦ beta z + E.modularParameter.tau z)
        fuchsianCuspRegion := by
  obtain ⟨S⟩ := betaTwoChartSections_of_normalizationCompatibleDescent E hdescent F Dmu
  exact exists_globalBeta_of_twoChartSections E F Dmu S

/-- Given the two concrete chart witnesses, assemble exactly the local-period package consumed by
the paper.  No general affine-torsor theorem is used in this definition. -/
noncomputable def periodLocalDataOfTwoChartSections
    (F : ExactLiftedModularNegOneFrame E)
    (Smu : (fuchsianMuDescentProblem E F).TwoChartSections)
    (Sbeta : (fuchsianBetaDescentProblem E F
      ((muCechSectionsOfTwoChartSections E F Smu).toLocalData E F)).TwoChartSections) :
    FuchsianPeriodLocalData E := by
  let M := muCechSectionsOfTwoChartSections E F Smu
  let B : BetaAffineCechSections E
      (descendedFuchsianMu E (M.toLocalData E F)) :=
    ⟨betaLocalDataOfTwoChartSections E F (M.toLocalData E F) Sbeta⟩
  exact exactFuchsianPeriodLocalData E F M B

/-- The two repaired-theorem outputs reach the actual nondegenerate period family. -/
theorem exists_actualPeriodFunctions_of_twoChartSections
    (F : ExactLiftedModularNegOneFrame E)
    (Smu : (fuchsianMuDescentProblem E F).TwoChartSections)
    (Sbeta : (fuchsianBetaDescentProblem E F
      ((muCechSectionsOfTwoChartSections E F Smu).toLocalData E F)).TwoChartSections) :
    Nonempty (PeriodFunctions E.modularParameter.toTriangleUniformization) :=
  exists_assembledFuchsianPeriodFunctions E
    (periodLocalDataOfTwoChartSections E F Smu Sbeta)

/-- Consequently, the normalization-compatible signature is sufficient at every downstream call
site: assuming that analytic theorem, the actual period functions follow.  What remains is a proof
of `NormalizationCompatibleAffineDescent`, not any additional paper-specific beta field. -/
theorem normalizationCompatibleDescent_suffices_for_actualConstruction
    (hdescent : NormalizationCompatibleAffineDescent)
    (F : ExactLiftedModularNegOneFrame E) :
    Nonempty (PeriodFunctions E.modularParameter.toTriangleUniformization) := by
  obtain ⟨Smu⟩ := hdescent (fuchsianMuDescentProblem E F)
    (fuchsianMu_hasCompatibleCuspNormalization E F)
    (fuchsianMu_normalization_preserves_holomorphic E F)
  let M := muCechSectionsOfTwoChartSections E F Smu
  obtain ⟨Sbeta⟩ := hdescent (fuchsianBetaDescentProblem E F (M.toLocalData E F))
    (fuchsianBeta_hasCompatibleCuspNormalization E F (M.toLocalData E F))
    (fuchsianBeta_normalization_preserves_holomorphic E F (M.toLocalData E F))
  exact exists_actualPeriodFunctions_of_twoChartSections E F Smu Sbeta

#print axioms fuchsianBeta_normalize_sub
#print axioms fuchsianBeta_normalize_cusp
#print axioms fuchsianBeta_hasCompatibleCuspNormalization
#print axioms fuchsianBeta_normalization_preserves_holomorphic
#print axioms fuchsianBeta_structureSheaf_fields
#print axioms fuchsianMu_hasCompatibleCuspNormalization
#print axioms fuchsianMu_normalization_preserves_holomorphic
#print axioms muCechSectionsOfTwoChartSections
#print axioms betaLocalDataOfTwoChartSections
#print axioms exists_globalBeta_of_twoChartSections
#print axioms exists_globalBeta_of_normalizationCompatibleDescent
#print axioms periodLocalDataOfTwoChartSections
#print axioms exists_actualPeriodFunctions_of_twoChartSections
#print axioms normalizationCompatibleDescent_suffices_for_actualConstruction

end SphereSixComplex.Periods.AgentBetaDownstream

module

public import SphereSixComplex.Geometry.PaperFillingCompactCores
import all SphereSixComplex.LatticeData

/-!
# Compact radial cores in a toric cusp filling

Compactness of a lattice quotient is reduced to a cocompact-fundamental-domain
statement for the polarized toric degeneration.  The reduction is completely generic and the
remaining datum mentions only the toric model, its lattice action, and compact representatives.
-/

open CategoryTheory TopologicalSpace Topology

namespace SphereSixComplex.Geometry.CuspFillingRadialCompactness

open Set SphereSixComplex.Periods
open CuspFilling CuspLocalPhaseAction CuspPuncturedCollarBridge
open CuspPeriodExpansion StandardInfiniteA2ToricModel
open StandardInfiniteA2ToricQuantitativeRegions
open CuspPhaseEstimates.CuspPeriodExpansion
open CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate

noncomputable section

/-- The `ℓ¹` size of a real two-vector. -/
@[expose] public def realL1 (x : Fin 2 → ℝ) : ℝ :=
  |x 0| + |x 1|

public theorem realL1_nonneg (x : Fin 2 → ℝ) : 0 ≤ realL1 x :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

public theorem realL1_eq_zero_iff (x : Fin 2 → ℝ) : realL1 x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    fin_cases i
    · have hx : |x 0| = 0 := by
        simp only [realL1] at h
        nlinarith [abs_nonneg (x 0), abs_nonneg (x 1)]
      simpa using abs_eq_zero.mp hx
    · have hx : |x 1| = 0 := by
        simp only [realL1] at h
        nlinarith [abs_nonneg (x 0), abs_nonneg (x 1)]
      simpa using abs_eq_zero.mp hx
  · rintro rfl
    simp [realL1]

@[simp]
public theorem realL1_neg (x : Fin 2 → ℝ) : realL1 (-x) = realL1 x := by
  simp [realL1]

/-- The real inverse of the integral fan shear `B₀`. -/
@[expose] public def realFanShearInverse (d : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![-d 1, d 0]

@[simp]
public theorem realFanShearInverse_add (x y : Fin 2 → ℝ) :
    realFanShearInverse (x + y) = realFanShearInverse x + realFanShearInverse y := by
  ext i
  fin_cases i <;> simp [realFanShearInverse, add_comm]

@[simp]
public theorem realFanShearInverse_smul (c : ℝ) (x : Fin 2 → ℝ) :
    realFanShearInverse (c • x) = c • realFanShearInverse x := by
  ext i
  fin_cases i <;> simp [realFanShearInverse]

@[simp]
public theorem realL1_realFanShearInverse (d : Fin 2 → ℝ) :
    realL1 (realFanShearInverse d) = realL1 d := by
  simp [realL1, realFanShearInverse, add_comm]

/-- Coordinatewise integral floor of a real two-vector. -/
public def floorVector (x : Fin 2 → ℝ) : ParameterLattice :=
  fun i ↦ ⌊x i⌋

/-- Coordinatewise fractional part of a real two-vector. -/
public def fractionalPartVector (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i ↦ x i - (floorVector x i : ℝ)

public theorem fractionalPartVector_nonneg (x : Fin 2 → ℝ) (i : Fin 2) :
    0 ≤ fractionalPartVector x i := by
  exact sub_nonneg.mpr (Int.floor_le (x i))

public theorem fractionalPartVector_lt_one (x : Fin 2 → ℝ) (i : Fin 2) :
    fractionalPartVector x i < 1 := by
  change Int.fract (x i) < 1
  exact Int.fract_lt_one _

public theorem realL1_fractionalPartVector_le_two (x : Fin 2 → ℝ) :
    realL1 (fractionalPartVector x) ≤ 2 := by
  have h0 := fractionalPartVector_nonneg x 0
  have h1 := fractionalPartVector_nonneg x 1
  have h0' := fractionalPartVector_lt_one x 0
  have h1' := fractionalPartVector_lt_one x 1
  rw [realL1, abs_of_nonneg h0, abs_of_nonneg h1]
  linarith

/-- The phase-corrected real fan displacement at a nonzero height. -/
@[expose] public noncomputable def effectiveFanDisplacement
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (q : ℂ) (d : Fin 2 → ℝ) :
    Fin 2 → ℝ :=
  d + fun i ↦
    (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseLogMatrix
      N q).mulVec (realFanShearInverse d) i / Real.log ‖q‖

/-- The effective fan displacement is real-linear. -/
@[expose] public noncomputable def effectiveFanDisplacementLinearMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (q : ℂ) :
    (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun := effectiveFanDisplacement N q
  map_add' x y := by
    ext i
    fin_cases i <;>
      simp [effectiveFanDisplacement, realFanShearInverse, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two] <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;>
      simp [effectiveFanDisplacement, realFanShearInverse, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two] <;> ring

@[simp]
public theorem effectiveFanDisplacementLinearMap_apply
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (q : ℂ) (d : Fin 2 → ℝ) :
    effectiveFanDisplacementLinearMap N q d = effectiveFanDisplacement N q d :=
  rfl

public theorem phaseLog_mulVec_real_le
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) {q : ℂ} {A : ℝ}
    (hA : ∀ i j, |CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseLogMatrix
      N q i j| ≤ A) (x : Fin 2 → ℝ) (i : Fin 2) :
    |(CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseLogMatrix
      N q).mulVec x i| ≤ A * realL1 x := by
  let R :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseLogMatrix N q
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, realL1]
  calc
    |R i 0 * x 0 + R i 1 * x 1| ≤ |R i 0 * x 0| + |R i 1 * x 1| :=
      abs_add_le _ _
    _ = |R i 0| * |x 0| + |R i 1| * |x 1| := by rw [abs_mul, abs_mul]
    _ ≤ A * |x 0| + A * |x 1| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (hA i 0) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (hA i 1) (abs_nonneg _))
    _ = A * (|x 0| + |x 1|) := by ring

public theorem realFanShearInverse_shearVector (lambda : ParameterLattice) :
    realFanShearInverse (fun i ↦ (shearVector lambda i : ℝ)) = realParameter lambda := by
  funext i
  fin_cases i <;>
    simp [realFanShearInverse, shearVector, SphereSixComplex.LatticeData.B₀,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, realParameter]

public theorem effectiveFanDisplacement_shearVector
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (q : ℂ) (lambda : ParameterLattice) :
    effectiveFanDisplacement N q (fun i ↦ (shearVector lambda i : ℝ)) =
      fun i ↦ (shearVector lambda i : ℝ) +
        (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseLogMatrix
          N q).mulVec (realParameter lambda) i / Real.log ‖q‖ := by
  rw [effectiveFanDisplacement, realFanShearInverse_shearVector]
  rfl

public theorem exists_upper_barycentric_perturbation_lower
    (u e : Fin 2 → ℝ) (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1)
    (he : ∀ i, |e i| ≤ epsilon) :
    ∃ upper : Bool, ∀ i,
      -2 * epsilon ≤ a2Barycentric upper (0 : ParameterLattice) (u + e) i := by
  have he0 := (abs_le.mp (he 0))
  have he1 := (abs_le.mp (he 1))
  by_cases hsum : u 0 + u 1 ≤ 1
  · refine ⟨false, fun i ↦ ?_⟩
    fin_cases i <;> simp [a2Barycentric] <;>
      linarith [hu0 0, hu0 1, hu1 0, hu1 1]
  · refine ⟨true, fun i ↦ ?_⟩
    have hsum' : 1 ≤ u 0 + u 1 := le_of_not_ge hsum
    fin_cases i <;> simp [a2Barycentric] <;>
      linarith [hu0 0, hu0 1, hu1 0, hu1 1]

/-- The quotient of a local toric degeneration by a fixed-point-free phase-corrected lattice
action. -/
public noncomputable abbrev PhaseCorrectedToricQuotient
    {M : Model} {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (F : C.FixedPointEstimates) :=
  letI := (C.toCuspActionData F).psiAction
  MulAction.orbitRel.Quotient (Multiplicative ParameterLattice) (LocalCarrier M r)

/-- The height radius descended to a phase-corrected toric quotient. -/
@[expose] public noncomputable def phaseCorrectedQuotientRadius
    {M : Model} {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (F : C.FixedPointEstimates) : PhaseCorrectedToricQuotient C F → ℝ := by
  let _ := (C.toCuspActionData F).psiAction
  exact Quotient.lift (fun p : LocalCarrier M r ↦ ‖M.t p‖) (by
    intro p q hpq
    change MulAction.orbitRel (Multiplicative ParameterLattice) _ p q at hpq
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hpq
    obtain ⟨lambda, rfl⟩ := hpq
    exact congrArg norm ((C.toCuspActionData F).preserves_t lambda q))

@[simp]
public theorem phaseCorrectedQuotientRadius_mk
    {M : Model} {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (F : C.FixedPointEstimates) (p : LocalCarrier M r) :
    phaseCorrectedQuotientRadius C F (Quotient.mk _ p) = ‖M.t p‖ :=
  rfl

/-- Exact cocompactness datum for a polarized toric degeneration over every closed smaller
height disc.  This is the usual compact fundamental-domain assertion for the lattice action;
it is independent of the six-sphere gluing and does not assume compactness of the quotient. -/
public structure RadialSublevelCocompactness
    {M : Model} {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r) : Prop where
  compact_fundamental_domain : ∀ a : ℝ, 0 ≤ a → a < r →
    ∃ K : Set (LocalCarrier M r), IsCompact K ∧
      K ⊆ {p | ‖M.t p‖ ≤ a} ∧
      ∀ p : LocalCarrier M r, ‖M.t p‖ ≤ a →
        ∃ lambda : ParameterLattice, C.psiMap lambda p ∈ K

/-- Concrete bounded-representative form of the required `A₂` toric cocompactness theorem.
Modulo the phase-corrected fan lattice, every point over a closed smaller height disc has a
representative in one of the two fixed affine polydiscs based at the zero vertex. -/
public structure A2TwoChartRadialSublevelRepresentatives
    {M : Model} {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r) : Prop where
  bounded_representative : ∀ a : ℝ, 0 ≤ a → a < r →
    ∃ S : ℝ, ∀ p : LocalCarrier M r, ‖M.t p‖ ≤ a →
      ∃ lambda : ParameterLattice, ∃ upper : Bool,
        (C.psiMap lambda p : M.Carrier) ∈
          closedToricPolydisc M upper (fun _ ↦ 0) S

/-- Bounded representatives in the two fixed affine `A₂` charts supply compact radial
fundamental domains. -/
public theorem radialSublevelCocompactness_of_twoChartRepresentatives
    {M : Model} {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (H : A2TwoChartRadialSublevelRepresentatives C) :
    RadialSublevelCocompactness C := by
  constructor
  intro a ha har
  obtain ⟨S, hS⟩ := H.bounded_representative a ha har
  let polydiscs : Set M.Carrier :=
    closedToricPolydisc M false (fun _ ↦ 0) S ∪
      closedToricPolydisc M true (fun _ ↦ 0) S
  let carrierCore : Set M.Carrier := {p | ‖M.t p‖ ≤ a} ∩ polydiscs
  let K : Set (LocalCarrier M r) := Subtype.val ⁻¹' carrierCore
  have hpolydiscs : IsCompact polydiscs :=
    (compact_closedToricPolydisc M false (fun _ ↦ 0) S).union
      (compact_closedToricPolydisc M true (fun _ ↦ 0) S)
  have hclosedRadius : IsClosed {p : M.Carrier | ‖M.t p‖ ≤ a} :=
    isClosed_le (continuous_norm.comp M.t_holomorphic.continuous) continuous_const
  have hcarrierCore : IsCompact carrierCore := hpolydiscs.inter_left hclosedRadius
  have hcarrierCore_local : carrierCore ⊆ cuspNeighborhood M r := by
    intro p hp
    exact (mem_cuspNeighborhood_iff M r p).2
      (mem_ball_zero_iff.mpr (hp.1.trans_lt har))
  have hK : IsCompact K := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert hcarrierCore using 1
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hp
      exact ⟨⟨p, hcarrierCore_local hp⟩, hp, rfl⟩
  refine ⟨K, hK, ?_, ?_⟩
  · intro p hp
    exact hp.1
  · intro p hp
    obtain ⟨lambda, upper, hlambda⟩ := hS p hp
    refine ⟨lambda, ?_⟩
    change (C.psiMap lambda p : M.Carrier) ∈ carrierCore
    refine ⟨?_, ?_⟩
    · change ‖M.t (C.psiMap lambda p)‖ ≤ a
      rw [C.psiMap_preserves_t]
      exact hp
    · cases upper
      · exact Or.inl hlambda
      · exact Or.inr hlambda

/-- A compact fundamental domain makes each closed radial sublevel of the quotient compact. -/
public theorem phaseCorrectedQuotientRadiusSublevel_isCompact
    {M : Model} {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (F : C.FixedPointEstimates) (H : RadialSublevelCocompactness C)
    (a : ℝ) (ha : 0 ≤ a) (har : a < r) :
    IsCompact {y : PhaseCorrectedToricQuotient C F |
      phaseCorrectedQuotientRadius C F y ≤ a} := by
  let _ := (C.toCuspActionData F).psiAction
  obtain ⟨K, hK, hKsub, hcover⟩ := H.compact_fundamental_domain a ha har
  let R : Setoid (LocalCarrier M r) :=
    MulAction.orbitRel (Multiplicative ParameterLattice) _
  have himage : IsCompact ((Quotient.mk R) '' K) := hK.image continuous_quot_mk
  convert himage using 1
  ext y
  induction y using Quotient.inductionOn with
  | _ p =>
    constructor
    · intro hp
      change ‖M.t p‖ ≤ a at hp
      obtain ⟨lambda, hlambda⟩ := hcover p hp
      refine ⟨C.psiMap lambda p, hlambda, ?_⟩
      apply Quotient.sound
      change MulAction.orbitRel (Multiplicative ParameterLattice) _
        (C.psiMap lambda p) p
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨Multiplicative.ofAdd lambda, ?_⟩
      change (C.toCuspActionData F).psiMap lambda p = C.psiMap lambda p
      exact (C.psiMap_eq_generic F lambda p).symm
    · rintro ⟨q, hq, hqp⟩
      change phaseCorrectedQuotientRadius C F (Quotient.mk _ p) ≤ a
      rw [← hqp, phaseCorrectedQuotientRadius_mk]
      exact hKsub hq

/-- The exact toric cocompactness input specialized to the actual normalized cusp
filling. -/
public def ActualCuspRadialSublevelCocompactness
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) : Prop :=
  RadialSublevelCocompactness
    (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius
        W.localWitness.radius_pos W.localWitness.radius_le)

/-- The concrete two-chart bounded-orbit statement for the actual `A₂` cusp action. -/
public def ActualA2TwoChartRadialSublevelRepresentatives
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) : Prop :=
  A2TwoChartRadialSublevelRepresentatives
    (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius
        W.localWitness.radius_pos W.localWitness.radius_le)

public theorem actual_effectiveFanDisplacement_correction_coord_le
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) (hp : M.t p ≠ 0)
    (d : Fin 2 → ℝ) (i : Fin 2) :
    |(CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseLogMatrix
      N (M.t p)).mulVec (realFanShearInverse d) i / Real.log ‖M.t p‖| ≤
        (1 / 4 : ℝ) * realL1 d := by
  have hnorm_pos : 0 < ‖M.t p‖ := norm_pos_iff.mpr hp
  have hnorm_lt : ‖M.t p‖ < 1 :=
    (mem_ball_zero_iff.mp p.property).trans W.localWitness.radius_lt_one
  have habslog_pos : 0 < |Real.log ‖M.t p‖| :=
    abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hnorm_pos (ne_of_lt hnorm_lt))
  have hvec := phaseLog_mulVec_real_le N
    (W.localWitness.phaseLogMatrix_entry_bound p) (realFanShearInverse d) i
  rw [realL1_realFanShearInverse] at hvec
  rw [abs_div]
  apply (div_le_iff₀ habslog_pos).2
  have hl1 := realL1_nonneg d
  have hdom := W.localWitness.phaseLog_dominates p hp
  nlinarith [W.localWitness.phaseBound_nonneg]

public theorem actual_effectiveFanDisplacement_correction_l1_le
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) (hp : M.t p ≠ 0)
    (d : Fin 2 → ℝ) :
    realL1 (effectiveFanDisplacement N (M.t p) d - d) ≤
      (1 / 2 : ℝ) * realL1 d := by
  have h0 := actual_effectiveFanDisplacement_correction_coord_le W p hp d 0
  have h1 := actual_effectiveFanDisplacement_correction_coord_le W p hp d 1
  simp only [realL1, effectiveFanDisplacement, Pi.sub_apply, Pi.add_apply, add_sub_cancel_left]
  calc
    _ ≤ (1 / 4 : ℝ) * realL1 d + (1 / 4 : ℝ) * realL1 d := add_le_add h0 h1
    _ = (1 / 2 : ℝ) * realL1 d := by ring

public noncomputable def actualEffectiveFanDisplacementEquiv
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) (hp : M.t p ≠ 0) :
    (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  LinearEquiv.ofInjectiveEndo (effectiveFanDisplacementLinearMap N (M.t p)) (by
    intro x y hxy
    let d := x - y
    have hzero : effectiveFanDisplacementLinearMap N (M.t p) d = 0 := by
      change effectiveFanDisplacementLinearMap N (M.t p) (x - y) = 0
      rw [map_sub, hxy, sub_self]
    have hbound := actual_effectiveFanDisplacement_correction_l1_le W p hp d
    have heq : effectiveFanDisplacement N (M.t p) d - d = -d := by
      change effectiveFanDisplacementLinearMap N (M.t p) d - d = -d
      rw [hzero, zero_sub]
    have hl1eq : realL1 (effectiveFanDisplacement N (M.t p) d - d) = realL1 d := by
      rw [heq]
      simp [realL1]
    have hd0 : realL1 d = 0 := by
      rw [hl1eq] at hbound
      nlinarith [realL1_nonneg d]
    have : d = 0 := (realL1_eq_zero_iff d).mp hd0
    exact sub_eq_zero.mp this)

public theorem actual_exists_reduced_rescaledPosition
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) (hp : M.t p ≠ 0) :
    let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
      W.localWitness.radius_pos W.localWitness.radius_le
    ∃ lambda : ParameterLattice, ∃ u e : Fin 2 → ℝ,
      (∀ i, 0 ≤ u i ∧ u i < 1) ∧
      (∀ i, |e i| ≤
        2 * W.localWitness.phaseBound / |Real.log ‖M.t p‖|) ∧
      rescaledPosition M (C.psiMap lambda p) = u + e := by
  let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
    W.localWitness.radius_pos W.localWitness.radius_le
  let L := actualEffectiveFanDisplacementEquiv W p hp
  let x : Fin 2 → ℝ := L.symm (rescaledPosition M p)
  let k : ParameterLattice := -floorVector x
  obtain ⟨lambda, hlambda⟩ := shearVector_surjective k
  let u := fractionalPartVector x
  let e := effectiveFanDisplacement N (M.t p) u - u
  refine ⟨lambda, u, e, ?_, ?_, ?_⟩
  · intro i
    exact ⟨fractionalPartVector_nonneg x i, fractionalPartVector_lt_one x i⟩
  · intro i
    have hnorm_pos : 0 < ‖M.t p‖ := norm_pos_iff.mpr hp
    have hnorm_lt : ‖M.t p‖ < 1 :=
      (mem_ball_zero_iff.mp p.property).trans W.localWitness.radius_lt_one
    have habslog_pos : 0 < |Real.log ‖M.t p‖| :=
      abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hnorm_pos (ne_of_lt hnorm_lt))
    have hvec := phaseLog_mulVec_real_le N
      (W.localWitness.phaseLogMatrix_entry_bound p) (realFanShearInverse u) i
    rw [realL1_realFanShearInverse] at hvec
    have hul1 : realL1 u ≤ 2 := realL1_fractionalPartVector_le_two x
    simp only [e, effectiveFanDisplacement, add_sub_cancel_left]
    change |(phaseLogMatrix N (M.t p)).mulVec (realFanShearInverse u) i /
      Real.log ‖M.t p‖| ≤ _
    rw [abs_div]
    apply (div_le_iff₀ habslog_pos).2
    have hA := W.localWitness.phaseBound_nonneg
    rw [div_mul_cancel₀ _ (ne_of_gt habslog_pos)]
    calc
      _ ≤ W.localWitness.phaseBound * realL1 u := hvec
      _ ≤ W.localWitness.phaseBound * 2 := mul_le_mul_of_nonneg_left hul1 hA
      _ = 2 * W.localWitness.phaseBound := by ring
  · have hdisp :=
      CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.rescaledPosition_psiMap_sub
        N M W.localWitness.radius_lt_one C rfl lambda p hp
    have hdelta : rescaledPosition M (C.psiMap lambda p) - rescaledPosition M p =
        effectiveFanDisplacement N (M.t p)
          (fun i ↦ (shearVector lambda i : ℝ)) := by
      rw [effectiveFanDisplacement_shearVector]
      exact hdisp
    have hdreal : (fun i ↦ (shearVector lambda i : ℝ)) =
        fun i ↦ -(floorVector x i : ℝ) := by
      funext i
      rw [hlambda]
      simp [k]
    calc
      rescaledPosition M (C.psiMap lambda p) = rescaledPosition M p +
          effectiveFanDisplacement N (M.t p)
            (fun i ↦ (shearVector lambda i : ℝ)) := by
              have h := congrArg (fun z ↦ z + rescaledPosition M p) hdelta
              simpa [add_comm] using h
      _ = L x + L (fun i ↦ (shearVector lambda i : ℝ)) := by
        rw [L.apply_symm_apply]
        rfl
      _ = L (x + fun i ↦ (shearVector lambda i : ℝ)) := by rw [map_add]
      _ = L u := by
        congr 1
        rw [hdreal]
        funext i
        simp only [u, fractionalPartVector]
        change x i + -((floorVector x i : ℤ) : ℝ) =
          x i - ((floorVector x i : ℤ) : ℝ)
        ring
      _ = effectiveFanDisplacement N (M.t p) u := rfl
      _ = u + e := by simp [e]

public theorem actual_exists_twoChart_bounded_representative_of_ne_zero
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) (hp : M.t p ≠ 0) :
    let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
      W.localWitness.radius_pos W.localWitness.radius_le
    ∃ lambda : ParameterLattice, ∃ upper : Bool,
      (C.psiMap lambda p : M.Carrier) ∈ closedToricPolydisc M upper (fun _ ↦ 0)
        (Real.exp (4 * W.localWitness.phaseBound)) := by
  let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
    W.localWitness.radius_pos W.localWitness.radius_le
  obtain ⟨lambda, u, e, hu, he, hy⟩ := actual_exists_reduced_rescaledPosition W p hp
  have hnorm_pos : 0 < ‖M.t p‖ := norm_pos_iff.mpr hp
  have hnorm_lt : ‖M.t p‖ < 1 :=
    (mem_ball_zero_iff.mp p.property).trans W.localWitness.radius_lt_one
  have hlog_neg : Real.log ‖M.t p‖ < 0 := Real.log_neg hnorm_pos hnorm_lt
  have habslog_pos : 0 < |Real.log ‖M.t p‖| := abs_pos.mpr (ne_of_lt hlog_neg)
  let epsilon := 2 * W.localWitness.phaseBound / |Real.log ‖M.t p‖|
  have hepsilon : 0 ≤ epsilon := div_nonneg
    (mul_nonneg (by norm_num) W.localWitness.phaseBound_nonneg) (abs_nonneg _)
  obtain ⟨upper, hupper⟩ := exists_upper_barycentric_perturbation_lower
    u e epsilon hepsilon (fun i ↦ (hu i).1) (fun i ↦ (hu i).2.le) (by
      intro i
      exact he i)
  refine ⟨lambda, upper, ?_⟩
  rw [closedToricPolydisc_eq]
  have hpt : M.t (C.psiMap lambda p) ≠ 0 := by
    rw [C.psiMap_preserves_t]
    exact hp
  refine ⟨?_, fun i ↦ ?_⟩
  · rw [← torusEmbedding_torusCoordinates M hpt]
    exact M.torus_mem_toricChart upper (fun _ ↦ 0) _
  · have hcoord_ne : M.toricChart upper (fun _ ↦ 0) (C.psiMap lambda p) i ≠ 0 := by
      have htchart := M.toricChart_t upper (fun _ ↦ 0) (C.psiMap lambda p)
        (by
          rw [← torusEmbedding_torusCoordinates M hpt]
          exact M.torus_mem_toricChart upper (fun _ ↦ 0) _)
      have hprod : M.toricChart upper (fun _ ↦ 0) (C.psiMap lambda p) 0 *
          M.toricChart upper (fun _ ↦ 0) (C.psiMap lambda p) 1 *
            M.toricChart upper (fun _ ↦ 0) (C.psiMap lambda p) 2 ≠ 0 := by
        rw [← htchart]
        exact hpt
      have h01 := (mul_ne_zero_iff.mp hprod).1
      fin_cases i
      · exact (mul_ne_zero_iff.mp h01).1
      · exact (mul_ne_zero_iff.mp h01).2
      · exact (mul_ne_zero_iff.mp hprod).2
    apply (Real.log_le_iff_le_exp (norm_pos_iff.mpr hcoord_ne)).mp
    have hnorm_lt' : ‖M.t (C.psiMap lambda p)‖ < 1 := by
      rw [C.psiMap_preserves_t]
      exact hnorm_lt
    rw [log_norm_toricChart M hpt hnorm_lt' upper (fun _ ↦ 0) i,
      C.psiMap_preserves_t, hy]
    have htheta := hupper i
    dsimp [epsilon] at htheta
    rw [abs_of_neg hlog_neg] at htheta
    have hA := W.localWitness.phaseBound_nonneg
    have hlogne : Real.log ‖M.t p‖ ≠ 0 := ne_of_lt hlog_neg
    field_simp [hlogne] at htheta
    norm_num [pow_succ] at htheta
    calc
      Real.log ‖M.t p‖ * a2Barycentric upper (fun _ ↦ 0) (u + e) i ≤
          Real.log ‖M.t p‖ *
            (4 * W.localWitness.phaseBound / Real.log ‖M.t p‖) :=
        mul_le_mul_of_nonpos_left htheta (le_of_lt hlog_neg)
      _ = 4 * W.localWitness.phaseBound := by field_simp

public theorem actual_exists_twoChart_bounded_representative_of_eq_zero
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) (hp : M.t p = 0) :
    let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
      W.localWitness.radius_pos W.localWitness.radius_le
    ∃ lambda : ParameterLattice, ∃ upper : Bool,
      (C.psiMap lambda p : M.Carrier) ∈ closedToricPolydisc M upper (fun _ ↦ 0)
        (Real.exp (4 * W.localWitness.phaseBound)) := by
  let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
    W.localWitness.radius_pos W.localWitness.radius_le
  let F := W.localWitness.fixedPoint
  let _ := (C.toCuspActionData F).psiAction
  let b := W.localWitness.radius / 2
  have hbpos : 0 < b := div_pos W.localWitness.radius_pos (by norm_num)
  have hbr : b < W.localWitness.radius := by
    dsimp [b]
    linarith [W.localWitness.radius_pos]
  let polydiscs : Set M.Carrier :=
    closedToricPolydisc M false (fun _ ↦ 0) (Real.exp (4 * W.localWitness.phaseBound)) ∪
      closedToricPolydisc M true (fun _ ↦ 0) (Real.exp (4 * W.localWitness.phaseBound))
  let carrierCore : Set M.Carrier := {q | ‖M.t q‖ ≤ b} ∩ polydiscs
  let K : Set (LocalCarrier M W.localWitness.radius) := Subtype.val ⁻¹' carrierCore
  have hpolydiscs : IsCompact polydiscs :=
    (compact_closedToricPolydisc M false (fun _ ↦ 0)
      (Real.exp (4 * W.localWitness.phaseBound))).union
        (compact_closedToricPolydisc M true (fun _ ↦ 0)
          (Real.exp (4 * W.localWitness.phaseBound)))
  have hclosedRadius : IsClosed {q : M.Carrier | ‖M.t q‖ ≤ b} :=
    isClosed_le (continuous_norm.comp M.t_holomorphic.continuous) continuous_const
  have hcarrierCore : IsCompact carrierCore := hpolydiscs.inter_left hclosedRadius
  have hcarrierCore_local : carrierCore ⊆ cuspNeighborhood M W.localWitness.radius := by
    intro q hq
    exact (mem_cuspNeighborhood_iff M W.localWitness.radius q).2
      (mem_ball_zero_iff.mpr (hq.1.trans_lt hbr))
  have hK : IsCompact K := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert hcarrierCore using 1
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hq
      exact ⟨⟨q, hcarrierCore_local hq⟩, hq, rfl⟩
  let R : Setoid (LocalCarrier M W.localWitness.radius) :=
    MulAction.orbitRel (Multiplicative ParameterLattice) _
  let quotientCore : Set (Quotient R) := (Quotient.mk R) '' K
  let _ : LocallyCompactSpace M.Carrier :=
    ChartedSpace.locallyCompactSpace ComplexModel M.Carrier
  let _ : LocallyCompactSpace (LocalCarrier M W.localWitness.radius) :=
    (cuspNeighborhood M W.localWitness.radius).isOpen.locallyCompactSpace
  let _ : IsCancelSMul (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData F).action_free
  let _ : ProperlyDiscontinuousSMul (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    C.properlyDiscontinuous F W.localWitness.compactOverlap
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) := by
    constructor
    intro gamma
    convert (C.genericPsiMap_holomorphic F
      (Multiplicative.toAdd gamma)).continuous using 1
    funext q
    exact (C.toCuspActionData F).psi_smul (Multiplicative.toAdd gamma) q
  let _ : T2Space (Quotient R) := by infer_instance
  have hquotientCoreCompact : IsCompact quotientCore :=
    hK.image continuous_quot_mk
  have hquotientCoreClosed : IsClosed quotientCore := hquotientCoreCompact.isClosed
  let saturation : Set (LocalCarrier M W.localWitness.radius) :=
    (Quotient.mk R) ⁻¹' quotientCore
  have hsaturationClosed : IsClosed saturation :=
    hquotientCoreClosed.preimage continuous_quot_mk
  let innerPunctured : Set (LocalCarrier M W.localWitness.radius) :=
    {q | M.t q ≠ 0 ∧ ‖M.t q‖ < b}
  have hinner_saturation : innerPunctured ⊆ saturation := by
    intro q hq
    obtain ⟨lambda, upper, hlambda⟩ :=
      actual_exists_twoChart_bounded_representative_of_ne_zero W q hq.1
    have hqK : C.psiMap lambda q ∈ K := by
      change (C.psiMap lambda q : M.Carrier) ∈ carrierCore
      refine ⟨?_, ?_⟩
      · change ‖M.t (C.psiMap lambda q)‖ ≤ b
        rw [C.psiMap_preserves_t]
        exact hq.2.le
      · cases upper
        · exact Or.inl hlambda
        · exact Or.inr hlambda
    change Quotient.mk R q ∈ quotientCore
    refine ⟨C.psiMap lambda q, hqK, ?_⟩
    apply Quotient.sound
    change MulAction.orbitRel (Multiplicative ParameterLattice) _
      (C.psiMap lambda q) q
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨Multiplicative.ofAdd lambda, ?_⟩
    change (C.toCuspActionData F).psiMap lambda q = C.psiMap lambda q
    exact (C.psiMap_eq_generic F lambda q).symm
  have htorus : Dense {q : M.Carrier | M.t q ≠ 0} := by
    rw [← M.torus_range]
    exact M.torus_dense
  have hpuncturedDense : Dense {q : LocalCarrier M W.localWitness.radius | M.t q ≠ 0} := by
    exact htorus.preimage
      (cuspNeighborhood M W.localWitness.radius).isOpen.isOpenMap_subtype_val
  let inner : Set (LocalCarrier M W.localWitness.radius) :=
    Subtype.val ⁻¹' cuspNeighborhood M b
  have hinnerOpen : IsOpen inner :=
    (cuspNeighborhood M b).isOpen.preimage continuous_subtype_val
  have hpinner : p ∈ inner := by
    exact mem_ball_zero_iff.mpr (by simp [hp, hbpos])
  have hpclosure : p ∈ closure innerPunctured := by
    have hsub := hpuncturedDense.open_subset_closure_inter hinnerOpen hpinner
    apply closure_mono _ hsub
    rintro q ⟨hqinner, hqne⟩
    exact ⟨hqne, mem_ball_zero_iff.mp hqinner⟩
  have hpsaturation : p ∈ saturation :=
    closure_minimal hinner_saturation hsaturationClosed hpclosure
  change Quotient.mk R p ∈ quotientCore at hpsaturation
  obtain ⟨q, hqK, hqp⟩ := hpsaturation
  have hrel := Quotient.exact hqp
  change MulAction.orbitRel (Multiplicative ParameterLattice) _ q p at hrel
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨gamma, hgamma⟩ := hrel
  let lambda := Multiplicative.toAdd gamma
  have hpsi : C.psiMap lambda p = q := by
    rw [C.psiMap_eq_generic F]
    change gamma • p = q
    exact hgamma
  change (q : M.Carrier) ∈ carrierCore at hqK
  rcases hqK.2 with hqfalse | hqtrue
  · exact ⟨lambda, false, by rwa [hpsi]⟩
  · exact ⟨lambda, true, by rwa [hpsi]⟩

/-- The actual polarized `A₂` toric action has uniformly bounded representatives in the two
fixed affine charts. -/
public theorem actualA2TwoChartRadialSublevelRepresentatives
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    ActualA2TwoChartRadialSublevelRepresentatives W := by
  constructor
  intro _a _ha _har
  refine ⟨Real.exp (4 * W.localWitness.phaseBound), fun p _hp ↦ ?_⟩
  by_cases ht : M.t p = 0
  · exact actual_exists_twoChart_bounded_representative_of_eq_zero W p ht
  · exact actual_exists_twoChart_bounded_representative_of_ne_zero W p ht

/-- The cocompactness datum proves compactness of every nonnegative closed radial
sublevel in the actual cusp filling. -/
public theorem actualLocalCuspFillingRadiusSublevel_isCompact
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (H : ActualCuspRadialSublevelCocompactness W)
    (a : ℝ) (ha : 0 ≤ a) (har : a < W.localWitness.radius) :
    IsCompact {y : actualLocalCuspFilling W |
      actualLocalCuspFillingRadius W y ≤ a} := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius
        W.localWitness.radius_pos W.localWitness.radius_le
  let F := W.localWitness.fixedPoint
  change IsCompact {y : PhaseCorrectedToricQuotient C F |
    phaseCorrectedQuotientRadius C F y ≤ a}
  exact phaseCorrectedQuotientRadiusSublevel_isCompact C F H a ha har

/-- The concrete two-chart bounded-orbit theorem implies compactness of actual cusp-filling
radial sublevels. -/
public theorem actualLocalCuspFillingRadiusSublevel_isCompact_of_twoChartRepresentatives
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (H : ActualA2TwoChartRadialSublevelRepresentatives W)
    (a : ℝ) (ha : 0 ≤ a) (har : a < W.localWitness.radius) :
    IsCompact {y : actualLocalCuspFilling W |
      actualLocalCuspFillingRadius W y ≤ a} := by
  apply actualLocalCuspFillingRadiusSublevel_isCompact W _ a ha har
  exact radialSublevelCocompactness_of_twoChartRepresentatives _ H

end

end SphereSixComplex.Geometry.CuspFillingRadialCompactness

namespace SphereSixComplex.Geometry.PaperAnalyticData

open Set CuspFilling CuspPuncturedCollarBridge
open CuspFillingRadialCompactness

noncomputable section

variable (P : PaperAnalyticData)

/-- The toric cocompactness statement discharges the exact cusp compact-core boundary
used by the four-piece compact cover. -/
public theorem actualLocalCuspRadialCoreCompactness_of_cocompactness
    (H : ActualCuspRadialSublevelCocompactness P.starCuspWitness) :
    P.ActualLocalCuspRadialCoreCompactness := by
  change ∀ a, a < P.starCuspWitness.localWitness.radius →
    IsCompact {y : actualLocalCuspFilling P.starCuspWitness |
      actualLocalCuspFillingRadius P.starCuspWitness y ≤ a}
  intro a ha
  by_cases ha0 : 0 ≤ a
  · exact actualLocalCuspFillingRadiusSublevel_isCompact
      P.starCuspWitness H a ha0 ha
  · have hempty : {y : actualLocalCuspFilling P.starCuspWitness |
        actualLocalCuspFillingRadius P.starCuspWitness y ≤ a} = ∅ := by
      ext y
      rw [mem_empty_iff_false, iff_false]
      intro hy
      have hnonneg : 0 ≤ actualLocalCuspFillingRadius P.starCuspWitness y := by
        induction y using Quotient.inductionOn with
        | _ p => exact norm_nonneg _
      exact (not_le_of_gt (lt_of_not_ge ha0)) (hnonneg.trans hy)
    rw [hempty]
    exact isCompact_empty

/-- The concrete `A₂` two-chart theorem discharges the cusp compact-core boundary. -/
public theorem actualLocalCuspRadialCoreCompactness_of_twoChartRepresentatives
    (H : ActualA2TwoChartRadialSublevelRepresentatives P.starCuspWitness) :
    P.ActualLocalCuspRadialCoreCompactness := by
  apply P.actualLocalCuspRadialCoreCompactness_of_cocompactness
  exact radialSublevelCocompactness_of_twoChartRepresentatives _ H

end

end SphereSixComplex.Geometry.PaperAnalyticData

module

public import SphereSixComplex.Geometry.EllipticHolomorphicLogCover
public import SphereSixComplex.Geometry.EllipticLogarithmicGaugeDescent
import all SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient

/-!
# The glued logarithmic gauge on the full punctured elliptic collars

The principal logarithm supplies a global formula for the torus-valued gauge.  Although its
vector-valued lift jumps across the branch cut, the jump is an integral period and disappears in
the torus quotient.  The explicit holomorphic logarithm cover therefore proves local continuity
and identifies the global gauge with every branch formula on overlaps.
-/

namespace SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph

open Filter Set
open scoped Manifold ContDiff
open SphereSixComplex.LatticeData SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticWholeFiberTrivialization
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLogarithmicGauge
open SphereSixComplex.Geometry.EllipticHolomorphicLogCover
open SphereSixComplex.Geometry.EllipticLogarithmicGaugeDescent
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph

noncomputable section

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- Two holomorphic logarithm branches differ pointwise by an integral multiple of `2 * pi * I`
on their overlap. -/
public theorem exists_int_log_branch_difference
    (B₁ B₂ : HolomorphicLogBranch) (w : ℂ)
    (h₁ : w ∈ B₁.carrier) (h₂ : w ∈ B₂.carrier) :
    ∃ k : ℤ, B₂.log w =
      B₁.log w + ((2 : ℂ) * Real.pi * Complex.I) * k := by
  have he : Complex.exp (B₂.log w) = Complex.exp (B₁.log w) := by
    rw [B₂.exp_log w h₂, B₁.exp_log w h₁]
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  refine ⟨k, ?_⟩
  rw [hk]
  ring

/-- The torus-valued logarithmic gauge is independent of the chosen holomorphic branch at every
point of an overlap. -/
public theorem logarithmicGaugeMap_eq_of_branches
    (cayley : UpperHalfPlane → ComplexUnitDisc) (v : Lattice)
    (B₁ B₂ : HolomorphicLogBranch) (q : TotalSpace (parameterMap F))
    (h₁ : (cayley (familyTotalSpaceBase F q) : ℂ) ∈ B₁.carrier)
    (h₂ : (cayley (familyTotalSpaceBase F q) : ℂ) ∈ B₂.carrier) :
    familyTranslationMap F
        (logarithmicGaugeSection F cayley v (fun w => B₂.log w)) q =
      familyTranslationMap F
        (logarithmicGaugeSection F cayley v (fun w => B₁.log w)) q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    obtain ⟨k, hk⟩ := exists_int_log_branch_difference B₁ B₂
      (cayley p.1) h₁ h₂
    exact logarithmicGaugeMap_mk_eq_of_branch_change F cayley v
      (fun w => B₁.log w) (fun w => B₂.log w) p.1 p.2 k hk

/-- The global formula used to glue the local order-three gauges. -/
@[expose] public noncomputable def orderThreePrincipalGaugeSection
    (z : UpperHalfPlane) : ComplexTwoSpace :=
  logarithmicGaugeSection F orderThreeCayleyHomeomorph epsilon
    (fun w => Complex.log w) z

/-- The global formula used to glue the local order-four gauges. -/
@[expose] public noncomputable def orderFourPrincipalGaugeSection
    (z : UpperHalfPlane) : ComplexTwoSpace :=
  logarithmicGaugeSection F orderFourCayleyHomeomorph (-epsilon')
    (fun w => Complex.log w) z

@[expose] public noncomputable def orderThreePrincipalGaugeEquiv :
    Equiv.Perm (TotalSpace (parameterMap F)) :=
  familyTranslationEquiv F (orderThreePrincipalGaugeSection F)

@[expose] public noncomputable def orderFourPrincipalGaugeEquiv :
    Equiv.Perm (TotalSpace (parameterMap F)) :=
  familyTranslationEquiv F (orderFourPrincipalGaugeSection F)

/-- On every explicit order-three logarithm chart, the global torus-valued formula agrees with
the local holomorphic formula. -/
public theorem orderThreePrincipalGauge_eq_branch
    (B : HolomorphicLogBranch) (q : TotalSpace (parameterMap F))
    (hq : (orderThreeCayleyHomeomorph (familyTotalSpaceBase F q) : ℂ) ∈ B.carrier)
    (hne : orderThreeCayleyHomeomorph (familyTotalSpaceBase F q) ≠ discCenter) :
    orderThreePrincipalGaugeEquiv F q =
      orderThreeLogarithmicGaugeMap F (fun w => B.log w) q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    rw [orderThreePrincipalGaugeEquiv.eq_def, familyTranslationEquiv_apply,
      orderThreeLogarithmicGaugeMap.eq_def]
    change
      familyTranslationMap F
          (logarithmicGaugeSection F orderThreeCayleyHomeomorph epsilon
            (fun w => Complex.log w)) (Quotient.mk _ p) =
        familyTranslationMap F
          (logarithmicGaugeSection F orderThreeCayleyHomeomorph epsilon
            (fun w => B.log w)) (Quotient.mk _ p)
    let w := orderThreeCayleyHomeomorph p.1
    have hw : (w : ℂ) ≠ 0 := coe_ne_zero_of_ne_center hne
    have he : Complex.exp (Complex.log w) = Complex.exp (B.log w) := by
      rw [Complex.exp_log hw, B.exp_log w hq]
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    apply logarithmicGaugeMap_mk_eq_of_branch_change F
      orderThreeCayleyHomeomorph epsilon
      (fun w => B.log w) (fun w => Complex.log w) p.1 p.2 k
    rw [hk]
    ring

/-- On every explicit order-four logarithm chart, the global torus-valued formula agrees with
the local holomorphic formula. -/
public theorem orderFourPrincipalGauge_eq_branch
    (B : HolomorphicLogBranch) (q : TotalSpace (parameterMap F))
    (hq : (orderFourCayleyHomeomorph (familyTotalSpaceBase F q) : ℂ) ∈ B.carrier)
    (hne : orderFourCayleyHomeomorph (familyTotalSpaceBase F q) ≠ discCenter) :
    orderFourPrincipalGaugeEquiv F q =
      orderFourLogarithmicGaugeMap F (fun w => B.log w) q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    rw [orderFourPrincipalGaugeEquiv.eq_def, familyTranslationEquiv_apply,
      orderFourLogarithmicGaugeMap.eq_def]
    change
      familyTranslationMap F
          (logarithmicGaugeSection F orderFourCayleyHomeomorph (-epsilon')
            (fun w => Complex.log w)) (Quotient.mk _ p) =
        familyTranslationMap F
          (logarithmicGaugeSection F orderFourCayleyHomeomorph (-epsilon')
            (fun w => B.log w)) (Quotient.mk _ p)
    let w := orderFourCayleyHomeomorph p.1
    have hw : (w : ℂ) ≠ 0 := coe_ne_zero_of_ne_center hne
    have he : Complex.exp (Complex.log w) = Complex.exp (B.log w) := by
      rw [Complex.exp_log hw, B.exp_log w hq]
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    apply logarithmicGaugeMap_mk_eq_of_branch_change F
      orderFourCayleyHomeomorph (-epsilon')
      (fun w => B.log w) (fun w => Complex.log w) p.1 p.2 k
    rw [hk]
    ring

public theorem neg_logarithmicGaugeSection
    (cayley : UpperHalfPlane → ComplexUnitDisc) (v : Lattice)
    (log : ComplexUnitDisc → ℂ) :
    -logarithmicGaugeSection F cayley v log =
      logarithmicGaugeSection F cayley v (fun w => -log w) := by
  funext z
  simp only [Pi.neg_apply, logarithmicGaugeSection, logarithmicGaugeScalar]
  module

public theorem orderThreePrincipalGauge_symm_eq_branch
    (B : HolomorphicLogBranch) (q : TotalSpace (parameterMap F))
    (hq : (orderThreeCayleyHomeomorph (familyTotalSpaceBase F q) : ℂ) ∈ B.carrier)
    (hne : orderThreeCayleyHomeomorph (familyTotalSpaceBase F q) ≠ discCenter) :
    (orderThreePrincipalGaugeEquiv F).symm q =
      familyTranslationMap F
        (-logarithmicGaugeSection F orderThreeCayleyHomeomorph epsilon
          (fun w => B.log w)) q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    rw [orderThreePrincipalGaugeEquiv.eq_def]
    change familyTranslationMap F
        (-logarithmicGaugeSection F orderThreeCayleyHomeomorph epsilon
          (fun w => Complex.log w)) (Quotient.mk _ p) =
      familyTranslationMap F
        (-logarithmicGaugeSection F orderThreeCayleyHomeomorph epsilon
          (fun w => B.log w)) (Quotient.mk _ p)
    rw [neg_logarithmicGaugeSection, neg_logarithmicGaugeSection]
    let w := orderThreeCayleyHomeomorph p.1
    have hw : (w : ℂ) ≠ 0 := coe_ne_zero_of_ne_center hne
    have he : Complex.exp (Complex.log w) = Complex.exp (B.log w) := by
      rw [Complex.exp_log hw, B.exp_log w hq]
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    apply logarithmicGaugeMap_mk_eq_of_branch_change F
      orderThreeCayleyHomeomorph epsilon
      (fun w => -B.log w) (fun w => -Complex.log w) p.1 p.2 (-k)
    rw [hk]
    push_cast
    ring

public theorem orderFourPrincipalGauge_symm_eq_branch
    (B : HolomorphicLogBranch) (q : TotalSpace (parameterMap F))
    (hq : (orderFourCayleyHomeomorph (familyTotalSpaceBase F q) : ℂ) ∈ B.carrier)
    (hne : orderFourCayleyHomeomorph (familyTotalSpaceBase F q) ≠ discCenter) :
    (orderFourPrincipalGaugeEquiv F).symm q =
      familyTranslationMap F
        (-logarithmicGaugeSection F orderFourCayleyHomeomorph (-epsilon')
          (fun w => B.log w)) q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    rw [orderFourPrincipalGaugeEquiv.eq_def]
    change familyTranslationMap F
        (-logarithmicGaugeSection F orderFourCayleyHomeomorph (-epsilon')
          (fun w => Complex.log w)) (Quotient.mk _ p) =
      familyTranslationMap F
        (-logarithmicGaugeSection F orderFourCayleyHomeomorph (-epsilon')
          (fun w => B.log w)) (Quotient.mk _ p)
    rw [neg_logarithmicGaugeSection, neg_logarithmicGaugeSection]
    let w := orderFourCayleyHomeomorph p.1
    have hw : (w : ℂ) ≠ 0 := coe_ne_zero_of_ne_center hne
    have he : Complex.exp (Complex.log w) = Complex.exp (B.log w) := by
      rw [Complex.exp_log hw, B.exp_log w hq]
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    apply logarithmicGaugeMap_mk_eq_of_branch_change F
      orderFourCayleyHomeomorph (-epsilon')
      (fun w => -B.log w) (fun w => -Complex.log w) p.1 p.2 (-k)
    rw [hk]
    push_cast
    ring

/-- A logarithmic gauge section is continuous at every base point lying in its holomorphic
branch carrier. -/
public theorem logarithmicGaugeSection_continuousAt
    (cayley : UpperHalfPlane ≃ₜ ComplexUnitDisc) (v : Lattice)
    (B : HolomorphicLogBranch) (z : UpperHalfPlane)
    (hz : (cayley z : ℂ) ∈ B.carrier) :
    ContinuousAt
      (logarithmicGaugeSection F cayley v (fun w => B.log w)) z := by
  have hlog : ContinuousAt B.log (cayley z : ℂ) :=
    (B.differentiableOn_log.differentiableAt
      (B.isOpen_carrier.mem_nhds hz)).continuousAt
  have hcayley : ContinuousAt (fun z : UpperHalfPlane => (cayley z : ℂ)) z :=
    continuous_subtype_val.continuousAt.comp cayley.continuous.continuousAt
  have hcomp : ContinuousAt
      (fun z : UpperHalfPlane => B.log (cayley z : ℂ)) z :=
    ContinuousAt.comp hlog hcayley
  have hscalar : ContinuousAt
      (fun z : UpperHalfPlane =>
        logarithmicGaugeScalar (B.log (cayley z : ℂ))) z := by
    exact continuousAt_const.mul hcomp
  have hperiod : ContinuousAt
      (fun z : UpperHalfPlane => periodVector (parameterMap F z).1 v) z :=
    (periodSection_contMDiff F v ω).continuous.continuousAt
  change ContinuousAt
    (fun z : UpperHalfPlane =>
      logarithmicGaugeScalar (B.log (cayley z : ℂ)) •
        periodVector (parameterMap F z).1 v) z
  exact hscalar.smul hperiod

/-- Local continuity of a descended fibre translation only needs continuity of its section at
the representative base point. -/
public theorem familyTranslationMap_continuousAt_of_section
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F)))
    (s : UpperHalfPlane → ComplexTwoSpace)
    (p : UpperHalfPlane × ComplexTwoSpace) (hs : ContinuousAt s p.1) :
    ContinuousAt (familyTranslationMap F s)
      (projection (parameterMap F) p) := by
  let π : UpperHalfPlane × ComplexTwoSpace → TotalSpace (parameterMap F) :=
    projection (parameterMap F)
  let loc := (hprojection p).localInverse
  have hlocal : ContinuousAt loc (π p) :=
    (hprojection p).localInverse_contMDiffAt.continuousAt
  have hlocalp : loc (π p) = p :=
    (hprojection p).localInverse_left_inv
      (hprojection p).localInverse_mem_target
  have hcover : ContinuousAt (familyTranslationCover s ∘ loc) (π p) := by
    have htranslation : ContinuousAt (familyTranslationCover s) p :=
      continuousAt_fst.prodMk
        ((hs.comp continuousAt_fst).add continuousAt_snd)
    exact htranslation.comp_of_eq hlocal hlocalp
  have hright : ContinuousAt (π ∘ familyTranslationCover s ∘ loc) (π p) :=
    (hprojection (familyTranslationCover s p)).contMDiffAt.continuousAt.comp_of_eq
      hcover (by simp [hlocalp])
  have hevent : familyTranslationMap F s =ᶠ[nhds (π p)]
      (π ∘ familyTranslationCover s ∘ loc) := by
    filter_upwards [(hprojection p).localInverse_eventuallyEq_right] with x hx
    calc
      familyTranslationMap F s x = familyTranslationMap F s (π (loc x)) :=
        congrArg _ hx.symm
      _ = π (familyTranslationCover s (loc x)) :=
        familyTranslationMap_mk F s (loc x)
  exact hright.congr_of_eventuallyEq hevent

public theorem orderThreePrincipalGauge_continuousOn
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) (r : ℝ) :
    ContinuousOn (orderThreePrincipalGaugeEquiv F)
      (orderThreePuncturedFamilyCollar F r) := by
  intro q hq
  induction q using Quotient.inductionOn with
  | _ p =>
    let w := orderThreeCayleyHomeomorph p.1
    have hw : w ≠ discCenter := by
      intro h
      have hpos := hq.1
      change 0 < ‖(w : ℂ)‖ at hpos
      rw [h] at hpos
      norm_num [discCenter] at hpos
    let B := (orderThreeBranchesAt w hw).source
    have hwB : (w : ℂ) ∈ B.carrier := mem_orderThreeBranchesAt w hw
    have hbranch : ContinuousAt
        (orderThreeLogarithmicGaugeMap F (fun u => B.log u))
        (Quotient.mk _ p) := by
      apply familyTranslationMap_continuousAt_of_section F hprojection
      exact logarithmicGaugeSection_continuousAt F
        orderThreeCayleyHomeomorph epsilon B p.1 hwB
    have hopen : IsOpen
        {x : TotalSpace (parameterMap F) |
          (orderThreeCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈ B.carrier} :=
      B.isOpen_carrier.preimage
        (continuous_subtype_val.comp
          (orderThreeCayleyHomeomorph.continuous.comp
            (familyTotalSpaceBase_continuous F)))
    have hnear : ∀ᶠ x in nhds (Quotient.mk _ p),
        (orderThreeCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈
          B.carrier := by
      apply hopen.mem_nhds
      exact hwB
    have heq : orderThreePrincipalGaugeEquiv F =ᶠ[
        nhdsWithin (Quotient.mk _ p) (orderThreePuncturedFamilyCollar F r)]
        orderThreeLogarithmicGaugeMap F (fun u => B.log u) := by
      have hnear' : ∀ᶠ x in
          nhdsWithin (Quotient.mk _ p) (orderThreePuncturedFamilyCollar F r),
          (orderThreeCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈
            B.carrier := hnear.filter_mono inf_le_left
      filter_upwards [hnear', self_mem_nhdsWithin] with x hxB hx
      apply orderThreePrincipalGauge_eq_branch F B x hxB
      intro hcenter
      have hpos := hx.1
      change 0 < ‖(orderThreeCayleyHomeomorph
        (familyTotalSpaceBase F x) : ℂ)‖ at hpos
      rw [hcenter] at hpos
      norm_num [discCenter] at hpos
    exact hbranch.continuousWithinAt.congr_of_eventuallyEq_of_mem heq hq

public theorem orderFourPrincipalGauge_continuousOn
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) (r : ℝ) :
    ContinuousOn (orderFourPrincipalGaugeEquiv F)
      (orderFourPuncturedFamilyCollar F r) := by
  intro q hq
  induction q using Quotient.inductionOn with
  | _ p =>
    let w := orderFourCayleyHomeomorph p.1
    have hw : w ≠ discCenter := by
      intro h
      have hpos := hq.1
      change 0 < ‖(w : ℂ)‖ at hpos
      rw [h] at hpos
      norm_num [discCenter] at hpos
    let B := (orderFourBranchesAt w hw).source
    have hwB : (w : ℂ) ∈ B.carrier := mem_orderFourBranchesAt w hw
    have hbranch : ContinuousAt
        (orderFourLogarithmicGaugeMap F (fun u => B.log u))
        (Quotient.mk _ p) := by
      apply familyTranslationMap_continuousAt_of_section F hprojection
      exact logarithmicGaugeSection_continuousAt F
        orderFourCayleyHomeomorph (-epsilon') B p.1 hwB
    have hopen : IsOpen
        {x : TotalSpace (parameterMap F) |
          (orderFourCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈ B.carrier} :=
      B.isOpen_carrier.preimage
        (continuous_subtype_val.comp
          (orderFourCayleyHomeomorph.continuous.comp
            (familyTotalSpaceBase_continuous F)))
    have hnear : ∀ᶠ x in nhds (Quotient.mk _ p),
        (orderFourCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈
          B.carrier := by
      apply hopen.mem_nhds
      exact hwB
    have heq : orderFourPrincipalGaugeEquiv F =ᶠ[
        nhdsWithin (Quotient.mk _ p) (orderFourPuncturedFamilyCollar F r)]
        orderFourLogarithmicGaugeMap F (fun u => B.log u) := by
      have hnear' : ∀ᶠ x in
          nhdsWithin (Quotient.mk _ p) (orderFourPuncturedFamilyCollar F r),
          (orderFourCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈
            B.carrier := hnear.filter_mono inf_le_left
      filter_upwards [hnear', self_mem_nhdsWithin] with x hxB hx
      apply orderFourPrincipalGauge_eq_branch F B x hxB
      intro hcenter
      have hpos := hx.1
      change 0 < ‖(orderFourCayleyHomeomorph
        (familyTotalSpaceBase F x) : ℂ)‖ at hpos
      rw [hcenter] at hpos
      norm_num [discCenter] at hpos
    exact hbranch.continuousWithinAt.congr_of_eventuallyEq_of_mem heq hq

public theorem orderThreePrincipalGauge_symm_continuousOn
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) (r : ℝ) :
    ContinuousOn (orderThreePrincipalGaugeEquiv F).symm
      (orderThreePuncturedFamilyCollar F r) := by
  intro q hq
  induction q using Quotient.inductionOn with
  | _ p =>
    let w := orderThreeCayleyHomeomorph p.1
    have hw : w ≠ discCenter := by
      intro h
      have hpos := hq.1
      change 0 < ‖(w : ℂ)‖ at hpos
      rw [h] at hpos
      norm_num [discCenter] at hpos
    let B := (orderThreeBranchesAt w hw).source
    have hwB : (w : ℂ) ∈ B.carrier := mem_orderThreeBranchesAt w hw
    let localMap := familyTranslationMap F
      (-logarithmicGaugeSection F orderThreeCayleyHomeomorph epsilon
        (fun u => B.log u))
    have hbranch : ContinuousAt localMap (Quotient.mk _ p) := by
      apply familyTranslationMap_continuousAt_of_section F hprojection
      exact (logarithmicGaugeSection_continuousAt F
        orderThreeCayleyHomeomorph epsilon B p.1 hwB).neg
    have hopen : IsOpen
        {x : TotalSpace (parameterMap F) |
          (orderThreeCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈ B.carrier} :=
      B.isOpen_carrier.preimage
        (continuous_subtype_val.comp
          (orderThreeCayleyHomeomorph.continuous.comp
            (familyTotalSpaceBase_continuous F)))
    have hnear : ∀ᶠ x in nhds (Quotient.mk _ p),
        (orderThreeCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈
          B.carrier := hopen.mem_nhds hwB
    have heq : (orderThreePrincipalGaugeEquiv F).symm =ᶠ[
        nhdsWithin (Quotient.mk _ p) (orderThreePuncturedFamilyCollar F r)]
        localMap := by
      have hnear' : ∀ᶠ x in
          nhdsWithin (Quotient.mk _ p) (orderThreePuncturedFamilyCollar F r),
          (orderThreeCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈
            B.carrier := hnear.filter_mono inf_le_left
      filter_upwards [hnear', self_mem_nhdsWithin] with x hxB hx
      apply orderThreePrincipalGauge_symm_eq_branch F B x hxB
      intro hcenter
      have hpos := hx.1
      change 0 < ‖(orderThreeCayleyHomeomorph
        (familyTotalSpaceBase F x) : ℂ)‖ at hpos
      rw [hcenter] at hpos
      norm_num [discCenter] at hpos
    exact hbranch.continuousWithinAt.congr_of_eventuallyEq_of_mem heq hq

public theorem orderFourPrincipalGauge_symm_continuousOn
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) (r : ℝ) :
    ContinuousOn (orderFourPrincipalGaugeEquiv F).symm
      (orderFourPuncturedFamilyCollar F r) := by
  intro q hq
  induction q using Quotient.inductionOn with
  | _ p =>
    let w := orderFourCayleyHomeomorph p.1
    have hw : w ≠ discCenter := by
      intro h
      have hpos := hq.1
      change 0 < ‖(w : ℂ)‖ at hpos
      rw [h] at hpos
      norm_num [discCenter] at hpos
    let B := (orderFourBranchesAt w hw).source
    have hwB : (w : ℂ) ∈ B.carrier := mem_orderFourBranchesAt w hw
    let localMap := familyTranslationMap F
      (-logarithmicGaugeSection F orderFourCayleyHomeomorph (-epsilon')
        (fun u => B.log u))
    have hbranch : ContinuousAt localMap (Quotient.mk _ p) := by
      apply familyTranslationMap_continuousAt_of_section F hprojection
      exact (logarithmicGaugeSection_continuousAt F
        orderFourCayleyHomeomorph (-epsilon') B p.1 hwB).neg
    have hopen : IsOpen
        {x : TotalSpace (parameterMap F) |
          (orderFourCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈ B.carrier} :=
      B.isOpen_carrier.preimage
        (continuous_subtype_val.comp
          (orderFourCayleyHomeomorph.continuous.comp
            (familyTotalSpaceBase_continuous F)))
    have hnear : ∀ᶠ x in nhds (Quotient.mk _ p),
        (orderFourCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈
          B.carrier := hopen.mem_nhds hwB
    have heq : (orderFourPrincipalGaugeEquiv F).symm =ᶠ[
        nhdsWithin (Quotient.mk _ p) (orderFourPuncturedFamilyCollar F r)]
        localMap := by
      have hnear' : ∀ᶠ x in
          nhdsWithin (Quotient.mk _ p) (orderFourPuncturedFamilyCollar F r),
          (orderFourCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈
            B.carrier := hnear.filter_mono inf_le_left
      filter_upwards [hnear', self_mem_nhdsWithin] with x hxB hx
      apply orderFourPrincipalGauge_symm_eq_branch F B x hxB
      intro hcenter
      have hpos := hx.1
      change 0 < ‖(orderFourCayleyHomeomorph
        (familyTotalSpaceBase F x) : ℂ)‖ at hpos
      rw [hcenter] at hpos
      norm_num [discCenter] at hpos
    exact hbranch.continuousWithinAt.congr_of_eventuallyEq_of_mem heq hq

public theorem orderThreeFamilyRadius_principalGauge
    (q : TotalSpace (parameterMap F)) :
    orderThreeFamilyRadius F (orderThreePrincipalGaugeEquiv F q) =
      orderThreeFamilyRadius F q := by
  rw [orderThreeFamilyRadius.eq_def, orderThreePrincipalGaugeEquiv.eq_def,
    familyTranslationEquiv_apply, familyTotalSpaceBase_familyTranslationMap]
  rfl

public theorem orderFourFamilyRadius_principalGauge
    (q : TotalSpace (parameterMap F)) :
    orderFourFamilyRadius F (orderFourPrincipalGaugeEquiv F q) =
      orderFourFamilyRadius F q := by
  rw [orderFourFamilyRadius.eq_def, orderFourPrincipalGaugeEquiv.eq_def,
    familyTranslationEquiv_apply, familyTotalSpaceBase_familyTranslationMap]
  rfl

public theorem orderThreeFamilyRadius_principalGauge_symm
    (q : TotalSpace (parameterMap F)) :
    orderThreeFamilyRadius F ((orderThreePrincipalGaugeEquiv F).symm q) =
      orderThreeFamilyRadius F q := by
  change orderThreeFamilyRadius F
    (familyTranslationMap F (-orderThreePrincipalGaugeSection F) q) = _
  rw [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_familyTranslationMap]
  rfl

public theorem orderFourFamilyRadius_principalGauge_symm
    (q : TotalSpace (parameterMap F)) :
    orderFourFamilyRadius F ((orderFourPrincipalGaugeEquiv F).symm q) =
      orderFourFamilyRadius F q := by
  change orderFourFamilyRadius F
    (familyTranslationMap F (-orderFourPrincipalGaugeSection F) q) = _
  rw [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_familyTranslationMap]
  rfl

@[expose] public noncomputable def orderThreePuncturedCollarGaugeEquiv (r : ℝ) :
    orderThreePuncturedFamilyCollar F r ≃
      orderThreePuncturedFamilyCollar F r where
  toFun q := ⟨orderThreePrincipalGaugeEquiv F q,
    by simpa [orderThreePuncturedFamilyCollar.eq_def,
      orderThreeFamilyRadius_principalGauge F] using q.property⟩
  invFun q := ⟨(orderThreePrincipalGaugeEquiv F).symm q,
    by simpa [orderThreePuncturedFamilyCollar.eq_def,
      orderThreeFamilyRadius_principalGauge_symm F] using q.property⟩
  left_inv q := Subtype.ext ((orderThreePrincipalGaugeEquiv F).left_inv q)
  right_inv q := Subtype.ext ((orderThreePrincipalGaugeEquiv F).right_inv q)

@[expose] public noncomputable def orderFourPuncturedCollarGaugeEquiv (r : ℝ) :
    orderFourPuncturedFamilyCollar F r ≃
      orderFourPuncturedFamilyCollar F r where
  toFun q := ⟨orderFourPrincipalGaugeEquiv F q,
    by simpa [orderFourPuncturedFamilyCollar.eq_def,
      orderFourFamilyRadius_principalGauge F] using q.property⟩
  invFun q := ⟨(orderFourPrincipalGaugeEquiv F).symm q,
    by simpa [orderFourPuncturedFamilyCollar.eq_def,
      orderFourFamilyRadius_principalGauge_symm F] using q.property⟩
  left_inv q := Subtype.ext ((orderFourPrincipalGaugeEquiv F).left_inv q)
  right_inv q := Subtype.ext ((orderFourPrincipalGaugeEquiv F).right_inv q)

@[expose] public noncomputable def orderThreePuncturedCollarGaugeHomeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) (r : ℝ) :
    orderThreePuncturedFamilyCollar F r ≃ₜ
      orderThreePuncturedFamilyCollar F r where
  toEquiv := orderThreePuncturedCollarGaugeEquiv F r
  continuous_toFun :=
    (orderThreePrincipalGauge_continuousOn F hprojection r).mapsToRestrict
      (fun _ h => by simpa [orderThreePuncturedFamilyCollar.eq_def,
        orderThreeFamilyRadius_principalGauge F] using h)
  continuous_invFun :=
    (orderThreePrincipalGauge_symm_continuousOn F hprojection r).mapsToRestrict
      (fun _ h => by simpa [orderThreePuncturedFamilyCollar.eq_def,
        orderThreeFamilyRadius_principalGauge_symm F] using h)

@[expose] public noncomputable def orderFourPuncturedCollarGaugeHomeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) (r : ℝ) :
    orderFourPuncturedFamilyCollar F r ≃ₜ
      orderFourPuncturedFamilyCollar F r where
  toEquiv := orderFourPuncturedCollarGaugeEquiv F r
  continuous_toFun :=
    (orderFourPrincipalGauge_continuousOn F hprojection r).mapsToRestrict
      (fun _ h => by simpa [orderFourPuncturedFamilyCollar.eq_def,
        orderFourFamilyRadius_principalGauge F] using h)
  continuous_invFun :=
    (orderFourPrincipalGauge_symm_continuousOn F hprojection r).mapsToRestrict
      (fun _ h => by simpa [orderFourPuncturedFamilyCollar.eq_def,
        orderFourFamilyRadius_principalGauge_symm F] using h)

public theorem orderThreeFamilyRadius_linearGenerator
    (hsource : U.sourceAction = fuchsianSourceAction)
    (q : TotalSpace (parameterMap F)) :
    orderThreeFamilyRadius F (familyDeckMap F g₁ q) =
      orderThreeFamilyRadius F q := by
  rw [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_familyDeckMap,
    hsource, orderThreeCayleyHomeomorph_generator]
  change ‖orderThreeMultiplier *
    (orderThreeCayleyHomeomorph (familyTotalSpaceBase F q)).1‖ = _
  rw [norm_mul, norm_orderThreeMultiplier, one_mul]
  rfl

public theorem orderFourFamilyRadius_linearGenerator
    (hsource : U.sourceAction = fuchsianSourceAction)
    (q : TotalSpace (parameterMap F)) :
    orderFourFamilyRadius F (familyDeckMap F g₂ q) =
      orderFourFamilyRadius F q := by
  rw [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_familyDeckMap,
    hsource, orderFourCayleyHomeomorph_generator]
  change ‖orderFourMultiplier *
    (orderFourCayleyHomeomorph (familyTotalSpaceBase F q)).1‖ = _
  rw [norm_mul, norm_orderFourMultiplier, one_mul]
  rfl

public theorem orderThreeFamilyRadius_linearRepresentation
    (hsource : U.sourceAction = fuchsianSourceAction)
    (g : FiniteCyclic 3) (q : TotalSpace (parameterMap F)) :
    orderThreeFamilyRadius F (orderThreeFamilyRepresentation F g q) =
      orderThreeFamilyRadius F q := by
  rw [cyclic_eq_generator_pow g, map_pow]
  induction (Multiplicative.toAdd g).val generalizing q with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      change orderThreeFamilyRadius F
        (smulOf (orderThreeLinearFamilyAction F) (cyclicGenerator 3)
          (((orderThreeFamilyRepresentation F) (cyclicGenerator 3) ^ k) q)) = _
      rw [orderThreeLinear_smulOf_generator,
        orderThreeFamilyRadius_linearGenerator F hsource, ih]

public theorem orderFourFamilyRadius_linearRepresentation
    (hsource : U.sourceAction = fuchsianSourceAction)
    (g : FiniteCyclic 4) (q : TotalSpace (parameterMap F)) :
    orderFourFamilyRadius F (orderFourFamilyRepresentation F g q) =
      orderFourFamilyRadius F q := by
  rw [cyclic_eq_generator_pow g, map_pow]
  induction (Multiplicative.toAdd g).val generalizing q with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      change orderFourFamilyRadius F
        (smulOf (orderFourLinearFamilyAction F) (cyclicGenerator 4)
          (((orderFourFamilyRepresentation F) (cyclicGenerator 4) ^ k) q)) = _
      rw [orderFourLinear_smulOf_generator,
        orderFourFamilyRadius_linearGenerator F hsource, ih]

@[expose] public noncomputable def orderThreeAffinePuncturedCarrier
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    OpenSubMulAction (orderThreeAffineFamilyAction F) where
  toSubMulAction := by
    letI := orderThreeAffineFamilyAction F
    exact {
      carrier := orderThreePuncturedFamilyCollar F r
      smul_mem' := by
        intro g q hq
        change orderThreeAffineFamilyRepresentation F g q ∈
          orderThreePuncturedFamilyCollar F r
        exact (orderThreePuncturedFamilyCollar_invariant F hsource r g q).2 hq }
  isOpen_carrier := orderThreePuncturedFamilyCollar_isOpen F r

@[expose] public noncomputable def orderFourAffinePuncturedCarrier
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    OpenSubMulAction (orderFourAffineFamilyAction F) where
  toSubMulAction := by
    letI := orderFourAffineFamilyAction F
    exact {
      carrier := orderFourPuncturedFamilyCollar F r
      smul_mem' := by
        intro g q hq
        change orderFourAffineFamilyRepresentation F g q ∈
          orderFourPuncturedFamilyCollar F r
        exact (orderFourPuncturedFamilyCollar_invariant F hsource r g q).2 hq }
  isOpen_carrier := orderFourPuncturedFamilyCollar_isOpen F r

@[expose] public noncomputable def orderThreeLinearPuncturedCarrier
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    OpenSubMulAction (orderThreeLinearFamilyAction F) where
  toSubMulAction := by
    letI := orderThreeLinearFamilyAction F
    exact {
      carrier := orderThreePuncturedFamilyCollar F r
      smul_mem' := by
        intro g q hq
        have hr : orderThreeFamilyRadius F
          (orderThreeFamilyRepresentation F g q) =
          orderThreeFamilyRadius F q := by
          exact orderThreeFamilyRadius_linearRepresentation F hsource g q
        change 0 < orderThreeFamilyRadius F (orderThreeFamilyRepresentation F g q) ∧
          orderThreeFamilyRadius F (orderThreeFamilyRepresentation F g q) < r
        rw [hr]
        exact hq }
  isOpen_carrier := orderThreePuncturedFamilyCollar_isOpen F r

@[expose] public noncomputable def orderFourLinearPuncturedCarrier
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    OpenSubMulAction (orderFourLinearFamilyAction F) where
  toSubMulAction := by
    letI := orderFourLinearFamilyAction F
    exact {
      carrier := orderFourPuncturedFamilyCollar F r
      smul_mem' := by
        intro g q hq
        have hr : orderFourFamilyRadius F
          (orderFourFamilyRepresentation F g q) =
          orderFourFamilyRadius F q := by
          exact orderFourFamilyRadius_linearRepresentation F hsource g q
        change 0 < orderFourFamilyRadius F (orderFourFamilyRepresentation F g q) ∧
          orderFourFamilyRadius F (orderFourFamilyRepresentation F g q) < r
        rw [hr]
        exact hq }
  isOpen_carrier := orderFourPuncturedFamilyCollar_isOpen F r

public theorem orderThreePrincipalGauge_generator
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ)
    (q : TotalSpace (parameterMap F))
    (hq : q ∈ orderThreePuncturedFamilyCollar F r) :
    orderThreePrincipalGaugeEquiv F (orderThreeAffineFamilyGenerator F q) =
      familyDeckMap F g₁ (orderThreePrincipalGaugeEquiv F q) := by
  let w := orderThreeCayleyHomeomorph (familyTotalSpaceBase F q)
  have hw : w ≠ discCenter := by
    intro h
    have hpos := hq.1
    change 0 < ‖(w : ℂ)‖ at hpos
    rw [h] at hpos
    norm_num [discCenter] at hpos
  let B := orderThreeBranchesAt w hw
  have hwB : (w : ℂ) ∈ B.source.carrier := mem_orderThreeBranchesAt w hw
  have hqB : q ∈ orderThreeLogarithmicGaugeCarrier F r B := ⟨hq, hwB⟩
  have hbase : orderThreeCayleyHomeomorph
      (familyTotalSpaceBase F (orderThreeAffineFamilyGenerator F q)) =
      orderThreeDiscRotation w := by
    rw [familyTotalSpaceBase_orderThreeGenerator, hsource,
      orderThreeCayleyHomeomorph_generator]
  have htargetmem :
      (orderThreeCayleyHomeomorph
        (familyTotalSpaceBase F (orderThreeAffineFamilyGenerator F q)) : ℂ) ∈
        B.target.carrier := by
    rw [hbase]
    exact B.rotation_mem w hwB
  have hqgen : orderThreeAffineFamilyGenerator F q ∈
      orderThreePuncturedFamilyCollar F r := by
    simpa only [orderThreePuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
      orderThreeFamilyRadius_generator F hsource] using hq
  have htargetne : orderThreeCayleyHomeomorph
      (familyTotalSpaceBase F (orderThreeAffineFamilyGenerator F q)) ≠ discCenter := by
    intro h
    have hpos := hqgen.1
    change 0 < ‖(orderThreeCayleyHomeomorph
      (familyTotalSpaceBase F (orderThreeAffineFamilyGenerator F q)) : ℂ)‖ at hpos
    rw [h] at hpos
    norm_num [discCenter] at hpos
  calc
    orderThreePrincipalGaugeEquiv F (orderThreeAffineFamilyGenerator F q) =
        orderThreeLogarithmicGaugeMap F (fun u => B.target.log u)
          (orderThreeAffineFamilyGenerator F q) :=
      orderThreePrincipalGauge_eq_branch F B.target _ htargetmem htargetne
    _ = familyDeckMap F g₁
        (orderThreeLogarithmicGaugeMap F (fun u => B.source.log u) q) :=
      orderThreeLogarithmicGauge_conjugates_generator_on F hsource B r hqB
    _ = familyDeckMap F g₁ (orderThreePrincipalGaugeEquiv F q) := by
      rw [orderThreePrincipalGauge_eq_branch F B.source q hwB hw]

public theorem orderFourPrincipalGauge_generator
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ)
    (q : TotalSpace (parameterMap F))
    (hq : q ∈ orderFourPuncturedFamilyCollar F r) :
    orderFourPrincipalGaugeEquiv F (orderFourAffineFamilyGenerator F q) =
      familyDeckMap F g₂ (orderFourPrincipalGaugeEquiv F q) := by
  let w := orderFourCayleyHomeomorph (familyTotalSpaceBase F q)
  have hw : w ≠ discCenter := by
    intro h
    have hpos := hq.1
    change 0 < ‖(w : ℂ)‖ at hpos
    rw [h] at hpos
    norm_num [discCenter] at hpos
  let B := orderFourBranchesAt w hw
  have hwB : (w : ℂ) ∈ B.source.carrier := mem_orderFourBranchesAt w hw
  have hqB : q ∈ orderFourLogarithmicGaugeCarrier F r B := ⟨hq, hwB⟩
  have hbase : orderFourCayleyHomeomorph
      (familyTotalSpaceBase F (orderFourAffineFamilyGenerator F q)) =
      orderFourDiscRotation w := by
    rw [familyTotalSpaceBase_orderFourGenerator, hsource,
      orderFourCayleyHomeomorph_generator]
  have htargetmem :
      (orderFourCayleyHomeomorph
        (familyTotalSpaceBase F (orderFourAffineFamilyGenerator F q)) : ℂ) ∈
        B.target.carrier := by
    rw [hbase]
    exact B.rotation_mem w hwB
  have hqgen : orderFourAffineFamilyGenerator F q ∈
      orderFourPuncturedFamilyCollar F r := by
    simpa only [orderFourPuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
      orderFourFamilyRadius_generator F hsource] using hq
  have htargetne : orderFourCayleyHomeomorph
      (familyTotalSpaceBase F (orderFourAffineFamilyGenerator F q)) ≠ discCenter := by
    intro h
    have hpos := hqgen.1
    change 0 < ‖(orderFourCayleyHomeomorph
      (familyTotalSpaceBase F (orderFourAffineFamilyGenerator F q)) : ℂ)‖ at hpos
    rw [h] at hpos
    norm_num [discCenter] at hpos
  calc
    orderFourPrincipalGaugeEquiv F (orderFourAffineFamilyGenerator F q) =
        orderFourLogarithmicGaugeMap F (fun u => B.target.log u)
          (orderFourAffineFamilyGenerator F q) :=
      orderFourPrincipalGauge_eq_branch F B.target _ htargetmem htargetne
    _ = familyDeckMap F g₂
        (orderFourLogarithmicGaugeMap F (fun u => B.source.log u) q) :=
      orderFourLogarithmicGauge_conjugates_generator_on F hsource B r hqB
    _ = familyDeckMap F g₂ (orderFourPrincipalGaugeEquiv F q) := by
      rw [orderFourPrincipalGauge_eq_branch F B.source q hwB hw]

@[expose] public noncomputable def orderThreePuncturedGaugeEquivariantHomeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    EquivariantOpenHomeomorph
      (orderThreeAffineFamilyAction F) (orderThreeLinearFamilyAction F)
      (orderThreeAffinePuncturedCarrier F hsource r)
      (orderThreeLinearPuncturedCarrier F hsource r) where
  toHomeomorph := orderThreePuncturedCollarGaugeHomeomorph F hprojection r
  equivariant := equivariant_of_cyclic_generator
    (S := orderThreeAffinePuncturedCarrier F hsource r)
    (T := orderThreeLinearPuncturedCarrier F hsource r)
    (orderThreePuncturedCollarGaugeHomeomorph F hprojection r)
    (cyclicGenerator 3)
    (fun g => ⟨(Multiplicative.toAdd g).val, cyclic_eq_generator_pow g⟩) (by
      intro q
      apply Subtype.ext
      change orderThreePrincipalGaugeEquiv F
          (smulOf (orderThreeAffineFamilyAction F) (cyclicGenerator 3) q) =
        smulOf (orderThreeLinearFamilyAction F) (cyclicGenerator 3)
          (orderThreePrincipalGaugeEquiv F q)
      rw [orderThreeAffine_smulOf_generator,
        orderThreeLinear_smulOf_generator]
      exact orderThreePrincipalGauge_generator F hsource r q q.property)

@[expose] public noncomputable def orderFourPuncturedGaugeEquivariantHomeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    EquivariantOpenHomeomorph
      (orderFourAffineFamilyAction F) (orderFourLinearFamilyAction F)
      (orderFourAffinePuncturedCarrier F hsource r)
      (orderFourLinearPuncturedCarrier F hsource r) where
  toHomeomorph := orderFourPuncturedCollarGaugeHomeomorph F hprojection r
  equivariant := equivariant_of_cyclic_generator
    (S := orderFourAffinePuncturedCarrier F hsource r)
    (T := orderFourLinearPuncturedCarrier F hsource r)
    (orderFourPuncturedCollarGaugeHomeomorph F hprojection r)
    (cyclicGenerator 4)
    (fun g => ⟨(Multiplicative.toAdd g).val, cyclic_eq_generator_pow g⟩) (by
      intro q
      apply Subtype.ext
      change orderFourPrincipalGaugeEquiv F
          (smulOf (orderFourAffineFamilyAction F) (cyclicGenerator 4) q) =
        smulOf (orderFourLinearFamilyAction F) (cyclicGenerator 4)
          (orderFourPrincipalGaugeEquiv F q)
      rw [orderFourAffine_smulOf_generator,
        orderFourLinear_smulOf_generator]
      exact orderFourPrincipalGauge_generator F hsource r q q.property)

/-- The actual full order-three punctured affine collar quotient is homeomorphic to the
corresponding restricted linear cyclic quotient. -/
@[expose] public noncomputable def orderThreePuncturedCollarQuotientHomeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    (orderThreeAffinePuncturedCarrier F hsource r).OrbitQuotient ≃ₜ
    (orderThreeLinearPuncturedCarrier F hsource r).OrbitQuotient :=
  orbitQuotientHomeomorph
    (orderThreePuncturedGaugeEquivariantHomeomorph F hprojection hsource r)

/-- The actual full order-four punctured affine collar quotient is homeomorphic to the
corresponding restricted linear cyclic quotient. -/
@[expose] public noncomputable def orderFourPuncturedCollarQuotientHomeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    (orderFourAffinePuncturedCarrier F hsource r).OrbitQuotient ≃ₜ
    (orderFourLinearPuncturedCarrier F hsource r).OrbitQuotient :=
  orbitQuotientHomeomorph
    (orderFourPuncturedGaugeEquivariantHomeomorph F hprojection hsource r)

end

end SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph

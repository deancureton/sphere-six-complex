module

public import SphereSixComplex.Geometry.CuspCombinatorics
public import Mathlib.Geometry.Manifold.Instances.Quotient
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The cusp-filling action

The integral shear on `N' = ℤ² × ℤ` and an interface for its phase-corrected action on
the toric cusp model.  Construction of the infinite toric variety and the analytic estimates for
the phase functions remain explicit inputs, as in §4 of the paper.
-/

open Matrix
open SphereSixComplex.LatticeData
open SphereSixComplex.Geometry.CuspCombinatorics

noncomputable section

namespace SphereSixComplex.Geometry.CuspFilling

open Manifold

public abbrev ParameterLattice := ToricLattice
public abbrev CuspLattice := ToricLattice × ℤ

@[expose] public def shearVector (lambda : ParameterLattice) : ToricLattice :=
  B₀ *ᵥ lambda

@[expose] public def shearMap (lambda : ParameterLattice) (p : CuspLattice) : CuspLattice :=
  (p.1 + p.2 • shearVector lambda, p.2)

public theorem shearMap_zero (p : CuspLattice) : shearMap 0 p = p := by
  rcases p with ⟨y, y3⟩
  simp [shearMap, shearVector]

public theorem shearMap_add (lambda mu : ParameterLattice) (p : CuspLattice) :
    shearMap (lambda + mu) p = shearMap lambda (shearMap mu p) := by
  rcases p with ⟨y, y3⟩
  simp [shearMap, shearVector, Matrix.mulVec_add, smul_add, add_assoc]
  abel_nf

@[expose] public def shearEquiv (lambda : ParameterLattice) : CuspLattice ≃+ CuspLattice where
  toFun := shearMap lambda
  invFun := shearMap (-lambda)
  left_inv p := by
    rw [← shearMap_add]
    simp [shearMap_zero]
  right_inv p := by
    rw [← shearMap_add]
    simp [shearMap_zero]
  map_add' p q := by
    rcases p with ⟨y, y3⟩
    rcases q with ⟨z, z3⟩
    ext <;> simp [shearMap, add_smul, add_assoc, add_left_comm]

@[simp]
public theorem shearEquiv_apply (lambda : ParameterLattice) (p : CuspLattice) :
    shearEquiv lambda p = shearMap lambda p := rfl

public theorem shearEquiv_add (lambda mu : ParameterLattice) :
    (shearEquiv (lambda + mu)).toEquiv =
      (shearEquiv lambda).toEquiv * (shearEquiv mu).toEquiv := by
  apply Equiv.ext
  exact shearMap_add lambda mu

public theorem shearVector_injective : Function.Injective shearVector := by
  intro lambda mu h
  have h' := congrArg (fun x : ToricLattice ↦ B₀Inv *ᵥ x) h
  simpa [shearVector, Matrix.mulVec_mulVec, B₀_inv_mul] using h'

public theorem shear_preserves_height (lambda : ParameterLattice) (p : CuspLattice) :
    (shearMap lambda p).2 = p.2 := rfl

@[expose] public def heightOne (v : ToricLattice) : CuspLattice := (v, 1)

public theorem shear_heightOne (lambda v : ToricLattice) :
    shearMap lambda (heightOne v) = heightOne (v + shearVector lambda) := by
  simp [shearMap, heightOne]

/-- The two translation classes of triangles in the `A₂` triangulation. -/
@[expose] public def a2Triangle (upper : Bool) (v : ToricLattice) : Fin 3 → ToricLattice :=
  if upper then ![v + e₁, v + e₂, v + e₁ + e₂] else ![v, v + e₁, v + e₂]

public theorem shear_triangle_vertex (lambda v : ToricLattice) (upper : Bool) (i : Fin 3) :
    shearMap lambda (heightOne (a2Triangle upper v i)) =
      heightOne (a2Triangle upper (v + shearVector lambda) i) := by
  rw [shear_heightOne]
  by_cases h : upper
  · fin_cases i <;> simp [a2Triangle, h] <;> abel_nf
  · fin_cases i <;> simp [a2Triangle, h] <;> abel_nf

public theorem shearVector_surjective : Function.Surjective shearVector := by
  intro y
  refine ⟨B₀Inv *ᵥ y, ?_⟩
  simp [shearVector, Matrix.mulVec_mulVec, B₀_mul_inv]

/-- The toric and analytic data needed to realize the phase-corrected maps `Psi_lambda`.
The two fixed-point fields are the conclusions of the two estimates in Theorem 4.5, Step 1;
`compact_overlap_finite` is the chart estimate of Steps 2--3. -/
public structure CuspActionData (Y Phase : Type*) [CommGroup Phase] where
  t : Y → ℂ
  toricShear : ParameterLattice →+ Additive (Equiv.Perm Y)
  phaseAction : Phase →* Equiv.Perm Y
  phase : ParameterLattice → ℂ → Phase
  phase_zero : ∀ z, phase 0 z = 1
  phase_add : ∀ lambda mu z, phase (lambda + mu) z = phase lambda z * phase mu z
  shear_preserves_t : ∀ lambda p,
    t (Additive.toMul (toricShear lambda) p) = t p
  phase_preserves_t : ∀ c p, t (phaseAction c p) = t p
  shear_phase_commute : ∀ lambda c p,
    Additive.toMul (toricShear lambda) (phaseAction c p) =
      phaseAction c (Additive.toMul (toricShear lambda) p)
  fixed_off_central : ∀ lambda p, t p ≠ 0 →
    phaseAction (phase lambda (t p)) (Additive.toMul (toricShear lambda) p) = p →
      lambda = 0
  fixed_central : ∀ lambda p, t p = 0 →
    phaseAction (phase lambda (t p)) (Additive.toMul (toricShear lambda) p) = p →
      lambda = 0

namespace CuspActionData

variable {Y Phase : Type*} [CommGroup Phase] (D : CuspActionData Y Phase)

@[expose] public def psiMap (lambda : ParameterLattice) (p : Y) : Y :=
  D.phaseAction (D.phase lambda (D.t p))
    (Additive.toMul (D.toricShear lambda) p)

public theorem psiMap_preserves_t (lambda : ParameterLattice) (p : Y) :
    D.t (D.psiMap lambda p) = D.t p := by
  rw [psiMap, D.phase_preserves_t, D.shear_preserves_t]

public theorem psiMap_zero (p : Y) : D.psiMap 0 p = p := by
  simp [psiMap, D.phase_zero]

public theorem psiMap_add (lambda mu : ParameterLattice) (p : Y) :
    D.psiMap (lambda + mu) p = D.psiMap lambda (D.psiMap mu p) := by
  have ht : D.t (D.phaseAction (D.phase mu (D.t p))
      (Additive.toMul (D.toricShear mu) p)) = D.t p := by
    rw [D.phase_preserves_t, D.shear_preserves_t]
  simp only [psiMap, D.phase_add]
  rw [ht]
  rw [AddMonoidHom.map_add]
  change
    D.phaseAction (D.phase lambda (D.t p) * D.phase mu (D.t p))
      ((Additive.toMul (D.toricShear lambda) *
        Additive.toMul (D.toricShear mu)) p) = _
  rw [Equiv.Perm.mul_apply, D.shear_phase_commute]
  rw [map_mul, Equiv.Perm.mul_apply]

@[expose] public def psiEquiv (lambda : ParameterLattice) : Equiv.Perm Y where
  toFun := D.psiMap lambda
  invFun := D.psiMap (-lambda)
  left_inv p := by
    rw [← D.psiMap_add]
    simp [D.psiMap_zero]
  right_inv p := by
    rw [← D.psiMap_add]
    simp [D.psiMap_zero]

@[simp]
public theorem psiEquiv_apply (lambda : ParameterLattice) (p : Y) :
    D.psiEquiv lambda p = D.psiMap lambda p := rfl

@[expose] public noncomputable def psiRepresentation :
    Multiplicative ParameterLattice →* Equiv.Perm Y where
  toFun lambda := D.psiEquiv (Multiplicative.toAdd lambda)
  map_one' := by
    apply Equiv.ext
    exact D.psiMap_zero
  map_mul' lambda mu := by
    apply Equiv.ext
    exact D.psiMap_add _ _

@[expose, instance_reducible] public noncomputable def psiAction :
    MulAction (Multiplicative ParameterLattice) Y where
  smul lambda p := D.psiRepresentation lambda p
  one_smul p := by
    change D.psiRepresentation 1 p = p
    rw [map_one]
    rfl
  mul_smul lambda mu p := by
    change D.psiRepresentation (lambda * mu) p =
      D.psiRepresentation lambda (D.psiRepresentation mu p)
    rw [map_mul]
    rfl

public theorem psi_smul (lambda : ParameterLattice) (p : Y) :
    letI := D.psiAction
    Multiplicative.ofAdd lambda • p = D.psiMap lambda p := rfl

public theorem preserves_t (lambda : Multiplicative ParameterLattice) (p : Y) :
    letI := D.psiAction
    D.t (lambda • p) = D.t p := by
  change D.t (D.psiMap (Multiplicative.toAdd lambda) p) = D.t p
  exact D.psiMap_preserves_t _ _

public theorem centralFiber_invariant (lambda : Multiplicative ParameterLattice) (p : Y) :
    letI := D.psiAction
    D.t (lambda • p) = 0 ↔ D.t p = 0 := by
  rw [D.preserves_t]

public theorem action_free :
    letI := D.psiAction
    IsCancelSMul (Multiplicative ParameterLattice) Y := by
  let _ := D.psiAction
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro lambda p hp
  apply Multiplicative.toAdd.injective
  change Multiplicative.toAdd lambda = 0
  change D.psiMap (Multiplicative.toAdd lambda) p = p at hp
  by_cases ht : D.t p = 0
  · exact D.fixed_central _ _ ht hp
  · exact D.fixed_off_central _ _ ht hp

public theorem properlyDiscontinuous [TopologicalSpace Y]
    (hcompact : ∀ K L : Set Y, IsCompact K → IsCompact L →
      {lambda : ParameterLattice |
        (D.psiMap lambda '' K ∩ L).Nonempty}.Finite) :
    letI := D.psiAction
    ProperlyDiscontinuousSMul (Multiplicative ParameterLattice) Y := by
  let _ := D.psiAction
  refine ⟨?_⟩
  intro K L hK hL
  have hpre := (hcompact K L hK hL).preimage
    (Set.injOn_of_injective Multiplicative.toAdd.injective)
  change {gamma : Multiplicative ParameterLattice |
    (D.psiMap (Multiplicative.toAdd gamma) '' K ∩ L).Nonempty}.Finite
  exact hpre

end CuspActionData

/-- The standard quotient-covering conclusion once continuity of the toric realization is supplied. -/
public theorem quotient_isQuotientCoveringMap
    {Y Phase : Type*} [CommGroup Phase] [TopologicalSpace Y]
    [T2Space Y] [LocallyCompactSpace Y]
    (D : CuspActionData Y Phase)
    (hcontinuous : ∀ lambda : ParameterLattice, Continuous (D.psiMap lambda))
    (hcompact : ∀ K L : Set Y, IsCompact K → IsCompact L →
      {lambda : ParameterLattice |
        (D.psiMap lambda '' K ∩ L).Nonempty}.Finite) :
    letI := D.psiAction
    IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice) Y))
      (Multiplicative ParameterLattice) := by
  let _ := D.psiAction
  let _ : IsCancelSMul (Multiplicative ParameterLattice) Y := D.action_free
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice) Y :=
    ⟨by
      intro lambda
      change Continuous (D.psiMap (Multiplicative.toAdd lambda))
      exact hcontinuous _⟩
  let _ : ProperlyDiscontinuousSMul (Multiplicative ParameterLattice) Y :=
    D.properlyDiscontinuous hcompact
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- The charted-space part of the quotient-manifold construction available in Mathlib. -/
public theorem quotient_chartedSpace
    {Y Phase H : Type*} [CommGroup Phase] [TopologicalSpace Y] [TopologicalSpace H]
    [T2Space Y] [LocallyCompactSpace Y] [ChartedSpace H Y]
    (D : CuspActionData Y Phase)
    (hcontinuous : ∀ lambda : ParameterLattice, Continuous (D.psiMap lambda))
    (hcompact : ∀ K L : Set Y, IsCompact K → IsCompact L →
      {lambda : ParameterLattice |
        (D.psiMap lambda '' K ∩ L).Nonempty}.Finite) :
    letI := D.psiAction
    Nonempty (ChartedSpace H
      (MulAction.orbitRel.Quotient (Multiplicative ParameterLattice) Y)) := by
  let _ := D.psiAction
  let _ : IsCancelSMul (Multiplicative ParameterLattice) Y := D.action_free
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice) Y :=
    ⟨by
      intro lambda
      change Continuous (D.psiMap (Multiplicative.toAdd lambda))
      exact hcontinuous _⟩
  let _ : ProperlyDiscontinuousSMul (Multiplicative ParameterLattice) Y :=
    D.properlyDiscontinuous hcompact
  exact ⟨inferInstance⟩

/-- Two local sheets of a quotient covering differ locally by a deck transformation. -/
public theorem localInverse_transition_eq_deck
    {G Y Q : Type*} [Group G] [TopologicalSpace Y] [TopologicalSpace Q]
    [MulAction G Y] [ContinuousConstSMul G Y]
    {f : Y → Q} (hf : IsQuotientCoveringMap f G)
    (a b y : Y)
    (hy : y ∈ ((hf.isCoveringMap.isLocalHomeomorph.localInverseAt a).symm.trans
      (hf.isCoveringMap.isLocalHomeomorph.localInverseAt b)).source) :
    ∃ g : G, ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧
      U ⊆ ((hf.isCoveringMap.isLocalHomeomorph.localInverseAt a).symm.trans
        (hf.isCoveringMap.isLocalHomeomorph.localInverseAt b)).source ∧
      Set.EqOn
        ((hf.isCoveringMap.isLocalHomeomorph.localInverseAt a).symm.trans
          (hf.isCoveringMap.isLocalHomeomorph.localInverseAt b))
        (fun z ↦ g • z)
        (((hf.isCoveringMap.isLocalHomeomorph.localInverseAt a).symm.trans
          (hf.isCoveringMap.isLocalHomeomorph.localInverseAt b)).source ∩ U) := by
  let hloc := hf.isCoveringMap.isLocalHomeomorph
  let l₁ := hloc.localInverseAt a
  let l₂ := hloc.localInverseAt b
  have hy' : y ∈ l₁.target ∧ f y ∈ l₂.source := by
    rw [OpenPartialHomeomorph.trans_source] at hy
    simpa [l₁, l₂, hloc.localInverseAt_symm] using hy
  have hfy : f (l₂ (f y)) = f y := hloc.apply_localInverseAt_of_mem hy'.2
  obtain ⟨g, hg⟩ := hf.apply_eq_iff_mem_orbit.mp hfy
  change g • y = l₂ (f y) at hg
  refine ⟨g, l₁.target ∩ f ⁻¹' l₂.source ∩ (fun z ↦ g • z) ⁻¹' l₂.target,
    ?_, ?_, ?_, ?_⟩
  · exact (l₁.open_target.inter (l₂.open_source.preimage hf.continuous)).inter
      (l₂.open_target.preimage (continuous_const_smul g))
  · refine ⟨⟨hy'.1, hy'.2⟩, ?_⟩
    change g • y ∈ l₂.target
    rw [hg]
    exact l₂.map_source hy'.2
  · intro z hz
    rw [OpenPartialHomeomorph.trans_source]
    simpa [l₁, l₂, hloc.localInverseAt_symm] using hz.1
  · intro z hz
    have hzf : f z ∈ l₂.source := hz.2.1.2
    have heq : l₂ (f z) = g • z := by
      apply hloc.injOn_localInverseAt_target (l₂.map_source hzf) hz.2.2
      rw [hloc.apply_localInverseAt_of_mem hzf, hf.map_smul]
    simpa [l₁, l₂, hloc.localInverseAt_symm] using heq

/-- A smooth deck transformation followed by a manifold chart belongs to the maximal atlas. -/
public theorem deck_trans_chart_mem_maximalAtlas
    {G Y E H : Type*} [Group G] [TopologicalSpace Y] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (I : ModelWithCorners ℂ E H) [ChartedSpace H Y] [IsManifold I ω Y]
    [MulAction G Y] (hdeck : ∀ g : G, ContMDiff I I ω fun z : Y ↦ g • z)
    (g : G) (b : Y) :
    let d : Y ≃ₜ Y := Homeomorph.mk (MulAction.toPerm g)
      (hdeck g).continuous (by
        change Continuous fun z : Y ↦ g⁻¹ • z
        exact (hdeck g⁻¹).continuous)
    d.toOpenPartialHomeomorph.trans (chartAt H b) ∈
      IsManifold.maximalAtlas I ω Y := by
  let d : Y ≃ₜ Y := Homeomorph.mk (MulAction.toPerm g)
    (hdeck g).continuous (by
      change Continuous fun z : Y ↦ g⁻¹ • z
      exact (hdeck g⁻¹).continuous)
  let phi := d.toOpenPartialHomeomorph.trans (chartAt H b)
  apply phi.mem_maximalAtlas_of_contMDiffOn
  · have hgOn : ContMDiffOn I I ω (fun z : Y ↦ g • z) Set.univ :=
      (hdeck g).contMDiffOn
    have hc : ContMDiffOn I I ω (chartAt H b) (chartAt H b).source :=
      contMDiffOn_chart
    have h := hc.comp' hgOn
    change ContMDiffOn I I ω (fun z : Y ↦ chartAt H b (g • z)) phi.source
    convert h using 1
    · rfl
    · change (d.toOpenPartialHomeomorph.trans (chartAt H b)).source =
        Set.univ ∩ (fun z : Y ↦ g • z) ⁻¹' (chartAt H b).source
      rw [OpenPartialHomeomorph.trans_source]
      simp only [Homeomorph.toOpenPartialHomeomorph_source, Set.univ_inter]
      ext z
      rfl
  · have hgOn : ContMDiffOn I I ω (fun z : Y ↦ g⁻¹ • z) Set.univ :=
      (hdeck g⁻¹).contMDiffOn
    have hc : ContMDiffOn I I ω (chartAt H b).symm (chartAt H b).target :=
      contMDiffOn_chart_symm
    have h := hgOn.comp' hc
    change ContMDiffOn I I ω
      (fun z : H ↦ g⁻¹ • (chartAt H b).symm z) phi.target
    convert h using 1
    · rfl
    · change (d.toOpenPartialHomeomorph.trans (chartAt H b)).target =
        (chartAt H b).target ∩ (chartAt H b).symm ⁻¹' Set.univ
      rw [OpenPartialHomeomorph.trans_target]
      simp

/-- The quotient atlas of a smooth quotient covering has smooth transition maps. -/
public theorem quotient_hasGroupoid
    {G Y Q E H : Type*} [Group G] [TopologicalSpace Y] [TopologicalSpace Q]
    [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (I : ModelWithCorners ℂ E H)
    [ChartedSpace H Y] [IsManifold I ω Y]
    [MulAction G Y] [ContinuousConstSMul G Y]
    {f : Y → Q} (hf : IsQuotientCoveringMap f G)
    (hdeck : ∀ g : G, ContMDiff I I ω fun z : Y ↦ g • z) :
    letI : ChartedSpace H Q :=
      hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective
    HasGroupoid Q (contDiffGroupoid ω I) := by
  let hloc := hf.isCoveringMap.isLocalHomeomorph
  let _ : ChartedSpace H Q := hloc.chartedSpace hf.surjective
  constructor
  intro e e' he he'
  change e ∈ {hloc.localInverseAt
      (hf.surjective.hasRightInverse.choose q) |>.trans
        (chartAt H (hf.surjective.hasRightInverse.choose q)) | q : Q} at he
  change e' ∈ {hloc.localInverseAt
      (hf.surjective.hasRightInverse.choose q) |>.trans
        (chartAt H (hf.surjective.hasRightInverse.choose q)) | q : Q} at he'
  rcases he with ⟨q, rfl⟩
  rcases he' with ⟨q', rfl⟩
  let a := hf.surjective.hasRightInverse.choose q
  let b := hf.surjective.hasRightInverse.choose q'
  let l₁ := hloc.localInverseAt a
  let l₂ := hloc.localInverseAt b
  let c₁ := chartAt H a
  let c₂ := chartAt H b
  let tau := (l₁.trans c₁).symm.trans (l₂.trans c₂)
  apply (contDiffGroupoid ω I).locality
  intro x hx
  change x ∈ tau.source at hx
  have hx' : (x ∈ c₁.target ∧ c₁.symm x ∈ l₁.target) ∧
      f (c₁.symm x) ∈ l₂.source ∧ l₂ (f (c₁.symm x)) ∈ c₂.source := by
    simpa [tau, l₁, l₂, c₁, c₂, OpenPartialHomeomorph.trans_source] using hx
  have hy : c₁.symm x ∈ (l₁.symm.trans l₂).source := by
    rw [OpenPartialHomeomorph.trans_source]
    simpa [l₁, hloc.localInverseAt_symm] using And.intro hx'.1.2 hx'.2.1
  obtain ⟨g, U, hU, hyU, hUsub, hEq⟩ :=
    localInverse_transition_eq_deck hf a b (c₁.symm x) hy
  let d : Y ≃ₜ Y := Homeomorph.mk (MulAction.toPerm g)
    (hdeck g).continuous (by
      change Continuous fun z : Y ↦ g⁻¹ • z
      exact (hdeck g⁻¹).continuous)
  let delta := c₁.symm.trans (d.toOpenPartialHomeomorph.trans c₂)
  have hdelta : delta ∈ contDiffGroupoid ω I := by
    apply IsManifold.compatible_of_mem_maximalAtlas
    · exact IsManifold.chart_mem_maximalAtlas a
    · exact deck_trans_chart_mem_maximalAtlas I hdeck g b
  let s := c₁.target ∩ c₁.symm ⁻¹' U
  have hs : IsOpen s :=
    c₁.symm.continuousOn_toFun.isOpen_inter_preimage c₁.open_target hU
  have hxs : x ∈ s := ⟨hx'.1.1, hyU⟩
  refine ⟨s, hs, hxs, ?_⟩
  apply (contDiffGroupoid ω I).mem_of_eqOnSource
    (closedUnderRestriction' hdelta hs)
  change (tau.restr s).EqOnSource (delta.restr s)
  constructor
  · rw [OpenPartialHomeomorph.restr_source, OpenPartialHomeomorph.restr_source,
      hs.interior_eq]
    ext z
    simp only [tau, delta, s, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      Set.mem_inter_iff, Set.mem_preimage]
    simp only [l₁, l₂]
    simp only [d, Homeomorph.toOpenPartialHomeomorph_source, Set.mem_univ, true_and]
    constructor
    · rintro ⟨hz, hzT, hzU⟩
      have hySource := hUsub hzU
      have hyEq : l₂ (f (c₁.symm z)) = g • c₁.symm z := by
        simpa [l₁, l₂, hloc.localInverseAt_symm] using hEq ⟨hySource, hzU⟩
      refine ⟨⟨hzT, ?_⟩, hzT, hzU⟩
      change g • c₁.symm z ∈ c₂.source
      rw [← hyEq]
      simpa [l₁, hloc.localInverseAt_symm] using hz.2.2
    · rintro ⟨hz, hzT, hzU⟩
      have hySource := hUsub hzU
      have hySource' : c₁.symm z ∈ l₁.target ∧ f (c₁.symm z) ∈ l₂.source := by
        simpa [l₁, l₂, hloc.localInverseAt_symm,
          OpenPartialHomeomorph.trans_source] using hySource
      have hyEq : l₂ (f (c₁.symm z)) = g • c₁.symm z := by
        simpa [l₁, l₂, hloc.localInverseAt_symm] using hEq ⟨hySource, hzU⟩
      refine ⟨⟨⟨hzT, hySource'.1⟩, ?_, ?_⟩, hzT, hzU⟩
      · simpa [l₁, hloc.localInverseAt_symm] using hySource'.2
      have hz' := hz.2
      change g • c₁.symm z ∈ c₂.source at hz'
      rw [← hyEq] at hz'
      simpa [l₁, hloc.localInverseAt_symm] using hz'
  · intro z hz
    have hzs : z ∈ s := by
      rw [OpenPartialHomeomorph.restr_source, hs.interior_eq] at hz
      exact hz.2
    have hyU' : c₁.symm z ∈ U := hzs.2
    have hyEq : l₂ (f (c₁.symm z)) = g • c₁.symm z := by
      simpa [l₁, l₂, hloc.localInverseAt_symm] using
        hEq ⟨hUsub hyU', hyU'⟩
    rw [OpenPartialHomeomorph.restr_apply, OpenPartialHomeomorph.restr_apply]
    simp only [tau, delta, OpenPartialHomeomorph.coe_trans,
      OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply]
    rw [show l₁.symm (c₁.symm z) = f (c₁.symm z) by
      exact congrFun (hloc.localInverseAt_symm a) (c₁.symm z)]
    change c₂ (l₂ (f (c₁.symm z))) = c₂ (g • c₁.symm z)
    rw [hyEq]

/-- A smooth quotient covering inherits a smooth manifold structure from its source. -/
public theorem quotient_isManifold
    {G Y Q E H : Type*} [Group G] [TopologicalSpace Y] [TopologicalSpace Q]
    [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (I : ModelWithCorners ℂ E H)
    [ChartedSpace H Y] [IsManifold I ω Y]
    [MulAction G Y] [ContinuousConstSMul G Y]
    {f : Y → Q} (hf : IsQuotientCoveringMap f G)
    (hdeck : ∀ g : G, ContMDiff I I ω fun z : Y ↦ g • z) :
    letI : ChartedSpace H Q :=
      hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective
    IsManifold I ω Q := by
  let _ : ChartedSpace H Q :=
    hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective
  let _ : HasGroupoid Q (contDiffGroupoid ω I) := quotient_hasGroupoid I hf hdeck
  exact IsManifold.mk

/-- The phase-corrected cusp quotient is a complex manifold when all deck maps are analytic. -/
public theorem cuspQuotient_isManifold
    {Y Phase E H : Type*} [CommGroup Phase] [TopologicalSpace Y] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (I : ModelWithCorners ℂ E H)
    [T2Space Y] [LocallyCompactSpace Y] [ChartedSpace H Y] [IsManifold I ω Y]
    (D : CuspActionData Y Phase)
    (hholomorphic : ∀ lambda : ParameterLattice, ContMDiff I I ω (D.psiMap lambda))
    (hcompact : ∀ K L : Set Y, IsCompact K → IsCompact L →
      {lambda : ParameterLattice |
        (D.psiMap lambda '' K ∩ L).Nonempty}.Finite) :
    letI := D.psiAction
    let hf := quotient_isQuotientCoveringMap D
      (fun lambda ↦ (hholomorphic lambda).continuous) hcompact
    letI : ChartedSpace H
      (MulAction.orbitRel.Quotient (Multiplicative ParameterLattice) Y) :=
      hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective
    IsManifold I ω
      (MulAction.orbitRel.Quotient (Multiplicative ParameterLattice) Y) := by
  let _ := D.psiAction
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice) Y :=
    ⟨by
      intro gamma
      change Continuous (D.psiMap (Multiplicative.toAdd gamma))
      exact (hholomorphic _).continuous⟩
  let hf := quotient_isQuotientCoveringMap D
    (fun lambda ↦ (hholomorphic lambda).continuous) hcompact
  let _ : ChartedSpace H
      (MulAction.orbitRel.Quotient (Multiplicative ParameterLattice) Y) :=
    hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective
  apply quotient_isManifold I hf
  intro gamma
  change ContMDiff I I ω (D.psiMap (Multiplicative.toAdd gamma))
  exact hholomorphic _

/-- A local homeomorphism between charted spaces is a local diffeomorphism at regularity zero.
This is the strongest implication available without smooth compatibility of the target atlas. -/
public theorem isLocalDiffeomorph_zero_of_isLocalHomeomorph
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {H₁ H₂ : Type*} [TopologicalSpace H₁] [TopologicalSpace H₂]
    {I : ModelWithCorners 𝕜 E H₁} {J : ModelWithCorners 𝕜 F H₂}
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H₁ M] [ChartedSpace H₂ N] {f : M → N}
    (hf : IsLocalHomeomorph f) : IsLocalDiffeomorph I J 0 f := by
  intro x
  obtain ⟨e, hx, he⟩ := hf x
  let Phi : PartialDiffeomorph I J M N 0 :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiffOn_zero_iff.mpr e.continuousOn
      contMDiffOn_invFun := contMDiffOn_zero_iff.mpr e.continuousOn_symm }
  refine ⟨Phi, hx, ?_⟩
  intro y _
  exact congrFun he y

/-- The regularity-zero corollary for the quotient atlas. -/
public theorem quotient_isManifold_zero
    {Y Phase E H : Type*} [CommGroup Phase] [TopologicalSpace Y] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (I : ModelWithCorners ℂ E H)
    [T2Space Y] [LocallyCompactSpace Y] [ChartedSpace H Y] [IsManifold I ω Y]
    (D : CuspActionData Y Phase)
    (hholomorphic : ∀ lambda : ParameterLattice, ContMDiff I I ω (D.psiMap lambda))
    (hcompact : ∀ K L : Set Y, IsCompact K → IsCompact L →
      {lambda : ParameterLattice |
        (D.psiMap lambda '' K ∩ L).Nonempty}.Finite) :
    letI := D.psiAction
    letI : ChartedSpace H
      (MulAction.orbitRel.Quotient (Multiplicative ParameterLattice) Y) :=
      (quotient_chartedSpace D (fun lambda ↦ (hholomorphic lambda).continuous) hcompact).some
    IsManifold I 0
      (MulAction.orbitRel.Quotient (Multiplicative ParameterLattice) Y) := by
  let _ := D.psiAction
  let _ : ChartedSpace H
      (MulAction.orbitRel.Quotient (Multiplicative ParameterLattice) Y) :=
    (quotient_chartedSpace D (fun lambda ↦ (hholomorphic lambda).continuous) hcompact).some
  infer_instance

/-- For the induced quotient atlas, the quotient projection is a `C⁰` local diffeomorphism.
The covering-map API supplies the local homeomorphism, and regularity zero is continuity. -/
public theorem quotient_projection_isLocalDiffeomorph_zero
    {Y Phase E H : Type*} [CommGroup Phase] [TopologicalSpace Y] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (I : ModelWithCorners ℂ E H)
    [T2Space Y] [LocallyCompactSpace Y] [ChartedSpace H Y] [IsManifold I ω Y]
    (D : CuspActionData Y Phase)
    (hholomorphic : ∀ lambda : ParameterLattice, ContMDiff I I ω (D.psiMap lambda))
    (hcompact : ∀ K L : Set Y, IsCompact K → IsCompact L →
      {lambda : ParameterLattice |
        (D.psiMap lambda '' K ∩ L).Nonempty}.Finite) :
    letI := D.psiAction
    letI : ChartedSpace H
      (MulAction.orbitRel.Quotient (Multiplicative ParameterLattice) Y) :=
      (quotient_chartedSpace D (fun lambda ↦ (hholomorphic lambda).continuous) hcompact).some
    IsLocalDiffeomorph I I 0
      (Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice) Y)) := by
  let _ := D.psiAction
  let _ : ChartedSpace H
      (MulAction.orbitRel.Quotient (Multiplicative ParameterLattice) Y) :=
    (quotient_chartedSpace D (fun lambda ↦ (hholomorphic lambda).continuous) hcompact).some
  apply isLocalDiffeomorph_zero_of_isLocalHomeomorph
  exact (quotient_isQuotientCoveringMap D
    (fun lambda ↦ (hholomorphic lambda).continuous) hcompact).isCoveringMap _ _
    |>.isLocalHomeomorph

end SphereSixComplex.Geometry.CuspFilling

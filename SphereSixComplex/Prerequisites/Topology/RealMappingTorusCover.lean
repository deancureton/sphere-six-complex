module

public import SphereSixComplex.Prerequisites.Geometry.QuotientTopology
public import SphereSixComplex.Prerequisites.Topology.CyclicPuncturedProductMappingTorus

open Set Topology
namespace SphereSixComplex.CyclicAngularFundamentalDomain
noncomputable section

variable {T : Type} [TopologicalSpace T]

/-- The integer deck action whose orbit quotient is `RealMappingTorus φ`. -/
@[expose, instance_reducible] public noncomputable def realMappingTorusDeckAction
    (φ : T ≃ₜ T) : MulAction (Multiplicative ℤ) (ℝ × T) where
  smul k p := mappingTorusShift φ (Multiplicative.toAdd k) p
  one_smul p := mappingTorusShift_zero φ p
  mul_smul k l p := by
    change mappingTorusShift φ (Multiplicative.toAdd k + Multiplicative.toAdd l) p =
      mappingTorusShift φ (Multiplicative.toAdd k)
        (mappingTorusShift φ (Multiplicative.toAdd l) p)
    exact mappingTorusShift_add φ (Multiplicative.toAdd k) (Multiplicative.toAdd l) p

public theorem realMappingTorusDeckAction_smul
    (φ : T ≃ₜ T) (k : Multiplicative ℤ) (p : ℝ × T) :
    letI := realMappingTorusDeckAction φ
    k • p = mappingTorusShift φ (Multiplicative.toAdd k) p :=
  rfl

/-- The mapping-torus deck action is free because it translates the real coordinate by an
integer. -/
public theorem realMappingTorusDeckAction_free (φ : T ≃ₜ T) :
    letI := realMappingTorusDeckAction φ
    IsCancelSMul (Multiplicative ℤ) (ℝ × T) := by
  let _ := realMappingTorusDeckAction φ
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro k p hp
  have hfst := congrArg Prod.fst hp
  change p.1 - ((Multiplicative.toAdd k : ℤ) : ℝ) = p.1 at hfst
  have hk : Multiplicative.toAdd k = 0 := by
    exact_mod_cast (sub_eq_self.mp hfst)
  exact Multiplicative.toAdd.injective (by simpa using hk)

/-- Every mapping-torus deck transformation is continuous. -/
public theorem realMappingTorusDeckAction_continuous (φ : T ≃ₜ T) :
    letI := realMappingTorusDeckAction φ
    ContinuousConstSMul (Multiplicative ℤ) (ℝ × T) := by
  let _ := realMappingTorusDeckAction φ
  refine ⟨fun k ↦ ?_⟩
  exact (mappingTorusShift φ (Multiplicative.toAdd k)).continuous

/-- Proper discontinuity follows solely from boundedness of the real-coordinate projections of
compact sets. -/
public theorem realMappingTorusDeckAction_properlyDiscontinuous (φ : T ≃ₜ T) :
    letI := realMappingTorusDeckAction φ
    ProperlyDiscontinuousSMul (Multiplicative ℤ) (ℝ × T) := by
  let _ := realMappingTorusDeckAction φ
  refine ⟨?_⟩
  intro K L hK hL
  have hKreal : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  have hLreal : IsCompact (Prod.fst '' L) := hL.image continuous_fst
  obtain ⟨aK, haK⟩ := hKreal.bddBelow
  obtain ⟨bK, hbK⟩ := hKreal.bddAbove
  obtain ⟨aL, haL⟩ := hLreal.bddBelow
  obtain ⟨bL, hbL⟩ := hLreal.bddAbove
  have hfinite :
      {k : Multiplicative ℤ |
        Multiplicative.toAdd k ∈ Set.Icc (Int.ceil (aK - bL)) (Int.floor (bK - aL))}.Finite :=
    (Set.finite_Icc (Int.ceil (aK - bL)) (Int.floor (bK - aL))).preimage
      Multiplicative.toAdd.injective.injOn
  apply hfinite.subset
  intro k hk
  rcases hk with ⟨q, ⟨p, hpK, hpq⟩, hqL⟩
  have hpLower : aK ≤ p.1 := haK ⟨p, hpK, rfl⟩
  have hpUpper : p.1 ≤ bK := hbK ⟨p, hpK, rfl⟩
  have hqLower : aL ≤ q.1 := haL ⟨q, hqL, rfl⟩
  have hqUpper : q.1 ≤ bL := hbL ⟨q, hqL, rfl⟩
  have hpqReal := congrArg Prod.fst hpq
  change p.1 - ((Multiplicative.toAdd k : ℤ) : ℝ) = q.1 at hpqReal
  constructor
  · rw [Int.ceil_le]
    linarith
  · rw [Int.le_floor]
    linarith

/-- The explicit real mapping-torus relation is the orbit relation of the deck action. -/
public theorem realMappingTorusSetoid_eq_orbitRel (φ : T ≃ₜ T) :
    letI := realMappingTorusDeckAction φ
    realMappingTorusSetoid φ = MulAction.orbitRel (Multiplicative ℤ) (ℝ × T) := by
  let _ := realMappingTorusDeckAction φ
  apply Setoid.ext
  intro p q
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨Multiplicative.ofAdd (-k), ?_⟩
    change mappingTorusShift φ (-k) (mappingTorusShift φ k p) = p
    rw [← mappingTorusShift_add, neg_add_cancel, mappingTorusShift_zero]
  · rintro ⟨k, hk⟩
    refine ⟨-(Multiplicative.toAdd k), ?_⟩
    change mappingTorusShift φ (Multiplicative.toAdd k) q = p at hk
    rw [← hk, ← mappingTorusShift_add, neg_add_cancel, mappingTorusShift_zero]

/-- The quotient map `ℝ × T → RealMappingTorus φ` is a regular covering with deck group `ℤ`. -/
public theorem realMappingTorusMk_isQuotientCoveringMap
    [T2Space T] [LocallyCompactSpace T] (φ : T ≃ₜ T) :
    letI := realMappingTorusDeckAction φ
    IsQuotientCoveringMap (Quotient.mk (realMappingTorusSetoid φ)) (Multiplicative ℤ) := by
  let _ := realMappingTorusDeckAction φ
  let _ : IsCancelSMul (Multiplicative ℤ) (ℝ × T) :=
    realMappingTorusDeckAction_free φ
  let _ : ContinuousConstSMul (Multiplicative ℤ) (ℝ × T) :=
    realMappingTorusDeckAction_continuous φ
  let _ : ProperlyDiscontinuousSMul (Multiplicative ℤ) (ℝ × T) :=
    realMappingTorusDeckAction_properlyDiscontinuous φ
  rw [realMappingTorusSetoid_eq_orbitRel φ]
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- The real mapping-torus quotient map, viewed only as a covering map. -/
public theorem realMappingTorusMk_isCoveringMap
    [T2Space T] [LocallyCompactSpace T] (φ : T ≃ₜ T) :
    IsCoveringMap (Quotient.mk (realMappingTorusSetoid φ)) := by
  let _ := realMappingTorusDeckAction φ
  exact (realMappingTorusMk_isQuotientCoveringMap φ).isCoveringMap

/-- The same real-line cover, transported to the cylinder presentation `CircleMappingTorus`. -/
@[expose] public def circleMappingTorusRealCoverProjection (φ : T ≃ₜ T) :
    C(ℝ × T, CircleMappingTorus φ) where
  toFun p := realMappingTorusHomeomorph φ
    (Quotient.mk (realMappingTorusSetoid φ) p)
  continuous_toFun :=
    (realMappingTorusHomeomorph φ).continuous.comp continuous_quot_mk

/-- The transported real-line projection is a regular integer covering. -/
public theorem circleMappingTorusRealCoverProjection_isQuotientCoveringMap
    [T2Space T] [LocallyCompactSpace T] (φ : T ≃ₜ T) :
    letI := realMappingTorusDeckAction φ
    IsQuotientCoveringMap (circleMappingTorusRealCoverProjection φ) (Multiplicative ℤ) := by
  let _ := realMappingTorusDeckAction φ
  change IsQuotientCoveringMap
    ((realMappingTorusHomeomorph φ) ∘ Quotient.mk (realMappingTorusSetoid φ))
      (Multiplicative ℤ)
  exact (realMappingTorusMk_isQuotientCoveringMap φ).homeomorph_comp
    (realMappingTorusHomeomorph φ)

/-- The transported real-line projection is a covering map. -/
public theorem circleMappingTorusRealCoverProjection_isCoveringMap
    [T2Space T] [LocallyCompactSpace T] (φ : T ≃ₜ T) :
    IsCoveringMap (circleMappingTorusRealCoverProjection φ) := by
  let _ := realMappingTorusDeckAction φ
  exact (circleMappingTorusRealCoverProjection_isQuotientCoveringMap φ).isCoveringMap

/-- For a contractible fibre, the explicit total space of the real mapping-torus cover is simply
connected. -/
public theorem realMappingTorusCoverSource_simplyConnected [ContractibleSpace T] :
    SimplyConnectedSpace (ℝ × T) := by
  infer_instance

/-- Adding the open radial collar coordinate preserves simple connectedness of the explicit
covering space. -/
public theorem radialRealMappingTorusCoverSource_simplyConnected
    [ContractibleSpace T] {r : ℝ} (hr : 0 < r) :
    SimplyConnectedSpace (RadialInterval r × ℝ × T) := by
  let _ : ContractibleSpace (RadialInterval r) :=
    (convex_Ioo (0 : ℝ) r).contractibleSpace (Set.nonempty_Ioo.mpr hr)
  infer_instance

end
end SphereSixComplex.CyclicAngularFundamentalDomain

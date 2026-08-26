module

public import SphereSixComplex.Topology.TwicePuncturedComplexMarkedMeridians
public import SphereSixComplex.Topology.EstablishedBasedVanKampen
public import SphereSixComplex.Topology.ManifoldLocallyContractible
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Generation of the twice-punctured-plane fundamental group

The two vertical half-planes form an open cover with contractible overlap.  The covering-space
form of van Kampen therefore says that the images of their fundamental groups generate the
ambient fundamental group.  Combining this with the explicit winding computations for the two
local pieces shows that the two marked clockwise meridians generate.
-/

@[expose] public section

noncomputable section

open Set Topology CategoryTheory TauCeti TauCeti.UniversalCover
open scoped ContinuousMap

namespace SphereSixComplex.Topology

namespace TwicePuncturedComplex

/-- Homotopy equivalence preserves path-connectedness. -/
public theorem pathConnectedSpace_of_homotopyEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace Y] (e : X ≃ₕ Y) : PathConnectedSpace X where
  nonempty := ⟨e.symm (Classical.choice (inferInstance : Nonempty Y))⟩
  joined x y := ⟨(e.left_inv.some.evalAt x).symm.trans
    ((PathConnectedSpace.somePath (e x) (e y)).map e.invFun.continuous) |>.trans
      (e.left_inv.some.evalAt y)⟩

public theorem ambient_isOpen : IsOpen (({0, 1} : Set ℂ)ᶜ) :=
  (Set.toFinite ({0, 1} : Set ℂ)).isClosed.isOpen_compl

public theorem ambient_pathConnected : PathConnectedSpace TwicePuncturedComplex := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  exact Set.Countable.isPathConnected_compl_of_one_lt_rank (by
    rw [Complex.rank_real_complex]
    norm_num) (Set.toFinite ({0, 1} : Set ℂ)).to_countable

public theorem ambient_locallyPathConnected : LocallyPathConnectedSpace TwicePuncturedComplex := by
  have _ : StronglyLocallyContractibleSpace ℂ :=
    SphereSixComplex.normedSpace_stronglyLocallyContractibleSpace
  have _ : StronglyLocallyContractibleSpace TwicePuncturedComplex :=
    ambient_isOpen.stronglyLocallyContractibleSpace
  infer_instance

public theorem ambient_semilocallySimplyConnected :
    TauCeti.SemilocallySimplyConnectedSpace TwicePuncturedComplex := by
  have _ : StronglyLocallyContractibleSpace ℂ :=
    SphereSixComplex.normedSpace_stronglyLocallyContractibleSpace
  have _ : StronglyLocallyContractibleSpace TwicePuncturedComplex :=
    ambient_isOpen.stronglyLocallyContractibleSpace
  infer_instance

public theorem left_isPathConnected : IsPathConnected twicePuncturedComplexLeft := by
  have _ : PathConnectedSpace PuncturedComplex := by
    change PathConnectedSpace (↑({0}ᶜ : Set ℂ))
    rw [← isPathConnected_iff_pathConnectedSpace]
    exact Set.Countable.isPathConnected_compl_of_one_lt_rank (by
      rw [Complex.rank_real_complex]
      norm_num) (Set.countable_singleton 0)
  have _ : PathConnectedSpace twicePuncturedComplexLeft :=
    pathConnectedSpace_of_homotopyEquiv
      twicePuncturedComplexLeftHomotopyEquivPuncturedComplex
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

public theorem right_isPathConnected : IsPathConnected twicePuncturedComplexRight := by
  have _ : PathConnectedSpace PuncturedComplex := by
    change PathConnectedSpace (↑({0}ᶜ : Set ℂ))
    rw [← isPathConnected_iff_pathConnectedSpace]
    exact Set.Countable.isPathConnected_compl_of_one_lt_rank (by
      rw [Complex.rank_real_complex]
      norm_num) (Set.countable_singleton 0)
  have _ : PathConnectedSpace twicePuncturedComplexRight :=
    pathConnectedSpace_of_homotopyEquiv
      twicePuncturedComplexRightHomotopyEquivPuncturedComplex
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

/-- The left-piece inclusion into the twice-punctured plane. -/
public def leftInclusion : C(twicePuncturedComplexLeft, TwicePuncturedComplex) :=
  PaperVanKampenFourPieceCover.subsetInclusion twicePuncturedComplexLeft

/-- The right-piece inclusion into the twice-punctured plane. -/
public def rightInclusion : C(twicePuncturedComplexRight, TwicePuncturedComplex) :=
  PaperVanKampenFourPieceCover.subsetInclusion twicePuncturedComplexRight

/-- The map on based fundamental groups induced by the left inclusion. -/
public def leftFundamentalGroupMap :
    FundamentalGroup twicePuncturedComplexLeft twicePuncturedComplexLeftBasepoint →*
      FundamentalGroup TwicePuncturedComplex twicePuncturedComplexBasepoint :=
  FundamentalGroup.map leftInclusion twicePuncturedComplexLeftBasepoint

/-- The map on based fundamental groups induced by the right inclusion. -/
public def rightFundamentalGroupMap :
    FundamentalGroup twicePuncturedComplexRight twicePuncturedComplexRightBasepoint →*
      FundamentalGroup TwicePuncturedComplex twicePuncturedComplexBasepoint :=
  FundamentalGroup.map rightInclusion twicePuncturedComplexRightBasepoint

/-- The cyclic exponential-cover deck group is generated by the deck value of one clockwise
turn. -/
public theorem complexExpDeckGroup_generated_by_negOne :
    Subgroup.closure
      ({MulOpposite.op (Multiplicative.ofAdd (complexExpDeckMultiple (-1)))} :
        Set (Multiplicative ComplexExpDeckGroup)ᵐᵒᵖ) = ⊤ := by
  apply top_unique
  intro y _
  rw [Subgroup.mem_closure_singleton]
  let d := (MulOpposite.unop y).toAdd
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp d.property
  refine ⟨-n, ?_⟩
  apply MulOpposite.unop_injective
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  change ((↑((-n) • complexExpDeckMultiple (-1)) : ℂ)) = d.1
  rw [← hn]
  simp [complexExpDeckMultiple]

/-- The marked zero meridian generates the local fundamental group of the left piece. -/
public theorem leftFundamentalGroup_generated_by_meridian :
    Subgroup.closure
      ({Path.Homotopic.Quotient.mk twicePuncturedClockwiseZeroMeridianInLeft} :
        Set (FundamentalGroup twicePuncturedComplexLeft
          twicePuncturedComplexLeftBasepoint)) = ⊤ := by
  apply top_unique
  intro x _
  rw [Subgroup.mem_closure_singleton]
  have hx : twicePuncturedComplexLeftFundamentalGroupEquiv x ∈
      Subgroup.closure
        ({MulOpposite.op (Multiplicative.ofAdd (complexExpDeckMultiple (-1)))} :
          Set (Multiplicative ComplexExpDeckGroup)ᵐᵒᵖ) := by
    rw [complexExpDeckGroup_generated_by_negOne]
    trivial
  rw [Subgroup.mem_closure_singleton] at hx
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, twicePuncturedComplexLeftFundamentalGroupEquiv.injective ?_⟩
  rw [map_zpow, twicePuncturedComplexLeftFundamentalGroupEquiv_meridian]
  exact hn

/-- The marked one meridian generates the local fundamental group of the right piece. -/
public theorem rightFundamentalGroup_generated_by_meridian :
    Subgroup.closure
      ({Path.Homotopic.Quotient.mk twicePuncturedClockwiseOneMeridianInRight} :
        Set (FundamentalGroup twicePuncturedComplexRight
          twicePuncturedComplexRightBasepoint)) = ⊤ := by
  apply top_unique
  intro x _
  rw [Subgroup.mem_closure_singleton]
  have hx : twicePuncturedComplexRightFundamentalGroupEquiv x ∈
      Subgroup.closure
        ({MulOpposite.op (Multiplicative.ofAdd (complexExpDeckMultiple (-1)))} :
          Set (Multiplicative ComplexExpDeckGroup)ᵐᵒᵖ) := by
    rw [complexExpDeckGroup_generated_by_negOne]
    trivial
  rw [Subgroup.mem_closure_singleton] at hx
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, twicePuncturedComplexRightFundamentalGroupEquiv.injective ?_⟩
  rw [map_zpow, twicePuncturedComplexRightFundamentalGroupEquiv_meridian]
  exact hn

/-- The based class of the actual clockwise zero meridian. -/
public def zeroMeridianClass :
    FundamentalGroup TwicePuncturedComplex twicePuncturedComplexBasepoint :=
  Path.Homotopic.Quotient.mk twicePuncturedClockwiseZeroMeridian

/-- The based class of the actual clockwise one meridian. -/
public def oneMeridianClass :
    FundamentalGroup TwicePuncturedComplex twicePuncturedComplexBasepoint :=
  Path.Homotopic.Quotient.mk twicePuncturedClockwiseOneMeridian

public theorem leftFundamentalGroupMap_meridian :
    leftFundamentalGroupMap
        (Path.Homotopic.Quotient.mk twicePuncturedClockwiseZeroMeridianInLeft) =
      zeroMeridianClass := by
  unfold leftFundamentalGroupMap
  change Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.mk twicePuncturedClockwiseZeroMeridianInLeft)
        leftInclusion = zeroMeridianClass
  rw [← Path.Homotopic.Quotient.mk_map]
  rfl

public theorem rightFundamentalGroupMap_meridian :
    rightFundamentalGroupMap
        (Path.Homotopic.Quotient.mk twicePuncturedClockwiseOneMeridianInRight) =
      oneMeridianClass := by
  unfold rightFundamentalGroupMap
  change Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.mk twicePuncturedClockwiseOneMeridianInRight)
        rightInclusion = oneMeridianClass
  rw [← Path.Homotopic.Quotient.mk_map]
  rfl

/-- Lifts of the two local sections agree throughout their path-connected overlap. -/
private theorem localLifts_agree
    {Q : Type*} [TopologicalSpace Q] (q : C(Q, TwicePuncturedComplex))
    (hq : IsCoveringMap q)
    (sLeft : C(twicePuncturedComplexLeft, Q))
    (sRight : C(twicePuncturedComplexRight, Q))
    (hsLeft : ∀ z, q (sLeft z) = z)
    (hsRight : ∀ z, q (sRight z) = z)
    (hbase : sLeft twicePuncturedComplexLeftBasepoint =
      sRight twicePuncturedComplexRightBasepoint)
    (x : TwicePuncturedComplex)
    (hx : x ∈ twicePuncturedComplexOverlap) :
    sLeft ⟨x, hx.1⟩ = sRight ⟨x, hx.2⟩ := by
  have _ : PathConnectedSpace twicePuncturedComplexOverlap :=
    isPathConnected_iff_pathConnectedSpace.mp twicePuncturedComplexOverlap_isPathConnected
  let g₁ : twicePuncturedComplexOverlap → Q := fun z => sLeft ⟨z, z.2.1⟩
  let g₂ : twicePuncturedComplexOverlap → Q := fun z => sRight ⟨z, z.2.2⟩
  have hcont₁ : Continuous g₁ :=
    sLeft.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hcont₂ : Continuous g₂ :=
    sRight.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hcomp : q ∘ g₁ = q ∘ g₂ := by
    funext z
    simp only [Function.comp_apply, g₁, g₂, hsLeft, hsRight]
  have heq := hq.eq_of_comp_eq hcont₁ hcont₂ hcomp
    ⟨twicePuncturedComplexBasepoint, twicePuncturedComplexBasepoint_mem_overlap⟩ hbase
  exact congrFun heq ⟨x, hx⟩

/-- The two pieces, indexed for `ContinuousMap.liftCover`. -/
private def piece : Fin 2 → Set TwicePuncturedComplex
  | 0 => twicePuncturedComplexLeft
  | 1 => twicePuncturedComplexRight

private theorem piece_isOpen (i : Fin 2) : IsOpen (piece i) := by
  fin_cases i
  · exact twicePuncturedComplexLeft_isOpen
  · exact twicePuncturedComplexRight_isOpen

private theorem piece_covers (x : TwicePuncturedComplex) : ∃ i, piece i ∈ nhds x := by
  have hx : x ∈ twicePuncturedComplexLeft ∪ twicePuncturedComplexRight := by
    rw [twicePuncturedComplexLeft_union_right]
    trivial
  rcases hx with hx | hx
  · exact ⟨0, twicePuncturedComplexLeft_isOpen.mem_nhds hx⟩
  · exact ⟨1, twicePuncturedComplexRight_isOpen.mem_nhds hx⟩

/-- Any subgroup containing both local fundamental-group images is the whole ambient group. -/
public theorem localFundamentalGroupImages_generate
    (H : Subgroup (FundamentalGroup TwicePuncturedComplex
      twicePuncturedComplexBasepoint))
    (hLeft : leftFundamentalGroupMap.range ≤ H)
    (hRight : rightFundamentalGroupMap.range ≤ H) : H = ⊤ := by
  classical
  let _ : LocallyPathConnectedSpace TwicePuncturedComplex := ambient_locallyPathConnected
  let _ : PathConnectedSpace TwicePuncturedComplex := ambient_pathConnected
  let _ : TauCeti.SemilocallySimplyConnectedSpace TwicePuncturedComplex :=
    ambient_semilocallySimplyConnected
  let q : C(SubgroupQuotient twicePuncturedComplexBasepoint H,
      TwicePuncturedComplex) :=
    ⟨subgroupQuotientProj twicePuncturedComplexBasepoint H,
      continuous_subgroupQuotientProj twicePuncturedComplexBasepoint H⟩
  have hq : IsCoveringMap q :=
    isCoveringMap_subgroupQuotientProj twicePuncturedComplexBasepoint H
  let e₀ := SubgroupQuotient.basepoint twicePuncturedComplexBasepoint H
  have he₀ : q e₀ = twicePuncturedComplexBasepoint :=
    subgroupQuotientProj_basepoint twicePuncturedComplexBasepoint H
  have hrange : (FundamentalGroup.mapOfEq q he₀).range = H :=
    range_mapOfEq_subgroupQuotientProj twicePuncturedComplexBasepoint H
  obtain ⟨sLeft, hsLeftBase, hsLeft⟩ :=
    PaperVanKampenFourPieceCover.exists_lift H twicePuncturedComplexLeft_isOpen
      left_isPathConnected twicePuncturedComplexBasepoint_mem_left e₀ he₀ (by
        rw [hrange]
        exact hLeft)
  obtain ⟨sRight, hsRightBase, hsRight⟩ :=
    PaperVanKampenFourPieceCover.exists_lift H twicePuncturedComplexRight_isOpen
      right_isPathConnected twicePuncturedComplexBasepoint_mem_right e₀ he₀ (by
        rw [hrange]
        exact hRight)
  let φ : ∀ i : Fin 2, C(piece i, SubgroupQuotient twicePuncturedComplexBasepoint H) :=
    fun i => match i with
      | 0 => sLeft
      | 1 => sRight
  have hφ : ∀ (i j : Fin 2) (x : TwicePuncturedComplex)
      (hxi : x ∈ piece i) (hxj : x ∈ piece j),
      φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    fin_cases i <;> fin_cases j
    · rfl
    · exact localLifts_agree q hq sLeft sRight hsLeft hsRight
        (hsLeftBase.trans hsRightBase.symm) x ⟨hxi, hxj⟩
    · exact (localLifts_agree q hq sLeft sRight hsLeft hsRight
        (hsLeftBase.trans hsRightBase.symm) x ⟨hxj, hxi⟩).symm
    · rfl
  let sec : C(TwicePuncturedComplex,
      SubgroupQuotient twicePuncturedComplexBasepoint H) :=
    ContinuousMap.liftCover piece φ hφ piece_covers
  have hsec : ∀ x, q (sec x) = x := by
    intro x
    obtain ⟨i, hi⟩ := piece_covers x
    have hx : x ∈ piece i := mem_of_mem_nhds hi
    have hval : sec x = φ i ⟨x, hx⟩ :=
      ContinuousMap.liftCover_coe (S := piece) (φ := φ) (hφ := hφ)
        (hS := piece_covers) (i := i) ⟨x, hx⟩
    rw [hval]
    fin_cases i
    · exact hsLeft ⟨x, hx⟩
    · exact hsRight ⟨x, hx⟩
  have hsecBase : sec twicePuncturedComplexBasepoint = e₀ := by
    have hx : twicePuncturedComplexBasepoint ∈ piece 0 :=
      twicePuncturedComplexBasepoint_mem_left
    have hval : sec twicePuncturedComplexBasepoint =
        φ 0 ⟨twicePuncturedComplexBasepoint, hx⟩ :=
      ContinuousMap.liftCover_coe (S := piece) (φ := φ) (hφ := hφ)
        (hS := piece_covers) (i := 0)
          ⟨twicePuncturedComplexBasepoint, hx⟩
    rw [hval]
    exact hsLeftBase
  have hiff := IsCoveringMap.exists_continuousMap_comp_eq_iff_range_le
    (p := (id : TwicePuncturedComplex → TwicePuncturedComplex))
    (q := subgroupQuotientProj twicePuncturedComplexBasepoint H)
    (e₀ := twicePuncturedComplexBasepoint) (f₀ := e₀)
    continuous_id hq rfl he₀
  have hle :
      (FundamentalGroup.mapOfEq
        (⟨id, continuous_id⟩ : C(TwicePuncturedComplex, TwicePuncturedComplex)) rfl).range ≤
        (FundamentalGroup.mapOfEq q he₀).range :=
    hiff.mp ⟨sec, hsecBase, funext hsec⟩
  rw [TauCeti.FundamentalGroup.mapOfEq_rfl] at hle
  apply top_unique
  intro γ _
  rw [← hrange]
  apply hle
  refine ⟨γ, ?_⟩
  show Path.Homotopic.Quotient.map γ
      (⟨id, continuous_id⟩ : C(TwicePuncturedComplex, TwicePuncturedComplex)) = γ
  induction γ using Quotient.ind with
  | _ p =>
    apply Path.Homotopic.Quotient.eq.mpr
    exact ⟨Path.Homotopy.refl _⟩

/-- The two actual clockwise meridians generate the based fundamental group of
`ℂ \ {0, 1}`. -/
public theorem markedMeridians_generate :
    Subgroup.closure ({zeroMeridianClass, oneMeridianClass} :
      Set (FundamentalGroup TwicePuncturedComplex twicePuncturedComplexBasepoint)) = ⊤ := by
  let K := Subgroup.closure ({zeroMeridianClass, oneMeridianClass} :
    Set (FundamentalGroup TwicePuncturedComplex twicePuncturedComplexBasepoint))
  apply localFundamentalGroupImages_generate K
  · rintro _ ⟨x, rfl⟩
    have hx : x ∈ Subgroup.closure
        ({Path.Homotopic.Quotient.mk twicePuncturedClockwiseZeroMeridianInLeft} :
          Set (FundamentalGroup twicePuncturedComplexLeft
            twicePuncturedComplexLeftBasepoint)) := by
      rw [leftFundamentalGroup_generated_by_meridian]
      trivial
    rw [Subgroup.mem_closure_singleton] at hx
    obtain ⟨n, rfl⟩ := hx
    rw [map_zpow, leftFundamentalGroupMap_meridian]
    apply K.zpow_mem
    apply Subgroup.subset_closure
    simp
  · rintro _ ⟨x, rfl⟩
    have hx : x ∈ Subgroup.closure
        ({Path.Homotopic.Quotient.mk twicePuncturedClockwiseOneMeridianInRight} :
          Set (FundamentalGroup twicePuncturedComplexRight
            twicePuncturedComplexRightBasepoint)) := by
      rw [rightFundamentalGroup_generated_by_meridian]
      trivial
    rw [Subgroup.mem_closure_singleton] at hx
    obtain ⟨n, rfl⟩ := hx
    rw [map_zpow, rightFundamentalGroupMap_meridian]
    apply K.zpow_mem
    apply Subgroup.subset_closure
    simp

end TwicePuncturedComplex

end SphereSixComplex.Topology

end

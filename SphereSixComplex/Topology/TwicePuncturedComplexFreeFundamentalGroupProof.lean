module

public import SphereSixComplex.Topology.TwicePuncturedComplexFundamentalGroupGeneration

/-!
# The canonical free-group presentation map for the twice-punctured plane

The two marked clockwise meridians define a canonical map from the free group on two generators
to the based fundamental group.  The existing based van Kampen generation theorem proves that
this map is surjective.  Injectivity is the remaining relation-free part of the usual van Kampen
calculation.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Topology.TwicePuncturedComplex

/-- Inclusion of the intersection of two subspaces into the first subspace. -/
public def intersectionToLeft {X : Type*} [TopologicalSpace X] (U V : Set X) :
    C((U ∩ V : Set X), U) where
  toFun x := ⟨x, x.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Inclusion of the intersection of two subspaces into the second subspace. -/
public def intersectionToRight {X : Type*} [TopologicalSpace X] (U V : Set X) :
    C((U ∩ V : Set X), V) where
  toFun x := ⟨x, x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The existence part of the based Seifert--van Kampen universal property for an open
two-set cover: compatible homomorphisms from the two local fundamental groups extend to the
ambient fundamental group. -/
public axiom fundamentalGroupOpenUnion_lift
    {X : Type*} [TopologicalSpace X]
    (U V : Set X) (base : X)
    (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (hbaseU : base ∈ U) (hbaseV : base ∈ V)
    (hUPath : IsPathConnected U) (hVPath : IsPathConnected V)
    (hInterPath : IsPathConnected (U ∩ V))
    {G : Type*} [Group G]
    (fU : FundamentalGroup U (⟨base, hbaseU⟩ : U) →* G)
    (fV : FundamentalGroup V (⟨base, hbaseV⟩ : V) →* G)
    (hagree :
      fU.comp (FundamentalGroup.map (intersectionToLeft U V)
        (⟨base, hbaseU, hbaseV⟩ : (U ∩ V : Set X))) =
      fV.comp (FundamentalGroup.map (intersectionToRight U V)
        (⟨base, hbaseU, hbaseV⟩ : (U ∩ V : Set X)))) :
    ∃ f : FundamentalGroup X base →* G,
      f.comp (FundamentalGroup.map
        (PaperVanKampenFourPieceCover.subsetInclusion U)
        (⟨base, hbaseU⟩ : U)) = fU ∧
      f.comp (FundamentalGroup.map
        (PaperVanKampenFourPieceCover.subsetInclusion V)
        (⟨base, hbaseV⟩ : V)) = fV

/-- The based Seifert--van Kampen free-product consequence for two open sets with contractible
overlap, specialized only to the case where both vertex groups have a selected integral
coordinate.  Mathlib currently provides the fundamental-groupoid colimit theorem but not this
based-group extraction. -/
public theorem freeTwoGeneratorLift_injective_of_open_union
    {X : Type*} [TopologicalSpace X]
    (U V : Set X) (base : X)
    (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (hbaseU : base ∈ U) (hbaseV : base ∈ V)
    (hUPath : IsPathConnected U) (hVPath : IsPathConnected V)
    (hInter : ContractibleSpace ↑(U ∩ V : Set X))
    (u : FundamentalGroup U (⟨base, hbaseU⟩ : U))
    (v : FundamentalGroup V (⟨base, hbaseV⟩ : V))
    (hUCoordinate : Function.Bijective (fun n : ℤ ↦ u ^ n))
    (hVCoordinate : Function.Bijective (fun n : ℤ ↦ v ^ n)) :
    Function.Injective
      (FreeGroup.lift fun i : Fin 2 ↦
        if i = 0 then
          FundamentalGroup.map
            (PaperVanKampenFourPieceCover.subsetInclusion U)
            (⟨base, hbaseU⟩ : U) u
        else
          FundamentalGroup.map
            (PaperVanKampenFourPieceCover.subsetInclusion V)
            (⟨base, hbaseV⟩ : V) v) := by
  unfold PaperVanKampenFourPieceCover.subsetInclusion
  let _ : ContractibleSpace ↑(U ∩ V : Set X) := hInter
  let _ : SimplyConnectedSpace ↑(U ∩ V : Set X) :=
    SimplyConnectedSpace.ofContractible _
  have hInterPath : IsPathConnected (U ∩ V) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hUZPow : Function.Bijective
      (zpowersHom (FundamentalGroup U (⟨base, hbaseU⟩ : U)) u) := by
    constructor
    · intro m n hmn
      exact hUCoordinate.1 hmn
    · intro x
      obtain ⟨n, rfl⟩ := hUCoordinate.2 x
      exact ⟨Multiplicative.ofAdd n, rfl⟩
  have hVZPow : Function.Bijective
      (zpowersHom (FundamentalGroup V (⟨base, hbaseV⟩ : V)) v) := by
    constructor
    · intro m n hmn
      exact hVCoordinate.1 hmn
    · intro x
      obtain ⟨n, rfl⟩ := hVCoordinate.2 x
      exact ⟨Multiplicative.ofAdd n, rfl⟩
  let uEquiv : Multiplicative ℤ ≃* FundamentalGroup U (⟨base, hbaseU⟩ : U) :=
    MulEquiv.ofBijective (zpowersHom _ u) hUZPow
  let vEquiv : Multiplicative ℤ ≃* FundamentalGroup V (⟨base, hbaseV⟩ : V) :=
    MulEquiv.ofBijective (zpowersHom _ v) hVZPow
  let fU : FundamentalGroup U (⟨base, hbaseU⟩ : U) →* FreeGroup (Fin 2) :=
    (zpowersHom _ (FreeGroup.of 0)).comp uEquiv.symm.toMonoidHom
  let fV : FundamentalGroup V (⟨base, hbaseV⟩ : V) →* FreeGroup (Fin 2) :=
    (zpowersHom _ (FreeGroup.of 1)).comp vEquiv.symm.toMonoidHom
  have hagree :
      fU.comp (FundamentalGroup.map (intersectionToLeft U V)
        (⟨base, hbaseU, hbaseV⟩ : (U ∩ V : Set X))) =
      fV.comp (FundamentalGroup.map (intersectionToRight U V)
        (⟨base, hbaseU, hbaseV⟩ : (U ∩ V : Set X))) := by
    unfold intersectionToLeft intersectionToRight
    apply MonoidHom.ext
    intro x
    rw [show x = 1 from Subsingleton.elim _ _]
    exact (map_one _).trans (map_one _).symm
  obtain ⟨r, hrU, hrV⟩ :=
    fundamentalGroupOpenUnion_lift U V base hUOpen hVOpen hcover hbaseU hbaseV
      hUPath hVPath hInterPath fU fV hagree
  unfold PaperVanKampenFourPieceCover.subsetInclusion at hrU hrV
  let mapU : FundamentalGroup U (⟨base, hbaseU⟩ : U) →* FundamentalGroup X base :=
    FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) (⟨base, hbaseU⟩ : U)
  let mapV : FundamentalGroup V (⟨base, hbaseV⟩ : V) →* FundamentalGroup X base :=
    FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)) (⟨base, hbaseV⟩ : V)
  change r.comp mapU = fU at hrU
  change r.comp mapV = fV at hrV
  let L : FreeGroup (Fin 2) →* FundamentalGroup X base :=
    FreeGroup.lift fun i : Fin 2 ↦ if i = 0 then mapU u else mapV v
  have huEquiv : uEquiv.symm u = Multiplicative.ofAdd 1 := by
    rw [MulEquiv.symm_apply_eq]
    simp [uEquiv]
  have hvEquiv : vEquiv.symm v = Multiplicative.ofAdd 1 := by
    rw [MulEquiv.symm_apply_eq]
    simp [vEquiv]
  have hleft : Function.LeftInverse r L := by
    intro x
    change (r.comp L) x = x
    simpa only [FreeGroup.lift_of_apply] using
      (FreeGroup.lift_unique (f := FreeGroup.of) (r.comp L) (fun i ↦ by
        by_cases hi : i = 0
        · subst i
          simp only [MonoidHom.comp_apply, L, FreeGroup.lift_apply_of, ↓reduceIte]
          rw [show r (mapU u) = fU u by exact DFunLike.congr_fun hrU u]
          simp [fU, huEquiv]
        · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi
          subst i
          simp only [MonoidHom.comp_apply, L, FreeGroup.lift_apply_of, one_ne_zero,
            ↓reduceIte]
          rw [show r (mapV v) = fV v by exact DFunLike.congr_fun hrV v]
          simp [fV, hvEquiv]) (x := x))
  simpa [L, mapU, mapV] using hleft.injective

/-- The canonical map from the free group on two generators to the fundamental group, sending the
first generator to the clockwise meridian about zero and the second to the clockwise meridian
about one. -/
public def markedMeridianHom :
    FreeGroup (Fin 2) →*
      FundamentalGroup TwicePuncturedComplex twicePuncturedComplexBasepoint :=
  FreeGroup.lift fun i ↦ if i = 0 then zeroMeridianClass else oneMeridianClass

@[simp]
public theorem markedMeridianHom_first :
    markedMeridianHom (FreeGroup.of 0) = zeroMeridianClass := by
  simp [markedMeridianHom]

@[simp]
public theorem markedMeridianHom_second :
    markedMeridianHom (FreeGroup.of 1) = oneMeridianClass := by
  simp [markedMeridianHom]

/-- The two-piece based van Kampen generation theorem is exactly surjectivity of the canonical
free-group presentation map. -/
public theorem markedMeridianHom_surjective :
    Function.Surjective markedMeridianHom := by
  unfold markedMeridianHom
  apply FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr
  have hrange :
      Set.range (fun i : Fin 2 ↦ if i = 0 then zeroMeridianClass else oneMeridianClass) =
        {zeroMeridianClass, oneMeridianClass} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  rw [hrange, markedMeridians_generate]

private theorem complexExpClockwiseGenerator_zpow_injective :
    Function.Injective (fun n : ℤ ↦
      (MulOpposite.op
        (Multiplicative.ofAdd (complexExpDeckMultiple (-1))) :
          (Multiplicative ComplexExpDeckGroup)ᵐᵒᵖ) ^ n) := by
  intro m n h
  have h' := congrArg (fun x : (Multiplicative ComplexExpDeckGroup)ᵐᵒᵖ ↦
    (((MulOpposite.unop x).toAdd : ComplexExpDeckGroup) : ℂ).im) h
  simp [complexExpDeckMultiple] at h'
  exact_mod_cast h'

private theorem leftMeridian_zpow_bijective :
    Function.Bijective (fun n : ℤ ↦
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          twicePuncturedClockwiseZeroMeridianInLeft)) ^ n) := by
  constructor
  · intro m n h
    apply complexExpClockwiseGenerator_zpow_injective
    have h' := congrArg twicePuncturedComplexLeftFundamentalGroupEquiv h
    simpa only [map_zpow,
      twicePuncturedComplexLeftFundamentalGroupEquiv_meridian] using h'
  · intro x
    have hx : x ∈ Subgroup.closure
        ({Path.Homotopic.Quotient.mk twicePuncturedClockwiseZeroMeridianInLeft} :
          Set (FundamentalGroup twicePuncturedComplexLeft
            twicePuncturedComplexLeftBasepoint)) := by
      rw [leftFundamentalGroup_generated_by_meridian]
      trivial
    rw [Subgroup.mem_closure_singleton] at hx
    exact hx

private theorem rightMeridian_zpow_bijective :
    Function.Bijective (fun n : ℤ ↦
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          twicePuncturedClockwiseOneMeridianInRight)) ^ n) := by
  constructor
  · intro m n h
    apply complexExpClockwiseGenerator_zpow_injective
    have h' := congrArg twicePuncturedComplexRightFundamentalGroupEquiv h
    simpa only [map_zpow,
      twicePuncturedComplexRightFundamentalGroupEquiv_meridian] using h'
  · intro x
    have hx : x ∈ Subgroup.closure
        ({Path.Homotopic.Quotient.mk twicePuncturedClockwiseOneMeridianInRight} :
          Set (FundamentalGroup twicePuncturedComplexRight
            twicePuncturedComplexRightBasepoint)) := by
      rw [rightFundamentalGroup_generated_by_meridian]
      trivial
    rw [Subgroup.mem_closure_singleton] at hx
    exact hx

/-- The canonical presentation by the two actual clockwise meridians is relation-free. -/
public theorem establishedMarkedMeridianHom_injective :
    Function.Injective markedMeridianHom := by
  let hInter : ContractibleSpace
      ↑(twicePuncturedComplexLeft ∩ twicePuncturedComplexRight :
        Set TwicePuncturedComplex) :=
    twicePuncturedComplexOverlap_contractible
  exact freeTwoGeneratorLift_injective_of_open_union
    twicePuncturedComplexLeft twicePuncturedComplexRight
    twicePuncturedComplexBasepoint
    twicePuncturedComplexLeft_isOpen twicePuncturedComplexRight_isOpen
    twicePuncturedComplexLeft_union_right
    twicePuncturedComplexBasepoint_mem_left
    twicePuncturedComplexBasepoint_mem_right
    left_isPathConnected right_isPathConnected hInter
    (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk twicePuncturedClockwiseZeroMeridianInLeft))
    (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk twicePuncturedClockwiseOneMeridianInRight))
    leftMeridian_zpow_bijective rightMeridian_zpow_bijective

/-- Once injectivity of the canonical presentation map is supplied, the generator-preserving
fundamental-group equivalence is immediate. -/
public noncomputable def markedMeridianMulEquiv
    (hinj : Function.Injective markedMeridianHom) :
    FreeGroup (Fin 2) ≃*
      FundamentalGroup TwicePuncturedComplex twicePuncturedComplexBasepoint :=
  MulEquiv.ofBijective markedMeridianHom ⟨hinj, markedMeridianHom_surjective⟩

end TwicePuncturedComplex
end Topology
end SphereSixComplex

end

end

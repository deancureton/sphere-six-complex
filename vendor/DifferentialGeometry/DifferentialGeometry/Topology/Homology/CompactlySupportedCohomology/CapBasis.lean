module

public import DifferentialGeometry.Topology.OpenCover.Induction
public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.CapCover
public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.CapDirectedUnion
public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.CapHomeomorph

@[expose] public section

noncomputable section

open Set TopologicalSpace

namespace DifferentialGeometry.Topology

private theorem compact_support_cap_bijective_preimage_subtypeVal
    {X : Type} [TopologicalSpace X] [T2Space X]
    (S T : Set X) (hTS : T ⊆ S) (k m : ℕ)
    (hTcap : ∀ (c : ∀ K : Compacts T, integralRelativeHomology (k + m) (K : Set T)ᶜ),
      (∀ (K L : Compacts T) (h : K ≤ L),
        integralRelativeHomologyMap (k + m) (ContinuousMap.id T)
          (show (L : Set T)ᶜ ⊆ (K : Set T)ᶜ from compl_subset_compl.mpr h) (c L) = c K) →
      (∀ p : T, Function.Bijective (fun z : ℤ => z • c {p})) →
      ∀ D : integralCompactlySupportedCohomology k T →ₗ[ℤ] integralSingularHomology m T,
        (∀ (K : Compacts T) (α : integralRelativeCohomology k (K : Set T)ᶜ),
          D (integralRelativeToCompactlySupportedCohomology k K α) =
            integralRelativeCohomologyCapToAbsolute (K : Set T)ᶜ k m α (c K)) →
        Function.Bijective D)
    (c : ∀ K : Compacts ((Subtype.val : S → X) ⁻¹' T),
      integralRelativeHomology (k + m) (K : Set ((Subtype.val : S → X) ⁻¹' T))ᶜ)
    (hc : ∀ (K L : Compacts ((Subtype.val : S → X) ⁻¹' T)) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id ((Subtype.val : S → X) ⁻¹' T))
        (show (L : Set ((Subtype.val : S → X) ⁻¹' T))ᶜ ⊆
          (K : Set ((Subtype.val : S → X) ⁻¹' T))ᶜ from compl_subset_compl.mpr h) (c L) = c K)
    (hp : ∀ p : ((Subtype.val : S → X) ⁻¹' T), Function.Bijective (fun z : ℤ => z • c {p}))
    (D : integralCompactlySupportedCohomology k ((Subtype.val : S → X) ⁻¹' T) →ₗ[ℤ]
      integralSingularHomology m ((Subtype.val : S → X) ⁻¹' T))
    (hD : ∀ (K : Compacts ((Subtype.val : S → X) ⁻¹' T))
      (α : integralRelativeCohomology k (K : Set ((Subtype.val : S → X) ⁻¹' T))ᶜ),
      D (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set ((Subtype.val : S → X) ⁻¹' T))ᶜ k m α (c K)) :
    Function.Bijective D := by
  let e := _root_.Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (show T ⊆ range (Subtype.val : S → X) from fun x hx => ⟨⟨x, hTS hx⟩, rfl⟩)
  exact integralCompactlySupportedCohomology_cap_bijective_of_homeomorph
    k m e.symm c hc hp hTcap D hD


private theorem compact_support_cap_bijective_of_directed_sUnion
    {X : Type} [TopologicalSpace X] [T2Space X]
    (k m : ℕ) (S : Set (Set X))
    (hdir : DirectedOn (· ⊆ ·) S) (hopen : ∀ U ∈ S, IsOpen U)
    (hlocal : ∀ U ∈ S, ∀
      (c : ∀ K : Compacts U, integralRelativeHomology (k + m) (K : Set U)ᶜ),
      (∀ (K L : Compacts U) (h : K ≤ L),
        integralRelativeHomologyMap (k + m) (ContinuousMap.id U)
          (show (L : Set U)ᶜ ⊆ (K : Set U)ᶜ from compl_subset_compl.mpr h) (c L) = c K) →
      (∀ p : U, Function.Bijective (fun z : ℤ => z • c {p})) →
      ∀ D : integralCompactlySupportedCohomology k U →ₗ[ℤ] integralSingularHomology m U,
        (∀ (K : Compacts U) (α : integralRelativeCohomology k (K : Set U)ᶜ),
          D (integralRelativeToCompactlySupportedCohomology k K α) =
            integralRelativeCohomologyCapToAbsolute (K : Set U)ᶜ k m α (c K)) →
          Function.Bijective D)
    (cS : ∀ K : Compacts (⋃₀ S), integralRelativeHomology (k + m) (K : Set (⋃₀ S))ᶜ)
    (hS : ∀ (K L : Compacts (⋃₀ S)) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id (⋃₀ S))
        (show (L : Set (⋃₀ S))ᶜ ⊆ (K : Set (⋃₀ S))ᶜ from
          compl_subset_compl.mpr h) (cS L) = cS K)
    (hgen : ∀ p : ⋃₀ S, Function.Bijective (fun z : ℤ => z • cS {p}))
    (D : integralCompactlySupportedCohomology k (⋃₀ S) →ₗ[ℤ]
      integralSingularHomology m (⋃₀ S))
    (hD : ∀ (K : Compacts (⋃₀ S)) (α : integralRelativeCohomology k (K : Set (⋃₀ S))ᶜ),
      D (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set (⋃₀ S))ᶜ k m α (cS K)) :
    Function.Bijective D := by
  let U : S → Set (⋃₀ S) := fun i => Subtype.val ⁻¹' (i : Set X)
  have hU (i : S) : IsOpen (U i) := (hopen i i.property).preimage continuous_subtype_val
  have hUdir : Directed (· ⊆ ·) U := by
    intro i j
    obtain ⟨W, hWS, hiW, hjW⟩ := hdir i i.property j j.property
    exact ⟨⟨W, hWS⟩, preimage_mono hiW, preimage_mono hjW⟩
  have hcover : ⋃ i, U i = univ := by
    apply eq_univ_of_forall
    intro p
    obtain ⟨V, hVS, hpV⟩ := p.property
    exact mem_iUnion.mpr ⟨⟨V, hVS⟩, hpV⟩
  apply integralCompactlySupportedCohomology_cap_bijective_of_local_generators_of_directed_open_cover
    k m U hU hUdir hcover cS hS hgen D hD
  intro i ci hi hgi Di hDi
  let e : U i ≃ₜ (i : Set X) :=
    _root_.Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (by simpa only [Subtype.range_val] using subset_sUnion_of_mem i.property)
  exact integralCompactlySupportedCohomology_cap_bijective_of_homeomorph
    k m e.symm ci hi hgi (hlocal i i.property) Di hDi



theorem integralCompactlySupportedCohomology_cap_bijective_of_basis
    {X : Type} [TopologicalSpace X] [T2Space X]
    (n : ℕ) (B : Set (Set X)) (hB : IsTopologicalBasis B)
    (hinter : ∀ U ∈ B, ∀ V ∈ B, U ∩ V ∈ B ∨ U ∩ V = ∅)
    (hseed : ∀ S ∈ B, ∀ i j : ℕ, i + j = n →
      ∀ (c : ∀ K : Compacts S, integralRelativeHomology (i + j) (K : Set S)ᶜ),
      (∀ (K L : Compacts S) (h : K ≤ L),
        integralRelativeHomologyMap (i + j) (ContinuousMap.id S)
          (show (L : Set S)ᶜ ⊆ (K : Set S)ᶜ from compl_subset_compl.mpr h) (c L) = c K) →
      (∀ p : S, Function.Bijective (fun z : ℤ => z • c {p})) →
      ∀ D : integralCompactlySupportedCohomology i S →ₗ[ℤ] integralSingularHomology j S,
        (∀ (K : Compacts S) (α : integralRelativeCohomology i (K : Set S)ᶜ),
          D (integralRelativeToCompactlySupportedCohomology i K α) =
            integralRelativeCohomologyCapToAbsolute (K : Set S)ᶜ i j α (c K)) →
          Function.Bijective D)
    (hvanish : ∀ q : ℕ, n < q → ∀ S : Set X, IsOpen S →
      Subsingleton (integralCompactlySupportedCohomology q S))
    (W : Set X) (hW : IsOpen W) (k m : ℕ) (hkm : k + m = n)
    (cW : ∀ K : Compacts W, integralRelativeHomology (k + m) (K : Set W)ᶜ)
    (hWfamily : ∀ (K L : Compacts W) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id W)
        (show (L : Set W)ᶜ ⊆ (K : Set W)ᶜ from compl_subset_compl.mpr h) (cW L) = cW K)
    (hpoint : ∀ p : W, Function.Bijective (fun z : ℤ => z • cW {p}))
    (DW : integralCompactlySupportedCohomology k W →ₗ[ℤ] integralSingularHomology m W)
    (hDW : ∀ (K : Compacts W) (α : integralRelativeCohomology k (K : Set W)ᶜ),
      DW (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set W)ᶜ k m α (cW K)) :
    Function.Bijective DW := by
  let P : Set X → Prop := fun S => ∀ i j : ℕ, i + j = n →
    ∀ (c : ∀ K : Compacts S, integralRelativeHomology (i + j) (K : Set S)ᶜ),
    (∀ (K L : Compacts S) (h : K ≤ L),
      integralRelativeHomologyMap (i + j) (ContinuousMap.id S)
        (show (L : Set S)ᶜ ⊆ (K : Set S)ᶜ from compl_subset_compl.mpr h) (c L) = c K) →
    (∀ p : S, Function.Bijective (fun z : ℤ => z • c {p})) →
    ∀ D : integralCompactlySupportedCohomology i S →ₗ[ℤ] integralSingularHomology j S,
      (∀ (K : Compacts S) (α : integralRelativeCohomology i (K : Set S)ᶜ),
        D (integralRelativeToCompactlySupportedCohomology i K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set S)ᶜ i j α (c K)) →
        Function.Bijective D
  have hempty : P ∅ := by
    have hP : P (⋃₀ (∅ : Set (Set X))) := by
      intro i j _
      exact compact_support_cap_bijective_of_directed_sUnion (X := X) i j ∅
        (by intro U hU; exact hU.elim)
        (by intro U hU; exact hU.elim)
        (by intro U hU; exact hU.elim)
    simpa only [Set.sUnion_empty] using hP
  have hunion : ∀ U V : Set X, IsOpen U → IsOpen V → P U → P V → P (U ∩ V) →
      P (U ∪ V) := by
    intro U V hU hV hPU hPV hPI i j hij c hc hp D hD
    let A : Set ↥(U ∪ V) := Subtype.val ⁻¹' U
    let C : Set ↥(U ∪ V) := Subtype.val ⁻¹' V
    have hA : IsOpen A := hU.preimage continuous_subtype_val
    have hC : IsOpen C := hV.preimage continuous_subtype_val
    apply integralCompactlySupportedCohomology_cap_bijective_of_two_open_cover
      n A C hA hC (fun p => p.property) ?_ ?_ i j hij c hc hp D hD
    · intro T hT a b hab
      rcases hT with rfl | rfl | rfl
      · exact compact_support_cap_bijective_preimage_subtypeVal (U ∪ V) U
          subset_union_left a b (hPU a b hab)
      · exact compact_support_cap_bijective_preimage_subtypeVal (U ∪ V) V
          subset_union_right a b (hPV a b hab)
      · exact compact_support_cap_bijective_preimage_subtypeVal (U ∪ V) (U ∩ V)
          (inter_subset_left.trans subset_union_left) a b (hPI a b hab)
    · intro q hq
      let e : ↥(A ∩ C) ≃ₜ ↥(U ∩ V) :=
        _root_.Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
          (show U ∩ V ⊆ range (Subtype.val : ↥(U ∪ V) → X) from
            fun x hx => ⟨⟨x, Or.inl hx.1⟩, rfl⟩)
      let _ := hvanish q hq (U ∩ V) (hU.inter hV)
      exact (integralCompactlySupportedCohomologyPushforward_homeomorph_bijective q e).injective.subsingleton
  have hdirected : ∀ S : Set (Set X), S.Nonempty → DirectedOn (· ⊆ ·) S →
      (∀ U ∈ S, IsOpen U ∧ P U) → P (⋃₀ S) := by
    intro S _ hdir hS i j hij
    exact compact_support_cap_bijective_of_directed_sUnion i j S hdir
      (fun U hU => (hS U hU).1) (fun U hU => (hS U hU).2 i j hij)
  exact (hB.isOpen_induction_of_union_of_directed_sUnion hinter hempty hseed hunion
    hdirected hW) k m hkm cW hWfamily hpoint DW hDW

end DifferentialGeometry.Topology

end

module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ChainSupport
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Separation.Hausdorff
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ChainCokernelElements
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyMaps
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeFunctoriality

@[expose] public section


section

open Set

universe u

namespace DifferentialGeometry.Topology

theorem exists_compact_carrier_integral_singular_chain
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A : Set X)
    (c : (integralSingularChains X).X n) (hc : c ∈ integralSingularChainsIn n A) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ A ∧ c ∈ integralSingularChainsIn n K := by
  classical
  let S := (integralSingularChainRepr n X c).support
  refine ⟨⋃ σ ∈ S, range (integralSingularSimplexEquiv n X σ), ?_, ?_, ?_⟩
  · exact S.isCompact_biUnion fun σ _ =>
      isCompact_range (integralSingularSimplexEquiv n X σ).continuous
  · intro x hx
    rcases mem_iUnion₂.mp hx with ⟨σ, hσ, hx⟩
    exact (integralSingularChainsIn_mem_iff n A c).mp hc σ
      (Finsupp.mem_support_iff.mp hσ) hx
  · apply (integralSingularChainsIn_mem_iff n _ c).mpr
    intro σ hσ x hx
    exact mem_iUnion₂.mpr ⟨σ, Finsupp.mem_support_iff.mpr hσ, hx⟩

end DifferentialGeometry.Topology

end


section

open Set

namespace DifferentialGeometry.Topology

private theorem exists_compact_neighborhood_avoiding_integral_chain
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (n : ℕ) (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (c : (integralSingularChains X).X n) (hc : c ∈ integralSingularChainsIn n Kᶜ) :
    ∃ L : Set X, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U ∧
      c ∈ integralSingularChainsIn n Lᶜ := by
  obtain ⟨F, hF, hFK, hcF⟩ := exists_compact_carrier_integral_singular_chain n Kᶜ c hc
  have hKF : K ⊆ Fᶜ := by
    intro x hx hxF
    exact hFK hxF hx
  obtain ⟨L, hL, hKL, hLUF⟩ := exists_compact_between hK
    (hU.inter hF.isClosed.isOpen_compl) (subset_inter hKU hKF)
  refine ⟨L, hL, hKL, hLUF.trans inter_subset_left, ?_⟩
  apply integralSingularChainsIn_mono n (show F ⊆ Lᶜ from ?_) hcF
  intro x hxF hxL
  exact (hLUF hxL).2 hxF

end DifferentialGeometry.Topology

end


section

open CategoryTheory CategoryTheory.Limits Set

universe v

namespace DifferentialGeometry.Topology

theorem exists_relative_homology_class_on_compact_neighborhood
    {X : Type v} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (n : ℕ) (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (a : integralRelativeHomology n Kᶜ) :
    ∃ (L : Set X) (hKL : K ⊆ interior L), IsCompact L ∧ L ⊆ U ∧
      ∃ b : integralRelativeHomology n Lᶜ,
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from
            fun _ hx hxK => hx (interior_subset (hKL hxK))) b = a := by
  obtain ⟨z, hz⟩ := moduleHomologyClass_surjective ((integralRelativeChains Kᶜ).sc n) a
  let πK : integralSingularChains X ⟶ integralRelativeChains Kᶜ :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion Kᶜ))
  obtain ⟨c, hc⟩ := chainCokernelπ_surjective
    (integralSingularChainMap (singularSubspaceInclusion Kᶜ)) n z.val
  let m := (ComplexShape.down ℕ).next n
  have hdcK : πK.f m ((integralSingularChains X).d n m c) = 0 := by
    have h := congrArg (fun f : (integralSingularChains X).X n ⟶
      (integralRelativeChains Kᶜ).X m => f c) (πK.comm n m)
    change (integralRelativeChains Kᶜ).d n m (πK.f n c) =
      πK.f m ((integralSingularChains X).d n m c) at h
    rw [← h]
    change (integralRelativeChains Kᶜ).d n m
      ((cokernel.π (integralSingularChainMap (singularSubspaceInclusion Kᶜ))).f n c) = 0
    rw [hc]
    exact z.property
  have hdc : (integralSingularChains X).d n m c ∈ integralSingularChainsIn m Kᶜ := by
    rw [integralSingularChainsIn_eq_range]
    exact (chainCokernelπ_eq_zero_iff _ m _).mp hdcK
  obtain ⟨L, hL, hKL, hLU, hdcL⟩ := exists_compact_neighborhood_avoiding_integral_chain
    m K U hK hU hKU ((integralSingularChains X).d n m c) hdc
  let πL : integralSingularChains X ⟶ integralRelativeChains Lᶜ :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion Lᶜ))
  have hdcLzero : πL.f m ((integralSingularChains X).d n m c) = 0 := by
    apply (chainCokernelπ_eq_zero_iff _ m _).mpr
    rw [integralSingularChainsIn_eq_range] at hdcL
    obtain ⟨d, hd⟩ := hdcL
    exact ⟨d, hd⟩
  let w : LinearMap.ker ((integralRelativeChains Lᶜ).sc n).g.hom :=
    ⟨πL.f n c, by
      change (integralRelativeChains Lᶜ).d n m (πL.f n c) = 0
      have h := congrArg (fun f : (integralSingularChains X).X n ⟶
        (integralRelativeChains Lᶜ).X m => f c) (πL.comm n m)
      exact h.trans hdcLzero⟩
  let hLK : MapsTo (ContinuousMap.id X) Lᶜ Kᶜ :=
    fun _ hx hxK => hx (interior_subset (hKL hxK))
  let ρ := integralRelativeChainMap (ContinuousMap.id X) hLK
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} ℤ)
    (ComplexShape.down ℕ) n).map ρ
  refine ⟨L, hKL, hL, hLU, moduleHomologyClass ((integralRelativeChains Lᶜ).sc n) w, ?_⟩
  change ShortComplex.homologyMap φ
    (moduleHomologyClass ((integralRelativeChains Lᶜ).sc n) w) = a
  rw [moduleHomologyClass_map]
  have hwz : moduleCycleMap φ w = z := by
    apply Subtype.ext
    change ρ.f n (πL.f n c) = z.val
    have h := integralRelativeChainMap_π (ContinuousMap.id X) hLK
    rw [integralSingularChainMap_id, Category.id_comp] at h
    exact (congrArg (fun f : integralSingularChains X ⟶ integralRelativeChains Kᶜ =>
      f.f n c) h).trans hc
  rw [hwz]
  exact hz

end DifferentialGeometry.Topology

end


section

open CategoryTheory CategoryTheory.Limits Set

universe v

namespace DifferentialGeometry.Topology

theorem exists_compact_neighborhood_relative_restriction_eq_zero
    {X : Type v} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (n : ℕ) (K U : Set X) (x : X) (hxK : x ∈ K) (hU : IsOpen U) (hxU : x ∈ U)
    (a : integralRelativeHomology n Kᶜ)
    (ha : integralRelativeHomologyMap n (ContinuousMap.id X)
      (show MapsTo (ContinuousMap.id X) Kᶜ ({x}ᶜ : Set X) from
        compl_subset_compl.mpr (singleton_subset_iff.mpr hxK)) a = 0) :
    ∃ L : Set X, IsCompact L ∧ x ∈ interior L ∧ L ⊆ U ∧
      integralRelativeHomologyMap n (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) Kᶜ (K ∩ L)ᶜ from
          compl_subset_compl.mpr inter_subset_left) a = 0 := by
  let hKx : MapsTo (ContinuousMap.id X) Kᶜ ({x}ᶜ : Set X) :=
    compl_subset_compl.mpr (singleton_subset_iff.mpr hxK)
  let ρx := integralRelativeChainMap (ContinuousMap.id X) hKx
  let φx := (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} ℤ)
    (ComplexShape.down ℕ) n).map ρx
  obtain ⟨z, hz⟩ := moduleHomologyClass_surjective ((integralRelativeChains Kᶜ).sc n) a
  have hz0 : moduleHomologyClass ((integralRelativeChains ({x}ᶜ : Set X)).sc n)
      (moduleCycleMap φx z) = 0 := by
    rw [← moduleHomologyClass_map]
    change integralRelativeHomologyMap n (ContinuousMap.id X) hKx
      (moduleHomologyClass ((integralRelativeChains Kᶜ).sc n) z) = 0
    rw [hz]
    exact ha
  obtain ⟨d, hd⟩ := (moduleHomologyClass_eq_zero_iff _ _).mp hz0
  let p := (ComplexShape.down ℕ).prev n
  let πK : integralSingularChains X ⟶ integralRelativeChains Kᶜ :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion Kᶜ))
  let πx : integralSingularChains X ⟶ integralRelativeChains ({x}ᶜ : Set X) :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion ({x}ᶜ : Set X)))
  obtain ⟨c, hc⟩ := chainCokernelπ_surjective
    (integralSingularChainMap (singularSubspaceInclusion Kᶜ)) n z.val
  obtain ⟨e, he⟩ := chainCokernelπ_surjective
    (integralSingularChainMap (singularSubspaceInclusion ({x}ᶜ : Set X))) p d
  change πK.f n c = z.val at hc
  change πx.f p e = d at he
  change (integralRelativeChains ({x}ᶜ : Set X)).d p n d = ρx.f n z.val at hd
  have hprojx : ρx.f n (πK.f n c) = πx.f n c := by
    have h := integralRelativeChainMap_π (ContinuousMap.id X) hKx
    rw [integralSingularChainMap_id, Category.id_comp] at h
    exact congrArg (fun f : integralSingularChains X ⟶
      integralRelativeChains ({x}ᶜ : Set X) => f.f n c) h
  have hde : πx.f n ((integralSingularChains X).d p n e) = πx.f n c := by
    calc
      πx.f n ((integralSingularChains X).d p n e) =
          (integralRelativeChains ({x}ᶜ : Set X)).d p n (πx.f p e) :=
        (congrArg (fun f : (integralSingularChains X).X p ⟶
          (integralRelativeChains ({x}ᶜ : Set X)).X n => f e) (πx.comm p n)).symm
      _ = (integralRelativeChains ({x}ᶜ : Set X)).d p n d := by rw [he]
      _ = ρx.f n z.val := hd
      _ = ρx.f n (πK.f n c) := by rw [hc]
      _ = πx.f n c := hprojx
  have hrem : c - (integralSingularChains X).d p n e ∈
      integralSingularChainsIn n ({x}ᶜ : Set X) := by
    have hzero : πx.f n (c - (integralSingularChains X).d p n e) = 0 := by
      change (πx.f n).hom (c - (integralSingularChains X).d p n e) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hde.symm
    rw [integralSingularChainsIn_eq_range]
    exact (chainCokernelπ_eq_zero_iff _ n _).mp hzero
  obtain ⟨L, hL, hxL, hLU, hremL⟩ := exists_compact_neighborhood_avoiding_integral_chain
    n {x} U isCompact_singleton hU (singleton_subset_iff.mpr hxU)
    (c - (integralSingularChains X).d p n e) hrem
  let πL : integralSingularChains X ⟶ integralRelativeChains (K ∩ L)ᶜ :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion (K ∩ L)ᶜ))
  have hremKL : c - (integralSingularChains X).d p n e ∈
      integralSingularChainsIn n (K ∩ L)ᶜ :=
    integralSingularChainsIn_mono n (compl_subset_compl.mpr inter_subset_right) hremL
  have hremzero : πL.f n (c - (integralSingularChains X).d p n e) = 0 := by
    apply (chainCokernelπ_eq_zero_iff _ n _).mpr
    rw [integralSingularChainsIn_eq_range] at hremKL
    obtain ⟨b, hb⟩ := hremKL
    exact ⟨b, hb⟩
  have hremEq : πL.f n c = πL.f n ((integralSingularChains X).d p n e) := by
    change (πL.f n).hom (c - (integralSingularChains X).d p n e) = 0 at hremzero
    rw [map_sub] at hremzero
    exact sub_eq_zero.mp hremzero
  let hKL : MapsTo (ContinuousMap.id X) Kᶜ (K ∩ L)ᶜ :=
    compl_subset_compl.mpr inter_subset_left
  let ρL := integralRelativeChainMap (ContinuousMap.id X) hKL
  let φL := (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} ℤ)
    (ComplexShape.down ℕ) n).map ρL
  refine ⟨L, hL, hxL (mem_singleton x), hLU, ?_⟩
  rw [← hz]
  change ShortComplex.homologyMap φL
    (moduleHomologyClass ((integralRelativeChains Kᶜ).sc n) z) = 0
  rw [moduleHomologyClass_map, moduleHomologyClass_eq_zero_iff]
  refine ⟨πL.f p e, ?_⟩
  change (integralRelativeChains (K ∩ L)ᶜ).d p n (πL.f p e) = ρL.f n z.val
  have hprojL : ρL.f n (πK.f n c) = πL.f n c := by
    have h := integralRelativeChainMap_π (ContinuousMap.id X) hKL
    rw [integralSingularChainMap_id, Category.id_comp] at h
    exact congrArg (fun f : integralSingularChains X ⟶ integralRelativeChains (K ∩ L)ᶜ =>
      f.f n c) h
  calc
    (integralRelativeChains (K ∩ L)ᶜ).d p n (πL.f p e) =
        πL.f n ((integralSingularChains X).d p n e) :=
      congrArg (fun f : (integralSingularChains X).X p ⟶
        (integralRelativeChains (K ∩ L)ᶜ).X n => f e) (πL.comm p n)
    _ = πL.f n c := hremEq.symm
    _ = ρL.f n (πK.f n c) := hprojL.symm
    _ = ρL.f n z.val := by rw [hc]

end DifferentialGeometry.Topology

end

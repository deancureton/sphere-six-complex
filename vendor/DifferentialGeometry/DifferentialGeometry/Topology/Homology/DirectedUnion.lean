module

public import DifferentialGeometry.Topology.Homology.ChainSupportCompact
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeMaps

@[expose] public section

noncomputable section

open Set

namespace DifferentialGeometry.Topology

universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Type v} [Nonempty ι]

theorem exists_integralSingularHomologyMap_eq_of_directed_open_cover
    (n : ℕ) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = univ)
    (α : integralSingularHomology n X) :
    ∃ i, ∃ β : integralSingularHomology n (U i),
      integralSingularHomologyMap n (singularSubspaceInclusion (U i)) β = α := by
  obtain ⟨c, hc⟩ := moduleHomologyClass_surjective ((integralSingularChains X).sc n) α
  obtain ⟨K, hK, hcK⟩ := exists_isCompact_integralSingularChainsIn n c.val
  obtain ⟨i, hKi⟩ := hK.elim_directed_cover U hU (by rw [hcover]; exact subset_univ K) hdir
  have hci : c.val ∈ integralSingularChainsIn n (U i) :=
    (integralSingularChainsIn_mono n hKi) hcK
  rw [integralSingularChainsIn_eq_range] at hci
  obtain ⟨c', hc'⟩ := hci
  have hdc' : (integralSingularChains (U i)).d n ((ComplexShape.down ℕ).next n) c' = 0 := by
    apply integralSingularChainInclusion_injective ((ComplexShape.down ℕ).next n) (U i)
    have h := congrArg (fun f => f c')
      ((integralSingularChainMap (singularSubspaceInclusion (U i))).comm n
        ((ComplexShape.down ℕ).next n))
    change (integralSingularChains X).d n ((ComplexShape.down ℕ).next n)
      ((integralSingularChainMap (singularSubspaceInclusion (U i))).f n c') =
      (integralSingularChainMap (singularSubspaceInclusion (U i))).f
        ((ComplexShape.down ℕ).next n)
        ((integralSingularChains (U i)).d n ((ComplexShape.down ℕ).next n) c') at h
    rw [← h, hc']
    exact c.property.trans (map_zero _).symm
  refine ⟨i, moduleHomologyClass ((integralSingularChains (U i)).sc n) ⟨c', hdc'⟩, ?_⟩
  exact (moduleHomologyClass_map
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ)
        n).map (integralSingularChainMap (singularSubspaceInclusion (U i))))
      ⟨c', hdc'⟩).trans
    ((congrArg (moduleHomologyClass ((integralSingularChains X).sc n))
      (Subtype.ext hc')).trans hc)

omit [Nonempty ι] in
theorem exists_integralSingularHomologyMap_inclusion_eq_zero_of_directed_open_cover
    (n : ℕ) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = univ)
    (i : ι) (α : integralSingularHomology n (U i))
    (hα : integralSingularHomologyMap n (singularSubspaceInclusion (U i)) α = 0) :
    ∃ j, ∃ hij : U i ⊆ U j,
      integralSingularHomologyMap n (ContinuousMap.inclusion hij) α = 0 := by
  let _ : Nonempty ι := ⟨i⟩
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ)
    (ComplexShape.down ℕ) n).map
      (integralSingularChainMap (singularSubspaceInclusion (U i)))
  obtain ⟨c, hc⟩ := moduleHomologyClass_surjective ((integralSingularChains (U i)).sc n) α
  have hc0 : moduleHomologyClass ((integralSingularChains X).sc n)
      (moduleCycleMap φ c) = 0 := by
    rw [← moduleHomologyClass_map]
    change integralSingularHomologyMap n (singularSubspaceInclusion (U i))
      (moduleHomologyClass ((integralSingularChains (U i)).sc n) c) = 0
    rw [hc]
    exact hα
  obtain ⟨b, hb⟩ := (moduleHomologyClass_eq_zero_iff _ _).mp hc0
  let p := (ComplexShape.down ℕ).prev n
  change (integralSingularChains X).d p n b =
    (integralSingularChainMap (singularSubspaceInclusion (U i))).f n c.val at hb
  obtain ⟨K, hK, hbK⟩ := exists_isCompact_integralSingularChainsIn p b
  obtain ⟨k, hKk⟩ := hK.elim_directed_cover U hU
    (by rw [hcover]; exact subset_univ K) hdir
  obtain ⟨j, hij, hkj⟩ := hdir i k
  have hbj : b ∈ integralSingularChainsIn p (U j) :=
    integralSingularChainsIn_mono p (hKk.trans hkj) hbK
  rw [integralSingularChainsIn_eq_range] at hbj
  obtain ⟨b', hb'⟩ := hbj
  let f := ContinuousMap.inclusion hij
  let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ)
    (ComplexShape.down ℕ) n).map (integralSingularChainMap f)
  refine ⟨j, hij, ?_⟩
  rw [← hc]
  change CategoryTheory.ShortComplex.homologyMap ψ
    (moduleHomologyClass ((integralSingularChains (U i)).sc n) c) = 0
  rw [moduleHomologyClass_map, moduleHomologyClass_eq_zero_iff]
  refine ⟨b', ?_⟩
  change (integralSingularChains (U j)).d p n b' =
    (integralSingularChainMap f).f n c.val
  apply integralSingularChainInclusion_injective n (U j)
  have hcomm := congrArg (fun g => g b')
    ((integralSingularChainMap (singularSubspaceInclusion (U j))).comm p n)
  change (integralSingularChains X).d p n
      ((integralSingularChainMap (singularSubspaceInclusion (U j))).f p b') =
    (integralSingularChainMap (singularSubspaceInclusion (U j))).f n
      ((integralSingularChains (U j)).d p n b') at hcomm
  rw [← hcomm, hb', hb]
  have hcomp : (singularSubspaceInclusion (U j)).comp f =
      singularSubspaceInclusion (U i) := rfl
  rw [← hcomp, integralSingularChainMap_comp]
  rfl


end DifferentialGeometry.Topology

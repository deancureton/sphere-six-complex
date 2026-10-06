module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubdivisionHomotopyIdentity

@[expose] public section

/-! # Original affine chains under continuous linear maps -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Continuous linear maps act on the SAME barycentric affine maps. -/
theorem affineSimplexMap_linear {ι : Type*} [Fintype ι] (f : E →L[ℝ] F)
    (v : ι → E) (t : Convexity.StdSimplex ℝ ι) :
    f (affineSimplexMap v t) = affineSimplexMap (f ∘ v) t := by
  change f (∑ i, t.weights i • v i) = ∑ i, t.weights i • f (v i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact f.map_smul _ _

/-- The actual original image simplex has the same image vertex list. -/
theorem affineSingularSimplex_linear (n : ℕ) (f : E →L[ℝ] F) (v : Fin (n + 1) → E) :
    integralSingularSimplexMap n ⟨f, f.continuous⟩ (affineSingularSimplex n v) =
      affineSingularSimplex n (f ∘ v) := by
  apply (integralSingularSimplexEquiv n F).injective
  rw [integralSingularSimplexMap_apply]
  unfold affineSingularSimplex
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro t
  exact affineSimplexMap_linear f v t

/-- The original chain map preserves coefficient-one affine generators. -/
theorem affineSingularChain_linear (n : ℕ) (f : E →L[ℝ] F) (v : Fin (n + 1) → E) :
    (integralSingularChainMap ⟨f, f.continuous⟩).f n (affineSingularChain n v) =
      affineSingularChain n (f ∘ v) := by
  unfold affineSingularChain
  rw [integralSimplexChain_map, affineSingularSimplex_linear]

/-- The image chains retain their actual image carrier. -/
theorem affineSingularChainsIn_linear (n : ℕ) (f : E →L[ℝ] F) (A : Set E)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularChainsIn n A) :
    (integralSingularChainMap ⟨f, f.continuous⟩).f n c ∈ affineSingularChainsIn n (f '' A) := by
  have h : affineSingularChainsIn n A ≤
      Submodule.comap ((integralSingularChainMap ⟨f, f.continuous⟩).f n).hom
        (affineSingularChainsIn n (f '' A)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    change (integralSingularChainMap ⟨f, f.continuous⟩).f n (affineSingularChain n v) ∈
      affineSingularChainsIn n (f '' A)
    rw [affineSingularChain_linear]
    exact affineSingularChain_mem n (f '' A) (f ∘ v) (fun i => ⟨v i, hv i, rfl⟩)
  exact h hc

/-- Coning commutes with the original continuous-linear chain map, without
requiring injectivity or nondegeneracy of the image simplex. -/
theorem affineSingularCone_linear (n : ℕ) (f : E →L[ℝ] F) (a : E) (A : Set E)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularChainsIn n A) :
    (integralSingularChainMap ⟨f, f.continuous⟩).f (n + 1) (affineSingularCone n a c) =
      affineSingularCone n (f a) ((integralSingularChainMap ⟨f, f.continuous⟩).f n c) := by
  let D := ((integralSingularChainMap ⟨f, f.continuous⟩).f (n + 1)).hom.comp (affineSingularCone n a) -
    (affineSingularCone n (f a)).comp ((integralSingularChainMap ⟨f, f.continuous⟩).f n).hom
  have h : affineSingularChainsIn n A ≤ LinearMap.ker D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, _, rfl⟩
    change D (affineSingularChain n v) = 0
    apply sub_eq_zero.mpr
    change (integralSingularChainMap ⟨f, f.continuous⟩).f (n + 1)
      (affineSingularCone n a (affineSingularChain n v)) = _
    rw [affineSingularCone_affine, affineSingularChain_linear]
    change affineSingularChain (n + 1) (f ∘ Fin.cons a v) =
      affineSingularCone n (f a) ((integralSingularChainMap ⟨f, f.continuous⟩).f n (affineSingularChain n v))
    rw [affineSingularChain_linear, affineSingularCone_affine]
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  exact sub_eq_zero.mp (h hc)

/-- The barycenter is transported by the SAME continuous linear map. -/
theorem affineSimplexBarycenter_linear (n : ℕ) (f : E →L[ℝ] F) (v : Fin (n + 1) → E) :
    f (affineSimplexBarycenter n v) = affineSimplexBarycenter n (f ∘ v) :=
  affineSimplexMap_linear f v _

end DifferentialGeometry.Topology

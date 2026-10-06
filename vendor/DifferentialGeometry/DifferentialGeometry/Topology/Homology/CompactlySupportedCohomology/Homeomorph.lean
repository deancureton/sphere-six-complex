module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactlySupportedCohomology.OpenEmbedding

@[expose] public section

noncomputable section

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

theorem integralCompactlySupportedCohomologyPushforward_homeomorph_bijective
    (n : ℕ) (e : X ≃ₜ Y) :
    Function.Bijective (integralCompactlySupportedCohomologyPushforward n
      ⟨e, e.continuous⟩ e.isOpenEmbedding) := by
  let : T2Space X := e.symm.t2Space
  let f : ContinuousMap X Y := ⟨e, e.continuous⟩
  let g : ContinuousMap Y X := ⟨e.symm, e.symm.continuous⟩
  have hgf : g.comp f = ContinuousMap.id X := ContinuousMap.ext e.symm_apply_apply
  have hfg : f.comp g = ContinuousMap.id Y := ContinuousMap.ext e.apply_symm_apply
  have hl : Function.LeftInverse
      (integralCompactlySupportedCohomologyPushforward n g e.symm.isOpenEmbedding)
      (integralCompactlySupportedCohomologyPushforward n f e.isOpenEmbedding) := by
    intro a
    have h := LinearMap.congr_fun (integralCompactlySupportedCohomologyPushforward_comp n
      f g e.isOpenEmbedding e.symm.isOpenEmbedding) a
    simpa only [hgf, integralCompactlySupportedCohomologyPushforward_id,
      LinearMap.comp_apply, LinearMap.id_apply] using h.symm
  have hr : Function.RightInverse
      (integralCompactlySupportedCohomologyPushforward n g e.symm.isOpenEmbedding)
      (integralCompactlySupportedCohomologyPushforward n f e.isOpenEmbedding) := by
    intro a
    have h := LinearMap.congr_fun (integralCompactlySupportedCohomologyPushforward_comp n
      g f e.symm.isOpenEmbedding e.isOpenEmbedding) a
    simpa only [hfg, integralCompactlySupportedCohomologyPushforward_id,
      LinearMap.comp_apply, LinearMap.id_apply] using h.symm
  exact ⟨hl.injective, hr.surjective⟩

end DifferentialGeometry.Topology

module

public import SphereSixComplex.Prerequisites.Topology.Collar.OpenPush
public import SphereSixComplex.Prerequisites.Topology.Homotopy.UnitSquare
public import TauCeti.Topology.Homotopy.Extension.Basic

/-! # Compact collared subsets have the homotopy extension property -/

@[expose] public section

noncomputable section

open Set Topology unitInterval

namespace SphereSixComplex.OpenTopologicalCollar

variable {X : Type*} [TopologicalSpace X] [T2Space X] {B : Set X}

/-- A compact collared subset is a cofibration. The cylinder retraction is supported in the
closed half of the collar, where compactness makes the gluing closed. -/
theorem hasHomotopyExtensionProperty (c : OpenTopologicalCollar X B) (hB : IsCompact B) :
    TauCeti.HasHomotopyExtensionProperty B := by
  classical
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let a : I → TopologicalCollarParameter := fun t ↦
    ⟨(t : ℝ) / 2, div_nonneg t.2.1 (by norm_num), by linarith [t.2.2]⟩
  have ha : Continuous a := (continuous_subtype_val.div_const 2).subtype_mk _
  let e : B × I → X := fun p ↦ (c.chart (p.1, a p.2)).1
  have he : Continuous e := continuous_subtype_val.comp
    (c.chart.continuous.comp (continuous_fst.prodMk (ha.comp continuous_snd)))
  have heinj : Function.Injective e := by
    intro p q hpq
    have h := c.chart.injective (Subtype.ext hpq)
    apply Prod.ext
    · exact congrArg (fun z : B × TopologicalCollarParameter ↦ z.1) h
    · apply Subtype.ext
      have hh := congrArg (fun z : B × TopologicalCollarParameter ↦ z.2.1) h
      change (p.2 : ℝ) / 2 = (q.2 : ℝ) / 2 at hh
      linarith
  let K := range e
  have hK : IsClosed K := (isCompact_range he).isClosed
  let q : K ≃ₜ B × I := (he.isClosedEmbedding heinj).isEmbedding.toHomeomorph.symm
  have heq (x : K) : e (q x) = x.1 :=
    congrArg Subtype.val (q.symm_apply_apply x)
  have hqe (b : B) (t : I) : q ⟨e (b, t), mem_range_self _⟩ = (b, t) :=
    q.apply_symm_apply (b, t)
  let j : B × TopologicalCollarParameter → X := fun p ↦ (c.chart p).1
  have hj : IsOpenEmbedding j :=
    c.neighborhood.2.isOpenEmbedding_subtypeVal.comp c.chart.isOpenEmbedding
  let V : Set (B × TopologicalCollarParameter) := {p | p.2.1 < 1 / 2}
  let U := j '' V
  have hU : IsOpen U := hj.isOpenMap _
    (isOpen_lt continuous_snd.subtype_val continuous_const)
  have hUK : U ⊆ K := by
    rintro x ⟨p, hp, rfl⟩
    let t : I := ⟨2 * p.2.1, by constructor <;> dsimp [V] at hp <;>
      linarith [p.2.2.1]⟩
    refine ⟨(p.1, t), ?_⟩
    have hat : a t = p.2 := Subtype.ext (by dsimp [a, t]; ring)
    simp only [e, hat, j]
  have htop (x : K) (hx : x.1 ∉ U) : (q x).2 = 1 := by
    by_contra ht
    have hlt : ((q x).2 : ℝ) < 1 := lt_of_le_of_ne (q x).2.2.2
      (fun h ↦ ht (Subtype.ext h))
    apply hx
    refine ⟨((q x).1, a (q x).2), ?_, heq x⟩
    change ((q x).2 : ℝ) / 2 < 1 / 2
    linarith
  let F : C(I × K, I × X) :=
    ⟨fun p ↦ ((unitSquareCornerRetraction ((q p.2).2, p.1)).2,
      e ((q p.2).1, (unitSquareCornerRetraction ((q p.2).2, p.1)).1)), by
        have h := unitSquareCornerRetraction.continuous.comp
          ((q.continuous.comp continuous_snd).snd.prodMk continuous_fst)
        exact h.snd.prodMk (he.comp ((q.continuous.comp continuous_snd).fst.prodMk h.fst))⟩
  have Ftop (t : I) (x : K) (hx : x.1 ∉ U) : F (t, x) = (0, x.1) := by
    simp only [F, ContinuousMap.coe_mk, htop x hx, unitSquareCornerRetraction_one_left]
    congr 1
    rw [← htop x hx]
    exact heq x
  let R : I × X → I × X := fun p ↦
    if hx : p.2 ∈ K then F (p.1, ⟨p.2, hx⟩) else (0, p.2)
  have hR : Continuous R := by
    let S : Set (I × X) := Prod.snd ⁻¹' K
    let T : Set (I × X) := Prod.snd ⁻¹' Uᶜ
    have hcover : S ∪ T = univ := by
      ext p
      simp only [mem_union, mem_preimage, mem_compl_iff, mem_univ, iff_true, S, T]
      exact (em (p.2 ∈ U)).elim (fun h ↦ Or.inl (hUK h)) Or.inr
    rw [← continuousOn_univ, ← hcover]
    apply ContinuousOn.union_of_isClosed _ _ (hK.preimage continuous_snd)
      (hU.isClosed_compl.preimage continuous_snd)
    · rw [continuousOn_iff_continuous_domRestrict]
      have hcont : Continuous (fun p : S ↦ F (p.1.1, ⟨p.1.2, p.2⟩)) :=
        F.continuous.comp ((continuous_fst.comp continuous_subtype_val).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
      convert hcont using 1
      funext p
      exact dite_eq_left p.2
    · apply (continuous_const.prodMk continuous_snd).continuousOn.congr
      intro p hp
      dsimp only [R]
      split_ifs with hx
      · exact Ftop p.1 ⟨p.2, hx⟩ hp
      · rfl
  apply TauCeti.hasHomotopyExtensionProperty_of_retraction hB.isClosed
    (r := ⟨R, hR⟩)
  · intro p
    rw [TauCeti.mem_cylinderExtensionDomain_iff]
    change (R p).1 = 0 ∨ (R p).2 ∈ B
    dsimp only [R]
    split_ifs with hx
    · rcases unitSquareCornerRetraction_mem ((q ⟨p.2, hx⟩).2, p.1) with ht | hb
      · exact Or.inl ht
      · right
        change e ((q ⟨p.2, hx⟩).1, _) ∈ B
        rw [hb]
        have ha0 : a 0 = openCollarZero := Subtype.ext (by simp [a, openCollarZero])
        change (c.chart ((q ⟨p.2, hx⟩).1, a 0)).1 ∈ B
        rw [ha0, c.zero]
        exact (q ⟨p.2, hx⟩).1.2
    · exact Or.inl rfl
  · intro p hp
    change R p = p
    rcases TauCeti.mem_cylinderExtensionDomain_iff.mp hp with ht | hb
    · dsimp only [R]
      split_ifs with hx
      · simp only [F, ContinuousMap.coe_mk, ht, unitSquareCornerRetraction_zero_right]
        exact Prod.ext ht.symm (heq ⟨p.2, hx⟩)
      · exact Prod.ext ht.symm rfl
    · let b : B := ⟨p.2, hb⟩
      have he0 : e (b, 0) = p.2 := by simpa [e, a, openCollarZero] using c.zero b
      have hx : p.2 ∈ K := ⟨(b, 0), he0⟩
      have hq : q ⟨p.2, hx⟩ = (b, 0) := by
        simpa only [he0] using hqe b 0
      simp only [R, hx, dite_eq_left, F, ContinuousMap.coe_mk, hq,
        unitSquareCornerRetraction_zero_left, he0]

end SphereSixComplex.OpenTopologicalCollar

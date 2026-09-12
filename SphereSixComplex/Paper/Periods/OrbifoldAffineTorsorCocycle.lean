module

public import SphereSixComplex.Paper.Periods.OrbifoldAffineTorsorTransport
public import SphereSixComplex.Paper.Periods.ExactFuchsianInvariantHolomorphicDescent

/-! Scalar overlap cocycles and holomorphic gluing of local equivariant affine sections. -/

@[expose] public section
noncomputable section
open SphereSixComplex.TriangleGroup
open scoped Manifold
namespace SphereSixComplex.Periods.OrbifoldAffineDescentData

public theorem frameZero_ne_zero_regular (P : OrbifoldAffineDescentData)
    {z : UpperHalfPlane} (hz : P.quotient.coordinate z ∉ ({0, 1} : Set ℂ)) :
    P.frameZero z ≠ 0 := by
  intro he
  rcases (P.frameZero_zero_iff z).mp he with ⟨_, g, rfl⟩ | ⟨_, g, rfl⟩
  · apply hz
    rw [P.quotient.coordinate_invariant, P.quotient.coordinate_at_one]
    simp
  · apply hz
    rw [P.quotient.coordinate_invariant, P.quotient.coordinate_at_two]
    simp

public theorem affineTransport_frameZero_sub (P : OrbifoldAffineDescentData)
    (g : Delta) (z : UpperHalfPlane) (u c : ℂ) :
    (P.affineTransport g (z, u + P.frameZero z * c)).2 =
      (P.affineTransport g (z, u)).2 + P.frameZero (fuchsianSourceAction g • z) * c := by
  induction g using delta_generator_induction generalizing z u with
  | one => simp
  | three =>
      rw [P.affineTransport_g₁]
      change P.affineOne z (u + P.frameZero z * c) =
        P.affineOne z u + P.frameZero (fuchsianSourceAction g₁ • z) * c
      rw [P.frameZero_one]
      have h := P.affineOne_sub z (u + P.frameZero z * c) u
      linear_combination h
  | four =>
      rw [P.affineTransport_g₂]
      change P.affineTwo z (u + P.frameZero z * c) =
        P.affineTwo z u + P.frameZero (fuchsianSourceAction g₂ • z) * c
      rw [P.frameZero_two]
      have h := P.affineTwo_sub z (u + P.frameZero z * c) u
      linear_combination h
  | mul g h hg hh =>
      rw [map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      have hp (v : ℂ) : P.affineTransport h (z, v) =
          (fuchsianSourceAction h • z, (P.affineTransport h (z, v)).2) := by
        apply Prod.ext
        · exact P.affineTransport_fst h _
        · rfl
      rw [hp, hh, hg]
      rw [hp u, map_mul, mul_smul]

public theorem affineTransport_regular_ratio (P : OrbifoldAffineDescentData)
    (g : Delta) {z : UpperHalfPlane} (hz : P.quotient.coordinate z ∉ ({0, 1} : Set ℂ))
    (u v : ℂ) :
    ((P.affineTransport g (z, u)).2 - (P.affineTransport g (z, v)).2) /
        P.frameZero (fuchsianSourceAction g • z) = (u - v) / P.frameZero z := by
  have hn := P.frameZero_ne_zero_regular hz
  have hn' : P.frameZero (fuchsianSourceAction g • z) ≠ 0 :=
    P.frameZero_ne_zero_regular (by simpa only [P.quotient.coordinate_invariant] using hz)
  have he : v + P.frameZero z * ((u - v) / P.frameZero z) = u := by field_simp; ring
  have h := P.affineTransport_frameZero_sub g z v ((u - v) / P.frameZero z)
  rw [he] at h
  rw [h, add_sub_cancel_left, mul_div_cancel_left₀ _ hn']

public theorem exists_regular_overlap_cocycle (P : OrbifoldAffineDescentData)
    {W : Set ℂ} (hW : IsOpen W) (hreg : W ⊆ ({0, 1} : Set ℂ)ᶜ)
    (s t : UpperHalfPlane → ℂ)
    (hs : ∀ z, P.quotient.coordinate z ∈ W → MDiffAt s z)
    (ht : ∀ z, P.quotient.coordinate z ∈ W → MDiffAt t z)
    (hes : ∀ g z, P.quotient.coordinate z ∈ W →
      s (fuchsianSourceAction g • z) = (P.affineTransport g (z, s z)).2)
    (het : ∀ g z, P.quotient.coordinate z ∈ W →
      t (fuchsianSourceAction g • z) = (P.affineTransport g (z, t z)).2) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f W ∧ ∀ z, P.quotient.coordinate z ∈ W →
      s z - t z = f (P.quotient.coordinate z) * P.frameZero z := by
  obtain ⟨f, hf, he⟩ := P.quotient.exists_regular_holomorphic_descent hW hreg
    (fun z ↦ (s z - t z) / P.frameZero z) (fun z hz ↦
      ((hs z hz).sub (ht z hz)).div P.frameZero_holomorphic.mdifferentiableAt
        (P.frameZero_ne_zero_regular (hreg hz))) (by
      intro g z hz
      rw [hes g z hz, het g z hz]
      exact P.affineTransport_regular_ratio g (hreg hz) (s z) (t z))
  refine ⟨f, hf.analyticOnNhd hW, ?_⟩
  intro z hz
  rw [he z hz, div_mul_cancel₀ _ (P.frameZero_ne_zero_regular (hreg hz))]

public theorem exists_local_section_cocycle (P : OrbifoldAffineDescentData)
    {ι : Type*} (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i))
    (hreg : ∀ i j, i ≠ j → U i ∩ U j ⊆ ({0, 1} : Set ℂ)ᶜ)
    (s : ι → UpperHalfPlane → ℂ)
    (hs : ∀ i z, P.quotient.coordinate z ∈ U i → MDiffAt (s i) z)
    (hes : ∀ i g z, P.quotient.coordinate z ∈ U i →
      s i (fuchsianSourceAction g • z) = (P.affineTransport g (z, s i z)).2) :
    ∃ f : ι → ι → ℂ → ℂ,
      (∀ i j, AnalyticOnNhd ℂ (f i j) (U i ∩ U j)) ∧
      (∀ i j k q, q ∈ U i → q ∈ U j → q ∈ U k → f i j q + f j k q = f i k q) ∧
      ∀ i j z, P.quotient.coordinate z ∈ U i → P.quotient.coordinate z ∈ U j →
        s i z - s j z = f i j (P.quotient.coordinate z) * P.frameZero z := by
  classical
  have hoff (i j : ι) (hij : i ≠ j) := P.exists_regular_overlap_cocycle
    ((hU i).inter (hU j)) (hreg i j hij) (s i) (s j)
    (fun z hz ↦ hs i z hz.1) (fun z hz ↦ hs j z hz.2)
    (fun g z hz ↦ hes i g z hz.1) (fun g z hz ↦ hes j g z hz.2)
  let f : ι → ι → ℂ → ℂ := fun i j ↦ if hij : i = j then 0 else (hoff i j hij).choose
  have hdiag (i : ι) : f i i = 0 := by simp [f]
  have htrans (i j : ι) (z : UpperHalfPlane)
      (hi : P.quotient.coordinate z ∈ U i) (hj : P.quotient.coordinate z ∈ U j) :
      s i z - s j z = f i j (P.quotient.coordinate z) * P.frameZero z := by
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · simpa only [f, dite_eq_right hij] using (hoff i j hij).choose_spec.2 z ⟨hi, hj⟩
  refine ⟨f, ?_, ?_, htrans⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      rw [hdiag]
      exact analyticOnNhd_const
    · simpa only [f, dite_eq_right hij] using (hoff i j hij).choose_spec.1
  · intro i j k q hi hj hk
    obtain ⟨z, rfl⟩ := P.quotient.coordinate_isQuotientMap.surjective q
    by_cases hn : P.frameZero z = 0
    · have hij : i = j := by
        by_contra hij
        exact P.frameZero_ne_zero_regular (hreg i j hij ⟨hi, hj⟩) hn
      have hjk : j = k := by
        by_contra hjk
        exact P.frameZero_ne_zero_regular (hreg j k hjk ⟨hj, hk⟩) hn
      subst j
      subst k
      simp [hdiag]
    · apply mul_right_cancel₀ hn
      have h1 := htrans i j z hi hj
      have h2 := htrans j k z hj hk
      have h3 := htrans i k z hi hk
      linear_combination -h1 - h2 + h3

public theorem glue_local_sections (P : OrbifoldAffineDescentData)
    {ι : Type*} (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ q, ∃ i, q ∈ U i) (s : ι → UpperHalfPlane → ℂ)
    (hs : ∀ i z, P.quotient.coordinate z ∈ U i → MDiffAt (s i) z)
    (hes : ∀ i g z, P.quotient.coordinate z ∈ U i →
      s i (fuchsianSourceAction g • z) = (P.affineTransport g (z, s i z)).2)
    (c : ι → ℂ → ℂ) (hc : ∀ i, AnalyticOnNhd ℂ (c i) (U i))
    (htrans : ∀ i j z, P.quotient.coordinate z ∈ U i → P.quotient.coordinate z ∈ U j →
      s i z - s j z = (c i (P.quotient.coordinate z) - c j (P.quotient.coordinate z)) *
        P.frameZero z) :
    ∃ t : UpperHalfPlane → ℂ, MDiff t ∧
      (∀ g z, t (fuchsianSourceAction g • z) = (P.affineTransport g (z, t z)).2) ∧
      ∀ i z, P.quotient.coordinate z ∈ U i →
        t z = s i z - c i (P.quotient.coordinate z) * P.frameZero z := by
  classical
  let idx (z : UpperHalfPlane) := (hcover (P.quotient.coordinate z)).choose
  have hidx (z : UpperHalfPlane) : P.quotient.coordinate z ∈ U (idx z) :=
    (hcover (P.quotient.coordinate z)).choose_spec
  let t := fun z ↦ s (idx z) z - c (idx z) (P.quotient.coordinate z) * P.frameZero z
  have heq (i : ι) (z : UpperHalfPlane) (hz : P.quotient.coordinate z ∈ U i) :
      t z = s i z - c i (P.quotient.coordinate z) * P.frameZero z := by
    have h := htrans (idx z) i z (hidx z) hz
    dsimp only [t]
    linear_combination h
  refine ⟨t, ?_, ?_, heq⟩
  · intro z
    let i := idx z
    have hi : P.quotient.coordinate z ∈ U i := hidx z
    have hci : MDiffAt (c i) (P.quotient.coordinate z) :=
      mdifferentiableAt_iff_differentiableAt.mpr (hc i _ hi).differentiableAt
    have hd : MDiffAt (fun w ↦ s i w - c i (P.quotient.coordinate w) * P.frameZero w) z :=
      (hs i z hi).sub ((hci.comp z P.quotient.coordinate_holomorphic.mdifferentiableAt).mul
        P.frameZero_holomorphic.mdifferentiableAt)
    apply hd.congr_of_eventuallyEq
    have hn := P.quotient.coordinate_holomorphic.continuous.continuousAt ((hU i).mem_nhds hi)
    filter_upwards [hn] with w hw
    exact heq i w hw
  · intro g z
    let i := idx z
    have hi : P.quotient.coordinate z ∈ U i := hidx z
    have hgi : P.quotient.coordinate (fuchsianSourceAction g • z) ∈ U i := by
      rwa [P.quotient.coordinate_invariant]
    rw [heq i _ hgi, heq i z hi, hes i g z hi, P.quotient.coordinate_invariant]
    have h := P.affineTransport_frameZero_sub g z (s i z) (-c i (P.quotient.coordinate z))
    have he : s i z + P.frameZero z * -c i (P.quotient.coordinate z) =
        s i z - c i (P.quotient.coordinate z) * P.frameZero z := by ring
    rw [he] at h
    rw [h]
    ring

end SphereSixComplex.Periods.OrbifoldAffineDescentData

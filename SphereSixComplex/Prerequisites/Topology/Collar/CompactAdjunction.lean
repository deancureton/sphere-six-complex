module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.LocalAtTarget

/-! # Recovering a compact space as an adjunction space -/

@[expose] public section

namespace SphereSixComplex

/-- Attach `K` to `B` by identifying each point of `A` with its image under `g`. -/
def AdjunctionSpace {K B : Type*} (A : Set K) (g : A → B) :=
  Quot (fun x y : K ⊕ B ↦ ∃ a : A, x = Sum.inl a.1 ∧ y = Sum.inr (g a))

namespace AdjunctionSpace

variable {K B : Type*} (A : Set K) (g : A → B)

instance [TopologicalSpace K] [TopologicalSpace B] : TopologicalSpace (AdjunctionSpace A g) :=
  inferInstanceAs (TopologicalSpace (Quot _))

def inl (k : K) : AdjunctionSpace A g := Quot.mk _ (Sum.inl k)
def inr (b : B) : AdjunctionSpace A g := Quot.mk _ (Sum.inr b)

theorem inl_eq_inr (a : A) : inl A g a.1 = inr A g (g a) :=
  Quot.sound ⟨a, rfl, rfl⟩

theorem continuous_inl [TopologicalSpace K] [TopologicalSpace B] :
    Continuous (inl A g) := continuous_quot_mk.comp _root_.continuous_inl

theorem continuous_inr [TopologicalSpace K] [TopologicalSpace B] :
    Continuous (inr A g) := continuous_quot_mk.comp _root_.continuous_inr

variable {X : Type*} [TopologicalSpace K] [TopologicalSpace B] [TopologicalSpace X]

/-- The universal map out of the attachment, for maps agreeing on the attaching subset. -/
def desc (f : C(K, X)) (h : C(B, X)) (heq : ∀ a : A, f a.1 = h (g a)) :
    C(AdjunctionSpace A g, X) where
  toFun := Quot.lift (Sum.elim f h) (by
    rintro x y ⟨a, rfl, rfl⟩
    exact heq a)
  continuous_toFun := continuous_quot_lift _ (f.continuous.sumElim h.continuous)

end AdjunctionSpace
end SphereSixComplex

namespace ContinuousMap

open SphereSixComplex

variable {K X : Type*} [TopologicalSpace K] [TopologicalSpace X]

/-- A compact surjection injective away from a closed target subset presents its target as
an attachment along the inverse image of that subset. -/
noncomputable def adjunctionHomeomorph [CompactSpace K] [T2Space X]
    (f : C(K, X)) (hf : Function.Surjective f) (B : Set X) (hB : IsClosed B)
    (hinj : Set.InjOn f (f ⁻¹' B)ᶜ) :
    AdjunctionSpace (f ⁻¹' B) (fun a ↦ (⟨f a.1, a.2⟩ : B)) ≃ₜ X := by
  let g : (f ⁻¹' B) → B := fun a ↦ ⟨f a.1, a.2⟩
  let d := AdjunctionSpace.desc (f ⁻¹' B) g f ⟨Subtype.val, continuous_subtype_val⟩
    (fun _ ↦ rfl)
  have hd : Function.Bijective d := by
    constructor
    · intro x y
      induction x using Quot.inductionOn with | _ x =>
        induction y using Quot.inductionOn with | _ y =>
          cases x with
          | inl k =>
            cases y with
            | inl l =>
              intro h
              change f k = f l at h
              by_cases hk : f k ∈ B
              · have hl : f l ∈ B := h ▸ hk
                exact (AdjunctionSpace.inl_eq_inr (f ⁻¹' B) g ⟨k, hk⟩).trans
                  ((congrArg (AdjunctionSpace.inr (f ⁻¹' B) g)
                    (Subtype.ext h)).trans
                    (AdjunctionSpace.inl_eq_inr (f ⁻¹' B) g ⟨l, hl⟩).symm)
              · have hl : f l ∉ B := by rwa [← h]
                exact congrArg (AdjunctionSpace.inl (f ⁻¹' B) g) (hinj hk hl h)
            | inr b =>
              intro h
              change f k = b.1 at h
              have hk : f k ∈ B := h.symm ▸ b.2
              exact (AdjunctionSpace.inl_eq_inr (f ⁻¹' B) g ⟨k, hk⟩).trans
                (congrArg (AdjunctionSpace.inr (f ⁻¹' B) g) (Subtype.ext h))
          | inr b =>
            cases y with
            | inl k =>
              intro h
              change b.1 = f k at h
              have hk : f k ∈ B := h ▸ b.2
              exact ((AdjunctionSpace.inl_eq_inr (f ⁻¹' B) g ⟨k, hk⟩).trans
                (congrArg (AdjunctionSpace.inr (f ⁻¹' B) g) (Subtype.ext h.symm))).symm
            | inr c =>
              intro h
              exact congrArg (AdjunctionSpace.inr (f ⁻¹' B) g) (Subtype.ext h)
    · intro x
      obtain ⟨k, rfl⟩ := hf x
      exact ⟨AdjunctionSpace.inl (f ⁻¹' B) g k, rfl⟩
  let _ : CompactSpace X := isCompact_univ_iff.mp (by
    rw [← Set.range_eq_univ.mpr hf]
    exact isCompact_range f.continuous)
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  let _ : CompactSpace (AdjunctionSpace (f ⁻¹' B) g) :=
    inferInstanceAs (CompactSpace (Quot _))
  exact d.continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective d hd)

/-- The compact adjunction theorem with a specified attaching subset and attaching map. -/
noncomputable def adjunctionHomeomorphOfPreimage [CompactSpace K] [T2Space X]
    (f : C(K, X)) (hf : Function.Surjective f) (B : Set X) (hB : IsClosed B)
    (A : Set K) (g : A → B) (hA : f ⁻¹' B = A)
    (hg : ∀ a, (g a).1 = f a.1) (hinj : Set.InjOn f Aᶜ) :
    AdjunctionSpace A g ≃ₜ X := by
  subst A
  have he : g = fun a ↦ (⟨f a.1, a.2⟩ : B) := funext fun a ↦ Subtype.ext (hg a)
  subst g
  exact f.adjunctionHomeomorph hf B hB hinj

@[simp] theorem adjunctionHomeomorphOfPreimage_inl [CompactSpace K] [T2Space X]
    (f : C(K, X)) (hf : Function.Surjective f) (B : Set X) (hB : IsClosed B)
    (A : Set K) (g : A → B) (hA : f ⁻¹' B = A)
    (hg : ∀ a, (g a).1 = f a.1) (hinj : Set.InjOn f Aᶜ) (k : K) :
    f.adjunctionHomeomorphOfPreimage hf B hB A g hA hg hinj
      (AdjunctionSpace.inl A g k) = f k := by
  subst A
  have he : g = fun a ↦ (⟨f a.1, a.2⟩ : B) := funext fun a ↦ Subtype.ext (hg a)
  subst g
  rfl

@[simp] theorem adjunctionHomeomorphOfPreimage_inr [CompactSpace K] [T2Space X]
    (f : C(K, X)) (hf : Function.Surjective f) (B : Set X) (hB : IsClosed B)
    (A : Set K) (g : A → B) (hA : f ⁻¹' B = A)
    (hg : ∀ a, (g a).1 = f a.1) (hinj : Set.InjOn f Aᶜ) (b : B) :
    f.adjunctionHomeomorphOfPreimage hf B hB A g hA hg hinj
      (AdjunctionSpace.inr A g b) = b.1 := by
  subst A
  have he : g = fun a ↦ (⟨f a.1, a.2⟩ : B) := funext fun a ↦ Subtype.ext (hg a)
  subst g
  rfl

/-- Away from the identified subset, a compact surjection is already a homeomorphism. -/
theorem isHomeomorph_restrictPreimage_of_injOn [CompactSpace K] [T2Space X]
    (f : C(K, X)) (hf : Function.Surjective f) (S : Set X)
    (hinj : Set.InjOn f (f ⁻¹' S)) :
    IsHomeomorph (f.restrictPreimage S) := by
  apply isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
  refine ⟨(f.restrictPreimage S).continuous, f.continuous.isClosedMap.restrictPreimage S,
    ?_, ?_⟩
  · intro x y h
    exact Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val h))
  · intro x
    obtain ⟨k, hk⟩ := hf x.1
    exact ⟨⟨k, show f k ∈ S by rw [hk]; exact x.2⟩, Subtype.ext hk⟩

end ContinuousMap

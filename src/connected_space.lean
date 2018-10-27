import analysis.topology.topological_space
import analysis.topology.continuity
import data.set.basic
import analysis.real

open set
open function

universes u v

section connected
variables {α: Type u} {β : Type v} {a : α} {b : β} {s s₁ s₂ : set α} {r r₁ r₂ : set β} {f : α → β}

variables [topological_space α]
variables [t' : topological_space β]

lemma preimage_empty_of_empty {f : α → β} {r : set β} (hf : surjective f): f⁻¹' r = ∅ → r = ∅ :=
suffices (∀a, a ∉ f ⁻¹' r) → ∀b, b ∉ r,
  by simpa only [eq_empty_iff_forall_not_mem],
assume h b,
let ⟨a, eq⟩ := hf b in
eq ▸ h a

lemma preimage_ne_empty_of_ne_empty {f : α → β } (_ : surjective f) {s : set β} (_ : s ≠ ∅ ) : f ⁻¹' s ≠ ∅ :=
let ⟨y, _⟩ := exists_mem_of_ne_empty ‹s ≠ ∅›,
    ⟨x, _⟩ := ‹surjective f›  y in
have f x ∈ s, from (eq.symm ‹f x = y›) ▸ ‹y ∈ s›,
show f⁻¹' s ≠ ∅, from ne_empty_of_mem ‹x ∈ f⁻¹' s›


lemma sep_neg {s₁ s₂ : set α} (h1 : s₁ ∩ s₂ = ∅) (h2 : s₁ ∪ s₂ = univ) : s₁ = -s₂ :=
have h3 : s₁ ⊆ -s₂, from subset_compl_iff_disjoint.mpr h1,
have h4 : -s₂ ⊆ s₁, from compl_subset_iff_union.mpr (eq.trans (union_comm s₂ s₁) h2),
show s₁ = -s₂, from antisymm h3 h4



--Separations of a topological space t
def separation [topological_space α] (s₁ s₂ : set α) : Prop :=
is_open s₁ ∧ is_open s₂ ∧ s₁ ≠ ∅ ∧ s₂ ≠ ∅ ∧ s₁ ∩ s₂ = ∅ ∧ s₁ ∪ s₂ = univ

/-
lemma sep_sym {t : topological_space α} {s₁ s₂ : set α} (h : separation t s₁ s₂) : separation t s₂ s₁ :=
let ⟨ho1, ho2, hne1, hne2, hce, huu⟩ := h in ⟨ho2, ho1, hne2, hne1, eq.trans (inter_comm s₂ s₁) hce, eq.trans (union_comm s₂ s₁) huu⟩

lemma sep_sets_closed {t : topological_space α} {s₁ s₂ : set α} (h : separation t s₁ s₂) : is_closed s₁ ∧ is_closed s₂ :=
let ⟨ho1, ho2, _, _, hce, huu⟩ := h in
have he1 : -s₂ = s₁, from eq.symm (sep_neg hce huu),
have he2 : -s₁ = s₂, from eq.symm (sep_neg (trans (inter_comm s₂ s₁) hce) (trans (union_comm s₂ s₁) huu)),
⟨he1 ▸ is_closed_compl_iff.mpr ho2, he2 ▸ is_closed_compl_iff.mpr ho1⟩
-/

--Connected topological spaces
class connected_space (α) [topological_space α] : Prop :=
(connected : ¬∃ s₁ s₂ : set α, separation s₁ s₂)


theorem im_connected {α β} {f : α → β} [topological_space α] [topological_space β] [connected_space α]
  (_ : continuous f) (_ : surjective f) : connected_space β :=
connected_space.mk $
assume _ : ∃ r₁ r₂ : set β, separation r₁ r₂,
  let ⟨r₁, r₂, _, _, _, _, _, _⟩ := ‹∃ r₁ r₂ : set β, separation r₁ r₂› in
  let s₁ := f⁻¹' r₁, s₂ := f⁻¹' r₂ in
  have is_open s₁, from ‹continuous f› r₁ ‹is_open r₁›,
  have is_open s₂, from ‹continuous f› r₂ ‹is_open r₂›,
  have s₁ ≠ ∅, from preimage_ne_empty_of_ne_empty ‹surjective f› ‹r₁ ≠ ∅›,
  have s₂ ≠ ∅, from preimage_ne_empty_of_ne_empty ‹surjective f› ‹r₂ ≠ ∅›,
  have _, from
  calc s₁ ∩ s₂ = f⁻¹' (r₁ ∩ r₂) : by simp
           ... = ∅              : by rw [‹r₁ ∩ r₂ = ∅›]; exact preimage_empty,
  have _, from
  calc s₁ ∪ s₂ = f⁻¹' (r₁ ∪ r₂) : by simp
           ... =  univ          : by rw [‹r₁ ∪ r₂ = univ›]; exact preimage_univ,
  show false, from connected_space.connected α
    ⟨s₁, s₂, ‹is_open s₁›, ‹is_open s₂›, ‹s₁ ≠ ∅›, ‹s₂ ≠ ∅›, ‹s₁ ∩ s₂ = ∅›, ‹s₁ ∪ s₂ = univ›⟩

def disconnected_subset (s : set α) : Prop :=
∃s₁ s₂ : set α, is_open s₁ ∧ is_open s₂ ∧ s₁ ∩ s ≠ ∅ ∧ s₂ ∩ s ≠ ∅ ∧ s₁ ∩ s₂ ∩ s = ∅ ∧ s ⊆ s₁ ∪ s₂

def connected_subset (s : set α) : Prop :=
¬(disconnected_subset s)

lemma set_is_univ_as_subtype (s : set α) : @univ s = (subtype.val) ⁻¹' s :=
sorry

lemma subtype_val_univ_is_set (s : set α) : (subtype.val) '' (@univ s) = s :=
sorry

lemma range_subtype_val_is_set (s : set α) : range (@subtype.val α s) = s :=
sorry

theorem subtype_connected_iff_subset_connected {s : set α} : connected_space s ↔ connected_subset s :=
suffices (∃ s₁ s₂ : set s, separation s₁ s₂) ↔ disconnected_subset s, from sorry,
let lift := @subtype.val α s in
iff.intro
  (assume h : ∃ s₁ s₂ : set s, separation s₁ s₂,
   let ⟨s₁, s₂, _, _, _, _, _, _⟩ := h in
   have ∃ s₁' : set α, is_open s₁' ∧ s₁ = (lift) ⁻¹' s₁', from ‹is_open s₁›,
   let ⟨s₁', _, _⟩ := this in
   have ∃ s₂' : set α, is_open s₂' ∧ s₂ = (lift) ⁻¹' s₂', from ‹is_open s₂›,
   let ⟨s₂', _, _⟩ := this in
   have s₁' ∩ s ≠ ∅, from
     (assume _ : s₁' ∩ s = ∅,
      have s₁ = ∅, from
        (calc
            s₁ = s₁ ∩ univ : eq.symm (inter_univ s₁)
           ... = ((lift) ⁻¹' s₁') ∩ univ : by rw ‹s₁ = (lift) ⁻¹' s₁'›
           ... = ((lift) ⁻¹' s₁') ∩ ((lift) ⁻¹' s) : by rw set_is_univ_as_subtype
           ... = (lift) ⁻¹' (s₁' ∩ s) : eq.symm preimage_inter
           ... = (lift) ⁻¹' ∅ : by rw ‹s₁' ∩ s = ∅›
           ... = ∅ : preimage_empty
        ),
      show false, from ‹s₁ ≠ ∅› ‹s₁ = ∅›
     ),
   have s₂' ∩ s ≠ ∅, from
     (assume _ : s₂' ∩ s = ∅,
      have s₂ = ∅, from
        (calc
            s₂ = s₂ ∩ univ : eq.symm (inter_univ s₂)
           ... = ((lift) ⁻¹' s₂') ∩ univ : by rw ‹s₂ = (lift) ⁻¹' s₂'›
           ... = ((lift) ⁻¹' s₂') ∩ ((lift) ⁻¹' s) : by rw set_is_univ_as_subtype
           ... = (lift) ⁻¹' (s₂' ∩ s) : eq.symm preimage_inter
           ... = (lift) ⁻¹' ∅ : by rw ‹s₂' ∩ s = ∅›
           ... = ∅ : preimage_empty
        ),
      show false, from ‹s₂ ≠ ∅› ‹s₂ = ∅›
     ),
   have s₁' ∩ s₂' ∩ s = ∅, from
     (calc
        s₁' ∩ s₂' ∩ s = s₁' ∩ s₂' ∩ (range lift) : by rw (range_subtype_val_is_set s)
                   ... = lift '' (lift ⁻¹' (s₁' ∩ s₂')) : by rw image_preimage_eq_inter_range
                   ... = lift '' ((lift ⁻¹' s₁') ∩ (lift ⁻¹' s₂')) : by rw preimage_inter
                   ... = lift '' (s₁ ∩ s₂) : by rw [‹s₁ = lift ⁻¹' s₁'›, ‹s₂ = lift ⁻¹' s₂'›]
                   ... = lift '' ∅ : by {rw [‹s₁ ∩ s₂ = ∅›]; refl}
                   ... = ∅ : image_empty lift
     ),
   have s ⊆ s₁' ∪ s₂', from
     (calc
          s = lift '' (univ) : by rw (subtype_val_univ_is_set s)
        ... = lift '' (s₁ ∪ s₂) : by rw ‹s₁ ∪ s₂ = univ›
        ... = lift '' s₁ ∪ lift '' s₂ : by rw image_union
        ... = (lift '' (lift ⁻¹' s₁')) ∪ (lift '' (lift ⁻¹' s₂')) : by rw [‹s₁ = lift ⁻¹' s₁'›, ‹s₂ = lift ⁻¹' s₂'›]
        ... ⊆ s₁' ∪ s₂' : union_subset_union (image_preimage_subset lift s₁') (image_preimage_subset lift s₂')
     ),
   show ∃s₁ s₂ : set α, is_open s₁ ∧ is_open s₂ ∧ s₁ ∩ s ≠ ∅ ∧ s₂ ∩ s ≠ ∅ ∧ s₁ ∩ s₂ ∩ s = ∅ ∧ s ⊆ s₁ ∪ s₂,
   from ⟨s₁', s₂', ‹is_open s₁'›, ‹is_open s₂'›, ‹s₁' ∩ s ≠ ∅›, ‹s₂' ∩ s ≠ ∅›, ‹s₁' ∩ s₂' ∩ s = ∅›, ‹s ⊆ s₁' ∪ s₂'›⟩
  )
  (sorry
  )

end connected


section real
variables {i: set ℝ} {s₁ s₂: set ℝ}
variables {t : topological_space ℝ}

--TODO: classification of interval

def interval (i : set ℝ) : Prop := ∀ (x y z : ℝ), x ∈ i → z ∈ i → x ≤ y → y ≤ z → y ∈ i


theorem sup_in_closed {i : set ℝ} (_ : is_closed i) (_ : bounded_above i) :  real.Sup i ∈ i := sorry

instance interval_connected {i : set ℝ} (_ : interval i) : connected_space i :=
subtype_connected_iff_subset_connected.mpr $
assume h : ∃s₁ s₂ : set ℝ, is_open s₁ ∧ is_open s₂ ∧ s₁ ≠ ∅ ∧ s₂ ≠ ∅ ∧ s₁ ∩ i ≠ ∅ ∧ s₂ ∩ i ≠ ∅ ∧ s₁ ∩ s₂ = ∅ ∧ i ⊆ s₁ ∪ s₂,
  let ⟨s₁, s₂, _, _, _, _, _, _, _, _⟩ := h in
  let ⟨a, _⟩ := exists_mem_of_ne_empty ‹s₁ ∩ i ≠ ∅›, ⟨b, _⟩ := exists_mem_of_ne_empty ‹s₂ ∩ i ≠ ∅› in
  have a ∈ s₁, from mem_of_mem_inter_left ‹a ∈ s₁ ∩ i›,
  have a ∈ i, from mem_of_mem_inter_right ‹a ∈ s₁ ∩ i›,
  have b ∈ s₂, from mem_of_mem_inter_left ‹b ∈ s₂ ∩ i›,
  have b ∈ i, from mem_of_mem_inter_right ‹b ∈ s₂ ∩ i›,
  have a ≠ b, from
    (assume _ : a = b,
    have b ∈ s₁ ∩ s₂, from mem_inter (‹a = b› ▸ ‹a ∈ s₁›) ‹b ∈ s₂›,
    show false, from eq_empty_iff_forall_not_mem.1 ‹s₁ ∩ s₂ = ∅› b ‹b ∈ s₁ ∩ s₂›
    ),
  have a < b, from sorry, --use suffices? (wlog)
  let Iab := {x | a ≤ x ∧ x ≤ b } in
  have Iab ⊆ i, from
    (suffices (∀x, x ∈ Iab → x ∈ i), by simpa only [subset_def],
    assume x,
    assume _ : x ∈ Iab, 
    have hab : a ≤ x ∧ x ≤ b, from eq.mp mem_set_of_eq ‹x ∈ Iab›,
    show x ∈ i, from ‹interval i› a x b ‹a ∈ i› ‹b ∈ i› hab.1 hab.2),
  let s₁' := s₁ ∩ Iab, s₂' := s₂ ∩ Iab in
  have s₁' ∪ s₂' = Iab, from
  (calc  s₁' ∪ s₂' = (s₁ ∪ s₂) ∩ Iab : eq.symm (inter_distrib_right s₁ s₂ Iab)
               ... = Iab             : inter_eq_self_of_subset_right (subset.trans ‹Iab ⊆ i› ‹i ⊆ s₁ ∪ s₂›)),
  let z := real.Sup s₁' in
  have is_closed s₁', from sorry,
  have bdd_above s₁', from
    ⟨b,
    (assume y,
    assume : y ∈ s₁',
    have s₁' ⊆ Iab, from ‹s₁' ∪ s₂' = Iab› ▸ subset_union_left s₁' s₂',
    have y ∈ Iab, from mem_of_subset_of_mem ‹s₁' ⊆ Iab› ‹y ∈ s₁'›,
    show y ≤ b, from and.right $ mem_def.mp ‹y ∈ Iab›
    )⟩,
  have z ∈ s₁', from sup_in_closed ‹is_closed s₁'› ‹bdd_above s₁'›,
  show false, from sorry

end real

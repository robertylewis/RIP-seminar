import analysis.topology.topological_space
import analysis.topology.continuity
import analysis.topology.topological_structures
import data.set.basic
import analysis.real
import tactic.wlog

open set
open function
open tactic

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

/-- The image of a connected space under a surjective map is connected. -/
theorem im_connected {α β} {f : α → β} [topological_space α] [topological_space β] [connected_space α]
  (_ : continuous f) (_ : surjective f) : connected_space β :=
connected_space.mk $
-- a space is connected if there exists no separation, so we assume there is one and derive false
-- we do this by constructing a 'preimage separation'
assume _ : ∃ r₁ r₂ : set β, separation r₁ r₂,
  -- supose we have a separation r₁ ∪ r₂ = β
  let ⟨r₁, r₂, _, _, _, _, _, _⟩ := ‹∃ r₁ r₂ : set β, separation r₁ r₂› in
  -- we claim that then (s₁=f⁻¹r₁) ∪ (s₂=f⁻¹r₂) is a separation of α
  let s₁ := f⁻¹' r₁, s₂ := f⁻¹' r₂ in
  -- we now need to show that s_i are open, disjoint, nonempty, and span α
  have is_open s₁, from ‹continuous f› r₁ ‹is_open r₁›,
  have is_open s₂, from ‹continuous f› r₂ ‹is_open r₂›,
  have s₁ ≠ ∅, from preimage_ne_empty_of_ne_empty ‹surjective f› ‹r₁ ≠ ∅›,
  have s₂ ≠ ∅, from preimage_ne_empty_of_ne_empty ‹surjective f› ‹r₂ ≠ ∅›,
  have s₁ ∩ s₂ = ∅, by rw ←(@preimage_empty α β f); rw ←‹r₁ ∩ r₂ = ∅›; simp,
  have s₁ ∪ s₂ = univ, by rw ←(@preimage_univ α β f); rw ←‹r₁ ∪ r₂ = univ›; simp,
  -- with this preparation at hand, we construct a separation
  have separation s₁ s₂, from ⟨‹is_open s₁›, ‹is_open s₂›, ‹s₁ ≠ ∅›, ‹s₂ ≠ ∅›, ‹s₁ ∩ s₂ = ∅›, ‹s₁ ∪ s₂ = univ›⟩,
  -- which contradicts the fact that α is connected
  show false, from connected_space.connected α
    ⟨s₁, s₂, ‹separation s₁ s₂›⟩

def disconnected_subset (s : set α) : Prop :=
∃s₁ s₂ : set α, is_open s₁ ∧ is_open s₂ ∧ s₁ ∩ s ≠ ∅ ∧ s₂ ∩ s ≠ ∅ ∧ s₁ ∩ s₂ ∩ s = ∅ ∧ s ⊆ s₁ ∪ s₂

def connected_subset (s : set α) : Prop :=
¬(disconnected_subset s)

lemma range_subtype_val_is_set (s : set α) : range (@subtype.val α s) = s :=
subtype_val_range

lemma subtype_val_univ_is_set (s : set α) : (subtype.val) '' (@univ s) = s :=
calc
  subtype.val '' (@univ s) = range subtype.val : image_univ
                       ... = s                 : subtype_val_range

lemma set_is_univ_as_subtype (s : set α) : @univ s = (subtype.val) ⁻¹' s :=
let lift := @subtype.val α s in
have @univ s ⊆ lift ⁻¹' s, from
  (assume x : s,
   assume _ : x ∈ @univ s,
   have lift x ∈ range lift, from ⟨x, eq.refl (lift x)⟩,
   have lift x ∈ s, from (range_subtype_val_is_set s) ▸ ‹lift x ∈ range lift›,
   show x ∈ lift ⁻¹' s, from ‹lift x ∈ s›
  ),
have lift ⁻¹' s ⊆ @univ s, from subset_univ (lift ⁻¹' s),
show @univ s = (subtype.val) ⁻¹' s, from eq_of_subset_of_subset ‹@univ s ⊆ lift ⁻¹' s› ‹lift ⁻¹' s ⊆ @univ s›

#check connected_space.

theorem subtype_connected_iff_subset_connected {s : set α} : connected_space s ↔ connected_subset s :=
suffices h₀ : (∃ s₁ s₂ : set s, separation s₁ s₂) ↔ disconnected_subset s, from
  (iff.intro
     (assume h : connected_space s,
      assume _ : disconnected_subset s,
      show false, from (@connected_space.connected s subtype.topological_space h) (h₀.mpr ‹disconnected_subset s›)
     )
     (assume h : connected_subset s,
      have ¬∃ s₁ s₂ : set s, separation s₁ s₂, from
        (assume h₁ : ∃ s₁ s₂ : set s, separation s₁ s₂,
         show false, from h (h₀.mp h₁)
        ),
      show connected_space s, from ⟨‹¬∃ s₁ s₂ : set s, separation s₁ s₂›⟩
     )
  ),
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
  (assume h : disconnected_subset s,
   let ⟨s₁, s₂, _, _, _, _, _, _⟩ := h in
   let s₁' := lift ⁻¹' s₁ in
   let s₂' := lift ⁻¹' s₂ in
   have is_open s₁', from ⟨s₁, ‹is_open s₁›, eq.refl s₁'⟩,
   have is_open s₂', from ⟨s₂, ‹is_open s₂›, eq.refl s₂'⟩,
   have s₁' ≠ ∅, from
     (assume _ : s₁' = ∅,
      have s₁ ∩ s = ∅, from
        calc
         s₁ ∩ s = s₁ ∩ (range lift) : by rw range_subtype_val_is_set
            ... = lift '' s₁' : eq.symm (@image_preimage_eq_inter_range s α lift s₁)
            ... = lift '' ∅ : by rw ‹s₁' = ∅›
            ... = ∅ : image_empty lift,
      show false, from ‹s₁ ∩ s ≠ ∅› ‹s₁ ∩ s = ∅›
     ), 
   have s₂' ≠ ∅, from
     (assume _ : s₂' = ∅,
      have s₂ ∩ s = ∅, from
        calc
         s₂ ∩ s = s₂ ∩ (range lift) : by rw range_subtype_val_is_set
            ... = lift '' s₂' : eq.symm (@image_preimage_eq_inter_range s α lift s₂)
            ... = lift '' ∅ : by rw ‹s₂' = ∅›
            ... = ∅ : image_empty lift,
      show false, from ‹s₂ ∩ s ≠ ∅› ‹s₂ ∩ s = ∅›
     ),
   have s₁' ∩ s₂' = ∅, from
     calc
      s₁' ∩ s₂' = s₁' ∩ s₂' ∩ univ : eq.symm (inter_univ (s₁' ∩ s₂'))
            ... = (lift ⁻¹' s₁) ∩ (lift ⁻¹' s₂) ∩ (lift ⁻¹' s) : by rw (eq.symm (set_is_univ_as_subtype s))
            ... = lift ⁻¹' (s₁ ∩ s₂ ∩ s) : by simp only [preimage_inter]
            ... = lift ⁻¹' ∅ : by rw ‹s₁ ∩ s₂ ∩ s = ∅›
            ... = ∅ : preimage_empty,
   have s₁' ∪ s₂' = univ, from
     (have s₁' ∪ s₂' ⊆ univ, from subset_univ (s₁' ∪ s₂'),
      have univ ⊆ s₁' ∪ s₂', from
        calc
         univ = lift ⁻¹' s : by rw set_is_univ_as_subtype
          ... ⊆ lift ⁻¹' (s₁ ∪ s₂) : preimage_mono ‹s ⊆ s₁ ∪ s₂›
          ... = (lift ⁻¹' s₁) ∪ (lift ⁻¹' s₂) : by rw preimage_union
          ... = s₁' ∪ s₂' : rfl,
      show s₁' ∪ s₂' = univ, from eq_of_subset_of_subset ‹s₁' ∪ s₂' ⊆ univ› ‹univ ⊆ s₁' ∪ s₂'›
     ),
   show ∃ s₁ s₂ : set s, separation s₁ s₂,
     from ⟨s₁', s₂', ‹is_open s₁'›, ‹is_open s₂'›, ‹s₁' ≠ ∅›, ‹s₂' ≠ ∅›, ‹s₁' ∩ s₂' = ∅›, ‹s₁' ∪ s₂' = univ›⟩
  )

#check @image_preimage_eq_inter_range

end connected


section real
variables {i: set ℝ} {s₁ s₂: set ℝ}
variables {t : topological_space ℝ}


--TODO: classification of interval

def interval (i : set ℝ) : Prop := ∀ (x y z : ℝ), x ∈ i → z ∈ i → x ≤ y → y ≤ z → y ∈ i

def has_max (S : set ℝ) : Prop := ∃ max ∈ S, ∀ x ∈ S, x ≤ max

/- A closed subset of ℝ that is bounded from above has a maximum. -/
lemma has_max_of_closed_bdd_above {S : set ℝ} (_ : is_closed S) (_ : bdd_above S) (_ : S ≠ ∅) : has_max S :=
-- a set that is bounded from above has a supremum
-- if that supremum is contained in the set, it is the maximum
have ∃ sup, ∀ bound, sup ≤ bound ↔ ∀ x ∈ S, x ≤ bound, from
  real.exists_sup S (set.exists_mem_of_ne_empty ‹S ≠ ∅›) ‹bdd_above S›,
let ⟨sup, bound_iff_ge_sup⟩ := this in
suffices sup ∈ S, from exists.intro sup ⟨‹sup ∈ S›, (bound_iff_ge_sup sup).mp (le_refl sup)⟩,
classical.by_contradiction
  -- we now show that the supremum is contained in the set
  -- for that we use that, since -S is open, sup ∈ -S implies that there is a metric ball around it that's not in S
  -- anything left of the supremum will be smaller than the sup, but still bound S
  -- this contradicts the assumptions
  (assume : sup ∉ S, show false, from
    have ∃ ε > 0, ball sup ε ⊆ -S, from is_open_metric.mp ‹is_open (-S)› sup ‹sup ∈ -S›,
    let ⟨ε, _, _⟩ := this in
      suffices ∀ x ∈ S, x ≤ sup - ε, from
        have ¬(sup ≤ sup - ε), from not_le_of_lt (show sup - ε < sup, by linarith),
        have (sup ≤ sup - ε), from ((bound_iff_ge_sup (sup - ε)).mpr ‹∀ x ∈ S, x ≤ sup - ε›),
        absurd this ‹¬(sup ≤ sup - ε)›,
      assume x (_ : x ∈ S),
      classical.by_contradiction
        (assume : ¬ x ≤ sup - ε, 
          have x ≤ sup, from (bound_iff_ge_sup sup).mp (le_refl sup) x ‹x ∈ S›,
          have 0 ≤ sup - x, by linarith,
          have dist x sup < ε, from 
            calc dist x sup = abs (sup - x) : by rw[dist_comm x sup]; refl
                        ... = sup - x : abs_of_nonneg ‹0 ≤ sup - x›
                        ... < ε : by linarith,
          have x ∈ -S, from mem_of_subset_of_mem ‹ball sup ε ⊆ -S› ‹x ∈ ball sup ε›,
          absurd ‹x ∈ S› ‹x ∈ -S›))

lemma sup_in_closed {S : set ℝ} (_ : is_closed S) (_ : bdd_above S) (_ : S ≠ ∅) : real.Sup S ∈ S :=
have has_max S, from has_max_of_closed_bdd_above ‹is_closed S› ‹bdd_above S› ‹S ≠ ∅›,
let ⟨max, (_ : max ∈ S), max_upper_bound⟩ := this in
have max ≤ real.Sup S, from real.le_Sup S ‹bdd_above S› ‹max ∈ S›,
have real.Sup S ≤ max, from (real.Sup_le S (set.exists_mem_of_ne_empty ‹S ≠ ∅›) ‹bdd_above S›).mpr max_upper_bound,
have max = real.Sup S, from le_antisymm ‹max ≤ real.Sup S› ‹real.Sup S ≤ max›,
show real.Sup S ∈ S, from ‹max = real.Sup S› ▸ ‹max ∈ S› 

lemma mem_iff_neg_mem {S : set ℝ} {x : ℝ} : -x ∈ S ↔ x ∈ {y | -y ∈ S} :=
by rw mem_set_of_eq

lemma bdd_above_iff_neg_bdd_below {S : set ℝ} : bdd_below S ↔ bdd_above {x | -x ∈ S} :=
iff.intro
  (assume ⟨y, h⟩, --S is bounded from below by y
    ⟨-y,
    assume x,
    assume _ : x ∈ {x | -x ∈ S},
    have -x ∈ S, from mem_iff_neg_mem.mpr ‹x ∈ {y | -y ∈ S}›,
    neg_neg x ▸ neg_le_neg (h (-x) ‹-x ∈ S›)⟩)
  (assume ⟨y, h⟩, --{x | -x ∈ S} is bounded from above by y
    ⟨-y,
    assume x,
    assume _ : x ∈ S,
    have -x ∈ {x | -x ∈ S}, by simp [‹x ∈ S›], --how to do this by def?
    neg_neg x ▸ neg_le_neg (h (-x) ‹-x ∈ {x | -x ∈ S}›)⟩)

#check ne_empty_iff_exists_mem.mp

lemma neg_closed {S : set ℝ} (_ : is_closed S) : is_closed {x | -x ∈ S} :=
let neg := λ (x : ℝ), -x in
have continuous neg, from topological_ring.continuous_neg ℝ,
show is_closed (neg ⁻¹' S), from continuous_iff_is_closed.mp ‹continuous neg› S ‹is_closed S›

lemma inf_in_closed {S : set ℝ} (_ : is_closed S) (_ : bdd_below S) (_ : S ≠ ∅) : real.Inf S ∈ S :=
let neg := λ (x : ℝ), -x in
let ⟨x, h⟩ := ne_empty_iff_exists_mem.mp ‹S ≠ ∅› in
have {x | -x ∈ S} ≠ ∅, from ne_empty_iff_exists_mem.mpr ⟨-x, mem_iff_neg_mem.mp (eq.symm (neg_neg x) ▸ h)⟩,
sup_in_closed
  (neg_closed ‹is_closed S›)
  (bdd_above_iff_neg_bdd_below.mp ‹bdd_below S›)
  ‹{x | -x ∈ S} ≠ ∅›


instance interval_connected {i : set ℝ} (_ : interval i) : connected_space i :=
subtype_connected_iff_subset_connected.mpr $
assume h : disconnected_subset i,
  let ⟨s₁, s₂, _, _, _, _, _, _⟩ := h in
  let ⟨a, _⟩ := exists_mem_of_ne_empty ‹s₁ ∩ i ≠ ∅›, ⟨b, _⟩ := exists_mem_of_ne_empty ‹s₂ ∩ i ≠ ∅› in
  have a ∈ s₁, from mem_of_mem_inter_left ‹a ∈ s₁ ∩ i›,
  have a ∈ i, from mem_of_mem_inter_right ‹a ∈ s₁ ∩ i›,
  have b ∈ s₂, from mem_of_mem_inter_left ‹b ∈ s₂ ∩ i›,
  have b ∈ i, from mem_of_mem_inter_right ‹b ∈ s₂ ∩ i›,
  have a ≠ b, from
    (assume _ : a = b,
    have b ∈ s₁ ∩ s₂ ∩ i, from mem_inter (mem_inter (‹a = b› ▸ ‹a ∈ s₁›) ‹b ∈ s₂›) ‹b ∈ i›,
    show false, from eq_empty_iff_forall_not_mem.1 ‹s₁ ∩ s₂ ∩ i = ∅› b ‹b ∈ s₁ ∩ s₂ ∩ i›),
  begin
    --wlog : a < b using [a b, b a],
    --exact ne_iff_lt_or_gt.mp ‹a ≠ b›,
    exact
      have a < b, from sorry, --wlog
      let Iab := {x | a ≤ x ∧ x ≤ b } in
      have Iab ⊆ i, from
        (suffices (∀x, x ∈ Iab → x ∈ i), by simpa only [subset_def],
        assume x,
        assume _ : x ∈ Iab, 
        have hab : a ≤ x ∧ x ≤ b, from mem_set_of_eq.mp ‹x ∈ Iab›,
        show x ∈ i, from ‹interval i› a x b ‹a ∈ i› ‹b ∈ i› hab.1 hab.2),
      let s₁' := s₁ ∩ Iab, s₂' := s₂ ∩ Iab in
      have s₁' ∪ s₂' = Iab, from
        (calc  s₁' ∪ s₂' = (s₁ ∪ s₂) ∩ Iab : eq.symm (inter_distrib_right s₁ s₂ Iab)
                    ... = Iab             : inter_eq_self_of_subset_right (subset.trans ‹Iab ⊆ i› ‹i ⊆ s₁ ∪ s₂›)),
      let sup := real.Sup s₁' in
      have is_closed s₁', from sorry,
      have bdd_above s₁', from
        ⟨b,
        (assume y,
        assume : y ∈ s₁',
        have s₁' ⊆ Iab, from ‹s₁' ∪ s₂' = Iab› ▸ subset_union_left s₁' s₂',
        have y ∈ Iab, from mem_of_subset_of_mem ‹s₁' ⊆ Iab› ‹y ∈ s₁'›,
        show y ≤ b, from and.right $ mem_def.mp ‹y ∈ Iab›
        )⟩,
      have s₁' ≠ ∅, from ne_empty_of_mem (mem_inter ‹a ∈ s₁› (mem_set_of_eq.mpr ⟨le_refl a, le_of_lt ‹a < b›⟩)),
      have sup ∈ s₁', from sup_in_closed ‹is_closed s₁'› ‹bdd_above s₁'› ‹s₁' ≠ ∅›,

      have sup ≤ b, from sorry, --(let ⟨b, h⟩ := bdd in h z ‹z ∈ s₁'›),
      let Isupb := {x | sup ≤ x ∧ x ≤ b } in
      let s₂'' := s₂' ∩ Isupb in
      let inf := real.Inf s₂'' in

      have is_closed s₂'', from sorry,
      have bdd_below s₂'', from sorry,
      have b ∈ s₂', from mem_inter ‹b ∈ s₂› (mem_set_of_eq.mpr ⟨le_of_lt ‹a < b›, le_refl b⟩),
      have s₂'' ≠ ∅, from ne_empty_of_mem (mem_inter ‹b ∈ s₂'› (mem_set_of_eq.mpr ⟨‹sup ≤ b›, le_refl b⟩)),
      have inf ∈ s₂'', from inf_in_closed ‹is_closed s₂''› ‹bdd_below s₂''› ‹s₂'' ≠ ∅›,

      have sup < inf, from sorry,
      let z := (sup + inf) / 2 in
      have sup < z, from sorry,
      have inf > z, from sorry,
      let Isi := {x | sup < x ∧ x < inf} in
      have z ∈ Isi, from mem_set_of_eq.mp (and.intro ‹sup < z› ‹z < inf›),
      have z ∉ s₁ ∪ s₂, from sorry, --union_def.mpr (nmem_set_of_eq.mpr 
      have sup ∈ i, from sorry,
      have inf ∈ i, from sorry,
      have z ∈ i, from ‹interval i› sup z inf ‹sup ∈ i› ‹inf ∈ i› (le_of_lt ‹sup < z›) (le_of_lt ‹z < inf›),
      have z ∈ s₁ ∪ s₂, from mem_of_subset_of_mem ‹i ⊆ s₁ ∪ s₂› ‹z ∈ i›,
      show false, from mem_union.elim ‹z ∈ s₁ ∪ s₂›
        (assume _ : z ∈ s₁,
        have z ∈ s₁', from sorry,
        have z ≤ sup, from real.le_Sup s₁' ‹bdd_above s₁'› ‹z ∈ s₁'›,
        not_lt_of_le ‹z ≤ sup› ‹sup < z›)
        (assume _ : z ∈ s₂,
        have z ∈ s₂', from sorry,
        have z ≥ inf, from sorry, --real.le_Sup s₁' ‹bdd_above s₁'› ‹z ∈ s₁'›,
        not_le_of_gt ‹inf > z› ‹inf ≤ z›)
  end

end real
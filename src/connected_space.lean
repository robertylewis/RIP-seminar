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


--Separations of a topological space
def separation [topological_space α] (s₁ s₂ : set α) : Prop :=
is_open s₁ ∧ is_open s₂ ∧ s₁ ≠ ∅ ∧ s₂ ≠ ∅ ∧ s₁ ∩ s₂ = ∅ ∧ s₁ ∪ s₂ = univ

lemma sep_symm {t : topological_space α} {s₁ s₂ : set α} (h : separation s₁ s₂) : separation s₂ s₁ :=
let ⟨ho1, ho2, hne1, hne2, hce, huu⟩ := h in ⟨ho2, ho1, hne2, hne1, (inter_comm s₁ s₂) ▸ hce, (union_comm s₁ s₂) ▸ huu⟩

lemma sep_sets_closed {t : topological_space α} {s₁ s₂ : set α} (h : separation s₁ s₂) : is_closed s₁ ∧ is_closed s₂ :=
let ⟨ho1, ho2, _, _, hce, huu⟩ := h in
have he1 : -s₂ = s₁, from eq.symm (sep_neg hce huu),
have he2 : -s₁ = s₂, from eq.symm (sep_neg (trans (inter_comm s₂ s₁) hce) (trans (union_comm s₂ s₁) huu)),
⟨he1 ▸ is_closed_compl_iff.mpr ho2, he2 ▸ is_closed_compl_iff.mpr ho1⟩


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


--Separations of a subset of a topological space
def subset_separation [topological_space α] (s s₁ s₂ : set α) : Prop :=
is_open s₁ ∧ is_open s₂ ∧ s₁ ∩ s ≠ ∅ ∧ s₂ ∩ s ≠ ∅ ∧ s₁ ∩ s₂ ∩ s = ∅ ∧ s ⊆ s₁ ∪ s₂

lemma subset_sep_symm {t : topological_space α} {s s₁ s₂ : set α} (h : subset_separation s s₁ s₂) : subset_separation s s₂ s₁ :=
let ⟨ho1, ho2, hne1, hne2, hce, huu⟩ := h in
⟨ho2, ho1, hne2, hne1, (inter_comm s₁ s₂) ▸ hce, (union_comm s₁ s₂) ▸ huu⟩


--Connected subsets of a topological space
def disconnected_subset (s : set α) : Prop :=
∃s₁ s₂ : set α, subset_separation s s₁ s₂

def connected_subset (s : set α) : Prop :=
¬(disconnected_subset s)

lemma subtype_val_univ_eq (s : set α) : (subtype.val) '' (@univ s) = s :=
calc
  subtype.val '' (@univ s) = range subtype.val : image_univ
                       ... = s                 : subtype_val_range

lemma preimage_subtype_val_eq_univ (s : set α) : @univ s = (subtype.val) ⁻¹' s :=
let lift := @subtype.val α s in
have @univ s ⊆ lift ⁻¹' s, from
  (assume x : s,
   assume _ : x ∈ @univ s,
   have lift x ∈ range lift, from ⟨x, eq.refl (lift x)⟩,
   have lift x ∈ s, by rw [←(@set_of_mem _ s), ←subtype_val_range]; assumption,
   show x ∈ lift ⁻¹' s, from ‹lift x ∈ s›
  ),
have lift ⁻¹' s ⊆ @univ s, from subset_univ (lift ⁻¹' s),
show @univ s = (subtype.val) ⁻¹' s, from eq_of_subset_of_subset ‹@univ s ⊆ lift ⁻¹' s› ‹lift ⁻¹' s ⊆ @univ s›

lemma image_preimage_subtype_val {s : set α} (t : set α) :
  subtype.val '' (@subtype.val α s ⁻¹' t) = s ∩ t :=
begin
  rw [image_preimage_eq_inter_range],
  rw [inter_comm],
  rw subtype_val_range,
  exact set_of_mem,
end

lemma preimage_subtype_val_empty_iff {s : set α} (t : set α) :
  @subtype.val α s ⁻¹' t = ∅ ↔ s ∩ t = ∅ :=
begin
  rw ←image_preimage_subtype_val,
  rw image_eq_empty,
end

lemma preimage_subtype_val_ne_empty_iff {s : set α} (t : set α) :
  @subtype.val α s ⁻¹' t ≠ ∅ ↔ s ∩ t ≠ ∅ :=
not_iff_not_of_iff (preimage_subtype_val_empty_iff t)

lemma connected_space_iff : connected_space α ↔ ¬∃ s₁ s₂ : set α, separation s₁ s₂ :=
begin
  constructor,
  apply connected_space.connected,
  apply connected_space.mk
end

theorem subtype_connected_iff_subset_connected {s : set α} : connected_space s ↔ connected_subset s :=
suffices h₀ : (∃ s₁ s₂ : set s, separation s₁ s₂) ↔ disconnected_subset s,
  by rw connected_space_iff; apply not_iff_not_of_iff; assumption,
let lift := @subtype.val α s in
iff.intro
  (assume h : ∃ s₁ s₂ : set s, separation s₁ s₂,
   let ⟨s₁, s₂, _, _, _, _, _, _⟩ := h in
   have ∃ s₁' : set α, is_open s₁' ∧ s₁ = (lift) ⁻¹' s₁', from ‹is_open s₁›,
   let ⟨s₁', _, _⟩ := this in
   have ∃ s₂' : set α, is_open s₂' ∧ s₂ = (lift) ⁻¹' s₂', from ‹is_open s₂›,
   let ⟨s₂', _, _⟩ := this in
   have s₁' ∩ s ≠ ∅,
     by rw [←inter_comm, ←preimage_subtype_val_ne_empty_iff, ←‹s₁ = lift ⁻¹' s₁'›]; assumption,
   have s₂' ∩ s ≠ ∅,
     by rw [←inter_comm, ←preimage_subtype_val_ne_empty_iff, ←‹s₂ = lift ⁻¹' s₂'›]; assumption,
   have s₁' ∩ s₂' ∩ s = ∅,
     by rw [←inter_comm, ←preimage_subtype_val_empty_iff, preimage_inter, ←‹s₁ = lift ⁻¹' s₁'›, ←‹s₂ = lift ⁻¹' s₂'›]; assumption,
   have s ⊆ s₁' ∪ s₂', from
     (calc
          s = lift '' (univ) : by rw (subtype_val_univ_eq s)
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
   have s₁' ≠ ∅, 
     by rw [preimage_subtype_val_ne_empty_iff, inter_comm]; assumption,
   have s₂' ≠ ∅, 
     by rw [preimage_subtype_val_ne_empty_iff, inter_comm]; assumption,
   have s₁' ∩ s₂' = ∅, 
     by rw [←preimage_inter, preimage_subtype_val_empty_iff, inter_comm]; assumption,
   have s₁' ∪ s₂' = univ, from
     (have s₁' ∪ s₂' ⊆ univ, from subset_univ (s₁' ∪ s₂'),
      have univ ⊆ s₁' ∪ s₂', from
        calc
         univ = lift ⁻¹' s : by rw preimage_subtype_val_eq_univ
          ... ⊆ lift ⁻¹' (s₁ ∪ s₂) : preimage_mono ‹s ⊆ s₁ ∪ s₂›
          ... = (lift ⁻¹' s₁) ∪ (lift ⁻¹' s₂) : by rw preimage_union
          ... = s₁' ∪ s₂' : rfl,
      show s₁' ∪ s₂' = univ, from eq_of_subset_of_subset ‹s₁' ∪ s₂' ⊆ univ› ‹univ ⊆ s₁' ∪ s₂'›
     ),
   show ∃ s₁ s₂ : set s, separation s₁ s₂,
     from ⟨s₁', s₂', ‹is_open s₁'›, ‹is_open s₂'›, ‹s₁' ≠ ∅›, ‹s₂' ≠ ∅›, ‹s₁' ∩ s₂' = ∅›, ‹s₁' ∪ s₂' = univ›⟩
  )

end connected


section intervals
open lattice

variables {α : Type*} [partial_order α] {i : set α}

/-- an interval is a convex set -/
def interval (i : set α) : Prop := ∀x y z, x ∈ i → z ∈ i → x ≤ y → y ≤ z → y ∈ i

/-- Left-open right-closed interval -/
def Ioc (a b : α) := {x | a < x ∧ x ≤ b}

/-- Left-infinite right-open interval -/
def Iic (a : α) := {x | x ≤ a}

/-- Left-open right-infinite interval -/
def Ioi (b : α) := {x | x < b}

--Classification of bounded above intervals

lemma exists_smaller_of_not_bounded_below {i : set α} (_ : ¬bdd_below i) (x : α) : ∃y∈i, y ≤ x := sorry

lemma exists_real_between {x y : ℝ} (_ : x < y) : ∃z, x < z ∧ z < y :=
suffices Ioo x y ≠ ∅, from exists_mem_of_ne_empty this,
mt Ioo_eq_empty_iff.mp (not_le_of_lt ‹x < y›)

theorem bdd_above_interval_iff {i : set ℝ} (_ : bdd_above i) : interval i ↔
∃b, i = Iic b ∨ i = Iio b ∨ ∃a, i = Icc a b ∨ i = Ioc a b ∨ i = Ico a b ∨ i = Ioo a b :=
iff.intro
  (assume _ : interval i,
  have i ≠ ∅, from sorry, --if this is the case, then we can construct it as a bounded interval
  have ∃ sup, ∀ bound, sup ≤ bound ↔ ∀ x ∈ i, x ≤ bound, from
    real.exists_sup i (set.exists_mem_of_ne_empty ‹i ≠ ∅›) ‹bdd_above i›,
  let ⟨sup, bound_iff_ge_sup⟩ := this in
  have le_sup : ∀ x ∈ i, x ≤ sup, from (bound_iff_ge_sup sup).mp $ le_refl sup,
  ⟨sup, classical.by_cases
    (assume _ : bdd_below i, /-left-bounded cases-/
    let ⟨a, ha⟩ := ‹bdd_below i› in
    classical.by_cases
      (assume _ : sup ∈ i,
      classical.by_cases
        (assume _ : a ∈ i, --left-closed right-closed case
        have i = Icc a sup, from sorry,
        sorry)
        (assume _ : a ∉ i, --left-open right-closed case
        have i = Ioc a sup, from sorry,
        sorry))
      (assume _ : sup ∉ i,
      classical.by_cases
        (assume _ : a ∈ i, --left-closed right-open case
        have i = Ico a sup, from sorry,
        sorry)
        (assume _ : a ∉ i, --left-open right-open case
        have i = Ioo a sup, from sorry,
        sorry)))
    (assume _ : ¬bdd_below i, /-left-infinite cases-/
    classical.by_cases
      --left-infinite right-closed case
      (assume _ : sup ∈ i,
      have i = Iic sup, from ext $
        assume x,
        let ⟨y, _, _⟩ := exists_smaller_of_not_bounded_below ‹¬bdd_below i› x in
        iff.intro
          (assume _ : x ∈ i, le_sup x ‹x ∈ i›)
          (assume _ : x ∈ Iic sup, ‹interval i› y x sup ‹y ∈ i› ‹sup ∈ i› ‹y ≤ x› ‹x ∈ Iic sup›),
      by simp [this]) --add the large disjunction
      --left-infinite right-open cases
      (assume _ : sup ∉ i,
      have i = Iio sup, from ext $
        assume x,
        let ⟨y, _, _⟩ := exists_smaller_of_not_bounded_below ‹¬bdd_below i› x in
        iff.intro
          (assume _ : x ∈ i,
          have x ≠ sup, from assume _ : x = sup, ‹sup ∉ i› $ ‹x = sup› ▸ ‹x ∈ i›,
          lt_of_le_of_ne (le_sup x ‹x ∈ i›) ‹x ≠ sup›)
          (assume _ : x ∈ Iio sup,
          have i ∩ Ioo x sup ≠ ∅, from
            assume _ : i ∩ Ioo x sup = ∅, --show that a smaller supremum exists
            let ⟨sup2, _⟩ := exists_real_between ‹x < sup› in
            have ∀ z ∈ i, z ≤ sup2, from
              assume z,
              assume _ : z ∈ i,
              le_of_not_lt $
                assume _ : z > sup2,
                have z ≠ sup, from assume _ : z = sup, ‹sup ∉ i› $ ‹z = sup› ▸ ‹z ∈ i›,
                have z < sup, from lt_of_le_of_ne (le_sup z ‹z ∈ i›) ‹z ≠ sup›,
                have z ∈ Ioo x sup, from ⟨lt_trans ‹x < sup2 ∧ sup2 < sup›.left ‹sup2 < z›, ‹z < sup›⟩,
                have z ∈ i ∩ Ioo x sup, from mem_inter ‹z ∈ i› ‹z ∈ Ioo x sup›,
                show false, from eq_empty_iff_forall_not_mem.mp ‹i ∩ Ioo x sup = ∅› z ‹z ∈ i ∩ Ioo x sup›,
            have sup ≤ sup2, from (bound_iff_ge_sup sup2).mpr this,
            show false, from (not_le_of_lt ‹x < sup2 ∧ sup2 < sup›.right) ‹sup ≤ sup2›,
          let ⟨z, _⟩ := exists_mem_of_ne_empty ‹i ∩ Ioo x sup ≠ ∅› in
          have z ∈ i, from mem_of_mem_inter_left ‹z ∈ i ∩ Ioo x sup›,
          have x ≤ z, from le_of_lt (mem_of_mem_inter_right ‹z ∈ i ∩ Ioo x sup›).left,
          ‹interval i› y x z ‹y ∈ i› ‹z ∈ i› ‹y ≤ x› ‹x ≤ z›),
      by simp [this])) --add the large disjunction
  ⟩)
  (sorry)


end intervals


section real
variables {i: set ℝ} {s₁ s₂: set ℝ}
variables {t : topological_space ℝ}

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

lemma bdd_above_Icc {a b : ℝ} : bdd_above (Icc a b) :=
⟨b, by intros; exact (mem_def.mp ‹y ∈ Icc a b›).right⟩

lemma bdd_below_Icc {a b : ℝ} : bdd_below (Icc a b) :=
⟨a, by intros; exact (mem_def.mp ‹y ∈ Icc a b›).left⟩

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

lemma inter_sep_comp_eq {α : Type u} {s s₁ s₂ : set α} (_ : s ∩ s₁ ∩ s₂ = ∅) (_ : s ⊆ s₁ ∪ s₂) : s ∩ s₁ = s ∩ -s₂ :=
have s ∩ s₁ ⊆ s ∩-s₂, by simpa [subset_compl_iff_disjoint],
have s ∩-s₂ ⊆ s ∩ s₁, from
calc s ∩-s₂ ⊆ s ∩ ((s₁ ∪ s₂) ∩ -s₂) : by simp [inter_subset_inter_left, ‹s ⊆ s₁ ∪ s₂›]
        ... ⊆ s ∩ s₁                : by simp [inter_subset_inter_right, inter_distrib_right],
eq_of_subset_of_subset ‹s ∩ s₁ ⊆ s ∩ -s₂› ‹s ∩-s₂ ⊆ s ∩ s₁›

lemma subset_separation_left_inter_closed {α : Type u} {s s₁ s₂ c : set α} [topological_space α]
  (sep : subset_separation s s₁ s₂) (_ : is_closed c) (_ : c ⊆ s) : is_closed (s₁ ∩ c) :=
let ⟨_, _, _, _, _, _⟩ := sep in
let s₁' := s₁ ∩ c in
have c ∩ s₁ ∩ s₂ = ∅, from subset_empty_iff.mp $
calc c ∩ s₁ ∩ s₂ ⊆ s ∩ s₁ ∩ s₂   : by simp [inter_subset_inter_left, inter_assoc, ‹c ⊆ s›]
             ... = s ∩ (s₁ ∩ s₂) : by rw [inter_assoc]
             ... = s₁ ∩ s₂ ∩ s   : by rw [inter_comm] --should be doable in one step
             ... = ∅             : ‹s₁ ∩ s₂ ∩ s = ∅›,
have c ⊆ s₁ ∪ s₂, from subset.trans ‹c ⊆ s› ‹s ⊆ s₁ ∪ s₂›,
have (-s₂) ∩ c = s₁ ∩ c, from
calc (-s₂) ∩ c = c ∩ (-s₂) : by rw [inter_comm]
           ... = c ∩ s₁    : eq.symm $ inter_sep_comp_eq ‹c ∩ s₁ ∩ s₂ = ∅› ‹c ⊆ s₁ ∪ s₂›
           ... = s₁ ∩ c    : by rw [inter_comm],
have s₁' ⊆ -s₂, from
  have s₁' ∩ s₂ = ∅, from subset_empty_iff.mp $
    calc s₁' ∩ s₂ = s₁ ∩ s₂ ∩ c : by simp [inter_comm, inter_assoc]
              ... ⊆ s₁ ∩ s₂ ∩ s : inter_subset_inter_right (s₁ ∩ s₂) ‹c ⊆ s›
              ... = ∅           : ‹s₁ ∩ s₂ ∩ s = ∅›,
  subset_compl_iff_disjoint.mpr ‹s₁ ∩ c ∩ s₂ = ∅›,
have s₁ ∩ ((-s₂ ∩ c)) = s₁', from
  (calc s₁ ∩ ((-s₂) ∩ c) = (-s₂) ∩ (s₁ ∩ c) : by simp [inter_left_comm]
                     ... = (-s₂) ∩ s₁'      : by simp
                     ... = s₁'              : inter_eq_self_of_subset_right ‹s₁' ⊆ -s₂›),
have is_open (-(-s₂)), from (eq.symm (compl_compl s₂)) ▸ ‹is_open s₂›,
have is_closed (-s₂), from ‹is_open (-(-s₂))›,
have is_closed (-s₂ ∩ c), from is_closed_inter ‹is_closed (-s₂)› ‹is_closed c›,
@eq.subst (set α) is_closed (-s₂ ∩ c) (s₁ ∩ c) ‹-s₂ ∩ c = s₁ ∩ c› ‹is_closed (-s₂ ∩ c)›

lemma subset_separation_right_inter_closed {α : Type u} {s s₁ s₂ c : set α} [topological_space α]
  (sep : subset_separation s s₁ s₂) (_ : is_closed c) (_ : c ⊆ s) : is_closed (s₂ ∩ c) :=
subset_separation_left_inter_closed (subset_sep_symm sep) ‹is_closed c› ‹c ⊆ s›


set_option eqn_compiler.zeta true

instance interval_connected {i : set ℝ} (_ : interval i) : connected_space i :=
subtype_connected_iff_subset_connected.mpr $
assume h : disconnected_subset i,
  let ⟨s₁, s₂, sep⟩ := h in
  let ⟨_, _, _, _, _, _⟩ := sep in
  let ⟨a, _⟩ := exists_mem_of_ne_empty ‹s₁ ∩ i ≠ ∅›, ⟨b, _⟩ := exists_mem_of_ne_empty ‹s₂ ∩ i ≠ ∅› in
  have a ∈ s₁, from mem_of_mem_inter_left ‹a ∈ s₁ ∩ i›,
  have a ∈ i, from mem_of_mem_inter_right ‹a ∈ s₁ ∩ i›,
  have b ∈ s₂, from mem_of_mem_inter_left ‹b ∈ s₂ ∩ i›,
  have b ∈ i, from mem_of_mem_inter_right ‹b ∈ s₂ ∩ i›,
  have a ≠ b, from
    (assume _ : a = b,
    have b ∈ s₁ ∩ s₂ ∩ i, from ⟨⟨‹a = b› ▸ ‹a ∈ s₁›, ‹b ∈ s₂›⟩, ‹b ∈ i›⟩,
    show false, from eq_empty_iff_forall_not_mem.1 ‹s₁ ∩ s₂ ∩ i = ∅› b ‹b ∈ s₁ ∩ s₂ ∩ i›),
  begin
    --wlog : a < b using [a b, b a],
    --exact ne_iff_lt_or_gt.mp ‹a ≠ b›,
    exact
      have a < b, from sorry, --wlog in
      have Icc a b ⊆ i, from
        (suffices (∀x, x ∈ Icc a b → x ∈ i), by simpa only [subset_def],
        assume x,
        assume _ : x ∈ Icc a b, 
        have hab : a ≤ x ∧ x ≤ b, from mem_set_of_eq.mp ‹x ∈ Icc a b›,
        show x ∈ i, from ‹interval i› a x b ‹a ∈ i› ‹b ∈ i› hab.1 hab.2),
      let s₁' := s₁ ∩ Icc a b, s₂' := s₂ ∩ Icc a b in
      have s₁' ∪ s₂' = Icc a b, from
        (calc  s₁' ∪ s₂' = (s₁ ∪ s₂) ∩ Icc a b : eq.symm (inter_distrib_right s₁ s₂ (Icc a b))
                     ... = Icc a b             : inter_eq_self_of_subset_right (subset.trans ‹Icc a b ⊆ i› ‹i ⊆ s₁ ∪ s₂›)),
      let sup := real.Sup s₁' in
      have is_closed s₁', from subset_separation_left_inter_closed sep is_closed_Icc ‹Icc a b ⊆ i›,
      have is_closed s₂', from subset_separation_right_inter_closed sep is_closed_Icc ‹Icc a b ⊆ i›,

      have bdd_above s₁', from bdd_above_Int2 bdd_above_Icc,
      have s₁' ≠ ∅, from ne_empty_of_mem (⟨‹a ∈ s₁›, mem_set_of_eq.mpr ⟨le_refl a, le_of_lt ‹a < b›⟩⟩),
      have sup ∈ s₁', from sup_in_closed ‹is_closed s₁'› ‹bdd_above s₁'› ‹s₁' ≠ ∅›,
      have sup ∈ Icc a b, from mem_of_mem_inter_right ‹sup ∈ s₁'›,
      have sup ∈ i, from mem_of_subset_of_mem ‹Icc a b ⊆ i› ‹sup ∈ Icc a b›,

      have sup ≤ b, from (mem_def.mp ‹sup ∈ Icc a b›).2,
      let s₂'' := s₂' ∩ Icc sup b in
      let inf := real.Inf s₂'' in

      have is_closed s₂'', from is_closed_inter ‹is_closed s₂'› is_closed_Icc,
      have bdd_below s₂', from bdd_below_Int2 bdd_below_Icc,
      have bdd_below s₂'', from bdd_below_Int1 ‹bdd_below s₂'›,
      have b ∈ s₂', from ⟨‹b ∈ s₂›, mem_set_of_eq.mpr ⟨le_of_lt ‹a < b›, le_refl b⟩⟩,
      have s₂'' ≠ ∅, from ne_empty_of_mem ⟨‹b ∈ s₂'›, mem_set_of_eq.mpr ⟨‹sup ≤ b›, le_refl b⟩⟩,
      have inf ∈ s₂'', from inf_in_closed ‹is_closed s₂''› ‹bdd_below s₂''› ‹s₂'' ≠ ∅›,
      have inf ∈ Icc a b, from mem_of_mem_inter_right $ mem_of_mem_inter_left ‹inf ∈ s₂''›,
      have inf ∈ i, from mem_of_subset_of_mem ‹Icc a b ⊆ i› ‹inf ∈ Icc a b›,

      have sup ≤ inf, from (mem_def.mp (mem_of_mem_inter_right ‹inf ∈ s₂''›)).left,
      have sup < inf, from lt_of_le_of_ne ‹sup ≤ inf› $ ne.intro
        (assume _ : sup = inf,
        have inf ∈ s₁', from ‹sup = inf› ▸ ‹sup ∈ s₁'›,
        have inf ∈ s₁ ∩ s₂ ∩ i, from ⟨⟨mem_of_mem_inter_left ‹inf ∈ s₁'›, mem_of_mem_inter_left $ mem_of_mem_inter_left ‹inf ∈ s₂''›⟩, ‹inf ∈ i›⟩,
        show false, from mem_empty_eq inf ▸ ‹s₁ ∩ s₂ ∩ i = ∅› ▸ ‹inf ∈ s₁ ∩ s₂ ∩ i›),
      
      let ⟨z, _⟩ := exists_real_between ‹sup < inf› in
      have sup < z, from ‹sup < z ∧ z < inf›.left,
      have z < inf, from ‹sup < z ∧ z < inf›.right,
      have z ∈ Ioo sup inf, from mem_set_of_eq.mp (and.intro ‹sup < z› ‹z < inf›),
      have z ∈ i, from ‹interval i› sup z inf ‹sup ∈ i› ‹inf ∈ i› (le_of_lt ‹sup < z›) (le_of_lt ‹z < inf›),
      have z ∈ s₁ ∪ s₂, from mem_of_subset_of_mem ‹i ⊆ s₁ ∪ s₂› ‹z ∈ i›,
      show false, from mem_union.elim ‹z ∈ s₁ ∪ s₂›
        (assume _ : z ∈ s₁,
        have z ∈ s₁',
          begin
            constructor,
            assumption,
            constructor,
            transitivity sup,
            exact (mem_def.mp ‹sup ∈ Icc a b›).left,
            exact le_of_lt ‹sup < z›,
            transitivity inf,
            exact le_of_lt ‹z < inf›,
            exact (mem_def.mp ‹inf ∈ Icc a b›).right
          end,
        have z ≤ sup, from real.le_Sup s₁' ‹bdd_above s₁'› ‹z ∈ s₁'›,
        not_lt_of_le ‹z ≤ sup› ‹sup < z›)
        (assume _ : z ∈ s₂,
        have z ∈ s₂'',
          begin
            constructor,
            constructor,
            assumption,
            constructor,
            transitivity sup,
            exact (mem_def.mp ‹sup ∈ Icc a b›).left,
            exact le_of_lt ‹sup < z›,
            transitivity inf,
            exact le_of_lt ‹z < inf›,
            exact (mem_def.mp ‹inf ∈ Icc a b›).right,
            constructor,
            exact le_of_lt ‹sup < z›,
            transitivity inf,
            exact le_of_lt ‹z < inf›,
            exact (mem_def.mp ‹inf ∈ Icc a b›).right
          end,
        have z ≥ inf, from real.Inf_le s₂'' ‹bdd_below s₂''› ‹z ∈ s₂''›,
        not_le_of_gt ‹inf > z› ‹inf ≤ z›)
  end

lemma is_open_Ioi {b : ℝ} : is_open (Ioi b) := sorry

theorem connected_of_interval {i : set ℝ} [connected_space i] : interval i :=
by intros x y z _ _ _ _;
exact
  --assume x≠y and y≠z
  classical.by_contradiction
  (assume _ : y ∉ i,
  have Iio y ∩ Ioi y ∩ i = ∅, from sorry,
  have i ⊆ Iio y ∪ Ioi y, from sorry,
  have Iio y ∩ i ≠ ∅, from sorry, --contains x
  have Ioi y ∩ i ≠ ∅, from sorry, --contains z
  have disconnected_subset i, from ⟨Iio y, Ioi y, is_open_Iio, is_open_Ioi, ‹Iio y ∩ i ≠ ∅›, ‹Ioi y ∩ i ≠ ∅›, ‹Iio y ∩ Ioi y ∩ i = ∅›, ‹i ⊆ Iio y ∪ Ioi y›⟩,
  have ¬connected_space i, by simpa [subtype_connected_iff_subset_connected],
  this ‹connected_space i›)


end real

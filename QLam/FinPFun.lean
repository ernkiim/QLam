import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.PFun
import Mathlib.Data.Multiset.MapFold
import Mathlib.Order.Basic

------------------------------------------------------------------------
-- Finite maps (partial functions with finite domain)

open Prod Insert

@[ext]
structure FinPFun (α β : Type*) where
  graph : Finset (α × β)
  well_defined : ⟨a,b⟩ ∈ graph → ⟨a,b'⟩ ∈ graph → b = b'
deriving DecidableEq

infixr:1000 " →f " => FinPFun

namespace FinPFun

open FinPFun

variable {α β : Type*} {a a' : α} {b b' : β} (f g : α →f β)

@[simp, grind .]
theorem well_defined' (h₁ : ⟨a, b⟩ ∈ f.graph) (h₂ : ⟨a, b'⟩ ∈ f.graph) : b = b' :=
  f.well_defined h₁ h₂

def Dom : Finset α where
  val := f.graph.val.map fst
  nodup := by
    apply Multiset.Nodup.map_on
    · intro ⟨a, b⟩ ab_in ⟨a, b'⟩ ab'_in rfl
      simp only [Prod.mk.injEq, true_and]
      exact f.well_defined ab_in ab'_in
    · exact f.graph.nodup

theorem unique_result_of_dom : a ∈ Dom f → ∃! b, ⟨a, b⟩ ∈ graph f := by
  unfold Dom; simp!
  intro b ab_in
  exact ⟨b, ab_in, fun b' ab'_in => f.well_defined ab'_in ab_in⟩

theorem unique_pair_of_dom : a ∈ Dom f → ∃! p, p.1 = a ∧ p ∈ graph f := by
  unfold Dom; simp!
  intro b ab_in
  exact ⟨⟨a, b⟩, ⟨rfl, ab_in⟩, fun p' ⟨p1_eq_a, p'_in⟩ => by
    ext
    · simp!; exact p1_eq_a
    · simp!; exact f.well_defined p'_in (p1_eq_a ▸ ab_in)⟩

theorem graph_of_dom (h : ⟨a, b⟩ ∈ graph f) : a ∈ Dom f := by
  unfold Dom; simp!; exact ⟨b, h⟩

@[simp, grind ·]
theorem dom_iff_graph : a ∈ Dom f ↔ ∃ b, ⟨a, b⟩ ∈ graph f := by
  constructor
  · intro a_in; exact (unique_result_of_dom f a_in).exists
  · intro ⟨_, h⟩; unfold Dom; simp!; exact ⟨_, h⟩

theorem fst_dom_of_graph : p ∈ graph f → p.1 ∈ Dom f := by
  intro p_in
  exact (dom_iff_graph f).mpr ⟨p.2, p_in⟩

theorem not_graph_of_not_dom : p.1 ∉ Dom f → p ∉ graph f := by
  contrapose; exact fst_dom_of_graph f

------------------------------------------------------------------------
-- Empty

protected def empty : α →f β where
  graph := ∅
  well_defined := by simp

instance : EmptyCollection (α →f β) := ⟨FinPFun.empty⟩

@[simp, grind =] theorem graph_empty_of_empty : graph (∅ : α →f β) = ∅ := rfl
@[simp, grind =] theorem dom_empty_of_empty : Dom   (∅ : α →f β) = ∅ := rfl

------------------------------------------------------------------------
-- Singleton

protected def singleton (p : α × β) : α →f β where
  graph := {p}
  well_defined := by rcases p; simp

instance : Singleton (α × β) (α →f β) := ⟨FinPFun.singleton⟩

@[simp, grind =]
theorem graph_singleton_of_singleton (p : α × β) : graph (singleton p) = {p} := rfl

theorem mem_graph_singleton (p p' : α × β) : p ∈ graph (singleton p') → p = p' := by simp

@[simp, grind =]
theorem dom_singleton_of_singleton (p : α × β) : Dom (singleton p) = {p.1} := rfl

theorem mem_dom_singleton (a : α) (p' : α × β) : a ∈ Dom (singleton p') → a = p'.1 := by simp

------------------------------------------------------------------------
-- Partial order and OrderBot

instance instPartialOrder : PartialOrder (α →f β) where
  le f g := f.graph ⊆ g.graph
  lt f g := f.graph ⊂ g.graph
  le_refl f := Finset.Subset.refl f.graph
  le_trans f g h := Finset.Subset.trans
  le_antisymm f g := by
    intro le₁ le₂; apply FinPFun.ext; exact Finset.Subset.antisymm le₁ le₂

theorem empty_le (f : α →f β) : ∅ ≤ f := by simp [(· ≤ ·)]

instance instOrderBot : OrderBot (α →f β) where
  bot := ∅
  bot_le := empty_le

@[simp, grind =] theorem bot_eq_empty : (⊥ : α →f β) = ∅ := rfl

@[grind →]
theorem mem_graph_of_mem_le (h : f ≤ g) :
    ⟨a, b⟩ ∈ graph f → ⟨a, b⟩ ∈ graph g := by
    simp only [(· ≤ ·)] at h
    apply h

theorem mem_dom_of_mem_le (h : f ≤ g) : a ∈ Dom f → a ∈ Dom g := by grind

theorem dom_le (h : f ≤ g) : Dom f ≤ Dom g := by simp only [(· ≤ ·)]; grind

------------------------------------------------------------------------
-- Disjointness helpers (general α →f β)

/-- If the domains of f and g are disjoint, so are their graphs. -/
theorem disjoint_graph_of_dom {f g : α →f β} :
    Disjoint (Dom f) (Dom g) → Disjoint (graph f) (graph g) := by
  contrapose; intro h
  have ⟨p, p_inf, p_ing⟩ := Finset.not_disjoint_iff.mp h
  apply Finset.not_disjoint_iff.mpr
  exact ⟨p.1, fst_dom_of_graph f p_inf, fst_dom_of_graph g p_ing⟩

theorem not_disjoint_of_in_graph {f g : α →f β}
    (h₁ : (a, b) ∈ f.graph) (h₂ : (a, b') ∈ g.graph) :
    ¬ Disjoint (Dom f) (Dom g) :=
  Finset.not_disjoint_iff.mpr ⟨a, graph_of_dom f h₁, graph_of_dom g h₂⟩

/-- Dom f is disjoint from ∅. -/
@[simp]
theorem disjoint_dom_empty_right (f : α →f β) : Disjoint (Dom f) (Dom (∅ : α →f β)) := by
  simp

/-- Dom f is disjoint from Dom {p} iff p.1 ∉ Dom f. -/
theorem disjoint_dom_singleton_iff {f : α →f β} {p : α × β} :
    Disjoint (Dom f) (Dom (singleton p)) ↔ p.1 ∉ Dom f := by
  simp [Finset.disjoint_left]
  grind

/-- If a ∉ Dom f then Dom f and Dom {(a,b)} are disjoint. -/
theorem disjoint_dom_singleton_of_not_mem {f : α →f β} {a : α} {b : β}
    (h : a ∉ Dom f) : Disjoint (Dom f) (Dom (singleton ⟨a, b⟩)) :=
  disjoint_dom_singleton_iff.mpr h

------------------------------------------------------------------------
-- Cons

section Cons

variable (p : α × β) (f : α →f β) (h : p.1 ∉ Dom f)

def cons : α →f β where
  graph := Finset.cons p f.graph
    (by contrapose h; exact fst_dom_of_graph f h)
  well_defined := by grind

notation p " :[" h "]: " Γ => cons p Γ h

@[simp, grind =]
theorem graph_cons :
    graph (p :[h]: f) = Finset.cons p (graph f) (not_graph_of_not_dom f h) := by
  ext ⟨a, b⟩; unfold cons; grind

@[simp, grind =]
theorem dom_cons : Dom (p :[h]: f) = Finset.cons p.1 (Dom f) h := by
  ext a; unfold cons; grind

theorem mem_graph_cons_self : p ∈ graph (p :[h]: f) := by grind

theorem mem_graph_cons_of_mem (p' : α × β) : p' ∈ graph f → p ∈ graph (p :[h]: f) := by grind

theorem mem_dom_cons_self : p.1 ∈ Dom (p :[h]: f) := by grind

theorem mem_dom_cons_of_mem (p' : α × β) : p'.1 ∈ Dom f → p'.1 ∈ Dom (p :[h]: f) := by grind

theorem cons_le : f ≤ (p :[h]: f) := by simp only [(· ≤ ·)]; grind

end Cons

------------------------------------------------------------------------
-- Insert / Erase

section Insert

variable [DecidableEq α]

def erase (f : α →f β) (a : α) : α →f β where
  graph := f.graph.filter (fst · ≠ a)
  well_defined := by grind

@[simp, grind =]
theorem dom_erase (f : α →f β) (a : α) : Dom (erase f a) = Finset.erase (Dom f) a := by
  unfold erase; grind

@[simp, grind =]
theorem erase_eq_of_not_dom (f : α →f β) (a : α) (h : a ∉ Dom f) : erase f a = f := by
  unfold erase; ext; grind

theorem notMem_dom_erase (f : α →f β) (a : α) : a ∉ Dom (erase f a) := by
  rw [dom_erase]; exact Finset.notMem_erase a f.Dom

@[simp, grind =]
theorem erase_cons (f : α →f β) (p : α × β) (h : p.1 ∉ Dom f) :
    erase (cons p f h) p.1 = f := by
  unfold erase; ext; grind

theorem disjoint_of_disjoint_erase (a : α) (f g : α →f β)
    (ha : a ∉ Dom f) (h : Disjoint (Dom (erase f a)) (Dom g)) :
    Disjoint (Dom f) (Dom g) := by
  rw [dom_erase] at h
  rw [Finset.disjoint_left] at h ⊢
  intro a' a'_in_f a'_in_g
  by_cases eq : a' = a
  · exact ha (eq ▸ a'_in_f)
  · exact h (Finset.mem_erase.mpr ⟨eq, a'_in_f⟩) a'_in_g

def insert (p : α × β) (f : α →f β) : α →f β :=
  cons p (erase f p.1) (notMem_dom_erase f p.1)

instance : Insert (α × β) (α →f β) := ⟨FinPFun.insert⟩
instance : LawfulSingleton (α × β) (α →f β) := ⟨fun _ ↦ rfl⟩
notation f " :+ " p => insert p f

theorem insert_eq_cons (p : α × β) (f : α →f β) (h : p.1 ∉ Dom f) :
    insert p f = cons p f h := by
  unfold insert; grind

@[simp, grind =]
theorem graph_insert_of_notmem (h : p.1 ∉ Dom f) :
    graph (insert p f) = Finset.cons p (graph f) (by grind) := by
  rw [insert_eq_cons p f h]
  grind

theorem mem_graph_insert : p ∈ graph (insert p f) := by unfold insert; grind

@[simp, grind =]
theorem dom_insert (p : α × β) (f : α →f β) :
    Dom (insert p f) = Insert.insert p.1 (Dom f) := by
  by_cases p.1 ∈ Dom f
  · case pos h => unfold insert; grind
  · case neg   => grind

theorem mem_dom_insert (p : α × β) (f : α →f β) : p.1 ∈ Dom (insert p f) := by simp

theorem dom_subset_insert (p : α × β) (f : α →f β) : Dom f ⊆ Dom (insert p f) := by
  simp [Finset.subset_insert]

theorem le_insert_of_not_mem {p : α × β} {f : α →f β} (h : p.1 ∉ Dom f) :
    f ≤ insert p f := by
  rw [insert_eq_cons _ _ h]
  exact cons_le _ _ h

------------------------------------------------------------------------
-- Graph / domain lemmas for insert

theorem mem_graph_insert_of_ne {f : α →f β} {p q : α × β} (hne : q.1 ≠ p.1) :
    q ∈ (insert p f).graph ↔ q ∈ f.graph := by
  unfold FinPFun.insert
  rw [graph_cons]
  simp only [Finset.mem_cons, erase, Finset.mem_filter]
  constructor
  · rintro (rfl | ⟨hq, _⟩)
    · exact absurd rfl hne
    · exact hq
  · intro hq
    right; exact ⟨hq, fun h => hne (h ▸ rfl)⟩

theorem mem_graph_insert_iff {f : α →f β} {p q : α × β} :
    q ∈ (insert p f).graph ↔ q = p ∨ (q.1 ≠ p.1 ∧ q ∈ f.graph) := by
  unfold FinPFun.insert
  rw [graph_cons]
  simp only [Finset.mem_cons, erase, Finset.mem_filter]
  constructor
  · rintro (rfl | ⟨hq, hne⟩)
    · left; rfl
    · right; exact ⟨fun h => hne (h ▸ rfl), hq⟩
  · rintro (rfl | ⟨hne, hq⟩)
    · left; rfl
    · right; exact ⟨hq, fun h => hne (h ▸ rfl)⟩

theorem insert_insert_self (p : α × β) (f : α →f β) :
    insert p (insert p f) = insert p f := by
  ext ⟨z, C⟩
  simp only [mem_graph_insert_iff]
  constructor
  · rintro (rfl | ⟨hne, h⟩)
    · left; rfl
    · rcases h with rfl | ⟨hne', hf⟩
      · exact absurd rfl hne
      · right; exact ⟨hne', hf⟩
  · rintro (rfl | ⟨hne, hf⟩)
    · left; rfl
    · right; exact ⟨hne, Or.inr ⟨hne, hf⟩⟩

theorem insert_insert_comm {f : α →f β} {p q : α × β} (hpq : p.1 ≠ q.1) :
    insert p (insert q f) = insert q (insert p f) := by
  ext ⟨z, C⟩
  simp only [mem_graph_insert_iff]
  constructor
  · rintro (rfl | ⟨hnep, rfl | ⟨hneq, hf⟩⟩)
    · right; exact ⟨hpq, Or.inl rfl⟩
    · left; rfl
    · right; exact ⟨fun h => hneq (h ▸ rfl), Or.inr ⟨hnep, hf⟩⟩
  · rintro (rfl | ⟨hneq, rfl | ⟨hnep, hf⟩⟩)
    · right; exact ⟨hpq.symm, Or.inl rfl⟩
    · left; rfl
    · right; exact ⟨fun h => hnep (h ▸ rfl), Or.inr ⟨hneq, hf⟩⟩

------------------------------------------------------------------------
-- erase and insert interact

theorem erase_insert (p : α × β) (f : α →f β) :
    erase (insert p f) p.1 = erase f p.1 := by
  ext ⟨z, C⟩
  simp only [erase, Finset.mem_filter, mem_graph_insert_iff]
  constructor
  · rintro ⟨rfl | ⟨hne, hf⟩, hzp⟩
    · exact absurd rfl hzp
    · exact ⟨hf, hzp⟩
  · rintro ⟨hf, hzp⟩
    exact ⟨Or.inr ⟨fun h => hzp (h ▸ rfl), hf⟩, hzp⟩

theorem erase_insert_of_not_mem {p : α × β} {f : α →f β} (h : p.1 ∉ Dom f) :
    erase (insert p f) p.1 = f := by
  rw [erase_insert, erase_eq_of_not_dom _ _ h]

end Insert

------------------------------------------------------------------------
-- Conj

section Conj

variable (f g : α →f β) (h : Disjoint (Dom f) (Dom g))

def conj : α →f β where
  graph := Finset.disjUnion f.graph g.graph (disjoint_graph_of_dom h)
  well_defined := by
    intro b b' a
    simp only [Finset.mem_disjUnion]
    rintro (in_f | in_g) (in'_f | in'_g)
    · exact f.well_defined in_f in'_f
    · absurd h; exact not_disjoint_of_in_graph in_f in'_g
    · absurd h; exact not_disjoint_of_in_graph in'_f in_g
    · exact g.well_defined in_g in'_g

@[simp, grind =]
theorem graph_conj_disjUnion :
    graph (conj f g h) =
    Finset.disjUnion (graph f) (graph g) (disjoint_graph_of_dom h) := rfl

@[grind! .]
theorem conj_le : f ≤ conj f g h ∧ g ≤ conj f g h := by simp [(· ≤ ·)]; grind

@[grind →]
theorem conj_empty : conj f g h = ∅ ↔ f = ∅ ∧ g = ∅ := by
  constructor
  · intro eq; constructor <;> (apply le_bot_iff.mp; grind)
  · rintro ⟨rfl, rfl⟩; rfl

theorem mem_graph_conj_iff : p ∈ graph (conj f g h) ↔ p ∈ graph f ∨ p ∈ graph g := by simp

@[simp, grind =]
theorem dom_conj_disjUnion : Dom (conj f g h) = Finset.disjUnion (Dom f) (Dom g) h := by grind

theorem dom_subset_conj_left : Dom f ⊆ Dom (conj f g h) := by grind
theorem dom_subset_conj_right : Dom g ⊆ Dom (conj f g h) := by grind

theorem mem_dom_conj_iff : a ∈ Dom (conj f g h) ↔ a ∈ Dom f ∨ a ∈ Dom g := by simp

theorem disjoint_dom_conj_right {f g₁ g₂ : α →f β}
    (hd : Disjoint (Dom g₁) (Dom g₂))
    (d₁ : Disjoint (Dom f) (Dom g₁))
    (d₂ : Disjoint (Dom f) (Dom g₂)) :
    Disjoint (Dom f) (Dom (conj g₁ g₂ hd)) := by
  simp only [dom_conj_disjUnion, Finset.disjoint_left, Finset.mem_disjUnion]
  intro a ha hc
  rcases hc with h | h
  · exact (Finset.disjoint_left.mp d₁ ha h)
  · exact (Finset.disjoint_left.mp d₂ ha h)

theorem disjoint_dom_cons_right {h₁ : p.1 ∉ Dom g}
    (h₂ : p.1 ∉ Dom f)
    (h₃ : Disjoint (Dom f) (Dom g)) :
    Disjoint (Dom f) (Dom (p :[h₁]: g)) := by
  simp only [dom_cons, Finset.disjoint_left, Finset.mem_cons]
  intro a ha hc
  rcases hc with rfl | hmem
  · exact h₂ ha
  · exact Finset.disjoint_left.mp h₃ ha hmem

theorem conj_eq_empty_iff {f g : α →f β} {h : Disjoint (Dom f) (Dom g)} :
    conj f g h = ∅ ↔ f = ∅ ∧ g = ∅ := conj_empty f g h
    
end Conj

end FinPFun

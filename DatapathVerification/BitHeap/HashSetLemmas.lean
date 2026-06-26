import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

open Std

theorem List.Perm.of_nodup_of_nodup_of_forall_mem_iff_mem {α : Type u} (l₁ l₂ : List α)
  (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h₃ : ∀ (a : α), a ∈ l₁ ↔ a ∈ l₂) :
    l₁.Perm l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp_all [List.eq_nil_iff_forall_not_mem]
  | cons hd tl ih =>
    classical
    simp only [mem_cons] at h₃
    refine (Perm.trans ((perm_cons _).2 ?_) (perm_cons_erase ((h₃ hd).1 (Or.inl rfl))).symm)
    exact ih _ h₁.tail (h₂.erase _) (by simpa [h₂.mem_erase_iff, ← h₃, and_or_left] using
      fun _ => (ne_of_mem_of_not_mem · (List.nodup_cons.1 h₁).1))

theorem List.filter_nodup {l : List α} {p : α → Bool} (hl : l.Nodup) :
    (l.filter p).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp [filter_cons]
    split
    · grind
    · grind

theorem Std.HashMap.nodup_toList [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
  (m : HashMap α β) :
    m.toList.Nodup := by
  have := HashMap.nodup_keys (m := m)
  simp [← HashMap.map_fst_toList_eq_keys] at this
  rw [List.nodup_iff_pairwise_ne] at this ⊢
  apply List.Pairwise.of_map _ _ this
  simp

theorem Std.HashSet.nodup_toList [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
  (m : Std.HashSet α) :
    m.toList.Nodup := by
  simp [toList, ← HashMap.map_fst_toList_eq_keys]
  rw [List.nodup_iff_pairwise_ne]
  apply List.Pairwise.map (fun (x : α × Unit) => x.1) (R := fun a b => a ≠ b)
  · grind
  · apply HashMap.nodup_toList

theorem Std.HashMap.erase_toList_perm_filter_toList [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
  (m : HashMap α β) :
    (m.erase d).toList.Perm (m.toList.filter (fun x => (x.1 == d) = false)) := by
  apply List.Perm.of_nodup_of_nodup_of_forall_mem_iff_mem
  · apply HashMap.nodup_toList
  · apply List.filter_nodup
    apply HashMap.nodup_toList
  · simp [HashMap.getKey?_erase, HashMap.getElem?_erase]
    intro a b
    by_cases h : d == a
    · simp [h, BEq.symm h]
    · simp at h
      simp [h, BEq.symm_false h]

theorem Std.HashSet.erase_toList_perm_filter_toList [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
  (m : Std.HashSet α) :
    (m.erase d).toList.Perm (m.toList.filter (fun x => (x == d) = false)) := by
  simp [toList, ← HashMap.map_fst_toList_eq_keys, erase]
  apply List.Perm.of_nodup_of_nodup_of_forall_mem_iff_mem
  · rw [List.nodup_iff_pairwise_ne]
    apply List.Pairwise.map (fun (x : α × Unit) => x.1) (R := fun a b => a ≠ b)
    · grind
    · apply HashMap.nodup_toList
  · apply List.filter_nodup
    apply List.Pairwise.map (fun (x : α × Unit) => x.1) (R := fun a b => a ≠ b)
    · grind
    · apply HashMap.nodup_toList
  · intro a
    simp only [List.mem_filter, Bool.not_eq_eq_eq_not,
      Bool.not_true, List.mem_map]
    simp [HashMap.getKey?_erase, HashMap.getElem?_erase]
    by_cases h : d == a
    · simp [h, BEq.symm h]
    · simp at h
      simp [h, BEq.symm_false h]

import Mathlib

universe u

variable {α : Type u} [LE α]

def heap_left_index (i : Nat) := 2*i+1

def heap_right_index (i : Nat) := 2*i+2

def heap_parent_index (i : Nat) := (i-1)/2

abbrev heap_max_parent_index (xs : Array α) := xs.size/2-1

@[simp]
lemma heap_max_valid : ∀ (i : Fin (heap_max_parent_index xs)), i < xs.size := by grind

abbrev heap_left (xs : Array α) (i : Fin (heap_max_parent_index xs)) :=
  have _ : heap_left_index i < xs.size := by grind [heap_left_index]
  xs[heap_left_index i] 

abbrev heap_right (xs : Array α) (i : Fin (heap_max_parent_index xs)) :=
  have _ : heap_right_index i < xs.size := by grind [heap_right_index]
  xs[heap_right_index i] 

structure Heap (α : Type u) [LE α] where
  xs : Array α
  
  max_heap : 
    ∀ (i : Fin (heap_max_parent_index xs)),
    xs[i] ≥ (heap_left xs i) ∧ xs[i] ≥ (heap_right xs i)
      
def Heap.find_max (H : Heap α) : Option α := 
  if h : (0 < H.xs.size) then Option.some H.xs[0] else Option.none

def Heap.insert (H : Heap α) (new : α) : Heap α := 
  match Heap.find_max H with
  | Option.none => Heap.mk #[new] (by grind)
  | Option.some a => 
      let xs_new := H.xs ++ #[new]
      let p := xs_new[heap_parent_index (H.xs.size)]?
      sorry
  


  

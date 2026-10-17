/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

/-! # Task graphs

`spawnAll` runs independent tasks, `spawnAfter` runs tasks once a set of tasks is done, and
`join` collects results without blocking a worker. The lemmas state the results as plain
computations, so proofs about a task graph reduce to proofs about the functions it runs.
-/

@[expose] public section
namespace CompPoly.Tasks

universe u v
variable {α : Type u} {β : Type v}

/-- Wait for every task without blocking a worker; results keep the task order. -/
def join (ts : Array (Task α)) : Task (Array α) :=
  ts.foldl (fun acc t ↦ acc.bind (sync := true) fun xs ↦ t.map (sync := true) fun x ↦ xs.push x)
    (.pure #[])

/-- `f i` for every `i < n`, as tasks. -/
@[inline] def spawnAll (n : Nat) (f : Nat → α) : Array (Task α) :=
  (Array.range n).map fun i ↦ Task.spawn fun _ ↦ f i

/-- `f xs i` for every `i < n`, as tasks that start once every task of `deps` is done; `xs` are
their results. -/
@[inline] def spawnAfter (deps : Array (Task α)) (n : Nat) (f : Array α → Nat → β) :
    Array (Task β) :=
  let all := join deps
  (Array.range n).map fun i ↦ all.bind fun xs ↦ Task.spawn fun _ ↦ f xs i

/-- A dependent task's result is its continuation's result on the dependency's result. -/
@[simp] theorem get_bind (t : Task α) (f : α → Task β) (prio : Task.Priority) (sync : Bool) :
    (t.bind f prio sync).get = (f t.get).get := rfl

/-- A spawned task's result is its function's result. -/
@[simp] theorem get_spawn (fn : Unit → α) (prio : Task.Priority) :
    (Task.spawn fn prio).get = fn () := rfl

/-- Joining tasks keeps their results in order. -/
theorem get_join (ts : Array (Task α)) : (join ts).get = ts.map Task.get := by
  suffices h : ∀ (l : List (Task α)) (acc : Task (Array α)),
      (l.foldl (fun acc t ↦ acc.bind (sync := true) fun xs ↦
        t.map (sync := true) fun x ↦ xs.push x) acc).get = acc.get ++ (l.map Task.get).toArray by
    rw [join, ← Array.foldl_toList, h]
    apply Array.toList_inj.mp
    simp
  intro l
  induction l with
  | nil => intro acc; simp
  | cons t l ih =>
    intro acc
    rw [List.foldl_cons, ih]
    apply Array.toList_inj.mp
    simp [Task.bind, Task.map]

/-- The results of independent tasks. -/
@[simp] theorem map_get_spawnAll (n : Nat) (f : Nat → α) :
    (spawnAll n f).map Task.get = (Array.range n).map f := by
  simp only [spawnAll, Array.map_map]
  rfl

/-- The results of dependent tasks, given the results of their dependencies. -/
@[simp] theorem map_get_spawnAfter (deps : Array (Task α)) (n : Nat) (f : Array α → Nat → β) :
    (spawnAfter deps n f).map Task.get = (Array.range n).map (f (deps.map Task.get)) := by
  simp only [spawnAfter, Array.map_map]
  congr 1
  funext i
  change f (join deps).get i = _
  rw [get_join]

end CompPoly.Tasks

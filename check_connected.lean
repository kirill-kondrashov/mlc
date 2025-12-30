import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Instances.Real

open Topology Set

example (s : Set ℝ) (x : ℝ) (h : x ∉ s) : connectedComponentIn s x = ∅ := by
  rw [eq_empty_iff_forall_not_mem]
  intro y hy
  have : y ∈ s := mem_of_mem_connectedComponentIn hy
  contradiction


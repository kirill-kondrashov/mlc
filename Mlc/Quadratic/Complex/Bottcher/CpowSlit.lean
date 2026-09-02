import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Basic

namespace MLC

open Complex Filter
open scoped Topology

lemma tendsto_log_of_tendsto_slitPlane {α : Type*} {l : Filter α}
    {f : α → ℂ} {x : ℂ}
    (hf : Tendsto f l (𝓝 x)) (hx : x ∈ Complex.slitPlane) :
    Tendsto (fun t => Complex.log (f t)) l (𝓝 (Complex.log x)) :=
  hf.clog hx

end MLC

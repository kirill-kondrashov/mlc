# TASK 104 — Implement parameter critical-orbit local germ

## Objective

Implement a concrete holomorphic parameter-neighborhood finite-time root branch
along the escaping critical orbit.

## Boundary

Keep the result local in parameter and finite in escape time. Do not introduce
global continuation or whole-basin contracts.

The critical-value basin bridge requires a direct reindexing proof
`c ∈ K c → c ∈ MandelbrotSet`; `mem_K_of_mandelbrot` alone is insufficient.
The final result must use an open ball contained in the raw ratio neighborhood.

## Result

Write:

`plan/GPT54_RESULT_104_IMPLEMENT_PARAMETER_CRITICAL_ORBIT_LOCAL_GERM.md`

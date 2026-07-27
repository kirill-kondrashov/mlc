Implement the checked Gauss--Lucas partial result:

`plan/GPT54_TASK_93_IMPLEMENT_GAUSS_LUCAS_PARAMETER_ORBIT_BOUND.md`

# Completed -- do not rerun

Result 93 added `Mlc/ParameterOrbitPolynomial.lean` and proved:

```lean
parameterOrbitPolynomial_derivative_root_norm_le_two
```

The result only locates critical points in `‖c‖ ≤ 2`; it does not control
critical values or prove finite filled-level connectivity. The finite-level
branch is therefore blocked at those remaining theorems.

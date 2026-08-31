# Supervisor Review 06: Frozen-base falsifiability audit

**Verdict:** repository audit accepted; numerical candidate not accepted.

The result file exists and the read-only safety claims match workspace status.
The structural conclusion is sound: no checked property presently forces the
intersection to be connected, and the old “>99% plus pixel noise” assertion is
not backed by reproducible repository evidence.

The rabbit/basilica candidates do not yet justify a certification task:

1. Components were labelled only inside cropped windows. None of the reported
   windows contains the full Mandelbrot set (the repository proves only the
   global closed-ball radius-2 bound), and the report did not prove the target
   lies inside a crop. Apparent components can reconnect outside the crop.
2. The required component bounding boxes were omitted, so it is impossible to
   tell whether secondary components touch or approach crop boundaries.
3. The ad hoc Python source was not preserved in the report or repository; only
   `/tmp` output was named. The experiment is therefore not reproducible from the
   result artifact.
4. Only 8-neighbor adjacency was used. Comparison with 4-neighbor adjacency and
   boundary-touch diagnostics is needed to understand discretization behavior.
5. The approximate rabbit base parameter's membership in `M` was not certified;
   this matters even for matching the theorem's hypotheses.

The recommendation is revised to **inconclusive, with screening incomplete**.
Run one corrected whole-domain experiment before attempting interval or
topological certification.

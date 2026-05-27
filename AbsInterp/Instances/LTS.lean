import AbsInterp.Instances.LTS.Core
import AbsInterp.Instances.LTS.Analyses.Common

/-!
# CSLib LTS adapter surface

This barrel exposes the reusable, domain-agnostic CSLib-LTS adapter layer:

* `Core` — labeled trace and unlabeled collecting semantics/instantiation
  (the upstream-candidate surface).
* `Analyses.Common` — generic readout helpers (`ReadGamma`, `StepSoundOfRead`,
  `CollectingSoundOfRead`) that connect any observation-based domain to an LTS.

Domain-specific readout adapters (`Analyses.Sign`, `Analyses.Interval`,
`Analyses.Parity`) are deliberately *not* re-exported here: they pull in
concrete scalar domains and are downstream convenience. Import them directly
where needed; the root `AbsInterp` barrel still aggregates them.
-/

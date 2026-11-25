# Local verification

The build log records the Lean 4.35.0-rc3 solution and challenge. The axiom logs cover the solution theorems and the challenge definitions. The physical grid theorem is included in the solution audit.

Comparator used the exports of both selected statements and the primitive constants required by the toolchain. Linux user namespaces were unavailable in the verification environment, so the local check ran without Comparator's nested sandbox. Palomar runs its own comparison in the registry preflight.

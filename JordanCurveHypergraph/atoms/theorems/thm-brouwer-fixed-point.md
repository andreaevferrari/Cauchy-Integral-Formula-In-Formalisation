---
id: 056f1a91c5e6
status: formal
type: theorem
lean:
  - decl: JordanCurve.Brouwer.brouwerFPT
    module: JordanCurve.Brouwer
    line: 502
    state: proven
references:
  - "Maehara, The Jordan curve theorem via the Brouwer fixed point theorem, 1984"
---

# Theorem — a continuous self-map of a compact convex set has a fixed point

The one input the whole separation argument rests on. Everything else in the
proof is plane geometry; this is the only place where a genuinely topological
fact enters.

## Statement

> [!theorem] Brouwer fixed point theorem, in the plane
> Let $s \subseteq \mathbb{C}$ be [[def-compact|compact]], convex and non-empty, and let $f : s \to s$ be [[def-continuity|continuous]]. Then $f$ has a fixed point.

## Notes

> [!note]- Notes (click to expand)
> - Only the two-dimensional case is needed, and only for convex compact sets — which is why the formal proof reaches it through the disc rather than through degree theory.
> - The route in the formalisation is: the once-around loop on the circle is not nullhomotopic, hence there is no retraction of the disc onto its boundary ([[thm-no-retraction-of-disc]]), hence Brouwer for the disc, hence for any convex compact set by nearest-point projection.

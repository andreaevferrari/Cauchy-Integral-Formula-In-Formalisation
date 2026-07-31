---
id: 1e3fd4005e16
status: proved
type: lemma
references:
  - "[[ref-beck|Beck et al., §3.4]]"
---

# Lemma — the derivative of t ↦ e^{it}

The one computation that connects the [[def-complex-exponential|exponential]]
to the geometry of the circle: the velocity of the parametrisation is the
position rotated by a quarter turn, which is what makes the circle a circle.

## Statement

> [!lemma] Derivative of the circular exponential
> The function $t \mapsto e^{it}$ on $\mathbb{R}$ is differentiable, with
> $$
> \frac{d}{dt} e^{it} \; = \; i \, e^{it} .
> $$

## Proof

> [!note]- Proof (click to expand)
> By [[def-complex-exponential]], $e^{it} = \sum_{k \ge 0} \frac{(it)^k}{k!}$, a power series in $t$ with infinite radius of convergence. A power series may be differentiated term by term inside its radius of convergence, so
> $$
> \frac{d}{dt} e^{it} \; = \; \sum_{k \ge 1} \frac{i^k k t^{k-1}}{k!} \; = \; i \sum_{k \ge 1} \frac{(it)^{k-1}}{(k-1)!} \; = \; i \sum_{j \ge 0} \frac{(it)^j}{j!} \; = \; i \, e^{it} . \qquad \square
> $$

## Notes

> [!note]- Notes (click to expand)
> - Term-by-term differentiation of a power series is the one real-analysis input, and it is where the floor of this network is: below it nothing is complex.

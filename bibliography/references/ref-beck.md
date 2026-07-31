---
label: BMPS25
type: reference
license: CC BY 4.0
---
# [BMPS25] Beck, Marchesi, Pixton, Sabalka — A First Course in Complex Analysis

**Matthias Beck, Gerald Marchesi, Dennis Pixton, Lucas Sabalka**,
*A First Course in Complex Analysis*, edition 1.6, August 2025.
<https://matthbeck.github.io/complex.html>

A one-semester undergraduate text from Binghamton University and San Francisco
State University. It assumes as little real analysis as it can — sequences and
series are built from scratch — and works toward the residue theorem.

Where the Cauchy integral formula sits in it:

| | |
|---|---|
| §4.1–4.2 | Integration: definition, basic properties, antiderivatives |
| §4.3 | Cauchy's Theorem (Theorem 4.3.4), Corollary 4.3.8 |
| **§4.4** | **Cauchy's Integral Formula (Theorem 4.4.5)**, Proposition 4.4.6 |
| §5 | Consequences: the formulas for $f'$ and $f''$, and the limit forms |

Theorem 4.4.5 as stated there: if $f$ is holomorphic in a region $G$ and
$\gamma$ is a positively oriented, simple, closed, piecewise smooth path with
$w$ inside $\gamma$ and $\gamma \sim_G 0$, then

$$f(w) = \frac{1}{2\pi i} \int_\gamma \frac{f(z)}{z-w} \, dz.$$

Note that its Cauchy's Theorem 4.3.4 is stated but not fully proved — the book
says the full proof is beyond its scope — so a card cut from §4.3 inherits a
gap that has to be filled from somewhere else.

Licensed **CC BY 4.0**: it may be quoted, adapted and redistributed, including
commercially, as long as the four authors are credited. That is why it was
chosen over the alternatives, which are all NC or unclear.

```bibtex
@book{bmps25,
  author    = {Beck, Matthias and Marchesi, Gerald and Pixton, Dennis and Sabalka, Lucas},
  title     = {A First Course in Complex Analysis},
  edition   = {1.6},
  year      = {2025},
  url       = {https://matthbeck.github.io/complex.html},
  note      = {Licensed CC BY 4.0},
}
```

The PDF and a `pdftotext -layout` dump are in `pipeline/sources/ref-beck/`,
which git does not track.

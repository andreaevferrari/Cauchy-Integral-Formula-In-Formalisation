---
type: rules
---

# The rules of this graph

What a node is, what an edge means, and what may appear where. The
mechanical half — text and graph mirroring each other, no undeclared notion,
uniform notation — is enforced by `tools/*_lint.py` rather than left to
habit. None of it is verification: a card can pass every check and still be
false, and the rule that carries the weight — exact match — is judged by a
person. What the checks buy is structural rigidity, which is what makes a
network worth formalizing from.

## 1 · Nodes (atoms)

One card per mathematical statement, filed under `atoms/<type>s/`:
`theorem`, `proposition`, `lemma`, `corollary`, `claim`, `remark`,
`definition`.

```
---
id: 7a4b8dc3d01c    sha256 of the normalized Statement — the identity
type: theorem
references:         (optional; provenance is metadata, not content.
  - "[[ref-x|Author, §n]]"   one quoted wikilink per citation — the locus
  - "[[pool-card]]"          in the display text; pool cards bare; a
  - "plain citation"         source without a bibliography card stays a
---                          plain string. Never hashed.)
# Theorem — <content-descriptive title>
<optional intro>      one or two sentences of intuition — what the object
                    looks like and why it exists; provenance belongs in
                    the references frontmatter. Never hashed.
## Statement
## Proof            (folded; absent = status: debt, see § Status)
## Notes            (folded callout like Proof; free commentary, never
                    hashed — background, intuition, figures:
                    ![[assets/*.svg]])
```

- The **id** is the mathematics: it changes exactly when the Statement
  changes. Proof, Notes, links' display text, filenames — none affect it.
- **Names describe content** (`thm-classification-free-product`), never a
  source's numbering. Renaming is free (update inlinks); identity is the id.

## 1b · Pools

This vault has one pool, `CauchyIntegralFormulaHypergraph`, and no raw pool:
its cards are written by hand from the sources in `pipeline/sources/` rather
than cut mechanically, so there is nothing to graduate out of.
`tools/pools.py` is the single declaration; every tool reads it, so adding a
pool is one line there.

- **An edge lives with its SOURCE.** It is the source's assertion that its
  statement or proof consumes the target.

## 2 · Edges

One file per edge, filed under `edges/<kind>/`, named `<source>→<target>`:

| kind | meaning | witnessed by |
|---|---|---|
| `uses` | the source's **proof** consumes the target result | a `[[link]]` in the Proof |
| `depends` | the source's **statement** builds on the target result | a `[[link]]` in the Statement |
| `references` | the target is a **definition** the source's text invokes | a `[[link]]` anywhere in Statement/Proof |

- **Text-mirror rule**: every edge is witnessed by a link and every link
  demands an edge — no phantom edges, no silent citations (`edge_lint`).
- **Exact-match rule**: an edge's target states *precisely* what the source
  consumes. If the available card proves something adjacent, insert the
  missing statement as its own card between them.
- An edge's id is `sha256(kind : source-id : target-id)` — it changes
  exactly when the relation or either endpoint's mathematics changes.

## 3 · Status: the two states of a statement

Every non-definition atom carries a `status:` property, computed by
`tools/frontier.py` from two checks — *does the card have a Proof
section?* and *do its Statement/Proof link into `cardpool/`?*

| status | definition | canvas |
|---|---|---|
| `debt` | no `## Proof` section | red |
| `proved` | proof present, every citation resolving inside the pool or to a declared ground notion | type colour |

Transition: `debt` → (write the proof) → `proved`. The third state
`open` — a proof standing on raw-pool cards — cannot occur here, since
this vault has no raw pool.

Definition and remark cards carry no status — neither has anything to prove.
Notes never affect status: a pool link in Notes is a soft pointer, not a
dependency.

## 4 · Where a concept may live

Every mathematical notion is in exactly one of three places:

1. **Definition card** (`atoms/definitions/`) — defines and *only* defines;
   a definition card never carries a theorem.
2. **Fact card** — any true statement, however small
   ($\pi_1(S^3/\Gamma) \cong \Gamma$), is a lemma/proposition with its
   own proof and id; facts
   are never smuggled into definitions or asides.
3. **Ground notion** — a declared primitive, listed in
   [[notation]] § Ground notions.

Anything in none of the three is an undeclared debt.

## 5 · Language

- **Statement and Proof are mathematics only** — no author names, no
  cf./see, no chapter pointers, no bibliography (`noise_lint`); prose in
  Let/Then form; key terms link their definition cards at first occurrence.
  A link alias must contain no math (`$…$` in an alias renders raw) — put
  the link on a plain word: `$S^2$-[[def-s2-bundle-over-s1|bundle]]`.
- **[[notation]] is normative**: one name and one symbol per concept,
  registered at graduation time.
- Statement templates: displayed formula (classification), itemized list
  (reassembly), enumerated conclusions (surgery flow). Proof styles:
  numbered steps for linear derivations, bold part headings for proofs in
  named parts, a single paragraph for one-move proofs; always end $\square$.
- **Every concept links at first occurrence.** In a Statement or Proof, a
  term with a definition card carries a `[[link]]` the first time it
  appears; later bare repeats in the same section are fine. `tools/term_lint.py`
  lists candidates (advisory — it cannot judge compounds).
- **A citation must be supported.** A proof cites `[[card]]` together with
  its *instantiation*: which objects here play the cited statement's data,
  and why its hypotheses hold at this point of the argument. What the
  citation yields is then *displayed* as a formula or stated symbolically
  — never paraphrased loosely. Prose that narrates ("the flow is repaired
  and continues") without a supported citation behind it is a defect.

## 6 · Growth

The graph grows by **writing the next card**: read the source in
`pipeline/sources/`, state the result in this vault's own terms and notation,
name it by content, wire the edges, and either write the proof or mark the
card `status: debt`. A card is never a translation of a source's numbering.
Checks, all of which must print clean:

```
python3 tools/assign_ids.py     ids (idempotent)
python3 tools/render_lint.py    tex→Obsidian rendering
python3 tools/noise_lint.py     no bibliographic noise in the mathematics
python3 tools/edge_lint.py      edges ⇔ text
```

## 7 · The formal counterpart

A card may name the Lean declaration that realises it. The rule is that a
card names a **declaration**, never a line:

```yaml
lean:
  - decl: Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
```

Everything else is resolved by `tools/lean_lint.py` against the checkout in
`.lake/packages/` and written back:

```yaml
lean:
  - decl: Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    module: Mathlib.Analysis.Complex.CauchyIntegral
    line: 532
    state: proven
    rev: fabf563a7c95
```

- **`decl` is the only field written by hand.** It is stable; a line number
  is not. Mathlib moves every day, and a line typed into a card is a claim
  that goes false silently.
- **`rev` is what makes staleness detectable.** It records the package
  revision the line was resolved against, so a card whose `rev` differs from
  `lake-manifest.json` is announcing that its line is a guess.
- **A declaration that cannot be found fails the check.** A card claiming a
  counterpart that no longer exists is worse than a card claiming none — this
  is the job `checkdecls` does for a blueprint, done here for cards.
- **`state` is read from the declaration**, `sorry` or `proven`, rather than
  asserted by the author.
- Naming a counterpart is not a claim that the two say the same thing. Where
  the formal statement is stronger, more general, or differently shaped, the
  card's Notes say so.

The four resolved fields are exactly what Astrolabe's `source: lean` record
reads: `module` gives it the file path it fetches, `line` and `state` it
takes as they are.

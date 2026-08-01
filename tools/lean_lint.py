#!/usr/bin/env python3
r"""lean_lint.py — resolve a card's `lean:` entries against the checkout.

A card names its formal counterpart by DECLARATION, which is stable, and
never by line number, which is not: Mathlib moves constantly, and a line
written by hand is a claim that goes quietly false. So the author writes

    lean:
      - decl: IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel

and this tool fills in the rest by finding the declaration in
`.lake/packages/`:

    lean:
      - decl: IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel
        module: Mathlib.Topology.Homotopy.Lifting
        line: 532
        state: proven
        rev: 4e28ab0...

`rev` is the package revision the line was resolved against, taken from
lake-manifest.json. It is what makes a stale line detectable rather than
merely wrong: re-run after a bump and every line is rewritten, or the
declaration is reported as gone.

**A declaration that cannot be found is an error** (exit 1), which is the
whole point — a card claiming a formal counterpart that no longer exists is
worse than a card claiming none.

The resolved fields are exactly what Astrolabe's leannets renderer reads for
a `source: lean` node: `module` gives it `file` and `path`, and `line` and
`state` it takes as they are.

Usage: python3 tools/lean_lint.py [--fix]
  --fix   write the resolved fields back into the cards
"""
import json, pathlib, re, sys

sys.path.insert(0, str(pathlib.Path(__file__).parent)); import pools

V = pathlib.Path(__file__).resolve().parent.parent
FIX = '--fix' in sys.argv

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|nonrec\s+)*'
    r'(theorem|lemma|irreducible_def|def|abbrev|instance|structure|inductive|class|opaque)\s+'
    r'([^\s({\[:]+)')
NS = re.compile(r'^namespace\s+(\S+)')
END = re.compile(r'^end\s+(\S+)\s*$')


def index_packages():
    """fully-qualified declaration -> (module, line, has_sorry).

    Namespaces are tracked by a stack, which is what makes `theorem foo`
    inside `namespace Complex` resolve as `Complex.foo`. `open` is not
    followed — a name reachable only through it will simply not be found,
    and being told so is better than a wrong hit.
    """
    out = {}
    # this library first, so a card naming a declaration vendored or written
    # HERE resolves to this repository rather than to a namesake upstream
    roots = [V] + sorted((V / '.lake' / 'packages').glob('*'))
    for pkg in roots:
        for f in pkg.rglob('*.lean'):
            if '.lake/' in str(f.relative_to(pkg)):
                continue
            try:
                lines = f.read_text(errors='replace').split('\n')
            except OSError:
                continue
            module = str(f.relative_to(pkg))[:-5].replace('/', '.')
            stack, pending = [], None
            for i, ln in enumerate(lines, 1):
                if (m := NS.match(ln)):
                    stack.append(m.group(1)); continue
                if (m := END.match(ln)):
                    if stack and stack[-1] == m.group(1):
                        stack.pop()
                    continue
                if (m := DECL.match(ln)):
                    if pending:
                        out.setdefault(pending[0], (pending[1], pending[2], pending[3]))
                    name = '.'.join(stack + [m.group(2)])
                    pending = (name, module, i, False)
                    continue
                if pending and re.search(r'\bsorry\b', ln):
                    pending = (pending[0], pending[1], pending[2], True)
            if pending:
                out.setdefault(pending[0], (pending[1], pending[2], pending[3]))
    return out


def revisions():
    """package name -> the revision lake resolved it to."""
    try:
        d = json.loads((V / 'lake-manifest.json').read_text())
    except OSError:
        return {}
    return {p['name']: p.get('rev', '') for p in d.get('packages', [])}


def main():
    if not (V / '.lake' / 'packages').exists():
        print('no .lake/packages — run `lake exe cache get` first'); return 1
    index, revs = index_packages(), revisions()
    print(f'{len(index)} declarations indexed')

    missing = written = total = 0
    for f in pools.atoms():
        text = f.read_text()
        block = re.search(r'^lean:\n((?:  - .*\n(?:    .*\n)*)+)', text, re.M)
        if not block:
            continue
        entries = re.findall(r'  - decl: (\S+)\n(?:    .*\n)*', block.group(1))
        resolved = []
        for decl in entries:
            total += 1
            hit = index.get(decl)
            if not hit:
                print(f'  MISSING  {f.stem}: {decl}')
                missing += 1
                resolved.append(f'  - decl: {decl}\n    state: unresolved\n')
                continue
            module, line, has_sorry = hit
            pkg = module.split('.')[0]
            rev = revs.get(pkg[0].lower() + pkg[1:], revs.get(pkg, ''))[:12]
            resolved.append(
                f'  - decl: {decl}\n'
                f'    module: {module}\n'
                f'    line: {line}\n'
                f'    state: {"sorry" if has_sorry else "proven"}\n'
                + (f'    rev: {rev}\n' if rev else ''))
        new = 'lean:\n' + ''.join(resolved)
        if FIX and new != 'lean:\n' + block.group(1):
            f.write_text(text[:block.start()] + new + text[block.end():])
            written += 1

    print(f'lean lint: {total} declaration(s), {missing} missing'
          + (f', {written} card(s) rewritten' if FIX else ''))
    if not FIX and total:
        print('re-run with --fix to write module/line/state/rev back into the cards')
    return 1 if missing else 0


if __name__ == '__main__':
    sys.exit(main())

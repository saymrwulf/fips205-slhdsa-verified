#!/usr/bin/env python3
"""Classify every external the extraction declares.

For each gen/<dir>/<X>_Template.lean, Aeneas states what the extracted Rust
needs from outside. Each such name must be provided by exactly one of:

  MODEL   — declared in the hand-written sibling gen/<dir>/<X>.lean: an
            assumption, which the axiom gate and the per-certificate cones
            then govern;
  PROVEN  — resolved to a real definition in the proven corpus, because a
            module of this repository declares it (namespace-aware).

Anything else is drift: the extraction asks for something this repository does
not provide.

────────────────────────────────────────────────────────────────────────────
WHY THIS FILE WAS REWRITTEN — 2026-08-01, round-7 external review

The first version matched declarations with a LINE-ORIENTED regex requiring the
keyword and the name on the same physical line, and it did not strip comments.
Both assumptions are false about Lean, and false about Aeneas's own output.
Three of the four forks contain, verbatim:

    axiom
      curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint.neg
      :
      curve25519_dalek.edwards.EdwardsPoint -> Result ...

The old pattern matched nothing there, so that declaration was SILENTLY
DROPPED: no MODEL row, no PROVEN row, and no failure. Every committed
MODEL-CORRESPONDENCE.txt was missing it, and every button passed green over the
incomplete table. A reviewer separately showed that a definition appearing only
inside a `/- ... -/` comment was read as a real declaration, so the scanner
could also report PROVEN for a name Lean resolves to an axiom.

The lesson is not "write a better regex". It is that this scanner was
FAIL-OPEN: input it could not parse produced silence instead of a stop. A gate
that drops what it cannot read is worse than no gate, because the button prints
green across the gap and the gap is invisible in the diff.

This version therefore:
  · strips comments first, including NESTED `/- ... -/` blocks, which Lean has
    and which a non-greedy match would close at the first inner `-/`;
  · allows a declaration's name to appear on a later line than its keyword;
  · tracks `namespace` / `section` / `end` over the stripped text;
  · FAILS CLOSED — every declaration keyword must yield a name, or the scanner
    exits non-zero naming file and line. Nothing is dropped, ever.

WHAT IT STILL IS NOT. This is a source scanner, not a semantic Lean query. It
cannot see `export`, aliases, or how Lean actually resolves a name at
elaboration. A PROVEN row is documentary evidence about the extraction
boundary; it is NOT a Lean-checked fact, and the trust documents must not claim
it is. What the estate relies on for soundness is kernel-side and
environment-derived — Phase 2b's axiom gate, Phase 2c's inventory, and the
exact per-certificate cones of Phase 3/3b — none of which consult this file.
────────────────────────────────────────────────────────────────────────────
"""
import re
import sys
import os
import glob

KEYWORDS = ('axiom', 'def', 'abbrev', 'opaque', 'structure', 'inductive',
            'instance', 'theorem', 'lemma')

# A declaration keyword opening a logical line, after any attributes and
# modifiers. The NAME is deliberately NOT part of this pattern: it may sit on a
# later line, which is precisely the case the previous scanner dropped.
KW = re.compile(
    r'^[ \t]*(?:@\[[^\]]*\][ \t\n]*)*'
    r'(?:private |protected |noncomputable |unsafe |partial |scoped |local )*'
    r'(' + '|'.join(KEYWORDS) + r')(?=[ \t\n])',
    re.M)

IDENT = re.compile(r"[ \t\n]*([A-Za-z_][A-Za-z0-9_.'!?]*)")

NS = re.compile(
    r"^[ \t]*(namespace|section|end)(?:[ \t]+([A-Za-z_][A-Za-z0-9_.']*))?[ \t]*$",
    re.M)


class ScanError(Exception):
    """Raised when a declaration cannot be parsed. Never swallowed."""


def strip_comments(text):
    """Remove Lean comments, preserving newlines so line numbers stay true.

    Block comments NEST in Lean, so this needs a depth counter: a non-greedy
    `/-.*?-/` would close the outer block at the first inner `-/` and leave the
    tail of a nested comment looking like source.
    """
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if text.startswith('/-', i):
            depth += 1
            out.append('  ')
            i += 2
            continue
        if text.startswith('-/', i):
            if depth:
                depth -= 1
            out.append('  ')
            i += 2
            continue
        if depth:
            out.append('\n' if text[i] == '\n' else ' ')
            i += 1
            continue
        if text.startswith('--', i):
            j = text.find('\n', i)
            if j < 0:
                out.append(' ' * (n - i))
                break
            out.append(' ' * (j - i))
            i = j
            continue
        out.append(text[i])
        i += 1
    return ''.join(out)


def declared(path):
    """{fully-qualified name: declaration keyword} for one file.

    Returns a MAPPING, not a set, because the keyword is load-bearing: an
    `axiom` the template never asks for must stop the button, while an extra
    `def` is an ordinary helper. Callers that only need names take `set(...)`.

    Raises ScanError on any declaration keyword whose name cannot be read.
    """
    raw = open(path, encoding='utf-8', errors='replace').read()
    text = strip_comments(raw)

    # Scope events by offset, so each declaration can be placed in its stack.
    events = [(m.start(), m.group(1), m.group(2)) for m in NS.finditer(text)]

    names = {}
    for m in KW.finditer(text):
        im = IDENT.match(text, m.end())
        if not im:
            line = text.count('\n', 0, m.start()) + 1
            raise ScanError(
                "%s:%d: `%s` with no parseable name. This scanner fails closed:"
                " it will not drop a declaration it cannot read."
                % (path, line, m.group(1)))
        stack = []
        for off, kind, arg in events:
            if off > m.start():
                break
            if kind == 'namespace':
                stack.append(arg)
            elif kind == 'section':
                # A NAMED SECTION DOES NOT QUALIFY DECLARATION NAMES. `section
                # Foo` opens a scope for `variable`/`open` and gives `end Foo` a
                # label to match; it does not make `bar` into `Foo.bar`. This
                # line pushed `arg`, so a template reading
                #     section Foo
                #     axiom bar : Nat
                #     end Foo
                # was reported as declaring `Foo.bar`. Round-8 review (GPT-5.6,
                # register key `section-prefix-bug`) showed the consequence:
                # `--names` handed Phase 2d only `Foo.bar`, Lean happily
                # resolved an unrelated `Foo.bar` definition elsewhere in the
                # corpus and returned PROVEN, and the axiom the extraction
                # ACTUALLY depends on was never queried at all. The scanner had
                # been rewritten that same week specifically to be fail-closed.
                # None appends a frame so `end` still balances, and the
                # comprehension below drops it from the prefix.
                stack.append(None)
            elif stack:
                stack.pop()
        prefix = [p for p in stack if p]
        full = '.'.join(prefix + [im.group(1)]) if prefix else im.group(1)
        names.setdefault(full, m.group(1))
    return names


def main(root):
    gen = os.path.join(root, 'gen')
    templates = sorted(glob.glob(os.path.join(gen, '*', '*_Template.lean')))
    # The proven corpus: every generated module that is neither a template nor
    # a hand-written model. These are the files Aeneas produced from Rust.
    models = {t.replace('_Template', '') for t in templates}
    corpus = set()
    for f in sorted(glob.glob(os.path.join(gen, '*', '*.lean'))):
        if f in models or f.endswith('_Template.lean'):
            continue
        corpus.update(declared(f))

    rows, unresolved = [], []
    for t in templates:
        model = t.replace('_Template', '')
        rel = os.path.relpath(t, gen).replace('_Template.lean', '')
        tnames = set(declared(t))
        mkinds = declared(model) if os.path.exists(model) else {}
        mnames = set(mkinds)
        for n in sorted(tnames):
            if n in mnames:
                rows.append(f'{rel}|{n}|MODEL')
            elif n in corpus:
                rows.append(f'{rel}|{n}|PROVEN')
            else:
                rows.append(f'{rel}|{n}|UNRESOLVED')
                unresolved.append(f'{rel}|{n}')
        # AN EXTRA AXIOM IS A FAILURE, and this is the second half of the
        # round-8 section-prefix finding. EXTRA was the one verdict that could
        # not fail: the model declares something the template did not ask for.
        # When the scanner mis-derived the template's name (`Foo.bar` instead of
        # `bar`), the axiom the extraction ACTUALLY depends on did not vanish —
        # it landed here, as a harmless-looking EXTRA row, while the invented
        # name was certified PROVEN. A silent bucket next to a fail-closed
        # parser is just a slower way of dropping things.
        #
        # There is no benign reading of an extra AXIOM either way. The model
        # exists to answer the template; an assumption nothing asks for is
        # either a parse the scanner got wrong or an unaudited assumption
        # nobody is governing. Both must stop the button. Extra non-axiom
        # declarations stay reportable-but-tolerated: helper definitions in a
        # model file are ordinary.
        for n in sorted(mnames - tnames):
            kind = mkinds.get(n, '')
            if kind == 'axiom':
                rows.append(f'{rel}|{n}|EXTRA-AXIOM')
                unresolved.append(f'{rel}|{n} (axiom in the model that no '
                                  f'template external asks for)')
            else:
                rows.append(f'{rel}|{n}|EXTRA')
    print('\n'.join(rows))
    print(f'CORRESPONDENCE-COUNT|{len(rows)}')
    return 1 if unresolved else 0


def emit_names(root):
    """Every name the EXTRACTION asks for, as `<rel>|<name>`.

    Template discovery is unavoidably textual: the template is not imported (it
    would clash with the model, which declares the same names), so no Lean
    environment contains it. That is why `declared()` fails closed — this list
    is the input to the semantic phase, and a name missing here is a name
    nothing will ever check.
    """
    gen = os.path.join(root, 'gen')
    for t in sorted(glob.glob(os.path.join(gen, '*', '*_Template.lean'))):
        rel = os.path.relpath(t, gen).replace('_Template.lean', '')
        for n in sorted(declared(t)):
            print(f'{rel}|{n}')
    return 0


if __name__ == '__main__':
    try:
        if len(sys.argv) > 2 and sys.argv[1] == '--names':
            sys.exit(emit_names(sys.argv[2]))
        sys.exit(main(sys.argv[1]))
    except ScanError as e:
        # Fail closed and loudly. Never degrade to a partial table.
        print('MODEL CORRESPONDENCE SCAN FAILED: %s' % e, file=sys.stderr)
        sys.exit(2)

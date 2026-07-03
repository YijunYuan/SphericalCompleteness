# Lean project cleanup

You are cleaning up a Lean 4 / mathlib-style project. Your job is to bring every file in the
project into full compliance with this repository's naming, style, and documentation
conventions, without changing what any declaration says or proves.

## Inputs

Before touching any code, read the three sibling files in this directory in full:

- `naming.md` — naming conventions (casing rules for `Prop`s vs. `Type`s vs. data, the
  symbol-to-word dictionary, variable-letter conventions, dot notation, predicate/suffix
  conventions, etc.)
- `style.md` — file structure and formatting conventions (copyright header, import grouping,
  module docstrings, indentation, line length, spacing, whitespace, how declarations and proofs
  are laid out, etc.)
- `doc.md` — documentation conventions (module docstrings, declaration docstrings, Markdown/LaTeX
  usage, what a docstring should convey, etc.)

These three documents are the sole source of truth for what "correct" looks like here. Don't
invent additional rules beyond what they specify, and don't skip a rule because it seems minor.

## Scope

Every `.lean` file that belongs to the project must be reviewed — excluding build output and
vendored dependencies (e.g. anything under `.lake/`, `build/`, or similar package-manager
directories). This includes root-level and umbrella/import files, small utility files, and files
that already look clean. "Looks fine at a glance" is not a reason to skip a file — every file gets
read and checked.

## Hard constraints

1. **Every file, every declaration.** Work through the project file by file. Within a file, work
   through every top-level item in source order — module header, module docstring, and each `def`,
   `abbrev`, `theorem`, `lemma`, `class`, `structure`, `instance`, `inductive`, and `notation`.
   Treat each declaration as its own review item against `naming.md`, `style.md`, and `doc.md`
   before moving to the next; don't batch-skim a whole file and call it reviewed.
2. **No semantic changes.** Never change the signature, type, statement, or logical content of a
   `def`, `theorem`, `lemma`, `class`, `structure`, `instance`, or any other declaration. A proof
   must keep proving exactly the same statement it proved before. The only identifier-level
   changes permitted are (a) renaming a declaration to satisfy `naming.md`, and (b) renaming local
   variables, binders, or argument names for clarity or convention compliance. Formatting,
   whitespace, line breaks, and comments/docstrings may of course change freely under the other
   rules below.
3. **Renames must be fully resolved.** Whenever you rename anything — a declaration, a field, a
   notation, a variable referenced elsewhere — search the *entire* project, not just the file
   you're editing, for every use site (other files' proofs and statements, notation built on it,
   docstrings that mention it by name, umbrella/import files, etc.) and update them all
   consistently. A rename isn't done until the whole project elaborates again. If a name is fixed
   by an external interface the declaration implements (e.g. a typeclass field name, or a
   structure/class it extends), leave that name alone — only rename what the project actually
   controls.
4. **Docstrings may be freely rewritten.** Documentation text is not under the no-semantic-change
   constraint: if a docstring is missing, wrong, stale, or just restates the type instead of
   explaining the mathematical content, rewrite it from scratch per `doc.md`. The same goes for
   module docstrings and section comments.

   When writing or rewriting a docstring, favor *explaining* over *describing*. Describing just
   restates the declaration's shape in words — "this takes two arguments and returns a bool," "a
   structure with three fields" — which adds nothing a reader can't already see from the
   signature. Explaining means saying why the declaration exists, what it means mathematically,
   and what's non-obvious about it:
   - For a `def`, if there is a meaningful design choice behind it — why this formulation and not
     an equivalent one, what case a particular clause is handling, why a hypothesis is phrased
     this way — say so. If a definition really is routine, a short, honest description is fine;
     don't invent design rationale that isn't there.
   - For a `theorem`/`lemma` of any real substance, explain the mathematical content and
     significance of the result, not just its logical shape. A reader should come away
     understanding what the statement *means* and why it matters, not just that it "takes
     hypotheses `h1` and `h2` and concludes `C`."
   - Reserve short, purely descriptive docstrings for declarations that really are self-explanatory
     from their name and type; spend the most explanatory effort on a file's main definitions and
     main results.
5. **Zero warnings, zero errors at the end.** Once every file has been edited, the project must
   build with no errors and no warnings anywhere (including linter warnings). This is the exit
   criterion for the whole task, not just for whichever file you're currently in.

## Process

For each file, in turn:

1. Read the whole file first.
2. Check the header, imports, and module docstring against `style.md` and `doc.md`; fix as needed.
3. Walk the declarations in order. For each one:
   - **Naming** — does its name, and the names of its bound variables/arguments, follow
     `naming.md`? If not, rename it and propagate the rename per constraint 3.
   - **Style** — does its formatting follow `style.md` (indentation, line length, spacing around
     `:`/`:=`, placement of `by`, blank-line separation between declarations, no empty lines inside
     a declaration, etc.)? Fix formatting issues.
   - **Documentation** — does it have a docstring, and does that docstring meet `doc.md`'s bar
     (conveys the mathematical meaning, correct delimiters, appropriate Markdown/LaTeX) and explain
     rather than merely describe, per constraint 4? Write or rewrite it as needed.
4. After editing a file, rebuild/re-elaborate the affected files to confirm nothing broke before
   moving to the next file, rather than discovering problems only at the very end.

Where practical, process files in dependency order — files with fewer local imports first — so
that by the time you reach a file, the declarations it depends on already have their final names.

## Notes

- Prefer small, verifiable steps: rename one declaration and its call sites, then verify, rather
  than renaming many things across many files before checking anything compiles.
- When it's unclear whether `naming.md` actually requires a change versus it being a matter of
  taste, make the minimal change that brings the declaration into compliance.
- Keep track of which files are fully reviewed and which remain, so "every file" in constraint 1
  is something you can actually verify at the end, not just something you believe.
- Finish with a full project build to confirm constraint 5 — including checking for any issue that
  only surfaces once multiple files' renames interact (a stale reference, a name collision, etc.).

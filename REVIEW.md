REVIEW instructions
===================

How to review a pull request to this fork. `AGENTS.md` says how to write the code; this file says what a review
looks for. Both the code review and the security review read it.

What failure looks like here
----------------------------

Joern's graph is what every later analysis trusts. A defect that loses or bends the graph silently is worse than a
crash, because nothing downstream can tell. Report these first:

- **The graph silently loses code.** A file, function, declaration, call or argument that the source has and the
  graph no longer holds, with no error and no log line. Look for exceptions caught and dropped, early returns that
  skip a subtree, and `CASTProblem*` nodes passed over.
- **The output is not deterministic.** Iteration over an unordered collection (`HashMap`, `HashSet`, `TrieMap`)
  where the order reaches node creation, ORDER, ARGUMENT_INDEX or full names; anything keyed on identity hash,
  time or thread scheduling.
- **The schema drops a write.** A property set on a node kind that does not declare it, or an unknown property, is
  dropped with no message. Check every new property write against the schema.
- **A per-run switch leaks.** A change that is meant to sit behind a switch but changes the graph with the switch
  off, or a switch read somewhere it was not meant to be.
- **The graph's invariants break.** ORDER unset or out of evaluation order; ARGUMENT_INDEX not unique or not from 1;
  a TYPE_FULL_NAME with no TYPE node; NAME or CODE left stale after a re-binding (data flow matches variables by
  NAME and calls by CODE); duplicate full names.
- **A test proves nothing.** The new test must fail without the change and pass with it. Test code is written from
  scratch, never copied from a real project's source.

Security
--------

Joern parses source it did not write. Treat every input file, compile database entry, define and include path as
untrusted. A change must not add:

- a crash or an uncaught exception on crafted input;
- a hang, unbounded recursion, or time or memory that grows without bound in the input;
- a silent drop of input on crafted input;
- a file read or write outside the paths the run was given.

Out of scope for this review
----------------------------

- Code the pull request did not change. Mark a defect found there as pre-existing, not as the author's.
- Formatting and lint: CI runs `scalafmt` and `scalafix`.
- Generated or downloaded files (`maven_install.json`, astgen binaries).
- Style preferences with no effect on behavior. Report at most three nits.

How to report
-------------

- Start with the count of findings. If there is nothing to fix, say so plainly.
- Give each finding a file and line, and the input or state that triggers it. A guess from a name is not a
  finding.
- Tag each finding Important, Nit or Pre-existing.
- For a bug fix, say whether the change fixes the cause or only the symptom.

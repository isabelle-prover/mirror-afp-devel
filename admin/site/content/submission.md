+++
title = "Entry Submission"
description = "Submit to the Archive of Formal Proofs"

[menu.main]
name = "Submission"
weight = 5
+++

## Submission Guidelines

**The submission must follow the following Isabelle style rules.** For additional guidelines on Isabelle proofs, also see the this [guide](https://proofcraft.org/blog/isabelle-style.html) (feel free to follow all of these; only the below are mandatory). For technical details about the submission process see the [submission form section](#submission-form).

*   No use of the commands `sorry` or `back`.
*   Instantiations must not use Isabelle-generated names such as `xa` — use Isar, the `subgoal` command or `rename_tac` to avoid such names.
*   No use of the command `smt_oracle`.
*   If your theories contain calls to `nitpick`, `quickcheck`, or `nunchaku` those calls must include the `expect` parameter. Alternatively the `expect` parameter must be set globally via, e.g. `nitpick_params`.
*   `apply` scripts should be indented by subgoal as in the Isabelle distribution. If an `apply` command is applied to a state with `n+1` subgoals, it must be indented by `n` spaces relative to the first `apply` in the sequence.
*   Only named lemmas should carry attributes such as `[simp]`.
*   The submission process employs the [Isabelle linter](https://github.com/isabelle-prover/isabelle-linter) that checks for most violations. It will also warn you about other anti-patterns (check the end of your build log).
*   We prefer structured Isar proofs over apply style, but do not mandate them.
*   If there are proof steps that take significant time, i.e. longer than roughly 1 min, please add a short comment to that step, so maintainers will know what to expect.
*   The entry must contain a ROOT file with one session that has the name of the entry. We strongly encourage precisely one session per entry, but exceptions can be made. All sessions must be in chapter AFP, and all theory files of the submission must be contained in at least one session. See also the example [ROOT](https://foss.heptapod.net/isa-afp/afp-2023/-/blob/branch/default/thys/Example-Submission/ROOT) file in the [Example submission](/entries/Example-Submission.html).
*   The submission should run in the current Isabelle/AFP release and produce a PDF document. To test this, you can run the following [Isabelle command on the command line](https://isabelle.in.tum.de/installation.html):
  ```
  <isabelle> build -v -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML" -D <entry dir>
  ```
*   The entry should cite all sources that the theories are based on, for example textbooks or research articles containing informal versions of the proofs.
*   All sessions must have a timeout after which they are assumed to be in a non-terminating state. Timeouts may be no finer than five-minute increments, i.e. must be divisible by 300.

Your submission must contain an abstract to be displayed on the web site – usually this will be the same as the abstract of your proof document in the root.tex file. You can use MathJax formulae in this web site abstract, either inline formulae in the form $a+b$ or \\(a+b\\) or display formulae in the form $$a + b$$ or \\\[a + b\\\]. Other occurrences of these characters must be escaped (e.g. \\$ or \\\\(). Note that MathJax in the title of an entry is _not_ allowed. MathJax supports most basic LaTeX functionality. For details on what parts of LaTeX are supported, see the [MathJax documentation.](https://docs.mathjax.org/en/v2.7-latest/tex.html)

It is possible and encouraged to build on other archive entries in your submission. There is a standardised way to [refer to other AFP entries](/help) in your theories.

It is also encouraged to identify parts of your submission as potentially suitable for inclusion in the Isabelle distribution (i.e. the basic libraries in `isabelle/src/HOL`).  Use the comment field of the submission form to alert the editors to this material, ideally with a suggestion where it could go (e.g. into `List`). You may also want to put it in a separate theory with a descriptive name like `More_List`.

## Submission Form

[Submission form](/webapp/submit)

Your submission will be refereed and you will receive notification as soon as possible. If accepted, you must agree to maintain your archive entry or nominate someone else to maintain it. The Isabelle development team will assist with maintenance, but it does not have the resources to fully maintain the complete archive.

If you have questions regarding your submission, please email [afp-submit@in.tum.de](mailto:afp-submit@in.tum.de). If your submission can only run on the development version of Isabelle or the AFP, notify us after submitting. If you need help with Isabelle, please use the [isabelle-users@cl.cam.ac.uk](mailto:isabelle-users@cl.cam.ac.uk) mailing list. It is always a good idea to [subscribe](https://lists.cam.ac.uk/mailman/listinfo/cl-isabelle-users).

# Updating Entries

## Change

The Archive of Formal Proofs is an online resource and therefore more dynamic than a normal scientific journal. Existing entries can and do evolve and can also be updated significantly by their authors.

This conflicts with the purpose of archiving and preserving entries as they have been submitted and with the purpose of providing a clear and simple interface to readers.

The AFP deals with this by synchronizing such updates with Isabelle releases:

*   The entries released and visible on the main site are always working with the most recent stable Isabelle version and do not change.
*   In the background, the archive maintainers evolve all entries to be up to date with the current Isabelle development version. Authors can contribute changes to this version which is available as a [Heptapod mercurial repository](https://foss.heptapod.net/isa-afp/afp-devel/) or as tar.gz package on the [download page](/download).
*   When a new Isabelle version is released, the above mentioned development version of AFP is frozen and turns into the main version displayed on the front page. Older versions (including the original submission) of all entries are archived and remain accessible.

Significant changes of an entry should be recorded in the metadata of the entry using the keyword "extra-history". The resulting web page should look [something like this](https://www.isa-afp.org/entries/JinjaThreads.html).

## Monotonicity

Updating an entry should be mostly monotone: you add new material, but you do not modify existing material in a major way. Ideally, entries (by other people) that build on yours should not be affected. Otherwise you have to liaise with them first. If you intend to carry out major non-monotone changes, you will need to submit a completely new entry (with a description of how it relates to the old one). This should be required only very rarely: AFP entries should be mature enough not to require major changes to their interface (i.e. the main functions and theorems provided).

Major monotone changes, e.g. adding a new concept rather than more results on existing concepts, may also call for a new entry, but one that builds on the existing one. This depends on how you would like to organize your entries.

## If you are an Author

The above means that if you are an author and would like to provide a new, better version of your AFP entry, you can do so.

To achieve this, you should base your changes on the [mercurial development version](https://foss.heptapod.net/isa-afp/afp-devel/) of your AFP entry and test it against the current [Isabelle development version](https://isabelle.sketis.net/repos/isabelle/).

If you would like to get write access to your entry in the mercurial repository or if you need assistance, please contact the [editors](/about#editors).

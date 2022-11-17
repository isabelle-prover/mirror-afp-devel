---
title: Entry Submission
menu: 
    main:
        name: "Submission"
        weight: 5
---

## Submission Guidelines

**The submission must follow the following Isabelle style rules.** For additional guidelines on Isabelle proofs, also see the this [guide](https://proofcraft.org/blog/isabelle-style.html) (feel free to follow all of these; only the below are mandatory). **Technical details about the submission process and the format of the submission are explained on the submission site.**

*   No use of the commands `sorry` or `back`.
*   Instantiations must not use Isabelle-generated names such as `xa` — use Isar, the `subgoal` command or `rename_tac` to avoid such names.
*   No use of the command `smt_oracle`.
*   If your theories contain calls to `nitpick`, `quickcheck`, or `nunchaku` those calls must include the `expect` parameter. Alternatively the `expect` parameter must be set globally via, e.g. `nitpick_params`.
*   `apply` scripts should be indented by subgoal as in the Isabelle distribution. If an `apply` command is applied to a state with `n+1` subgoals, it must be indented by `n` spaces relative to the first `apply` in the sequence.
*   Only named lemmas should carry attributes such as `[simp]`.
*   We prefer structured Isar proofs over apply style, but do not mandate them.
*   If there are proof steps that take significant time, i.e. longer than roughly 1 min, please add a short comment to that step, so maintainers will know what to expect.
*   The entry must contain a ROOT file with one session that has the name of the entry. We strongly encourage precisely one session per entry, but exceptions can be made. All sessions must be in chapter AFP, and all theory files of the submission must be contained in at least one session. See also the example [ROOT](https://foss.heptapod.net/isa-afp/afp-2020/-/blob/branch/default/thys/Example-Submission/ROOT) file in the [Example submission](/entries/Example-Submission.html).
*   The entry should cite all sources that the theories are based on, for example textbooks or research articles containing informal versions of the proofs.

Your submission must contain an abstract to be displayed on the web site – usually this will be the same as the abstract of your proof document in the root.tex file. You can use LaTeX formulae in this web site abstract, either inline formulae in the form $a+b$ or \\(a+b\\) or display formulae in the form $$a + b$$ or \\\[a + b\\\]. Other occurrences of these characters must be escaped (e.g. \\$ or \\\\(). Note that LaTeX in the title of an entry is _not_ allowed. Most basic LaTeX functionality should be supported. For details on what parts of LaTeX are supported, see the [MathJax documentation.](https://docs.mathjax.org/en/v2.7-latest/tex.html)

It is possible and encouraged to build on other archive entries in your submission. There is a standardised way to [refer to other AFP entries](/help) in your theories.

## Submission Form

[Submission form](/webapp/submit)

Your submission will be refereed and you will receive notification as soon as possible. If accepted, you must agree to maintain your archive entry or nominate someone else to maintain it. The Isabelle development team will assist with maintenance, but it does not have the resources to fully maintain the complete archive.

If you have questions regarding your submission, please email [afp-submit@in.tum.de](mailto:afp-submit@in.tum.de). If you need help with Isabelle, please use the [isabelle-users@cl.cam.ac.uk](mailto:isabelle-users@cl.cam.ac.uk) mailing list. It is always a good idea to [subscribe](https://lists.cam.ac.uk/mailman/listinfo/cl-isabelle-users).

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

To achieve this, you should base your changes on the [mercurial development version](https:/foss.heptapod.net/isa-afp/afp-devel/) of your AFP entry and test it against the current [Isabelle development version](https://isabelle.in.tum.de/devel/).

If you would like to get write access to your entry in the mercurial repository or if you need assistance, please contact the [editors](/about#editors).

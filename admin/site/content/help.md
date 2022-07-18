---
title: Help
menu:
    main:
        name: "Help"
        weight: 4
---

This section focuses on the Archive of Formal Proofs. For help with Isabelle, see the [Isabelle Documentation](https://isabelle.in.tum.de/documentation.html). More resources are listed in the [Isabelle Quick Access Links](https://isabelle.systems).

## Referring to AFP Entries in Isabelle/JEdit

Once you have downloaded the AFP, you can include its articles and theories in your own developments. If you would like to make your work available to others _without_ having to include the AFP articles you depend on, here is how to do it.

From Isabelle2021-1 on, the recommended method for making the whole AFP available to Isabelle is the `isabelle components -u` command.

#### Linux and Mac

Assuming you have downloaded and unzipped the afp to `/home/myself/afp`, run:

    isabelle components -u /home/myself/afp/thys

#### Windows

If the AFP is in `C:\afp`, run the following command in a Cygwin terminal:

    isabelle components -u /cygdrive/c/afp/thys

#### Use

You can now refer to article `ABC` from the AFP in another theory via:

    imports "ABC.Some_ABC_Theory"

This allows you to distribute your material separately from any AFP theories. Users of your distribution also need to install the AFP in the above manner.


## Citing Entries

The following gives an example of the preferred way for citing entries in the AFP:

> M. Jaskelioff and S. Merz, Proving the Correctness of Disk Paxos. _Archive of Formal Proofs_, June 2005, [https://isa-afp.org/entries/DiskPaxos.html](https://isa-afp.org/entries/DiskPaxos.html), Formal proof development.

The bibtex entry for this would be:

```
@article{Jaskelioff-Merz-AFP05,
  author =   {Mauro Jaskelioff and Stephan Merz},
  title =    {Proving the Correctness of Disk Paxos},
  journal =  {Archive of Formal Proofs},
  month =    Jun,
  year =     2005,
  note =     {\url{https://isa-afp.org/entries/DiskPaxos.html}, Formal proof development},
  ISSN =     {2150-914x}
}
```

## Mailing Lists

* isabelle-users@cl.cam.ac.uk provides a forum for Isabelle users to discuss problems, exchange information, and make announcements. Users of official Isabelle releases should subscribe or see the archive.

* isabelle-dev@in.tum.de covers the Isabelle development process, including intermediate repository versions, and administrative issues concerning the website or testing infrastructure. Early adopters of development snapshots or repository versions should subscribe or see the archive (also available at mail-archive.com).

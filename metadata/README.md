Metadata format
===============

We're using the [TOML](https://toml.io/en/v1.0.0) format for metadata files. The data model is
defined in Isabelle/Scala, so larger changes can also be done in a programmatic way.

`entries/<name>.toml`
---------------------

Storage for entry metadata. Format:

```toml 
title = "<text>"
date = <YYYY>-<MM>-<DD>
topics = ["<topic>/<subtopic>/...", "<topic2>/..."]
abstract = """
<multiline text>
"""
license = "<license>"
note = "<text>"
[authors]
[contributors]
[notify]
[history]
[extra]
```

Optional:

- ```toml
  sitegen_ignore = <bool>
  ```
- in `[authors]` and `[contributors]`:
  ```toml
  [authors.<author_id>]
  homepage = "<homepage_id>"
  email = "<email_id>"
  ```
- in `[notify]`:
  ```toml
  <author_id> = "<email_id>"
  ```
- in `[history]`:
  ```toml
  <YYYY>-<MM>-<DD> = "<text>"
  ```
- in `[extra]`:
  ```toml
  extra-<key> = "<heading>: <text>"
  ```

[Example](/metadata/entries/Presburger-Automata.toml)

Details:

- **name**:
  The toml file name (`<short-name>` in this terminology) must correspond to the folder name
  in `thys` directory. This short name is used as entry identifier during the whole process.

- **date**:
  The date is the submission date of the entry.

- **topics**:
  Currently, only three levels of topics and subtopics are allowed, but you may specify as many
  topics as you wish. If multiple topics are specified, the entry will appear under each of them.
  The topic must also appear in the `topics` file (see below).

- **license**:
  Allowed values for the license are "bsd" and "lgpl".

- **authors**
  Authors and affiliations must appear in the `authors` file (see below). For each author, you may
  provide an affiliation as homepage and/or email.

- **contributors**
  Sometimes existing entries get significant contributions from other authors. These authors can be
  listed on a 'contributors' line. A separate change-history entry should indicate what these people
  have contributed.

- **extra**
  If you want to have some additional text fields below the 'Abstract' column, you can use
  the `extra` facility, where `<key>` denotes an identifier (most cases 0, 1, ...) unique for each
  entry. The particular
  `<key>` has no impact on output and is solely used for disambiguating multiple extra fields.

  Example:
  ```toml
  extra-0 = "Warning: Untested..."
  ```

`topics.toml`
-------------
Each topic and its subtopics must go into there. Format:

```toml
["First level topic"]

["First level topic"."Second level topic"]

["First level topic"."Second level topic"."Third level topic"]

["First level topic"."Another second level topic"]
```

Topics without space may omit quotes. Only three levels of indentation are supported currently.


`authors.toml`
--------------
Name, alphanumeric short name, and affiliations for each author. Format:

```toml
[<shortname>]
name = "<name>"
[<name>.emails]
[<name>.homepages]
```

Optional:

- in [<name>.emails]:
  ```toml
  <id> = "<address>"
  ```

- in [<name>.homepages]
  ```toml
  <id> = "<url>"
  ```

Author shortnames are derived from last name and characters from the first name until unique,
e.g. `haslbeck` and `haslbeckm`. Homepage and email ids are usually of form `<shortname>_email` (
or `<shortname>_homepage`) and are incremented for multiples, e.g. `haslbeckm_email1`.


`releases.toml`
---------------
Contains all releases. The youngest release is always ignored, so don't forget to add new releases
when a new Isabelle version is released. Format:

```toml
[name]
<isabelle-release> = <yyyy>-<mm>-<dd>
```

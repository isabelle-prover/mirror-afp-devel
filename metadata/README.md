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
[related]
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
- in `[related]`:
  ```toml
  dois = [ "<doi>", ... ]
  pubs = [ "<text>", ... ] 
  links = [ "<link>", ... ]
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

- **authors**:
  Authors and affiliations must appear in the `authors` file (see below). For each author, you may
  provide an affiliation as homepage and/or email.

- **contributors**:
  Sometimes existing entries get significant contributions from other authors. These authors can be
  listed on a 'contributors' line. A separate change-history entry should indicate what these people
  have contributed.

- **extra**:
  If you want to have some additional text fields below the 'Abstract' column, you can use
  the `extra` facility, where `<key>` denotes an identifier (most cases 0, 1, ...) unique for each
  entry. The particular
  `<key>` has no impact on output and is solely used for disambiguating multiple extra fields.

  Example:
  ```toml
  extra-0 = "Warning: Untested..."
  ```
- **related**:
  A Place for references related to this article, e.g., print publications. DOIs are preferred and
  stored by name only (e.g., `10.1000/182`). If there is none, use a formatted citation (html tags
  are allowed). Hyperlinks are to be listed as plain-text urls.

`topics.toml`
-------------
Each topic and its subtopics must go into there. Format:

```toml
["First level topic"]

["First level topic".classification]
<classification>

["First level topic"."Second level topic"]

["First level topic"."Second level topic".classification]
<classification>

["First level topic"."Second level topic"."Third level topic"]

["First level topic"."Second level topic"."Third level topic".classification]
<classification>

["First level topic"."Another second level topic"]

["First level topic"."Another second level topic".classification]
<classification>
```

Topics without space may omit quotes. Only three levels of indentation are supported currently.

Optional:
- in `[<...>.classification]`:
  - AMS:
    ```toml
    ams.id = "<id>"
    ams.hierarchy = [
      "<descriptions>",
    ]
    ```
  - ACM:
    ```toml
    acm.id = "<id>"
    acm.desc = "<description>"
    ```

Details:
- **classification**:
  A corresponding topic for each AMS and ACM subject classification can be put here.
  - AMS:
    Data comes from [MSC2020 database](https://mathscinet.ams.org/mathscinet/msc/msc2020.html). IDs
    are used without `-XX` or `xx`. In the hierarchy, descriptions are stored for each level (text 
    in `{...}` is omitted), top level first.
  - ACM:
    Data comes from [2012 ACM CCS](https://dl.acm.org/ccs), and the fields can be directly copied 
    from the xml output.


`authors.toml`
--------------
Name, alphanumeric short name, and affiliations for each author. Format:

```toml
[<shortname>]
name = "<name>"
[<shortname>.emails]
[<shortname>.homepages]
```

Optional:
- in `[<shortname>]`:
  ```toml
  orcid = "<id>"
  ```
- in `[<shortname>.emails]`:
  ```toml
  [<shortname>.emails.<id>]
  user = [
    <parts>
  ]
  host = [
    <parts>
  ]
  ```
- in `[<shortname>.homepages]`:
  ```toml
  <id> = "<url>"
  ```

Example:
```toml
[huch]
name = "Fabian Huch"
orcid = "0000-0002-9418-1580"

[huch.emails]

[huch.emails.huch_email]
user = [
  "huch",
]
host = [
  "in",
  "tum",
  "de",
]

[huch.homepages]
huch_homepage = "https://home.in.tum.de/~huch"
```

Details:
- **shortname**:
  Author shortnames are derived from last name and characters from the first name until unique,
  e.g. `haslbeck` and `haslbeckm`. Homepage and email ids are usually of form `<shortname>_email` (
  or `<shortname>_homepage`) and are incremented for multiples, e.g. `haslbeckm_email1`.
- **orcid**:
  Orcid id, identifier only.
- **parts**:
  User and host are represented as lists of parts split by dots. 


`releases.toml`
---------------
Contains all releases. The youngest release is always ignored, so don't forget to add new releases
when a new Isabelle version is released. Format:

```toml
[name]
<isabelle-release> = <yyyy>-<mm>-<dd>
```

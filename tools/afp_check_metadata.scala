/* Author: Fabian Huch, TU Muenchen

Tool to check metadata consistency.
 */
package afp


import isabelle.*

import afp.Metadata.TOML
import isabelle.TOML.{parse, Format, Key, Table}


object AFP_Check_Metadata {

  def diff(t1: Table, t2: Table): List[Key] =
    (t1.domain diff t2.domain).toList ++ t1.table.values.flatMap {
      case (k, tr1) => t2.table.get(k).toList.flatMap(diff(tr1, _))
    }

  def afp_check_metadata(
    strict: Boolean = false,
    reformat: Boolean = false,
    format_all: Boolean = false,
    slow: Boolean = false,
    verbose: Boolean = false,
    progress: Progress = new Progress
  ): Unit = {
    def warn(msg: String): Unit = if (strict) error(msg) else progress.echo_warning(msg)

    progress.echo_if(verbose, "Loading metadata...")
    val afp = AFP_Structure.load()
    val entries = afp.entries.values.toList


    /* TOML encoding/decoding */

    def to_entry(name: String, t: isabelle.TOML.Table): Metadata.Entry =
      TOML.to_entry(name, t, afp.authors, afp.topics, afp.licenses,
        afp.releases.getOrElse(name, Nil))

    def check_toml[A](kind: String, a: A, from: A => Table, to: Table => A): Unit =
      if (to(from(a)) != a) error("Inconsistent toml encode/decode: " + kind)

    progress.echo_if(verbose, "Checking toml conversions...")
    check_toml("authors", afp.authors.values.toList, TOML.from_authors, TOML.to_authors)
    check_toml("topics", Metadata.Topics.root_topics(afp.topics), TOML.from_topics, TOML.to_topics)
    check_toml("licenses", afp.licenses.values.toList, TOML.from_licenses, TOML.to_licenses)
    check_toml("releases", afp.releases.values.flatten.toList, TOML.from_releases, TOML.to_releases)
    entries.foreach(entry =>
      check_toml("entry " + entry.name, entry, TOML.from_entry, to_entry(entry.name, _)))


    /* duplicate ids */

    var seen_ids = Set.empty[String]
    def check_id(id: String): Unit =
      if (seen_ids.contains(id)) error("Duplicate id: " + id) else seen_ids += id

    progress.echo_if(verbose, "Checking for duplicate ids...")

    afp.authors.values.foreach { author =>
      check_id(author.id)
      author.emails.map(_.id).foreach(check_id)
      author.homepages.map(_.id).foreach(check_id)
    }
    afp.topics.values.map(_.id).foreach(check_id)
    afp.licenses.values.map(_.id).foreach(check_id)
    entries.map(_.name).foreach(check_id)


    /* unread fields */

    progress.echo_if(verbose, "Checking for unused fields...")

    def check_unused_toml[A](file: Path, to: Table => A, from: A => Table): Unit = {
      val toml = parse(File.read(file))
      val recoded = from(to(toml))
      val diff_keys = diff(parse(File.read(file)), recoded)
      if (diff_keys.nonEmpty) warn("Unused fields: " + commas_quote(diff_keys))
    }

    check_unused_toml(Metadata.files.authors_toml, TOML.to_authors, TOML.from_authors)
    check_unused_toml(Metadata.files.topics_toml, TOML.to_topics, TOML.from_topics)
    check_unused_toml(Metadata.files.licenses_toml, TOML.to_licenses, TOML.from_licenses)
    check_unused_toml(Metadata.files.releases_toml, TOML.to_releases, TOML.from_releases)
    entries.foreach(entry =>
      check_unused_toml(Metadata.files.entry_toml(entry.name), to_entry(entry.name, _),
        TOML.from_entry))


    /* unused values */

    def warn_unused(name: String, unused: Set[String]): Unit =
      if (unused.nonEmpty) warn("Extra (unused) " + name + ": " + commas_quote(unused.toList))

    progress.echo_if(verbose, "Checking for unused values...")

    val all_affils = entries.flatMap(entry => entry.authors ++ entry.contributors ++ entry.notifies)
    warn_unused("authors", afp.authors.keySet diff all_affils.map(_.author).toSet)

    def author_affil_id(author: Metadata.Author.ID, affil: String): String = author + " " + affil

    val affils = afp.authors.values.flatMap(author =>
      (author.emails.map(_.id) ++ author.homepages.map(_.id)).map(author_affil_id(author.id, _)))
    val used_affils = all_affils.collect {
      case Metadata.Email(author, id, _) => author_affil_id(author, id)
      case Metadata.Homepage(author, id, _) => author_affil_id(author, id)
    }
    warn_unused("affiliations", affils.toSet diff used_affils.toSet)
    val leaf_topics = afp.topics.values.filter(_.sub_topics.isEmpty).map(_.id)
    warn_unused("topics", leaf_topics.toSet diff entries.flatMap(_.topics).map(_.id).toSet)
    warn_unused("licenses", afp.licenses.keySet diff entries.map(_.license.id).toSet)


    /* formatting of commonly patched files */

    if (reformat) {
      Metadata.files.save_authors(afp.authors.values.toList)

      if (format_all) {
        Metadata.files.save_topics(Metadata.Topics.root_topics(afp.topics))
        Metadata.files.save_licenses(afp.licenses.values.toList)
        Metadata.files.save_releases(afp.releases.values.toList.flatten)
        entries.foreach(Metadata.files.save_entry)
      }
    }
    else {
      def check_toml_format(toml: Table, file: Path): Unit = {
        val present = File.read(file)
        val formatted = Format(toml)
        if (present != formatted) progress.echo_warning("Badly formatted toml: " + file)
      }

      progress.echo_if(verbose, "Checking formatting...")
      check_toml_format(TOML.from_authors(afp.authors.values.toList), Metadata.files.authors_toml)

      if (format_all) {
        check_toml_format(TOML.from_topics(afp.topics.values.toList), Metadata.files.topics_toml)
        check_toml_format(TOML.from_licenses(afp.licenses.values.toList),
          Metadata.files.licenses_toml)
        check_toml_format(TOML.from_releases(afp.releases.values.toList.flatten),
          Metadata.files.releases_toml)
        entries.foreach(entry =>
          check_toml_format(TOML.from_entry(entry), Metadata.files.entry_toml(entry.name)))
      }
    }


    /* extra */

    if (slow) {
      progress.echo_if(verbose, "Checking DOIs...")
      entries.flatMap(entry => entry.related).collect { case d: Metadata.DOI => d.formatted() }
    }

    progress.echo_if(verbose, "Checked " + afp.authors.size + " authors with " + affils.size +
      " affiliations, " + afp.topics.size + " topics, " + afp.releases.values.flatten.size + 
      " releases, " + afp.licenses.size + " licenses, and " + entries.size + " entries.")
  }

  val isabelle_tool = Isabelle_Tool("afp_check_metadata", "Checks the AFP metadata files",
    Scala_Project.here,
  { args =>

    var fast = false
    var reformat = false
    var format_all = false
    var strict = false
    var verbose = false

    val getopts = Getopts("""
Usage: isabelle afp_check_metadata [OPTIONS]

  Options are:
    -a    check formatting of all metadata
    -f    fast checks only
    -v    verbose
    -R    reformat metadata files
    -S    strict mode (fail on warnings)

  Check AFP metadata files for consistency.
""",
      "a" -> (_ => format_all = true),
      "f" -> (_ => fast = true),
      "v" -> (_ => verbose = true),
      "R" -> (_ => reformat = true),
      "S" -> (_ => strict = true))

    getopts(args)

    val progress = new Console_Progress()

    afp_check_metadata(strict = strict, reformat = reformat, format_all = format_all, slow = !fast,
      verbose = verbose, progress = progress)
  })
}

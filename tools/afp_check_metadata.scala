/* Author: Fabian Huch, TU Muenchen

Tool to check metadata consistency.
 */
package afp


import isabelle._

import afp.Metadata._


object AFP_Check_Metadata {

  def diff(t1: afp.TOML.T, t2: afp.TOML.T): List[afp.TOML.Key] = {
    (t1.keySet diff t2.keySet).toList ++ t1.flatMap {
      case (k, afp.TOML.T(tr1)) => t2.get(k).map {
        case afp.TOML.T(tr2) => diff (tr1, tr2)
        case _ => Nil
      }.getOrElse(Nil)
      case _ => Nil
    }
  }

  val isabelle_tool = Isabelle_Tool("afp_check_metadata", "Checks the AFP metadata files",
    Scala_Project.here,
  { args =>

    var strict = false

    val getopts = Getopts("""
Usage: isabelle afp_check_metadata [OPTIONS]

  Options are:
    -S           strict mode (fail on warnings)

  Check AFP metadata files for consistency.
""",
      "S" -> (_ => strict = true))

    getopts(args)

    val progress = new Console_Progress()

    val afp_structure = AFP_Structure()

    progress.echo("Checking author file...")
    val authors = afp_structure.load_authors.map(author => author.id -> author).toMap
    def sub_topics(topic: Topic): List[Topic] =
      topic :: topic.sub_topics.flatMap(sub_topics)
    progress.echo("Checking topic file...")
    val root_topics = afp_structure.load_topics
    val topics = Utils.grouped_sorted(root_topics.flatMap(sub_topics), (t: Topic) => t.id)
    progress.echo("Checking license file....")
    val licenses = afp_structure.load_licenses.map(license => license.id -> license).toMap
    progress.echo("Checking release file....")
    val releases = afp_structure.load_releases.groupBy(_.entry)
    progress.echo("Checking entry files...")
    val entries = afp_structure.entries.map(name =>
      afp_structure.load_entry(name, authors, topics, licenses, releases))


    /* TOML encoding/decoding */

    def check_toml[A](kind: String, a: A, from: A => afp.TOML.T, to: afp.TOML.T => A): Unit =
      if (to(from(a)) != a) error("Inconsistent toml encode/decode: " + kind)

    progress.echo("Checking toml conversions...")
    check_toml("authors", authors.values.toList, TOML.from_authors, TOML.to_authors)
    check_toml("topics", root_topics, TOML.from_topics, TOML.to_topics)
    check_toml("licenses", licenses.values.toList, TOML.from_licenses, TOML.to_licenses)
    check_toml("releases", releases.values.flatten.toList, TOML.from_releases, TOML.to_releases)
    entries.foreach(entry => check_toml("entry " + entry.name, entry, TOML.from_entry,
      t => TOML.to_entry(entry.name, t, authors, topics, licenses, releases.getOrElse(entry.name, Nil))))

    def warn(msg: String): Unit = if (strict) error(msg) else progress.echo_warning(msg)


    /* duplicate ids */

    var seen_ids = Set.empty[String]
    def check_id(id: String): Unit =
      if (seen_ids.contains(id)) error("Duplicate id: " + id) else seen_ids += id

    progress.echo("Checking for duplicate ids...")

    authors.values.foreach { author =>
      check_id(author.id)
      author.emails.map(_.id).foreach(check_id)
      author.homepages.map(_.id).foreach(check_id)
    }
    topics.values.map(_.id).foreach(check_id)
    licenses.values.map(_.id).foreach(check_id)
    entries.map(_.name).foreach(check_id)


    /* unused fields */

    progress.echo("Checking for unused fields...")
    def check_unused_toml[A](file: Path, to: afp.TOML.T => A, from: A => afp.TOML.T): Unit = {
      val toml = afp.TOML.parse(File.read(file))
      val recoded = from(to(toml))
      val diff_keys = diff(afp.TOML.parse(File.read(file)), recoded)
      if (diff_keys.nonEmpty) warn("Unused fields: " + commas_quote(diff_keys))
    }

    check_unused_toml(afp_structure.authors_file, TOML.to_authors, TOML.from_authors)
    check_unused_toml(afp_structure.topics_file, TOML.to_topics, TOML.from_topics)
    check_unused_toml(afp_structure.licenses_file, TOML.to_licenses, TOML.from_licenses)
    check_unused_toml(afp_structure.releases_file, TOML.to_releases, TOML.from_releases)
    entries.foreach(entry => check_unused_toml(afp_structure.entry_file(entry.name),
      t => TOML.to_entry(entry.name, t, authors, topics, licenses, releases.getOrElse(entry.name, Nil)),
      TOML.from_entry))


    /* unused values */

    def warn_unused(name: String, unused: Set[String]): Unit =
      if (unused.nonEmpty) warn("Extra (unused) " + name + ": " + commas_quote(unused.toList))

    progress.echo("Checking for unused values...")

    val all_affils = entries.flatMap(entry => entry.authors ++ entry.contributors ++ entry.notifies)
    warn_unused("authors", authors.keySet diff all_affils.map(_.author).toSet)

    def author_affil_id(author: Author.ID, affil: String): String = author + " " + affil

    val affils = authors.values.flatMap(author =>
      (author.emails.map(_.id) ++ author.homepages.map(_.id)).map(author_affil_id(author.id, _)))
    val used_affils = all_affils.collect {
      case Email(author, id, _) => author_affil_id(author, id)
      case Homepage(author, id, _) => author_affil_id(author, id)
    }
    warn_unused("affiliations", affils.toSet diff used_affils.toSet)
    val leaf_topics = topics.values.filter(_.sub_topics.isEmpty).map(_.id)
    warn_unused("topics", leaf_topics.toSet diff entries.flatMap(_.topics).map(_.id).toSet)
    warn_unused("licenses", licenses.keySet diff entries.map(_.license.id).toSet)


    /* extra */

    progress.echo("Checking dois...")
    entries.flatMap(entry => entry.related).collect { case d: DOI => d.formatted() }

    progress.echo("Checked " + authors.size + " authors with " + affils.size + " affiliations, " +
      topics.size + " topics, " + releases.values.flatten.size + " releases, " + licenses.size +
      " licenses, and " + entries.size + " entries.")
  })
}

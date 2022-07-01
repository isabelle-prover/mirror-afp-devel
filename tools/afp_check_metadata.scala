/* Author: Fabian Huch, TU Muenchen

Tool to check metadata consistency.
 */
package afp


import isabelle._

import afp.Metadata._


object AFP_Check_Metadata {
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

    val afp = AFP_Structure()

    progress.echo("Checking author file...")
    val authors = afp.load_authors.map(author => author.id -> author).toMap
    def sub_topics(topic: Topic): List[Topic] =
      topic :: topic.sub_topics.flatMap(sub_topics)
    progress.echo("Checking topic file...")
    val topics =
      Utils.grouped_sorted(afp.load_topics.flatMap(sub_topics), (t: Topic) => t.id)
    progress.echo("Checking license file....")
    val licenses = afp.load_licenses.map(license => license.id -> license).toMap
    progress.echo("Checking release file....")
    val releases = afp.load_releases.groupBy(_.entry)
    progress.echo("Checking entry files...")
    val entries = afp.entries.map(name => afp.load_entry(name, authors, topics, licenses, releases))

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

    progress.echo("Checked " + authors.size + " authors with " + affils.size + " affiliations, " +
      topics.size + " topics, " + licenses.size + " licenses, and " + entries.size + " entries.")
  })
}

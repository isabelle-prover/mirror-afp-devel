package afp


import isabelle._

import afp.Metadata.Author


object AFP_Build_Site
{

  object JSON
  {
    type T = isabelle.JSON.T

    object Object
    {
      type T = isabelle.JSON.Object.T
    }

    def from_authors(authors: List[Author]): T =
      Metadata.TOML.from_authors(authors)

    def from_affiliations(
      affiliations: List[Metadata.Affiliation],
      authors: Map[Metadata.Author.ID, Metadata.Author]): T =
    {
      Utils.group_sorted(affiliations, (a: Metadata.Affiliation) => a.author).toList.map {
        case (author, author_affiliations) =>
          val homepage = author_affiliations.collectFirst { case Metadata.Homepage(_, _, url) => url }
          val email = author_affiliations.collectFirst { case Metadata.Email(_, _, address) => address }

          var res = Utils.the_entry(authors, author).name
          homepage.foreach(url => res = "<a href=" + quote(url) + ">" + res + "</a>")
          email.foreach(address => res += "<a href=" + quote("mailto:" + address) + ">" + "\uD83D\uDCE7</a>")
          res
      }
    }

    def from_change_history(history: Metadata.Change_History): Object.T =
    {
      if (history.isEmpty) {
        Map.empty
      } else {
        Map("Change history" -> history.map {
          case (date, str) => "[" + date.toString + "] " + str
        }.mkString("\n"))
      }
    }

    def from_entry(entry: Metadata.Entry, authors: Map[Metadata.Author.ID, Author]): T =
      isabelle.JSON.Object(
        ("title" -> entry.title) ::
          ("authors" -> from_affiliations(entry.authors, authors)) ::
          (if (entry.contributors.nonEmpty) "contributors" -> from_affiliations(entry.contributors, authors) :: Nil
           else Nil) :::
          ("date" -> entry.date.toString) ::
          ("topics" -> entry.topics.map(_.id)) ::
          ("abstract" -> entry.`abstract`) ::
          ("license" -> entry.license) ::
          (if (entry.releases.nonEmpty)
            "releases" -> entry.releases.map(r => r.isabelle -> r.date.toString).toMap :: Nil
           else Nil) :::
          (if (entry.note.nonEmpty) "note" -> entry.note :: Nil else Nil) :::
          (if (entry.change_history.nonEmpty || entry.extra.nonEmpty)
            "extra" -> (from_change_history(entry.change_history) ++ entry.extra) :: Nil
           else Nil): _*)
  }

  private val gen_dir = Path.explode("$AFP_BASE/web/hugo")

  private def write_gen(file: Path, content: JSON.T): Unit =
  {
    val path = gen_dir + file
    path.dir.file.mkdirs()
    File.write(path, isabelle.JSON.Format(content))
  }

  def afp_build_site(progress: Progress = new Progress()): Unit =
  {
    val metadata_dir = Path.explode("$AFP_BASE") + Path.basic("metadata")


    /* authors */

    progress.echo("Preparing authors...")

    val authors_toml = TOML.parse(File.read(metadata_dir + Path.basic("authors.toml")))
    val authors = Metadata.TOML.to_authors(authors_toml)
    val authors_by_id = Utils.grouped_sorted(authors, (a: Metadata.Author) => a.id)

    write_gen(Path.make(List("data", "authors.json")), JSON.from_authors(authors))


    /* topics */

    progress.echo("Preparing topics...")

    val topics_toml = TOML.parse(File.read(metadata_dir + Path.basic("topics.toml")))
    val topics = Metadata.TOML.to_topics(topics_toml)

    def sub_topics(topic: Metadata.Topic): List[Metadata.Topic] = topic :: topic.sub_topics.flatMap(sub_topics)

    val all_topics_by_id = Utils.grouped_sorted(topics.flatMap(sub_topics), (t: Metadata.Topic) => t.id)


    /* releases */

    progress.echo("Preparing releases...")

    val toml_releases = TOML.parse(File.read(metadata_dir + Path.basic("releases.toml")))
    val all_releases = Metadata.TOML.to_releases(toml_releases).groupBy(_.entry)


    /* entries */

    val Entry = """([a-zA-Z0-9_+-]+)\.toml""".r
    val entries_dir = metadata_dir + Path.basic("entries")
    for (file <- File.read_dir(entries_dir)) {
      val short_name = file match {
        case Entry(short_name) => short_name
        case _ => error("Unrecognized file in entries: " + file)
      }

      progress.echo("Preparing entry " + short_name + "...")

      val content = File.read(entries_dir + Path.basic(file))
      val toml = TOML.parse(content) ++ TOML.T("short_name" -> short_name)
      val releases = all_releases.getOrElse(short_name, error("No releases for entry: " + quote(short_name)))
      val metadata = Metadata.TOML.to_entry(toml, authors_by_id, all_topics_by_id, releases)

      write_gen(Path.make(List("entries", short_name + ".json")), JSON.from_entry(metadata, authors_by_id))
    }
  }

  val isabelle_tool =
    Isabelle_Tool(
      "afp_build_site",
      "generates afp website",
      Scala_Project.here,
      args => {
        val getopts = Getopts(
          """
Usage: isabelle afp_build_site [OPTIONS]

  Options are:
    -B DIR       afp base dir (default "$AFP_BASE")
    -H DIR       afp browser info dir (default "$AFP_BASE/web/browser_info")
    -R DIR       afp release dir (default "$AFP_BASE/web/release")

  Generates the AFP website.
"""
        )

        getopts(args)

        val progress = new Console_Progress()

        afp_build_site(progress)
      }
    )
}
/* Author: Fabian Huch, TU Muenchen

Generation and compilation of SSG project for the AFP website.
 */
package afp


import isabelle._


object AFP_Site_Gen
{
  /* json */

  object JSON
  {
    type T = isabelle.JSON.T

    object Object
    {
      type T = isabelle.JSON.Object.T
    }

    def from_authors(authors: List[Metadata.Author]): T =
    {
      authors.map(author => author.id -> isabelle.JSON.Object(
        "name" -> author.name,
        "emails" -> author.emails.map(_.address),
        "homepages" -> author.homepages.map(_.url))).toMap
    }

    def from_topics(topics: List[Metadata.Topic]): T =
      topics.map(topic => isabelle.JSON.Object(topic.name -> from_topics(topic.sub_topics)))

    def from_affiliations(affiliations: List[Metadata.Affiliation]): Object.T =
    {
      Utils.group_sorted(affiliations, (a: Metadata.Affiliation) => a.author).view.mapValues(author_affiliations =>
      {
        val homepage = author_affiliations.collectFirst { case Metadata.Homepage(_, _, url) => url }
        val email = author_affiliations.collectFirst { case Metadata.Email(_, _, address) => address }

        isabelle.JSON.Object(
          homepage.map(s => List("homepage" -> s)).getOrElse(Nil) :::
            email.map(s => List("email" -> s)).getOrElse(Nil): _*)
      }).toMap
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

    def from_entry(entry: Metadata.Entry): JSON.Object.T =
      isabelle.JSON.Object(
        "title" -> entry.title ::
          "authors" -> entry.authors.map(_.author).distinct ::
          "affiliations" -> from_affiliations(entry.authors ++ entry.contributors) ::
          (if (entry.contributors.nonEmpty) "contributors" -> entry.contributors.map(_.author).distinct :: Nil
          else Nil) :::
          "date" -> entry.date.toString ::
          "topics" -> entry.topics.map(_.id) ::
          "abstract" -> entry.`abstract` ::
          "license" -> entry.license.name ::
          (if (entry.releases.nonEmpty)
            "releases" -> entry.releases.map(r => r.isabelle -> r.date.toString).toMap :: Nil
          else Nil) :::
          (if (entry.note.nonEmpty) "note" -> entry.note :: Nil else Nil) :::
          (if (entry.change_history.nonEmpty || entry.extra.nonEmpty)
            "extra" -> (from_change_history(entry.change_history) ++ entry.extra) :: Nil
          else Nil): _*)

    def from_keywords(keywords: List[String]): T =
      keywords.zipWithIndex.map
        { case (keyword, i) => isabelle.JSON.Object("id" -> i, "keyword" -> keyword) }
  }


  /* keyword extraction */

  private val replacements = List(
    "<[^>]*>".r -> "",
    "[^\\w\\s()'.,;:-]".r -> " ",
    "\\s+".r -> " ")

  def extract_keywords(text: String): List[String] =
  {
    val stripped_text =
      replacements.foldLeft(text) { case (res, (regex, replacement)) => regex.replaceAllIn(res, replacement) }

    val arg = quote(stripped_text.replaceAll("\"", "\\\""))

    val keyword_cmd = "from keywords import *; print_keywords(" + arg + ")"

    Python.run(keyword_cmd).check.out_lines
  }


  /* site generation */

  def afp_site_gen(
    layout: Hugo.Layout,
    status_file: Option[Path],
    afp_structure: AFP_Structure,
    progress: Progress = new Progress()): Unit =
  {
    /* add authors */

    progress.echo("Preparing authors...")

    val authors = afp_structure.load_authors
    val authors_by_id = Utils.grouped_sorted(authors, (a: Metadata.Author) => a.id)

    layout.write_data(Path.basic("authors.json"), JSON.from_authors(authors))


    /* add topics */

    progress.echo("Preparing topics...")

    val topics = afp_structure.load_topics
    def sub_topics(topic: Metadata.Topic): List[Metadata.Topic] = topic :: topic.sub_topics.flatMap(sub_topics)

    val topics_by_id = Utils.grouped_sorted(topics.flatMap(sub_topics), (t: Metadata.Topic) => t.id)

    layout.write_data(Path.basic("topics.json"), JSON.from_topics(topics))


    /* add licenses */

    progress.echo("Preparing licenses...")

    val licenses_by_id = Utils.grouped_sorted(afp_structure.load_licenses,
      (l: Metadata.License) => l.id)

    /* add releases */

    progress.echo("Preparing releases...")

    val releases_by_entry = afp_structure.load_releases.groupBy(_.entry)


    /* extract keywords */

    progress.echo("Extracting keywords...")

    var seen_keywords = Set.empty[String]
    val entry_keywords = afp_structure.entries.map(name =>
    {
      val entry = afp_structure.load_entry(name, authors_by_id, topics_by_id, licenses_by_id,
        releases_by_entry)

      val Keyword = """\('([^']*)', ([^)]*)\)""".r
      val scored_keywords = extract_keywords(entry.`abstract`).map {
        case Keyword(keyword, score) => keyword -> score.toDouble
        case s => error("Could not parse: " + s)
      }
      seen_keywords ++= scored_keywords.map(_._1)

      name -> scored_keywords.filter(_._2 > 1.0).map(_._1)
    }).toMap
    
    seen_keywords = seen_keywords.filter(k => !k.endsWith("s") || !seen_keywords.contains(k.stripSuffix("s")))
    layout.write_static(Path.make(List("data", "keywords.json")), JSON.from_keywords(seen_keywords.toList))

    def get_keywords(name: Metadata.Entry.Name): List[String] =
      entry_keywords(name).filter(seen_keywords.contains).take(8)


    /* add entries and theory listings */

    progress.echo("Preparing entries...")

    val sessions_structure = afp_structure.sessions_structure
    val sessions_deps = Sessions.deps(sessions_structure)

    for (name <- afp_structure.entries) {
      val entry = afp_structure.load_entry(name, authors_by_id, topics_by_id, licenses_by_id,
        releases_by_entry)

      val deps =
        for {
          session <- afp_structure.entry_sessions(name)
          dep <- sessions_structure.imports_graph.imm_preds(session.name)
          if session.name != dep && sessions_structure(dep).groups.contains("AFP")
        } yield dep

      val theories = afp_structure.entry_sessions(name).map { session =>
        val base = sessions_deps(session.name)
        val theories = base.session_theories.map(_.theory_base_name)
        val session_json = isabelle.JSON.Object(
            "title" -> session.name,
            "entry" -> name,
            "url" -> ("/theories/" + session.name.toLowerCase),
            "theories" -> theories)
        layout.write_content(Path.make(List("theories", session.name + ".md")), session_json)
        isabelle.JSON.Object("session" -> session.name, "theories" -> theories)
      }

      val entry_json = JSON.from_entry(entry) ++ isabelle.JSON.Object(
      "dependencies" -> deps.distinct,
      "sessions" -> theories,
      "url" -> ("/entries/" + name + ".html"),
      "keywords" -> get_keywords(name))

      layout.write_content(Path.make(List("entries", name + ".md")), entry_json)
    }


    /* add statistics */

    progress.echo("Preparing statistics...")

    val statistics_cmd = "from statistics import *; add_statistics(" +
      commas_quote(
        List(
          Path.explode("$AFP_BASE").absolute.implode,
          Path.explode("$AFP").absolute.implode,
          layout.data_dir.implode)) +
      ")"
    Python.run(statistics_cmd).check
    (layout.data_dir + Path.basic("statistics.html")).file.delete()


    /* project */

    progress.echo("Preparing project files")

    layout.copy_project()


    /* status */

    status_file match {
      case Some(status_file) =>
        progress.echo("Preparing devel version...")
        val status_json = isabelle.JSON.parse(File.read(status_file))
        layout.write_data(Path.basic("status.json"), status_json)
      case None =>
    }

    progress.echo("Finished sitegen preparation.")
  }


  /* build site */

  def afp_build_site(
    out_dir: Path, layout: Hugo.Layout,
    do_watch: Boolean = false,
    progress: Progress = new Progress()): Unit =
  {
    if (do_watch) {
      Hugo.watch(layout, out_dir, progress).check
    } else {
      progress.echo("Building site...")

      Hugo.build(layout, out_dir).check

      progress.echo("Build in " + (out_dir + Path.basic("index.html")).absolute.implode)
    }
  }


  /* tool wrapper */

  val isabelle_tool = Isabelle_Tool("afp_site_gen", "generates afp website source", Scala_Project.here, args =>
  {
    var base_dir = Path.explode("$AFP_BASE")
    var status_file: Option[Path] = None
    var hugo_dir = base_dir + Path.make(List("web", "hugo"))
    var out_dir: Path = base_dir + Path.make(List("web", "out"))
    var build_only = false
    var devel_mode = false

    val getopts = Getopts("""
Usage: isabelle afp_site_gen [OPTIONS]

  Options are:
    -B DIR       afp base dir (default """" + base_dir.implode + """")
    -D FILE      build status file for devel version
    -H DIR       generated hugo project dir (default """" + hugo_dir.implode + """")
    -O DIR       output dir for build (default """ + out_dir.implode + """)
    -b           build only
    -d           devel mode (overrides hugo dir, builds site in watch mode)

  Generates the AFP website source. HTML files of entries are dynamically loaded.
  Providing a status file will build the development version of the archive.
  Site will be built from generated source if output dir is specified.
""",
      "B:" -> (arg => base_dir = Path.explode(arg)),
      "D:" -> (arg => status_file = Some(Path.explode(arg))),
      "H:" -> (arg => hugo_dir = Path.explode(arg)),
      "O:" -> (arg => out_dir = Path.explode(arg)),
      "b" -> (_ => build_only = true),
      "d" -> (_ => devel_mode = true))

    getopts(args)

    if (devel_mode) hugo_dir = base_dir + Path.make(List("admin", "site"))

    val afp_structure = AFP_Structure(base_dir)
    val layout = Hugo.Layout(hugo_dir)
    val progress = new Console_Progress()

    if (!build_only) {
      progress.echo("Preparing site generation in " + hugo_dir.implode)

      afp_site_gen(layout = layout, status_file = status_file, afp_structure = afp_structure,
        progress = progress)
    }

    afp_build_site(out_dir = out_dir, layout = layout, do_watch = devel_mode, progress = progress)
  })
}
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
      Metadata.TOML.from_authors(authors)

    def from_topics(topics: List[Metadata.Topic]): T =
      Metadata.TOML.from_topics(topics)

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
          "license" -> entry.license ::
          (if (entry.releases.nonEmpty)
            "releases" -> entry.releases.map(r => r.isabelle -> r.date.toString).toMap :: Nil
          else Nil) :::
          (if (entry.note.nonEmpty) "note" -> entry.note :: Nil else Nil) :::
          (if (entry.change_history.nonEmpty || entry.extra.nonEmpty)
            "extra" -> (from_change_history(entry.change_history) ++ entry.extra) :: Nil
          else Nil): _*)
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
    out_dir: Option[Path],
    layout: Hugo.Layout,
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


    /* add releases */

    progress.echo("Preparing releases...")

    val releases_by_entry = afp_structure.load_releases.groupBy(_.entry)


    /* extract keywords */

    progress.echo("Extracting keywords...")

    var seen_keywords = Set.empty[String]
    val entry_keywords = afp_structure.entries.map(name =>
    {
      val entry = afp_structure.load_entry(name, authors_by_id, topics_by_id, releases_by_entry)

      val Keyword = """\('([^']*)', ([^)]*)\)""".r
      val scored_keywords = extract_keywords(entry.`abstract`).map {
        case Keyword(keyword, score) => keyword -> score.toDouble
        case s => error("Could not parse: " + s)
      }
      seen_keywords ++= scored_keywords.map(_._1)

      name -> scored_keywords.filter(_._2 > 1.0).map(_._1)
    }).toMap
    
    seen_keywords = seen_keywords.filter(k => !k.endsWith("s") || !seen_keywords.contains(k.stripSuffix("s")))

    def get_keywords(name: Metadata.Entry.Name): List[String] =
      entry_keywords(name).filter(seen_keywords.contains).take(8)


    /* add entries and theory listings */

    progress.echo("Preparing entries...")

    val sessions_structure = afp_structure.sessions_structure
    val sessions_deps = Sessions.deps(sessions_structure)

    for (name <- afp_structure.entries) {
      val entry = afp_structure.load_entry(name, authors_by_id, topics_by_id, releases_by_entry)

      val deps =
        for {
          session <- afp_structure.entry_sessions(name)
          dep <- sessions_structure.imports_graph.imm_preds(session.name)
          if session.name != dep  && sessions_structure(dep).groups.contains("afp")
        } yield dep

      val topo_theories =
        for {
          session <- afp_structure.entry_sessions(name)
          base = sessions_deps(session.name)
          node <- base.session_theories
        } yield node.theory_base_name

      val entry_json = JSON.from_entry(entry) ++ isabelle.JSON.Object(
          "dependencies" -> deps.distinct,
          "theories" -> topo_theories,
          "aliases" -> List("/entries/" + name + ".html"),
          "keywords" -> get_keywords(name))

      val theories_json = isabelle.JSON.Object(
        "url" -> ("/entries/" + name.toLowerCase + "/theories"),
        "theories" -> topo_theories)

      layout.write_content(Path.make(List("entries", name + ".md")), entry_json)
      layout.write_content(Path.make(List("theories", name + ".md")), theories_json)
    }


    /* add related entries and keywords */

    progress.echo("Preparing related entries...")

    val entries_dir = layout.content_dir + Path.basic("entries")
    val keywords_file = layout.static_dir + Path.make(List("data", "keywords.json"))
    keywords_file.dir.file.mkdirs()
    val related_cmd = "from related import *; add_related(" +
      commas_quote(List(entries_dir.implode, keywords_file.implode)) +
      ")"
    Python.run(related_cmd).check


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


    /* hugo */

    out_dir match {
      case Some(out_dir) =>
        progress.echo("Building site...")

        Hugo.build(layout, out_dir).check

        progress.echo("Finished building site")
      case None =>
        progress.echo("Finished sitegen preparation.")
    }
  }

  val isabelle_tool = Isabelle_Tool("afp_site_gen", "generates afp website source", Scala_Project.here, args =>
  {
    var base_dir = Path.explode("$AFP_BASE")
    var hugo_dir = base_dir + Path.make(List("web", "hugo"))
    var out_dir: Option[Path] = None

    val getopts = Getopts("""
Usage: isabelle afp_site_gen [OPTIONS]

  Options are:
    -B DIR       afp base dir (default """" + base_dir.implode + """")
    -H DIR       generated hugo project dir (default """" + hugo_dir.implode + """")
    -O DIR       output dir (default none)

  Generates the AFP website source. HTML files of entries are dynamically loaded.
  Site will be built from generated source if output dir is specified.
""",
      "B:" -> (arg => base_dir = Path.explode(arg)),
      "H:" -> (arg => hugo_dir = Path.explode(arg)),
      "O:" -> (arg => out_dir = Some(Path.explode(arg))))

    getopts(args)

    val afp_structure = AFP_Structure(base_dir)
    val layout = Hugo.Layout(hugo_dir)
    val progress = new Console_Progress()

    progress.echo("Preparing site generation in " + hugo_dir.implode)

    afp_site_gen(out_dir = out_dir, layout = layout, afp_structure = afp_structure, progress = progress)
  })
}
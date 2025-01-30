/* Author: Fabian Huch, TU Muenchen

Generation and compilation of SSG project for the AFP website.
 */
package afp


import isabelle.*

import afp.Metadata.{Affiliation, Author, ACM, AMS, Classification, DOI, Email, Entry, Formatted, Homepage, Reference, Release, Topic, Unaffiliated}


object AFP_Site_Gen {
  /* cache */

  class Cache(
    dir: Path = Path.explode("$ISABELLE_HOME_USER"),
    progress: Progress = new Progress()
  ) {
    private val cache_file = dir + Path.basic("dois.json")

    private var dois: Map[String, String] = {
      if (cache_file.is_file) {
        val content = File.read(cache_file)
        val json =
          try { isabelle.JSON.parse(content) }
          catch { case ERROR(msg) => error("Could not parse " + cache_file.toString + ": " + msg) }

        json match {
          case m: Map[_, _] if m.keySet.forall(_.isInstanceOf[String]) &&
            m.values.forall(_.isInstanceOf[String]) =>
            m.asInstanceOf[Map[String, String]]
          case _ => error("Could not read dois")
        }
      }
      else {
        progress.echo_warning("No DOI cache found - resolving might take some time")
        Map.empty
      }
    }

    def resolve_doi(doi: DOI): String = synchronized {
      dois.get(doi.identifier) match {
        case Some(value) => value
        case None =>
          val res = doi.formatted()
          dois += (doi.identifier -> res)
          File.write(cache_file, JSON.Format(dois))
          res
      }
    }
  }


  /* json params for hugo templates */

  object JSON_Encode {
    def email(email: Email): JSON.Object.T =
      JSON.Object(
        "user" -> email.user.split('.').toList,
        "host" -> email.host.split('.').toList)

    def authors(authors: List[Author]): JSON.Object.T =
      authors.map(author =>
        author.id -> (JSON.Object(
          "name" -> author.name,
          "emails" -> author.emails.map(email),
          "homepages" -> author.homepages.map(_.url.toString)) ++
          JSON.optional(
            "orcid", author.orcid.map(orcid => JSON.Object(
              "id" -> orcid.identifier,
              "url" -> orcid.url.toString))))).toMap

    def classification(classification: Classification): JSON.Object.T =
      JSON.Object(
        "desc" -> classification.desc,
        "url" -> classification.url.toString,
        "type" -> (classification match {
          case _: ACM => "ACM"
          case _: AMS => "AMS"
        }))

    def topics(elems: List[Topic]): JSON.Object.T =
        JSON.Object(elems.map(topic =>
          topic.name -> (
            JSON.optional("classification",
              proper_list(topic.classification.map(classification))) ++
            JSON.optional("topics", proper_list(topic.sub_topics).map(topics)))): _*)

    def affiliations(affiliations: List[Affiliation]): JSON.Object.T = {
      Utils.group_sorted(affiliations, (a: Affiliation) => a.author).view.mapValues(
      { author_affiliations =>
        val homepage = author_affiliations.collectFirst { case homepage: Homepage => homepage }
        val mail = author_affiliations.collectFirst { case email: Email => email }

        JSON.optional("homepage", homepage.map(_.url.toString)) ++
        JSON.optional("email", mail.map(email))
      }).toMap
    }

    def change_history(entry: (Metadata.Date, String)): JSON.Object.T =
      JSON.Object(
        "date" -> entry._1.toString,
        "value" -> entry._2)

    def release(release: Release): JSON.Object.T =
      JSON.Object(
        "date" -> release.date.toString,
        "isabelle" -> release.isabelle)

    def related(related: Reference, cache: Cache): JSON.T =
      related match {
        case d: DOI =>
          val href = d.url.toString
          cache.resolve_doi(d).replace(href, "<a href=" + quote(href) + ">" + href + "</a>")
        case Formatted(text) => text
      }

    def entry(
      entry: Entry,
      sessions: List[(String, List[String])],
      deps: List[Entry.Name],
      similar: List[Entry.Name],
      cache: Cache
    ): JSON.Object.T = {
      JSON.Object(
        "title" -> entry.title,
        "authors" -> entry.authors.map(_.author).distinct,
        "affiliations" -> affiliations(entry.authors ++ entry.contributors),
        "date" -> entry.date.toString,
        "topics" -> entry.topics.map(_.id),
        "abstract" -> entry.`abstract`,
        "license" -> entry.license.name,
        "dependencies" -> deps,
        "similar" -> similar,
        "sessions" -> sessions.map((session, theories) =>
          JSON.Object(
            "session" -> session,
            "theories" -> theories))) ++
        JSON.optional("contributors", proper_list(entry.contributors.map(_.author).distinct)) ++
        JSON.optional("releases",
          proper_list(entry.releases.sortBy(_.isabelle).reverse.map(release))) ++
        JSON.optional("note", proper_string(entry.note)) ++
        JSON.optional("history",
          proper_list(entry.change_history.toList.sortBy(_._1).reverse.map(change_history))) ++
        JSON.optional("extra", if (entry.extra.isEmpty) None else Some(entry.extra)) ++
        JSON.optional("related", proper_list(entry.related.map(related(_, cache))))
    }

    def keyword(keyword: String): JSON.T = JSON.Object("keyword" -> keyword)

    def statistics(stats: AFP_Stats.Statistics): JSON.Object.T =
      JSON.Object(
        "years" -> stats.years.map(_.rep),
        "num_lemmas" -> stats.cumulated_thms(),
        "num_loc" -> stats.cumulated_loc(),
        "articles_year" -> stats.years.map(_.rep).map(stats.cumulated_entries),
        "loc_years" -> stats.years.map(_.rep).map(stats.cumulated_loc),
        "author_years" -> stats.years.map(_.new_authors),
        "author_years_cumulative" -> stats.years.map(_.rep).map(stats.cumulated_authors),
        "loc_articles" -> stats.years.flatMap(_.entries.map(_.loc)),
        "all_articles" -> stats.years.flatMap(_.entries.map(_.name)),
        "article_years_unique" -> stats.years.filter(_.entries.nonEmpty).flatMap(year =>
          year.rep.toString :: Library.replicate(year.entries.drop(1).length, "")))

    def session(
      entry: Option[Entry.Name],
      theories: List[(String, Path)],
      rss: Boolean
    ): JSON.Object.T = {
      JSON.Object(
        "theories" -> theories.map((name, path) =>
          JSON.Object(
            "name" -> name,
            "path" -> path.implode)),
        "rss" -> rss) ++
      JSON.optional("entry", entry)
    }
  }


  /** site generation **/

  val theme = "afp"


  /* init from sources */

  def init_project(
    hugo: Hugo.Project,
    afp: AFP_Structure = AFP_Structure(),
    symlinks: Boolean = false
  ): Unit = {
    Isabelle_System.make_directory(hugo.dir)
    Isabelle_System.make_directory(hugo.themes_dir)

    val config_file = afp.site_dir + Path.basic("hugo").ext("toml")
    val theme_dir = afp.site_dir + Path.basic("theme")
    val content_dir = afp.site_dir + Path.basic("content")

    if (symlinks) {
      Isabelle_System.symlink(config_file, hugo.dir)
      Isabelle_System.symlink(theme_dir, hugo.themes_dir + Path.basic(theme))

      Isabelle_System.make_directory(hugo.content_dir)
      for (entry <- File.read_dir(content_dir)) {
        Isabelle_System.symlink(
          content_dir + Path.basic(entry),
          hugo.content_dir + Path.basic(entry))
      }
    }
    else {
      Isabelle_System.copy_file(config_file, hugo.dir)
      Isabelle_System.copy_dir(theme_dir, hugo.themes_dir + Path.basic(theme), direct = true)
      Isabelle_System.copy_dir(content_dir, hugo.content_dir, direct = true)
    }
  }


  /** generate hugo project **/

  def afp_hugo_gen(
    hugo: Hugo.Project,
    cache: Cache,
    afp: AFP_Structure = AFP_Structure(),
    status_file: Option[Path] = None,
    symlinks: Boolean = false,
    progress: Progress = new Progress()
  ): Unit = {
    init_project(hugo, afp, symlinks)


    /* load metadata and required data */

    progress.echo("Loading data ...")

    val topics = afp.load_topics
    val licenses = afp.load_licenses
    val releases = afp.load_releases
    val authors = afp.load_authors
    val all_entries = afp.load_entries(authors, topics, licenses, releases).values.toList
    val entries = all_entries.filterNot(_.statistics_ignore)

    val sessions_structure = afp.sessions_structure
    val entry_sessions = all_entries.map(entry => entry -> afp.entry_sessions(entry.name)).toMap
    val session_entry =
      for {
        (entry, sessions) <- entry_sessions
        session <- sessions
      } yield session.name -> entry

    val entry_deps =
      (for (entry <- all_entries)
      yield {
        entry.name ->
          (for {
            session <- entry_sessions(entry)
            dep_session <- sessions_structure.imports_graph.imm_preds(session.name)
            if sessions_structure(dep_session).is_afp
            dep <- session_entry.get(dep_session)
            if dep != entry
          } yield dep.name).distinct
      }).toMap


    /* add topics */

    progress.echo("Preparing topics ...")

    val root_topics = Metadata.Topics.root_topics(topics)

    hugo.write_data(Path.basic("topics").json, JSON.Format(JSON_Encode.topics(root_topics)))


    /* prepare authors and entries */

    progress.echo("Preparing authors ...")

    val seen_affiliations =
      all_entries.flatMap(entry => entry.authors ::: entry.contributors).distinct
    val seen_authors =
      Utils.group_sorted(seen_affiliations.distinct, (a: Affiliation) => a.author).map {
        case (id, affiliations) =>
          val seen_emails = affiliations.collect { case e: Email => e }
          val seen_homepages = affiliations.collect { case h: Homepage => h }
          authors(id).copy(emails = seen_emails, homepages = seen_homepages)
      }

    hugo.write_data(
      Path.basic("authors").json,
      JSON.Format(JSON_Encode.authors(seen_authors.toList)))


    /* extract keywords */

    progress.echo("Extracting keywords ...")

    val entry_keywords =
      (for (entry <- entries) yield {
        val scored_keywords = Rake.extract_keywords(entry.`abstract`)
        entry.name -> scored_keywords.map(_._1)
      }).toMap

    val seen_keywords0 = entry_keywords.values.flatten.toSet
    val seen_keywords =
      seen_keywords0.filter(k => !k.endsWith("s") || !seen_keywords0.contains(k.stripSuffix("s")))

    val keywords_linewise =
      (for (keyword <- seen_keywords.toList.sorted)
       yield JSON.Format(JSON_Encode.keyword(keyword))).mkString("[", ",\n", "]")
    hugo.write_static(Path.explode("data/keywords").json, keywords_linewise)

    def get_keywords(name: Metadata.Entry.Name): List[String] =
      entry_keywords.getOrElse(name, Nil).filter(seen_keywords.contains).take(8)
    def get_words(name: Metadata.Entry.Name): List[String] =
      get_keywords(name).flatMap(space_explode(' ', _))

    val word_counts = entry_keywords
      .values.flatten.flatMap(space_explode(' ', _))
      .groupMapReduce(identity)(_ => 1)(_ + _)


    /* add sessions and theory listings */

    progress.echo("Preparing sessions ...")

    val sessions_deps = Sessions.deps(sessions_structure)
    val browser_info = Browser_Info.context(sessions_structure)

    def theories_of(session_name: String): List[String] =
      sessions_deps(session_name).proper_session_theories.map(_.theory_base_name)

    val distro_sessions =
      (for ((session_name, (info, _)) <- sessions_structure.imports_graph.iterator if !info.is_afp)
      yield session_name -> None).toList

    val afp_sessions =
      for {
        entry <- all_entries
        session <- entry_sessions(entry)
      } yield session.name -> Some(entry.name)

    for ((session_name, entry) <- afp_sessions ::: distro_sessions) {
      val session_dir = browser_info.session_dir(session_name)
      val thy_paths =
        for (thy_name <- theories_of(session_name))
        yield thy_name -> (session_dir + Path.basic(thy_name).html)

      val params = JSON_Encode.session(entry, thy_paths, entry.isDefined)
      val metadata =
        Hugo.Metadata(title = session_name, url = "/sessions/" + session_name.toLowerCase,
          params = params, draft = entry.contains(afp.example_entry))

      hugo.write_content(Hugo.Content("sessions", Path.basic(session_name), metadata))
    }


    /* add entries and theory listings */

    progress.echo("Preparing entries ...")

    all_entries.foreach { entry =>
      val deps = entry_deps(entry.name)

      val keywords = get_keywords(entry.name)
      val words = keywords.flatMap(space_explode(' ', _))
      val sessions =
        afp.entry_sessions(entry.name).map(session => session.name -> theories_of(session.name))

      val similar =
        (for {
          other <- entries
          if other.name != entry.name
          if !deps.contains(other.name) && !entry_deps(other.name).contains(entry.name)
          score = get_words(other.name).intersect(words).map(1.0 / word_counts(_).toDouble).sum
          if score > 1.0
        } yield (other.name, score)).sortBy(_._2).reverse.map(_._1)

      val entry_json = JSON_Encode.entry(entry, sessions, deps, similar, cache)

      val metadata =
        Hugo.Metadata(title = entry.title, url = "/entries/" + entry.name + ".html", date =
          entry.date.toString, keywords = keywords, params = entry_json, draft =
          entry.name == afp.example_entry)

      hugo.write_content(Hugo.Content("entries", Path.basic(entry.name), metadata))
    }


    /* add statistics */

    progress.echo("Preparing statistics ...")

    val statistics_json = JSON_Encode.statistics(AFP_Stats.statistics(sessions_deps, afp, entries))

    hugo.write_data(Path.basic("statistics").json, JSON.Format(statistics_json))


    /* status */

    status_file match {
      case Some(status_file) =>
        progress.echo("Preparing devel version ...")
        val status_json = isabelle.JSON.parse(File.read(status_file))
        hugo.write_data(Path.basic("status").json, JSON.Format(status_json))
      case None =>
    }

    progress.echo("Finished sitegen preparation.")
  }


  /** build site **/

  def afp_build_site(
    out_dir: Path,
    hugo: Hugo.Project,
    server: Boolean = false,
    clean: Boolean = false,
    progress: Progress = new Progress()
  ): Unit = {
    val root = out_dir.absolute

    if (clean) {
      progress.echo("Cleaning output dir...")
      Isabelle_System.rm_tree(root)
      Isabelle_System.make_directory(root)
    }

    progress.echo("Building site...")
    hugo.build(root, draft = true, progress = progress)

    hugo.build(root, server = server, progress = progress)
    if (!server) progress.echo("Build in " + root)
  }


  /** sitegen **/

  def afp_site_gen(
    out_dir: Path,
    read_dir: Option[Path] = None,
    write_dir: Option[Path] = None,
    afp: AFP_Structure = AFP_Structure(),
    status_file: Option[Path] = None,
    clean: Boolean = false,
    devel: Boolean = false,
    progress: Progress = new Progress
  ): Unit =
    Isabelle_System.with_tmp_dir("afp_site_gen") { dir =>
      val cache = new Cache(progress = progress)

      if (read_dir.isEmpty) {
        val dir1 = write_dir.getOrElse(dir).absolute
        if (clean && write_dir.nonEmpty) Isabelle_System.rm_tree(dir1)

        val hugo = Hugo.project(dir1, theme)
        afp_hugo_gen(hugo, cache, afp = afp, status_file = status_file, symlinks = devel,
          progress = progress)
      }

      if (write_dir.isEmpty) {
        val dir1 = read_dir.getOrElse(dir).absolute
        val out_dir1 = (if (devel) dir + Path.basic("out") else out_dir).absolute

        val hugo = Hugo.project(dir1, theme)
        afp_build_site(out_dir1, hugo, server = devel, clean = clean, progress = progress)
      }
    }


  /* tool wrapper */

  val isabelle_tool = Isabelle_Tool("afp_site_gen", "generates afp website source",
    Scala_Project.here,
    { args =>
      var out_dir = AFP.BASE + Path.explode("web")
      var status_file: Option[Path] = None
      var read_dir: Option[Path] = None
      var write_dir: Option[Path] = None
      var clean = false
      var devel = false

      val getopts = Getopts("""
  Usage: isabelle afp_site_gen [OPTIONS]

    Options are:
      -D FILE      build status file for devel version
      -O DIR       output directory for build (default """ + out_dir.implode + """)
      -R DIR       read hugo project from directory (instead of generation)
      -W DIR       write hugo project to specified output directory
      -c           clean up output directories
      -d           devel mode (symlinks sources and serves site instead of build)

    Generates the AFP website. HTML files of entries are dynamically loaded.
    Providing a status file will build the development version of the archive.
  """,
        "D:" -> (arg => status_file = Some(Path.explode(arg))),
        "O:" -> (arg => out_dir = Path.explode(arg)),
        "R:" -> (arg => read_dir = Some(Path.explode(arg))),
        "W:" -> (arg => write_dir = Some(Path.explode(arg))),
        "c" -> (_ => clean = true),
        "d" -> (_ => devel = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      status_file.foreach(path =>
        if (!path.is_file || !path.file.exists()) error("Invalid status file: " + path))

      val afp = AFP_Structure()
      val progress = new Console_Progress()

      afp_site_gen(out_dir, read_dir = read_dir, write_dir = write_dir, afp = afp, status_file =
        status_file, clean = clean, devel = devel, progress = progress)
    })
}
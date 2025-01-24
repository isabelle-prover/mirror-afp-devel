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


  /* json */

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

    def entry(entry: Entry, cache: Cache): JSON.Object.T = {
      JSON.Object(
        "title" -> entry.title,
        "authors" -> entry.authors.map(_.author).distinct,
        "affiliations" -> affiliations(entry.authors ++ entry.contributors),
        "date" -> entry.date.toString,
        "topics" -> entry.topics.map(_.id),
        "abstract" -> entry.`abstract`,
        "license" -> entry.license.name) ++
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
  }


  /* stats */

  def afp_stats(deps: Sessions.Deps, structure: AFP_Structure, entries: List[Entry]): JSON.T = {
    def round(int: Int): Int = Math.round(int.toFloat / 100) * 100

    def nodes(entry: Entry): List[Document.Node.Name] =
      structure.entry_sessions(entry.name).flatMap(session =>
        deps(session.name).proper_session_theories)

    val theorem_commands = List("theorem", "lemma", "corollary", "proposition", "schematic_goal")

    var entry_lines = Map.empty[Entry, Int]
    var entry_lemmas = Map.empty[Entry, Int]
    for {
      entry <- entries
      node <- nodes(entry)
      lines = split_lines(File.read(node.path)).map(_.trim)
    } {
      entry_lines += entry -> (entry_lines.getOrElse(entry, 0) + lines.count(_.nonEmpty))
      entry_lemmas += entry -> (entry_lemmas.getOrElse(entry, 0) +
        lines.count(line => theorem_commands.exists(line.startsWith)))
    }

    val first_year = entries.flatMap(_.releases).map(_.date.getYear).min
    def years(upto: Int): List[Int] = Range.inclusive(first_year, upto).toList

    val current_year = Date.now().rep.getYear
    val all_years = years(current_year)

    // per Isabelle release year
    val by_year = entries.groupBy(_.date.getYear)
    val size_by_year = by_year.view.mapValues(_.length).toMap
    val loc_by_year = by_year.view.mapValues(_.map(entry_lines).sum).toMap
    val authors_by_year = by_year.view.mapValues(_.flatMap(_.authors).map(_.author)).toMap

    val num_lemmas = entries.map(entry_lemmas).sum
    val num_lines = entries.map(entry_lines).sum

    // accumulated
    def total_articles(year: Int): Int =
      years(year).map(size_by_year.getOrElse(_, 0)).sum

    def total_loc(year: Int): Int =
      round(years(year).map(loc_by_year.getOrElse(_, 0)).sum)

    def total_authors(year: Int): Int =
      years(year).flatMap(authors_by_year.getOrElse(_, Nil)).distinct.length

    def fresh_authors(year: Int): Int =
      total_authors(year) - total_authors(year - 1)

    val sorted = entries.sortBy(_.date)

    def map_repetitions(elems: List[String], to: String): List[String] =
      elems.foldLeft(("", List.empty[String])) {
        case((last, acc), s) => (s, acc :+ (if (last == s) to else s))
      }._2

    JSON.Object(
      "years" -> all_years,
      "num_lemmas" -> num_lemmas,
      "num_loc" -> num_lines,
      "articles_year" -> all_years.map(total_articles),
      "loc_years" -> all_years.map(total_loc),
      "author_years" -> all_years.map(fresh_authors),
      "author_years_cumulative" -> all_years.map(total_authors),
      "loc_articles" -> sorted.map(entry_lines),
      "all_articles" -> sorted.map(_.name),
      "article_years_unique" -> map_repetitions(sorted.map(_.date.getYear.toString), ""))
  }


  /** site generation **/

  /* init from sources */

  def init_project(
    hugo: Hugo.Project,
    afp: AFP_Structure = AFP_Structure(),
    symlinks: Boolean = false
  ): Unit = {
    Isabelle_System.make_directory(hugo.dir)

    val config_file = afp.site_dir + Path.basic("config").json
    val themes_dir = afp.site_dir + Path.basic("themes")
    val content_dir = afp.site_dir + Path.basic("content")

    if (symlinks) {
      Isabelle_System.symlink(config_file, hugo.dir)
      Isabelle_System.symlink(themes_dir, hugo.themes_dir)

      Isabelle_System.make_directory(hugo.content_dir)
      for (entry <- File.read_dir(content_dir)) {
        Isabelle_System.symlink(
          content_dir + Path.basic(entry),
          hugo.content_dir + Path.basic(entry))
      }
    }
    else {
      Isabelle_System.copy_file(config_file, hugo.dir)
      Isabelle_System.copy_dir(themes_dir, hugo.themes_dir, direct = true)
      Isabelle_System.copy_dir(content_dir, hugo.content_dir, direct = true)
    }
  }


  /* generate project for hugo */

  def afp_site_gen(
    hugo: Hugo.Project,
    cache: Cache,
    afp: AFP_Structure = AFP_Structure(),
    status_file: Option[Path] = None,
    symlinks: Boolean = false,
    progress: Progress = new Progress()
  ): Unit = {
    init_project(hugo, afp, symlinks)


    /* add topics */

    progress.echo("Preparing topics...")

    val topics = afp.load_topics
    val root_topics = Metadata.Topics.root_topics(topics)

    hugo.write_data(Path.basic("topics").json, JSON.Format(JSON_Encode.topics(root_topics)))


    /* add licenses */

    progress.echo("Preparing licenses...")

    val licenses = afp.load_licenses


    /* add releases */

    progress.echo("Preparing releases...")

    val releases = afp.load_releases


    /* prepare authors and entries */

    progress.echo("Preparing authors...")

    val authors = afp.load_authors

    var seen_affiliations: List[Affiliation] = Nil

    val entries =
      afp.entries.flatMap { name =>
        val entry = afp.load_entry(name, authors, topics, licenses, releases)
        seen_affiliations = seen_affiliations :++ entry.authors ++ entry.contributors
        Some(entry)
      }

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

    progress.echo("Extracting keywords...")

    var seen_keywords = Set.empty[String]
    val entry_keywords =
      entries.filterNot(_.statistics_ignore).map { entry =>
        val scored_keywords = Rake.extract_keywords(entry.`abstract`)
        seen_keywords ++= scored_keywords.map(_._1)

        entry.name -> scored_keywords.map(_._1)
      }.toMap

    seen_keywords =
      seen_keywords.filter(k => !k.endsWith("s") || !seen_keywords.contains(k.stripSuffix("s")))

    val keywords_linewise =
      (for (keyword <- seen_keywords.toList.sorted)
       yield JSON.Format(JSON_Encode.keyword(keyword))).mkString("[", ",\n", "]")
    hugo.write_static(Path.explode("data/keywords").json, keywords_linewise)

    def get_keywords(name: Metadata.Entry.Name): List[String] =
      entry_keywords.getOrElse(name, Nil).filter(seen_keywords.contains).take(8)


    /* add entries and theory listings */

    progress.echo("Preparing entries...")

    val sessions_structure = afp.sessions_structure
    val sessions_deps = Sessions.deps(sessions_structure)
    val browser_info = Browser_Info.context(sessions_structure)

    def theories_of(session_name: String): List[String] =
      sessions_deps(session_name).proper_session_theories.map(_.theory_base_name)

    def write_session_json(
      entry: Option[Metadata.Entry.Name],
      session_name: String,
      rss: Boolean = true
    ): Unit = {
      val params =
        JSON.Object(
          "rss" -> rss,
          "theories" -> theories_of(session_name).map(thy_name => JSON.Object(
            "name" -> thy_name,
            "path" -> (browser_info.session_dir(session_name) + Path.basic(thy_name).html).implode
          ))) ++
          JSON.optional("entry" -> entry)
      val metadata =
        Hugo.Metadata(title = session_name, url = "/sessions/" + session_name.toLowerCase,
          params = params, draft = entry.contains(afp.example_entry))
      hugo.write_content(Hugo.Content("sessions", Path.basic(session_name), metadata))
    }

    val entry_sessions =
      entries.map(entry => entry -> afp.entry_sessions(entry.name)).toMap
    val session_entry = entry_sessions.flatMap((entry, sessions) =>
      sessions.map(session => session.name -> entry))

    entries.foreach { entry =>
      val deps =
        for {
          session <- entry_sessions(entry)
          dep_session <- sessions_structure.imports_graph.imm_preds(session.name)
          if sessions_structure(dep_session).is_afp
          dep <- session_entry.get(dep_session)
          if dep != entry
        } yield dep.name

      val sessions =
        afp.entry_sessions(entry.name).map { session =>
          write_session_json(Some(entry.name), session.name)
          JSON.Object(
            "session" -> session.name,
            "theories" -> theories_of(session.name))
        }

      val entry_json =
        JSON_Encode.entry(entry, cache) ++ JSON.Object(
          "dependencies" -> deps.distinct,
          "sessions" -> sessions)

      val metadata =
        Hugo.Metadata(title = entry.title, url = "/entries/" + entry.name + ".html", date =
          entry.date.toString, keywords = get_keywords(entry.name), params =
          entry_json, draft = entry.name == afp.example_entry)

      hugo.write_content(Hugo.Content("entries", Path.basic(entry.name), metadata))
    }

    for {
      (session_name, (info, _)) <- sessions_structure.imports_graph.iterator
      if !info.is_afp
    } write_session_json(None, session_name, rss = false)


    /* add statistics */

    progress.echo("Preparing statistics...")

    val statistics_json =
      afp_stats(sessions_deps, afp, entries.filterNot(_.statistics_ignore))

    hugo.write_data(Path.basic("statistics").json, JSON.Format(statistics_json))


    /* status */

    status_file match {
      case Some(status_file) =>
        progress.echo("Preparing devel version...")
        val status_json = isabelle.JSON.parse(File.read(status_file))
        hugo.write_data(Path.basic("status").json, JSON.Format(status_json))
      case None =>
    }

    progress.echo("Finished sitegen preparation.")
  }


  /* build site */

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


  /* tool wrapper */

  val isabelle_tool = Isabelle_Tool("afp_site_gen", "generates afp website source",
    Scala_Project.here,
    { args =>
      var out_dir: Path = AFP.BASE + Path.explode("web")
      var status_file: Option[Path] = None
      var clean = false
      var devel_mode = false

      val getopts = Getopts("""
  Usage: isabelle afp_site_gen [OPTIONS]

    Options are:
      -D FILE      build status file for devel version
      -O DIR       output dir for build (default """ + out_dir.implode + """)
      -c           clean up output directory
      -d           devel mode (symlinks sources and builds site in watch mode)

    Generates the AFP website source. HTML files of entries are dynamically loaded.
    Providing a status file will build the development version of the archive.
    Site will be built from generated source if output dir is specified.
  """,
        "D:" -> (arg => status_file = Some(Path.explode(arg))),
        "O:" -> (arg => out_dir = Path.explode(arg)),
        "c" -> (_ => clean = true),
        "d" -> (_ => devel_mode = true))

      getopts(args)

      status_file.foreach(path =>
        if (!path.is_file || !path.file.exists()) error("Invalid status file: " + path))

      val afp = AFP_Structure()
      val progress = new Console_Progress()
      val cache = new Cache(progress = progress)

      Isabelle_System.with_tmp_dir("afp_site_gen") { dir =>
        val hugo = Hugo.project(dir)

        afp_site_gen(hugo, cache, afp = afp, status_file = status_file, symlinks = devel_mode,
          progress = progress)
        afp_build_site(out_dir, hugo, server = devel_mode, clean = clean, progress = progress)
      }
    })
}
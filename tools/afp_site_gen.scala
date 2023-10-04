/* Author: Fabian Huch, TU Muenchen

Generation and compilation of SSG project for the AFP website.
 */
package afp


import isabelle.*

import afp.Metadata.{Affiliation, Author, ACM, AMS, Classification, DOI, Email, Entry, Formatted, Homepage, Reference, Release, Topic, Unaffiliated}


object AFP_Site_Gen {
  /* cache */
  class Cache(layout: Hugo.Layout) {
    private val doi_cache = Path.basic("dois.json")

    private var dois: Map[String, String] = {
      val file = layout.cache_dir + doi_cache

      if (file.file.exists) {
        val content = File.read(file)
        val json =
          try { isabelle.JSON.parse(content) }
          catch { case ERROR(msg) => error("Could not parse " + file.toString + ": " + msg) }
        JSON.to_dois(json)
      } else Map.empty
    }

    def resolve_doi(doi: DOI): String = {
      dois.get(doi.identifier) match {
        case Some(value) => value
        case None =>
          val res = doi.formatted()
          dois += (doi.identifier -> res)
          layout.write_cache(doi_cache, JSON.from_dois(dois))
          res
      }
    }
  }

  /* json */

  object JSON {
    type T = isabelle.JSON.T

    object Object {
      type T = isabelle.JSON.Object.T
      def apply(entries: isabelle.JSON.Object.Entry*): T = isabelle.JSON.Object.apply(entries: _*)
    }

    def opt(k: String, v: String): Object.T = if (v.isEmpty) Object() else Object(k -> v)
    def opt(k: String, v: Option[T]): Object.T = v.map(v => Object(k -> v)).getOrElse(Object())
    def opt[A <: Iterable[_]](k: String, vals: A): Object.T =
      if (vals.isEmpty) Object() else Object(k -> vals)

    def from_dois(dois: Map[String, String]): Object.T = dois
    def to_dois(dois: T): Map[String, String] = dois match {
      case m: Map[_, _] if m.keySet.forall(_.isInstanceOf[String]) &&
          m.values.forall(_.isInstanceOf[String]) =>
        m.asInstanceOf[Map[String, String]]
      case _ => error("Could not read dois")
    }

    def from_email(email: Email): Object.T =
      Object(
        "user" -> email.user.split('.').toList,
        "host" -> email.host.split('.').toList)

    def from_authors(authors: List[Author]): Object.T =
      authors.map(author =>
        author.id -> (Object(
          "name" -> author.name,
          "emails" -> author.emails.map(from_email),
          "homepages" -> author.homepages.map(_.url.toString)) ++
          opt("orcid", author.orcid.map(orcid => Object(
            "id" -> orcid.identifier,
            "url" -> orcid.url.toString))))).toMap

    def from_classification(classification: Classification): Object.T =
      Object(
        "desc" -> classification.desc,
        "url" -> classification.url.toString,
        "type" -> (classification match {
          case _: ACM => "ACM"
          case _: AMS => "AMS"
        }))

    def from_topics(topics: List[Topic]): Object.T =
        Object(topics.map(topic =>
          topic.name -> (
            opt("classification", topic.classification.map(from_classification)) ++
            opt("topics", from_topics(topic.sub_topics)))): _*)

    def from_affiliations(affiliations: List[Affiliation]): Object.T = {
      Utils.group_sorted(affiliations, (a: Affiliation) => a.author).view.mapValues(
      { author_affiliations =>
        val homepage = author_affiliations.collectFirst { case homepage: Homepage => homepage }
        val email = author_affiliations.collectFirst { case email: Email => email }

        Object() ++
          opt("homepage", homepage.map(_.url.toString)) ++
          opt("email", email.map(from_email))
      }).toMap
    }

    def from_change_history(entry: (Metadata.Date, String)): Object.T =
      Object(
        "date" -> entry._1.toString,
        "value" -> entry._2)

    def from_release(release: Release): Object.T =
      Object(
        "date" -> release.date.toString,
        "isabelle" -> release.isabelle)

    def from_related(related: Reference, cache: Cache): T =
      related match {
        case d: DOI =>
          val href = d.url.toString
          cache.resolve_doi(d).replace(href, "<a href=" + quote(href) + ">" + href + "</a>")
        case Formatted(text) => text
      }

    def from_entry(entry: Entry, cache: Cache): Object.T = (
      Object(
        "title" -> entry.title,
        "authors" -> entry.authors.map(_.author).distinct,
        "affiliations" -> from_affiliations(entry.authors ++ entry.contributors),
        "date" -> entry.date.toString,
        "topics" -> entry.topics.map(_.id),
        "abstract" -> entry.`abstract`,
        "license" -> entry.license.name) ++
        opt("contributors", entry.contributors.map(_.author).distinct) ++
        opt("releases", entry.releases.sortBy(_.isabelle).reverse.map(from_release)) ++
        opt("note", entry.note) ++
        opt("history", entry.change_history.toList.sortBy(_._1).reverse.map(from_change_history)) ++
        opt("extra", entry.extra) ++
        opt("related", entry.related.map(from_related(_, cache))))

    def from_keywords(keywords: List[String]): T =
      keywords.sorted.map(keyword => Object("keyword" -> keyword))
  }


  /* stats */

  def afp_stats(deps: Sessions.Deps, structure: AFP_Structure, entries: List[Entry]): JSON.T = {
    def round(int: Int): Int = Math.round(int.toFloat / 100) * 100

    def nodes(entry: Entry): List[Document.Node.Name] =
      structure.entry_sessions(entry.name)
        .flatMap(session => deps(session.name).proper_session_theories)

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

    isabelle.JSON.Object(
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


  /* site generation */

  def afp_site_gen(
    layout: Hugo.Layout,
    status_file: Option[Path],
    afp_structure: AFP_Structure,
    clean: Boolean = false,
    progress: Progress = new Progress()
  ): Unit = {
    /* clean old */

    if (clean) {
      progress.echo("Cleaning up generated files...")
      layout.clean()
    }

    /* add topics */

    progress.echo("Preparing topics...")

    val topics = afp_structure.load_topics
    val topics_by_id =
      Utils.grouped_sorted(topics.flatMap(_.all_topics), (t: Metadata.Topic) => t.id)

    layout.write_data(Path.basic("topics.json"), JSON.from_topics(topics))


    /* add licenses */

    progress.echo("Preparing licenses...")

    val licenses_by_id = Utils.grouped_sorted(afp_structure.load_licenses,
      (l: Metadata.License) => l.id)


    /* add releases */

    progress.echo("Preparing releases...")

    val releases_by_entry = afp_structure.load_releases.groupBy(_.entry)


    /* prepare authors and entries */

    progress.echo("Preparing authors...")

    val full_authors = afp_structure.load_authors
    val authors_by_id = Utils.grouped_sorted(full_authors, (a: Metadata.Author) => a.id)

    var seen_affiliations: List[Affiliation] = Nil

    val entries =
      afp_structure.entries.flatMap { name =>
        val entry = afp_structure.load_entry(name, authors_by_id, topics_by_id, licenses_by_id,
          releases_by_entry)

        seen_affiliations = seen_affiliations :++ entry.authors ++ entry.contributors
        Some(entry)
      }

    val authors =
      Utils.group_sorted(seen_affiliations.distinct, (a: Affiliation) => a.author).map {
        case (id, affiliations) =>
          val seen_emails = affiliations.collect { case e: Email => e }
          val seen_homepages = affiliations.collect { case h: Homepage => h }
          authors_by_id(id).copy(emails = seen_emails, homepages = seen_homepages)
      }

    layout.write_data(Path.basic("authors.json"), JSON.from_authors(authors.toList))

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
    layout.write_static(Path.make(List("data", "keywords.json")),
      JSON.from_keywords(seen_keywords.toList))

    def get_keywords(name: Metadata.Entry.Name): List[String] =
      entry_keywords.getOrElse(name, Nil).filter(seen_keywords.contains).take(8)


    /* add entries and theory listings */

    progress.echo("Preparing entries...")

    val sessions_structure = afp_structure.sessions_structure
    val sessions_deps = Sessions.deps(sessions_structure)
    def theories_of(session_name: String) =
      sessions_deps(session_name).proper_session_theories.map(_.theory_base_name)

    val cache = new Cache(layout)

    val entry_sessions =
      entries.map(entry => entry -> afp_structure.entry_sessions(entry.name)).toMap
    val session_entry = entry_sessions.flatMap((entry, sessions) =>
      sessions.map(session => session.name -> entry)).toMap

    entries.foreach { entry =>
      val deps =
        for {
          session <- entry_sessions(entry)
          dep_session <- sessions_structure.imports_graph.imm_preds(session.name)
          if sessions_structure(dep_session).groups.contains("AFP")
          dep <- session_entry.get(dep_session)
          if dep != entry
        } yield dep.name

      val theories =
        afp_structure.entry_sessions(entry.name).map { session =>
          val theories = theories_of(session.name)
          val session_json =
            isabelle.JSON.Object(
              "title" -> session.name,
              "entry" -> entry.name,
              "url" -> ("/theories/" + session.name.toLowerCase),
              "theories" -> theories)

          layout.write_content(Path.make(List("theories", session.name + ".md")), session_json)
          isabelle.JSON.Object("session" -> session.name, "theories" -> theories)
        }

      val entry_json =
        JSON.from_entry(entry, cache) ++ isabelle.JSON.Object(
          "dependencies" -> deps.distinct,
          "sessions" -> theories,
          "url" -> ("/entries/" + entry.name + ".html"),
          "keywords" -> get_keywords(entry.name))

      layout.write_content(Path.make(List("entries", entry.name + ".md")), entry_json)
    }


    /* add statistics */

    progress.echo("Preparing statistics...")

    val statistics_json =
      afp_stats(sessions_deps, afp_structure, entries.filterNot(_.statistics_ignore))

    layout.write_data(Path.basic("statistics.json"), statistics_json)


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
    clean: Boolean = false,
    progress: Progress = new Progress()
  ): Unit = {
    if (clean) {
      progress.echo("Cleaning output dir...")
      Hugo.clean(out_dir)
    }

    if (do_watch) {
      Hugo.watch(layout, out_dir, progress)
    } else {
      progress.echo("Building site...")
      Hugo.build(layout, out_dir)
      progress.echo("Build in " + (out_dir + Path.basic("index.html")).absolute.implode)
    }
  }


  /* tool wrapper */

  val isabelle_tool = Isabelle_Tool("afp_site_gen", "generates afp website source",
    Scala_Project.here,
    { args =>
      var base_dir = Path.explode("$AFP_BASE")
      var status_file: Option[Path] = None
      var hugo_dir = base_dir + Path.make(List("web", "hugo"))
      var out_dir: Path = base_dir + Path.make(List("web", "out"))
      var build_only = false
      var devel_mode = false
      var fresh = false

      val getopts = Getopts("""
  Usage: isabelle afp_site_gen [OPTIONS]

    Options are:
      -B DIR       afp base dir (default """" + base_dir.implode + """")
      -D FILE      build status file for devel version
      -H DIR       generated hugo project dir (default """" + hugo_dir.implode + """")
      -O DIR       output dir for build (default """ + out_dir.implode + """)
      -b           build only
      -d           devel mode (overrides hugo dir, builds site in watch mode)
      -f           fresh build: clean up existing hugo and build directories

    Generates the AFP website source. HTML files of entries are dynamically loaded.
    Providing a status file will build the development version of the archive.
    Site will be built from generated source if output dir is specified.
  """,
        "B:" -> (arg => base_dir = Path.explode(arg)),
        "D:" -> (arg => status_file = Some(Path.explode(arg))),
        "H:" -> (arg => hugo_dir = Path.explode(arg)),
        "O:" -> (arg => out_dir = Path.explode(arg)),
        "b" -> (_ => build_only = true),
        "d" -> (_ => devel_mode = true),
        "f" -> (_ => fresh = true))

      getopts(args)

      status_file.foreach(path =>
        if (!path.is_file || !path.file.exists()) error("Invalid status file: " + path))

      if (devel_mode) hugo_dir = base_dir + Path.make(List("admin", "site"))

      val afp_structure = AFP_Structure(base_dir)
      val layout = Hugo.Layout(hugo_dir)
      val progress = new Console_Progress()

      if (!build_only) {
        progress.echo("Preparing site generation in " + hugo_dir.implode)

        afp_site_gen(layout = layout, status_file = status_file, afp_structure = afp_structure,
          clean = fresh, progress = progress)
      }

      afp_build_site(out_dir = out_dir, layout = layout, do_watch = devel_mode,
        clean = fresh, progress = progress)
    })
}
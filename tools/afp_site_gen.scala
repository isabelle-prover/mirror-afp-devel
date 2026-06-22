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
    progress: Progress = new Progress
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

  class JSON_Encode(cache: Cache, authors: Metadata.Authors) {
    def topic_id(topic: Topic): String = Word.lowercase(topic.id).replacing(" " -> "-", "/" -> "_")

    def email(email: Email): JSON.Object.T = {
      val user = email.user.split('.').toList
      val host = email.host.split('.').toList
      val bytes = Bytes(JSON.Format(JSON.Object("user" -> user, "host" -> host)))
      JSON.Object(
        "user" -> Library.separate(".", user.map(_.reverse)).reverse,
        "host" -> Library.separate(".", host.map(_.reverse)).reverse,
        "base64" -> Base64.encode(bytes.make_array))
    }

    def author(author: Author, author_entries: List[Entry]): JSON.Object.T =
      JSON.Object(
        "id" -> author.id,
        "name" -> author.name,
        "entries" -> entries(author_entries),
        "emails" -> author.emails.map(email),
        "homepages" -> author.homepages.map(_.url.toString)) ++
        JSON.optional(
          "orcid", author.orcid.map(orcid => JSON.Object(
            "id" -> orcid.identifier,
            "url" -> orcid.url.toString)))

    def classification(classification: Classification): JSON.Object.T =
      JSON.Object(
        "desc" -> classification.desc,
        "url" -> classification.url.toString,
        "type" -> (classification match {
          case _: ACM => "ACM"
          case _: AMS => "AMS"
        }))

    def topic(topic: Topic, is_root: Boolean, topic_entries: List[Entry]): JSON.Object.T =
      JSON.Object(
        "root" -> is_root,
        "name" -> topic.name,
        "count" -> topic_entries.length,
        "entries" -> entries(topic_entries),
        "subtopics" -> topic.sub_topics.map(topic_id).sorted,
        "classification" -> topic.classification.map(classification))

    def affiliations(affiliations: List[Affiliation]): List[JSON.T] = {
      def sep(obj: JSON.Object.T, sep: String): JSON.Object.T = obj ++ JSON.Object("sep" -> sep)

      def affiliation(elem: (Author.ID, List[Affiliation])): JSON.Object.T =
        JSON.Object(
          "author" -> elem._1,
          "name" -> authors(elem._1).name) ++
          JSON.optional("homepage", elem._2.collectFirst { case h: Homepage => h.url.toString }) ++
          JSON.optional("email", elem._2.collectFirst { case e: Email => email(e) })

      Utils.group_sorted(affiliations, (a: Affiliation) => a.author).toList.reverse match {
        case Nil => Nil
        case a :: Nil => List(affiliation(a))
        case a2 :: a1 :: Nil => List(sep(affiliation(a1), " and "), affiliation(a2))
        case a_n :: a_m :: as =>
          as.reverse.map(a => sep(affiliation(a), ", ")) :::
            sep(affiliation(a_m), " and ") :: affiliation(a_n) :: Nil
      }
    }

    def change_history(entry: (Metadata.Date, String)): JSON.Object.T =
      JSON.Object(
        "date" -> entry._1.toString,
        "value" -> entry._2)

    def release(release: Release): JSON.Object.T =
      JSON.Object(
        "date" -> release.date.toString,
        "isabelle" -> release.isabelle)

    def related(related: Reference): JSON.Object.T =
      related match {
        case d: DOI =>
          val href = d.url.toString
          JSON.Object(
            "doi" -> d.identifier,
            "html" ->
              cache.resolve_doi(d).replacing(
                href -> ("<a href=" + quote(href) + ">" + href + "</a>")))
        case Formatted(text) => JSON.Object("html" -> text)
      }

    def entry(
      entry: Entry,
      sessions: List[(String, List[String])],
      used_by: List[Entry.Name],
      deps: List[Entry.Name],
      similar: List[Entry.Name],
    ): JSON.Object.T = {
      JSON.Object(
        "name" -> entry.name,
        "title" -> entry.title,
        "authors" -> affiliations(entry.authors),
        "date" -> entry.date.toString,
        "topics" -> entry.topics.map(topic_id),
        "abstract" -> entry.`abstract`,
        "creation_note" -> entry.creation_note,
        "license" -> entry.license.name,
        "dependencies" -> deps,
        "used_by" -> used_by,
        "similar" -> similar,
        "sessions" -> sessions.map((name, thys) => JSON.Object(
          "name" -> name,
          "theories" -> thys)),
        "contributors" -> affiliations(entry.contributors),
        "releases" -> entry.releases.sortBy(_.isabelle).reverse.map(release),
        "history" -> entry.change_history.toList.sortBy(_._1).reverse.map(change_history),
        "extra" -> entry.extra,
        "related" -> entry.related.map(related)) ++
        JSON.optional("note", proper_string(entry.note))
    }

    def entries(entries: List[Entry]): JSON.T =
      entries.groupBy(_.date.getYear).toList.sortBy(_._1).reverse.map((year, entries) =>
        JSON.Object(
          "year" -> year,
          "entries" -> entries.sortBy(e => (e.date, e.name)).reverse.map(_.name)))

    def keyword(keyword: String): JSON.T = JSON.Object("keyword" -> keyword)

    def statistics(
      stats: AFP_Stats.Statistics,
      num_entries: Int,
      num_authors: Int,
      top_used: List[Metadata.Entry.Name]
    ): JSON.T =
      JSON.Object(
        "num_entries" -> num_entries,
        "num_authors" -> num_authors,
        "top_used" -> top_used,
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

    def theory(
      entry: Option[Entry.Name],
      session: String,
      theory: String,
      path: Path
    ): JSON.Object.T =
      JSON.Object(
        "name" -> theory,
        "session" -> session,
        "path" -> path.implode) ++
        JSON.optional("entry", entry)

    def home(e: List[Metadata.Entry]): JSON.Object.T = JSON.Object("entries" -> entries(e))
  }


  /** site generation **/

  val theme = "afp"


  /* init from sources */

  def init_project(
    hugo: Hugo.Project,
    symlinks: Boolean = false
  ): Unit = {
    Isabelle_System.make_directory(hugo.dir)
    Isabelle_System.make_directory(hugo.themes_dir)

    val config_file = AFP_Structure.site_dir + Path.basic("hugo").ext("toml")
    val theme_dir = AFP_Structure.site_dir + Path.basic("theme")
    val content_dir = AFP_Structure.site_dir + Path.basic("content")

    if (symlinks) {
      Isabelle_System.symlink(config_file, hugo.dir)
      Isabelle_System.symlink(theme_dir, hugo.themes_dir + Path.basic(theme))
    }
    else {
      Isabelle_System.copy_file(config_file, hugo.dir)
      Isabelle_System.copy_dir(theme_dir, hugo.themes_dir + Path.basic(theme), direct = true)
    }
    Isabelle_System.copy_dir(content_dir, hugo.content_dir, direct = true)
  }


  /** generate hugo project **/

  def afp_hugo_gen(
    hugo: Hugo.Project,
    cache: Cache,
    status_file: Option[Path] = None,
    symlinks: Boolean = false,
    progress: Progress = new Progress
  ): Unit = {
    /* initialize project with dynamic Isabelle assets */

    init_project(hugo, symlinks)
    HTML.init_fonts(hugo.static_dir)

    val css_dir = Isabelle_System.make_directory(hugo.static_dir + Path.basic("css"))
    val css = HTML.fonts_css_dir("/") + "\n\n" + File.read(HTML.isabelle_css)
    File.write(css_dir + Path.basic("isabelle.css"), css)


    /* load metadata and required data */

    progress.echo("Loading data ...")

    val afp = AFP_Structure.load()
    val proper_entries = afp.entry_list.filter(_.is_proper).map(_.metadata)

    val json_encode = new JSON_Encode(cache, afp.authors)

    val home_meta =
      Hugo.Metadata(title = "Archive of Formal Proofs", menu = Some(Hugo.Menu_Item("Home", 1)),
        params = json_encode.home(proper_entries))
    hugo.write_content(Hugo.Index("", home_meta))


    /* add topics */

    progress.echo("Preparing topics ...")

    val topics_meta =
      Hugo.Metadata(title = "Topics", menu = Some(Hugo.Menu_Item("Topics", 2)),
        outputs = List("html", "json"))
    hugo.write_content(Hugo.Index("topics", topics_meta))

    for (topic <- afp.topics.values.toList.sortBy(_.id)) {
      val url = "/topics/" + Word.lowercase(topic.id).replacing(" " -> "-")
      val topic_entries = proper_entries.filter(_.topics.contains(topic))
      val is_root = afp.root_topics.contains(topic)
      val params = json_encode.topic(topic, is_root, topic_entries)
      val meta =
        Hugo.Metadata(title = topic.id, url = url, outputs = List("html", "rss"),  params = params)

      val file = Path.basic(json_encode.topic_id(topic))
      hugo.write_content(Hugo.Content("topics", file, meta))
    }


    /* prepare authors and entries */

    progress.echo("Preparing authors ...")

    val seen_affiliations =
      afp.entry_list.map(_.metadata).flatMap(entry => entry.authors ::: entry.contributors).distinct
    val seen_authors =
      Utils.group_sorted(seen_affiliations.distinct, (a: Affiliation) => a.author).map {
        case (id, affiliations) =>
          val seen_emails = affiliations.collect { case e: Email => e }
          val seen_homepages = affiliations.collect { case h: Homepage => h }
          afp.authors(id).copy(emails = seen_emails, homepages = seen_homepages)
      }

    val authors_meta =
      Hugo.Metadata(title = "Authors", description = "Authors of the Archive of Formal Proofs",
        outputs = List("html", "json"))
    hugo.write_content(Hugo.Index("authors", authors_meta))
    for { 
      author <- seen_authors 
      author_entries = proper_entries.filter(_.authors.map(_.author).contains(author.id))
      if author_entries.nonEmpty
    } {
      val meta =
        Hugo.Metadata(title = author.name, outputs = List("html", "rss"),
          params = json_encode.author(author, author_entries))
      hugo.write_content(Hugo.Content("authors", Path.basic(author.id), meta))
    }


    /* extract keywords */

    progress.echo("Extracting keywords ...")

    val entry_keywords =
      (for (entry <- proper_entries) yield {
        val scored_keywords = Rake.extract_keywords(entry.`abstract`)
        entry.name -> scored_keywords.map(_._1)
      }).toMap

    val seen_keywords0 = entry_keywords.values.flatten.toSet
    val seen_keywords =
      seen_keywords0.filter(k => !k.endsWith("s") || !seen_keywords0.contains(k.stripSuffix("s")))

    val keywords_linewise =
      (for (keyword <- seen_keywords.toList.sorted)
       yield JSON.Format(json_encode.keyword(keyword))).mkString("[", ",\n", "]")
    hugo.write_static(Path.explode("data/keywords").json, keywords_linewise)

    def get_keywords(name: Metadata.Entry.Name): List[String] =
      entry_keywords.getOrElse(name, Nil).filter(seen_keywords.contains).take(8).sorted
    def get_words(name: Metadata.Entry.Name): List[String] =
      get_keywords(name).flatMap(space_explode(' ', _))

    val word_counts = entry_keywords
      .values.flatten.flatMap(space_explode(' ', _))
      .groupMapReduce(identity)(_ => 1)(_ + _)


    /* add theory listings */

    progress.echo("Preparing sessions ...")

    val browser_info = Browser_Info.context(afp.sessions_structure)
    val sessions_deps = Sessions.deps(afp.sessions_structure)

    def theory_page(
      num_thy: Int,
      entry: Option[AFP_Structure.Entry],
      session_name: String,
      name: Document.Node.Name
    ): String = {
      val path = browser_info.session_dir(session_name) + Path.basic(name.theory_base_name).html
      val params = json_encode.theory(entry.map(_.name), session_name, name.theory_base_name, path)
      val url = "/" + Path.make(List("thys", session_name, name.theory_base_name)).html.implode

      val  menu = Some(Hugo.Menu_Item(name.theory_base_name, num_thy + 1, menu = session_name))
      val metadata = Hugo.Metadata(title = name.theory, url = url, params = params, menu = menu)
      hugo.write_content(Hugo.Content("thys", Path.basic(name.theory), metadata))
      name.theory
    }

    val afp_deps = afp.sessions_structure.imports_graph.all_preds(afp.sessions.map(_.name))
    for {
      session <- afp_deps
      if !afp.sessions_structure(session).is_afp
      (theory, i) <- sessions_deps(session).proper_session_theories.zipWithIndex
    } theory_page(i, None, session, theory)

    val entry_theories =
      afp.entry_list.map(entry => entry ->
        entry.sessions.map(session => session.name ->
          (for ((theory, i) <- sessions_deps(session.name).proper_session_theories.zipWithIndex)
          yield theory_page(i, Some(entry), session.name, theory)))).toMap


    /* add entries */

    progress.echo("Preparing entries ...")

    hugo.write_content(Hugo.Index("entries", Hugo.Metadata(outputs = List("json"))))

    afp.entry_list.foreach { entry =>
      val used_by =
        afp.uses_graph.imm_succs(entry.name).toList.sortBy(afp.the_entry(_).metadata.date)

      val keywords = get_keywords(entry.name)
      val words = keywords.flatMap(space_explode(' ', _))

      val similar =
        (for {
          other <- afp.entry_list
          if other != entry
          if !afp.uses_graph.imm_preds(entry.name).contains(other.name)
          if !afp.uses_graph.imm_succs(entry.name).contains(other.name)
          score = get_words(other.name).intersect(words).map(1.0 / word_counts(_).toDouble).sum
          if score > 1.0
        } yield (other.name, score)).sortBy(_._2).reverse.map(_._1)

      val deps = afp.uses_graph.imm_preds(entry.name).toList
      val entry_json =
        json_encode.entry(entry.metadata, entry_theories(entry), used_by, deps, similar)

      val metadata =
        Hugo.Metadata(title = entry.metadata.title, url = "/entries/" + entry.name + ".html", date =
          entry.metadata.date.toString, keywords = keywords, params = entry_json)

      hugo.write_content(Hugo.Content("entries", Path.basic(entry.name), metadata))
    }


    /* add statistics */

    progress.echo("Preparing statistics ...")

    val num_used =
      for (entry <- proper_entries) yield entry.name -> afp.uses_graph.imm_succs(entry.name).size

    val top_10 = num_used.sortBy(_.swap).reverse.take(10).map(_._1)
    val num_authors = seen_authors.size
    val num_entries = proper_entries.filterNot(_.statistics_ignore).length
    val stats = AFP_Stats.statistics(sessions_deps, proper_entries)
    val statistics_json = json_encode.statistics(stats, num_entries, num_authors, top_10)

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
    progress: Progress = new Progress
  ): Unit = {
    val root = out_dir.absolute

    if (clean) {
      progress.echo("Cleaning output dir...")
      Isabelle_System.rm_tree(root)
      Isabelle_System.make_directory(root)
    }

    progress.echo("Building site...")

    hugo.build(root, server = server, progress = progress)
    if (!server) progress.echo("Build in " + root)
  }


  /** sitegen **/

  def afp_site_gen(
    out_dir: Path,
    read_dir: Option[Path] = None,
    write_dir: Option[Path] = None,
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
        afp_hugo_gen(hugo, cache, status_file = status_file, symlinks = devel,
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
      var verbose = false

      val getopts = Getopts("""
  Usage: isabelle afp_site_gen [OPTIONS]

    Options are:
      -D FILE      build status file for devel version
      -O DIR       output directory for build (default """ + out_dir.implode + """)
      -R DIR       read hugo project from directory (instead of generation)
      -W DIR       write hugo project to specified output directory
      -c           clean up output directories
      -d           devel mode (symlinks sources and serves site instead of build)
      -v           verbose

    Generates the AFP website. HTML files of entries are dynamically loaded.
    Providing a status file will build the development version of the archive.
  """,
        "D:" -> (arg => status_file = Some(Path.explode(arg))),
        "O:" -> (arg => out_dir = Path.explode(arg)),
        "R:" -> (arg => read_dir = Some(Path.explode(arg))),
        "W:" -> (arg => write_dir = Some(Path.explode(arg))),
        "c" -> (_ => clean = true),
        "d" -> (_ => devel = true),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      status_file.foreach(path =>
        if (!path.is_file || !path.file.exists()) error("Invalid status file: " + path))

      val progress = new Console_Progress(verbose = verbose || devel)

      afp_site_gen(out_dir, read_dir = read_dir, write_dir = write_dir, status_file = status_file,
        clean = clean, devel = devel, progress = progress)
    })
}
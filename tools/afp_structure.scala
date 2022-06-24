/* Author: Fabian Huch, TU Muenchen

AFP Metadata file structure with save and load operations.
 */
package afp


import isabelle._


class AFP_Structure private(val base_dir: Path) {
  /* files */

  val metadata_dir = base_dir + Path.basic("metadata")

  val thys_dir = base_dir + Path.basic("thys")

  private val authors_file = metadata_dir + Path.basic("authors.toml")

  private val releases_file = metadata_dir + Path.basic("releases.toml")
  
  private val licenses_file = metadata_dir + Path.basic("licenses.toml")

  private val topics_file = metadata_dir + Path.basic("topics.toml")

  private val entries_dir = metadata_dir + Path.basic("entries")

  private def entry_file(name: Metadata.Entry.Name): Path = entries_dir + Path.basic(name + ".toml")


  /* load */

  private def load[A](file: Path, parser: afp.TOML.T => A): A = {
    val content = File.read(file)
    val toml =
      try { TOML.parse(content) }
      catch { case ERROR(msg) => error("Could not parse " + file.toString + ": " + msg) }
    parser(toml)
  }

  def load_authors: List[Metadata.Author] = load(authors_file, Metadata.TOML.to_authors)

  def load_releases: List[Metadata.Release] = load(releases_file, Metadata.TOML.to_releases)

  def load_licenses: List[Metadata.License] = load(licenses_file, Metadata.TOML.to_licenses)
  
  def load_topics: List[Metadata.Topic] = load(topics_file, Metadata.TOML.to_topics)

  def load_entry(name: Metadata.Entry.Name,
    authors: Map[Metadata.Author.ID, Metadata.Author],
    topics: Map[Metadata.Topic.ID, Metadata.Topic],
    licenses: Map[Metadata.License.ID, Metadata.License],
    releases: Map[Metadata.Entry.Name, List[Metadata.Release]]
  ): Metadata.Entry = {
    val entry_releases = releases.getOrElse(name, Nil)
    load(entry_file(name), toml =>
      Metadata.TOML.to_entry(toml ++ TOML.T("name" -> name), authors, topics, licenses, entry_releases))
  }

  def load(): List[Metadata.Entry] = {
    val authors = load_authors.map(author => author.id -> author).toMap
    def sub_topics(topic: Metadata.Topic): List[Metadata.Topic] =
      topic :: topic.sub_topics.flatMap(sub_topics)
    val topics = Utils.grouped_sorted(load_topics.flatMap(sub_topics), (t: Metadata.Topic) => t.id)
    val licenses = load_licenses.map(license => license.id -> license).toMap
    val releases = load_releases.groupBy(_.entry)
    entries.map(name => load_entry(name, authors, topics, licenses, releases))
  }


  /* save */

  private def save(file: Path, content: afp.TOML.T): Unit = {
    file.file.mkdirs()
    File.write(file, TOML.Format(content))
  }

  def save_authors(authors: List[Metadata.Author]): Unit =
    save(authors_file, Metadata.TOML.from_authors(authors))

  def save_releases(releases: List[Metadata.Release]): Unit =
    save(releases_file, Metadata.TOML.from_releases(releases))

  def save_topics(topics: List[Metadata.Topic]): Unit =
    save(topics_file, Metadata.TOML.from_topics(topics))

  def save_entry(entry: Metadata.Entry): Unit =
    save(entry_file(entry.name), Metadata.TOML.from_entry(entry))


  /* sessions */

  def entries: List[Metadata.Entry.Name] = {
    val Entry = """([a-zA-Z0-9+_-]+)\.toml""".r
    val file_entries = File.read_dir(entries_dir).map {
      case Entry(name) => name
      case f => error("Unrecognized file in metadata: " + f)
    }
    val session_entries = Sessions.parse_roots(thys_dir + Path.basic("ROOTS"))

    val session_set = session_entries.toSet
    val metadata_set = file_entries.toSet

    if (session_set != metadata_set) {
      val inter = session_set.intersect(metadata_set)
      val session_without_metadata =
        if (session_set.subsetOf(inter)) ""
        else "No metadata for session in ROOTS: " + commas_quote(session_set -- inter)
      val metadata_without_session =
        if (metadata_set.subsetOf(inter)) ""
        else "Metadata entries missing in ROOTS: " + commas_quote(metadata_set -- inter)
      error("Metadata does not match sessions:\n" + session_without_metadata + metadata_without_session)
    } else session_entries
  }

  def sessions_structure: Sessions.Structure =
    Sessions.load_structure(options = Options.init(), select_dirs = List(thys_dir))

  def entry_sessions(name: Metadata.Entry.Name): List[Sessions.Session_Entry] =
    Sessions.parse_root(thys_dir + Path.make(List(name, "ROOT"))).collect { case e: Sessions.Session_Entry => e }

  def hg_id: String = Mercurial.repository(base_dir).id()
}

object AFP_Structure {
  def apply(base_dir: Path = Path.explode("$AFP_BASE")): AFP_Structure = new AFP_Structure(base_dir.absolute)
}

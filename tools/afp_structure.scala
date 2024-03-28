/* Author: Fabian Huch, TU Muenchen

AFP Metadata file structure with save and load operations.
 */
package afp


import isabelle.*


class AFP_Structure private(val base_dir: Path, options: Options) {
  /* files */

  val metadata_dir = base_dir + Path.basic("metadata")
  val thys_dir = AFP.main_dir(base_dir)

  def entry_thy_dir(name: Metadata.Entry.Name): Path = thys_dir + Path.basic(name)

  val authors_file = metadata_dir + Path.basic("authors.toml")
  val releases_file = metadata_dir + Path.basic("releases.toml")
  val licenses_file = metadata_dir + Path.basic("licenses.toml")
  val topics_file = metadata_dir + Path.basic("topics.toml")

  val entries_dir = metadata_dir + Path.basic("entries")

  def entry_file(name: Metadata.Entry.Name): Path = entries_dir + Path.basic(name + ".toml")


  /* load */

  private def load[A](file: Path, parser: isabelle.TOML.Table => A): A = {
    val content = File.read(file)
    val toml =
      try { TOML.parse(content) }
      catch { case ERROR(msg) => error("Could not parse " + file.toString + ": " + msg) }
    parser(toml)
  }

  def load_authors: Metadata.Authors =
    Metadata.Authors(load(authors_file, Metadata.TOML.to_authors))

  def load_releases: Metadata.Releases =
    Metadata.Releases(load(releases_file, Metadata.TOML.to_releases))

  def load_licenses: Metadata.Licenses =
    Metadata.Licenses(load(licenses_file, Metadata.TOML.to_licenses))

  def load_topics: Metadata.Topics = 
    Metadata.Topics(load(topics_file, Metadata.TOML.to_topics))

  def load_entry(
    name: Metadata.Entry.Name,
    authors: Metadata.Authors,
    topics: Metadata.Topics,
    licenses: Metadata.Licenses,
    releases: Metadata.Releases
  ): Metadata.Entry = {
    val entry_releases = releases.getOrElse(name, Nil)
    load(entry_file(name), toml =>
      Metadata.TOML.to_entry(name, toml, authors, topics, licenses, entry_releases))
  }

  def load_entries(
    authors: Metadata.Authors = load_authors,
    topics: Metadata.Topics = load_topics,
    licenses: Metadata.Licenses = load_licenses,
    releases: Metadata.Releases = load_releases
  ): Metadata.Entries =
    Metadata.Entries(entries.map(name => load_entry(name, authors, topics, licenses, releases)))


  /* save */

  private def save(file: Path, content: isabelle.TOML.Table): Unit = {
    file.dir.file.mkdirs()
    File.write(file, TOML.Format(content))
  }

  def save_authors(authors: List[Metadata.Author]): Unit =
    save(authors_file, Metadata.TOML.from_authors(authors))

  def save_releases(releases: List[Metadata.Release]): Unit =
    save(releases_file, Metadata.TOML.from_releases(releases))

  def save_topics(root_topics: List[Metadata.Topic]): Unit =
    save(topics_file, Metadata.TOML.from_topics(root_topics))

  def save_licenses(licenses: List[Metadata.License]): Unit =
    save(licenses_file, Metadata.TOML.from_licenses(licenses))

  def save_entry(entry: Metadata.Entry): Unit =
    save(entry_file(entry.name), Metadata.TOML.from_entry(entry))


  /* sessions */

  def entries_unchecked: List[Metadata.Entry.Name] = {
    val Entry = """([a-zA-Z0-9+_-]+)\.toml""".r
    File.read_dir(entries_dir).map {
      case Entry(name) => name
      case f => error("Unrecognized file in metadata: " + f)
    }
  }

  def entries: List[Metadata.Entry.Name] = {
    val session_entries = Sessions.parse_roots(thys_dir + Sessions.ROOTS)

    val session_set = session_entries.toSet
    val metadata_set = entries_unchecked.toSet

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
    Sessions.load_structure(options, select_dirs = List(thys_dir))

  def entry_sessions(name: Metadata.Entry.Name): List[Sessions.Session_Entry] =
    Sessions.parse_root_entries(thys_dir + Path.basic(name) + Sessions.ROOT)

  def hg_id: String = Mercurial.repository(base_dir).id()
}

object AFP_Structure {
  def apply(base_dir: Path = AFP.BASE, options: Options = Options.init0()): AFP_Structure =
    new AFP_Structure(base_dir.absolute, options)
}

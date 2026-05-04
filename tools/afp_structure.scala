/* Author: Fabian Huch, TU Muenchen

General AFP structure.
 */
package afp

import scala.language.unsafeNulls

import isabelle.*


object AFP_Structure {
  val thys_dir = AFP.main_dir()
  val site_dir = AFP.BASE + Path.explode("admin/site")

  def entry_dir(name: String): Path = thys_dir + Path.basic(name)
  def entry_sessions(name: String): List[Sessions.Session_Entry] =
    Sessions.parse_root_entries(entry_dir(name) + Sessions.ROOT)

  class Entry private[AFP_Structure](
    val name: String,
    val metadata: Metadata.Entry,
    val sessions: List[Sessions.Info],
  ) {
    override def toString: String = name

    def entry_dir: Path = AFP_Structure.entry_dir(name)
    def is_proper: Boolean = !metadata.statistics_ignore

    override def hashCode(): Int = name.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Entry => other.name == name
        case _ => false
      }
  }

  def roots_entries: List[String] = Sessions.parse_roots(thys_dir + Sessions.ROOTS)

  def sessions(options: Options = Options.init()): Sessions.Structure =
    Sessions.load_structure(options, select_dirs = List(thys_dir))

  def entry_names: List[String] = {
    val session_entries = roots_entries

    val session_set = session_entries.toSet
    val metadata_set = Metadata.files.entries.toSet

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


  /* cumulative information */

  def load(): AFP = {
    val authors = Metadata.files.load_authors()
    val topics = Metadata.files.load_topics()
    val licenses = Metadata.files.load_licenses()
    val releases = Metadata.files.load_releases()
    val entries =
      Metadata.Entries(entry_names.map(name =>
        Metadata.files.load_entry(name, authors, topics, licenses, releases)))

    val sessions_structure = sessions()

    def load_entry(name: String): Entry = {
      val sessions = for (session <- entry_sessions(name)) yield sessions_structure(session.name)
      Entry(name, entries(name), sessions)
    }

    val entry_list = entry_names.map(load_entry)

    val session_entry = entry_list.flatMap(entry => entry.sessions.map(_.name -> entry)).toMap
    def entry_deps(entry: Entry): List[Entry] =
      (for {
        session <- entry.sessions
        dep <- session.deps
        dep_entry <- session_entry.get(dep)
        if dep_entry != entry
      } yield dep_entry).distinct

    val uses_graph =
      Graph.make(
        entry_list.map(entry => ((entry.name, entry), entry_deps(entry).map(_.name))),
        converse = true)

    new AFP(authors, topics, licenses, releases, entries, entry_list, uses_graph,
      sessions_structure)
  }

  class AFP private[AFP_Structure](
    val authors: Metadata.Authors,
    val topics: Metadata.Topics,
    val licenses: Metadata.Licenses,
    val releases: Metadata.Releases,
    val entries: Metadata.Entries,
    val entry_list: List[Entry],
    val uses_graph: Graph[String, Entry],
    val sessions_structure: Sessions.Structure
  ) {
    override def toString: String = "AFP(" + AFP.BASE.absolute + ")"

    def root_topics: List[Metadata.Topic] = Metadata.Topics.root_topics(topics)

    def the_entry(name: String): Entry =
      entry_list.find(_.name == name) getOrElse error("No such entry: " + name)

    def sessions: List[Sessions.Info] = entry_list.flatMap(_.sessions)
    def perhaps_session_entry(session: String): Option[Entry] =
      entry_list.find(_.sessions.exists(_.name == session))
  }
}

/* Author: Fabian Huch, TU Muenchen

General AFP structure.
 */
package afp


import isabelle.*


object AFP_Structure {
  val thys_dir = AFP.main_dir()
  val site_dir = AFP.BASE + Path.explode("admin/site")

  def entry_sessions(name: String): List[Sessions.Session_Entry] =
    Sessions.parse_root_entries(thys_dir + Path.basic(name) + Sessions.ROOT)

  def sessions_structure(options: Options = Options.init()): Sessions.Structure =
    Sessions.load_structure(options, select_dirs = List(thys_dir))

  def entries: List[Metadata.Entry.Name] = {
    val session_entries = Sessions.parse_roots(thys_dir + Sessions.ROOTS)

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

  def load_entries(
    authors: Metadata.Authors = Metadata.files.load_authors,
    topics: Metadata.Topics = Metadata.files.load_topics,
    licenses: Metadata.Licenses = Metadata.files.load_licenses,
    releases: Metadata.Releases = Metadata.files.load_releases
  ): Metadata.Entries =
    Metadata.Entries(entries.map(name =>
      Metadata.files.load_entry(name, authors, topics, licenses, releases)))
}

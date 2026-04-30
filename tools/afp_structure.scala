/* Author: Fabian Huch, TU Muenchen

General AFP structure.
 */
package afp


import isabelle.*


object AFP_Structure {
  val thys_dir = AFP.main_dir()
  val site_dir = AFP.BASE + Path.explode("admin/site")

  def entry_dir(name: String): Path = thys_dir + Path.basic(name)
  def entry_sessions(name: String): List[Sessions.Session_Entry] =
    Sessions.parse_root_entries(entry_dir(name) + Sessions.ROOT)

  def roots_entries: List[String] = Sessions.parse_roots(thys_dir + Sessions.ROOTS)

  def sessions_structure(options: Options = Options.init()): Sessions.Structure =
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

    new AFP(authors, topics, licenses, releases, entries, sessions_structure())
  }

  class AFP private[AFP_Structure](
    val authors: Metadata.Authors,
    val topics: Metadata.Topics,
    val licenses: Metadata.Licenses,
    val releases: Metadata.Releases,
    val entries: Metadata.Entries,
    val sessions_structure: Sessions.Structure)
}

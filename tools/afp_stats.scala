/* Author: Fabian Huch, TU Muenchen

Statistics over the AFP.

NB: 'per year' statistics for lines of code and thms are approximated
from current measurements and entry history.
 */

package afp


import isabelle._


object AFP_Stats {
  case class Entry(name: Metadata.Entry.Name, loc: Int, thms: Int)
  case class Year(rep: Int, new_authors: Int = 0, entries: List[Entry] = Nil) {
    def new_loc: Int = entries.map(_.loc).sum
    def new_thms: Int = entries.map(_.thms).sum
    def new_entries = entries.length
  }

  case class Statistics(years: List[Year]) {
    def cumulated(year: Int = Int.MaxValue): List[Year] = years.takeWhile(_.rep <= year)
    def cumulated_loc(year: Int = Int.MaxValue): Int = cumulated(year).map(_.new_loc).sum
    def cumulated_thms(year: Int = Int.MaxValue): Int = cumulated(year).map(_.new_thms).sum
    def cumulated_authors(year: Int = Int.MaxValue): Int = cumulated(year).map(_.new_authors).sum
    def cumulated_entries(year: Int = Int.MaxValue): Int = cumulated(year).map(_.new_entries).sum
  }

  val theorem_commands = List("theorem", "lemma", "corollary", "proposition", "schematic_goal")

  def entry_stats(deps: Sessions.Deps, afp: AFP_Structure, entry: Metadata.Entry): Entry = {
    val (loc, thms) =
      (for {
        session <- afp.entry_sessions(entry.name)
        node <- deps(session.name).proper_session_theories
        lines = split_lines(File.read(node.path)).map(_.trim)
      } yield {
        (lines.count(_.nonEmpty), lines.count(line => theorem_commands.exists(line.startsWith)))
      }).unzip

    Entry(entry.name, loc.sum, thms.sum)
  }

  def statistics(
    deps: Sessions.Deps,
    afp: AFP_Structure,
    entries: List[Metadata.Entry]
  ): Statistics = {
    val first_year = entries.flatMap(_.releases).map(_.date.getYear).min
    def years(upto: Int): List[Int] = Range.inclusive(first_year, upto).toList

    val by_year = entries.groupBy(_.date.getYear).withDefault(Nil)
    val authors_by_year =
      by_year.view.mapValues(_.flatMap(_.authors).map(_.author)).toMap.withDefault(Nil)

    def total_authors(year: Int): Int = years(year).flatMap(authors_by_year(_)).distinct.length
    def new_authors(year: Int): Int = total_authors(year) - total_authors(year - 1)

    val all_years =
      for (year <- years(entries.map(_.date.getYear).max)) yield {
        val entries =
          for (entry <- by_year(year).sortBy(_.date)) yield entry_stats(deps, afp, entry)
        Year(year, new_authors(year), entries)
      }

    Statistics(all_years)
  }
}
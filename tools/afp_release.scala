/* Author: Fabian Huch, TU Muenchen

Tooling to manage AFP releases.
 */
package afp


import isabelle.*

import java.time.LocalDate


object AFP_Release {

  def afp_import_releases(
    user: String,
    host: String,
    releases_dir: Path,
    base_dir: Path,
    options: Options
  ): Unit = {
    val Release_Tar = """afp-(.+)-(\d{4}-\d{2}-\d{2})\.tar\.gz""".r

    val afp_structure = AFP_Structure(base_dir)

    val isabelle_releases =
      split_lines(File.read(afp_structure.metadata_dir + Path.basic("release-dates")))
    val Isa_Release = """(.+) = (.+)""".r
    val release_dates = isabelle_releases.filterNot(_.isBlank).map {
      case Isa_Release(isabelle_version, date) => LocalDate.parse(date) -> isabelle_version
      case line => error("Could not parse: " + quote(line))
    }

    using(SSH.open_session(options, host, user = user)) { ssh =>
      val releases = ssh.read_dir(releases_dir).collect {
        case Release_Tar(entry, date_str) =>
          val date = LocalDate.parse(date_str)
          release_dates.findLast { case (isa_date, _) => !isa_date.isAfter(date) } match {
            case Some(_, isabelle) => Metadata.Release(entry, date, isabelle)
            case None => error("No Isabelle version found for " + date_str)
          }
      }

      afp_structure.save_releases(releases)
    }
  }

  def afp_release(date: LocalDate, isabelle: Metadata.Isabelle.Version, base_dir: Path): Unit = {
    def add_release(entry: Metadata.Entry): Metadata.Entry =
      entry.copy(releases = entry.releases :+ Metadata.Release(entry.name, date, isabelle))

    val afp_structure = AFP_Structure(base_dir)

    val releases = afp_structure.load().values.toList.map(add_release).flatMap(_.releases)

    afp_structure.save_releases(releases)
  }

  val isabelle_tool = Isabelle_Tool("afp_release", "Create an AFP release",
    Scala_Project.here,
    { args =>

      var isabelle = Isabelle_System.isabelle_identifier().getOrElse("")
      var date = LocalDate.now()
      var options = Options.init()
      var releases: String = "afpweb@isa-afp.org:/srv/afp/release"
      var import_releases = false

      val getopts = Getopts("""
Usage: isabelle afp_release [OPTIONS]

  Options are:
    -i ID            Isabelle id (default: """ + quote(isabelle) + """)
    -d DATE          release date (default: """ + quote(date.toString) + """)
    -o OPTION        override Isabelle system OPTION (via NAME=VAL or NAME)
    -r REMOTE        remote location of releases (default: """ + quote(releases) + """)"
    -I               import releases from directory instead

  Register releases for old Isabelle version (when creating a new AFP release),
  or import all releases from release dir.
""",
        "i:" -> (arg => isabelle = arg),
        "d:" -> (arg => date = LocalDate.parse(arg)),
        "o:" -> (arg => options = options + arg),
        "r:" -> (arg => releases = arg),
        "I" -> (_ => import_releases = true))

      getopts(args)

      val base_dir = Path.explode("$AFP_BASE")

      if (import_releases) {
        val Remote = """([^@]+)@([^:]+):(.*)""".r
        releases match {
          case Remote(user, host, dir) =>
            afp_import_releases(user = user, host = host, releases_dir = Path.explode(dir),
              base_dir = base_dir, options = options)
          case _ => error("Invalid remote: " + quote(releases))
        }
      }
      else {
        if (isabelle.isEmpty) getopts.usage()
        afp_release(date, isabelle, base_dir)
      }
    })
}

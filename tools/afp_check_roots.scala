/* Author: Lars Hupel and Fabian Huch, TU Muenchen


 */
package afp


import isabelle.{Path, *}

import java.io.File as JFile


object AFP_Check_Roots {
  def print_good(string: String): Unit =
    println(Console.BOLD + Console.GREEN + string + Console.RESET)

  def print_bad(string: String): Unit =
    println(Console.BOLD + Console.RED + string + Console.RESET)

  case class Check[T](
    name: String,
    failure_msg: String,
    run: (Sessions.Structure, List[String], AFP_Structure) => List[T],
    failure_format: T => String = (t: T) => t.toString
  ) {
    override def toString: String = name

    def apply(
      structure: Sessions.Structure,
      sessions: List[String],
      afp_structure: AFP_Structure
    ): Boolean =
      run(structure, sessions, afp_structure) match {
        case Nil => true
        case offenders =>
          print_bad(failure_msg)
          offenders.foreach(offender => println("  " + failure_format(offender)))
          false
      }
  }

  val known_checks: List[Check[_]] =
    List(
      Check[String]("check_timeout",
        "The following entries contain sessions without timeouts or with timeouts not divisible by 300:",
        (structure, sessions, _) =>
          sessions.flatMap { session_name =>
            val info = structure(session_name)
            val timeout = info.options.real("timeout")
            if (timeout == 0 || timeout % 300 != 0) Some(session_name) else None
          }),
      Check[String]("check_chapter", "The following entries are not in the AFP chapter:",
        (structure, sessions, _) =>
          sessions.flatMap { session_name =>
            val info = structure(session_name)
            if (info.chapter != "AFP") Some(session_name) else None
          }),
      Check[(String, List[String])]("check_groups", "The following sessions have wrong groups:",
        (structure, sessions, _) =>
          sessions.flatMap { session_name =>
            val info = structure(session_name)
            if (!info.groups.toSet.subsetOf(AFP.groups.keySet + "AFP") ||
              !info.groups.contains("AFP"))
              Some((session_name, info.groups))
            else None
          },
        t => t._1 + "{" + t._2.mkString(", ") + "}"),
      Check[String]("check_presence",
        "The following entries do not contain a corresponding session on top level:",
        (structure, sessions, afp_structure) => {
          val entries = afp_structure.entries_unchecked

          entries.flatMap { entry_name =>
            if (!sessions.contains(entry_name) ||
              structure(entry_name).dir.base.implode != entry_name)
              Some(entry_name)
            else None
          }
        }),
      Check[(String, List[Path])]("check_unused_thys",
        "The following sessions contain unused theories:",
        (structure, sessions, afp_structure) => {
          val thys_dir = afp_structure.thys_dir
          val selection = Sessions.Selection(sessions = sessions)
          val deps = structure.selection_deps(selection = selection)

          def rel_path(path: Path): Path =
            File.relative_path(afp_structure.thys_dir.absolute, path.absolute).get

          def is_thy_file(file: JFile): Boolean = file.isFile && file.getName.endsWith(".thy")

          sessions.flatMap { session_name =>
            val theory_nodes = deps.base_info(session_name).base.proper_session_theories
            val session_thy_files = theory_nodes.map(node => rel_path(node.path))

            val dir = structure(session_name).dir
            val physical_files = File.find_files(dir.file, is_thy_file, include_dirs = true).map(
              file => rel_path(Path.explode(file.getAbsolutePath)))

            val unused = physical_files.toSet -- session_thy_files.toSet
            if (unused.nonEmpty) Some(session_name -> unused.toList)
            else None
          }
        },
        t => t._1 + ": {" + t._2.mkString((", ")) + "}")
    ).sortBy(_.name)

  def the_check(name: String): Check[_] =
    known_checks.find(check => check.name == name) getOrElse
      error("Unkown check " + quote(name))

  def afp_check_roots(checks: List[Check[_]], afp_structure: AFP_Structure): Unit = {
    val structure = afp_structure.sessions_structure
    val sessions = structure.build_selection(Sessions.Selection.empty).sorted

    val bad = checks.exists(check => !check(structure, sessions, afp_structure))

    if (bad) {
      print_bad("Errors found.")
      System.exit(1)
    }
    else {
      print_good(sessions.length.toString + " sessions have been checked")
      print_good(checks.length.toString + " checks have found no errors")
    }
  }

  val isabelle_tool = Isabelle_Tool("afp_check_roots", "check ROOT files of AFP sessions",
    Scala_Project.here,
    { args =>
      var checks: List[Check[_]] = known_checks

      val getopts = Getopts("""
Usage: isabelle afp_check_roots [OPTIONS]

  Options are:
    -C NAMES    checks (default: """ + known_checks.mkString("\"", ",", "\"") + """)

  Check ROOT files of AFP sessions.
""",
      "C:" -> (arg => checks = Library.distinct(space_explode(',', arg)).map(the_check)))

      getopts(args)

      val afp_structure = AFP_Structure()

      afp_check_roots(checks, afp_structure)
    })
}

/* Author: Lars Hupel and Fabian Huch, TU Muenchen

Tools to check AFP session roots.
 */
package afp


import isabelle.{Path, *}

import java.io.File as JFile


object AFP_Check_Roots {
  def print_good(string: String): Unit =
    println(Console.BOLD + Console.GREEN + string + Console.RESET)

  def print_bad(string: String): Unit =
    println(Console.BOLD + Console.RED + string + Console.RESET)

  val exclude = List("etc")

  def dir_entries(path: Path): List[String] =
    File.read_dir(path).filter(name => (path + Path.basic(name)).is_dir).filterNot(exclude.contains)


  /* checks */

  case class Check[T](
    name: String,
    failure_msg: String,
    run: (Sessions.Structure, List[String], List[Path]) => List[T],
    failure_format: T => String = (t: T) => t.toString
  ) {
    override def toString: String = name

    def apply(
      structure: Sessions.Structure,
      sessions: List[String],
      check_dirs: List[Path]
    ): Boolean =
      run(structure, sessions, check_dirs) match {
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
        (structure, sessions, check_dirs) => {
          val entries = check_dirs.flatMap(dir_entries)

          entries.flatMap { entry_name =>
            if (!sessions.contains(entry_name) ||
              structure(entry_name).dir.base.implode != entry_name)
              Some(entry_name)
            else None
          }
        }),
      Check[String]("check_roots",
        "The following entries do not match with the ROOTS file:",
        (_, _, check_dirs) => {
          check_dirs.flatMap { dir =>
            val root_entries = Sessions.parse_roots(dir + Path.basic("ROOTS")).toSet
            val file_entries = dir_entries(dir).toSet
            (root_entries.union(file_entries) -- root_entries.intersect(file_entries)).toList
          }
        }
      ),
      Check[(String, List[Path])]("check_unused_thys",
        "The following sessions contain unused theories:",
        (structure, sessions, check_dirs) => {
          val selection = Sessions.Selection(sessions = sessions)
          val deps = structure.selection_deps(selection = selection)

          def is_thy_file(file: JFile): Boolean = file.isFile && file.getName.endsWith(".thy")

          val entry_dirs = check_dirs.flatMap(dir => dir_entries(dir).map(dir + Path.basic(_)))
          entry_dirs.flatMap { dir =>
            val entry = dir.base.implode
            def rel_path(path: Path): Path = File.relative_path(dir.absolute, path.absolute).get

            val sessions = Sessions.parse_root(dir + Path.basic("ROOT")).collect {
              case e: Sessions.Session_Entry => e.name
            }
            val theory_nodes = sessions.flatMap(deps.base_info(_).base.proper_session_theories)
            val thy_files = theory_nodes.map(node => rel_path(node.path))

            val physical_files = File.find_files(dir.file, is_thy_file, include_dirs = true)
            val rel_files = physical_files.map(file => rel_path(Path.explode(file.getAbsolutePath)))

            val unused = rel_files.toSet -- thy_files.toSet
            if (unused.nonEmpty) Some(entry -> unused.toList)
            else None
          }
        },
        t => t._1 + ": {" + t._2.mkString((", ")) + "}")
    ).sortBy(_.name)

  def the_check(name: String): Check[_] =
    known_checks.find(check => check.name == name) getOrElse
      error("Unkown check " + quote(name))


  /* check */

  def afp_check_roots(checks: List[Check[_]], dirs: List[Path], check_dirs: List[Path]): Unit = {
    val structure = Sessions.load_structure(Options.init(), dirs = dirs, select_dirs = check_dirs)
    val sessions = structure.build_selection(Sessions.Selection.empty).sorted

    val bad = checks.exists(check => !check(structure, sessions, check_dirs))

    if (bad) {
      print_bad("Errors found.")
      System.exit(1)
    }
    else {
      print_good(sessions.length.toString + " sessions have been checked")
      print_good(checks.length.toString + " checks have found no errors")
    }
  }


  /* isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("afp_check_roots", "check ROOT files of AFP sessions",
    Scala_Project.here,
    { args =>
      var dirs: List[Path] = Nil
      var checks: List[Check[_]] = known_checks
      var check_dirs: List[Path] = Nil

      val getopts = Getopts("""
Usage: isabelle afp_check_roots [OPTIONS]

  Options are:
    -d DIR      add entry dir
    -C NAMES    checks (default: """ + known_checks.mkString("\"", ",", "\"") + """)
    -D DIR      add and check entry dir

  Check ROOT files of AFP sessions.
""",
      "d:" -> (arg => dirs ::= Path.explode(arg)),
      "C:" -> (arg => checks = Library.distinct(space_explode(',', arg)).map(the_check)),
      "D:" -> (arg => check_dirs ::= Path.explode(arg)))

      getopts(args)

      if (check_dirs.isEmpty) {
        check_dirs ::= AFP_Structure().thys_dir
      } else {
        dirs ::= AFP_Structure().thys_dir
      }

      afp_check_roots(checks, dirs, check_dirs)
    })
}

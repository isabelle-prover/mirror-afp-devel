/* Author: Lars Hupel and Fabian Huch, TU Muenchen

Tools to check AFP session roots.
 */
package afp


import isabelle.*

import java.io.File as JFile


object AFP_Check_Roots {
  val exclude = List("etc")

  def dir_entries(path: Path): List[String] =
    File.read_dir(path).filter(name => (path + Path.basic(name)).is_dir).filterNot(exclude.contains)

  def root_sessions(root_file: Path): List[String] =
    Sessions.parse_root(root_file).collect { case e: Sessions.Session_Entry => e.name }


  /* checks */

  case class Check[T](
    name: String,
    failure_msg: String,
    run: (Sessions.Structure, List[String], List[Path]) => List[T],
    failure_format: T => String = (t: T) => t.toString,
    is_error: Boolean = true
  ) {
    override def toString: String = name

    def apply(
      structure: Sessions.Structure,
      sessions: List[String],
      check_dirs: List[Path],
      progress: Progress
    ): Boolean =
      run(structure, sessions, check_dirs) match {
        case Nil => true
        case offenders =>
          val msg = failure_msg + offenders.map("\n" + failure_format(_)).mkString
          progress.echo_error_message(msg)
          false
      }
  }

  val known_checks: List[Check[_]] =
    List(
      Check[String]("timeout",
        "The following entries contain sessions without timeouts or with timeouts not divisible by 300:",
        (structure, sessions, _) =>
          sessions.filter { session_name =>
            val info = structure(session_name)
            val timeout = info.options.real("timeout")
            timeout == 0 || timeout % 300 != 0
          }),
      Check[String]("chapter", "The following entries are not in the AFP chapter:",
        (structure, sessions, _) => sessions.filterNot(structure(_).chapter == "AFP")),
      Check[(String, List[String])]("groups", "The following sessions have wrong groups:",
        (structure, sessions, _) =>
          sessions.flatMap { session_name =>
            val info = structure(session_name)
            if (!info.groups.toSet.subsetOf(AFP.groups.keySet + "AFP") ||
              !info.groups.contains("AFP"))
              Some((session_name, info.groups))
            else None
          },
        t => t._1 + "{" + t._2.mkString(", ") + "}"),
      Check[String]("presence",
        "The following entries do not contain a corresponding session on top level:",
        (structure, sessions, check_dirs) =>
          check_dirs.flatMap(dir_entries).flatMap { entry_name =>
            if (!sessions.contains(entry_name) ||
              structure(entry_name).dir.base.implode != entry_name)
              Some(entry_name)
            else None
          }),
      Check[String]("roots",
        "The following entries do not match with the ROOTS file:",
        (_, _, check_dirs) =>
          check_dirs.flatMap { dir =>
            val root_entries = Sessions.parse_roots(dir + Path.basic("ROOTS")).toSet
            val file_entries = dir_entries(dir).toSet
            (root_entries.union(file_entries) -- root_entries.intersect(file_entries)).toList
          }),
      Check[(String, List[Path])]("unused_thys",
        "The following sessions contain unused theories:",
        (structure, sessions, check_dirs) => {
          val selection = Sessions.Selection(sessions = sessions)
          val deps = structure.selection_deps(selection = selection)

          def is_thy_file(file: JFile): Boolean = file.isFile && file.getName.endsWith(".thy")

          check_dirs.flatMap(dir => dir_entries(dir).map(dir + Path.basic(_))).flatMap { dir =>
            val sessions = root_sessions(dir + Path.basic("ROOT"))

            def rel_path(path: Path): Path = File.relative_path(dir.absolute, path.absolute).get

            val theory_nodes = sessions.flatMap(deps.apply(_).proper_session_theories)
            val thy_files = theory_nodes.map(node => rel_path(node.path))

            val physical_files =
              for (file <- File.find_files(dir.file, is_thy_file, include_dirs = true))
              yield rel_path(Path.explode(file.getAbsolutePath))

            val unused = physical_files.toSet -- thy_files.toSet
            if (unused.nonEmpty) Some(dir.base.implode -> unused.toList)
            else None
          }
        },
        t => t._1 + ": {" + t._2.mkString(", ") + "}"),
      Check[(String, List[Path])]("unused_document_files",
        "The following entries contain unused document files:",
        (structure, _, check_dirs) => {
          check_dirs.flatMap(dir => dir_entries(dir).map(dir + Path.basic(_))).flatMap { dir =>
            val sessions = root_sessions(dir + Path.basic("ROOT"))

            val session_document_files =
              sessions.flatMap { session_name =>
                val info = structure(session_name)
                info.document_files.map { case (dir, file) => (info.dir + dir, file) }
              }

            def rel_path(path: Path): Path = File.relative_path(dir.absolute, path.absolute).get

            val document_files =
              session_document_files.map { case (dir, path) => rel_path(dir + path) }

            val physical_files =
              for {
                document_dir <- session_document_files.map(_._1.file).distinct
                document_file <- File.find_files(document_dir, _.isFile, include_dirs = true)
              } yield rel_path(Path.explode(document_file.getAbsolutePath))

            val unused = physical_files.toSet -- document_files.toSet
            if (unused.nonEmpty) Some(dir.base.implode -> unused.toList) else None
          }
        },
        t => t._1 + ": {" + t._2.mkString(", ") + "}",
        is_error = false),
      Check[String]("document_presence",
        "The following entries do not contain a document root.tex",
        (structure, _, check_dirs) =>
          check_dirs.flatMap(dir_entries).filterNot(
            structure(_).document_files.map(_._2).contains(Path.basic("root.tex"))))
    ).sortBy(_.name)

  def the_check(name: String): Check[_] =
    known_checks.find(check => check.name == name) getOrElse
      error("Unkown check " + quote(name))


  /* check */

  def afp_check_roots(
    checks: List[Check[_]],
    dirs: List[Path],
    check_dirs: List[Path],
    progress: Progress = new Progress()
  ): Unit = {
    val structure = Sessions.load_structure(Options.init(), dirs = dirs, select_dirs = check_dirs)
    val sessions = structure.build_selection(Sessions.Selection.empty).sorted

    val (ok, bad) = checks.partition(_(structure, sessions, check_dirs, progress))

    if (bad.exists(_.is_error)) System.exit(1)
    else {
      progress.echo(sessions.length.toString + " sessions have been checked")
      if (bad.nonEmpty)
        progress.echo(bad.length.toString + " checks out of " + checks.length.toString +
          " have found warnings")
      else progress.echo(checks.length.toString + " checks have found no errors")
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

      val progress = new Console_Progress()

      if (check_dirs.isEmpty) {
        check_dirs ::= AFP_Structure().thys_dir
      } else {
        dirs ::= AFP_Structure().thys_dir
      }

      afp_check_roots(checks, dirs, check_dirs, progress)
    })
}

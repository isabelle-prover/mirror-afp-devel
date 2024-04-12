/* Author: Lars Hupel and Fabian Huch, TU Muenchen

Tools to check AFP session roots.
 */
package afp


import isabelle.*

import java.io.File as JFile


object AFP_Check_Roots {
  val exclude = List("etc")

  private def entries(dir: Path): List[String] =
    for {
      name <- File.read_dir(dir)
      if (dir + Path.basic(name)).is_dir
      if !exclude.contains(name)
    } yield name

  private def entry_dirs(dir: Path): List[Path] =
    for (entry <- entries(dir)) yield dir + Path.basic(entry)

  private def rel_path(entry_dir: Path, path: Path): Path =
    File.relative_path(entry_dir.absolute, path.absolute).get

  private def is_thy_file(file: JFile): Boolean = file.isFile && file.getName.endsWith(".thy")


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
          if (is_error) progress.echo_error_message(msg)
          else progress.echo_warning(msg)
          false
      }
  }


  val known_checks: List[Check[_]] =
    List(
      Check[String]("timeout",
        "The following entries contain sessions without timeouts or with timeouts not divisible by 300:",
        (structure, sessions, _) =>
          for {
            session_name <- sessions
            info = structure(session_name)
            timeout = info.options.real("timeout")
            if timeout == 0 || timeout % 300 != 0
          } yield session_name),
      Check[String]("chapter", "The following entries are not in the AFP chapter:",
        (structure, sessions, _) => sessions.filterNot(structure(_).chapter == AFP.chapter)),
      Check[(String, List[String])]("groups", "The following sessions have wrong groups:",
        (structure, sessions, _) =>
          for {
            session_name <- sessions
            info = structure(session_name)
            if !info.groups.toSet.subsetOf(Sessions.afp_groups)
          } yield (session_name, info.groups),
        t => t._1 + ": {" + t._2.mkString(", ") + "}"),
      Check[String]("presence",
        "The following entries do not contain a corresponding session on top level:",
        (structure, sessions, check_dirs) =>
          for {
            dir <- check_dirs
            entry_name <- entries(dir)
            entry_info = structure(entry_name)
            if !sessions.contains(entry_name) || entry_info.dir.base.implode != entry_name
          } yield entry_name),
      Check[String]("roots",
        "The following entries do not match with the ROOTS file:",
        (_, _, check_dirs) =>
          for {
            dir <- check_dirs
            root_entries = Sessions.parse_roots(dir + Sessions.ROOTS).toSet
            file_entries = entries(dir).toSet
            extra <- root_entries.union(file_entries) -- root_entries.intersect(file_entries)
          } yield extra),
      Check[(String, List[Path])]("unused_thys",
        "The following sessions contain unused theories:",
        (structure, sessions, check_dirs) => {
          val selection = Sessions.Selection(sessions = sessions)
          val deps = structure.selection_deps(selection = selection)

          for {
            entry_dir <- check_dirs.flatMap(entry_dirs)
            sessions = Sessions.parse_root_entries(entry_dir + Sessions.ROOT).map(_.name)

            theory_nodes = sessions.flatMap(deps.apply(_).proper_session_theories)
            thy_files = theory_nodes.map(node => rel_path(entry_dir, node.path))

            physical_files =
              for (file <- File.find_files(entry_dir.file, is_thy_file, include_dirs = true))
              yield rel_path(entry_dir, Path.explode(file.getAbsolutePath))

            unused = physical_files.toSet -- thy_files.toSet
            if unused.nonEmpty
          } yield entry_dir.base.implode -> unused.toList
        },
        t => t._1 + ": {" + t._2.mkString(", ") + "}"),
      Check[(String, List[Path])]("unused_document_files",
        "The following entries contain unused document files:",
        (structure, _, check_dirs) =>
          for {
            entry_dir <- check_dirs.flatMap(entry_dirs)
            sessions = Sessions.parse_root_entries(entry_dir + Sessions.ROOT).map(_.name)

            session_document_files =
              sessions.flatMap { session_name =>
                val info = structure(session_name)
                info.document_files.map { case (dir, file) => (info.dir + dir, file) }
              }

            document_files =
              session_document_files.map { case (dir, path) => rel_path(entry_dir, dir + path) }

            physical_files =
              for {
                document_dir <- session_document_files.map(_._1.file).distinct
                document_file <- File.find_files(document_dir, _.isFile, include_dirs = true)
              } yield rel_path(entry_dir, Path.explode(document_file.getAbsolutePath))

            unused = physical_files.toSet -- document_files.toSet

            if unused.nonEmpty
          } yield entry_dir.base.implode -> unused.toList,
        t => t._1 + ": {" + t._2.mkString(", ") + "}",
        is_error = false),
      Check[String]("document_presence",
        "The following entries do not contain a document root.tex",
        (structure, _, check_dirs) =>
          check_dirs.flatMap(entries).filterNot(
            structure(_).document_files.map(_._2).contains(Path.basic("root.tex")))),
      Check[(String, List[String])]("thy_name_clashes",
        "The following would cause name conflicts:",
        (structure, sessions, check_dirs) => {
          val all_sessions = structure.build_selection(Sessions.Selection(all_sessions = true))
          val deps = structure.selection_deps(Sessions.Selection(all_sessions = true))
          def session_thys(session_name: String): List[(String, String)] =
            deps(session_name).proper_session_theories.map(node =>
              Long_Name.base_name(node.theory) -> session_name)

          val session_set = sessions.toSet
          val duplicates =
            all_sessions.flatMap(session_thys).groupMap(_._1)(_._2).filter(_._2.length > 1)
          duplicates.filter(_._2.toSet.intersect(session_set).nonEmpty).toList
        },
        t => "Conflicting theory name " + quote(t._1) + " in sessions " + commas_quote(t._2),
        is_error = false)
    ).sortBy(_.name)

  def the_check(name: String): Check[_] =
    known_checks.find(check => check.name == name).getOrElse(error("Unknown check " + quote(name)))


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

/* Author: Fabian Huch

Publishes archive entry + main web pages on AFP web server.
 */
package afp

import java.io.{InputStreamReader, BufferedReader}

import isabelle._


object AFP_Publish {
  val date_format = Date.Format("uuuu-MM-dd")


  /* export file structure */

  object Export_Files {
    def init(): Export_Files = {
      val afp_export = Export_Files(Date.now().format(date_format), AFP.BASE)
      Isabelle_System.rm_tree(afp_export.dir)
      afp_export
    }
  }

  class Export_Files private(val date: String, base_dir: Path) {
    val name = "afp-export-" + date
    val dir = base_dir + Path.basic(name)

    def web_dir: Path = dir + Path.basic("web")
    def release_dir: Path = web_dir + Path.basic("release")
    def release_date: Path = web_dir + Path.basic("release-date.txt")
    def browser_info_dir: Path = web_dir + Path.basic("browser_info")
    def browser_info(current: Boolean = false): Path =
      browser_info_dir + Path.basic(if (current) "current" else Isabelle_System.isabelle_name())

    def afp_archive_name(current: Boolean = false): String =
      "afp-" + (if (current) "current" else date)
    def afp_archive_dir: Path = dir + Path.basic(afp_archive_name())
    def afp_archive(current: Boolean = false): Path =
      release_dir + Path.basic(afp_archive_name(current))

    def entry_name(entry: String, current: Boolean = false): String =
      "afp-" + entry + "-" + (if (current) "current" else date)
    def entry_archive(entry: String, current: Boolean = false): Path =
      release_dir + Path.basic(entry_name(entry, current = current))
  }


  /* publish */

  object Context {
    def apply(options: Options): Context =
      new Context(options, Store(options), AFP.self_repository())
  }

  class Context private(val options: Options, store: Store, val repository: Mercurial.Repository) {
    def afp_website_ssh_host: String = options.string("afp_website_ssh_host")

    def open_ssh(): SSH.Session =
      SSH.open_session(options,
        afp_website_ssh_host,
        options.int("afp_website_ssh_port"),
        options.string("afp_website_ssh_user"))

    def presentation_dir: Path = store.presentation_dir

    def website_dir: Path = Path.explode(options.string("afp_website_dir"))
  }

  def tar_gz(archive: Path, dir: Path, name: String): Path = {
    val tar_cmd =
      "tar --no-xattrs -C" + File.bash_path(dir) + " -cf" + File.bash_path(archive.tar) + " " + name
    val tar_env = Isabelle_System.Settings(List("COPYFILE_DISABLE" -> "1")).env
    Isabelle_System.bash(tar_cmd, env = tar_env).check
    Isabelle_System.bash("gzip --best " + archive.tar)
    archive.tar.gz
  }

  def publish(
    options: Options,
    entries: List[String] = Nil,
    max_jobs: Option[Int] = None,
    interactive: Boolean = true,
    skip_checks: Boolean = false,
    progress: Progress = new Progress
  ): Unit = {
    val sessions = entries.flatMap(AFP_Structure.entry_sessions).map(_.name)
    val context = Context(options)

    def relative_args(args: List[String]): String =
      Bash.strings(List("--cwd", File.standard_path(context.repository.root)) ::: args)

    val include = List("thys", "web", "etc", "tools/lib/afp_build")
    val exclude = List("etc/build.props")

    if (!skip_checks) {
      progress.echo("Checking sync with " + AFP_System.afp_name)

      val changed = context.repository.status(relative_args(include))
      if (changed.nonEmpty) error("Commit changes first.")

      val outgoing = context.repository.command("outgoing", args = "-q").check.out_lines
      if (outgoing.nonEmpty) error("Push changes to Heptapod first.")
    }

    val files = Export_Files.init()

    Isabelle_System.with_tmp_dir("afp_export") { tmp_dir =>
      /* export */

      progress.echo("Exporting from working copy " + context.repository.root.implode)
      context.repository.archive(File.standard_path(tmp_dir), options =
        relative_args(include.map("-I" + _) ::: exclude.map("-X" + _)))

      Isabelle_System.copy_dir(tmp_dir + Path.basic("web"), files.web_dir, direct = true)
      File.write(files.release_date, files.date)


      /* release */

      if (entries.nonEmpty) {
        Isabelle_System.make_directory(files.release_dir)

        progress.echo("Cleaning up browser_info directory")
        Isabelle_System.rm_tree(context.presentation_dir)

        progress.echo("Generating HTML for [" + sessions.mkString(" ") + "]")
        Build.build(context.options, selection = Sessions.Selection(sessions = sessions), progress =
          progress, clean_build = true, afp_root = Some(AFP.BASE), max_jobs = max_jobs).check

        progress.echo("Copying generated HTML")
        Isabelle_System.make_directory(files.browser_info())
        for {
          name <- File.read_dir(context.presentation_dir)
          dir = context.presentation_dir + Path.basic(name)
          if dir.is_dir
        } Isabelle_System.copy_dir(dir, files.browser_info())
        Isabelle_System.symlink(files.browser_info().base, files.browser_info(current = true))

        progress.echo("Tarring [" + files.afp_archive_name() + "]")
        Isabelle_System.make_directory(files.afp_archive_dir)
        for (dir <- List("thys", "etc", "tools")) {
          Isabelle_System.copy_dir(tmp_dir + Path.basic(dir), files.afp_archive_dir)
        }
        val archive_file =
          tar_gz(files.afp_archive(), files.afp_archive_dir.dir, files.afp_archive_dir.file_name)
        Isabelle_System.symlink(archive_file.base, files.afp_archive(current = true).tar.gz)
      }

      for (entry_name <- entries) {
        progress.echo("Tarring [" + entry_name + "]")

        val archive_file =
          tar_gz(files.entry_archive(entry_name), tmp_dir + Path.basic("thys"), entry_name)
        Isabelle_System.symlink(archive_file.base,
          files.entry_archive(entry_name, current = true).tar.gz)

        progress.echo("Finished [" + entry_name + "]")
      }
    }


    /* sync */

    val do_publish =
      if (entries.isEmpty || !interactive) true
      else {
        progress.echo(
          cat_lines(
            List(
              "Web pages are prepared for publication under",
              "[" + files.web_dir.absolute.implode + "]",
              "Please check content.")))
        val console_reader = new BufferedReader(new InputStreamReader(System.in))
        progress.echo("Type y if you want to publish. Any other key quits.")
        console_reader.readLine() match {
          case "y" => true
          case _ => false
        }
      }

    if (do_publish) {
      progress.echo("Publishing to [" + context.afp_website_ssh_host + "]")

      using(context.open_ssh()) { ssh =>
        val rsync_context = Rsync.Context(progress, ssh)
        val web_source = File.standard_path(files.web_dir)
        rsync_context.exec(
          chmod = "Dg=rx,Do=rx,Fg=r,Fo=r",
          args = List("-rplz", "--", Url.direct_path(web_source),
          rsync_context.target(context.website_dir))).check

        progress.echo("Published.")
      }
    }
    else {
      progress.echo("Aborted.")
      System.exit(1)
    }
  }


  /* tool wrapper */

  val isabelle_tool = Isabelle_Tool("afp_publish", "publish afp archives and web pages",
    Scala_Project.here,
    { args =>
      var publish_all = false
      var force = false
      var max_jobs: Option[Int] = None
      var options = Options.init(update = AFP_System.AFP_BUILD_OPTIONS)
      var skip_checks = false

      val getopts = Getopts("""
  Usage: isabelle afp_publish [OPTIONS] [ENTRIES ...]

    Options are:
      -a           publish all entries
      -j NUM       number of parallel build jobs (default: 1)
      -f           do not ask before publishing
      -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
      -s           skip checks

    Publishes archive for the given entries (if any) and AFP web page.
  """,
        "a" -> (_ => publish_all = true),
        "f" -> (_ => force = true),
        "j:" -> (arg => max_jobs = Some(Value.Int.parse(arg))),
        "o:" -> (arg => options = options + arg),
        "s" -> (_ => skip_checks = true)
        )

      val entries =
        getopts(args) match {
          case Nil if publish_all => AFP_Structure.entry_names
          case xs if !publish_all => xs
          case _ => getopts.usage()
        }

      val progress = new Console_Progress(verbose = true)

      publish(options, entries = entries, max_jobs = max_jobs, interactive = !force,
        skip_checks = skip_checks, progress = progress)
    })
}
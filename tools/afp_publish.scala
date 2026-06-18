/* Author: Fabian Huch

Publishes archive entry + main web pages on AFP web server.
 */
package afp


import isabelle._
import java.io.{InputStreamReader, BufferedReader}


object AFP_Publish {
  val date_format = Date.Format("uuuu-MM-dd")

  object Context {
    def apply(options: Options): Context =
      new Context(options, Store(options), AFP_System.repository())
  }

  class Context private(val options: Options, store: Store, val repository: Mercurial.Repository) {
    def open_ssh(): SSH.Session =
      SSH.open_session(options,
        options.string("afp_website_ssh_host"),
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
    val context = Context(options)

    if (!skip_checks) {
      progress.echo("Checking sync with " + AFP_System.afp_name)
      val outgoing = context.repository.command("outgoing", args = "-q").check.out_lines
      if (outgoing.nonEmpty) error("Push changes to Heptapod first.")
    }


    /* export */

    progress.echo("Exporting from working copy " + context.repository.root.implode)
    val date = Date.now().format(date_format)
    val export_dir = AFP.BASE + Path.basic("afp-export-" + date)
    Isabelle_System.rm_tree(export_dir)

    val include = List("thys", "web", "etc", "tools/lib/afp_build")
    val exclude = List("etc/build.props")
    val archive_args =
      List("--cwd", File.standard_path(context.repository.root)) :::
        include.map("-I" + _) :::
        exclude.map("-X" + _)
    context.repository.archive(File.standard_path(export_dir), options = Bash.strings(archive_args))

    val export_web = export_dir + Path.basic("web")
    File.write(export_web + Path.basic("release-date.txt"), date)

    val export_name = "afp-" + date
    val export_afp = Isabelle_System.make_directory(export_dir + Path.basic(export_name))
    for (dir <- List("thys", "etc", "tools")) {
      Isabelle_System.move_file(export_dir + Path.basic(dir), export_afp)
    }


    /* release */

    val do_publish = 
      if (entries.nonEmpty) {
        val sessions = entries.flatMap(AFP_Structure.entry_sessions).map(_.name)

        progress.echo("Cleaning up browser_info directory")
        Isabelle_System.rm_tree(context.presentation_dir)

        val browser_info = export_web + Path.basic("browser_info")
        val html_thys =
          Isabelle_System.make_directory(browser_info + Path.basic(Isabelle_System.isabelle_name()))

        Isabelle_System.symlink(html_thys, browser_info + Path.basic("current"))
        val tars = Isabelle_System.make_directory(export_web + Path.basic("release"))

        progress.echo("Tarring [" + export_name + "]")

        val archive_file = tar_gz(tars + Path.basic(export_name), export_dir, export_name)
        Isabelle_System.symlink(archive_file, tars + Path.basic("afp-current").tar.gz)

        progress.echo("Generating HTML for [" + sessions.mkString(" ") + "]")
        Build.build(context.options, selection = Sessions.Selection(sessions = sessions), progress =
          progress, clean_build = true, afp_root = Some(AFP.BASE), max_jobs = max_jobs).check

        for (entry_name <- entries) {
          progress.echo("Tarring [" + entry_name + "]")

          val export_name = "afp-" + entry_name + "-" + date
          val archive_file =
            tar_gz(tars + Path.basic(export_name), export_afp + Path.basic("thys"), entry_name)
          Isabelle_System.symlink(archive_file,
            tars + Path.basic("afp-" + entry_name + "-current").tar.gz)

          progress.echo("Finished [" + entry_name + "]")
        }

        progress.echo("Copying generated HTML")
        for {
          name <- File.read_dir(context.presentation_dir)
          dir = context.presentation_dir + Path.basic(name)
          if dir.is_dir
        } Isabelle_System.copy_dir(dir, html_thys)

        if (interactive) {
          progress.echo(
            cat_lines(
              List(
                "Web pages are prepared for publication under",
                "[" + export_web.absolute.implode + "]",
                "Please check content.")))
          val console_reader = new BufferedReader(new InputStreamReader(System.in))
          progress.echo("Type y if you want to publish. Any other key quits.")
          console_reader.readLine() match {
            case "y" => true
            case _ => false
          }
        }
        else true
      } else true


    /* sync */

    if (do_publish) {
      using(context.open_ssh()) { ssh =>
        progress.echo("Publishing to [" + ssh.host + "]")

        val rsync_context = Rsync.Context(progress, ssh, chmod = "Dg=rx,Do=rx,Fg=r,Fo=r")
        val web_source = File.standard_path(export_web)
        Rsync.exec(rsync_context, args = List("-rplz", "--", Url.direct_path(web_source),
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
      var force = false
      var max_jobs: Option[Int] = None
      var options = Options.init(specs = AFP_System.AFP_BUILD_OPTIONS)
      var skip_checks = false

      val getopts = Getopts("""
  Usage: isabelle afp_publish [OPTIONS] [ENTRIES ...]

    Options are:
      -j NUM       number of parallel build jobs (default: 1)
      -f           do not ask before publishing
      -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
      -s           skip checks

    Publishes archive for the given entries (if any) and AFP web page.
  """,
        "f" -> (_ => force = true),
        "j:" -> (arg => max_jobs = Some(Value.Int.parse(arg))),
        "o:" -> (arg => options = options + arg),
        "s" -> (_ => skip_checks = true)
        )

      val entries = getopts(args)

      val progress = new Console_Progress(verbose = true)

      publish(options, entries = entries, max_jobs = max_jobs, interactive = !force,
        skip_checks = skip_checks, progress = progress)
    })
}
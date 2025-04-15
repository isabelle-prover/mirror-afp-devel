/* Author: Fabian Huch, TU Muenchen

CI jobs for AFP build.
 */
package afp


import isabelle.*
import isabelle.find_facts.Find_Facts


object AFP_Build_CI {
  /* session status */

  object Status {
    def merge(statuses: List[Status]): Status =
      statuses.foldLeft(Ok: Status)(_ merge _)

    def from_results(results: Build.Results, session: String): Status =
      if (results.cancelled(session)) Skipped
      else if (results(session).ok) Ok
      else Failed
  }

  sealed abstract class Status(val str: String) {
    def merge(that: Status): Status = (this, that) match {
      case (Ok, s) => s
      case (Failed, _) => Failed
      case (Skipped, Failed) => Failed
      case (Skipped, _) => Skipped
    }
  }

  case object Ok extends Status("ok")
  case object Skipped extends Status("skipped")
  case object Failed extends Status("failed")


  /* context */

  class Context private(
    options: Options,
    val store: Store,
    val mail_system: Option[Build_CI.Mail_System],
    val afp: AFP_Structure,
  ) {
    lazy val entries = afp.load_entries()
    lazy val entry_sessions: Map[Metadata.Entry.Name, List[String]] =
      entries.values.map(entry => entry.name -> afp.entry_sessions(entry.name).map(_.name)).toMap

    def session_entry(session_name: String): Option[Metadata.Entry.Name] = {
      val entry = entry_sessions.find { case (_, sessions) => sessions.contains(session_name) }
      entry.map { case (name, _) => name }
    }

    val isabelle_path = Path.explode("$ISABELLE_HOME")
    val isabelle_id =
      if (Mercurial.Hg_Sync.ok(isabelle_path)) File.read(isabelle_path + Mercurial.Hg_Sync.PATH_ID)
      else Mercurial.self_repository().id()

    def website_dir: Path = Path.explode(options.string("afp_ci_website_dir"))

    def open_ssh(): SSH.System =
      SSH.open_system(options,
        options.string("afp_ci_website_ssh_host"),
        options.int("afp_ci_website_ssh_port"),
        options.string("afp_ci_website_ssh_user"))
  }

  object Context {
    def apply(options: Options, afp: AFP_Structure = AFP_Structure()): Context =
      new Context(options, Store(options), Build_CI.Mail_System.try_open(options), afp)
  }


  /** operations **/

  def notify_failed(
    context: Context,
    url: Option[Url],
    results: Build.Results,
    progress: Progress
  ): Unit =
    for (mail_system <- context.mail_system if !results.ok) {
      progress.echo(Build_CI.section("NOTIFICATIONS"))

      for {
        session <- results.sessions
        result = results(session)
        if !result.ok && !result.interrupted && !results.cancelled(session)
        entry <- context.session_entry(session)
      } {
        val subject = "Build of AFP entry " + entry + " failed"
        val content = """
The build for the session """ + session + """ belonging to the AFP entry """ + entry + """ failed.

You are receiving this mail because you are the maintainer of that AFP entry.

The following information might help you with resolving the problem.

""" + if_proper(url, "Build log: " + url.get + "\n") + """
Isabelle ID:  """ + context.isabelle_id + """
AFP ID:       """ + context.afp.hg_id + """
Timeout?      """ + result.timeout + """
Exit code:    """ + result.rc + """

Last 50 lines from stdout (if available):

""" + result.out_lines.takeRight(50).mkString("\n") + """"

Last 50 lines from stderr (if available):

""" + result.err_lines.takeRight(50).mkString("\n") + "\n"

        val recipients = context.entries.get(entry).map(_.notifies).getOrElse(Nil)
        if (recipients.isEmpty) progress.echo("Entry " + entry + ": no maintainers specified")
        else {
          val to = recipients.map(mail => Mail.address(mail.address))
          mail_system.server.send(Mail(subject, to, content, Some(mail_system.from), "AFP Build"))
        }
      }
    }

  def sitegen(
    context: Context,
    url: Option[Url],
    results: Build.Results,
    progress: Progress,
  ): Unit = {
    val entry_status =
      for {
        (entry, sessions) <- results.sessions.groupBy(context.session_entry).toList
        entry <- entry
        session_status = sessions.map(Status.from_results(results, _))
      } yield JSON.Object("entry" -> entry, "status" -> Status.merge(session_status.toList).str)

    val status_json =
      JSON.Object(
        "entries" -> entry_status,
        "build_data" -> (JSON.Object(
          "isabelle_id" -> context.isabelle_id,
          "afp_id" -> context.afp.hg_id,
          "time" -> Date.Format.default(progress.start)) ++
          url.map(url => "url" -> url.toString)))

    progress.echo(Build_CI.section("SITEGEN"))

    Isabelle_System.with_tmp_dir("hugo") { dir =>
      val status_file = dir + Path.basic("status").json
      File.write(status_file, JSON.Format(status_json))

      val output_dir = dir + Path.basic("output")

      AFP_Site_Gen.afp_site_gen(output_dir, afp = context.afp, status_file = Some(status_file),
        progress = progress)

      val release_dir = dir + Path.basic("release")
      Isabelle_System.make_directory(release_dir)

      progress.echo("Packing tars...")
      for ((name, _) <- context.entries) {
        val archive = release_dir + Path.basic("afp-" + name + "-current.tar.gz")
        Isabelle_System.gnutar("-czf " + File.bash_path(archive) + " " + Bash.string(name),
          dir = context.afp.thys_dir).check
      }

      using(context.open_ssh()) { ssh =>
        val rsync_context = Rsync.Context(ssh = ssh)

        val website_source = File.standard_path(output_dir)
        Rsync.exec(rsync_context, clean = true, args = List("--", Url.direct_path(website_source),
          rsync_context.target(context.website_dir))).check

        val release_source = File.standard_path(release_dir)
        Rsync.exec(rsync_context, args = List("--", Url.direct_path(release_source),
          rsync_context.target(context.website_dir + Path.basic("release")))).check

        val browser_info_source = File.standard_path(context.store.presentation_dir)
        val browser_info_dir = context.website_dir + Path.basic("browser_info")
        ssh.make_directory(browser_info_dir)
        Rsync.exec(rsync_context, args = List("--", Url.direct_path(browser_info_source),
          rsync_context.target(browser_info_dir + Path.basic("current")))).check
      }
    }
  }


  /** ci build jobs **/

  /* all */

  val all =
    Build_CI.Job("all",
      "builds Isabelle + AFP (without very slow)",
      Build_CI.Cluster("cluster.schedule"),
      Time.hms(4, 0, 0),
      afp = true,
      selection =
        Sessions.Selection(all_sessions = true, exclude_session_groups = List("very_slow")),
      build_prefs = List(Options.Spec.eq("build_engine", Build_Schedule.Build_Engine.name)),
      hook = new Build_CI.Hook {
        override def post(
          options: Options,
          url: Option[Url],
          results: Build.Results,
          progress: Progress
        ): Unit = notify_failed(Context(options), url, results, progress)
      },
      other_settings =
        List("ISABELLE_TOOL_JAVA_OPTIONS=\"$ISABELLE_TOOL_JAVA_OPTIONS -Xmx8G -Xss64M\""))


  /* nightly presentation */

  val presentation =
    Build_CI.Job("presentation",
      "nightly build for all of Isabelle/AFP, including documents and afp site",
      Build_CI.Cluster("cluster.schedule"),
      Time.hms(8, 0, 0),
      afp = true,
      selection = Sessions.Selection(all_sessions = true),
      presentation = true,
      build_prefs = List(Options.Spec.eq("build_engine", Build_Schedule.Build_Engine.name)),
      hook = new Build_CI.Hook {
        override def pre(options: Options, progress: Progress): Unit =
          Build.build_process(options, build_cluster = true, remove_builds = true, force = true,
            progress = progress)

        override def post(
          options: Options,
          url: Option[Url],
          results: Build.Results,
          progress: Progress
        ): Unit = {
          val context = Context(options)
          notify_failed(context, url, results, progress)
          sitegen(context, url, results, progress)
        }
      },
      other_settings =
        List("ISABELLE_TOOL_JAVA_OPTIONS=\"$ISABELLE_TOOL_JAVA_OPTIONS -Xmx16G -Xss64M\""),
      trigger = Build_CI.Timed.nightly())


  /* weekly indexing */

  val indexing =
    Build_CI.Job("indexing",
      "weekly build for all of Isabelle/AFP, indexing theories into find_facts",
      Build_CI.Cluster("cluster.schedule"),
      Time.hms(8, 0, 0),
      afp = true,
      selection = Sessions.Selection(all_sessions = true),
      build_prefs = List(Options.Spec.eq("build_engine", Build_Schedule.Build_Engine.name)),
      hook = new Build_CI.Hook {
        override def post(
          options: Options,
          url: Option[Url],
          results: Build.Results,
          progress: Progress
        ): Unit = {
          val dirs = AFP.main_dirs(Some(AFP.BASE))
          val afp = AFP_Structure(options)
          val database = "afp-" + afp.hg_id
          val find_facts_options =
            List(
              Options.Spec.eq("find_facts_database_name", database),
              Options.Spec.make("build_database"),
              Options.Spec.make("build_database_server"))

          val cmd = Find_Facts.find_facts_index_command(results.sessions_ok, options =
            find_facts_options, dirs = dirs, no_build = true)

          val isabelle_home = Path.explode("$ISABELLE_HOME")
          val isabelle_identifier = Isabelle_System.isabelle_identifier() getOrElse ""
          val script = Bash.context(cmd, SSH.Local.user_home, isabelle_identifier, isabelle_home)

          Isabelle_System.bash(script,
            progress_stdout = progress.echo(_),
            progress_stderr = progress.echo_error_message(_)).check
        }
      },
      other_settings =
        List("ISABELLE_TOOL_JAVA_OPTIONS=\"$ISABELLE_TOOL_JAVA_OPTIONS -Xmx8G -Xss64M\""),
      trigger = Build_CI.Timed.weekly(start = Time.hms(3, 17, 0)))
}

class CI_Jobs extends Isabelle_CI_Jobs(
  AFP_Build_CI.all, AFP_Build_CI.presentation, AFP_Build_CI.indexing)

/* Author: Lars Hupel and Fabian Huch, TU Muenchen

Unified AFP CI integration.
 */
package afp


import isabelle.*

import java.time.ZoneId
import java.time.format.DateTimeFormatter


object AFP_Build {
  /* mailing */


  object Mailer {
    def failed_subject(name: Metadata.Entry.Name): String = "Build of AFP entry " + name + " failed"

    def failed_text(session_name: String, entry: Metadata.Entry.Name, isabelle_id: String,
      afp_id: String, result: Process_Result): String = """
The build for the session
  """ + session_name + """",
belonging to the AFP entry
  """ + entry + """
failed.

You are receiving this mail because you are the maintainer of that AFP
entry.

The following information might help you with resolving the problem.

Build log:    """ + Isabelle_System.getenv("BUILD_URL") + """
Isabelle ID:  """ + isabelle_id + """
AFP ID:       """ + afp_id + """
Timeout?      """ + result.timeout + """
Exit code:    """ + result.rc + """

Last 50 lines from stdout (if available):

""" + result.out_lines.takeRight(50).mkString("\n") + """"

Last 50 lines from stderr (if available):

""" + result.err_lines.takeRight(50).mkString("\n") + "\n"
  }


  /* metadata tooling */

  class Metadata_Tools private(
    val structure: AFP_Structure,
    val server: Mail.Server,
    val entries: Metadata.Entries
  ) {
    def maintainers(name: Metadata.Entry.Name): List[Metadata.Email] = {
      entries.get(name) match {
        case None => Nil
        case Some(entry) => entry.notifies
      }
    }

    val sessions: Map[Metadata.Entry.Name, List[String]] =
      entries.values.map(entry =>
        entry.name -> structure.entry_sessions(entry.name).map(_.name)).toMap

    def session_entry(session_name: String): Option[Metadata.Entry.Name] = {
      val entry = sessions.find { case (_, sessions) => sessions.contains(session_name) }
      entry.map { case (name, _) => name }
    }

    def by_entry(sessions: List[String]): Map[Option[Metadata.Entry.Name], List[String]] =
      sessions.groupBy(session_entry)

    def notify(name: Metadata.Entry.Name, subject: String, text: String): Boolean = {
      val recipients = entries.get(name).map(_.notifies).getOrElse(Nil)
      if (recipients.nonEmpty) {
        val from = Some(Mail.address("ci@isabelle.systems"))
        val to = recipients.map(mail => Mail.address(mail.address))
        val mail = Mail(subject, to, text, from, "Jenkins Admin")
        server.send(mail)
      }
      recipients.nonEmpty
    }
  }

  object Metadata_Tools {
    def load(afp: AFP_Structure, options: Options): Metadata_Tools =
      new Metadata_Tools(afp, CI_Build.mail_server(options), afp.load())
  }


  /* utilities */

  def status_as_json(
    isabelle_id: String,
    afp_id: String,
    start_time: String,
    status: Map[Option[String], CI_Build.Status]
  ): JSON.T = {
    val entries =
      status.collect {
        case (Some(entry), status) => JSON.Object("entry" -> entry, "status" -> status.str)
      }

    JSON.Object(
      "build_data" -> JSON.Object(
        "isabelle_id" -> isabelle_id,
        "afp_id" -> afp_id,
        "time" -> start_time,
        "url" -> Isabelle_System.getenv("BUILD_URL"),
        "job" -> Isabelle_System.getenv("JOB_NAME")),
      "entries" -> entries)
  }

  def status_as_html(status: Map[Option[String], CI_Build.Status]): XML.Body = {
    val entries =
      status.toList.collect {
        case (None, CI_Build.Failed) => HTML.item(HTML.text("Distribution"))
        case (Some(entry), CI_Build.Failed) =>
          HTML.item(List(
            HTML.link("https://devel.isa-afp.org/entries/" + entry + ".html",
              HTML.text(entry))))
      }

    if (entries.isEmpty) Nil
    else HTML.text("Failed entries: ") ::: HTML.list(entries) :: Nil
  }


  /* ci build jobs */

  val afp =
    CI_Build.Job("afp", "builds the AFP, without slow sessions", CI_Build.Profile.from_host, {
      val afp = AFP_Structure()

      val status_file = Path.explode("$ISABELLE_HOME/status.json").file
      val deps_file = Path.explode("$ISABELLE_HOME/dependencies.json").file

      def pre_hook(options: Options): CI_Build.Result = {
        println("AFP id " + afp.hg_id)
        if (status_file.exists()) status_file.delete()
        CI_Build.Result.ok
      }

      def post_hook(results: Build.Results, options: Options, start_time: Time): CI_Build.Result = {
        CI_Build.print_section("DEPENDENCIES")
        println("Generating dependencies file ...")
        val result = Isabelle_System.bash("isabelle afp_dependencies")
        result.check
        println("Writing dependencies file ...")
        File.write(deps_file, result.out)
        CI_Build.print_section("COMPLETED")
        CI_Build.Result.ok
      }

      CI_Build.Build_Config(
        clean = false, include = List(afp.thys_dir), pre_hook = pre_hook,
        post_hook = post_hook, selection = Sessions.Selection(
          session_groups = List("AFP"),
          exclude_session_groups = List("slow")))
    })

  val all =
    CI_Build.Job("all", "builds Isabelle + AFP (without slow)", CI_Build.Profile.from_host, {
      val afp = AFP_Structure()
      val isabelle_home = Path.explode(Isabelle_System.getenv_strict("ISABELLE_HOME"))
      val isabelle_id = CI_Build.hg_id(isabelle_home)

      val status_file = Path.explode("$ISABELLE_HOME/status.json").file
      val report_file = Path.explode("$ISABELLE_HOME/report.html").file
      val deps_file = Path.explode("$ISABELLE_HOME/dependencies.json").file


      def pre_hook(options: Options): CI_Build.Result = {
        println("AFP id " + afp.hg_id)
        if (status_file.exists()) status_file.delete()
        if (report_file.exists()) report_file.delete()

        File.write(report_file, "")

        val server = CI_Build.mail_server(options)
        if (!server.defined) {
          println("Mail configuration not found.")
          CI_Build.Result.error
        }
        else {
          server.check()
          CI_Build.Result.ok
        }
      }

      def post_hook(results: Build.Results, options: Options, start_time: Time): CI_Build.Result = {
        CI_Build.print_section("DEPENDENCIES")
        println("Generating dependencies file ...")
        val result = Isabelle_System.bash("isabelle afp_dependencies")
        result.check

        println("Writing dependencies file ...")
        File.write(deps_file, result.out)

        val metadata = Metadata_Tools.load(afp, options)

        val status = metadata.by_entry(results.sessions.toList).view.mapValues { sessions =>
          CI_Build.Status.merge(sessions.map(CI_Build.Status.from_results(results, _)))
        }.toMap

        CI_Build.print_section("REPORT")
        println("Writing report file ...")
        File.write(report_file,
          HTML.output(status_as_html(status), hidden = false, structural = true))

        CI_Build.print_section("SITEGEN")
        println("Writing status file ...")
        val formatted_time =
          start_time.instant.atZone(ZoneId.systemDefault)
            .format(DateTimeFormatter.RFC_1123_DATE_TIME)
        File.write(status_file,
          JSON.Format(status_as_json(isabelle_id, afp.hg_id, formatted_time, status)))
        println("Running sitegen ...")

        val script = afp.base_dir + Path.explode("admin/sitegen-devel")
        val sitegen_cmd =
          Bash.strings(List(script.file.toString, status_file.toString, deps_file.toString))

        val sitegen_res =
          Isabelle_System.bash(sitegen_cmd, progress_stdout = println, progress_stderr = println)
        if (!sitegen_res.ok) println("sitegen failed")

        if (!results.ok) {
          CI_Build.print_section("NOTIFICATIONS")
          for (session_name <- results.sessions) {
            val result = results(session_name)
            if (!result.ok && !results.cancelled(session_name) && metadata.server.defined) {
              metadata.session_entry(session_name).foreach { entry =>
                val subject = Mailer.failed_subject(entry)
                val text = Mailer.failed_text(session_name, entry, isabelle_id, afp.hg_id, result)
                val notified = metadata.notify(entry, subject, text)
                if (!notified) println("Entry " + entry + ": WARNING no maintainers specified")
              }
            }
          }
        }

        CI_Build.print_section("COMPLETED")
        CI_Build.Result(sitegen_res.rc)
      }

      CI_Build.Build_Config(
        clean = false, include = List(afp.thys_dir), pre_hook = pre_hook,
        post_hook = post_hook, selection = Sessions.Selection(
          all_sessions = true,
          exclude_session_groups = List("slow")))
    })
  
  val mac =
    CI_Build.Job("mac", "builds the AFP (without some sessions) on Mac Os",
      CI_Build.Profile.from_host.copy(threads = 8, jobs = 1), {
        val afp = AFP_Structure()

        def pre_hook(options: Options): CI_Build.Result = {
          println("Build for AFP id " + afp.hg_id)
          CI_Build.Result.ok
        }

        CI_Build.Build_Config(
          include = List(afp.thys_dir), pre_hook = pre_hook, selection =
            Sessions.Selection(
              all_sessions = true,
              exclude_sessions = List("HOL-Proofs", "HOL-ODE-Numerics", "Linear_Programming",
                "HOL-Nominal-Examples", "HOL-Analysis"),
              exclude_session_groups = List("slow")))
      })
  
  val slow =
    CI_Build.Job("slow", "builds the AFP slow sessions",
      CI_Build.Profile.from_host.copy(threads = 8, jobs = 1), {
        val afp = AFP_Structure()

        def pre_hook(options: Options): CI_Build.Result = {
          println("Build for AFP id " + afp.hg_id)
          CI_Build.Result.ok
        }

        CI_Build.Build_Config(
          include = List(afp.thys_dir), pre_hook = pre_hook,
          selection = Sessions.Selection(session_groups = List("slow")))
      })

  val testboard =
    CI_Build.Job("testboard", "builds the AFP testboard", CI_Build.Profile.from_host, {
      val afp = AFP_Structure()
      val report_file = Path.explode("$ISABELLE_HOME/report.html").file

      def pre_hook(options: Options): CI_Build.Result = {
        println("AFP id " + afp.hg_id)
        if (report_file.exists()) report_file.delete()

        File.write(report_file, "")
        CI_Build.Result.ok
      }

      def post_hook(results: Build.Results, options: Options, start_time: Time): CI_Build.Result = {
        val metadata = Metadata_Tools.load(afp, options)

        val status = metadata.by_entry(results.sessions.toList).view.mapValues { sessions =>
          CI_Build.Status.merge(sessions.map(CI_Build.Status.from_results(results, _)))
        }.toMap

        CI_Build.print_section("REPORT")
        println("Writing report file ...")
        File.write(report_file,
          HTML.output(status_as_html(status), hidden = false, structural = true))
        CI_Build.print_section("COMPLETED")
        CI_Build.Result.ok
      }

      CI_Build.Build_Config(
        clean = false, include = List(afp.thys_dir), pre_hook = pre_hook,
        post_hook = post_hook, selection =
          Sessions.Selection(
            all_sessions = true,
            exclude_session_groups = List("slow")))
    })
}

class CI_Builds extends Isabelle_CI_Builds(
  AFP_Build.afp,
  AFP_Build.all,
  AFP_Build.slow,
  AFP_Build.mac,
  AFP_Build.testboard)

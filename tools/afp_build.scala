/* Author: Lars Hupel and Fabian Huch, TU Muenchen

Unified AFP CI integration.
 */
package afp


import isabelle._

import afp.Metadata.{Email, Entry}

import java.time.{Instant, ZoneId}
import java.time.format.DateTimeFormatter
import java.util.{Map => JMap, Properties => JProperties}
import javax.mail.internet.{InternetAddress, MimeMessage}
import javax.mail.{Authenticator, Message, MessagingException, PasswordAuthentication, Transport, Session => JSession}
import scala.sys.process._


object AFP_Build {

  /* Result */

  case class Result(rc: Int)
  case object Result {
    def ok: Result = Result(Process_Result.RC.ok)
    def error: Result = Result(Process_Result.RC.error)
  }


  /* Profile */

  case class Profile(threads: Int, jobs: Int, numa: Boolean)

  object Profile {
    def from_host: Profile = {
      Isabelle_System.hostname() match {
        case "hpcisabelle" => Profile(8, 8, numa = true)
        case "lxcisa1" => Profile(4, 10, numa = false)
        case _ => Profile(2, 2, numa = false)
      }
    }
  }


  /* Config */

  case class Build_Config(
    documents: Boolean = true,
    clean: Boolean = true,
    include: List[Path] = Nil,
    select: List[Path] = Nil,
    pre_hook: () => Result = () => { Result.ok },
    post_hook: Build.Results => Result = { _ => Result.ok },
    selection: Sessions.Selection = Sessions.Selection.empty
  )


  /* Status */

  object Status {
    def merge(statuses: List[Status]): Status =
      statuses.foldLeft(Ok: Status)(_ merge _)

    def from_results(results: Build.Results, session: String): Status =
      if (results.cancelled(session))
        Skipped
      else if (results(session).ok)
        Ok
      else
        Failed
  }

  case object Ok extends Status("ok")
  case object Skipped extends Status("skipped")
  case object Failed extends Status("failed")


  /* Mailing */

  case class Mail(subject: String, recipients: List[String], text: String) {
    def send(): Unit = {
      val user = System.getProperty("mail.smtp.user")
      val sender = System.getProperty("mail.smtp.from")
      val password = System.getProperty("mail.smtp.password")

      System.setProperty("mail.smtp.ssl.protocols", "TLSv1.2")

      val authenticator = new Authenticator() {
        override def getPasswordAuthentication =
          new PasswordAuthentication(user, password)
      }

      val session = JSession.getDefaultInstance(System.getProperties, authenticator)
      val message = new MimeMessage(session)
      message.setFrom(new InternetAddress("ci@isabelle.systems", "Isabelle/Jenkins"))
      message.setSender(new InternetAddress(sender))
      message.setSubject(subject)
      message.setText(text, "UTF-8")
      message.setSentDate(new java.util.Date())

      recipients.foreach { recipient =>
        message.addRecipient(Message.RecipientType.TO, new InternetAddress(recipient))
      }

      try {
        Transport.send(message)
      } catch {
        case ex: MessagingException => println(s"Sending mail failed: ${ex.getMessage}")
      }
    }
  }

  object Mail {
    def apply(subject: String, recipients: List[String], text: String) =
      new Mail(subject, recipients, text)

    def failed_subject(name: Entry.Name): String = s"Build of AFP entry $name failed"

    def failed_text(session_name: String, entry: Entry.Name, isabelle_id: String,
      afp_id: String, result: Process_Result): String = s"""
The build for the session
  $session_name,
belonging to the AFP entry
  $entry
failed.

You are receiving this mail because you are the maintainer of that AFP
entry.

The following information might help you with resolving the problem.

Build log:    ${Isabelle_System.getenv("BUILD_URL")}
Isabelle ID:  $isabelle_id
AFP ID:       $afp_id
Timeout?      ${result.timeout}
Exit code:    ${result.rc}

Last 50 lines from stdout (if available):

${result.out_lines.takeRight(50).mkString("\n")}

Last 50 lines from stderr (if available):

${result.err_lines.takeRight(50).mkString("\n")}
"""
  }

  sealed abstract class Status(val str: String) {
    def merge(that: Status): Status = (this, that) match {
      case (Ok, s) => s
      case (Failed, _) => Failed
      case (Skipped, Failed) => Failed
      case (Skipped, _) => Skipped
    }
  }


  /* Metadata tooling */

  case class Metadata_Tools private(structure: AFP_Structure, entries: Map[Entry.Name, Entry]) {

    def maintainers(name: Entry.Name): List[Email] = {
      entries.get(name) match {
        case None => Nil
        case Some(entry) => entry.notifies
      }
    }

    val sessions: Map[Entry.Name, List[String]] =
      entries.values.map(entry =>
        entry.name -> structure.entry_sessions(entry.name).map(_.name)).toMap

    def session_entry(session_name: String): Option[Entry.Name] = {
      val entry = sessions.find { case (_, sessions) => sessions.contains(session_name) }
      entry.map { case (name, _) => name }
    }

    def by_entry(sessions: List[String]): Map[Option[Entry.Name], List[String]] =
      sessions.groupBy(session_entry)

    def notify(name: Entry.Name, subject: String, text: String): Boolean = {
      val recipients = entries.get(name).map(_.notifies).getOrElse(Nil)
      if (recipients.nonEmpty) Mail(subject, recipients.map(_.address), text).send()
      recipients.nonEmpty
    }
  }

  object Metadata_Tools {
    def apply(structure: AFP_Structure, entries: List[Entry]): Metadata_Tools =
      new Metadata_Tools(structure, entries.map(entry => entry.name -> entry).toMap)
    def load(afp: AFP_Structure): Metadata_Tools = Metadata_Tools(afp, afp.load())
  }


  /* Utilities */

  def status_as_json(isabelle_id: String, afp_id: String, start_time: String,
    status: Map[Option[String], Status]): String = {
    val entries_strings = status.collect {
      case (Some(entry), status) =>
        s"""{"entry": "$entry", "status": "${status.str}"}"""
    }

    val entries_string = entries_strings.mkString("[", ",\n", "]")

    s"""
      {"build_data":
        {"isabelle_id": "$isabelle_id",
         "afp_id": "$afp_id",
         "time": "$start_time",
         "url": "${Isabelle_System.getenv("BUILD_URL")}",
         "job": "${Isabelle_System.getenv("JOB_NAME")}"
        },
       "entries":
         $entries_string
      }
    """
  }

  def status_as_html(status: Map[Option[String], Status]): String = {
    val entries_strings = status.collect {
      case (None, Failed) =>
        s"<li>Distribution</li>"
      case (Some(entry), Failed) =>
        s"""<li><a href="https://devel.isa-afp.org/entries/$entry.html">$entry</a></li>"""
    }

    if (entries_strings.isEmpty)
      ""
    else
      entries_strings.mkString("Failed entries: <ul>", "\n", "</ul>")
  }

  private def load_properties(): JProperties = {
    val props = new JProperties()
    val file_name = Isabelle_System.getenv("ISABELLE_CI_PROPERTIES")

    if (file_name != "") {
      val file = Path.explode(file_name).file
      if (file.exists())
        props.load(new java.io.FileReader(file))
      props
    }
    else
      props
  }

  private def compute_timing(results: Build.Results, group: Option[String]): Timing = {
    val timings = results.sessions.collect {
      case session if group.forall(results.info(session).groups.contains(_)) =>
        results(session).timing
    }
    timings.foldLeft(Timing.zero)(_ + _)
  }

  private def with_documents(options: Options, config: Build_Config): Options = {
    if (config.documents)
      options
        .bool.update("browser_info", true)
        .string.update("document", "pdf")
        .string.update("document_variants", "document:outline=/proof,/ML")
    else
      options
  }

  final def hg_id(path: Path): String =
    Mercurial.repository(path).id()

  final def print_section(title: String): Unit =
    println(s"\n=== $title ===\n")

  def ci_profile_build(profile: Profile, config: Build_Config): Unit = {
    val isabelle_home = Path.explode(Isabelle_System.getenv_strict("ISABELLE_HOME"))
    val isabelle_id = hg_id(isabelle_home)

    val start_time = Instant.now().atZone(ZoneId.systemDefault).format(DateTimeFormatter.RFC_1123_DATE_TIME)

    print_section("CONFIGURATION")
    println(Build_Log.Settings.show())
    val props = load_properties()
    System.getProperties.asInstanceOf[JMap[AnyRef, AnyRef]].putAll(props)

    val options =
      with_documents(Options.init(), config)
        .int.update("parallel_proofs", 1)
        .int.update("threads", profile.threads)

    println(s"jobs = ${profile.jobs}, threads = ${profile.threads}, numa = ${profile.numa}")

    print_section("BUILD")
    println(s"Build started at $start_time")
    println(s"Isabelle id $isabelle_id")
    val pre_result = config.pre_hook()

    print_section("LOG")
    val (results, elapsed_time) = {
      val progress = new Console_Progress(verbose = true)
      val start_time = Time.now()
      val results = progress.interrupt_handler {
        Build.build(
          options + "system_heaps",
          selection = config.selection,
          progress = progress,
          clean_build = config.clean,
          verbose = true,
          numa_shuffling = profile.numa,
          max_jobs = profile.jobs,
          dirs = config.include,
          select_dirs = config.select)
      }
      val end_time = Time.now()
      (results, end_time - start_time)
    }

    print_section("TIMING")

    val groups = results.sessions.map(results.info).flatMap(_.groups)
    for (group <- groups)
      println(s"Group $group: " + compute_timing(results, Some(group)).message_resources)

    val total_timing = compute_timing(results, None).copy(elapsed = elapsed_time)
    println("Overall: " + total_timing.message_resources)

    if (!results.ok) {
      print_section("FAILED SESSIONS")

      for (name <- results.sessions) {
        if (results.cancelled(name)) {
          println(s"Session $name: CANCELLED")
        }
        else {
          val result = results(name)
          if (!result.ok)
            println(s"Session $name: FAILED ${ result.rc }")
        }
      }
    }

    val post_result = config.post_hook(results)

    System.exit(List(pre_result.rc, results.rc, post_result.rc).max)
  }


  /* Isabelle CI tools */

  def ci_build_afp = Isabelle_Tool("ci_build_afp", "builds the AFP, without slow sessions",
    Scala_Project.here,
  { args =>
    val getopts = Getopts("""
Usage: isabelle ci_build_afp

  Builds the AFP, without slow sessions.
""")
    getopts(args)

    val afp = AFP_Structure()

    val status_file = Path.explode("$ISABELLE_HOME/status.json").file
    val deps_file = Path.explode("$ISABELLE_HOME/dependencies.json").file

    val profile = Profile.from_host
    def pre_hook(): Result = {
      println(s"AFP id ${afp.hg_id}")
      if (status_file.exists())
        status_file.delete()
      Result.ok
    }
    def post_hook: Result = {
      print_section("DEPENDENCIES")
      println("Generating dependencies file ...")
      val result = Isabelle_System.bash("isabelle afp_dependencies")
      result.check
      println("Writing dependencies file ...")
      File.write(deps_file, result.out)
      print_section("COMPLETED")
      Result.ok
    }
    val config = Build_Config(clean = false, include = List(afp.thys_dir), pre_hook = pre_hook,
      post_hook = _ => post_hook, selection = Sessions.Selection(
        session_groups = List("AFP"),
        exclude_session_groups = List("slow")))

    ci_profile_build(profile, config)
  })


  def ci_build_all = Isabelle_Tool("ci_build_all", "builds Isabelle + AFP (without slow)",
    Scala_Project.here,
  { args =>
    val getopts = Getopts("""
Usage: isabelle ci_build_all

  Builds Isabelle + AFP (without slow).
  """)
    getopts(args)

    val start_time = Instant.now().atZone(ZoneId.systemDefault).format(DateTimeFormatter.RFC_1123_DATE_TIME)
    val afp = AFP_Structure()
    val isabelle_home = Path.explode(Isabelle_System.getenv_strict("ISABELLE_HOME"))
    val isabelle_id = hg_id(isabelle_home)

    val status_file = Path.explode("$ISABELLE_HOME/status.json").file
    val report_file = Path.explode("$ISABELLE_HOME/report.html").file
    val deps_file = Path.explode("$ISABELLE_HOME/dependencies.json").file
    val can_send_mails = System.getProperties.containsKey("mail.smtp.host")

    val profile = Profile.from_host
    def pre_hook(): Result = {
      println(s"AFP id ${afp.hg_id}")
      if (status_file.exists())
        status_file.delete()
      if (report_file.exists())
        report_file.delete()

      File.write(report_file, "")

      if (!can_send_mails) {
        println(s"Mail configuration not found.")
        Result.error
      } else {
        Result.ok
      }
    }
    def post_hook(results: Build.Results): Result = {
      print_section("DEPENDENCIES")
      println("Generating dependencies file ...")
      val result = Isabelle_System.bash("isabelle afp_dependencies")
      result.check
      println("Writing dependencies file ...")
      File.write(deps_file, result.out)

      val metadata = Metadata_Tools.load(afp)

      val status = metadata.by_entry(results.sessions.toList).view.mapValues { sessions =>
        Status.merge(sessions.map(Status.from_results(results, _)))
      }.toMap

      print_section("REPORT")
      println("Writing report file ...")
      File.write(report_file, status_as_html(status))

      print_section("SITEGEN")
      println("Writing status file ...")
      File.write(status_file, status_as_json(isabelle_id, afp.hg_id, start_time, status))
      println("Running sitegen ...")

      val script = afp.base_dir + Path.explode("admin/sitegen-devel")
      val sitegen_rc = List(script.file.toString, status_file.toString, deps_file.toString).!
      if (sitegen_rc > 0) {
        println("sitegen failed")
      }

      if (!results.ok) {
        print_section("NOTIFICATIONS")
        for (session_name <- results.sessions) {
          val result = results(session_name)
          if (!result.ok && !results.cancelled(session_name) && can_send_mails) {
            metadata.session_entry(session_name).foreach { entry =>
              val subject = Mail.failed_subject(entry)
              val text = Mail.failed_text(session_name, entry, isabelle_id, afp.hg_id, result)
              val notified = metadata.notify(entry, subject, text)
              if (!notified) println(s"Entry $entry: WARNING no maintainers specified")
            }
          }
        }
      }

      print_section("COMPLETED")
      Result(sitegen_rc)
    }
    val config = Build_Config(clean = false, include = List(afp.thys_dir), pre_hook = pre_hook,
      post_hook = post_hook, selection = Sessions.Selection(
        all_sessions = true,
        exclude_session_groups = List("slow")))

    ci_profile_build(profile, config)
  })


  def ci_build_mac = Isabelle_Tool("ci_build_mac", "builds the AFP (without some sessions) on Mac Os",
    Scala_Project.here,
  { args =>
    val getopts = Getopts("""
Usage: isabelle ci_build_mac

  Builds the AFP (without some sessions) on Mac Os.
  """)
    getopts(args)

    val afp = AFP_Structure()

    val profile = Profile.from_host.copy(threads = 8, jobs = 1)
    def pre_hook(): Result = {
      println(s"Build for AFP id ${afp.hg_id}")
      Result.ok
    }
    val config = Build_Config(include = List(afp.thys_dir), pre_hook = pre_hook, selection =
      Sessions.Selection(
        all_sessions = true,
        exclude_sessions = List("HOL-Proofs", "HOL-ODE-Numerics", "Linear_Programming", "HOL-Nominal-Examples", "HOL-Analysis"),
        exclude_session_groups = List("slow")))

    ci_profile_build(profile, config)
  })


  def ci_build_slow = Isabelle_Tool("ci_build_slow", "builds the AFP slow sessions",
    Scala_Project.here,
  { args =>
    val getopts = Getopts("""
Usage: isabelle ci_build_slow

  Builds the AFP slow sessions.
  """)
    getopts(args)

    val afp = AFP_Structure()

    val profile = Profile.from_host.copy(threads = 8, jobs = 1)
    def pre_hook(): Result = {
      println(s"Build for AFP id ${afp.hg_id}")
      Result.ok
    }
    val config = Build_Config(include = List(afp.thys_dir), pre_hook = pre_hook,
      selection = Sessions.Selection(session_groups = List("slow")))

    ci_profile_build(profile, config)
  })


  val ci_build_testboard = Isabelle_Tool("ci_build_testboard", "builds the AFP testboard",
    Scala_Project.here,
  { args =>
    val getopts = Getopts("""
Usage: isabelle ci_build_testboard

  Builds the AFP testboard.
""")
    getopts(args)

    val afp = AFP_Structure()
    val report_file = Path.explode("$ISABELLE_HOME/report.html").file

    val profile = Profile.from_host
    def pre_hook(): Result = {
      println(s"AFP id ${ afp.hg_id }")
      if (report_file.exists())
        report_file.delete()

      File.write(report_file, "")
      Result.ok
    }
    def post_hook(results: Build.Results): Result = {
      val metadata = Metadata_Tools.load(afp)

      val status = metadata.by_entry(results.sessions.toList).view.mapValues { sessions =>
        Status.merge(sessions.map(Status.from_results(results, _)))
      }.toMap

      print_section("REPORT")
      println("Writing report file ...")
      File.write(report_file, status_as_html(status))
      print_section("COMPLETED")
      Result.ok
    }
    val config = Build_Config(clean = false, include = List(afp.thys_dir), pre_hook = pre_hook,
      post_hook = post_hook, selection =
        Sessions.Selection(
          all_sessions = true,
          exclude_session_groups = List("slow")))

    ci_profile_build(profile, config)
  })
}
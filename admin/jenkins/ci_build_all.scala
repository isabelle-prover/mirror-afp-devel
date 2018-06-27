object profile extends isabelle.CI_Profile
{
  import isabelle._
  import java.io.FileReader
  import scala.sys.process._
  import org.apache.commons.configuration2._

  override def clean = false
  override def numa = true

  val afp = Path.explode("$AFP_BASE")
  val afp_thys = afp + Path.explode("thys")
  val afp_id = hg_id(afp)

  sealed abstract class Status(val str: String)
  {
    def merge(that: Status): Status = (this, that) match {
      case (Ok, s) => s
      case (Failed, s) => Failed
      case (Skipped, Failed) => Failed
      case (Skipped, s) => Skipped
    }
  }
  object Status
  {
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

  case class Mail(subject: String, recipients: List[String], text: String) {
    import java.util._
    import javax.mail._
    import javax.mail.internet._
    import javax.activation._

    def send(): Unit = {
      val authenticator = new Authenticator() {
        override def getPasswordAuthentication() =
          new PasswordAuthentication(System.getProperty("mail.smtp.user"), System.getProperty("mail.smtp.password"))
      }

      val session = Session.getDefaultInstance(System.getProperties(), authenticator)
      val message = new MimeMessage(session)
      message.setFrom(new InternetAddress("ci@isabelle.systems", "Isabelle/Jenkins"))
      message.setSubject(subject)
      message.setText(text, "UTF-8")
      message.setSentDate(new java.util.Date())

      recipients.foreach { recipient =>
        message.addRecipient(Message.RecipientType.TO, new InternetAddress(recipient))
      }

      try {
        Transport.send(message)
      }
      catch {
        case ex: MessagingException => println(s"Sending mail failed: ${ex.getMessage}")
      }
    }
  }

  class Metadata(ini: INIConfiguration)
  {

    def maintainers(entry: String): List[String] =
    {
      val config = ini.getSection(entry)
      val raw =
        if (config.containsKey("notify"))
          config.getString("notify")
        else
          ""
      List(raw.split(','): _*).map(_.trim).filterNot(_.isEmpty)
    }

    def entry_of_session(info: Sessions.Info): Option[String] =
      if (info.dir.dir.file == afp_thys.file)
        Some(info.dir.base.implode)
      else
        None

    def notify(name: String, result: Process_Result, info: Sessions.Info): Unit =
      entry_of_session(info).foreach { entry =>
        val mails = maintainers(entry)

        val text =
          s"""|The build for the session
              |  $name,
              |belonging to the AFP entry
              |  $entry
              |failed.
              |
              |You are receiving this mail because you are the maintainer of that AFP
              |entry.
              |
              |The following information might help you with resolving the problem.
              |
              |Build log:    ${Isabelle_System.getenv("BUILD_URL")}
              |Isabelle ID:  $isabelle_id
              |AFP ID:       $afp_id
              |Timeout?      ${result.timeout}
              |Exit code:    ${result.rc}
              |
              |Last 50 lines from stdout (if available):
              |
              |${result.out_lines.takeRight(50).mkString("\n")}
              |
              |Last 50 lines from stderr (if available):
              |
              |${result.err_lines.takeRight(50).mkString("\n")}
              |""".stripMargin

        val subject = s"Build of AFP entry $entry failed"

        if (mails.isEmpty)
          println(s"Entry $entry: WARNING no maintainers specified")
        else
          Mail(text = text, subject = subject, recipients = mails).send()
      }

    def group_by_entry(results: Build.Results): Map[Option[String], List[String]] =
      results.sessions.toList.map { name =>
        entry_of_session(results.info(name)) -> name
      }.groupBy(_._1).mapValues(_.map(_._2))

    def results_as_json(results: Build.Results): String =
    {
      val entries_status =
        group_by_entry(results).mapValues(sessions => Status.merge(sessions.map(Status.from_results(results, _))))

      val entries_strings = entries_status.collect {
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
  }

  val status_file = Path.explode("$ISABELLE_HOME/status.json").file
  val deps_file = Path.explode("$ISABELLE_HOME/dependencies.json").file
  def can_send_mails = System.getProperties().containsKey("mail.smtp.host")

  def threads = 8
  def jobs = 8
  def include = List(afp_thys)
  def select = Nil

  def pre_hook(args: List[String]) =
  {
    println(s"AFP id $afp_id")
    if (status_file.exists())
      status_file.delete()

    if (!can_send_mails)
      println(s"Mail configuration not found.")
  }

  def post_hook(results: Build.Results) =
  {
    print_section("DEPENDENCIES")
    println("Generating dependencies file ...")
    val result = Isabelle_System.bash("isabelle afp_dependencies")
    result.check
    println("Writing dependencies file ...")
    File.write(deps_file, result.out)

    val metadata = {
      val path = afp + Path.explode("metadata/metadata")
      val ini = new INIConfiguration()
      if (path.is_file) {
        val reader = new FileReader(path.file)
        ini.read(reader)
        reader.close()
      }
      new Metadata(ini)
    }

    print_section("SITEGEN")
    println("Writing status file ...")
    File.write(status_file, metadata.results_as_json(results))
    println("Running sitegen ...")

    val script = afp + Path.explode("admin/sitegen-devel")
    val sitegen_result = List(script.file.toString, status_file.toString, deps_file.toString).!
    if (sitegen_result > 0)
      println("sitegen failed")

    if (!results.ok)
    {
      print_section("NOTIFICATIONS")
      for (name <- results.sessions)
      {
        val result = results(name)
        if (!result.ok && !results.cancelled(name) && can_send_mails)
          metadata.notify(name, result, results.info(name))
      }
    }

    print_section("COMPLETED")
  }

  def selection =
    Sessions.Selection(
      all_sessions = true,
      exclude_session_groups = List("slow"))

}

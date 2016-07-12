object profile extends isabelle.CI_Profile
{

  import isabelle._
  import java.io.{FileReader, PrintWriter}
  import org.apache.commons.configuration2._


  val is_testboard = Isabelle_System.getenv("ISABELLE_CI_TESTBOARD") == "true"

  val afp = Path.explode("$ISABELLE_HOME/afp")
  val afp_thys = afp + Path.explode("thys")

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

  class Metadata(ini: INIConfiguration) {
    def maintainers(entry: String): List[String] = {
      val config = ini.getSection(entry)
      val raw =
        if (config.containsKey("notify"))
          config.getString("notify")
        else
          ""
      raw.split(' ').toList.filterNot(_.isEmpty)
    }

    def notify(name: String, result: Process_Result, info: Sessions.Info): Unit =
      if (info.dir.dir.implode == afp_thys.implode) {
        val entry = info.dir.base.implode
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
              |Isabelle ID:  ${Isabelle_System.getenv("ISABELLE_CI_REPO_ID")}
              |AFP ID:       ${Isabelle_System.getenv("ISABELLE_CI_AFP_ID")}
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

    def results_as_json(results: Build.Results): String =
    {
      val entries_strings =
        results.sessions.map { name =>
          val result = results(name)

          val status_str =
            if (result.ok) "ok"
            else if (results.cancelled(name)) "skipped"
            else "failed"

          s"""{"entry": "$name", "status": "$status_str"}"""
        }

      val entries_string = entries_strings.mkString("[", ",", "]")

      s"""
        {"build_data": {},
         "entries": $entries_string
        }
      """
    }
  }

  val status_file = Path.explode("$ISABELLE_HOME/status.json").file
  def can_send_mails = System.getProperties().containsKey("mail.smtp.host")


  def threads = 2
  def jobs = 8
  def include = List(afp_thys)
  def select = Nil

  def pre_hook(args: List[String]) =
  {
    println(s"Build for AFP id ${hg_id(afp)}")
    if (status_file.exists())
      status_file.delete()

    if (!is_testboard && !can_send_mails)
      println(s"Not a testboard run, but mail configuration not found.")
  }

  def post_hook(results: Build.Results) = {
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

    val writer = new PrintWriter(status_file)
    writer.print(metadata.results_as_json(results))
    writer.close()

    if (!results.ok)
    {
      for (name <- results.sessions)
      {
        val result = results(name)
        if (!result.ok && !results.cancelled(name) && !is_testboard && can_send_mails)
          metadata.notify(name, result, results.info(name))
      }
    }
  }

  def select_sessions(tree: Sessions.Tree): (List[String], Sessions.Tree) =
    tree.selection(
      session_groups = List("AFP"),
      exclude_session_groups = List("slow"))

}

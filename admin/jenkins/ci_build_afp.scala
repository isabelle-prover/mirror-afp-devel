object profile extends isabelle.CI_Profile
{

  import isabelle._
  import java.io.FileReader
  import org.apache.commons.configuration2._


  val isTestboard = Isabelle_System.getenv("ISABELLE_CI_TESTBOARD") == "true"

  val afp = Path.explode("$ISABELLE_HOME/afp")
  val afp_thys = afp + Path.explode("thys")

  case class Mail(subject: String, recipients: List[String], text: String) {
    import java.util._
    import javax.mail._
    import javax.mail.internet._
    import javax.activation._

    def send(): Unit = {
      val session = Session.getDefaultInstance(System.getProperties())
      val message = new MimeMessage(session)
      message.setFrom(new InternetAddress("ci@isabelle.systems", "Isabelle/Jenkins"))
      message.setSubject(subject)
      message.setText(text, "UTF-8")

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
  }


  def threads = 4
  def jobs = 2
  def all = false
  def groups = List("AFP")
  def exclude = List("slow")
  def include = List(afp_thys)
  def select = Nil

  def pre_hook(args: List[String]) =
    println(s"Build for AFP id ${hg_id(afp)}")

  def post_hook(results: Build.Results) = {
    val canSendMails = System.getProperties().containsKey("mail.smtp.host")

    if (!isTestboard && !canSendMails)
      println(s"Not a testboard run, but mail configuration not found. Check ${Isabelle_System.getenv_strict("ISABELLE_CI_PROPERTIES")}.")

    if (!results.ok) {
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

      for (name <- results.sessions) {
        val result = results(name)
        if (!result.ok && !results.cancelled(name) && !isTestboard && canSendMails)
          metadata.notify(name, result, results.info(name))
      }
    }
  }

}

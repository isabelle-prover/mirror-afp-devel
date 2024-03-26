/* Author: Fabian Huch, TU Muenchen

AFP submission system backend.
 */
package afp


import isabelle.*
import isabelle.HTML.*

import afp.Web_App.{ACTION, API, FILE, Params}
import afp.Web_App.Params.{List_Key, Nest_Key, empty}
import afp.Web_App.More_HTML.*
import afp.Metadata.{Affiliation, Author, DOI, Email, Entry, Formatted, Homepage, License, Orcid, Reference, Release, Topic, Unaffiliated}

import java.text.Normalizer
import java.time.LocalDate

import scala.collection.immutable.StringView
import scala.util.matching.Regex


object AFP_Submit {

  case class Val_Opt[A] private(opt: Option[A], err: Option[String]) {
    def is_empty: Boolean = opt.isEmpty
  }
  object Val_Opt {
    def ok[A](value: A): Val_Opt[A] = Val_Opt(Some(value), None)
    def user_err[A](msg: String): Val_Opt[A] = Val_Opt(None, Some(msg))
    def error[A]: Val_Opt[A] = Val_Opt(None, None)
  }

  case class Val[A] private(v: A, err: Option[String]) {
    def with_err(err: String): Val[A] = Val.err(v, err)
    def perhaps_err(opt: Val_Opt[_]): Val[A] = opt.err.map(with_err).getOrElse(this)
  }

  object Val {
    def ok[A](value: A): Val[A] = Val(value, None)
    def err[A](value: A, msg: String): Val[A] = Val(value, Some(msg))
  }


  /* data model */

  object Model {
    object Related extends Enumeration {
      val DOI, Plaintext = Value

      def from_string(s: String): Option[Value] = values.find(_.toString == s)
      def get(r: Reference): Value = r match {
        case afp.Metadata.DOI(_) => DOI
        case afp.Metadata.Formatted(_) => Plaintext
      }
    }

    case class Create_Entry(
      name: Val[String] = Val.ok(""),
      title: Val[String] = Val.ok(""),
      affils: Val[List[Affiliation]] = Val.ok(Nil),
      notifies: Val[List[Email]] = Val.ok(Nil),
      author_input: Option[Author] = None,
      notify_input: Option[Author] = None,
      topics: Val[List[Topic]] = Val.ok(Nil),
      topic_input: Option[Topic] = None,
      license: License,
      `abstract`: Val[String] = Val.ok(""),
      related: List[Reference] = Nil,
      related_kind: Option[Related.Value] = None,
      related_input: Val[String] = Val.ok("")
    ) {
      val used_affils: Set[Affiliation] = (affils.v ++ notifies.v).toSet
      val used_authors: Set[Author.ID] = used_affils.map(_.author)
    }

    case class Create(
      entries: Val[List[Create_Entry]] = Val.ok(Nil),
      new_authors: Val[List[Author]] = Val.ok(Nil),
      new_author_input: String = "",
      new_author_orcid: String = "",
      new_affils: Val[List[Affiliation]] = Val.ok(Nil),
      new_affils_author: Option[Author] = None,
      new_affils_input: String = "",
    ) extends T {
      def update_entry(num: Int, entry: Create_Entry): Create =
        this.copy(entries = Val.ok(entries.v.updated(num, entry)))

      def updated_authors(old_authors: Map[Author.ID, Author]): Map[Author.ID, Author] =
        (old_authors ++ new_authors.v.map(author => author.id -> author)).map {
          case (id, author) =>
            val emails =
              author.emails ++ new_affils.v.collect { case e: Email if e.author == id => e }
            val homepages =
              author.homepages ++ new_affils.v.collect { case h: Homepage if h.author == id => h }
            id -> author.copy(emails = emails.distinct, homepages = homepages.distinct)
        }

      val used_affils: Set[Affiliation] = entries.v.toSet.flatMap(_.used_affils)
      val used_authors: Set[Author.ID] =
        new_affils.v.map(_.author).toSet ++ entries.v.flatMap(_.used_authors)

      def create(authors: Map[Author.ID, Author]): (Map[Author.ID, Author], List[Entry]) =
        (updated_authors(authors), entries.v.map(entry =>
          Entry(
            name = entry.name.v,
            title = entry.title.v,
            authors = entry.affils.v,
            date = LocalDate.now(),
            topics = entry.topics.v,
            `abstract` = entry.`abstract`.v.trim,
            notifies = entry.notifies.v,
            license = entry.license,
            note = "",
            related = entry.related)))
    }

    object Build extends Enumeration {
      val Pending, Running, Aborted, Failed, Success = Value
    }

    object Status extends Enumeration {
      val Submitted, Review, Added, Rejected = Value

      def from_string(s: String): Option[Value] = values.find(_.toString == s)
    }

    case class Overview(id: String, date: LocalDate, name: String, status: Status.Value)
    case class Metadata(authors: Map[Author.ID, Author], entries: List[Entry]) {
      def new_authors(old_authors: Map[Author.ID, Author]): Set[Author] =
        entries.flatMap(_.authors).map(_.author).filterNot(old_authors.contains).toSet.map(authors)

      def new_affils(old_authors: Map[Author.ID, Author]): Set[Affiliation] =
        entries.flatMap(entry => entry.authors ++ entry.notifies).toSet.filter {
          case _: Unaffiliated => false
          case e: Email => !old_authors.get(e.author).exists(_.emails.contains(e))
          case h: Homepage => !old_authors.get(h.author).exists(_.homepages.contains(h))
        }
    }

    sealed trait T
    case object Invalid extends T
    case class Upload(meta: Metadata, message: String, error: String) extends T
    case class Created(id: String) extends T
    case class Submission(
      id: Handler.ID,
      meta: Metadata,
      message: String,
      build: Build.Value,
      status: Option[Status.Value],
      log: String) extends T
    case class Submission_List(submissions: List[Overview]) extends T
  }


  /* Physical submission handling */

  trait Handler {
    def create(
      date: Date,
      meta: Model.Metadata,
      message: String,
      archive: Bytes,
      ext: String
    ): Handler.ID
    def list(): Model.Submission_List
    def get(id: Handler.ID,
      topics: Map[Topic.ID, Topic],
      licenses: Map[License.ID, License]
    ): Option[Model.Submission]
    def submit(id: Handler.ID): Unit
    def set_status(id: Handler.ID, status: Model.Status.Value): Unit
    def abort_build(id: Handler.ID): Unit
    def get_patch(id: Handler.ID): Option[Path]
    def get_archive(id: Handler.ID): Option[Path]
  }
  object Handler {
    import Model._

    type ID = String

    object ID {
      private val format = Date.Format.make(
        List(
          Date.Formatter.pattern("uuuu-MM-dd_HH-mm-ss_SSS"),
          Date.Formatter.pattern("uuuu-MM-dd_HH-mm-ss_SSS_VV")),
        _ + "_" + Date.timezone().getId)

      def apply(submission_time: Date): ID = format(submission_time)
      def unapply(id: ID): Option[Date] = format.unapply(id)
      def check(id: ID): Option[ID] = unapply(id).map(apply)
    }


    /* Handler for local edits */

    class Edit(afp_structure: AFP_Structure) extends Handler {
      val authors = afp_structure.load_authors.map(author => author.id -> author).toMap
      val topics = afp_structure.load_topics.flatMap(_.all_topics)
      val all_topics = topics.map(topic => topic.id -> topic).toMap
      val licenses = afp_structure.load_licenses.map(license => license.id -> license).toMap
      val releases = afp_structure.load_releases.groupBy(_.entry)
      val dates = afp_structure.load().map(entry => entry.name -> entry.date).toMap

      override def create(
        date: Date,
        meta: Metadata,
        message: String,
        archive: Bytes,
        ext: String
      ): ID = {
        val entry =
          meta.entries match {
            case e :: Nil => e
            case _ => isabelle.error("Must be a single entry")
          }

        val old = afp_structure.load_entry(entry.name, authors, all_topics, licenses, releases)
        val updated =
          old.copy(
            title = entry.title,
            authors = entry.authors,
            topics = entry.topics,
            `abstract` = entry.`abstract`,
            notifies = entry.notifies,
            license = entry.license,
            related = entry.related)

        afp_structure.save_entry(updated)
        // TODO what happens to the authors

        entry.name
      }

      override def list(): Submission_List =
        Submission_List(afp_structure.entries.sortBy(dates.get).reverse.map { entry =>
          Overview(entry, dates(entry), entry, Status.Added)
        })

      override def get(
        id: ID, topics: Map[ID, Topic], licenses: Map[ID, License]
      ): Option[Submission] =
        if (!afp_structure.entries.contains(id)) None
        else {
          val entry = afp_structure.load_entry(id, authors, all_topics, licenses, releases)
          val meta = Metadata(authors, List(entry))
          Some(Submission(id, meta, "", Model.Build.Success, Some(Status.Added), ""))
        }

      override def submit(id: ID): Unit = ()
      override def set_status(id: ID, status: Model.Status.Value): Unit = ()
      override def abort_build(id: ID): Unit = ()
      override def get_patch(id: ID): Option[Path] = None
      override def get_archive(id: ID): Option[Path] = None
    }


    /* Adapter to existing submission system */

    class Adapter(submission_dir: Path, afp_structure: AFP_Structure) extends Handler {

      private val up: Path = submission_dir + Path.basic("up")
      private def up(id: ID): Path = up + Path.basic(id)
      private def down(id: ID): Path = submission_dir + Path.basic("down") + Path.basic(id)

      private def signal(id: ID, s: String): Unit =
        File.write(up(id) + Path.basic(s), s.toUpperCase)
      private def is_signal(id: ID, s: String): Boolean = (up(id) + Path.basic(s)).file.exists()

      private def read_build(id: ID): Build.Value = {
        val build = down(id) + Path.basic("result")
        if (!build.file.exists) Build.Pending
        else File.read(build).trim match {
          case "" => Build.Running
          case "NOT_FINISHED" => Build.Running
          case "FAILED" => if (is_signal(id, "kill")) Build.Aborted else Build.Failed
          case "SUCCESS" => Build.Success
          case s => isabelle.error("Unkown build status: " + quote(s))
        }
      }

      private def status_file(id: ID): Path = up(id) + Path.basic("AFP_STATUS")
      private def read_status(id: ID): Option[Status.Value] = {
        val status = status_file(id)
        if (!status.file.exists()) None
        else File.read(status).trim match {
          case "SUBMITTED" => Some(Status.Submitted)
          case "PROCESSING" => Some(Status.Review)
          case "REJECTED" => Some(Status.Rejected)
          case "ADDED" => Some(Status.Added)
          case s => isabelle.error("Unknown status: " + quote(s))
        }
      }

      private def info_file(id: ID): Path = up(id) + Path.basic("info.json")
      private def patch_file(id: ID): Path = up(id) + Path.basic("patch")

      private val archive_name: String = "archive"

      def make_partial_patch(base_dir: Path, src: Path, dst: Path): String = {
        val patch = Isabelle_System.make_patch(base_dir, src, dst, "--unidirectional-new-file")
        split_lines(patch).filterNot(_.startsWith("Only in")).mkString("\n")
      }

      def create(date: Date, meta: Metadata, message: String, archive: Bytes, ext: String): ID = {
        val id = ID(date)
        val dir = up(id)
        dir.file.mkdirs()

        val structure = AFP_Structure(dir)
        structure.save_authors(meta.authors.values.toList.sortBy(_.id))
        meta.entries.foreach(structure.save_entry)

        val archive_file = dir + Path.basic(archive_name + ext)
        Bytes.write(archive_file, archive)

        val metadata_rel =
          File.relative_path(afp_structure.base_dir, afp_structure.metadata_dir).getOrElse(
            afp_structure.metadata_dir)
        val metadata_patch =
          make_partial_patch(afp_structure.base_dir, metadata_rel, structure.metadata_dir)
        File.write(patch_file(id), metadata_patch)

        val info =
          JSON.Format(JSON.Object(
            "comment" -> message,
            "entries" -> meta.entries.map(_.name),
            "notify" -> meta.entries.flatMap(_.notifies).map(_.address).distinct))
        File.write(info_file(id), info)

        signal(id, "done")
        id
      }

      def list(): Submission_List =
        Submission_List(
          File.read_dir(up).flatMap(ID.unapply).reverse.flatMap { date =>
            val id = ID(date)
            val day = date.rep.toLocalDate
            read_status(id).map(Overview(id, day, AFP_Structure(up(id)).entries_unchecked.head, _))
          })

      def get(
        id: ID,
        topics: Map[Topic.ID, Topic],
        licenses: Map[License.ID, License]
      ): Option[Submission] =
        ID.check(id).filter(up(_).file.exists).map { id =>
          val structure = AFP_Structure(up(id))
          val authors = structure.load_authors.map(author => author.id -> author).toMap
          val entries = structure.entries_unchecked.map(
            structure.load_entry(_, authors, topics, licenses, Map.empty))

          val log_file = down(id) + Path.basic("isabelle.log")
          val log = if (log_file.file.exists) File.read(log_file) else ""

          JSON.parse(File.read(info_file(id))) match {
            case JSON.Object(m) if m.contains("comment") =>
              val meta = Metadata(authors, entries)
              Submission(id, meta, m("comment").toString, read_build(id), read_status(id), log)
            case _ => isabelle.error("Could not read info")
          }
        }

      private def check(id: ID): Option[ID] = ID.check(id).filter(up(_).file.exists)

      def submit(id: ID): Unit = check(id).foreach(signal(_, "mail"))

      def set_status(id: ID, status: Status.Value): Unit =
        check(id).foreach { id =>
          val content =
            status match {
              case Status.Submitted => "SUBMITTED"
              case Status.Review => "PROCESSING"
              case Status.Added => "ADDED"
              case Status.Rejected => "REJECTED"
            }
          File.write(status_file(id), content)
        }

      def abort_build(id: ID): Unit = check(id).foreach(signal(_, "kill"))

      def get_patch(id: ID): Option[Path] = check(id).map(patch_file)
      def get_archive(id: ID): Option[Path] = check(id).flatMap { id =>
        val dir = up(id)
        File.read_dir(dir).find(_.startsWith(archive_name + ".")).map(dir + Path.basic(_))
      }
    }
  }


  /* server */

  object Mode extends Enumeration {
    val EDIT, SUBMISSION = Value
  }

  class Server(
    api: API,
    afp_structure: AFP_Structure,
    mode: Mode.Value,
    handler: Handler,
    devel: Boolean,
    verbose: Boolean,
    progress: Progress,
    port: Int = 0
  ) extends Web_App.Server[Model.T](api, port, verbose, progress) {
    val repo = Mercurial.the_repository(afp_structure.base_dir)

    var authors: Map[Author.ID, Metadata.Author] = Map.empty
    var topics: List[Topic] = Nil
    var all_topics: Map[Topic.ID, Topic] = Map.empty
    var licenses: Map[License.ID, License] = Map.empty
    var releases: Map[Entry.Name, List[Release]] = Map.empty
    var entries: Set[Entry.Name] = Set.empty

    private def load(): Unit = synchronized {
      authors = afp_structure.load_authors.map(author => author.id -> author).toMap
      topics = afp_structure.load_topics.flatMap(_.all_topics)
      all_topics = topics.map(topic => topic.id -> topic).toMap
      licenses = afp_structure.load_licenses.map(license => license.id -> license).toMap
      releases = afp_structure.load_releases.groupBy(_.entry)
      entries = afp_structure.entries.toSet
    }

    load()


    /* endpoints */

    val SUBMIT = Path.explode("submit")
    val SUBMISSION = Path.explode("submission")
    val SUBMISSIONS = Path.explode("submissions")
    val API_SUBMISSION = Path.explode("api/submission")
    val API_SUBMISSION_UPLOAD = Path.explode("api/submission/upload")
    val API_SUBMISSION_CREATE = Path.explode("api/submission/create")
    val API_SUBMISSION_STATUS = Path.explode("api/submission/status")
    val API_RESUBMIT = Path.explode("api/resubmit")
    val API_BUILD_ABORT = Path.explode("api/build/abort")
    val API_SUBMIT = Path.explode("api/submit")
    val API_SUBMISSION_AUTHORS_ADD = Path.explode("api/submission/authors/add")
    val API_SUBMISSION_AUTHORS_REMOVE = Path.explode("api/submission/authors/remove")
    val API_SUBMISSION_AFFILIATIONS_ADD = Path.explode("api/submission/affiliations/add")
    val API_SUBMISSION_AFFILIATIONS_REMOVE = Path.explode("api/submission/affiliations/remove")
    val API_SUBMISSION_ENTRIES_ADD = Path.explode("api/submission/entries/add")
    val API_SUBMISSION_ENTRIES_REMOVE = Path.explode("api/submission/entries/remove")
    val API_SUBMISSION_ENTRY_TOPICS_ADD = Path.explode("api/submission/entry/topics/add")
    val API_SUBMISSION_ENTRY_TOPICS_REMOVE = Path.explode("api/submission/entry/topics/remove")
    val API_SUBMISSION_ENTRY_AUTHORS_ADD = Path.explode("api/submission/entry/authors/add")
    val API_SUBMISSION_ENTRY_AUTHORS_REMOVE = Path.explode("api/submission/entry/authors/remove")
    val API_SUBMISSION_ENTRY_NOTIFIES_ADD = Path.explode("api/submission/entry/notifies/add")
    val API_SUBMISSION_ENTRY_NOTIFIES_REMOVE = Path.explode("api/submission/entry/notifies/remove")
    val API_SUBMISSION_ENTRY_RELATED_ADD = Path.explode("api/submission/entry/related/add")
    val API_SUBMISSION_ENTRY_RELATED_REMOVE = Path.explode("api/submission/entry/related/remove")
    val API_SUBMISSION_DOWNLOAD = Path.explode("api/download/patch")
    val API_SUBMISSION_DOWNLOAD_ZIP = Path.explode("api/download/archive.zip")
    val API_SUBMISSION_DOWNLOAD_TGZ = Path.explode("api/download/archive.tar.gz")
    val API_CSS = Path.explode("api/main.css")


    /* fields */

    val ABSTRACT = "abstract"
    val ADDRESS = "address"
    val AFFILIATION = "affiliation"
    val ARCHIVE = "archive"
    val AUTHOR = "author"
    val DATE = "date"
    val ENTRY = "entry"
    val ID = "id"
    val INPUT = "input"
    val KIND = "kind"
    val LICENSE = "license"
    val MESSAGE = "message"
    val NAME = "name"
    val NOTIFY = "notify"
    val ORCID = "orcid"
    val RELATED = "related"
    val STATUS = "status"
    val TITLE = "title"
    val TOPIC = "topic"


    /* utils */

    def keyed(id: String, value: String): String = "[" + id + "] " + value

    def author_string(author: Author): String = {
      val orcid =
        author.orcid.map(orcid => " (ORCID id: " + orcid.identifier + ")").getOrElse("")
      keyed(author.id, author.name) + orcid
    }

    def author_option(author: Author): XML.Elem = option(author.id, author_string(author))

    def affil_id(affil: Affiliation): String =
      affil match {
        case Unaffiliated(_) => ""
        case Email(_, id, _) => id
        case Homepage(_, id, _) => id
      }

    def affil_address(affil: Affiliation): String =
      affil match {
        case Unaffiliated(_) => ""
        case Email(_, _, address) => address
        case Homepage(_, _, url) => url.toString
      }

    def affil_string(affil: Affiliation): String =
      affil match {
        case Unaffiliated(_) => "No email or homepage"
        case Email(_, id, address) => keyed(id, address)
        case Homepage(_, id, url) => keyed(id, url.toString)
      }

    def related_string(related: Reference): String = related match {
      case Metadata.DOI(identifier) => identifier
      case Metadata.Formatted(rep) => rep
    }

    def indexed[A, B](l: List[A], key: Params.Key, field: String, f: (A, Params.Key) => B) =
      l.zipWithIndex map {
        case (a, i) => f(a, List_Key(key, field, i))
      }

    def fold[A](it: List[Params.Data], a: A)(f: (Params.Data, A) => Option[A]): Option[A] =
      it.foldLeft(Option(a)) {
        case (None, _) => None
        case (Some(a), param) => f(param, a)
      }

    def download_link(href: String, body: XML.Body): XML.Elem =
      class_("download")(link(href, body)) + ("target" -> "_blank")
    def frontend_link(path: Path, params: Properties.T, body: XML.Body): XML.Elem =
      link(api.app_url(path, params), body) + ("target" -> "_parent")

    def render_if(cond: Boolean, body: XML.Body): XML.Body = if (cond) body else Nil
    def render_if(cond: Boolean, elem: XML.Elem): XML.Body = if (cond) List(elem) else Nil
    def render_error(for_elem: String, validated: Val[_]): XML.Body =
      validated.err.map(error =>
        break ::: List(css("color: red")(label(for_elem, error)))).getOrElse(Nil)


    /* view */

    def render_create(model: Model.Create): XML.Body = {
      val updated_authors = model.updated_authors(authors)
      val authors_list = updated_authors.values.toList.sortBy(_.id)
      val (entry_authors, other_authors) =
        updated_authors.values.toList.sortBy(_.id).partition(author =>
          model.used_authors.contains(author.id))
      val email_authors = authors_list.filter(_.emails.nonEmpty)

      def render_topic(topic: Topic, key: Params.Key): XML.Elem =
        par(
          hidden(Nest_Key(key, ID), topic.id) ::
          text(topic.id) :::
          action_button(api.api_url(API_SUBMISSION_ENTRY_TOPICS_REMOVE), "x", key) :: Nil)

      def render_affil(affil: Affiliation, key: Params.Key): XML.Elem = {
        val author = updated_authors(affil.author)
        val affils = author.emails ::: author.homepages ::: Unaffiliated(author.id) :: Nil
        par(
          hidden(Nest_Key(key, ID), affil.author) ::
            text(author_string(updated_authors(affil.author))) :::
            selection(Nest_Key(key, AFFILIATION),
              Some(affil_id(affil)),
              affils.map(affil => option(affil_id(affil), affil_string(affil)))) ::
            action_button(api.api_url(API_SUBMISSION_ENTRY_AUTHORS_REMOVE), "x", key) :: Nil)
      }

      def render_notify(email: Email, key: Params.Key): XML.Elem = {
        val author = updated_authors(email.author)
        par(
          hidden(Nest_Key(key, ID), email.author) ::
            text(author_string(updated_authors(email.author))) :::
            selection(
              Nest_Key(key, AFFILIATION),
              Some(affil_id(email)),
              author.emails.map(affil => option(affil_id(affil), affil_string(affil)))) ::
            action_button(api.api_url(API_SUBMISSION_ENTRY_NOTIFIES_REMOVE), "x", key) :: Nil)
      }

      def render_related(related: Reference, key: Params.Key): XML.Elem =
        par(
          hidden(Nest_Key(key, KIND), Model.Related.get(related).toString) ::
          hidden(Nest_Key(key, INPUT), related_string(related)) ::
          text(related_string(related)) :::
          action_button(api.api_url(API_SUBMISSION_ENTRY_RELATED_REMOVE), "x", key) :: Nil)

      def render_entry(entry: Model.Create_Entry, key: Params.Key): XML.Elem =
        fieldset(legend("Entry") ::
          par(
            fieldlabel(Nest_Key(key, TITLE), "Title of article") ::
            textfield(Nest_Key(key, TITLE), "Example Submission", entry.title.v) ::
            render_error(Nest_Key(key, TITLE), entry.title)) ::
          par(
            fieldlabel(Nest_Key(key, NAME), "Short name") ::
            textfield(Nest_Key(key, NAME), "Example_Submission", entry.name.v) ::
            explanation(Nest_Key(key, NAME),
              "Name of the folder where your ROOT and theory files reside.") ::
            render_error(Nest_Key(key, NAME), entry.name)) ::
          fieldset(legend("Topics") ::
            indexed(entry.topics.v, key, TOPIC, render_topic) :::
            selection(Nest_Key(key, TOPIC),
              entry.topic_input.map(_.id),
              topics.map(topic => option(topic.id, topic.id))) ::
            action_button(api.api_url(API_SUBMISSION_ENTRY_TOPICS_ADD), "add", key) ::
            render_error("", entry.topics)) ::
          par(List(
            fieldlabel(Nest_Key(key, LICENSE), "License"),
            radio(Nest_Key(key, LICENSE),
              entry.license.id,
              licenses.values.toList.map(license => license.id -> license.name)),
            explanation(Nest_Key(key, LICENSE),
              "Note: For LGPL submissions, please include the header \"License: LGPL\" in each file"))) ::
          par(
            fieldlabel(Nest_Key(key, ABSTRACT), "Abstract") ::
            placeholder("HTML and MathJax, no LaTeX")(
              textarea(Nest_Key(key, ABSTRACT), entry.`abstract`.v) +
                ("rows" -> "8") +
                ("cols" -> "70")) ::
            explanation(Nest_Key(key, ABSTRACT),
              "Note: You can use HTML or MathJax (not LaTeX!) to format your abstract.") ::
            render_error(Nest_Key(key, ABSTRACT), entry.`abstract`)) ::
          fieldset(legend("Authors") ::
            indexed(entry.affils.v, key, AUTHOR, render_affil) :::
            selection(Nest_Key(key, AUTHOR),
              entry.author_input.map(_.id),
              authors_list.map(author => option(author.id, author_string(author)))) ::
            action_button(api.api_url(API_SUBMISSION_ENTRY_AUTHORS_ADD), "add", key) ::
            explanation(Nest_Key(key, AUTHOR),
              "Add an author from the list. Register new authors first below.") ::
            render_error(Nest_Key(key, AUTHOR), entry.affils)) ::
          fieldset(legend("Contact") ::
            indexed(entry.notifies.v, key, NOTIFY, render_notify) :::
            selection(Nest_Key(key, NOTIFY),
              entry.notify_input.map(_.id),
              optgroup("Suggested", email_authors.filter(author =>
                entry.used_authors.contains(author.id)).map(author_option)) ::
                email_authors.filter(author =>
                  !entry.used_authors.contains(author.id)).map(author_option)) ::
            action_button(api.api_url(API_SUBMISSION_ENTRY_NOTIFIES_ADD), "add", key) ::
            explanation(Nest_Key(key, NOTIFY),
              "These addresses serve two purposes: " +
              "1. They are used to send you updates about the state of your submission. " +
              "2. They are the maintainers of the entry once it is accepted. " +
              "Typically this will be one or more of the authors.") ::
            render_error("", entry.notifies)) ::
          fieldset(legend("Related Publications") ::
            indexed(entry.related, key, RELATED, render_related) :::
            selection(Nest_Key(Nest_Key(key, RELATED), KIND),
              entry.related_kind.map(_.toString),
              Model.Related.values.toList.map(v => option(v.toString, v.toString))) ::
            textfield(Nest_Key(Nest_Key(key, RELATED), INPUT),
              "10.1109/5.771073", entry.related_input.v) ::
            action_button(api.api_url(API_SUBMISSION_ENTRY_RELATED_ADD), "add", key) ::
            explanation(Nest_Key(Nest_Key(key, RELATED), INPUT),
              "Publications related to the entry, as DOIs (10.1109/5.771073) or plaintext (HTML)." +
              "Typically a publication by the authors describing the entry," +
              " background literature (articles, books) or web resources. ") ::
            render_error(Nest_Key(Nest_Key(key, RELATED), INPUT), entry.related_input)) ::
          render_if(mode == Mode.SUBMISSION,
            action_button(api.api_url(API_SUBMISSION_ENTRIES_REMOVE), "remove entry", key)))

      def render_new_author(author: Author, key: Params.Key): XML.Elem =
        par(
          hidden(Nest_Key(key, ID), author.id) ::
          hidden(Nest_Key(key, NAME), author.name) ::
          hidden(Nest_Key(key, ORCID), author.orcid.map(_.identifier).getOrElse("")) ::
          text(author_string(author)) :::
          render_if(!model.used_authors.contains(author.id),
            action_button(api.api_url(API_SUBMISSION_AUTHORS_REMOVE), "x", key)))

      def render_new_affil(affil: Affiliation, key: Params.Key): XML.Elem =
        par(
          hidden(Nest_Key(key, AUTHOR), affil.author) ::
          hidden(Nest_Key(key, ID), affil_id(affil)) ::
          hidden(Nest_Key(key, AFFILIATION), affil_address(affil)) ::
          text(author_string(updated_authors(affil.author)) + ": " + affil_string(affil)) :::
          render_if(!model.used_affils.contains(affil),
            action_button(api.api_url(API_SUBMISSION_AFFILIATIONS_REMOVE), "x", key)))

      val (upload, preview) = mode match {
        case Mode.EDIT => ("Save", "preview and save >")
        case Mode.SUBMISSION => ("Upload", "preview and upload >")
      }

      List(submit_form(api.api_url(API_SUBMISSION),
        indexed(model.entries.v, Params.empty, ENTRY, render_entry) :::
        render_error("", model.entries) :::
        render_if(mode == Mode.SUBMISSION,
          par(List(
            explanation("",
              "You can submit multiple entries at once. " +
              "Put the corresponding folders in the archive " +
              "and use the button below to add more input fields for metadata. "),
            api_button(api.api_url(API_SUBMISSION_ENTRIES_ADD), "additional entry")))) :::
        break :::
        fieldset(legend("New Authors") ::
          explanation("", "If you are new to the AFP, add yourself here.") ::
          indexed(model.new_authors.v, Params.empty, AUTHOR, render_new_author) :::
          fieldlabel(Nest_Key(AUTHOR, NAME), "Name") ::
          textfield(Nest_Key(AUTHOR, NAME), "Gerwin Klein", model.new_author_input) ::
          fieldlabel(Nest_Key(AUTHOR, ORCID), "ORCID id (optional)") ::
          textfield(Nest_Key(AUTHOR, ORCID), "0000-0002-1825-0097", model.new_author_orcid) ::
          api_button(api.api_url(API_SUBMISSION_AUTHORS_ADD), "add") ::
          render_error("", model.new_authors)) ::
        fieldset(legend("New email or homepage") ::
          explanation("",
            "Add new email or homepages here. " +
            "If you would like to update an existing, " +
            "submit with the old one and write to the editors.") ::
          indexed(model.new_affils.v, Params.empty, AFFILIATION, render_new_affil) :::
          fieldlabel(AFFILIATION, "Author") ::
          selection(AFFILIATION,
            model.new_affils_author.map(_.id),
            optgroup("Entry authors", entry_authors.map(author_option)) ::
              other_authors.map(author_option)) ::
          fieldlabel(Nest_Key(AFFILIATION, ADDRESS), "Email or Homepage") ::
          textfield(Nest_Key(AFFILIATION, ADDRESS), "https://proofcraft.org",
            model.new_affils_input) ::
          api_button(api.api_url(API_SUBMISSION_AFFILIATIONS_ADD), "add") ::
          render_error("", model.new_affils)) ::
        break :::
        fieldset(List(legend(upload),
          api_button(api.api_url(API_SUBMISSION_UPLOAD), preview))) :: Nil))
    }

    def render_metadata(meta: Model.Metadata): XML.Body = {
      def render_topic(topic: Topic, key: Params.Key): XML.Elem =
        item(hidden(Nest_Key(key, ID), topic.id) :: text(topic.id))

      def render_affil(affil: Affiliation, key: Params.Key): XML.Elem =
        item(
          hidden(Nest_Key(key, ID), affil.author) ::
          hidden(Nest_Key(key, AFFILIATION), affil_id(affil)) ::
          text(author_string(meta.authors(affil.author)) + ", " + affil_string(affil)))

      def render_related(related: Reference, key: Params.Key): XML.Elem =
        item(
          hidden(Nest_Key(key, KIND), Model.Related.get(related).toString) ::
          hidden(Nest_Key(key, INPUT), related_string(related)) ::
          unescape(related_string(related)))

      def render_entry(entry: Entry, key: Params.Key): XML.Elem =
        fieldset(List(
          legend("Entry"),
          par(
            fieldlabel(Nest_Key(key, TITLE), "Title") ::
            hidden(Nest_Key(key, TITLE), entry.title) ::
            text(entry.title)),
          par(
            fieldlabel(Nest_Key(key, NAME), "Short Name") ::
            hidden(Nest_Key(key, NAME), entry.name) ::
            text(entry.name)),
          par(
            fieldlabel(Nest_Key(key, DATE), "Date") ::
            hidden(Nest_Key(key, DATE), entry.date.toString) ::
            text(entry.date.toString)),
          par(List(
            fieldlabel("", "Topics"),
            list(indexed(entry.topics, key, TOPIC, render_topic)))),
          par(
            fieldlabel(Nest_Key(key, LICENSE), "License") ::
            hidden(Nest_Key(key, LICENSE), entry.license.id) ::
            text(entry.license.name)),
          par(List(
            fieldlabel(Nest_Key(key, ABSTRACT), "Abstract"),
            hidden(Nest_Key(key, ABSTRACT), entry.`abstract`),
            class_("mathjax_process")(span(unescape(entry.`abstract`))))),
          par(List(
            fieldlabel("", "Authors"),
            list(indexed(entry.authors, key, AUTHOR, render_affil)))),
          par(List(
            fieldlabel("", "Contact"),
            list(indexed(entry.notifies, key, NOTIFY, render_affil)))),
          par(List(
            fieldlabel("", "Related Publications"),
            list(indexed(entry.related, key, RELATED, render_related))))))

      def render_new_author(author: Author, key: Params.Key): XML.Elem =
        par(List(
          hidden(Nest_Key(key, ID), author.id),
          hidden(Nest_Key(key, NAME), author.name),
          hidden(Nest_Key(key, ORCID), author.orcid.map(_.identifier).getOrElse(""))))

      def render_new_affil(affil: Affiliation, key: Params.Key): XML.Elem =
        par(List(
          hidden(Nest_Key(key, AUTHOR), affil.author),
          hidden(Nest_Key(key, ID), affil_id(affil)),
          hidden(Nest_Key(key, AFFILIATION), affil_address(affil))))

      indexed(meta.entries, Params.empty, ENTRY, render_entry) :::
        indexed(meta.new_authors(authors).toList, Params.empty, AUTHOR, render_new_author) :::
        indexed(meta.new_affils(authors).toList, Params.empty, AFFILIATION, render_new_affil)
    }

    def render_submission(submission: Model.Submission): XML.Body = {
      def status_text(status: Option[Model.Status.Value]): String =
        status.map {
          case Model.Status.Submitted => "AFP editors notified."
          case Model.Status.Review => "Review in progress."
          case Model.Status.Added => "Added to the AFP."
          case Model.Status.Rejected => "Submission rejected."
        } getOrElse
          "Draft saved. Check the logs for errors and warnings, " +
          "and submit to editors once successfully built."

      val archive_url =
        if (handler.get_archive(submission.id).exists(_.get_ext == "zip"))
          API_SUBMISSION_DOWNLOAD_ZIP
        else API_SUBMISSION_DOWNLOAD_TGZ

      val resubmit = mode match {
        case Mode.EDIT => "Update"
        case Mode.SUBMISSION => "Resubmit"
      }

      List(submit_form(api.api_url(SUBMISSION, List(ID -> submission.id)),
        render_if(mode == Mode.SUBMISSION,
          download_link(api.api_url(archive_url, List(ID -> submission.id)), text("archive")) ::
          download_link(api.api_url(API_SUBMISSION_DOWNLOAD, List(ID -> submission.id)),
            text("metadata patch")) ::
          text(" (apply with: 'patch -p0 < FILE')")) :::
        render_if(mode == Mode.SUBMISSION, par(
          hidden(MESSAGE, submission.message) ::
          text("Comment: " + submission.message))) :::
        section("Metadata") ::
        render_metadata(submission.meta) :::
        section("Status") ::
        span(text(status_text(submission.status))) ::
        render_if(submission.build != Model.Build.Running,
          action_button(api.api_url(API_RESUBMIT), resubmit, submission.id)) :::
        render_if(submission.build == Model.Build.Running,
          action_button(api.api_url(API_BUILD_ABORT), "Abort build", submission.id)) :::
        render_if(submission.build == Model.Build.Success && submission.status.isEmpty,
          action_button(api.api_url(API_SUBMIT), "Send submission to AFP editors", submission.id)) :::
        render_if(mode == Mode.SUBMISSION,
          fieldset(legend("Build") ::
            bold(text(submission.build.toString)) ::
            par(text("Isabelle log:") ::: source(submission.log) :: Nil) ::
            Nil))))
    }

    def render_upload(upload: Model.Upload): XML.Body = {
      val submit = mode match {
        case Mode.EDIT => "save"
        case Mode.SUBMISSION => "submit"
      }

      List(submit_form(api.api_url(API_SUBMISSION), List(
        fieldset(legend("Overview") :: render_metadata(upload.meta)),
        fieldset(legend("Submit") ::
          api_button(api.api_url(API_SUBMISSION), "< edit metadata") ::
          render_if(mode == Mode.SUBMISSION, List(
            par(List(
              fieldlabel(MESSAGE, "Message for the editors (optional)"),
              textfield(MESSAGE, "", upload.message),
              explanation(
                MESSAGE,
                "Note: Anything special or noteworthy about your submission can be covered here. " +
                  "It will not become part of your entry. " +
                  "You're also welcome to leave suggestions for our AFP submission service here. ")
            )),
            par(List(
              fieldlabel(ARCHIVE, "Archive file (.tar.gz or .zip)"),
              browse(ARCHIVE, List(".zip", ".tar.gz")),
              explanation(ARCHIVE,
                "Note: Your zip or tar file must contain exactly one folder for each entry with your theories, ROOT, etc. " +
                "The folder name must be the short/folder name used in the submission form. " +
                "Hidden files and folders (e.g., __MACOSX) are not allowed."))))) :::
          api_button(api.api_url(API_SUBMISSION_CREATE), submit) ::
          render_error(ARCHIVE, Val.err((), upload.error))))))
    }

    def render_submission_list(submission_list: Model.Submission_List): XML.Body = {
      def render_overview(overview: Model.Overview, key: Params.Key): XML.Elem =
        item(
          hidden(Nest_Key(key, ID), overview.id) ::
          hidden(Nest_Key(key, DATE), overview.date.toString) ::
          hidden(Nest_Key(key, NAME), overview.name) ::
          span(text(overview.date.toString)) ::
          span(List(frontend_link(SUBMISSION, List(ID -> overview.id),
            text(overview.name)))) ::
          render_if(mode == Mode.SUBMISSION,
            class_("right")(span(List(
              selection(Nest_Key(key, STATUS), Some(overview.status.toString),
                Model.Status.values.toList.map(v => option(v.toString, v.toString))),
              action_button(api.api_url(API_SUBMISSION_STATUS), "update", key))))))

      def list1(ls: List[XML.Elem]): XML.Elem = if (ls.isEmpty) par(Nil) else list(ls)

      val ls = indexed(submission_list.submissions, Params.empty, ENTRY, (o, k) => (o, k))
      val finished =
        ls.filter(t => Set(Model.Status.Added, Model.Status.Rejected).contains(t._1.status))

      List(submit_form(api.api_url(API_SUBMISSION_STATUS),
        render_if(mode == Mode.SUBMISSION,
          text("Open") :::
          list1(ls.filter(_._1.status == Model.Status.Submitted).map(render_overview)) ::
          text("In Progress") :::
          list1(ls.filter(_._1.status == Model.Status.Review).map(render_overview)) ::
          text("Finished")) :::
        list1(finished.map(render_overview)) :: Nil))
    }

    def render_created(created: Model.Created): XML.Body = {
      val status = mode match {
        case Mode.SUBMISSION => "View your submission status: "
        case Mode.EDIT => "View the entry at: "
      }

      List(div(
        span(text("Entry successfully saved. " + status)) ::
        break :::
        frontend_link(SUBMISSION, List(ID -> created.id),
          text(api.app_url(SUBMISSION, List(ID -> created.id)))) ::
        break :::
        render_if(mode == Mode.SUBMISSION, span(text("(keep that url!).")))))
    }

    def render_invalid: XML.Body =
      text("Invalid request")

    def render(model: Model.T): XML.Body =
      model match {
        case create: Model.Create => render_create(create)
        case upload: Model.Upload => render_upload(upload)
        case submission: Model.Submission => render_submission(submission)
        case submissions: Model.Submission_List => render_submission_list(submissions)
        case created: Model.Created => render_created(created)
        case Model.Invalid => render_invalid
      }


    /* validation */

    def validate_topic(id: String, selected: List[Topic]): Val_Opt[Topic] =
      if (id.isEmpty) Val_Opt.user_err("Select topic first")
      else {
        topics.find(_.id == id) match {
          case Some(topic) =>
            if (selected.contains(topic)) Val_Opt.user_err("Topic already selected")
            else Val_Opt.ok(topic)
          case _ => Val_Opt.error
        }
      }

    def validate_new_author(
      id: String,
      name: String,
      orcid_str: String,
      authors: Map[Author.ID, Author]
    ): Val_Opt[Author] = {
      val Id = """[a-zA-Z][a-zA-Z0-9]*""".r
      id match {
        case Id() if !authors.contains(id) =>
          if (name.isEmpty || name.trim != name)
            Val_Opt.user_err("Name must not be empty")
          else if (orcid_str.isEmpty)
            Val_Opt.ok(Author(id, name))
          else Exn.capture(Orcid(orcid_str)) match {
            case Exn.Res(orcid) =>
              if (authors.values.exists(_.orcid.exists(_ == orcid)))
                Val_Opt.user_err("Author with that orcid already exists")
              else Val_Opt.ok(Author(id, name, orcid = Some(orcid)))
            case _ => Val_Opt.user_err("Invalid orcid")
          }
        case _ => Val_Opt.error
      }
    }

    def validate_new_affil(id: String, address: String, author: Author): Val_Opt[Affiliation] = {
      if (address.isBlank) Val_Opt.user_err("Address must not be empty")
      else if (address.contains("@")) {
        val Id = (author.id + """_email\d*""").r
        id match {
          case Id() if !author.emails.map(_.id).contains(id) =>
            val Address = """([^@\s]+)@([^@\s]+)""".r
            address match {
              case Address(user, host) => Val_Opt.ok(Email(author.id, id, user, host))
              case _ => Val_Opt.user_err("Invalid email address")
            }
          case _ => Val_Opt.error
        }
      }
      else {
        val Id = (author.id + """_homepage\d*""").r
        id match {
          case Id() if !author.homepages.map(_.id).contains(id) =>
            if (Url.is_wellformed(address)) Val_Opt.ok(Homepage(author.id, id, Url(address)))
            else Val_Opt.user_err("Invalid url")
          case _ => Val_Opt.error
        }
      }
    }

    def validate_related(
      kind: Model.Related.Value,
      related: String,
      references: List[Reference]
    ): Val_Opt[Reference] =
      if (related.isBlank) Val_Opt.user_err("Reference must not be empty")
      else {
        kind match {
          case Model.Related.DOI =>
            Exn.capture(DOI(related)) match {
              case Exn.Res(doi) =>
                if (references.contains(doi)) Val_Opt.user_err("Already present")
                else Val_Opt.ok(doi)
              case _ => Val_Opt.user_err("Invalid DOI format")
            }
          case Model.Related.Plaintext =>
            val formatted = Formatted(related)
            if (references.contains(formatted)) Val_Opt.user_err("Already present")
            else Val_Opt.ok(formatted)
        }
      }


    /* param parsing */

    def parse_create(params: Params.Data): Option[Model.Create] = {
      def parse_topic(topic: Params.Data, topics: List[Topic]): Option[Topic] =
        validate_topic(topic.get(ID).value, topics).opt

      def parse_email(email: Params.Data, authors: Map[Author.ID, Author]): Option[Email] =
        authors.get(email.get(ID).value).flatMap(
          _.emails.find(_.id == email.get(AFFILIATION).value))

      def parse_affil(affil: Params.Data, authors: Map[Author.ID, Author]): Option[Affiliation] =
        authors.get(affil.get(ID).value).flatMap { author =>
          val id = affil.get(AFFILIATION).value
          if (id.isEmpty) Some(Unaffiliated(author.id))
          else (author.emails ++ author.homepages).collectFirst {
            case e: Email if e.id == id => e
            case h: Homepage if h.id == id => h
          }
        }

      def parse_related(related: Params.Data, references: List[Reference]): Option[Reference] =
        Model.Related.from_string(related.get(KIND).value).flatMap(
          validate_related(_, related.get(INPUT).value, references).opt)

      def parse_new_author(author: Params.Data, authors: Map[Author.ID, Author]): Option[Author] =
        validate_new_author(
          author.get(ID).value, author.get(NAME).value, author.get(ORCID).value, authors).opt

      def parse_new_affil(affil: Params.Data, authors: Map[Author.ID, Author]): Option[Affiliation] =
        authors.get(affil.get(AUTHOR).value).flatMap(author =>
          validate_new_affil(affil.get(ID).value, affil.get(AFFILIATION).value, author).opt)

      def parse_entry(entry: Params.Data, authors: Map[Author.ID, Author]): Option[Model.Create_Entry] =
        for {
          topics <-
            fold(entry.list(TOPIC), List.empty[Topic]) {
              case (topic, topics) => parse_topic(topic, topics).map(topics :+ _)
            }
          affils <-
            fold(entry.list(AUTHOR), List.empty[Affiliation]) {
              case (affil, affils) => parse_affil(affil, authors).map(affils :+ _)
            }
          notifies <-
            fold(entry.list(NOTIFY), List.empty[Email]) {
              case (email, emails) => parse_email(email, authors).map(emails :+ _)
            }
          related <-
            fold(entry.list(RELATED), List.empty[Reference]) {
              case (related, references) => parse_related(related, references).map(references :+ _)
            }
          license <- licenses.get(entry.get(LICENSE).value)
        } yield Model.Create_Entry(
          name = Val.ok(entry.get(NAME).value),
          title = Val.ok(entry.get(TITLE).value),
          topics = Val.ok(topics),
          topic_input = parse_topic(entry.get(TOPIC), Nil),
          license = license,
          `abstract` = Val.ok(entry.get(ABSTRACT).value),
          author_input = authors.get(entry.get(AUTHOR).value),
          notify_input = authors.get(entry.get(NOTIFY).value),
          affils = Val.ok(affils),
          notifies = Val.ok(notifies),
          related = related,
          related_kind = Model.Related.from_string(entry.get(RELATED).get(KIND).value),
          related_input = Val.ok(entry.get(RELATED).get(INPUT).value))

      for {
        (new_author_ids, all_authors) <-
          fold(params.list(AUTHOR), (List.empty[Author.ID], authors)) {
            case (author, (new_authors, authors)) =>
              parse_new_author(author, authors).map(author =>
                (new_authors :+ author.id, authors.updated(author.id, author)))
          }
        (new_affils, all_authors) <-
          fold(params.list(AFFILIATION), (List.empty[Affiliation], all_authors)) {
            case (affil, (new_affils, authors)) =>
              parse_new_affil(affil, authors).map { affil =>
                val author = authors(affil.author)
                (new_affils :+ affil, affil match {
                  case _: Unaffiliated => authors
                  case e: Email =>
                    authors.updated(author.id, author.copy(emails = author.emails :+ e))
                  case h: Homepage =>
                    authors.updated(author.id, author.copy(homepages = author.homepages :+ h))
                })
              }
            }
        new_authors = new_author_ids.map(all_authors)
        entries <- fold(params.list(ENTRY), List.empty[Model.Create_Entry]) {
          case (entry, entries) => parse_entry(entry, all_authors).map(entries :+ _)
        }
      } yield Model.Create(
        entries = Val.ok(entries),
        new_authors = Val.ok(new_authors),
        new_author_input = params.get(AUTHOR).get(NAME).value,
        new_author_orcid = params.get(AUTHOR).get(ORCID).value,
        new_affils = Val.ok(new_affils),
        new_affils_author = all_authors.get(params.get(AFFILIATION).value),
        new_affils_input = params.get(AFFILIATION).get(ADDRESS).value)
    }

    def parse_submission_list(params: Params.Data): Option[Model.Submission_List] = {
      def parse_overview(entry: Params.Data): Option[Model.Overview] =
        for {
          date <-
            Exn.capture(LocalDate.parse(entry.get(DATE).value)) match {
              case Exn.Res(date) => Some(date)
              case Exn.Exn(_) => None
            }
          status <- Model.Status.from_string(entry.get(STATUS).value)
        } yield Model.Overview(entry.get(ID).value, date, entry.get(NAME).value, status)

      val submissions =
        fold(params.list(ENTRY), List.empty[Model.Overview]) {
          case (entry, overviews) => parse_overview(entry).map(overviews :+ _)
        }
      submissions.map(Model.Submission_List.apply)
    }

    /* control */

    def add_entry(params: Params.Data): Option[Model.T] = parse_create(params).map { model =>
      model.copy(entries = Val.ok(model.entries.v :+ Model.Create_Entry(license = licenses.head._2)))
    }

    def remove_entry(params: Params.Data): Option[Model.T] =
      for {
        model <- parse_create(params)
        num_entry <- List_Key.num(ENTRY, params.get(Web_App.ACTION).value)
      } yield model.copy(entries = Val.ok(Utils.remove_at(num_entry, model.entries.v)))

    def add_author(params: Params.Data): Option[Model.T] =
      for {
        model <- parse_create(params)
        num_entry <- List_Key.num(ENTRY, params.get(Web_App.ACTION).value)
        entry <- model.entries.v.unapply(num_entry)
      } yield
        entry.author_input match {
          case None =>
            model.update_entry(num_entry, entry.copy(
              affils = entry.affils.with_err("Select author first")))
          case Some(author) =>
            val default_affil = author.emails.headOption.orElse(
              author.homepages.headOption).getOrElse(Unaffiliated(author.id))

            model.update_entry(num_entry, entry.copy(
              author_input = None, affils = Val.ok(entry.affils.v :+ default_affil)))
        }

    def remove_author(params: Params.Data): Option[Model.T] =
      for {
        model <- parse_create(params)
        (action, num_affil) <- List_Key.split(AUTHOR, params.get(Web_App.ACTION).value)
        num_entry <- List_Key.num(ENTRY, action)
        entry <- model.entries.v.unapply(num_entry)
      } yield
        model.update_entry(num_entry, entry.copy(affils =
          Val.ok(Utils.remove_at(num_affil, entry.affils.v))))

    def add_notify(params: Params.Data): Option[Model.T] =
      for {
        model <- parse_create(params)
        num_entry <- List_Key.num(ENTRY, params.get(Web_App.ACTION).value)
        entry <- model.entries.v.unapply(num_entry)
        entry1 <-
          entry.notify_input match {
            case Some(author) =>
              author.emails.headOption.map(email => entry.copy(
                notify_input = None, notifies = Val.ok(entry.notifies.v :+ email)))
            case None =>
              Some(entry.copy(notifies = entry.notifies.with_err("Select author first")))
          }
      } yield model.update_entry(num_entry, entry1)

    def remove_notify(params: Params.Data): Option[Model.T] =
      for {
        model <- parse_create(params)
        (action, num_notify) <- List_Key.split(NOTIFY, params.get(Web_App.ACTION).value)
        num_entry <- List_Key.num(ENTRY, action)
        entry <- model.entries.v.unapply(num_entry)
      } yield
        model.update_entry(num_entry, entry.copy(notifies =
          Val.ok(Utils.remove_at(num_notify, entry.notifies.v))))

    def add_topic(params: Params.Data): Option[Model.T] =
      for {
        model <- parse_create(params)
        num_entry <- List_Key.num(ENTRY, params.get(Web_App.ACTION).value)
        entry <- model.entries.v.unapply(num_entry)
        entry_params <- params.list(ENTRY).unapply(num_entry)
      } yield {
        val topic = validate_topic(entry_params.get(TOPIC).value, entry.topics.v)
        val topic_input = if (topic.is_empty) entry.topic_input else None
        model.update_entry(num_entry, entry.copy(
          topic_input = topic_input,
          topics = Val.ok(entry.topics.v ++ topic.opt).perhaps_err(topic)))
      }

    def remove_topic(params: Params.Data): Option[Model.T] =
      for {
        model <- parse_create(params)
        (action, num_topic) <- List_Key.split(TOPIC, params.get(Web_App.ACTION).value)
        num_entry <- List_Key.num(ENTRY, action)
        entry <- model.entries.v.unapply(num_entry)
      } yield {
        val entry1 = entry.copy(topics = Val.ok(Utils.remove_at(num_topic, entry.topics.v)))
        model.copy(entries = Val.ok(model.entries.v.updated(num_entry, entry1)))
      }

    def add_related(params: Params.Data): Option[Model.T] =
      for {
        model <- parse_create(params)
        num_entry <- List_Key.num(ENTRY, params.get(Web_App.ACTION).value)
        entry <- model.entries.v.unapply(num_entry)
      } yield {
        val entry1 =
          entry.related_kind match {
            case None =>
              entry.copy(related_input =
                entry.related_input.with_err("Select reference kind first"))
            case Some(kind) =>
              val reference = validate_related(kind, entry.related_input.v, entry.related)
              val related_input = if (reference.is_empty) entry.related_input.v else ""
              entry.copy(
                related = entry.related ++ reference.opt,
                related_input = Val.ok(related_input).perhaps_err(reference))
          }
        model.update_entry(num_entry, entry1)
      }

    def remove_related(params: Params.Data): Option[Model.T] =
      for {
        model <- parse_create(params)
        (action, num_related) <- List_Key.split(RELATED, params.get(Web_App.ACTION).value)
        num_entry <- List_Key.num(ENTRY, action)
        entry <- model.entries.v.unapply(num_entry)
      } yield {
        val entry1 = entry.copy(related = Utils.remove_at(num_related, entry.related))
        model.copy(entries = Val.ok(model.entries.v.updated(num_entry, entry1)))
      }

    def add_new_author(params: Params.Data): Option[Model.T] = parse_create(params).map { model =>
      val name = model.new_author_input.trim
      if (name.isEmpty)
        model.copy(new_authors = model.new_authors.with_err("Name must not be empty"))
      else {
        def as_ascii(str: String) = {
          var res: String = str
          List("ö" -> "oe", "ü" -> "ue", "ä" -> "ae", "ß" -> "ss").foreach {
            case (c, rep) => res = res.replace(c, rep)
          }
          Normalizer.normalize(res, Normalizer.Form.NFD).replaceAll("[^\\x00-\\x7F]", "")
        }

        def make_author_id(name: String): String = {
          val normalized = as_ascii(name)
          val Suffix = """^.*?([a-zA-Z]*)$""".r
          val suffix = normalized match {
            case Suffix(suffix) => suffix
            case _ => ""
          }
          val Prefix = """^([a-zA-Z]*).*$""".r
          val prefix = normalized.stripSuffix(suffix) match {
            case Prefix(prefix) => prefix
            case _ => ""
          }
          val updated_authors = model.updated_authors(authors)

          var ident = suffix.toLowerCase
          for {
            c <- prefix.toLowerCase
            if updated_authors.contains(ident)
          } ident += c.toString

          Utils.make_unique(ident, updated_authors.keySet)
        }

        val id = make_author_id(name)

        val author = validate_new_author(id, model.new_author_input, model.new_author_orcid,
          model.updated_authors(authors))
        val new_author_input = if (author.is_empty) model.new_author_input else ""
        val new_author_orcid = if (author.is_empty) model.new_author_orcid else ""

        model.copy(
          new_author_input = new_author_input,
          new_author_orcid = new_author_orcid,
          new_authors = Val.ok(model.new_authors.v ++ author.opt).perhaps_err(author))
      }
    }

    def remove_new_author(params: Params.Data): Option[Model.T] =
      for {
        model <- parse_create(params)
        num_author <- List_Key.num(AUTHOR, params.get(Web_App.ACTION).value)
        author <- model.new_authors.v.unapply(num_author)
        if !model.used_authors.contains(author.id)
      } yield model.copy(new_authors =
        Val.ok(Utils.remove_at(num_author, model.new_authors.v)))

    def add_new_affil(params: Params.Data): Option[Model.T] =
      parse_create(params).map { model =>
        model.new_affils_author match {
          case Some(author) =>
            val address = model.new_affils_input.trim
            if (address.isEmpty)
              model.copy(new_affils = model.new_affils.with_err("Must not be empty"))
            else {
              val id =
                if (address.contains("@"))
                  Utils.make_unique(author.id + "_email", author.emails.map(_.id).toSet)
                else
                  Utils.make_unique(author.id + "_homepage", author.homepages.map(_.id).toSet)

              val affil = validate_new_affil(id, address, author)
              val new_affils_input = if (affil.is_empty) model.new_affils_input else ""
              model.copy(
                new_affils_input = new_affils_input,
                new_affils = Val.ok(model.new_affils.v ++ affil.opt).perhaps_err(affil))
            }
          case None => model.copy(new_affils = model.new_affils.with_err("Select author first"))
        }
      }

    def remove_new_affil(params: Params.Data): Option[Model.T] =
      for {
        model <- parse_create(params)
        num_affil <- List_Key.num(AFFILIATION, params.get(Web_App.ACTION).value)
        affil <- model.new_affils.v.unapply(num_affil)
        if !model.used_affils.contains(affil)
      } yield model.copy(new_affils = Val.ok(Utils.remove_at(num_affil, model.new_affils.v)))

    def upload(params: Params.Data): Option[Model.T] = parse_create(params).map { create =>
      var ok = true

      def validate[A](validator: A => Val[A], value: A): Val[A] = {
        val res = validator(value)
        if (res.err.nonEmpty) ok = false
        res
      }

      def title(title: String): Val[String] =
        if (title.isBlank) Val.err(title, "Title must not be blank")
        else if (title.trim != title) Val.err(title, "Title must not contain extra spaces")
        else Val.ok(title)

      def name(name: String): Val[String] =
        if (name.isBlank) Val.err(name, "Name must not be blank")
        else if (!"[a-zA-Z0-9_-]+".r.matches(name)) Val.err(name,
          "Invalid character in name")
        else mode match {
          case Mode.EDIT =>
            if (Server.this.entries.contains(name)) Val.ok(name)
            else Val.err(name, "Entry does not exist")
          case Mode.SUBMISSION =>
            if (Server.this.entries.contains(name)) Val.err(name, "Entry already exists")
            else Val.ok(name)
        }

      def entries(entries: List[Model.Create_Entry]): Val[List[Model.Create_Entry]] =
        if (entries.isEmpty) Val.err(entries, "Must contain at least one entry")
        else if (Library.duplicates(entries.map(_.name)).nonEmpty)
          Val.err(entries, "Entries must have different names")
        else Val.ok(entries)

      def new_authors(authors: List[Author]): Val[List[Author]] =
        if (!authors.forall(author => create.used_authors.contains(author.id)))
          Val.err(authors, "Unused authors")
        else Val.ok(authors)

      def new_affils(affils: List[Affiliation]): Val[List[Affiliation]] =
        if (!affils.forall(affil => create.used_affils.contains(affil)))
          Val.err(affils, "Unused affils")
        else Val.ok(affils)

      def entry_authors(authors: List[Affiliation]): Val[List[Affiliation]] =
        if (authors.isEmpty) Val.err(authors, "Must contain at least one author")
        else if (!Utils.is_distinct(authors)) Val.err(authors, "Duplicate affiliations")
        else Val.ok(authors)

      def notifies(notifies: List[Email]): Val[List[Email]] =
        if (notifies.isEmpty) Val.err(notifies, "Must contain at least one maintainer")
        else if (!Utils.is_distinct(notifies)) Val.err(notifies, "Duplicate emails")
        else Val.ok(notifies)

      def topics(topics: List[Topic]): Val[List[Topic]] =
        if (topics.isEmpty) Val.err(topics, "Must contain at least one topic") else Val.ok(topics)

      def `abstract`(txt: String): Val[String] =
        if (txt.isBlank) Val.err(txt, "Entry must contain an abstract")
        else if (List("\\cite", "\\emph", "\\texttt").exists(txt.contains(_)))
          Val.err(txt, "LaTeX not allowed, use MathJax for math symbols")
        else Val.ok(txt)

      val validated = create.copy(
        entries = validate(
          entries, create.entries.v.map(entry => entry.copy(
            name = validate(name, entry.name.v),
            title = validate(title, entry.title.v),
            affils = validate(entry_authors, entry.affils.v),
            notifies = validate(notifies, entry.notifies.v),
            topics = validate(topics, entry.topics.v),
            `abstract` = validate(`abstract`, entry.`abstract`.v)
          ))),
        new_authors = validate(new_authors, create.new_authors.v),
        new_affils = validate(new_affils, create.new_affils.v))

      if (ok) {
        val (updated_authors, entries) = create.create(authors)
        Model.Upload(Model.Metadata(updated_authors, entries), params.get(MESSAGE).value, "")
      } else validated
    }

    def create(params: Params.Data): Option[Model.T] = {
      upload(params) match {
        case Some(upload: Model.Upload) =>
          mode match {
            case Mode.EDIT =>
              handler.create(Date.now(), upload.meta, upload.message, Bytes.empty, "")
              Some(Model.Created(upload.meta.entries.head.name))
            case Mode.SUBMISSION =>
              val archive = Bytes.decode_base64(params.get(ARCHIVE).get(FILE).value)
              val file_name = params.get(ARCHIVE).value

              if (archive.is_empty || file_name.isEmpty) {
                Some(upload.copy(error = "Select a file"))
              } else if (!file_name.endsWith(".zip") && !file_name.endsWith(".tar.gz")) {
                Some(upload.copy(error = "Only .zip and .tar.gz archives allowed"))
              } else {
                val ext = if (file_name.endsWith(".zip")) ".zip" else ".tar.gz"
                val id = handler.create(Date.now(), upload.meta, upload.message, archive, ext)
                Some(Model.Created(id))
              }
          }
        case _ => None
      }
    }

    def empty_submission: Option[Model.T] =
      Some(Model.Create(entries =
        Val.ok(List(Model.Create_Entry(license = licenses.head._2)))))

    def get_submission(props: Properties.T): Option[Model.Submission] =
      Properties.get(props, ID).flatMap(handler.get(_, all_topics, licenses))

    def resubmit(params: Params.Data): Option[Model.T] =
      handler.get(params.get(ACTION).value, all_topics, licenses).map(submission =>
        Model.Upload(submission.meta, submission.message, ""))

    def submit(params: Params.Data): Option[Model.T] =
      handler.get(params.get(ACTION).value, all_topics, licenses).flatMap { submission =>
        if (submission.status.nonEmpty) None
        else {
          handler.submit(submission.id)
          Some(submission.copy(status = Some(Model.Status.Submitted)))
        }
      }

    def abort_build(params: Params.Data): Option[Model.T] =
      handler.get(params.get(ACTION).value, all_topics, licenses).flatMap { submission =>
        if (submission.build != Model.Build.Running) None
        else {
          handler.abort_build(submission.id)
          Some(submission.copy(build = Model.Build.Aborted))
        }
      }

    def set_status(params: Params.Data): Option[Model.T] = {
      for {
        list <- parse_submission_list(params)
        num_entry <- List_Key.num(ENTRY, params.get(ACTION).value)
        changed <- list.submissions.unapply(num_entry)
      } yield {
        if (changed.status == Model.Status.Added && !devel) {
          progress.echo_if(verbose, "Updating server data...")
          val id_before = repo.id()
          repo.pull()
          repo.update()
          val id_after = repo.id()
          if (id_before != id_after) {
            load()
            progress.echo("Updated repo from " + id_before + " to " + id_after)
          }
        }
        handler.set_status(changed.id, changed.status)
        list
      }
    }

    def submission_list: Option[Model.T] = Some(handler.list())

    def download(props: Properties.T): Option[Path] =
      Properties.get(props, ID).flatMap(handler.get_patch)

    def download_archive(props: Properties.T): Option[Path] =
      Properties.get(props, ID).flatMap(handler.get_archive)

    def style_sheet: Option[Path] =
      Some(afp_structure.base_dir + Path.make(List("tools", "main.css")))

    val error_model = Model.Invalid

    val endpoints = List(
      Get(SUBMIT, "empty submission form", _ => empty_submission),
      Get(SUBMISSION, "get submission", get_submission),
      Get(SUBMISSIONS, "list submissions", _ => submission_list),
      Get_File(API_SUBMISSION_DOWNLOAD, "download patch", download),
      Get_File(API_SUBMISSION_DOWNLOAD_ZIP, "download archive", download_archive),
      Get_File(API_SUBMISSION_DOWNLOAD_TGZ, "download archive", download_archive),
      Get_File(API_CSS, "download css", _ => style_sheet),
      Post(API_RESUBMIT, "get form for resubmit", resubmit),
      Post(API_SUBMIT, "submit to editors", submit),
      Post(API_BUILD_ABORT, "abort the build", abort_build),
      Post(API_SUBMISSION, "get submission form", parse_create),
      Post(API_SUBMISSION_AUTHORS_ADD, "add author",  add_new_author),
      Post(API_SUBMISSION_AUTHORS_REMOVE, "remove author", remove_new_author),
      Post(API_SUBMISSION_AFFILIATIONS_ADD, "add affil", add_new_affil),
      Post(API_SUBMISSION_AFFILIATIONS_REMOVE, "remove affil", remove_new_affil),
      Post(API_SUBMISSION_ENTRIES_ADD, "add entry", add_entry),
      Post(API_SUBMISSION_ENTRIES_REMOVE, "remove entry", remove_entry),
      Post(API_SUBMISSION_ENTRY_AUTHORS_ADD, "add entry author", add_author),
      Post(API_SUBMISSION_ENTRY_AUTHORS_REMOVE, "remove entry author", remove_author),
      Post(API_SUBMISSION_ENTRY_NOTIFIES_ADD, "add notify", add_notify),
      Post(API_SUBMISSION_ENTRY_NOTIFIES_REMOVE, "remove notify", remove_notify),
      Post(API_SUBMISSION_ENTRY_TOPICS_ADD, "add topic", add_topic),
      Post(API_SUBMISSION_ENTRY_TOPICS_REMOVE, "remove topic", remove_topic),
      Post(API_SUBMISSION_ENTRY_RELATED_ADD, "add related", add_related),
      Post(API_SUBMISSION_ENTRY_RELATED_REMOVE, "remove related", remove_related),
      Post(API_SUBMISSION_UPLOAD, "upload archive", upload),
      Post(API_SUBMISSION_CREATE, "create submission", create),
      Post(API_SUBMISSION_STATUS, "set submission status", set_status))

    val head =
      List(
        XML.Elem(Markup("script", List(
          "type" -> "text/javascript",
          "id" -> "MathJax-script",
          "async" -> "async",
          "src" -> "https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-svg.js")), text("\n")),
        script(
          "MathJax={tex:{inlineMath:[['$','$'],['\\\\(','\\\\)']]},processEscapes:true,svg:{fontCache:'global'}}"),
        style_file(api.api_url(API_CSS)))
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("afp_submit", "start afp submission server",
    Scala_Project.here,
    { args =>

      var backend_path = Path.current
      var frontend_url = Url("http://localhost:8080")
      var devel = false
      var verbose = false
      var port = 8080
      var dir: Option[Path] = None

      val getopts = Getopts("""
Usage: isabelle afp_submit [OPTIONS]

  Options are:
      -a PATH      backend path (if endpoint is not server root)
      -b URL       application frontend url. Default: """ + frontend_url + """"
      -d           devel mode (serves frontend and skips automatic AFP repository updates)
      -p PORT      server port. Default: """ + port + """
      -v           verbose
      -D DIR       submission directory

  Start afp submission server. Server is in "edit" mode
  unless directory to store submissions in is specified.
""",
        "a:" -> (arg => backend_path = Path.explode(arg)),
        "b:" -> (arg => frontend_url = Url(arg)),
        "d" -> (_ => devel = true),
        "p:" -> (arg => port = Value.Int.parse(arg)),
        "v" -> (_ => verbose = true),
        "D:" -> (arg => dir = Some(Path.explode(arg))))

      getopts(args)

      val afp_structure = AFP_Structure()

      val progress = new Console_Progress(verbose = verbose)

      val (handler, mode) = dir match {
        case Some(dir) => (Handler.Adapter(dir, afp_structure), Mode.SUBMISSION)
        case None => (Handler.Edit(afp_structure), Mode.EDIT)
      }

      val api = new API(frontend_url, backend_path, devel = devel)
      val server = new Server(api = api, afp_structure = afp_structure, mode = mode,
        handler = handler, devel = devel, verbose = verbose, progress = progress, port = port)

      server.run()
    })
}

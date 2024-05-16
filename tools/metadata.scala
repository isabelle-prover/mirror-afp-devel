/* Author: Fabian Huch, TU Muenchen

AFP metadata model and TOML serialization.
 */
package afp


import isabelle.*

import java.time.LocalDate
import java.net.URI

import scala.collection.immutable.ListMap


object Metadata {
  /* affiliations */

  sealed trait Affiliation { def author: Author.ID }

  case class Unaffiliated(override val author: Author.ID)
    extends Affiliation

  case class Email(override val author: Author.ID, id: Email.ID, address: String)
    extends Affiliation {

    private val Address = "([^@]+)@(.+)".r
    val (user, host) = address match {
      case Address(user, host) => (user, host)
      case _ => error("Invalid address: " + address)
    }
  }

  object Email {
    type ID = String

    def apply(author: Author.ID, id: Email.ID, user: String, host: String): Email =
      Email(author, id, user + "@" + host)
  }

  case class Homepage(override val author: Author.ID, id: Homepage.ID, url: Url) extends Affiliation

  object Homepage { type ID = String }


  /* authors */

  case class Orcid(identifier: String) {
    require(
      "^([0-9]{4})-([0-9]{4})-([0-9]{4})-([0-9]{3}[0-9X])$".r.matches(identifier),
      "Invalid format for orcid: " + quote(identifier))

    def url: Url = Url("https://orcid.org/" + identifier)
  }

  case class Author(
    id: Author.ID,
    name: String,
    emails: List[Email] = Nil,
    homepages: List[Homepage] = Nil,
    orcid: Option[Orcid] = None
  )

  object Author { type ID = String }

  type Authors = ListMap[Author.ID, Author]
  object Authors {
    def empty: Authors = Authors(Nil)
    def apply(authors: List[Author]): Authors =
      ListMap.from(authors.map(author => author.id -> author))
  }


  /* topics */

  sealed trait Classification {
    def desc: String
    def url: Url
  }

  case class ACM(id: String, override val desc: String) extends Classification {
    val url = Url("https://dl.acm.org/topic/ccs2012/" + id)
  }

  case class AMS(id: String, hierarchy: List[String]) extends Classification {
    val code: String = id.length match {
      case 2 => id + "-XX"
      case 3 => id + "xx"
      case 5 => id
      case _ => error("Invalid ams id:" + id)
    }
    override val desc: String = hierarchy.mkString(" / ")
    override val url: Url = Url("https://mathscinet.ams.org/mathscinet/msc/msc2020.html?t=" + code)
  }

  case class Topic(
    id: Topic.ID,
    name: String,
    classification: List[Classification] = Nil,
    sub_topics: List[Topic] = Nil
  ) {
    def all_topics: List[Topic] = this :: sub_topics.flatMap(_.all_topics)
  }

  object Topic { type ID = String }

  type Topics = ListMap[Topic.ID, Topic]
  object Topics {
    def empty: Topics = Topics(Nil)
    def apply(root_topics: List[Topic]): Topics =
      ListMap.from(root_topics.flatMap(_.all_topics).map(topic => topic.id -> topic))
    
    def root_topics(topics: Topics): List[Topic] = {
      val sub_topics = topics.values.flatMap(_.sub_topics).map(_.id).toSet
      topics.values.filterNot(topic => sub_topics.contains(topic.id)).toList
    }
  }


  /* releases */

  type Date = LocalDate

  object Isabelle { type Version = String }

  case class Release(entry: Entry.Name, date: Date, isabelle: Isabelle.Version)

  type Releases = ListMap[Entry.Name, List[Release]]
  object Releases {
    def empty: Releases = Releases(Nil)
    def apply(releases: List[Release]): Releases =
      Utils.group_sorted(releases, (release: Release) => release.entry)
  }


  /* license */

  case class License(id: License.ID, name: String)

  object License { type ID = String }

  type Licenses = ListMap[License.ID, License]
  object Licenses {
    def empty: Licenses = Licenses(Nil)
    def apply(licenses: List[License]): Licenses =
      ListMap.from(licenses.map(license => license.id -> license))
  }


  /* references */

  sealed trait Reference

  case class DOI(identifier: String) extends Reference {
    require("^10.([1-9][0-9]{3,})/(.+)".r.matches(identifier),
      "invalid format for DOI: " + quote(identifier))

    def uri: URI = new URI("doi:" + identifier)
    def url: Url = Url("https://doi.org/" + identifier)
    def formatted(style: String = "apa"): String =
      Utils.fetch_text(url, Map("Accept" -> ("text/x-bibliography; style=" + style)))
  }

  case class Formatted(rep: String) extends Reference


  /* misc */

  type Change_History = Map[Date, String]
  type Extra = Map[String, String]


  /* entry */

  case class Entry(
    name: Entry.Name,
    title: String,
    authors: List[Affiliation],
    date: Date,
    topics: List[Topic],
    `abstract`: String,
    notifies: List[Email],
    license: License,
    note: String,
    contributors: List[Affiliation] = Nil,
    change_history: Change_History = Map.empty,
    extra: Extra = Map.empty,
    releases: List[Release] = Nil,
    statistics_ignore: Boolean = false,
    related: List[Reference] = Nil)

  object Entry { type Name = String }

  type Entries = ListMap[Entry.Name, Entry]
  object Entries {
    def empty: Entries = Entries(Nil)
    def apply(entries: List[Entry]) = ListMap.from(entries.map(entry => entry.name -> entry))
  }


  /* toml */

  private def by_id[A](elems: Map[String, A], id: String): A =
    elems.getOrElse(id, error("Elem " + quote(id) + " not found in " + commas_quote(elems.keys)))

  object TOML {
    import isabelle.TOML.{Array, Boolean, Key, Local_Date, String, Table}


    /* affils */

    def from_email(email: Email): Table =
      Table(
        "user" -> Array(email.user.split('.').map(String(_))),
        "host" -> Array(email.host.split('.').map(String(_))))

    def to_email(author_id: Author.ID, email_id: Email.ID, email: Table): Email = {
      val user = email.array("user").string.values.map(_.rep)
      val host = email.array("host").string.values.map(_.rep)
      Email(author_id, email_id, user.mkString("."), host.mkString("."))
    }

    /* author */

    def from_author(author: Author): Table =
      Table(
        "name" -> String(author.name),
        "emails" -> Table(author.emails.map(e => e.id -> from_email(e))),
        "homepages" -> Table(author.homepages.map(h => h.id -> String(h.url.toString)))) ++
        author.orcid.map(orcid => Table("orcid" -> String(orcid.identifier))).getOrElse(Table())

    def to_author(author_id: Author.ID, author: Table): Author = {
      val emails = author.table("emails").table.values.map {
        case (id, email) => to_email(author_id, id, email)
      }
      val homepages = author.table("homepages").string.values.map {
        case (id, url) => Homepage(author = author_id, id = id, url = Url(url.rep))
      }
      val orcid = author.string.get("orcid").map(_.rep).map(Orcid(_))
      Author(
        id = author_id,
        name = author.string("name").rep,
        orcid = orcid,
        emails = emails,
        homepages = homepages)
    }

    def from_authors(authors: List[Author]): Table =
      Table(authors.map(author => author.id -> from_author(author)))

    def to_authors(authors: Table): List[Author] = authors.table.values.map(to_author)


    /* topics */

    def from_acm(acm: ACM): Table = Table("id" -> String(acm.id), "desc" -> String(acm.desc))

    def to_acm(acm: Table): ACM = ACM(acm.string("id").rep, acm.string("desc").rep)

    def from_ams(ams: AMS): Table =
      Table("id" -> String(ams.id), "hierarchy" -> Array(ams.hierarchy.map(String(_))))

    def to_ams(ams: Table): AMS =
      AMS(ams.string("id").rep, ams.array("hierarchy").string.values.map(_.rep))

    def from_classifications(classifications: List[Classification]): Table =
      Table(classifications.map {
        case acm: ACM => "acm" -> from_acm(acm)
        case ams: AMS => "ams" -> from_ams(ams)
      })

    def to_classifications(classifications: Table): List[Classification] =
      classifications.table.values.map {
        case ("ams", ams) => to_ams(ams)
        case ("acm", acm) => to_acm(acm)
        case (c, _) => error("Unknown topic classification: " + quote(c))
      }

    def from_topics(root_topics: List[Topic]): Table =
      Table(root_topics.map(t => t.name -> (
        Table("classification" -> from_classifications(t.classification)) ++
        from_topics(t.sub_topics))))

    def to_topics(root_topics: Table): List[Topic] = {
      def to_topics_rec(topics: List[(Key, Table)], root: Topic.ID): List[Topic] = {
        topics.map {
          case (name, data) =>
            val id = (if (root.nonEmpty) root + "/" else "") + name

            val classifications = to_classifications(data.table("classification"))
            val sub_topics = data.table.values.filterNot(_._1 == "classification")

            Topic(id, name, classifications, to_topics_rec(sub_topics, id))
        }
      }

      to_topics_rec(root_topics.table.values, "")
    }


    /* releases */

    def from_releases(releases: List[Release]): Table =
      Table(Utils.group_sorted(releases, (r: Release) => r.entry).view.mapValues { entry_releases =>
        Table(entry_releases.map(r => r.date.toString -> String(r.isabelle)))
      }.toList)

    def to_releases(map: Table): List[Release] =
      map.table.values.flatMap {
        case (entry, releases) => releases.string.values.map {
          case (date, version) =>
            Release(entry = entry, date = LocalDate.parse(date), isabelle = version.rep)
        }
      }


    /* affiliation */

    def from_affiliations(affiliations: List[Affiliation]): Table =
      Table(Utils.group_sorted(affiliations, (a: Affiliation) => a.author).view.mapValues(vs =>
        Table(vs.collect {
          case Email(_, id, _) => "email" -> String(id)
          case Homepage(_, id, _) => "homepage" -> String(id)
        })).toList)

    def to_affiliations(affiliations: Table, authors: Authors): List[Affiliation] = {
      def to_affiliation(affiliation: (Key, String), author: Author): Affiliation = {
        affiliation match {
          case ("email", id) => author.emails.find(_.id == id.rep) getOrElse
            error("Email not found: " + quote(id.rep))
          case ("homepage", id) => author.homepages.find(_.id == id.rep) getOrElse
            error("Homepage not found: " + quote(id.rep))
          case e => error("Unknown affiliation type: " + e)
        }
      }

      affiliations.table.values.flatMap {
        case (id, author_affiliations) =>
          val author = by_id(authors, id)
          if (author_affiliations.is_empty) List(Unaffiliated(author.id))
          else author_affiliations.string.values.map(to_affiliation(_, author))
      }
    }

    def from_emails(emails: List[Email]): Table =
      Table(emails.map(email => email.author -> String(email.id)))

    def to_emails(emails: Table, authors: Authors): List[Email] =
      emails.string.values.map {
        case (author, id) => by_id(authors, author).emails.find(_.id == id.rep) getOrElse
          error("Email not found: " + quote(id.rep))
      }


    /* license */

    def from_licenses(licenses: List[License]): Table =
      Table(licenses.map(license => license.id -> Table("name" -> String(license.name))))

    def to_licenses(licenses: Table): List[License] = {
      licenses.table.values.map {
        case (id, license) => License(id, license.string("name").rep)
      }
    }

    def to_license(license: String, licenses: Licenses): License =
      licenses.getOrElse(license.rep, error("No such license: " + quote(license.rep)))


    /* history */

    def from_change_history(change_history: Change_History): Table =
      Table(change_history.map { case (date, str) => date.toString -> String(str) })

    def to_change_history(change_history: Table): Change_History =
      change_history.string.values.map {
        case (date, entry) => LocalDate.parse(date) -> entry.rep
      }.toMap


    /* references */

    def from_related(references: List[Reference]): Table = {
      val dois = references.collect { case d: DOI => d }
      val formatted = references.collect { case f: Formatted => f }

      Table(
        "dois" -> Array(dois.map(_.identifier).map(String(_))),
        "pubs" -> Array(formatted.map(_.rep).map(String(_))))
    }

    def to_related(references: Table): List[Reference] = {
      val dois = references.array.get("dois").toList.flatMap(_.string.values.map(_.rep))
      val pubs = references.array.get("pubs").toList.flatMap(_.string.values.map(_.rep))

      dois.map(DOI(_)) ++ pubs.map(Formatted(_))
    }


    /* entry */

    def from_entry(entry: Entry): Table = {
      Table(
        "title" -> String(entry.title),
        "authors" -> from_affiliations(entry.authors),
        "contributors" -> from_affiliations(entry.contributors),
        "date" -> Local_Date(entry.date),
        "topics" -> Array(entry.topics.map(_.id).map(String(_))),
        "abstract" -> String(entry.`abstract`),
        "notify" -> from_emails(entry.notifies),
        "license" -> String(entry.license.id),
        "note" -> String(entry.note),
        "history" -> from_change_history(entry.change_history),
        "extra" -> Table(entry.extra.view.mapValues(String(_)).toList),
        "related" -> from_related(entry.related)) ++
        (if (entry.statistics_ignore) Table("statistics_ignore" -> Boolean(true)) else Table())
    }

    def to_entry(
      name: Entry.Name,
      entry: Table,
      authors: Authors,
      topics: Topics,
      licenses: Licenses,
      releases: List[Release]
    ): Entry =
      Entry(
        name = name,
        title = entry.string("title").rep,
        authors = to_affiliations(entry.table("authors"), authors),
        date = entry.local_date("date").rep,
        topics = entry.array("topics").string.values.map(_.rep).map(by_id(topics, _)),
        `abstract` = entry.string("abstract").rep,
        notifies = to_emails(entry.table("notify"), authors),
        license = to_license(entry.string("license"), licenses),
        note = entry.string("note").rep,
        contributors = to_affiliations(entry.table("contributors"), authors),
        change_history = to_change_history(entry.table("history")),
        extra = entry.table("extra").string.values.map((k, v) => (k, v.rep)).toMap,
        releases = releases,
        statistics_ignore = entry.boolean.get("statistics_ignore").map(_.rep).getOrElse(false),
        related = to_related(entry.table("related")))
  }


  /* RDF export */

  object RDF {
    def from_entry(entry: Entry, authors: Authors): Properties.T = {
      def from_affiliations(affiliations: List[Affiliation], prop: String): Properties.T =
        (for (affiliation <- affiliations) yield prop -> authors(affiliation.author).name).distinct
      val date = Date(entry.date.atStartOfDay(Date.timezone_berlin))

      isabelle.RDF.meta_data(
        (Markup.META_TITLE -> entry.title) ::
        from_affiliations(entry.authors, Markup.META_CREATOR) :::
        (Markup.META_DATE -> isabelle.RDF.date_format(date)) ::
        from_affiliations(entry.contributors, Markup.META_CONTRIBUTOR) :::
        (Markup.META_LICENSE -> entry.license.name) ::
        (Markup.META_DESCRIPTION -> entry.`abstract`) :: Nil)
    }
  }
}

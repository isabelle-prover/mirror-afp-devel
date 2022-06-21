/* Author: Fabian Huch, TU Muenchen

AFP metadata model and TOML serialization.
 */
package afp


import isabelle._

import afp.TOML._

import java.time.LocalDate


object Metadata
{
  sealed abstract class Affiliation(val author: Author.ID)

  case class Unaffiliated(override val author: Author.ID)
    extends Affiliation(author)

  case class Email(override val author: Author.ID, id: Email.ID, address: String)
    extends Affiliation(author)

  object Email {
    type ID = String
  }

  case class Homepage(override val author: Author.ID, id: Homepage.ID, url: String)
    extends Affiliation(author)

  object Homepage {
    type ID = String
  }

  case class Author(
    id: Author.ID,
    name: String,
    emails: List[Email],
    homepages: List[Homepage]
  )

  object Author {
    type ID = String
  }

  case class Topic(id: Topic.ID, name: String, sub_topics: List[Topic])

  object Topic {
    type ID = String
  }

  type Date = LocalDate

  object Isabelle {
    type Version = String
  }

  case class Release(entry: Entry.Name, date: Date, isabelle: Isabelle.Version)

  case class License(id: License.ID, name: String)

  object License {
    type ID = String
  }

  type Change_History = Map[Date, String]
  type Extra = Map[String, String]

  case class Entry(
    name: Entry.Name,
    title: String,
    authors: List[Affiliation],
    date: Date,
    topics: List[Topic],
    `abstract`: String,
    notifies: List[Email],
    contributors: List[Affiliation],
    license: License,
    note: String,
    change_history: Change_History,
    extra: Extra,
    releases: List[Release],
    sitegen_ignore: Boolean)

  object Entry {
    type Name = String
  }


  /* toml */

  object TOML {
    private def by_id[A](elems: Map[String, A], id: String): A =
      elems.getOrElse(id, error("Elem " + quote(id) + " not found in " + commas_quote(elems.map(_.toString))))


    /* author */

    def from_authors(authors: List[Author]): T = {
      def from_author(author: Author): T =
        T(
          "name" -> author.name,
          "emails" -> T(author.emails.map(email => email.id -> email.address)),
          "homepages" -> T(author.homepages.map(homepage => homepage.id -> homepage.url)))

      T(authors.map(author => author.id -> from_author(author)))
    }

    def to_authors(authors: T): List[Author] = {
      def to_author(author_id: Author.ID, author: T): Author = {
        val emails = split_as[String](get_as[T](author, "emails")) map {
          case (id, address) => Email(author = author_id, id = id, address = address)
        }
        val homepages = split_as[String](get_as[T](author, "homepages")) map {
          case (id, url) => Homepage(author = author_id, id = id, url = url)
        }
        Author(
          id = author_id,
          name = get_as[String](author, "name"),
          emails = emails,
          homepages = homepages
        )
      }

      split_as[T](authors).map { case (id, author) => to_author(id, author) }
    }


    /* topics */

    def from_topics(root_topics: List[Topic]): T =
      T(root_topics.map(t => t.name -> from_topics(t.sub_topics)))

    def to_topics(root_topics: T): List[Topic] = {
      def to_topics_rec(topics: T, root: Topic.ID): List[Topic] =
        split_as[T](topics).map {
          case (name, sub_topics) =>
            val id = (if (root.nonEmpty) root + "/" else "") + name
            Topic(id, name, to_topics_rec(sub_topics, id))
        }

      to_topics_rec(root_topics, "")
    }


    /* releases */

    def from_releases(releases: List[Release]): T =
      T(Utils.group_sorted(releases, (r: Release) => r.entry).view.mapValues { entry_releases =>
        T(entry_releases.map(r => r.isabelle -> r.date))
      }.toList)

    def to_releases(map: T): List[Release] =
      split_as[T](map).flatMap {
        case (entry, releases) => split_as[Date](releases).map {
          case (version, date) => Release(entry = entry, date = date, isabelle = version)
        }
      }


    /* affiliation */

    def from_affiliations(affiliations: List[Affiliation]): T =
      T(Utils.group_sorted(affiliations, (a: Affiliation) => a.author).view.mapValues(vs =>
        T(vs.collect {
          case Email(_, id, _) => "email" -> id
          case Homepage(_, id, _) => "homepage" -> id
        })).toList)

    def to_affiliations(affiliations: T, authors: Map[Author.ID, Author]): List[Affiliation] = {
      def to_affiliation(affiliation: (String, String), author: Author): Affiliation = {
        affiliation match {
          case ("email", id: String) => author.emails.find(_.id == id) getOrElse
            error("Email not found: " + quote(id))
          case ("homepage", id: String) => author.homepages.find(_.id == id) getOrElse
            error("Homepage not found: " + quote(id))
          case e => error("Unknown affiliation type: " + e)
        }
      }

      split_as[T](affiliations).flatMap {
        case (id, author_affiliations) =>
          val author = by_id(authors, id)
          if (author_affiliations.isEmpty) List(Unaffiliated(author.id))
          else split_as[String](author_affiliations).map(to_affiliation(_, author))
      }
    }

    def from_emails(emails: List[Email]): T =
      T(emails.map(email => email.author -> email.id))

    def to_emails(emails: T, authors: Map[Author.ID, Author]): List[Email] =
      emails.toList.map {
        case (author, id: String) => by_id(authors, author).emails.find(_.id == id) getOrElse
          error("Email not found: " + quote(id))
        case e => error("Unknown email: " + quote(e.toString))
      }


    /* license */

    def from_licenses(licenses: List[License]): T =
      T(licenses.map(license => license.id -> T("name" -> license.name)))

    def to_licenses(licenses: T): List[License] = {
      split_as[T](licenses) map {
        case (id, license) => License(id, get_as[String](license, "name"))
      }
    }

    def to_license(license: String, licenses: Map[License.ID, License]): License =
      licenses.getOrElse(license, error("No such license: " + quote(license)))


    /* history */

    def from_change_history(change_history: Change_History): T =
      change_history.map { case (date, str) => date.toString -> str }

    def to_change_history(change_history: T): Change_History =
      change_history.map {
        case (date, entry: String) => LocalDate.parse(date) -> entry
        case e => error("Unknown history entry: " + quote(e.toString))
      }


    /* entry */

    def from_entry(entry: Entry): T = {
      T(
        "title" -> entry.title,
        "authors" -> from_affiliations(entry.authors),
        "contributors" -> from_affiliations(entry.contributors),
        "date" -> entry.date,
        "topics" -> entry.topics.map(_.id),
        "abstract" -> entry.`abstract`,
        "notify" -> from_emails(entry.notifies),
        "license" -> entry.license.id,
        "note" -> entry.note,
        "history" -> from_change_history(entry.change_history),
        "extra" -> entry.extra) ++
        (if (entry.sitegen_ignore) T("sitegen_ignore" -> true) else T())
    }

    def to_entry(entry: T, authors: Map[Author.ID, Author], topics: Map[Topic.ID, Topic],
      licenses: Map[License.ID, License], releases: List[Release]): Entry =
      Entry(
        name = get_as[String](entry, "name"),
        title = get_as[String](entry, "title"),
        authors = to_affiliations(get_as[T](entry, "authors"), authors),
        date = get_as[Date](entry, "date"),
        topics = get_as[List[String]](entry, "topics").map(by_id(topics, _)),
        `abstract` = get_as[String](entry, "abstract"),
        notifies = to_emails(get_as[T](entry, "notify"), authors),
        contributors = to_affiliations(get_as[T](entry, "contributors"), authors),
        license = to_license(get_as[String](entry, "license"), licenses),
        note = get_as[String](entry, "note"),
        change_history = to_change_history(get_as[T](entry, "history")),
        extra = get_as[Extra](entry, "extra"),
        releases = releases,
        sitegen_ignore = optional_as[Boolean](entry, "sitegen_ignore").getOrElse(false))
  }
}

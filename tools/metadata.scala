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

  object Email
  {
    type ID = Int
  }

  case class Homepage(override val author: Author.ID, id: Homepage.ID, url: String)
    extends Affiliation(author)

  object Homepage
  {
    type ID = Int
  }

  case class Author(
    id: Author.ID,
    name: String,
    emails: List[Email],
    homepages: List[Homepage]
  )

  object Author
  {
    type ID = String
  }

  case class Topic(id: Topic.ID, name: String, sub_topics: List[Topic])

  object Topic
  {
    type ID = String
  }

  type Date = LocalDate

  object Isabelle
  {
    type Version = String
  }

  case class Release(entry: Entry.Name, date: Date, isabelle: Isabelle.Version)

  type License = String
  type Change_History = Map[Date, String]
  type Extra = Map[String, String]

  case class Entry(
    short_name: Entry.Name,
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
    releases: List[Release])

  object Entry
  {
    type Name = String
  }


  /* toml */

  object TOML
  {
    private def by_id[A](elems: List[A], id: Int): A =
      elems.lift(id).getOrElse(error("Elem " + id + " not found in " + commas_quote(elems.map(_.toString))))

    private def by_id[A](elems: Map[String, A], id: String): A =
      elems.getOrElse(id, error("Elem " + quote(id) + " not found in " + commas_quote(elems.map(_.toString))))


    /* author */

    def from_authors(authors: List[Author]): T =
    {
      def from_author(author: Author): T =
        T(
          "name" -> author.name,
          "emails" -> author.emails.map(_.address),
          "homepages" -> author.homepages.map(_.url))

      T(authors.map(author => author.id -> from_author(author)))
    }

    def to_authors(authors: T): List[Author] =
    {
      def to_author(id: Author.ID, author: T): Author =
      {
        val emails = get_as[List[String]](author, "emails").zipWithIndex.map {
          case (address, idx) => Email(author = id, id = idx, address = address)
        }
        val homepages = get_as[List[String]](author, "homepages").zipWithIndex.map {
          case (url, idx) => Homepage(author = id, id = idx, url = url)
        }
        Author(
          id = id,
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

    def to_topics(root_topics: T): List[Topic] =
    {
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

    def to_affiliations(affiliations: T, authors: Map[Author.ID, Author]): List[Affiliation] =
    {
      def to_affiliation(affiliation: (String, Int), author: Author): Affiliation =
      {
        affiliation match {
          case ("email", id: Int) => by_id(author.emails, id)
          case ("homepage", id: Int) => by_id(author.homepages, id)
          case e => error("Unknown affiliation type: " + e)
        }
      }

      split_as[T](affiliations).flatMap {
        case (id, author_affiliations) =>
          val author = by_id(authors, id)
          if (author_affiliations.isEmpty) List(Unaffiliated(author.id))
          else split_as[Int](author_affiliations).map(to_affiliation(_, author))
      }
    }

    def from_emails(emails: List[Email]): T =
      T(emails.map(email => email.author -> email.id))

    def to_emails(emails: T, authors: Map[Author.ID, Author]): List[Email] =
      emails.toList.map {
        case (author, id: Int) => by_id(by_id(authors, author).emails, id)
        case e => error("Unknown email: " + quote(e.toString))
      }


    /* history */

    def from_change_history(change_history: Change_History): T =
      change_history.map { case (date, str) => date.toString -> str }

    def to_change_history(change_history: T): Change_History =
      change_history.map {
        case (date, entry: String) => LocalDate.parse(date) -> entry
        case e => error("Unknown history entry: " + quote(e.toString))
      }


    /* entry */

    def from_entry(entry: Entry): T =
      T(
        "title" -> entry.title,
        "authors" -> from_affiliations(entry.authors),
        "contributors" -> from_affiliations(entry.contributors),
        "date" -> entry.date,
        "topics" -> entry.topics.map(_.id),
        "abstract" -> entry.`abstract`,
        "notify" -> from_emails(entry.notifies),
        "license" -> entry.license,
        "note" -> entry.note,
        "history" -> from_change_history(entry.change_history),
        "extra" -> entry.extra)

    def to_entry(entry: T, authors: Map[Author.ID, Author], topics: Map[Topic.ID, Topic], releases: List[Release]): Entry =
      Entry(
        short_name = get_as[String](entry, "short_name"),
        title = get_as[String](entry, "title"),
        authors = to_affiliations(get_as[T](entry, "authors"), authors),
        date = get_as[Date](entry, "date"),
        topics = get_as[List[String]](entry, "topics").map(by_id(topics, _)),
        `abstract` = get_as[String](entry, "abstract"),
        notifies = to_emails(get_as[T](entry, "notify"), authors),
        contributors = to_affiliations(get_as[T](entry, "contributors"), authors),
        license = get_as[License](entry, "license"),
        note = get_as[String](entry, "note"),
        change_history = to_change_history(get_as[T](entry, "history")),
        extra = get_as[Extra](entry, "extra"),
        releases = releases)
  }
}

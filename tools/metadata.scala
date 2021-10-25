package afp


import isabelle._

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
  object Homepage {
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

  type Date = LocalDate
  type Topic = String
  type License = String
  type Change_History = String
  type Release = String
  type Release_History = List[Date]

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
  )
  object Entry {
    type Name = String
  }

  /* json */

  object TOML
  {
    type T = afp.TOML.T

    def apply(entries: (afp.TOML.Key, afp.TOML.V)*): T = afp.TOML.T(entries: _*)
    def apply(entries: List[(afp.TOML.Key, afp.TOML.V)]): T = afp.TOML.T(entries)

    def authors(authors: List[Author]): T =
      TOML(authors.map(author => author.id -> TOML(author)))

    private def apply(author: Author): T =
      TOML(
        "name" -> author.name,
        "emails" -> author.emails.map(_.address),
        "homepages" -> author.homepages.map(_.url)
      )

    private def apply(affiliation: Affiliation): T =
    {
      affiliation match {
        case Unaffiliated(_) => TOML()
        case Email(_, id, _) => TOML("email" -> id)
        case Homepage(_, id, _) => TOML("homepage" -> id)
      }
    }

    def affiliations(affiliations: List[Affiliation]): T =
      affiliations.groupBy(_.author).view.mapValues { author_affiliations =>
        Map("affiliations" -> author_affiliations.map(TOML.apply).filter(_.nonEmpty))
      }.toMap

    def emails(emails: List[Email]): T =
      TOML(emails.map(email => email.author -> email.id))

    def apply(entry: Entry): T =
      TOML(
        "title" -> entry.title,
        "authors" -> affiliations(entry.authors),
        "contributors" -> affiliations(entry.contributors),
        "date" -> entry.date,
        "topics" -> entry.topics,
        "abstract" -> entry.`abstract`,
        "notify" -> emails(entry.notifies),
        "license" -> entry.license
      )
  }
}
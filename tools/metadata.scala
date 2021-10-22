package afp


import isabelle._


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

  type Date = String
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

  object JSON
  {
    def apply(author: Author): isabelle.JSON.Object.T =
      isabelle.JSON.Object(
        author.id -> isabelle.JSON.Object(
          "name" -> author.name,
          "emails" -> author.emails.map(_.address),
          "homepages" -> author.homepages.map(_.url),
        )
      )

    def apply(affiliation: Affiliation): isabelle.JSON.Object.T =
      affiliation match {
        case Unaffiliated(author) =>
          isabelle.JSON.Object("id" -> author)
        case Email(author, id, _) =>
          isabelle.JSON.Object(
            "id" -> author,
            "affiliation" -> id
          )
        case Homepage(author, id, _) =>
          isabelle.JSON.Object(
            "id" -> author,
            "affiliation" -> id
          )
      }


    def apply(entry: Entry): isabelle.JSON.Object.T =
      isabelle.JSON.Object(
        "title" -> entry.title,
        "authors" -> entry.authors.map(JSON.apply),
        "contributors" -> entry.contributors.map(_.author),
        "date" -> entry.date,
        "topics" -> entry.topics,
        "abstract" -> entry.`abstract`,
        "notify" -> entry.notifies.map(JSON.apply),
        "license" -> entry.license
      )
  }
}
package afp.migration


import isabelle._

import afp._
import afp.Metadata.{Author, Email, Homepage}

import java.net.URL


object AFP_Obfuscate_Emails {

  type T = TOML.T

  def parse_authors(authors: T): List[Author] = {
    def to_author(author_id: Author.ID, author: T): Author = {
      val emails = TOML.split_as[String](TOML.get_as[T](author, "emails")) map {
        case (id, address) => Email(author = author_id, id = id, address = address)
      }
      val homepages = TOML.split_as[String](TOML.get_as[T](author, "homepages")) map {
        case (id, url) => Homepage(author = author_id, id = id, url = new URL(url))
      }
      Author(
        id = author_id,
        name = TOML.get_as[String](author, "name"),
        emails = emails,
        homepages = homepages)
    }

    TOML.split_as[T](authors).map { case (id, author) => to_author(id, author) }
  }

  val isabelle_tool = Isabelle_Tool("afp_obfuscate_emails", "obfuscate email addresses",
    Scala_Project.here,
  { args =>
    val getopts = Getopts("""
Usage: isabelle afp_obfuscate_emails [OPTIONS]

Obfuscates author email addresses.
""")

    getopts(args)

    val afp = AFP_Structure()

    val old_content = File.read(afp.metadata_dir + Path.basic("authors.toml"))
    val old_toml =
      try { TOML.parse(old_content) }
      catch { case ERROR(msg) => error("Could not parse old style authors file: " + msg) }
    val authors: List[Author] = parse_authors(old_toml)

    afp.save_authors(authors.sortBy(_.id))
  })
}
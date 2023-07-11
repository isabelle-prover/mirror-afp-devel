package afp.migration


import isabelle._

import afp._
import afp.TOML.Table
import afp.Metadata.{Author, Email, Homepage}

import java.net.URL


object AFP_Obfuscate_Emails {

  def parse_authors(authors: Table): List[Author] = {
    def to_author(author_id: Author.ID, author: Table): Author = {
      val emails = author.table("emails").string.values.map {
        case (id, address) => Email(author = author_id, id = id, address = address.rep)
      }
      val homepages = author.table("homepages").string.values.map {
        case (id, url) => Homepage(author = author_id, id = id, url = new URL(url.rep))
      }
      Author(
        id = author_id,
        name = author.string("name").rep,
        emails = emails,
        homepages = homepages)
    }

    authors.table.values.map { case (id, author) => to_author(id, author) }
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
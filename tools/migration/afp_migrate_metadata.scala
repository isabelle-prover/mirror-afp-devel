package afp.migration


import isabelle._

import afp._
import afp.Metadata.{TOML => _, _}

import scala.collection.BufferedIterator

import java.io.BufferedReader
import java.text.Normalizer
import java.time.LocalDate
import java.net.URI

import org.jline.utils.InputStreamReader


object AFP_Migrate_Metadata
{
  private class Context(
    names_mapping: Map[String, String],
    email_names: Map[String, String],
    dates_mapping: Map[String, String])
  {
    /* mappings */

    def transform_name(name: String): String =
      names_mapping.getOrElse(name, name)

    def parse_date(date: String): Metadata.Date =
      LocalDate.parse(dates_mapping.getOrElse(date, date))

    def name(address: String): String =
      email_names.getOrElse(address, error("No name for address " + address))

    /* seen */

    private var _seen_authors = Set.empty[Author.ID]
    private var _seen_emails = Set.empty[Email.ID]
    private var _seen_homepages = Set.empty[Homepage.ID]
    private var _seen_licenses = Map.empty[License.ID, License]
    private var _seen_author_names = Map.empty[String, Author]

    def seen_authors: Set[Author.ID] = _seen_authors
    def seen_emails: Set[Email.ID] = _seen_emails
    def seen_homepages: Set[Homepage.ID] = _seen_homepages

    def author(name: String): Option[Author] = _seen_author_names.get(name)

    def authors: List[Author] = _seen_author_names.values.toList
    def licenses: List[License] = _seen_licenses.values.toList

    def update_author(author: Author): Unit =
    {
      _seen_authors += author.id
      _seen_author_names = _seen_author_names.updated(author.name, author)
    }

    def email(author: Author.ID): Email.ID =
    {
      val id = unique_id(author + "_email", this.seen_emails)
      _seen_emails += id
      id
    }

    def homepage(homepage: Homepage.ID): Homepage.ID =
    {
      val id = unique_id(homepage + "_homepage", this.seen_homepages)
      _seen_homepages += id
      id
    }

    def license(license_str: String): License =
    {
      val license = License(license_str.toLowerCase, license_str)
      _seen_licenses += license.id -> license
      license
    }
  }

  private def is_email(url: String) = url.contains("@")

  private def as_ascii(str: String) =
  {
    var res: String = str
    List("ö" -> "oe", "ü" -> "ue", "ä" -> "ae", "ß" -> "ss").foreach {
      case (c, rep) => res = res.replace(c, rep)
    }
    res = Normalizer.normalize(res, Normalizer.Form.NFD).replaceAll("[^\\x00-\\x7F]", "")
    if (res.exists(_ > 127)) error("Contained non convertible non-ascii character: " + str)
    res
  }

  def unique_id(prefix: String, ids: Set[String]): String =
  {
    if (!ids.contains(prefix)) prefix
    else {
      var num = 1
      while (ids.contains(prefix + num)) { num += 1 }
      prefix + num
    }
  }

  def private_dom(full_dom: String): String =
  {
    val stream = getClass.getClassLoader.getResourceAsStream("public_suffix_list.dat")
    val reader = new BufferedReader(new InputStreamReader(stream))
    val public_suffixes = File.read_lines(reader, _ => ()).filterNot(_.startsWith("//"))
    val stripped = public_suffixes.map(full_dom.stripSuffix(_)).minBy(_.length)
    if (stripped.endsWith(".")) stripped.dropRight(1) else stripped
  }

  def make_author_id(name: String, context: Context): String =
  {
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
    var ident = suffix.toLowerCase
    for {
      c <- prefix.toLowerCase
    } {
      if (context.seen_authors.contains(ident)) {
        ident += c.toString
      } else return ident
    }
    unique_id(ident, context.seen_authors)
  }

  def author_urls(name_urls: String, context: Context): (String, List[String]) =
  {
    val name = AFP.trim_mail(name_urls)
    val urls_string = name_urls.stripPrefix(name).trim
    val transformed = context.transform_name(name)
    if (urls_string == "<>") {
      (transformed, List(""))
    } else {
      (transformed, urls_string.split(Array('<', '>')).toList.filterNot(_.isBlank))
    }
  }

  def add_email(author: Author, address: String, context: Context): (Author, Email) =
  {
    val email = Email(author = author.id, id = context.email(author.id), address = address)
    val update_author = author.copy(emails = author.emails :+ email)
    context.update_author(update_author)
    (update_author, email)
  }

  def get_affiliations(name_url: String, context: Context): List[Affiliation] =
  {
    val (name, urls) = author_urls(name_url, context)
    val author = context.author(name).getOrElse(error("Author not found: " + name))

    urls.map { url =>
      if (is_email(url)) {
        val address = url.stripPrefix("mailto:")

        author.emails.find(_.address == address) getOrElse
          error("Email not found: " + (author, address))
      }
      else if (url.isEmpty) {
        Unaffiliated(author.id)
      }
      else {
        author.homepages.find(_.url == url) getOrElse
          error("Url not found for: " + (author, url))
      }
    }
  }

  def get_email_affiliation(address: String, context: Context, progress: Progress): Email =
  {
    context.authors.flatMap(_.emails).find(_.address == address) match {
      case Some(email) => email
      case None =>
        val name = context.name(address)
        val author = context.author(name) match {
          case Some(author) => author
          case None =>
            progress.echo_warning("New author: " + name)
            Author(make_author_id(name, context), name, Nil, Nil)
        }
        add_email(author, address, context)._2
    }
  }

  def update_author(name_urls: String, context: Context): Unit =
  {
    val (name, urls) = author_urls(name_urls, context)
    var author = context.author(name) match {
      case Some(author) => author
      case None => Author(make_author_id(name, context), name, Nil, Nil)
    }

    urls.foreach { url =>
      if (is_email(url)) {
        val address = url.stripPrefix("mailto:")

        if (!author.emails.exists(_.address == address)) {
          author = add_email(author, address, context)._1
        }
      }
      else if (url.nonEmpty && !author.homepages.exists(_.url == url)) {
        val homepage = Homepage(author = author.id, id = context.homepage(author.id), url = url)

        author = author.copy(homepages = author.homepages :+ homepage)
      }
    }

    context.update_author(author)
  }

  def map_entry(
    entry: AFP.Entry,
    releases: Map[Entry.Name, List[Release]],
    topics: Map[Topic.ID, Topic],
    context: Context,
    progress: Progress): Entry =
  {
    val author_affiliations = entry.authors.flatMap(get_affiliations(_, context))
    val contributor_affiliations = entry.contributors.flatMap(get_affiliations(_, context))
    val notify_emails = entry.get_strings("notify").map(get_email_affiliation(_, context, progress))
    val change_history = parse_change_history(entry.get_string("extra-history"), context)
    val extra = entry.metadata.filter { case (k, _) => k.startsWith("extra-") && k != "extra-history" }

    Entry(
      name = entry.name,
      title = entry.title,
      authors = author_affiliations,
      date = LocalDate.from(entry.date.rep),
      topics = entry.topics.map(topics),
      `abstract` = entry.`abstract`,
      notifies = notify_emails,
      contributors = contributor_affiliations,
      license = context.license(entry.license),
      note = entry.get_string("note"),
      change_history = change_history,
      extra = extra.toMap,
      releases = releases(entry.name)
    )
  }

  def parse_change_history(history: String, context: Context): Change_History =
  {
    val matches = """\[(\d{4}-\d{2}-\d{2})]: ([^\[]+)""".r.findAllMatchIn(history.stripPrefix("Change history:"))
    matches.toList.map(_.subgroups match {
      case date :: content :: Nil => context.parse_date(date) -> content
      case _ => error("Could not parse change history: " + quote(history))
    }).toMap
  }

  def parse_topics(lines: List[String]): List[Topic] =
  {
    val lines_iterator: BufferedIterator[String] = lines.filterNot(_.isBlank).iterator.buffered

    def get_indent(line: String) = line.takeWhile(_.isWhitespace).length

    def parse_level(level: Int, root: Option[Topic.ID]): List[Topic] =
    {
      val name = lines_iterator.next().trim
      val id = root.map(_ + "/").getOrElse("") + name
      val (sub_topics, next_topics) = lines_iterator.headOption match {
        case Some(next) if get_indent(next) == level + 2 =>
          val sub = parse_level(level + 2, Some(id))
          val next = lines_iterator.headOption match {
            case Some(next1) if get_indent(next1) == level => parse_level(level, root)
            case _ => Nil
          }
          (sub, next)
        case Some(next) if get_indent(next) == level =>
          (Nil, parse_level(level, root))
        case _ => (Nil, Nil)
      }
      Topic(id = id, name = name, sub_topics = sub_topics) :: next_topics
    }

    parse_level(0, None)
  }

  def parse_releases(
    releases: List[String],
    isabelle_releases: List[String],
    all_entries: List[Entry.Name],
    context: Context): List[Release] =
  {
    val Isa_Release = """(.+) = (.+)""".r
    val release_dates = isabelle_releases.filterNot(_.isBlank).map {
      case Isa_Release(isabelle_version, date) => context.parse_date(date) -> isabelle_version
      case line => error("Could not parse: " + quote(line))
    }
    val current = release_dates.last

    def to_release(entry: Entry.Name, release_date: LocalDate): Release =
      Release(entry, release_date, release_dates.findLast { case (date, _) => date.isBefore(release_date) }.get._2)

    val Entry_Release = """afp-([a-zA-Z0-9_+-]+)-(\d{4}-\d{2}-\d{2})\.tar\.gz""".r
    val entry_releases = Utils.group_sorted(
      releases.filterNot(_.isBlank).map {
        case Entry_Release(entry, date_string) =>
          val date = context.parse_date(date_string)
          entry -> to_release(entry, date)
        case line => error("Could not parse: " + quote(line))
      }, (e: (Entry.Name, Release)) => e._1)
    all_entries.flatMap(e => entry_releases.getOrElse(e, Nil).map(_._2) :+ to_release(e, current._1))
  }

  def migrate_metadata(
    base_dir: Path,
    overwrite: Boolean,
    context: Context,
    options: Options = Options.init(),
    progress: Progress = new Progress()): Unit =
  {
    val metadata = AFP.init(options, base_dir)
    val metadata_dir = base_dir + Path.basic("metadata")

    def read(file: Path): String =
      File.read(metadata_dir + file)

    def write(toml: TOML.T, file: Path) =
    {
      val path = metadata_dir + file
      if (!overwrite && path.file.exists) error("File already exists: " + path.file_name)
      else path.dir.file.mkdirs()
      File.write(path, TOML.Format(toml))
    }


    /* topics */

    progress.echo("Parsing topics...")

    val root_topics = parse_topics(split_lines(read(Path.basic("topics"))))

    def sub_topics(topic: Topic): List[Topic] =
      topic :: topic.sub_topics.flatMap(sub_topics)

    val topic_map = root_topics.flatMap(sub_topics).map(topic => topic.id -> topic).toMap

    write(Metadata.TOML.from_topics(root_topics), Path.basic("topics.toml"))


    /* releases */

    progress.echo("Parsing releases...")

    val releases = parse_releases(
      split_lines(read(Path.basic("releases"))),
      split_lines(read(Path.basic("release-dates"))),
      metadata.entries.map(_.name), context)
    val releases_map = releases.groupBy(_.entry)

    write(Metadata.TOML.from_releases(releases), Path.basic("releases.toml"))


    /* collect authors (without notify affiliations) */

    progress.echo("Collecting authors...")

    for {
      entry <- metadata.entries
      name_url <- entry.authors ++ entry.contributors
    } update_author(name_url, context)

    /* entries */

    progress.echo("Parsing entries...")

    for (entry_metadata <- metadata.entries) {
      val entry = map_entry(entry_metadata, releases_map, topic_map, context, progress)

      write(Metadata.TOML.from_entry(entry), Path.make(List("entries", entry.name + ".toml")))
    }


    /* licenses */

    write(Metadata.TOML.from_licenses(context.licenses), Path.basic("licenses.toml"))


    /* authors */

    write(Metadata.TOML.from_authors(context.authors), Path.basic("authors.toml"))
  }

  val isabelle_tool =
    Isabelle_Tool(
      "afp_migrate_metadata",
      "migrates old sitegen metadata to new format",
      Scala_Project.here,
      args => {
        var base_dir = Path.explode("$AFP_BASE")

        var names = List(
          "Lawrence C Paulson" -> "Lawrence C. Paulson",
          "Lawrence Paulson" -> "Lawrence C. Paulson",
          "Florian Kammueller" -> "Florian Kammüller",
          "Jasmin Blanchette" -> "Jasmin Christian Blanchette",
          "Ognjen Maric" -> "Ognjen Marić",
          "Maximilian P.L. Haslbeck" -> "Maximilian P. L. Haslbeck",
          "Maximilian Haslbeck" -> "Max W. Haslbeck",
          "Sebastiaan Joosten" -> "Sebastiaan J. C. Joosten",
          "Jacques Fleuriot" -> "Jacques D. Fleuriot",
          "Jose Manuel Rodriguez Caballero" -> "José Manuel Rodríguez Caballero")

        var emails = List(
          "a.bentkamp@vu.nl" -> "Alexander Bentkamp",
          "a.popescu@mdx.ac.uk" -> "Andrei Popescu",
          "a.popescu@sheffield.ac.uk" -> "Andrei Popescu",
          "afp@liftm.de" -> "Julius Michaelis",
          "ahfrom@dtu.dk" -> "Asta Halkjær From",
          "ak2110@cam.ac.uk" -> "Angeliki Koutsoukou-Argyraki",
          "akihisayamada@nii.ac.jp" -> "Akihisa Yamada",
          "aleje@dtu.dk" -> "Alexander Birch Jensen",
          "alexander.katovsky@cantab.net" -> "Alexander Katovsky",
          "alexander.maletzky@risc-software.at" -> "Alexander Maletzky",
          "alexander.maletzky@risc.jku.at" -> "Alexander Maletzky",
          "andreas.lochbihler@digitalasset.com" -> "Andreas Lochbihler",
          "andreasvhess@gmail.com" -> "Andreas V. Hess",
          "andschl@dtu.dk" -> "Anders Schlichtkrull",
          "apdb3@cam.ac.uk" -> "Anthony Bordg",
          "avigad@cmu.edu" -> "Jeremy Avigad",
          "ballarin@in.tum.de" -> "Clemens Ballarin",
          "bdd@liftm.de" -> "Julius Michaelis",
          "benblumson@gmail.com" -> "Ben Blumson",
          "berghofe@in.tum.de" -> "Stefan Berghofer",
          "bjbohrer@gmail.com" -> "Brandon Bohrer",
          "boehmes@in.tum.de" -> "Sascha Böhme",
          "brianh@cs.pdx.edu" -> "Brian Huffman",
          "brunnerj@in.tum.de" -> "Julian Brunner",
          "bzhan@ios.ac.cn" -> "Bohua Zhan",
          "c.benzmueller@fu-berlin.de" -> "Christoph Benzmüller",
          "c.benzmueller@gmail.com" -> "Christoph Benzmüller",
          "caw77@cam.ac.uk" -> "Conrad Watt",
          "cezary.kaliszyk@uibk.ac.at" -> "Cezary Kaliszyk",
          "christian.sternagel@uibk.ac.at" -> "Christian Sternagel",
          "christian.urban@kcl.ac.uk" -> "Christian Urban",
          "coglio@kestrel.edu" -> "Alessandro Coglio",
          "corey.lewis@data61.csiro.au" -> "Corey Lewis",
          "d1623001@s.konan-u.ac.jp" -> "Fumiya Iwama",
          "danijela@matf.bg.ac.rs" -> "Danijela Simić",
          "denis.lohner@kit.edu" -> "Denis Lohner",
          "denis.nikif@gmail.com" -> "Denis Nikiforov",
          "diego.marmsoler@tum.de" -> "Diego Marmsoler",
          "diekmann@net.in.tum.de" -> "Cornelius Diekmann",
          "dubut@nii.ac.jp" -> "Jérémy Dubut",
          "eminkarayel@google.com" -> "Emin Karayel",
          "f.smola@sms.ed.ac.uk" -> "Filip Smola",
          "fadouaghourabi@gmail.com" -> "Fadoua Ghourabi",
          "fimmler@andrew.cmu.edu" -> "Fabian Immler",
          "fimmler@cs.cmu.edu" -> "Fabian Immler",
          "florian.haftmann@informatik.tu-muenchen.de" -> "Florian Haftmann",
          "florian.kammuller@gmail.com" -> "Florian Kammüller",
          "friedrich.kurz@tum.de" -> "Friedrich Kurz",
          "ftuong@lri.fr" -> "Frédéric Tuong",
          "g.struth@dcs.shef.ac.uk" -> "Georg Struth",
          "ggrov@inf.ed.ac.uk" -> "Gudmund Grov",
          "giamp@dmi.unict.it" -> "Giampaolo Bella",
          "giuliano@losa.fr" -> "Giuliano Losa",
          "Harald.Zankl@uibk.ac.at" -> "Harald Zankl",
          "haslbecm@in.tum.de" -> "Max W. Haslbeck",
          "haslbema@in.tum.de" -> "Maximilian P. L. Haslbeck",
          "heimesl@student.ethz.ch" -> "Lukas Heimes",
          "hetzl@logic.at" -> "Stefan Hetzl",
          "holub@karlin.mff.cuni.cz" -> "Štěpán Holub",
          "Ian.Hayes@itee.uq.edu.au" -> "Ian J. Hayes",
          "isabelleopenflow@liftm.de" -> "Julius Michaelis",
          "Jacques.Fleuriot@ed.ac.uk" -> "Jacques D. Fleuriot",
          "jason.jaskolka@carleton.ca" -> "Jason Jaskolka",
          "jdf@ed.ac.uk" -> "Jacques D. Fleuriot",
          "jeremy.sylvestre@ualberta.ca" -> "Jeremy Sylvestre",
          "jesus-maria.aransay@unirioja.es" -> "Jesús Aransay",
          "jonjulian23@gmail.com" -> "Jonathan Julian Huerta y Munive",
          "jose.divason@unirioja.es" -> "Jose Divasón",
          "jose.divasonm@unirioja.es" -> "Jose Divasón",
          "joseph-thommes@gmx.de" -> "Joseph Thommes",
          "jovi@dtu.dk" -> "Jørgen Villadsen",
          "jsiek@indiana.edu" -> "Jeremy Siek",
          "jsylvest@ualberta.ca" -> "Jeremy Sylvestre",
          "julian.nagele@uibk.ac.at" -> "Julian Nagele",
          "julian.parsert@uibk.ac.at" -> "Julian Parsert",
          "kevin.kappelmann@tum.de" -> "Kevin Kappelmann",
          "kkz@mit.edu" -> "Karen Zee",
          "kleing@unsw.edu.au" -> "Gerwin Klein",
          "krauss@in.tum.de" -> "Alexander Krauss",
          "kreuzerk@in.tum.de" -> "Katharina Kreuzer",
          "lars@hupel.info" -> "Lars Hupel",
          "lcp@cl.cam.ac.uk" -> "Lawrence C. Paulson",
          "lennart.beringer@ifi.lmu.de" -> "Lennart Beringer",
          "liwenda1990@hotmail.com" -> "Wenda Li",
          "mail@andreas-lochbihler.de" -> "Andreas Lochbihler",
          "mail@michael-herzberg.de" -> "Michael Herzberg",
          "maintainafpppt@liftm.de" -> "Julius Michaelis",
          "maksym.bortin@nicta.com.au" -> "Maksym Bortin",
          "manuel.eberl@tum.de" -> "Manuel Eberl",
          "martin.desharnais@unibw.de" -> "Martin Desharnais",
          "mathias.fleury@jku.at" -> "Mathias Fleury",
          "matthias.brun@inf.ethz.ch" -> "Matthias Brun",
          "max.haslbeck@gmx.de" -> "Max W. Haslbeck",
          "maximilian.haslbeck@uibk.ac.at" -> "Max W. Haslbeck",
          "me@eminkarayel.de" -> "Emin Karayel",
          "MichaelNedzelsky@yandex.ru" -> "Michael Nedzelsky",
          "mihailsmilehins@gmail.com" -> "Mihails Milehins",
          "mnacho.echenim@univ-grenoble-alpes.fr" -> "Mnacho Echenim",
          "mnfrd.krbr@gmail.com" -> "Manfred Kerber",
          "mohammad.abdulaziz8@gmail.com" -> "Mohammad Abdulaziz",
          "mohammad.abdulaziz@in.tum.de" -> "Mohammad Abdulaziz",
          "mr644@cam.ac.uk" -> "Michael Rawson",
          "mrtnrau@googlemail.com" -> "Martin Rau",
          "nanjiang@whu.edu.cn" -> "Nan Jiang",
          "Nicolas.Peltier@imag.fr" -> "Nicolas Peltier",
          "nipkow@in.tum.de" -> "Tobias Nipkow",
          "noschinl@gmail.com" -> "Lars Noschinski",
          "pagano@famaf.unc.edu.ar" -> "Miguel Pagano",
          "pc@cs.st-andrews.ac.uk" -> "Peter Chapman",
          "peter.lammich@uni-muenster.de" -> "Peter Lammich",
          "peter@hoefner-online.de" -> "Peter Höfner",
          "ralph.bottesch@uibk.ac.at" -> "Ralph Bottesch",
          "reza.sefidgar@inf.ethz.ch" -> "S. Reza Sefidgar",
          "richter@informatik.rwth-aachen.de" -> "Stefan Richter",
          "roelofoosterhuis@gmail.com" -> "Roelof Oosterhuis",
          "rok@strnisa.com" -> "Rok Strniša",
          "rosskops@in.tum.de" -> "Simon Roßkopf",
          "s.griebel@tum.de" -> "Simon Griebel",
          "s.j.c.joosten@utwente.nl" -> "Sebastiaan J. C. Joosten",
          "samo@dtu.dk" -> "Sebastian Mödersheim",
          "schirmer@in.tum.de" -> "Norbert Schirmer",
          "sidney.amani@data61.csiro.au" -> "Sidney Amani",
          "sjcjoosten@gmail.com" -> "Sebastiaan J. C. Joosten",
          "stepan.starosta@fit.cvut.cz" -> "Štěpán Starosta",
          "Stephan.Merz@loria.fr" -> "Stephan Merz",
          "sterraf@famaf.unc.edu.ar" -> "Pedro Sánchez Terraf",
          "stourret@mpi-inf.mpg.de" -> "Sophie Tourret",
          "stvienna@gmail.com" -> "Stephan Adelsberger",
          "susannahej@gmail.com" -> "Susannah Mansky",
          "tdardini@student.ethz.ch" -> "Thibault Dardinier",
          "tim@tbrk.org" -> "Timothy Bourke",
          "toby.murray@unimelb.edu.au" -> "Toby Murray",
          "traytel@di.ku.dk" -> "Dmitriy Traytel",
          "traytel@in.tum.de" -> "Dmitriy Traytel",
          "traytel@inf.ethz.ch" -> "Dmitriy Traytel",
          "uuomul@yahoo.com" -> "Andrei Popescu",
          "walter.guttman@canterbury.ac.nz" -> "Walter Guttmann",
          "walter.guttmann@canterbury.ac.nz" -> "Walter Guttmann",
          "wimmers@in.tum.de" -> "Simon Wimmer",
          "wl302@cam.ac.uk" -> "Wenda Li",
          "yongkiat@cs.cmu.edu" -> "Yong Kiam Tan",
          "Yutaka.Nagashima@data61.csiro.au" -> "Yutaka Nagashima")

        var dates = List(
          "2020-14-04" -> "2020-04-14",
          "2020-15-04" -> "2020-04-15")

        var overwrite = false

        val getopts = Getopts(
          """
Usage: isabelle afp_migrate_metadata [OPTIONS]

  Options are:
    -B DIR            afp base dir (default "$AFP_BASE")
    -n FROM,TO        names to convert (default:
                      """ + names.mkString("\n                      ") +
            """)
    -e EMAIL,AUTHOR   emails to associate (default:
                      """ + emails.mkString("\n                      ") +
            """)
    -d FROM,TO        date strings to convert (default:
                      """ + dates.mkString("\n                       ") +
            """)
    -f                overwrite existing

  Migrates old sitegen metadata to new format.
""",
          "B:" -> (arg => base_dir = Path.explode(arg)),
          "n:" -> (arg => names ::= arg.splitAt(arg.indexOf(","))),
          "e:" -> (arg => emails ::= arg.splitAt(arg.indexOf(","))),
          "d:" -> (arg => dates ::= arg.splitAt(arg.indexOf(","))),
          "f" -> (_ => overwrite = true)
        )

        getopts(args)

        val progress = new Console_Progress()

        val context = new Context(names.toMap, emails.toMap, dates.toMap)

        val options = Options.init()

        migrate_metadata(
          base_dir = base_dir,
          context = context,
          overwrite = overwrite,
          options = options,
          progress = progress)
      }
    )
}
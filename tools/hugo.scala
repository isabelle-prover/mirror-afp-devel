/* Author: Fabian Huch, TU Muenchen

Site generation via Hugo. See also: https://gohugo.io/.
 */
package afp


import isabelle.*


object Hugo {
  def isabelle_hugo: Path = {
    Path.explode(proper_string(Isabelle_System.getenv("ISABELLE_HUGO"))
      getOrElse error("No hugo component found"))
  }


  /* hugo content */

  case class Menu_Item(name: String, weight: Int, menu: String = "main") {
    def json: JSON.Object.T = JSON.Object(menu -> JSON.Object("name" -> name, "weight" -> weight))
  }

  case class Metadata(
    title: String = "",
    description: String = "",
    url: String = "",
    date: String = "",
    `type`: String = "",
    weight: Int = 0,
    keywords: List[String] = Nil,
    draft: Boolean = false,
    outputs: List[String] = Nil,
    menu: Option[Menu_Item] = None,
    params: JSON.Object.T = JSON.Object.empty
  ) {
    def json: JSON.Object.T = {
      params ++
      JSON.optional("title", proper_string(title)) ++
      JSON.optional("description", proper_string(description)) ++
      JSON.optional("url", proper_string(url)) ++
      JSON.optional("date", proper_string(date)) ++
      JSON.optional("type", proper_string(`type`)) ++
      JSON.optional("weight", if (weight > 0) Some(weight) else None) ++
      JSON.optional("keywords", proper_list(keywords)) ++
      JSON.optional("draft", proper_bool(draft)) ++
      JSON.optional("outputs", proper_list(outputs)) ++
      JSON.optional("menu", menu.map(_.json))
    }
  }

  case class Content(section: String, rel_path: Path, metadata: Metadata, src: String = "") {
    def file: Path = (if (section.nonEmpty) Path.basic(section) + rel_path else rel_path).ext("md")
    def print: String = JSON.Format(metadata.json) + "\n" + src
  }

  object Index {
    def apply(section: String, metadata: Metadata, src: String = ""): Content =
      Content(section, Path.basic("_index"), metadata, src)
  }


  /* hugo project */

  def project(src_dir: Path, theme: String): Project = new Project(src_dir, theme)

  class Project private[Hugo](val dir: Path, theme: String) {
    override def toString: String = "Hugo.Project(" + dir + ")"

    val themes_dir: Path = dir + Path.explode("themes")
    val data_dir: Path = dir + Path.basic("data")
    val static_dir: Path = dir + Path.basic("static")
    val content_dir: Path = dir + Path.basic("content")

    private def write(file: Path, content: String): Unit = {
      Isabelle_System.make_directory(file.dir)
      File.write(file, content)
    }

    def write_data(rel_path: Path, content: String): Unit = write(data_dir + rel_path, content)
    def write_static(rel_path: Path, content: String): Unit = write(static_dir + rel_path, content)
    def write_content(content: Content): Unit = write(content_dir + content.file, content.print)

    def build(
      out_dir: Path,
      draft: Boolean = false,
      server: Boolean = false,
      progress: Progress = new Progress
    ): Unit = {
      val script =
        File.bash_path(isabelle_hugo + Path.basic("hugo")) +
          if_proper(server, " server") +
          if_proper(draft, " -D") +
          if_proper(!progress.verbose, " --logLevel error") +
          " -t " + Bash.string(theme) +
          " -s " + File.bash_platform_path(dir) +
          " -d " + File.bash_platform_path(out_dir)
      val res =  Isabelle_System.bash(script, progress_stdout = progress.echo(_, verbose = true))
      if (!res.ok) {
        if (!progress.verbose) progress.echo_error_message(cat_lines(res.out_lines))
        error("Building hugo project failed")
      }
    }
  }
}

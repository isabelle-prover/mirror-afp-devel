package afp


import isabelle._


object Hugo
{
  val hugo_home = Isabelle_System.getenv("ISABELLE_HUGO")
  val hugo_static = Path.explode("$AFP_BASE") + Path.make(List("admin", "site"))

  class Layout private(private[Hugo] val src_dir: Path)
  {
    private def write(file: Path, content: String): Unit =
    {
      val path = src_dir + file
      if (!path.dir.file.exists()) path.dir.file.mkdirs()
      File.write(path, content)
    }

    val data_dir = src_dir + Path.basic("data")

    def write_data(file: Path, content: JSON.T): Unit =
      write(Path.basic("data") + file, isabelle.JSON.Format(content))

    val content_dir = src_dir + Path.basic("content")

    def write_content(file: Path, content: JSON.T): Unit =
      write(Path.basic("content") + file, isabelle.JSON.Format(content))

    val static_dir = src_dir + Path.basic("static")
    
    def write_static(file: Path, content: JSON.T): Unit =
      write(Path.basic("static") + file, isabelle.JSON.Format(content))

    def copy_project(): Unit =
    {
      if (hugo_static.canonical != src_dir) {
        for {
          file <- List(
            List("content", "_index.md"),
            List("content", "about.md"),
            List("content", "contribution.md"),
            List("content", "download.md"),
            List("content", "help.md"),
            List("content", "search.md"),
            List("content", "statistics.md"),
            List("content", "submission.md"),
            List("themes"),
            List("config.json"))
        } Isabelle_System.copy_dir(hugo_static + Path.make(file), src_dir + Path.make(file))
      }
    }
  }

  object Layout
  {
    def apply(src_dir: Path = Path.explode("$AFP_BASE") + Path.make(List("web", "hugo"))): Layout =
      new Layout(src_dir.canonical)
  }

  private lazy val exec =
    Path.explode(proper_string(hugo_home).getOrElse(error("No hugo component found"))) + Path.basic("hugo")

  def build(layout: Layout, out_dir: Path = Path.explode("$AFP_BASE") + Path.basic("web")): Process_Result =
  {
    Isabelle_System.bash(
      exec.implode + " -s " + quote(layout.src_dir.implode) + " -d " + quote(out_dir.canonical.implode))
  }

  def watch(layout: Layout, out_dir: Path = Path.explode("$AFP_BASE") + Path.basic("web"),
    progress: Progress = new Progress()): Process_Result =
  {
    Isabelle_System.bash(
      exec.implode + " server -s " + quote(layout.src_dir.implode) + " -d " + quote(out_dir.canonical.implode),
      progress_stdout = progress.echo,
      progress_stderr = progress.echo_warning)
  }
}
package afp


import isabelle._


object Hugo
{
  val hugo_home = Isabelle_System.getenv("ISABELLE_HUGO")
  val hugo_static = Path.explode("$AFP_BASE") + Path.make(List("admin", "site"))

  class Layout private(src_dir: Path, out_dir: Path)
  {
    private def write(file: Path, content: JSON.T): Unit =
    {
      val path = src_dir + file
      path.dir.file.mkdirs()
      File.write(path, isabelle.JSON.Format(content))
    }

    val data_dir = src_dir + Path.basic("data")

    def write_data(file: Path, content: JSON.T): Unit =
      write(Path.basic("data") + file, content)

    val content_dir = src_dir + Path.basic("content")

    def write_content(file: Path, content: JSON.T): Unit =
      write(Path.basic("content") + file, content)

    def write_static(): Unit =
      Isabelle_System.copy_dir(hugo_static, out_dir)

    def build(): Process_Result =
    {
      val exec = Path.explode(proper_string(hugo_home).getOrElse(error("No hugo component found"))) + Path.basic("hugo")
      Isabelle_System.bash(
        exec.implode + " -s " + quote(src_dir.implode) + " -d " + quote(out_dir.implode))
    }
  }

  object Layout
  {
    private val web_dir = Path.explode("$AFP_BASE") + Path.basic("web")

    def apply(src_dir: Path = web_dir + Path.basic("hugo"), out_dir: Path = web_dir): Layout =
      new Layout(src_dir.absolute, out_dir.absolute)
  }
}
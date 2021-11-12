package afp


import isabelle._


object Python
{
  val python_home = Isabelle_System.getenv("ISABELLE_PYTHON")

  val python_path = (Path.explode("$AFP_BASE") + Path.make(List("admin", "sitegen-lib"))).absolute

  def run(command: String): Process_Result =
  {
    val exec =
      Path.explode(proper_string(python_home).getOrElse("No python component found")) +
      Path.make(List("bin", "python3"))
    Isabelle_System.bash(exec.implode + " -c '" + command + "'",
      env = Isabelle_System.settings(List("PYTHONPATH" -> python_path.implode)))
  }
}

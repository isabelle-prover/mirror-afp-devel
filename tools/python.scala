package afp


import isabelle._


object Python
{
  val python_home = Isabelle_System.getenv("ISABELLE_PYTHON")

  val python_path = (Path.explode("$AFP_BASE") + Path.make(List("admin", "sitegen-lib"))).absolute

  def run(script: String): Process_Result =
  {
    val exec =
      Path.explode(proper_string(python_home).getOrElse("No python component found")) +
      Path.make(List("bin", "python3"))
    
    val script_file = Isabelle_System.tmp_file("isabelle_python", "py")
    File.write(script_file, script)
    
    val res = Isabelle_System.bash(exec.implode + " " + script_file.getAbsolutePath,
      env = Isabelle_System.settings(List("PYTHONPATH" -> python_path.implode)))
    
    script_file.delete()
    res
  }
}

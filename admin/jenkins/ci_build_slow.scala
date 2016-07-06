object profile extends isabelle.CI_Profile
{

  import isabelle._

  val afp = Path.explode("$ISABELLE_HOME/afp")
  val afp_thys = afp + Path.explode("thys")

  def threads = 8
  def jobs = 1
  def all = false
  def groups = List("slow")
  def exclude = Nil
  def include = List(afp_thys)
  def select = Nil

  def pre_hook(args: List[String]) =
    println(s"Build for AFP id ${hg_id(afp)}")

  def post_hook(results: Build.Results) = {}

  override def select_sessions(tree: Sessions.Tree): (List[String], Sessions.Tree) =
    tree.selection(session_groups = List("slow"))

}

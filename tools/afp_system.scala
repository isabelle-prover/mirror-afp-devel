/* Author: Fabian Huch

Miscellaneous AFP system operations.
*/
package afp


import isabelle.*


object AFP_System {
  def hg_id: String =
    Mercurial.Hg_Sync.id_directory(AFP.BASE) getOrElse AFP.self_repository().id()
}
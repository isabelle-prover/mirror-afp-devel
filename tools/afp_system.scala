/* Author: Fabian Huch

Miscellaneous AFP system operations.
*/
package afp

import isabelle._


object AFP_System {
  def afp_version: String = Isabelle_System.getenv_strict("AFP_VERSION")
  def afp_name: String = "afp-" + afp_version

  def AFP_BUILD_OPTIONS: Options.Update =
    Word.explode(Isabelle_System.getenv("AFP_BUILD_OPTIONS")).map(Options.Spec.make)
}
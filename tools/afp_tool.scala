package afp


import isabelle.Isabelle_Scala_Tools

import afp.migration._


class Admin_Tools extends Isabelle_Scala_Tools(
  AFP_Migrate_Metadata.isabelle_tool,
)

class Tools extends Isabelle_Scala_Tools(
  AFP_Check_Roots.isabelle_tool,
  AFP_Dependencies.isabelle_tool,
)

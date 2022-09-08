package afp


import isabelle._

import afp.migration._


class Admin_Tools extends Isabelle_Scala_Tools(
  AFP_Migrate_Metadata.isabelle_tool,
  AFP_Obfuscate_Emails.isabelle_tool,
  AFP_Build_Hugo.isabelle_tool,
)

class Tools extends Isabelle_Scala_Tools(
  AFP_Site_Gen.isabelle_tool,
  AFP_Check_Roots.isabelle_tool,
  AFP_Check_Metadata.isabelle_tool,
  AFP_Dependencies.isabelle_tool,
)

class Build_Tools extends Isabelle_Scala_Tools(
  AFP_Build.ci_build_afp,
  AFP_Build.ci_build_all,
  AFP_Build.ci_build_mac,
  AFP_Build.ci_build_slow,
  AFP_Build.ci_build_testboard
)
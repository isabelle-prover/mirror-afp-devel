package afp


import isabelle._


class Tools extends Isabelle_Scala_Tools(
  AFP_Site_Gen.isabelle_tool,
  AFP_Check_Roots.isabelle_tool,
  AFP_Check_Metadata.isabelle_tool,
  AFP_Dependencies.isabelle_tool,
  AFP_Release.isabelle_tool,
  AFP_Submit.isabelle_tool,
  AFP_Submit.isabelle_tool1)

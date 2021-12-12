theory DisableKodkodScala
  imports Main
begin

text \<open>Some of the nitpick invocation within this AFP entry do not work,
  if "Kodkod Scala" is enabled, i.e., if the box under 
  Plugin Options — Isabelle — General — Miscelleaneous Tools — Kodkod Scala 
  is activated. Therefore, in this theory we explicitly disable this configuration option.\<close>

ML \<open>
  Options.default_put_bool \<^system_option>\<open>kodkod_scala\<close> false
\<close>

end
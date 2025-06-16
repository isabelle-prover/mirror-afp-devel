theory RunningCodeFromIsabelle
  imports HelloWorld
begin

section\<open>Running the Generated Code inside Isabelle\<close>

(*Maintainer note: We invoke the generated code ON PURPOSE from bash to demonstrate how to use
  the generated code from outside Isabelle and make sure the code runs.*)


text\<open>
  Usually, one would use \<^theory_text>\<open>export_code\<close> to generate code. Here, we want to write the code to
  a temp directory and execute it right afterwards inside Isablle, so we invoke the code generator
  directly from Isabelle/ML.
\<close>

subsection\<open>Haskell\<close>

ML\<open>
val (files, _) =
  Code_Target.produce_code @{context} false [@{const_name main}] "Haskell" "Main" NONE []

val target = File.tmp_path (Path.basic ("export" ^ serial_string ()))

val ghc = getenv "ISABELLE_GHC";

val cmd =
  "cd " ^ File.bash_path target ^ " && " ^
    Bash.string ghc ^ " Main.hs && " ^
    "(  echo 'Cyber Cat 42' | ./Main )";

Isabelle_System.make_directory target;

List.app (fn ([file], content) => Bytes.write (target + Path.basic file) content) files;

val exitcode =
  if ghc <> "" then
    Isabelle_System.bash cmd
  else
    (writeln "not running Haskell, because $ISABELLE_GHC is not set."; 0);

if exitcode <> 0 then
  raise (Fail ("example Haskell code did not run as expected, " ^
                 "exit code was " ^ (Int.toString exitcode)))
else ()
\<close>


subsection\<open>SML\<close>

ML\<open>

val ([(_, content)], _) =
  Code_Target.produce_code @{context} false [@{const_name main}] "SML" "HelloWorld" NONE []

val target = File.tmp_path (Path.basic ("export" ^ serial_string ()))
val file = target + Path.basic "main.ML"

val cmd =
  "echo 'Super Goat 2000' | " ^
    File.bash_path \<^path>\<open>$ML_HOME/poly\<close> ^ " --use " ^ File.bash_platform_path file ^
    " --eval 'HelloWorld.main ()'";

Isabelle_System.make_directory target;
Bytes.write file content;

val exitcode = Isabelle_System.bash cmd;

if exitcode <> 0 then
  raise (Fail ("example SML code did not run as expected, " ^
                 "exit code was " ^ (Int.toString exitcode)))
else ()
\<close>


end
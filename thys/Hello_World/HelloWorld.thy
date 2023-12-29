theory HelloWorld
  imports IO
begin

section\<open>Hello, World!\<close>

text\<open>
  The idea of a \<^term>\<open>main :: unit io\<close> function is that, upon start of your program, you will be
  handed a value of type \<^typ>\<open>\<^url>\<close>. You can pass this world through your code and modify it.
  Be careful with the \<^typ>\<open>\<^url>\<close>, it's the only one we have.
\<close>


text\<open>The main function, defined in Isabelle. It should have the right type in Haskell.\<close>
definition main :: "unit io" where
  "main \<equiv> do {
               _ \<leftarrow> println (STR ''Hello World! What is your name?'');
               name \<leftarrow> getLine;
               println (STR ''Hello, '' + name + STR ''!'')
             }"


section\<open>Generating Code\<close>

text\<open>Checking that the generated code compiles.\<close>

export_code main checking Haskell? SML

(*<*)
setup \<open>
let
  val parser =
    Scan.repeat (Args.const {proper = true, strict = true}) --
      Scan.lift (\<^keyword>\<open>in\<close> |-- Parse.name -- (\<^keyword>\<open>module_name\<close> |-- Parse.name))

  fun action ctxt (consts, (target, module)) =
    Code_Target.produce_code ctxt false consts target module NONE []
    |> fst
    |> map (Bytes.content o snd) |> String.concatWith "\n"
in
  Document_Output.antiquotation_verbatim @{binding code} parser action
end\<close>
(*>*)

subsection\<open>Haskell\<close>

text\<open>The generated code in Haskell (including the prelude) is shown below.\<close>

text_raw\<open>@{code main in Haskell module_name HelloWorld}\<close>

subsection\<open>SML\<close>

text\<open>The generated code in SML (including the prelude) is shown below.\<close>

text_raw\<open>@{code main in SML module_name HelloWorld}\<close>

end

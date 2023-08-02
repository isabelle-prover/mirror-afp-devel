section\<open>Generating an Exectuable of the Evaluator\<close>

theory 
  Compile_Evaluator 
  imports 
    Solidity_Evaluator 
begin


compile_generated_files _  (in Solidity_Evaluator) export_files  "solidity-evaluator"  (exe)
  where \<open>fn dir =>
    let
       val modules_src =
        Generated_Files.get_files \<^theory>\<open>Solidity_Evaluator\<close>
        |> filter (fn p => String.isSubstring "src" (Path.implode (#path p))) 
        |> map (#path #> Path.implode  #> unsuffix ".hs" #> space_explode "/" #> space_implode "." 
                      #> unprefix "code.solidity-evaluator.src.");
       val modules_app =
        Generated_Files.get_files \<^theory>\<open>Solidity_Evaluator\<close>
        |> filter (fn p => String.isSubstring "app" (Path.implode (#path p))) 
        |> map (#path #> Path.implode  #> unsuffix ".hs" #> space_explode "/" #> space_implode "." 
                      #> unprefix "code.solidity-evaluator.app.");
      val _ =
        GHC.new_project dir
          {name = "solidity-evaluator",
           depends =
            [],
           modules = modules_app};
     val res = Generated_Files.execute dir \<open>Build\<close> (String.concat [
              "echo \"\n  default-extensions:  TypeSynonymInstances, FlexibleInstances\" >> solidity-evaluator.cabal"
                 ," && rm -rf src"
                 ," && mv code/solidity-evaluator/src src"
                 ," && mv code/solidity-evaluator/app/* src/"
                 ," && isabelle ghc_stack install --local-bin-path . ."])
   in
     writeln (res) 
   end\<close> 


end 

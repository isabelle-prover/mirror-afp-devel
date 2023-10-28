\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>ML Parsing Utils\<close>
theory ML_Parsing_Utils
  imports
    ML_Attributes
    ML_Attribute_Utils
begin

paragraph \<open>Summary\<close>
text \<open>Parsing utilities for ML. We provide an antiquotation that takes a list of
keys and creates a corresponding record with getters and mappers and a parser for corresponding
key-value pairs.\<close>

ML_file\<open>parse_util.ML\<close>

ML_file\<open>parse_key_value.ML\<close>
ML_file\<open>parse_key_value_antiquot.ML\<close>

(*use the following to test the code generation*)
(* ML_command\<open>
  Parse_Key_Value_Antiquot.mk_all "Test" NONE ["ABC", "DEFG" ]
  |> split_lines |> map Pretty.str |> Pretty.fbreaks |> Pretty.block |> Pretty.writeln
\<close> *)

paragraph \<open>Example\<close>

ML_command\<open>
  \<comment> \<open>Create record type and utility functions.\<close>
  @{parse_entries (struct) Test [ABC, DEFG]}

  val parser =
    let
      \<comment> \<open>Create the key-value parser.\<close>
      val parse_entry = Parse_Key_Value.parse_entry
        Test.parse_key \<comment>\<open>parser for keys\<close>
        (Scan.succeed [])  \<comment>\<open>delimiter parser\<close>
        (Test.parse_entry \<comment>\<open>value parser\<close>
          Parse.string \<comment>\<open>parser for ABC\<close>
          Parse.int) \<comment>\<open>parser for DEFG\<close>
      val required_keys = [Test.key Test.ABC] \<comment>\<open>required keys\<close>
      val default_entries = Test.empty_entries () \<comment>\<open>default values for entries\<close>
    in Test.parse_entries_required Parse.and_list1 required_keys parse_entry default_entries end
    \<comment> \<open>This parses, for example, \<open>ABC = hello and DEFG = 3\<close> or \<open>DEFG = 3 and ABC = hello\<close>,
    but not \<open>DEFG = 3\<close> since the key "ABC" is missing.\<close>
\<close>

end

(* 
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
*)
theory Example_Application
  imports 
    Xmlt
begin

text \<open>Let us consider inputs that consist of an optional number and a list of first order terms,
  where these terms use strings as function names and numbers for variables.
  We assume that we have a XML-document that describes these kinds of inputs and now want to parse them.\<close>

definition exampleInput where "exampleInput = STR 
  ''<input>
      <magicNumber>42</magicNumber>
      <funapp> <!-- first term in list -->
         <symbol>fo&lt;&gt;bar</symbol>
         <var>1</var> <!-- first subterm -->
         <var>3</var> <!-- second subterm -->
      </funapp>
      <var>15</var> <!-- second term in list -->
   </input>''" 

datatype fo_term = Fun string "fo_term list" | Var int

definition var :: "fo_term xmlt" where "var = xml_change (xml_int (STR ''var'')) (xml_return \<circ> Var)"

text \<open>a recursive parser is best defined via partial-function. Note that the xml-argument
  should be provided, otherwise strict evalution languages will not terminate.\<close>
partial_function (sum_bot) parse_term :: "fo_term xmlt"
where
 [code]: "parse_term xml = (
    XMLdo (STR ''funapp'') {
      name \<leftarrow> xml_text (STR ''symbol'');
      args \<leftarrow>* parse_term;
      xml_return (Fun name args)
    } XMLor var) xml" 

text \<open>for non-recursive parsers, we can eta-contract\<close>
definition parse_input :: "(int option \<times> fo_term list) xmlt" where
  "parse_input = XMLdo (STR ''input'') {
      onum \<leftarrow>? xml_int (STR ''magicNumber'');
      terms \<leftarrow>* parse_term;
      xml_return (onum,terms)
   }" 

definition test where "test = parse_xml_string parse_input (String.explode exampleInput)" 

value test (* successfully parses the example input *)
export_code test checking SML
end
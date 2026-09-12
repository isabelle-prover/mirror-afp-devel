section \<open>Tactic for instantiating existentials\<close>
theory Inst_Ex_Assn
  imports Separation_Logic_Imperative_HOL.Assertions
begin

thm ent_ex_postI

text \<open>
  Coinduction proofs in Isabelle often lead to proof obligations with nested conjunctions and
  existential quantifiers, e.g. \<^prop>\<open>\<exists>x y. P x y \<and> (\<exists>z. Q x y z)\<close> .

  The following tactic allows instantiating these existentials with a given list of witnesses.

  This tactic was adjusted to work with the assertion specific prop\<open>\<exists>\<^sub>A\<close>
\<close>

ML_file \<open>inst_ex_assn.ML\<close>

method_setup inst_ex_assn = \<open>
  Scan.lift (Scan.repeat Parse.term) >> 
    (fn ts => fn ctxt => SIMPLE_METHOD' (Inst_Ex_Assn.tac ctxt 
       (map (Syntax.read_term ctxt)  ts)))
\<close>

end
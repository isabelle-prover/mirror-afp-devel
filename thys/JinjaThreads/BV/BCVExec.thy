(*  Title:      JinjaThreads/BV/BCVExec.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Code generation for the byte code verifier} *}

theory BCVExec imports
  "BVNoTypeError" 
  "BVExec"
begin

code_const "undefined :: cname"
  (SML "\"\"")

lemmas [code_inline] = exec_lub_def

lemmas [code] = JVM_le_unfold[THEN meta_eq_to_obj_eq]

lemma err_code [code]:
  "Err.err A = err_case True A"
by(auto simp add: err_def mem_def split: err.split)

lemma list_code [code]:
  "list n A = (\<lambda>xs. size xs = n \<and> list_all A xs)"
unfolding list_def Collect_def
by(auto intro!: ext simp add: list_all_iff mem_def)

lemma opt_code [code]:
  "opt A = option_case True A"
by(auto simp add: opt_def mem_def split: option.split)

lemma Times_code [code_inline]:
  "Sigma A (%_. B) = (\<lambda>(a, b). a \<in> A \<and> b \<in> B)"
by(auto)(auto simp add: mem_def)

lemma upto_esl_code [code]:
  "upto_esl m (A, r, f) = (Union ((\<lambda>n. list n A) ` {..m}), Listn.le r, Listn.sup f)"
by(auto simp add: upto_esl_def)

lemmas [code] = lesub_def plussub_def

lemma JVM_sup_unfold [code]:
  "JVM_SemiType.sup S m n = 
  lift2 (Opt.sup (Product.sup (Listn.sup (SemiType.sup S)) (\<lambda>x y. OK (map2 (lift2 (SemiType.sup S)) x y))))"
unfolding JVM_SemiType.sup_def JVM_SemiType.sl_def Opt.esl_def Err.sl_def
  stk_esl_def loc_sl_def Product.esl_def Listn.sl_def upto_esl_def 
  SemiType.esl_def Err.esl_def 
by simp

(* FIXME: why is @{thm sup_fun_eq} declared [code del] in Lattices.thy? *)
declare sup_fun_eq [code] 

lemma [code]: "states P mxs mxl = fst(sl P mxs mxl)"
unfolding states_def ..

lemma check_types_code [code]:
  "check_types P mxs mxl \<tau>s = (list_all (states P mxs mxl) \<tau>s)"
unfolding check_types_def by(auto simp add: list_all_iff mem_def)

lemma wf_jvm_prog_code [code]:
  "wf_jvm_prog = wf_jvm_prog\<^isub>k"
  by (simp add: ext_iff jvm_kildall_correct)

ML {* @{code wf_jvm_prog} *}

end

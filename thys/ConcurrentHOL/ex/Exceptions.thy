(*<*)
theory Exceptions
imports
  "ConcurrentHOL.ConcurrentHOL"
begin

(*>*)
section\<open> Exceptions\label{sec:exceptions} \<close>

text\<open>

A sketch of how we might handle exceptions in this framework.

\<close>

setup \<open>Sign.mandatory_path "raw"\<close>

type_synonym ('s, 'x, 'v) exn = "('s, 'x + 'v) prog"

definition action :: "('v \<times> 's \<times> 's) set \<Rightarrow> ('s, 'x, 'v) raw.exn" where
  "action = prog.action \<circ> image (map_prod Inr id)"

definition return :: "'v \<Rightarrow> ('s, 'x, 'v) raw.exn" where
  "return = prog.return \<circ> Inr"

definition throw :: "'x \<Rightarrow> ('s, 'x, 'v) raw.exn" where
  "throw = prog.return \<circ> Inl"

definition catch :: "('s, 'x, 'v) raw.exn \<Rightarrow> ('x \<Rightarrow> ('s, 'x, 'v) raw.exn) \<Rightarrow> ('s, 'x, 'v) raw.exn" where
  "catch f handler = f \<bind> case_sum handler raw.return"

definition bind :: "('s, 'x, 'v) raw.exn \<Rightarrow> ('v \<Rightarrow> ('s, 'x, 'v) raw.exn) \<Rightarrow> ('s, 'x, 'v) raw.exn" where
  "bind f g = f \<bind> case_sum raw.throw g"

definition parallel :: "('s, 'x, unit) raw.exn \<Rightarrow> ('s, 'x, unit) raw.exn \<Rightarrow> ('s, 'x, unit) raw.exn" where
  "parallel P Q = (P \<bind> case_sum \<bottom> prog.return \<parallel> Q \<bind> case_sum \<bottom> prog.return) \<bind> raw.return"

setup \<open>Sign.mandatory_path "bind"\<close>

lemma bind:
  shows "raw.bind (raw.bind f g) h = raw.bind f (\<lambda>x. raw.bind (g x) h)"
by (simp add: raw.bind_def prog.bind.bind sum.case_distrib[where h="\<lambda>f. f \<bind> case_sum raw.throw h"])
   (simp add: raw.throw_def comp_def prog.bind.return cong: sum.case_cong)

lemma return:
  shows returnL: "raw.bind (raw.return v) = (\<lambda>g. g v)"
    and returnR: "raw.bind f raw.return = f"
by (simp_all add: fun_eq_iff raw.bind_def raw.return_def raw.throw_def prog.bind.return case_sum_Inl_Inr_L)

lemma throwL:
  shows "raw.bind (raw.throw x) = (\<lambda>g. raw.throw x)"
by (simp add: fun_eq_iff raw.bind_def raw.throw_def prog.bind.return)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "catch"\<close>

lemma catch:
  shows "raw.catch (raw.catch f handler\<^sub>1) handler\<^sub>2 = raw.catch f (\<lambda>x. raw.catch (handler\<^sub>1 x) handler\<^sub>2)"
by (simp add: raw.catch_def prog.bind.bind sum.case_distrib[where h="\<lambda>f. f \<bind> case_sum handler\<^sub>2 raw.return"])
   (simp add: raw.return_def comp_def prog.bind.return cong: sum.case_cong)

lemma returnL:
  shows "raw.catch (raw.return v) = (\<lambda>handler. raw.return v)"
by (simp add: fun_eq_iff raw.catch_def raw.return_def prog.bind.return)

lemma throw:
  shows throwL: "raw.catch (raw.throw x) = (\<lambda>g. g x)"
    and throwR: "raw.catch f raw.throw = f"
by (simp_all add: fun_eq_iff raw.catch_def raw.return_def raw.throw_def prog.bind.return case_sum_Inl_Inr_L)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "parallel"\<close>

lemma commute:
  shows "raw.parallel P Q = raw.parallel Q P"
by (simp add: raw.parallel_def prog.parallel.commute)

lemma assoc:
  shows "raw.parallel P (raw.parallel Q R) = raw.parallel (raw.parallel P Q) R"
by (simp add: raw.parallel_def raw.return_def prog.bind.bind prog.bind.return prog.parallel.assoc)

lemma return:
  shows "raw.parallel (raw.return ()) P = raw.catch P (\<lambda>x. \<bottom>)" (is ?thesis1)
    and "raw.parallel P (raw.return ()) = raw.catch P (\<lambda>x. \<bottom>)" (is ?thesis2)
proof -
  show ?thesis1
    by (simp add: raw.parallel_def raw.return_def
                  prog.bind.bind prog.bind.return prog.parallel.return prog.bind.botL
                  sum.case_distrib[where h="\<lambda>f. f \<bind> prog.return \<circ> Inr"]
            flip: raw.catch_def[unfolded raw.return_def o_def]
            cong: sum.case_cong)
  then show ?thesis2
    by (simp add: raw.parallel.commute)
qed

lemma throw:
  shows "raw.parallel (raw.throw x) P = raw.bind (raw.catch P (\<lambda>x. \<bottom>)) (\<lambda>x. \<bottom>)" (is ?thesis1)
    and "raw.parallel P (raw.throw x) = raw.bind (raw.catch P (\<lambda>x. \<bottom>)) (\<lambda>x. \<bottom>)" (is ?thesis2)
proof -
  show ?thesis1
    by (simp add: raw.parallel_def raw.throw_def raw.bind_def raw.return_def raw.catch_def
                  prog.bind.bind prog.bind.return prog.bind.botL prog.parallel.bot
                  sum.case_distrib[where h="\<lambda>f. prog.bind f (\<lambda>x. \<bottom>)"]
                  sum.case_distrib[where h="\<lambda>f. f \<bind> case_sum (prog.return \<circ> Inl) (\<lambda>x. \<bottom>)"]
            cong: sum.case_cong)
  then show ?thesis2
    by (simp add: raw.parallel.commute)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

typedef ('s, 'x, 'v) exn = "UNIV :: ('s, 'x, 'v) raw.exn set"
by blast

setup_lifting type_definition_exn

instantiation exn :: (type, type, type) complete_distrib_lattice
begin

lift_definition bot_exn :: "('s, 'x, 'v) exn" is "\<bottom>" .
lift_definition top_exn :: "('s, 'x, 'v) exn" is "\<top>" .
lift_definition sup_exn :: "('s, 'x, 'v) exn \<Rightarrow> ('s, 'x, 'v) exn \<Rightarrow> ('s, 'x, 'v) exn" is sup .
lift_definition inf_exn :: "('s, 'x, 'v) exn \<Rightarrow> ('s, 'x, 'v) exn \<Rightarrow> ('s, 'x, 'v) exn" is inf .
lift_definition less_eq_exn :: "('s, 'x, 'v) exn \<Rightarrow> ('s, 'x, 'v) exn \<Rightarrow> bool" is less_eq .
lift_definition less_exn :: "('s, 'x, 'v) exn \<Rightarrow> ('s, 'x, 'v) exn \<Rightarrow> bool" is less .
lift_definition Inf_exn :: "('s, 'x, 'v) exn set \<Rightarrow> ('s, 'x, 'v) exn" is Inf .
lift_definition Sup_exn :: "('s, 'x, 'v) exn set \<Rightarrow> ('s, 'x, 'v) exn" is Sup .

instance by standard (transfer; auto intro: Inf_lower InfI le_supI1 SupI SupE Inf_Sup)+

end

setup \<open>Sign.mandatory_path "exn"\<close>

lift_definition action :: "('v \<times> 's \<times> 's) set \<Rightarrow> ('s, 'x, 'v) exn" is raw.action .
lift_definition return :: "'v \<Rightarrow> ('s, 'x, 'v) exn" is raw.return .
lift_definition throw :: "'x \<Rightarrow> ('s, 'x, 'v) exn" is raw.throw .
lift_definition catch :: "('s, 'x, 'v) exn \<Rightarrow> ('x \<Rightarrow> ('s, 'x, 'v) exn) \<Rightarrow> ('s, 'x, 'v) exn" is raw.catch .
lift_definition bind :: "('s, 'x, 'v) exn \<Rightarrow> ('v \<Rightarrow> ('s, 'x, 'v) exn) \<Rightarrow> ('s, 'x, 'v) exn" is raw.bind .
lift_definition parallel :: "('s, 'x, unit) exn \<Rightarrow> ('s, 'x, unit) exn \<Rightarrow> ('s, 'x, unit) exn" is raw.parallel .

adhoc_overloading
  Monad_Syntax.bind exn.bind
adhoc_overloading
  parallel exn.parallel

setup \<open>Sign.mandatory_path "bind"\<close>

lemma bind:
  shows "f \<bind> g \<bind> h = exn.bind f (\<lambda>x. g x \<bind> h)"
by transfer (rule raw.bind.bind)

lemma return:
  shows returnL: "(\<bind>) (exn.return v) = (\<lambda>g. g v)" (is ?thesis1)
    and returnR: "f \<bind> exn.return = f" (is ?thesis2)
by (transfer; rule raw.bind.return)+

lemma throwL:
  shows "(\<bind>) (exn.throw x) = (\<lambda>g. exn.throw x)"
by transfer (rule raw.bind.throwL)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "catch"\<close>

lemma catch:
  shows "exn.catch (exn.catch f handler\<^sub>1) handler\<^sub>2 = exn.catch f (\<lambda>x. exn.catch (handler\<^sub>1 x) handler\<^sub>2)"
by transfer (rule raw.catch.catch)

lemma returnL:
  shows "exn.catch (exn.return v) = (\<lambda>handler. exn.return v)"
by transfer (rule raw.catch.returnL)

lemma throw:
  shows throwL: "exn.catch (exn.throw x) = (\<lambda>g. g x)"
    and throwR: "exn.catch f exn.throw = f"
by (transfer; rule raw.catch.throw)+

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "parallel"\<close>

lemma commute:     
  shows "exn.parallel P Q = exn.parallel Q P"
by transfer (rule raw.parallel.commute)

lemma assoc:
  shows "exn.parallel P (exn.parallel Q R) = exn.parallel (exn.parallel P Q) R"
by transfer (rule raw.parallel.assoc)

lemma return:
  shows returnL: "exn.return () \<parallel> P = exn.catch P \<bottom>"
    and returnR: "P \<parallel> exn.return () = exn.catch P \<bottom>"
unfolding bot_fun_def by (transfer; rule raw.parallel.return)+

lemma throw:
  shows throwL: "exn.throw x \<parallel> P = exn.catch P \<bottom> \<bind> \<bottom>"
    and throwR: "P \<parallel> exn.throw x = exn.catch P \<bottom> \<bind> \<bottom>"
unfolding bot_fun_def by (transfer; rule raw.parallel.throw)+

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)

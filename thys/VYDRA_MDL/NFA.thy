theory NFA
  imports "HOL-Library.IArray"
begin

type_synonym state = nat

datatype transition = eps_trans state nat | symb_trans state | split_trans state state

fun state_set :: "transition \<Rightarrow> state set" where
  "state_set (eps_trans s _) = {s}"
| "state_set (symb_trans s) = {s}"
| "state_set (split_trans s s') = {s, s'}"

fun fmla_set :: "transition \<Rightarrow> nat set" where
  "fmla_set (eps_trans _ n) = {n}"
| "fmla_set _ = {}"

lemma rtranclp_closed: "rtranclp R q q' \<Longrightarrow> X = X \<union> {q'. \<exists>q \<in> X. R q q'} \<Longrightarrow>
  q \<in> X \<Longrightarrow> q' \<in> X"
  by (induction q q' rule: rtranclp.induct) auto

lemma rtranclp_closed_sub: "rtranclp R q q' \<Longrightarrow> {q'. \<exists>q \<in> X. R q q'} \<subseteq> X \<Longrightarrow>
  q \<in> X \<Longrightarrow> q' \<in> X"
  by (induction q q' rule: rtranclp.induct) auto

lemma rtranclp_closed_sub': "rtranclp R q q' \<Longrightarrow> q' = q \<or> (\<exists>q''. R q q'' \<and> rtranclp R q'' q')"
  using converse_rtranclpE by force

lemma rtranclp_step: "rtranclp R q q'' \<Longrightarrow> (\<And>q'. R q q' \<longleftrightarrow> q' \<in> X) \<Longrightarrow>
  q = q'' \<or> (\<exists>q' \<in> X. R q q' \<and> rtranclp R q' q'')"
  by (induction q q'' rule: rtranclp.induct)
     (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma rtranclp_unfold: "rtranclp R x z \<Longrightarrow> x = z \<or> (\<exists>y. R x y \<and> rtranclp R y z)"
  by (induction x z rule: rtranclp.induct) auto

context fixes
  q0 :: "state" and
  qf :: "state" and
  transs :: "transition list"
begin

(* sets of states *)

qualified definition SQ :: "state set" where
  "SQ = {q0..<q0 + length transs}"

lemma q_in_SQ[code_unfold]: "q \<in> SQ \<longleftrightarrow> q0 \<le> q \<and> q < q0 + length transs"
  by (auto simp: SQ_def)

lemma finite_SQ: "finite SQ"
  by (auto simp add: SQ_def)

lemma transs_q_in_set: "q \<in> SQ \<Longrightarrow> transs ! (q - q0) \<in> set transs"
  by (auto simp add: SQ_def)

qualified definition Q :: "state set" where
  "Q = SQ \<union> {qf}"

lemma finite_Q: "finite Q"
  by (auto simp add: Q_def SQ_def)

lemma SQ_sub_Q: "SQ \<subseteq> Q"
  by (auto simp add: SQ_def Q_def)

(* set of formula indices *)

qualified definition nfa_fmla_set :: "nat set" where
  "nfa_fmla_set = \<Union>(fmla_set ` set transs)"

(* step relation *)

qualified definition step_eps :: "bool list \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "step_eps bs q q' \<longleftrightarrow> q \<in> SQ \<and>
    (case transs ! (q - q0) of eps_trans p n \<Rightarrow> n < length bs \<and> bs ! n \<and> p = q'
    | split_trans p p' \<Rightarrow> p = q' \<or> p' = q' | _ \<Rightarrow> False)"

lemma step_eps_dest: "step_eps bs q q' \<Longrightarrow> q \<in> SQ"
  by (auto simp add: step_eps_def)

lemma step_eps_mono: "step_eps [] q q' \<Longrightarrow> step_eps bs q q'"
  by (auto simp: step_eps_def split: transition.splits)

(* successors in step relation *)

qualified definition step_eps_sucs :: "bool list \<Rightarrow> state \<Rightarrow> state set" where
  "step_eps_sucs bs q = (if q \<in> SQ then
    (case transs ! (q - q0) of eps_trans p n \<Rightarrow> if n < length bs \<and> bs ! n then {p} else {}
    | split_trans p p' \<Rightarrow> {p, p'} | _ \<Rightarrow> {}) else {})"

lemma step_eps_sucs_sound: "q' \<in> step_eps_sucs bs q \<longleftrightarrow> step_eps bs q q'"
  by (auto simp add: step_eps_sucs_def step_eps_def split: transition.splits)

qualified definition step_eps_set :: "bool list \<Rightarrow> state set \<Rightarrow> state set" where
  "step_eps_set bs R = \<Union>(step_eps_sucs bs ` R)"

lemma step_eps_set_sound: "step_eps_set bs R = {q'. \<exists>q \<in> R. step_eps bs q q'}"
  using step_eps_sucs_sound by (auto simp add: step_eps_set_def)

lemma step_eps_set_mono: "R \<subseteq> S \<Longrightarrow> step_eps_set bs R \<subseteq> step_eps_set bs S"
  by (auto simp add: step_eps_set_def)

(* reflexive and transitive closure of step relation *)

qualified definition step_eps_closure :: "bool list \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "step_eps_closure bs = (step_eps bs)\<^sup>*\<^sup>*"

lemma step_eps_closure_dest: "step_eps_closure bs q q' \<Longrightarrow> q \<noteq> q' \<Longrightarrow> q \<in> SQ"
  unfolding step_eps_closure_def
  apply (induction q q' rule: rtranclp.induct) using step_eps_dest by auto

qualified definition step_eps_closure_set :: "state set \<Rightarrow> bool list \<Rightarrow> state set" where
  "step_eps_closure_set R bs = \<Union>((\<lambda>q. {q'. step_eps_closure bs q q'}) ` R)"

lemma step_eps_closure_set_refl: "R \<subseteq> step_eps_closure_set R bs"
  by (auto simp add: step_eps_closure_set_def step_eps_closure_def)

lemma step_eps_closure_set_mono: "R \<subseteq> S \<Longrightarrow> step_eps_closure_set R bs \<subseteq> step_eps_closure_set S bs"
  by (auto simp add: step_eps_closure_set_def)

lemma step_eps_closure_set_empty: "step_eps_closure_set {} bs = {}"
  by (auto simp add: step_eps_closure_set_def)

lemma step_eps_closure_set_mono': "step_eps_closure_set R [] \<subseteq> step_eps_closure_set R bs"
  by (auto simp: step_eps_closure_set_def step_eps_closure_def) (metis mono_rtranclp step_eps_mono)

lemma step_eps_closure_set_split: "step_eps_closure_set (R \<union> S) bs =
  step_eps_closure_set R bs \<union> step_eps_closure_set S bs"
  by (auto simp add: step_eps_closure_set_def)

lemma step_eps_closure_set_Un: "step_eps_closure_set (\<Union>x \<in> X. R x) bs =
  (\<Union>x \<in> X. step_eps_closure_set (R x) bs)"
  by (auto simp add: step_eps_closure_set_def)

lemma step_eps_closure_set_idem: "step_eps_closure_set (step_eps_closure_set R bs) bs =
  step_eps_closure_set R bs"
  unfolding step_eps_closure_set_def step_eps_closure_def by auto

lemma step_eps_closure_set_flip:
  assumes "step_eps_closure_set R bs = R \<union> S"
  shows "step_eps_closure_set S bs \<subseteq> R \<union> S"
  using step_eps_closure_set_idem[of R bs, unfolded assms, unfolded step_eps_closure_set_split]
  by auto

lemma step_eps_closure_set_unfold: "(\<And>q'. step_eps bs q q' \<longleftrightarrow> q' \<in> X) \<Longrightarrow>
  step_eps_closure_set {q} bs = {q} \<union> step_eps_closure_set X bs"
  unfolding step_eps_closure_set_def step_eps_closure_def
  using rtranclp_step[of "step_eps bs" q]
  by (auto simp add: converse_rtranclp_into_rtranclp)

lemma step_step_eps_closure: "step_eps bs q q' \<Longrightarrow> q \<in> R \<Longrightarrow> q' \<in> step_eps_closure_set R bs"
  unfolding step_eps_closure_set_def step_eps_closure_def by auto

lemma step_eps_closure_set_code[code]:
  "step_eps_closure_set R bs =
    (let R' = R \<union> step_eps_set bs R in if R = R' then R else step_eps_closure_set R' bs)"
  using rtranclp_closed
  by (auto simp add: step_eps_closure_set_def step_eps_closure_def step_eps_set_sound Let_def)

(* no step_eps *)

lemma step_eps_closure_empty: "step_eps_closure bs q q' \<Longrightarrow> (\<And>q'. \<not>step_eps bs q q') \<Longrightarrow> q = q'"
  unfolding step_eps_closure_def by (induction q q' rule: rtranclp.induct) auto

lemma step_eps_closure_set_step_id: "(\<And>q q'. q \<in> R \<Longrightarrow> \<not>step_eps bs q q') \<Longrightarrow>
  step_eps_closure_set R bs = R"
  using step_eps_closure_empty step_eps_closure_set_refl unfolding step_eps_closure_set_def by blast

(* symbol step relation *)

qualified definition step_symb :: "state \<Rightarrow> state \<Rightarrow> bool" where
  "step_symb q q' \<longleftrightarrow> q \<in> SQ \<and>
    (case transs ! (q - q0) of symb_trans p \<Rightarrow> p = q' | _ \<Rightarrow> False)"

lemma step_symb_dest: "step_symb q q' \<Longrightarrow> q \<in> SQ"
  by (auto simp add: step_symb_def)

(* successors in symbol step relation *)

qualified definition step_symb_sucs :: "state \<Rightarrow> state set" where
  "step_symb_sucs q = (if q \<in> SQ then
    (case transs ! (q - q0) of symb_trans p \<Rightarrow> {p} | _ \<Rightarrow> {}) else {})"

lemma step_symb_sucs_sound: "q' \<in> step_symb_sucs q \<longleftrightarrow> step_symb q q'"
  by (auto simp add: step_symb_sucs_def step_symb_def split: transition.splits)

qualified definition step_symb_set :: "state set \<Rightarrow> state set" where
  "step_symb_set R = {q'. \<exists>q \<in> R. step_symb q q'}"

lemma step_symb_set_mono: "R \<subseteq> S \<Longrightarrow> step_symb_set R \<subseteq> step_symb_set S"
  by (auto simp add: step_symb_set_def)

lemma step_symb_set_empty: "step_symb_set {} = {}"
  by (auto simp add: step_symb_set_def)

lemma step_symb_set_proj: "step_symb_set R = step_symb_set (R \<inter> SQ)"
  using step_symb_dest by (auto simp add: step_symb_set_def)

lemma step_symb_set_split: "step_symb_set (R \<union> S) = step_symb_set R \<union> step_symb_set S"
  by (auto simp add: step_symb_set_def)

lemma step_symb_set_Un: "step_symb_set (\<Union>x \<in> X. R x) = (\<Union>x \<in> X. step_symb_set (R x))"
  by (auto simp add: step_symb_set_def)

lemma step_symb_set_code[code]: "step_symb_set R = \<Union>(step_symb_sucs ` R)"
  using step_symb_sucs_sound by (auto simp add: step_symb_set_def)

(* delta function *)

qualified definition delta :: "state set \<Rightarrow> bool list \<Rightarrow> state set" where
  "delta R bs = step_symb_set (step_eps_closure_set R bs)"

lemma delta_eps: "delta (step_eps_closure_set R bs) bs = delta R bs"
  unfolding delta_def step_eps_closure_set_idem by (rule refl)

lemma delta_eps_split:
  assumes "step_eps_closure_set R bs = R \<union> S"
  shows "delta R bs = step_symb_set R \<union> delta S bs"
  unfolding delta_def assms step_symb_set_split
  using step_symb_set_mono[OF step_eps_closure_set_flip[OF assms], unfolded step_symb_set_split]
    step_symb_set_mono[OF step_eps_closure_set_refl] by auto

lemma delta_split: "delta (R \<union> S) bs = delta R bs \<union> delta S bs"
  by (auto simp add: delta_def step_symb_set_split step_eps_closure_set_split)

lemma delta_Un: "delta (\<Union>x \<in> X. R x) bs = (\<Union>x \<in> X. delta (R x) bs)"
  unfolding delta_def step_eps_closure_set_Un step_symb_set_Un by simp

lemma delta_step_symb_set_absorb: "delta R bs = delta R bs \<union> step_symb_set R"
  using step_eps_closure_set_refl by (auto simp add: delta_def step_symb_set_def)

lemma delta_sub_eps_mono:
  assumes "S \<subseteq> step_eps_closure_set R bs"
  shows "delta S bs \<subseteq> delta R bs"
  unfolding delta_def
  using step_symb_set_mono[OF step_eps_closure_set_mono[OF assms, of bs,
        unfolded step_eps_closure_set_idem]] by simp

(* run delta function *)

qualified definition run :: "state set \<Rightarrow> bool list list \<Rightarrow> state set" where
  "run R bss = foldl delta R bss"

lemma run_eps_split:
  assumes "step_eps_closure_set R bs = R \<union> S" "step_symb_set R = {}"
  shows "run R (bs # bss) = run S (bs # bss)"
  unfolding run_def foldl.simps delta_eps_split[OF assms(1), unfolded assms(2)]
  by auto

lemma run_empty: "run {} bss = {}"
  unfolding run_def
  by (induction bss)
     (auto simp add: delta_def step_symb_set_empty step_eps_closure_set_empty)

lemma run_Nil: "run R [] = R"
  by (auto simp add: run_def)

lemma run_Cons: "run R (bs # bss) = run (delta R bs) bss"
  unfolding run_def by simp

lemma run_split: "run (R \<union> S) bss = run R bss \<union> run S bss"
  unfolding run_def
  by (induction bss arbitrary: R S) (auto simp add: delta_split)

lemma run_Un: "run (\<Union>x \<in> X. R x) bss = (\<Union>x \<in> X. run (R x) bss)"
  unfolding run_def
  by (induction bss arbitrary: R) (auto simp add: delta_Un)

lemma run_comp: "run R (bss @ css) = run (run R bss) css"
  unfolding run_def by simp

(* accept function *)

qualified definition accept_eps :: "state set \<Rightarrow> bool list \<Rightarrow> bool" where
  "accept_eps R bs \<longleftrightarrow> (qf \<in> step_eps_closure_set R bs)"

lemma step_eps_accept_eps: "step_eps bs q qf \<Longrightarrow> q \<in> R \<Longrightarrow> accept_eps R bs"
  unfolding accept_eps_def using step_step_eps_closure by simp

lemma accept_eps_empty: "accept_eps {} bs \<longleftrightarrow> False"
  by (auto simp add: accept_eps_def step_eps_closure_set_def)

lemma accept_eps_split: "accept_eps (R \<union> S) bs \<longleftrightarrow> accept_eps R bs \<or> accept_eps S bs"
  by (auto simp add: accept_eps_def step_eps_closure_set_split)

lemma accept_eps_Un: "accept_eps (\<Union>x \<in> X. R x) bs \<longleftrightarrow> (\<exists>x \<in> X. accept_eps (R x) bs)"
  by (auto simp add: accept_eps_def step_eps_closure_set_def)

qualified definition accept :: "state set \<Rightarrow> bool" where
  "accept R \<longleftrightarrow> accept_eps R []"

(* is a run accepting? *)

qualified definition run_accept_eps :: "state set \<Rightarrow> bool list list \<Rightarrow> bool list \<Rightarrow> bool" where
  "run_accept_eps R bss bs = accept_eps (run R bss) bs"

lemma run_accept_eps_empty: "\<not>run_accept_eps {} bss bs"
  unfolding run_accept_eps_def run_empty accept_eps_empty by simp

lemma run_accept_eps_Nil: "run_accept_eps R [] cs \<longleftrightarrow> accept_eps R cs"
  by (auto simp add: run_accept_eps_def run_Nil)

lemma run_accept_eps_Cons: "run_accept_eps R (bs # bss) cs \<longleftrightarrow> run_accept_eps (delta R bs) bss cs"
  by (auto simp add: run_accept_eps_def run_Cons)

lemma run_accept_eps_Cons_delta_cong: "delta R bs = delta S bs \<Longrightarrow>
  run_accept_eps R (bs # bss) cs \<longleftrightarrow> run_accept_eps S (bs # bss) cs"
  unfolding run_accept_eps_Cons by auto

lemma run_accept_eps_Nil_eps: "run_accept_eps (step_eps_closure_set R bs) [] bs \<longleftrightarrow> run_accept_eps R [] bs"
  unfolding run_accept_eps_Nil accept_eps_def step_eps_closure_set_idem by (rule refl)

lemma run_accept_eps_Cons_eps: "run_accept_eps (step_eps_closure_set R cs) (cs # css) bs \<longleftrightarrow>
  run_accept_eps R (cs # css) bs"
  unfolding run_accept_eps_Cons delta_eps by (rule refl)

lemma run_accept_eps_Nil_eps_split:
  assumes "step_eps_closure_set R bs = R \<union> S" "step_symb_set R = {}" "qf \<notin> R"
  shows "run_accept_eps R [] bs = run_accept_eps S [] bs"
  unfolding Nil run_accept_eps_Nil accept_eps_def assms(1)
  using assms(3) step_eps_closure_set_refl step_eps_closure_set_flip[OF assms(1)] by auto

lemma run_accept_eps_Cons_eps_split:
  assumes "step_eps_closure_set R cs = R \<union> S" "step_symb_set R = {}" "qf \<notin> R"
  shows "run_accept_eps R (cs # css) bs = run_accept_eps S (cs # css) bs"
  unfolding run_accept_eps_def Cons run_eps_split[OF assms(1,2)] by (rule refl)

lemma run_accept_eps_split: "run_accept_eps (R \<union> S) bss bs \<longleftrightarrow>
  run_accept_eps R bss bs \<or> run_accept_eps S bss bs"
  unfolding run_accept_eps_def run_split accept_eps_split by auto

lemma run_accept_eps_Un: "run_accept_eps (\<Union>x \<in> X. R x) bss bs \<longleftrightarrow>
  (\<exists>x \<in> X. run_accept_eps (R x) bss bs)"
  unfolding run_accept_eps_def run_Un accept_eps_Un by simp

qualified definition run_accept :: "state set \<Rightarrow> bool list list \<Rightarrow> bool" where
  "run_accept R bss = accept (run R bss)"

end

definition "iarray_of_list xs = IArray xs"

context fixes
  transs :: "transition iarray"
  and len :: nat
begin

qualified definition step_eps' :: "bool iarray \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "step_eps' bs q q' \<longleftrightarrow> q < len \<and>
    (case transs !! q of eps_trans p n \<Rightarrow> n < IArray.length bs \<and> bs !! n \<and> p = q'
    | split_trans p p' \<Rightarrow> p = q' \<or> p' = q' | _ \<Rightarrow> False)"

qualified definition step_eps_closure' :: "bool iarray \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "step_eps_closure' bs = (step_eps' bs)\<^sup>*\<^sup>*"

qualified definition step_eps_sucs' :: "bool iarray \<Rightarrow> state \<Rightarrow> state set" where
  "step_eps_sucs' bs q = (if q < len then
    (case transs !! q of eps_trans p n \<Rightarrow> if n < IArray.length bs \<and> bs !! n then {p} else {}
    | split_trans p p' \<Rightarrow> {p, p'} | _ \<Rightarrow> {}) else {})"

lemma step_eps_sucs'_sound: "q' \<in> step_eps_sucs' bs q \<longleftrightarrow> step_eps' bs q q'"
  by (auto simp add: step_eps_sucs'_def step_eps'_def split: transition.splits)

qualified definition step_eps_set' :: "bool iarray \<Rightarrow> state set \<Rightarrow> state set" where
  "step_eps_set' bs R = \<Union>(step_eps_sucs' bs ` R)"

lemma step_eps_set'_sound: "step_eps_set' bs R = {q'. \<exists>q \<in> R. step_eps' bs q q'}"
  using step_eps_sucs'_sound by (auto simp add: step_eps_set'_def)

qualified definition step_eps_closure_set' :: "state set \<Rightarrow> bool iarray \<Rightarrow> state set" where
  "step_eps_closure_set' R bs = \<Union>((\<lambda>q. {q'. step_eps_closure' bs q q'}) ` R)"

lemma step_eps_closure_set'_code[code]:
  "step_eps_closure_set' R bs =
    (let R' = R \<union> step_eps_set' bs R in if R = R' then R else step_eps_closure_set' R' bs)"
  using rtranclp_closed
  by (auto simp add: step_eps_closure_set'_def step_eps_closure'_def step_eps_set'_sound Let_def)

qualified definition step_symb_sucs' :: "state \<Rightarrow> state set" where
  "step_symb_sucs' q = (if q < len then
    (case transs !! q of symb_trans p \<Rightarrow> {p} | _ \<Rightarrow> {}) else {})"

qualified definition step_symb_set' :: "state set \<Rightarrow> state set" where
  "step_symb_set' R = \<Union>(step_symb_sucs' ` R)"

qualified definition delta' :: "state set \<Rightarrow> bool iarray \<Rightarrow> state set" where
  "delta' R bs = step_symb_set' (step_eps_closure_set' R bs)"

qualified definition accept_eps' :: "state set \<Rightarrow> bool iarray \<Rightarrow> bool" where
  "accept_eps' R bs \<longleftrightarrow> (len \<in> step_eps_closure_set' R bs)"

qualified definition accept' :: "state set \<Rightarrow> bool" where
  "accept' R \<longleftrightarrow> accept_eps' R (iarray_of_list [])"

qualified definition run' :: "state set \<Rightarrow> bool iarray list \<Rightarrow> state set" where
  "run' R bss = foldl delta' R bss"

qualified definition run_accept_eps' :: "state set \<Rightarrow> bool iarray list \<Rightarrow> bool iarray \<Rightarrow> bool" where
  "run_accept_eps' R bss bs = accept_eps' (run' R bss) bs"

qualified definition run_accept' :: "state set \<Rightarrow> bool iarray list \<Rightarrow> bool" where
  "run_accept' R bss = accept' (run' R bss)"

end

locale nfa_array =
  fixes transs :: "transition list"
    and transs' :: "transition iarray"
    and len :: nat
  assumes transs_eq: "transs' = IArray transs"
    and len_def: "len = length transs"
begin

abbreviation "step_eps \<equiv> NFA.step_eps 0 transs"
abbreviation "step_eps' \<equiv> NFA.step_eps' transs' len"
abbreviation "step_eps_closure \<equiv> NFA.step_eps_closure 0 transs"
abbreviation "step_eps_closure' \<equiv> NFA.step_eps_closure' transs' len"
abbreviation "step_eps_sucs \<equiv> NFA.step_eps_sucs 0 transs"
abbreviation "step_eps_sucs' \<equiv> NFA.step_eps_sucs' transs' len"
abbreviation "step_eps_set \<equiv> NFA.step_eps_set 0 transs"
abbreviation "step_eps_set' \<equiv> NFA.step_eps_set' transs' len"
abbreviation "step_eps_closure_set \<equiv> NFA.step_eps_closure_set 0 transs"
abbreviation "step_eps_closure_set' \<equiv> NFA.step_eps_closure_set' transs' len"
abbreviation "step_symb_sucs \<equiv> NFA.step_symb_sucs 0 transs"
abbreviation "step_symb_sucs' \<equiv> NFA.step_symb_sucs' transs' len"
abbreviation "step_symb_set \<equiv> NFA.step_symb_set 0 transs"
abbreviation "step_symb_set' \<equiv> NFA.step_symb_set' transs' len"
abbreviation "delta \<equiv> NFA.delta 0 transs"
abbreviation "delta' \<equiv> NFA.delta' transs' len"
abbreviation "accept_eps \<equiv> NFA.accept_eps 0 len transs"
abbreviation "accept_eps' \<equiv> NFA.accept_eps' transs' len"
abbreviation "accept \<equiv> NFA.accept 0 len transs"
abbreviation "accept' \<equiv> NFA.accept' transs' len"
abbreviation "run \<equiv> NFA.run 0 transs"
abbreviation "run' \<equiv> NFA.run' transs' len"
abbreviation "run_accept_eps \<equiv> NFA.run_accept_eps 0 len transs"
abbreviation "run_accept_eps' \<equiv> NFA.run_accept_eps' transs' len"
abbreviation "run_accept \<equiv> NFA.run_accept 0 len transs"
abbreviation "run_accept' \<equiv> NFA.run_accept' transs' len"

lemma q_in_SQ: "q \<in> NFA.SQ 0 transs \<longleftrightarrow> q < len"
  using len_def
  by (auto simp: NFA.SQ_def)

lemma step_eps'_eq: "bs' = IArray bs \<Longrightarrow> step_eps bs q q' \<longleftrightarrow> step_eps' bs' q q'"
  by (auto simp: NFA.step_eps_def NFA.step_eps'_def q_in_SQ transs_eq split: transition.splits)

lemma step_eps_closure'_eq: "bs' = IArray bs \<Longrightarrow> step_eps_closure bs q q' \<longleftrightarrow> step_eps_closure' bs' q q'"
proof -
  assume lassm: "bs' = IArray bs"
  have step_eps_eq_folded: "step_eps bs = step_eps' bs'"
    using step_eps'_eq[OF lassm]
    by auto
  show ?thesis
    by (auto simp: NFA.step_eps_closure_def NFA.step_eps_closure'_def step_eps_eq_folded)
qed

lemma step_eps_sucs'_eq: "bs' = IArray bs \<Longrightarrow> step_eps_sucs bs q = step_eps_sucs' bs' q"
  by (auto simp: NFA.step_eps_sucs_def NFA.step_eps_sucs'_def q_in_SQ transs_eq
      split: transition.splits)

lemma step_eps_set'_eq: "bs' = IArray bs \<Longrightarrow> step_eps_set bs R = step_eps_set' bs' R"
  by (auto simp: NFA.step_eps_set_def NFA.step_eps_set'_def step_eps_sucs'_eq)

lemma step_eps_closure_set'_eq: "bs' = IArray bs \<Longrightarrow> step_eps_closure_set R bs = step_eps_closure_set' R bs'"
  by (auto simp: NFA.step_eps_closure_set_def NFA.step_eps_closure_set'_def step_eps_closure'_eq)

lemma step_symb_sucs'_eq: "bs' = IArray bs \<Longrightarrow> step_symb_sucs R = step_symb_sucs' R"
  by (auto simp: NFA.step_symb_sucs_def NFA.step_symb_sucs'_def q_in_SQ transs_eq
      split: transition.splits)

lemma step_symb_set'_eq: "bs' = IArray bs \<Longrightarrow> step_symb_set R = step_symb_set' R"
  by (auto simp: step_symb_set_code NFA.step_symb_set'_def step_symb_sucs'_eq)

lemma delta'_eq: "bs' = IArray bs \<Longrightarrow> delta R bs = delta' R bs'"
  by (auto simp: NFA.delta_def NFA.delta'_def step_eps_closure_set'_eq step_symb_set'_eq)

lemma accept_eps'_eq: "bs' = IArray bs \<Longrightarrow> accept_eps R bs = accept_eps' R bs'"
  by (auto simp: NFA.accept_eps_def NFA.accept_eps'_def step_eps_closure_set'_eq)

lemma accept'_eq: "accept R = accept' R"
  by (auto simp: NFA.accept_def NFA.accept'_def accept_eps'_eq iarray_of_list_def)

lemma run'_eq: "bss' = map IArray bss \<Longrightarrow> run R bss = run' R bss'"
  by (induction bss arbitrary: R bss') (auto simp: NFA.run_def NFA.run'_def delta'_eq)

lemma run_accept_eps'_eq: "bss' = map IArray bss \<Longrightarrow> bs' = IArray bs \<Longrightarrow>
  run_accept_eps R bss bs \<longleftrightarrow> run_accept_eps' R bss' bs'"
  by (auto simp: NFA.run_accept_eps_def NFA.run_accept_eps'_def accept_eps'_eq run'_eq)

lemma run_accept'_eq: "bss' = map IArray bss \<Longrightarrow>
  run_accept R bss \<longleftrightarrow> run_accept' R bss'"
  by (auto simp: NFA.run_accept_def NFA.run_accept'_def run'_eq accept'_eq)

end

locale nfa =
  fixes q0 :: nat
    and qf :: nat
    and transs :: "transition list"
  assumes state_closed: "\<And>t. t \<in> set transs \<Longrightarrow> state_set t \<subseteq> NFA.Q q0 qf transs"
    and transs_not_Nil: "transs \<noteq> []"
    and qf_not_in_SQ: "qf \<notin> NFA.SQ q0 transs"
begin

abbreviation "SQ \<equiv> NFA.SQ q0 transs"
abbreviation "Q \<equiv> NFA.Q q0 qf transs"
abbreviation "nfa_fmla_set \<equiv> NFA.nfa_fmla_set transs"
abbreviation "step_eps \<equiv> NFA.step_eps q0 transs"
abbreviation "step_eps_sucs \<equiv> NFA.step_eps_sucs q0 transs"
abbreviation "step_eps_set \<equiv> NFA.step_eps_set q0 transs"
abbreviation "step_eps_closure \<equiv> NFA.step_eps_closure q0 transs"
abbreviation "step_eps_closure_set \<equiv> NFA.step_eps_closure_set q0 transs"
abbreviation "step_symb \<equiv> NFA.step_symb q0 transs"
abbreviation "step_symb_sucs \<equiv> NFA.step_symb_sucs q0 transs"
abbreviation "step_symb_set \<equiv> NFA.step_symb_set q0 transs"
abbreviation "delta \<equiv> NFA.delta q0 transs"
abbreviation "run \<equiv> NFA.run q0 transs"
abbreviation "accept_eps \<equiv> NFA.accept_eps q0 qf transs"
abbreviation "run_accept_eps \<equiv> NFA.run_accept_eps q0 qf transs"

lemma Q_diff_qf_SQ: "Q - {qf} = SQ"
  using qf_not_in_SQ by (auto simp add: NFA.Q_def)

lemma q0_sub_SQ: "{q0} \<subseteq> SQ"
  using transs_not_Nil by (auto simp add: NFA.SQ_def)

lemma q0_sub_Q: "{q0} \<subseteq> Q"
  using q0_sub_SQ SQ_sub_Q by auto

lemma step_eps_closed: "step_eps bs q q' \<Longrightarrow> q' \<in> Q"
  using transs_q_in_set state_closed
  by (fastforce simp add: NFA.step_eps_def split: transition.splits)

lemma step_eps_set_closed: "step_eps_set bs R \<subseteq> Q"
  using step_eps_closed by (auto simp add: step_eps_set_sound)

lemma step_eps_closure_closed: "step_eps_closure bs q q' \<Longrightarrow> q \<noteq> q' \<Longrightarrow> q' \<in> Q"
  unfolding NFA.step_eps_closure_def
  apply (induction q q' rule: rtranclp.induct) using step_eps_closed by auto

lemma step_eps_closure_set_closed_union: "step_eps_closure_set R bs \<subseteq> R \<union> Q"
  using step_eps_closure_closed by (auto simp add: NFA.step_eps_closure_set_def NFA.step_eps_closure_def)

lemma step_eps_closure_set_closed: "R \<subseteq> Q \<Longrightarrow> step_eps_closure_set R bs \<subseteq> Q"
  using step_eps_closure_set_closed_union by auto

lemma step_symb_closed: "step_symb q q' \<Longrightarrow> q' \<in> Q"
  using transs_q_in_set state_closed
  by (fastforce simp add: NFA.step_symb_def split: transition.splits)

lemma step_symb_set_closed: "step_symb_set R \<subseteq> Q"
  using step_symb_closed by (auto simp add: NFA.step_symb_set_def)

lemma step_symb_set_qf: "step_symb_set {qf} = {}"
  using qf_not_in_SQ step_symb_set_proj[of _ _ "{qf}"] step_symb_set_empty by auto

lemma delta_closed: "delta R bs \<subseteq> Q"
  using step_symb_set_closed by (auto simp add: NFA.delta_def)

lemma run_closed_Cons: "run R (bs # bss) \<subseteq> Q"
  unfolding NFA.run_def
  using delta_closed by (induction bss arbitrary: R bs) auto

lemma run_closed: "R \<subseteq> Q \<Longrightarrow> run R bss \<subseteq> Q"
  using run_Nil run_closed_Cons by (cases bss) auto

(* transitions from accepting state *)

lemma step_eps_qf: "step_eps bs qf q \<longleftrightarrow> False"
  using qf_not_in_SQ step_eps_dest by force

lemma step_symb_qf: "step_symb qf q \<longleftrightarrow> False"
  using qf_not_in_SQ step_symb_dest by force

lemma step_eps_closure_qf: "step_eps_closure bs q q' \<Longrightarrow> q = qf \<Longrightarrow> q = q'"
  unfolding NFA.step_eps_closure_def
  apply (induction q q' rule: rtranclp.induct) using step_eps_qf by auto

lemma step_eps_closure_set_qf: "step_eps_closure_set {qf} bs = {qf}"
  using step_eps_closure_qf unfolding NFA.step_eps_closure_set_def NFA.step_eps_closure_def by auto

lemma delta_qf: "delta {qf} bs = {}"
  using step_eps_closure_qf step_symb_qf
  by (auto simp add: NFA.delta_def NFA.step_symb_set_def NFA.step_eps_closure_set_def)

lemma run_qf_many: "run {qf} (bs # bss) = {}"
  unfolding run_Cons delta_qf run_empty by (rule refl)

lemma run_accept_eps_qf_many: "run_accept_eps {qf} (bs # bss) cs \<longleftrightarrow> False"
  unfolding NFA.run_accept_eps_def using run_qf_many accept_eps_empty by simp

lemma run_accept_eps_qf_one: "run_accept_eps {qf} [] bs \<longleftrightarrow> True"
  unfolding NFA.run_accept_eps_def NFA.accept_eps_def using run_Nil step_eps_closure_set_refl by force

end

locale nfa_cong = nfa q0 qf transs + nfa': nfa q0' qf' transs'
  for q0 q0' qf qf' transs transs' +
  assumes SQ_sub: "nfa'.SQ \<subseteq> SQ" and
  qf_eq: "qf = qf'" and
  transs_eq: "\<And>q. q \<in> nfa'.SQ \<Longrightarrow> transs ! (q - q0) = transs' ! (q - q0')"
begin

lemma q_Q_SQ_nfa'_SQ:  "q \<in> nfa'.Q \<Longrightarrow> q \<in> SQ \<longleftrightarrow> q \<in> nfa'.SQ"
  using SQ_sub qf_not_in_SQ qf_eq by (auto simp add: NFA.Q_def)

lemma step_eps_cong: "q \<in> nfa'.Q \<Longrightarrow> step_eps bs q q' \<longleftrightarrow> nfa'.step_eps bs q q'"
  using q_Q_SQ_nfa'_SQ transs_eq by (auto simp add: NFA.step_eps_def)

lemma eps_nfa'_step_eps_closure: "step_eps_closure bs q q' \<Longrightarrow> q \<in> nfa'.Q \<Longrightarrow>
  q' \<in> nfa'.Q \<and> nfa'.step_eps_closure bs q q'"
  unfolding NFA.step_eps_closure_def
  apply (induction q q' rule: rtranclp.induct)
  using nfa'.step_eps_closure_closed step_eps_cong by (auto simp add: NFA.step_eps_closure_def)

lemma nfa'_eps_step_eps_closure: "nfa'.step_eps_closure bs q q' \<Longrightarrow> q \<in> nfa'.Q \<Longrightarrow>
  q' \<in> nfa'.Q \<and> step_eps_closure bs q q'"
  unfolding NFA.step_eps_closure_def
  apply (induction q q' rule: rtranclp.induct)
  using nfa'.step_eps_closed step_eps_cong
  by (auto simp add: NFA.step_eps_closure_def intro: rtranclp.intros(2))

lemma step_eps_closure_set_cong: "R \<subseteq> nfa'.Q \<Longrightarrow> step_eps_closure_set R bs =
  nfa'.step_eps_closure_set R bs"
  using eps_nfa'_step_eps_closure nfa'_eps_step_eps_closure
  by (fastforce simp add: NFA.step_eps_closure_set_def)

lemma step_symb_cong: "q \<in> nfa'.Q \<Longrightarrow> step_symb q q' \<longleftrightarrow> nfa'.step_symb q q'"
  using q_Q_SQ_nfa'_SQ transs_eq by (auto simp add: NFA.step_symb_def)

lemma step_symb_set_cong: "R \<subseteq> nfa'.Q \<Longrightarrow> step_symb_set R = nfa'.step_symb_set R"
  using step_symb_cong by (auto simp add: NFA.step_symb_set_def)

lemma delta_cong: "R \<subseteq> nfa'.Q \<Longrightarrow> delta R bs = nfa'.delta R bs"
  using step_symb_set_cong nfa'.step_eps_closure_set_closed
  by (auto simp add: NFA.delta_def step_eps_closure_set_cong)

lemma run_cong: "R \<subseteq> nfa'.Q \<Longrightarrow> run R bss = nfa'.run R bss"
  unfolding NFA.run_def
  using nfa'.delta_closed delta_cong by (induction bss arbitrary: R) auto

lemma accept_eps_cong: "R \<subseteq> nfa'.Q \<Longrightarrow> accept_eps R bs \<longleftrightarrow> nfa'.accept_eps R bs"
  unfolding NFA.accept_eps_def using step_eps_closure_set_cong qf_eq by auto

lemma run_accept_eps_cong:
  assumes "R \<subseteq> nfa'.Q"
  shows "run_accept_eps R bss bs \<longleftrightarrow> nfa'.run_accept_eps R bss bs"
  unfolding NFA.run_accept_eps_def run_cong[OF assms]
    accept_eps_cong[OF nfa'.run_closed[OF assms]] by simp

end

fun list_split :: "'a list \<Rightarrow> ('a list \<times> 'a list) set" where
  "list_split [] = {}"
| "list_split (x # xs) = {([], x # xs)} \<union> (\<Union>(ys, zs) \<in> list_split xs. {(x # ys, zs)})"

lemma list_split_unfold: "(\<Union>(ys, zs) \<in> list_split (x # xs). f ys zs) =
  f [] (x # xs) \<union> (\<Union>(ys, zs) \<in> list_split xs. f (x # ys) zs)"
  by (induction xs) auto

lemma list_split_def: "list_split xs = (\<Union>n < length xs. {(take n xs, drop n xs)})"
  using less_Suc_eq_0_disj by (induction xs rule: list_split.induct) auto+

locale nfa_cong' = nfa q0 qf transs + nfa': nfa q0' qf' transs'
  for q0 q0' qf qf' transs transs' +
  assumes SQ_sub: "nfa'.SQ \<subseteq> SQ" and
  qf'_in_SQ: "qf' \<in> SQ" and
  transs_eq: "\<And>q. q \<in> nfa'.SQ \<Longrightarrow> transs ! (q - q0) = transs' ! (q - q0')"
begin

lemma nfa'_Q_sub_Q: "nfa'.Q \<subseteq> Q"
  unfolding NFA.Q_def using SQ_sub qf'_in_SQ by auto

lemma q_SQ_SQ_nfa'_SQ:  "q \<in> nfa'.SQ \<Longrightarrow> q \<in> SQ \<longleftrightarrow> q \<in> nfa'.SQ"
  using SQ_sub by auto

lemma step_eps_cong_SQ: "q \<in> nfa'.SQ \<Longrightarrow> step_eps bs q q' \<longleftrightarrow> nfa'.step_eps bs q q'"
  using q_SQ_SQ_nfa'_SQ transs_eq by (auto simp add: NFA.step_eps_def)

lemma step_eps_cong_Q: "q \<in> nfa'.Q \<Longrightarrow> nfa'.step_eps bs q q' \<Longrightarrow> step_eps bs q q'"
  using SQ_sub transs_eq by (auto simp add: NFA.step_eps_def)

lemma nfa'_step_eps_closure_cong: "nfa'.step_eps_closure bs q q' \<Longrightarrow> q \<in> nfa'.Q \<Longrightarrow>
  step_eps_closure bs q q'"
  unfolding NFA.step_eps_closure_def
  apply (induction q q' rule: rtranclp.induct)
  using NFA.Q_def NFA.step_eps_closure_def
  by (auto simp add: rtranclp.rtrancl_into_rtrancl step_eps_cong_SQ step_eps_dest)

lemma nfa'_step_eps_closure_set_sub: "R \<subseteq> nfa'.Q \<Longrightarrow> nfa'.step_eps_closure_set R bs \<subseteq>
  step_eps_closure_set R bs"
  unfolding NFA.step_eps_closure_set_def
  using nfa'_step_eps_closure_cong by fastforce

lemma eps_nfa'_step_eps_closure_cong: "step_eps_closure bs q q' \<Longrightarrow> q \<in> nfa'.Q \<Longrightarrow>
  (q' \<in> nfa'.Q \<and> nfa'.step_eps_closure bs q q') \<or>
  (nfa'.step_eps_closure bs q qf' \<and> step_eps_closure bs qf' q')"
  unfolding NFA.step_eps_closure_def
  apply (induction q q' rule: rtranclp.induct)
  using nfa'.step_eps_closure_closed nfa'.step_eps_closed step_eps_cong_SQ NFA.Q_def
  by (auto simp add: intro: rtranclp.rtrancl_into_rtrancl) fastforce+

lemma nfa'_eps_step_eps_closure_cong: "nfa'.step_eps_closure bs q q' \<Longrightarrow> q \<in> nfa'.Q \<Longrightarrow>
  q' \<in> nfa'.Q \<and> step_eps_closure bs q q'"
  unfolding NFA.step_eps_closure_def
  apply (induction q q' rule: rtranclp.induct)
  using nfa'.step_eps_closed step_eps_cong_Q
  by (auto intro: rtranclp.intros(2))

lemma step_eps_closure_set_cong_reach: "R \<subseteq> nfa'.Q \<Longrightarrow> qf' \<in> nfa'.step_eps_closure_set R bs \<Longrightarrow>
  step_eps_closure_set R bs = nfa'.step_eps_closure_set R bs \<union> step_eps_closure_set {qf'} bs"
  using eps_nfa'_step_eps_closure_cong nfa'_eps_step_eps_closure_cong
    rtranclp_trans[of "step_eps bs"]
  unfolding NFA.step_eps_closure_set_def NFA.step_eps_closure_def
  by auto blast+

lemma step_eps_closure_set_cong_unreach: "R \<subseteq> nfa'.Q \<Longrightarrow> qf' \<notin> nfa'.step_eps_closure_set R bs \<Longrightarrow>
  step_eps_closure_set R bs = nfa'.step_eps_closure_set R bs"
  using eps_nfa'_step_eps_closure_cong nfa'_eps_step_eps_closure_cong
  unfolding NFA.step_eps_closure_set_def NFA.step_eps_closure_def
  by auto blast+

lemma step_symb_cong_SQ: "q \<in> nfa'.SQ \<Longrightarrow> step_symb q q' \<longleftrightarrow> nfa'.step_symb q q'"
  using q_SQ_SQ_nfa'_SQ transs_eq by (auto simp add: NFA.step_symb_def)

lemma step_symb_cong_Q: "nfa'.step_symb q q' \<Longrightarrow> step_symb q q'"
  using SQ_sub transs_eq by (auto simp add: NFA.step_symb_def)

lemma step_symb_set_cong_SQ: "R \<subseteq> nfa'.SQ \<Longrightarrow> step_symb_set R = nfa'.step_symb_set R"
  using step_symb_cong_SQ by (auto simp add: NFA.step_symb_set_def)

lemma step_symb_set_cong_Q: "nfa'.step_symb_set R \<subseteq> step_symb_set R"
  using step_symb_cong_Q by (auto simp add: NFA.step_symb_set_def)

lemma delta_cong_unreach:
  assumes "R \<subseteq> nfa'.Q" "\<not>nfa'.accept_eps R bs"
  shows "delta R bs = nfa'.delta R bs"
proof -
  have "nfa'.step_eps_closure_set R bs \<subseteq> nfa'.SQ"
    using nfa'.step_eps_closure_set_closed[OF assms(1), unfolded NFA.Q_def]
      assms(2)[unfolded NFA.accept_eps_def] by auto
  then show ?thesis
    unfolding NFA.accept_eps_def NFA.delta_def using step_symb_set_cong_SQ
      step_eps_closure_set_cong_unreach[OF assms(1) assms(2)[unfolded NFA.accept_eps_def]]
    by auto
qed

lemma nfa'_delta_sub_delta:
  assumes "R \<subseteq> nfa'.Q"
  shows "nfa'.delta R bs \<subseteq> delta R bs"
  unfolding NFA.delta_def
  using step_symb_set_mono[OF nfa'_step_eps_closure_set_sub[OF assms]] step_symb_set_cong_Q
  by fastforce

lemma delta_cong_reach:
  assumes "R \<subseteq> nfa'.Q" "nfa'.accept_eps R bs"
  shows "delta R bs = nfa'.delta R bs \<union> delta {qf'} bs"
proof (rule set_eqI, rule iffI)
  fix q
  assume assm: "q \<in> delta R bs"
  have nfa'_eps_diff_Un: "nfa'.step_eps_closure_set R bs =
    nfa'.step_eps_closure_set R bs - {qf'} \<union> {qf'}"
    using assms(2)[unfolded NFA.accept_eps_def] by auto
  from assm have "q \<in> step_symb_set (nfa'.step_eps_closure_set R bs - {qf'}) \<union>
    step_symb_set {qf'} \<union> delta {qf'} bs"
    unfolding NFA.delta_def step_eps_closure_set_cong_reach[OF assms(1)
      assms(2)[unfolded NFA.accept_eps_def]] step_symb_set_split[symmetric]
      nfa'_eps_diff_Un[symmetric] by simp
  then have "q \<in> step_symb_set (nfa'.step_eps_closure_set R bs - {qf'}) \<union> delta {qf'} bs"
    using step_symb_set_mono[of "{qf'}" "step_eps_closure_set {qf'} bs",
      OF step_eps_closure_set_refl, unfolded NFA.delta_def[symmetric]]
    delta_step_symb_set_absorb by blast
  then show "q \<in> nfa'.delta R bs \<union> delta {qf'} bs"
    unfolding NFA.delta_def
    using nfa'.step_eps_closure_set_closed[OF assms(1), unfolded NFA.Q_def]
      step_symb_set_cong_SQ[of "nfa'.step_eps_closure_set R bs - {qf'}"]
      step_symb_set_mono by blast
next
  fix q
  assume "q \<in> nfa'.delta R bs \<union> delta {qf'} bs"
  then show "q \<in> delta R bs"
    using nfa'_delta_sub_delta[OF assms(1)] delta_sub_eps_mono[of "{qf'}" _ _ R bs]
      assms(2)[unfolded NFA.accept_eps_def] nfa'_step_eps_closure_set_sub[OF assms(1)]
    by fastforce
qed

lemma run_cong:
  assumes "R \<subseteq> nfa'.Q"
  shows "run R bss = nfa'.run R bss \<union> (\<Union>(css, css') \<in> list_split bss.
    if nfa'.run_accept_eps R css (hd css') then run {qf'} css' else {})"
  using assms
proof (induction bss arbitrary: R rule: list_split.induct)
  case 1
  then show ?case
    using run_Nil by simp
next
  case (2 x xs)
  show ?case
    apply (cases "nfa'.accept_eps R x")
    unfolding run_Cons delta_cong_reach[OF 2(2)]
      delta_cong_unreach[OF 2(2)] run_split run_accept_eps_Nil run_accept_eps_Cons
      list_split_unfold[of "\<lambda>ys zs. if nfa'.run_accept_eps R ys (hd zs)
      then run {qf'} zs else {}" x xs] using 2(1)[of "nfa'.delta R x",
    OF nfa'.delta_closed, unfolded run_accept_eps_Nil] by auto
qed

lemma run_cong_Cons_sub:
  assumes "R \<subseteq> nfa'.Q" "delta {qf'} bs \<subseteq> nfa'.delta R bs"
  shows "run R (bs # bss) = nfa'.run R (bs # bss) \<union>
    (\<Union>(css, css') \<in> list_split bss.
    if nfa'.run_accept_eps (nfa'.delta R bs) css (hd css') then run {qf'} css' else {})"
  unfolding run_Cons using run_cong[OF nfa'.delta_closed]
    delta_cong_reach[OF assms(1)] delta_cong_unreach[OF assms(1)]
  by (cases "nfa'.accept_eps R bs") (auto simp add: Un_absorb2[OF assms(2)])

lemma accept_eps_nfa'_run:
  assumes "R \<subseteq> nfa'.Q"
  shows "accept_eps (nfa'.run R bss) bs \<longleftrightarrow>
    nfa'.accept_eps (nfa'.run R bss) bs \<and> accept_eps (run {qf'} []) bs"
  unfolding NFA.accept_eps_def run_Nil
  using step_eps_closure_set_cong_reach[OF nfa'.run_closed[OF assms]]
    step_eps_closure_set_cong_unreach[OF nfa'.run_closed[OF assms]] qf_not_in_SQ
    qf'_in_SQ nfa'.step_eps_closure_set_closed[OF nfa'.run_closed[OF assms],
    unfolded NFA.Q_def] SQ_sub
  by (cases "qf' \<in> nfa'.step_eps_closure_set (nfa'.run R bss) bs") fastforce+

lemma run_accept_eps_cong:
  assumes "R \<subseteq> nfa'.Q"
  shows "run_accept_eps R bss bs \<longleftrightarrow> (nfa'.run_accept_eps R bss bs \<and> run_accept_eps {qf'} [] bs) \<or>
    (\<exists>(css, css') \<in> list_split bss. nfa'.run_accept_eps R css (hd css') \<and>
    run_accept_eps {qf'} css' bs)"
  unfolding NFA.run_accept_eps_def run_cong[OF assms] accept_eps_split
    accept_eps_Un accept_eps_nfa'_run[OF assms]
  using accept_eps_empty by (auto split: if_splits)+

lemma run_accept_eps_cong_Cons_sub:
  assumes "R \<subseteq> nfa'.Q" "delta {qf'} bs \<subseteq> nfa'.delta R bs"
  shows "run_accept_eps R (bs # bss) cs \<longleftrightarrow>
    (nfa'.run_accept_eps R (bs # bss) cs \<and> run_accept_eps {qf'} [] cs) \<or>
    (\<exists>(css, css') \<in> list_split bss. nfa'.run_accept_eps (nfa'.delta R bs) css (hd css') \<and>
    run_accept_eps {qf'} css' cs)"
  unfolding NFA.run_accept_eps_def run_cong_Cons_sub[OF assms]
    accept_eps_split accept_eps_Un accept_eps_nfa'_run[OF assms(1)]
  using accept_eps_empty by (auto split: if_splits)+

lemmas run_accept_eps_cong_Cons_sub_simp =
  run_accept_eps_cong_Cons_sub[unfolded list_split_def, simplified,
    unfolded run_accept_eps_Cons[symmetric] take_Suc_Cons[symmetric]]

end

locale nfa_cong_Plus = nfa_cong q0 q0' qf qf' transs transs' +
  right: nfa_cong q0 q0'' qf qf'' transs transs''
  for q0 q0' q0'' qf qf' qf'' transs transs' transs'' +
  assumes step_eps_q0: "step_eps bs q0 q \<longleftrightarrow> q \<in> {q0', q0''}" and
  step_symb_q0: "\<not>step_symb q0 q"
begin

lemma step_symb_set_q0: "step_symb_set {q0} = {}"
  unfolding NFA.step_symb_set_def using step_symb_q0 by simp

lemma qf_not_q0: "qf \<notin> {q0}"
  using qf_not_in_SQ q0_sub_SQ by auto

lemma step_eps_closure_set_q0: "step_eps_closure_set {q0} bs = {q0} \<union>
  (nfa'.step_eps_closure_set {q0'} bs \<union> right.nfa'.step_eps_closure_set {q0''} bs)"
  using step_eps_closure_set_unfold[OF step_eps_q0]
    insert_is_Un[of q0' "{q0''}"]
    step_eps_closure_set_split[of _ _ "{q0'}" "{q0''}"]
    step_eps_closure_set_cong[OF nfa'.q0_sub_Q]
    right.step_eps_closure_set_cong[OF right.nfa'.q0_sub_Q]
  by auto

lemmas run_accept_eps_Nil_cong =
  run_accept_eps_Nil_eps_split[OF step_eps_closure_set_q0 step_symb_set_q0 qf_not_q0,
    unfolded run_accept_eps_split
    run_accept_eps_cong[OF nfa'.step_eps_closure_set_closed[OF nfa'.q0_sub_Q]]
    right.run_accept_eps_cong[OF right.nfa'.step_eps_closure_set_closed[OF right.nfa'.q0_sub_Q]]
    run_accept_eps_Nil_eps]

lemmas run_accept_eps_Cons_cong =
  run_accept_eps_Cons_eps_split[OF step_eps_closure_set_q0 step_symb_set_q0 qf_not_q0,
    unfolded run_accept_eps_split
    run_accept_eps_cong[OF nfa'.step_eps_closure_set_closed[OF nfa'.q0_sub_Q]]
    right.run_accept_eps_cong[OF right.nfa'.step_eps_closure_set_closed[OF right.nfa'.q0_sub_Q]]
    run_accept_eps_Cons_eps]

lemma run_accept_eps_cong: "run_accept_eps {q0} bss bs \<longleftrightarrow>
  (nfa'.run_accept_eps {q0'} bss bs \<or> right.nfa'.run_accept_eps {q0''} bss bs)"
  using run_accept_eps_Nil_cong run_accept_eps_Cons_cong by (cases bss) auto

end

locale nfa_cong_Times = nfa_cong' q0 q0 qf q0' transs transs' +
  right: nfa_cong q0 q0' qf qf transs transs''
  for q0 q0' qf transs transs' transs''
begin

lemmas run_accept_eps_cong =
  run_accept_eps_cong[OF nfa'.q0_sub_Q, unfolded
    right.run_accept_eps_cong[OF right.nfa'.q0_sub_Q], unfolded list_split_def, simplified]

end

locale nfa_cong_Star = nfa_cong' q0 q0' qf q0 transs transs'
  for q0 q0' qf transs transs' +
  assumes step_eps_q0: "step_eps bs q0 q \<longleftrightarrow> q \<in> {q0', qf}" and
  step_symb_q0: "\<not>step_symb q0 q"
begin

lemma step_symb_set_q0: "step_symb_set {q0} = {}"
  unfolding NFA.step_symb_set_def using step_symb_q0 by simp

lemma run_accept_eps_Nil: "run_accept_eps {q0} [] bs"
  unfolding NFA.run_accept_eps_def NFA.run_def using step_eps_accept_eps step_eps_q0 by fastforce

lemma rtranclp_step_eps_q0_q0': "(step_eps bs)\<^sup>*\<^sup>* q q' \<Longrightarrow> q = q0 \<Longrightarrow>
  q' \<in> {q0, qf} \<or> (q' \<in> nfa'.SQ \<and> (nfa'.step_eps bs)\<^sup>*\<^sup>* q0' q')"
  apply (induction q q' rule: rtranclp.induct)
  using step_eps_q0 step_eps_dest qf_not_in_SQ step_eps_cong_SQ nfa'.q0_sub_SQ
    nfa'.step_eps_closed[unfolded NFA.Q_def] by fastforce+

lemma step_eps_closure_set_q0: "step_eps_closure_set {q0} bs \<subseteq> {q0, qf} \<union>
  (nfa'.step_eps_closure_set {q0'} bs \<inter> nfa'.SQ)"
  unfolding NFA.step_eps_closure_set_def NFA.step_eps_closure_def
  using rtranclp_step_eps_q0_q0' by auto

lemma delta_sub_nfa'_delta: "delta {q0} bs \<subseteq> nfa'.delta {q0'} bs"
  unfolding NFA.delta_def
  using step_symb_set_mono[OF step_eps_closure_set_q0, unfolded step_symb_set_q0
    step_symb_set_qf step_symb_set_split insert_is_Un[of q0 "{qf}"]]
    step_symb_set_cong_SQ
  by (metis boolean_algebra_cancel.sup0 inf_le2 step_symb_set_proj step_symb_set_q0
      step_symb_set_qf sup_commute)

lemma step_eps_closure_set_q0_split: "step_eps_closure_set {q0} bs = {q0, qf} \<union>
  step_eps_closure_set {q0'} bs"
  unfolding NFA.step_eps_closure_set_def NFA.step_eps_closure_def
  using step_eps_qf step_eps_q0
  apply (auto)
   apply (metis rtranclp_unfold)
  by (metis r_into_rtranclp rtranclp.rtrancl_into_rtrancl rtranclp_idemp)

lemma delta_q0_q0': "delta {q0} bs = delta {q0'} bs"
  unfolding NFA.delta_def step_eps_closure_set_q0_split step_symb_set_split
  unfolding NFA.delta_def[symmetric]
  unfolding NFA.step_symb_set_def
  using step_symb_q0 step_symb_dest qf_not_in_SQ
  by fastforce

lemmas run_accept_eps_cong_Cons =
  run_accept_eps_cong_Cons_sub_simp[OF nfa'.q0_sub_Q delta_sub_nfa'_delta,
    unfolded run_accept_eps_Cons_delta_cong[OF delta_q0_q0', symmetric]]

end

end

(*  Title:      Jinja/Compiler/Correctness2.thy
    Author:     Tobias Nipkow
    Copyright   TUM 2003
*)

header {* \isaheader{Correctness of Stage 2} *}

theory Correctness2
imports List_Prefix Compiler2
begin

(*<*)hide_const (open) Throw(*>*)

subsection{* Instruction sequences *}

text{* How to select individual instructions and subsequences of
instructions from a program given the class, method and program
counter. *}

definition before :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> nat \<Rightarrow> instr list \<Rightarrow> bool"
   ("(_,_,_,_/ \<rhd> _)" [51,0,0,0,51] 50) where
 "P,C,M,pc \<rhd> is \<longleftrightarrow> is \<le> drop pc (instrs_of P C M)"

definition at :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> nat \<Rightarrow> instr \<Rightarrow> bool"
   ("(_,_,_,_/ \<triangleright> _)" [51,0,0,0,51] 50) where
 "P,C,M,pc \<triangleright> i \<longleftrightarrow> (\<exists>is. drop pc (instrs_of P C M) = i#is)"

lemma [simp]: "P,C,M,pc \<rhd> []"
(*<*)by(simp add:before_def)(*>*)


lemma [simp]: "P,C,M,pc \<rhd> (i#is) = (P,C,M,pc \<triangleright> i \<and> P,C,M,pc + 1 \<rhd> is)"
(*<*)by(fastsimp simp add:before_def at_def prefix_def drop_Suc drop_tl)(*>*)

(*<*)
declare drop_drop[simp del]
(*>*)


lemma [simp]: "P,C,M,pc \<rhd> (is\<^isub>1 @ is\<^isub>2) = (P,C,M,pc \<rhd> is\<^isub>1 \<and> P,C,M,pc + size is\<^isub>1 \<rhd> is\<^isub>2)"
(*<*)
apply(simp add:before_def prefix_def)
apply(subst add_commute)
apply(simp add: drop_drop[symmetric])
apply fastsimp
done
(*>*)

(*<*)
declare drop_drop[simp]
(*>*)


lemma [simp]: "P,C,M,pc \<triangleright> i \<Longrightarrow> instrs_of P C M ! pc = i"
(*<*)by(clarsimp simp add:at_def prefix_def nth_via_drop)(*>*)


lemma beforeM:
  "P \<turnstile> C sees M: Ts\<rightarrow>T = body in D \<Longrightarrow>
  compP\<^isub>2 P,D,M,0 \<rhd> compE\<^isub>2 body @ [Return]"
(*<*)
apply(drule sees_method_idemp)
apply(simp add:before_def compP\<^isub>2_def compMb\<^isub>2_def)
done
(*>*)

text{* This lemma executes a single instruction by rewriting: *}

lemma [simp]:
  "P,C,M,pc \<triangleright> instr \<Longrightarrow>
  (P \<turnstile> (None, h, (vs,ls,C,M,pc) # frs) -jvm\<rightarrow> \<sigma>') =
  ((None, h, (vs,ls,C,M,pc) # frs) = \<sigma>' \<or>
   (\<exists>\<sigma>. exec(P,(None, h, (vs,ls,C,M,pc) # frs)) = Some \<sigma> \<and> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'))"
(*<*)
apply(simp only: exec_all_def)
apply(blast intro: converse_rtranclE converse_rtrancl_into_rtrancl)
done
(*>*)


section{* Exception tables *}

constdefs
  pcs :: "ex_table \<Rightarrow> nat set"
  "pcs xt  \<equiv>  \<Union>(f,t,C,h,d) \<in> set xt. {f ..< t}"

lemma pcs_subset:
shows "\<And>pc d. pcs(compxE\<^isub>2 e pc d) \<subseteq> {pc..<pc+size(compE\<^isub>2 e)}"
and "\<And>pc d. pcs(compxEs\<^isub>2 es pc d) \<subseteq> {pc..<pc+size(compEs\<^isub>2 es)}"
(*<*)
apply(induct e and es)
apply (simp_all add:pcs_def)
apply (fastsimp split:bop.splits)+
done
(*>*)


lemma [simp]: "pcs [] = {}"
(*<*)by(simp add:pcs_def)(*>*)


lemma [simp]: "pcs (x#xt) = {fst x ..< fst(snd x)} \<union> pcs xt"
(*<*)by(auto simp add: pcs_def)(*>*)


lemma [simp]: "pcs(xt\<^isub>1 @ xt\<^isub>2) = pcs xt\<^isub>1 \<union> pcs xt\<^isub>2"
(*<*)by(simp add:pcs_def)(*>*)


lemma [simp]: "pc < pc\<^isub>0 \<or> pc\<^isub>0+size(compE\<^isub>2 e) \<le> pc \<Longrightarrow> pc \<notin> pcs(compxE\<^isub>2 e pc\<^isub>0 d)"
(*<*)using pcs_subset by fastsimp(*>*)


lemma [simp]: "pc < pc\<^isub>0 \<or> pc\<^isub>0+size(compEs\<^isub>2 es) \<le> pc \<Longrightarrow> pc \<notin> pcs(compxEs\<^isub>2 es pc\<^isub>0 d)"
(*<*)using pcs_subset by fastsimp(*>*)


lemma [simp]: "pc\<^isub>1 + size(compE\<^isub>2 e\<^isub>1) \<le> pc\<^isub>2 \<Longrightarrow> pcs(compxE\<^isub>2 e\<^isub>1 pc\<^isub>1 d\<^isub>1) \<inter> pcs(compxE\<^isub>2 e\<^isub>2 pc\<^isub>2 d\<^isub>2) = {}"
(*<*)using pcs_subset by fastsimp(*>*)


lemma [simp]: "pc\<^isub>1 + size(compE\<^isub>2 e) \<le> pc\<^isub>2 \<Longrightarrow> pcs(compxE\<^isub>2 e pc\<^isub>1 d\<^isub>1) \<inter> pcs(compxEs\<^isub>2 es pc\<^isub>2 d\<^isub>2) = {}"
(*<*)using pcs_subset by fastsimp(*>*)


lemma [simp]:
 "pc \<notin> pcs xt\<^isub>0 \<Longrightarrow> match_ex_table P C pc (xt\<^isub>0 @ xt\<^isub>1) = match_ex_table P C pc xt\<^isub>1"
(*<*)by (induct xt\<^isub>0) (auto simp: matches_ex_entry_def)(*>*)


lemma [simp]: "\<lbrakk> x \<in> set xt; pc \<notin> pcs xt \<rbrakk> \<Longrightarrow> \<not> matches_ex_entry P D pc x"
(*<*)by(auto simp:matches_ex_entry_def pcs_def)(*>*)


lemma [simp]:
assumes xe: "xe \<in> set(compxE\<^isub>2 e pc d)" and outside: "pc' < pc \<or> pc+size(compE\<^isub>2 e) \<le> pc'"
shows "\<not> matches_ex_entry P C pc' xe"
(*<*)
proof
  assume "matches_ex_entry P C pc' xe"
  with xe have "pc' \<in> pcs(compxE\<^isub>2 e pc d)"
    by(force simp add:matches_ex_entry_def pcs_def)
  with outside show False by simp
qed
(*>*)


lemma [simp]:
assumes xe: "xe \<in> set(compxEs\<^isub>2 es pc d)" and outside: "pc' < pc \<or> pc+size(compEs\<^isub>2 es) \<le> pc'"
shows "\<not> matches_ex_entry P C pc' xe"
(*<*)
proof
  assume "matches_ex_entry P C pc' xe"
  with xe have "pc' \<in> pcs(compxEs\<^isub>2 es pc d)"
    by(force simp add:matches_ex_entry_def pcs_def)
  with outside show False by simp
qed
(*>*)


lemma match_ex_table_app[simp]:
  "\<forall>xte \<in> set xt\<^isub>1. \<not> matches_ex_entry P D pc xte \<Longrightarrow>
  match_ex_table P D pc (xt\<^isub>1 @ xt) = match_ex_table P D pc xt"
(*<*)by(induct xt\<^isub>1) simp_all(*>*)


lemma [simp]:
  "\<forall>x \<in> set xtab. \<not> matches_ex_entry P C pc x \<Longrightarrow>
  match_ex_table P C pc xtab = None"
(*<*)using match_ex_table_app[where ?xt = "[]"] by fastsimp(*>*)


lemma match_ex_entry:
  "matches_ex_entry P C pc (start, end, catch_type, handler) =
  (start \<le> pc \<and> pc < end \<and>  P \<turnstile> C \<preceq>\<^sup>* catch_type)"
(*<*)by(simp add:matches_ex_entry_def)(*>*)


definition caught :: "jvm_prog \<Rightarrow> pc \<Rightarrow> heap \<Rightarrow> addr \<Rightarrow> ex_table \<Rightarrow> bool" where
  "caught P pc h a xt \<longleftrightarrow>
  (\<exists>entry \<in> set xt. matches_ex_entry P (cname_of h a) pc entry)"

definition beforex :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ex_table \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> bool"
              ("(2_,/_,/_ \<rhd>/ _ /'/ _,/_)" [51,0,0,0,0,51] 50) where
  "P,C,M \<rhd> xt / I,d \<longleftrightarrow>
  (\<exists>xt\<^isub>0 xt\<^isub>1. ex_table_of P C M = xt\<^isub>0 @ xt @ xt\<^isub>1 \<and> pcs xt\<^isub>0 \<inter> I = {} \<and> pcs xt \<subseteq> I \<and>
    (\<forall>pc \<in> I. \<forall>C pc' d'. match_ex_table P C pc xt\<^isub>1 = \<lfloor>(pc',d')\<rfloor> \<longrightarrow> d' \<le> d))"

definition dummyx :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ex_table \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> bool"  ("(2_,_,_ \<triangleright>/ _ '/_,_)" [51,0,0,0,0,51] 50) where
  "P,C,M \<triangleright> xt/I,d \<longleftrightarrow> P,C,M \<rhd> xt/I,d"

lemma beforexD1: "P,C,M \<rhd> xt / I,d \<Longrightarrow> pcs xt \<subseteq> I"
(*<*)by(auto simp add:beforex_def)(*>*)


lemma beforex_mono: "\<lbrakk> P,C,M \<rhd> xt/I,d'; d' \<le> d \<rbrakk> \<Longrightarrow> P,C,M \<rhd> xt/I,d"
(*<*)by(fastsimp simp:beforex_def)(*>*)


lemma [simp]: "P,C,M \<rhd> xt/I,d \<Longrightarrow> P,C,M \<rhd> xt/I,Suc d"
(*<*)by(fastsimp intro:beforex_mono)(*>*)


lemma beforex_append[simp]:
  "pcs xt\<^isub>1 \<inter> pcs xt\<^isub>2 = {} \<Longrightarrow>
  P,C,M \<rhd> xt\<^isub>1 @ xt\<^isub>2/I,d =
  (P,C,M \<rhd> xt\<^isub>1/I-pcs xt\<^isub>2,d  \<and>  P,C,M \<rhd> xt\<^isub>2/I-pcs xt\<^isub>1,d \<and> P,C,M \<triangleright> xt\<^isub>1@xt\<^isub>2/I,d)"
(*<*)
apply(rule iffI)
 prefer 2
 apply(simp add:dummyx_def)
apply(auto simp add: beforex_def dummyx_def)
 apply(rule_tac x = xt\<^isub>0 in exI)
 apply auto
apply(rule_tac x = "xt\<^isub>0@xt\<^isub>1" in exI)
apply auto
done
(*>*)


lemma beforex_appendD1:
  "\<lbrakk> P,C,M \<rhd> xt\<^isub>1 @ xt\<^isub>2 @ [(f,t,D,h,d)] / I,d;
    pcs xt\<^isub>1 \<subseteq> J; J \<subseteq> I; J \<inter> pcs xt\<^isub>2 = {} \<rbrakk>
  \<Longrightarrow> P,C,M \<rhd> xt\<^isub>1 / J,d"
(*<*)
apply(auto simp:beforex_def)
apply(rule exI,rule exI,rule conjI, rule refl)
apply(rule conjI, blast)
apply(auto)
apply(subgoal_tac "pc \<notin> pcs xt\<^isub>2")
 prefer 2 apply blast
apply (auto split:split_if_asm)
done
(*>*)


lemma beforex_appendD2:
  "\<lbrakk> P,C,M \<rhd> xt\<^isub>1 @ xt\<^isub>2 @ [(f,t,D,h,d)] / I,d;
    pcs xt\<^isub>2 \<subseteq> J; J \<subseteq> I; J \<inter> pcs xt\<^isub>1 = {} \<rbrakk>
  \<Longrightarrow> P,C,M \<rhd> xt\<^isub>2 / J,d"
(*<*)
apply(auto simp:beforex_def)
apply(rule_tac x = "xt\<^isub>0 @ xt\<^isub>1" in exI)
apply fastsimp
done
(*>*)


lemma beforexM:
  "P \<turnstile> C sees M: Ts\<rightarrow>T = body in D \<Longrightarrow>
  compP\<^isub>2 P,D,M \<rhd> compxE\<^isub>2 body 0 0/{..<size(compE\<^isub>2 body)},0"
(*<*)
apply(drule sees_method_idemp)
apply(drule sees_method_compP[where f = compMb\<^isub>2])
apply(simp add:beforex_def compP\<^isub>2_def compMb\<^isub>2_def)
apply(rule_tac x = "[]" in exI)
using pcs_subset apply fastsimp
done
(*>*)


lemma match_ex_table_SomeD2:
 "\<lbrakk> match_ex_table P D pc (ex_table_of P C M) = \<lfloor>(pc',d')\<rfloor>;
    P,C,M \<rhd> xt/I,d; \<forall>x \<in> set xt. \<not> matches_ex_entry P D pc x; pc \<in> I \<rbrakk>
 \<Longrightarrow> d' \<le> d"
(*<*)
apply(auto simp:beforex_def)
apply(subgoal_tac "pc \<notin> pcs xt\<^isub>0")
apply auto
done
(*>*)


lemma match_ex_table_SomeD1:
  "\<lbrakk> match_ex_table P D pc (ex_table_of P C M) = \<lfloor>(pc',d')\<rfloor>;
     P,C,M \<rhd> xt / I,d; pc \<in> I; pc \<notin> pcs xt \<rbrakk> \<Longrightarrow> d' \<le> d"
(*<*)by(auto elim: match_ex_table_SomeD2)(*>*)


subsection{* The correctness proof *}

(*<*)
declare nat_add_distrib[simp] caught_def[simp]
declare fun_upd_apply[simp del]
(*>*)


definition
  handle :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr \<Rightarrow> heap \<Rightarrow> val list \<Rightarrow> val list \<Rightarrow> nat \<Rightarrow> frame list
                \<Rightarrow> jvm_state" where
  "handle P C M a h vs ls pc frs = find_handler P a h ((vs,ls,C,M,pc) # frs)"

lemma handle_Cons:
 "\<lbrakk> P,C,M \<rhd> xt/I,d; d \<le> size vs; pc \<in> I;
    \<forall>x \<in> set xt. \<not> matches_ex_entry P (cname_of h xa) pc x \<rbrakk> \<Longrightarrow>
  handle P C M xa h (v # vs) ls pc frs = handle P C M xa h vs ls pc frs"
(*<*)by(auto simp:handle_def Suc_diff_le dest: match_ex_table_SomeD2)(*>*)

lemma handle_append:
 "\<lbrakk> P,C,M \<rhd> xt/I,d; d \<le> size vs; pc \<in> I; pc \<notin> pcs xt \<rbrakk> \<Longrightarrow>
  handle P C M xa h (ws @ vs) ls pc frs = handle P C M xa h vs ls pc frs"
(*<*)
apply(auto simp:handle_def)
apply(rename_tac pc' d')
apply(subgoal_tac "size ws \<le> length ws + length vs - d'")
apply(simp add:drop_all)
apply(fastsimp dest:match_ex_table_SomeD2 split:nat_diff_split)
done
(*>*)


lemma aux_isin[simp]: "\<lbrakk> B \<subseteq> A; a \<in> B \<rbrakk> \<Longrightarrow> a \<in> A"
(*<*)by blast(*>*)


lemma fixes P\<^isub>1 defines [simp]: "P \<equiv> compP\<^isub>2 P\<^isub>1"
shows Jcc:
  "P\<^isub>1 \<turnstile>\<^sub>1 \<langle>e,(h\<^isub>0,ls\<^isub>0)\<rangle> \<Rightarrow> \<langle>ef,(h\<^isub>1,ls\<^isub>1)\<rangle> \<Longrightarrow>
  (\<And>C M pc v xa vs frs I.
     \<lbrakk> P,C,M,pc \<rhd> compE\<^isub>2 e; P,C,M \<rhd> compxE\<^isub>2 e pc (size vs)/I,size vs;
       {pc..<pc+size(compE\<^isub>2 e)} \<subseteq> I \<rbrakk> \<Longrightarrow>
     (ef = Val v \<longrightarrow>
      P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow>
            (None,h\<^isub>1,(v#vs,ls\<^isub>1,C,M,pc+size(compE\<^isub>2 e))#frs))
     \<and>
     (ef = Throw xa \<longrightarrow>
      (\<exists>pc\<^isub>1. pc \<le> pc\<^isub>1 \<and> pc\<^isub>1 < pc + size(compE\<^isub>2 e) \<and>
               \<not> caught P pc\<^isub>1 h\<^isub>1 xa (compxE\<^isub>2 e pc (size vs)) \<and>
               P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow> handle P C M xa h\<^isub>1 vs ls\<^isub>1 pc\<^isub>1 frs)))"
(*<*)
  (is "_ \<Longrightarrow> (\<And>C M pc v xa vs frs I.
                  PROP ?P e h\<^isub>0 ls\<^isub>0 ef h\<^isub>1 ls\<^isub>1 C M pc v xa vs frs I)")
(*>*)

and "P\<^isub>1 \<turnstile>\<^sub>1 \<langle>es,(h\<^isub>0,ls\<^isub>0)\<rangle> [\<Rightarrow>] \<langle>fs,(h\<^isub>1,ls\<^isub>1)\<rangle> \<Longrightarrow>
    (\<And>C M pc ws xa es' vs frs I.
      \<lbrakk> P,C,M,pc \<rhd> compEs\<^isub>2 es; P,C,M \<rhd> compxEs\<^isub>2 es pc (size vs)/I,size vs;
       {pc..<pc+size(compEs\<^isub>2 es)} \<subseteq> I \<rbrakk> \<Longrightarrow>
      (fs = map Val ws \<longrightarrow>
       P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^isub>1,(rev ws @ vs,ls\<^isub>1,C,M,pc+size(compEs\<^isub>2 es))#frs))
      \<and>
      (fs = map Val ws @ Throw xa # es' \<longrightarrow>
       (\<exists>pc\<^isub>1. pc \<le> pc\<^isub>1 \<and> pc\<^isub>1 < pc + size(compEs\<^isub>2 es) \<and>
                \<not> caught P pc\<^isub>1 h\<^isub>1 xa (compxEs\<^isub>2 es pc (size vs)) \<and>
                P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow> handle P C M xa h\<^isub>1 vs ls\<^isub>1 pc\<^isub>1 frs)))"
(*<*)
  (is "_ \<Longrightarrow> (\<And>C M pc ws xa es' vs frs I.
                  PROP ?Ps es h\<^isub>0 ls\<^isub>0 fs h\<^isub>1 ls\<^isub>1 C M pc ws xa es' vs frs I)")
proof (induct rule:eval\<^isub>1_evals\<^isub>1_inducts)
  case New\<^isub>1 thus ?case by (clarsimp simp add:blank_def expand_fun_eq)
next
  case NewFail\<^isub>1 thus ?case by(auto simp: handle_def pcs_def)
next
  case (Cast\<^isub>1 e h\<^isub>0 ls\<^isub>0 a h\<^isub>1 ls\<^isub>1 D fs C')
  let ?pc = "pc + length(compE\<^isub>2 e)"
  have "P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^isub>1,(Addr a#vs,ls\<^isub>1,C,M,?pc)#frs)" using Cast\<^isub>1 by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^isub>1,(Addr a#vs,ls\<^isub>1,C,M,?pc+1)#frs)"
    using Cast\<^isub>1 by (auto simp add:cast_ok_def)
  finally show ?case by auto
next
  case (CastNull\<^isub>1 e h\<^isub>0 ls\<^isub>0 h\<^isub>1 ls\<^isub>1 C')
  let ?pc = "pc + length(compE\<^isub>2 e)"
  have "P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow>
            (None,h\<^isub>1,(Null#vs,ls\<^isub>1,C,M,?pc)#frs)"
    using CastNull\<^isub>1 by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^isub>1,(Null#vs,ls\<^isub>1,C,M,?pc+1)#frs)"
    using CastNull\<^isub>1 by (auto simp add:cast_ok_def)
  finally show ?case by auto
next
  case (CastFail\<^isub>1 e h\<^isub>0 ls\<^isub>0 a h\<^isub>1 ls\<^isub>1 D fs C')
  let ?pc = "pc + length(compE\<^isub>2 e)"
  let ?xa = "addr_of_sys_xcpt ClassCast"
  have "P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^isub>1,(Addr a#vs,ls\<^isub>1,C,M,?pc)#frs)"
    using CastFail\<^isub>1 by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^isub>1 (Addr a#vs) ls\<^isub>1 ?pc frs"
    using CastFail\<^isub>1 by (auto simp add:handle_def cast_ok_def)
  also have "handle P C M ?xa h\<^isub>1 (Addr a#vs) ls\<^isub>1 ?pc frs =
             handle P C M ?xa h\<^isub>1 vs ls\<^isub>1 ?pc frs"
    using CastFail\<^isub>1.prems by(auto simp:handle_Cons)
  finally have exec: "P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow> \<dots>".
  show ?case (is "?N \<and> (?eq \<longrightarrow> (\<exists>pc\<^isub>1. ?H pc\<^isub>1))")
  proof
    show ?N by simp
  next
    have "?eq \<longrightarrow> ?H ?pc" using exec by auto
    thus "?eq \<longrightarrow> (\<exists>pc\<^isub>1. ?H pc\<^isub>1)" by blast
  qed
next
  case CastThrow\<^isub>1 thus ?case by fastsimp
next
  case Val\<^isub>1 thus ?case by simp
next
  case Var\<^isub>1 thus ?case by auto
next
  case (BinOp\<^isub>1 e\<^isub>1 h\<^isub>0 ls\<^isub>0 v\<^isub>1 h\<^isub>1 ls\<^isub>1 e\<^isub>2 v\<^isub>2 h\<^isub>2 ls\<^isub>2 bop w)
  let ?pc\<^isub>1 = "pc + length(compE\<^isub>2 e\<^isub>1)"
  let ?pc\<^isub>2 = "?pc\<^isub>1 + length(compE\<^isub>2 e\<^isub>2)"
  have IH\<^isub>2: "PROP ?P e\<^isub>2 h\<^isub>1 ls\<^isub>1 (Val v\<^isub>2) h\<^isub>2 ls\<^isub>2 C M ?pc\<^isub>1 v\<^isub>2 xa (v\<^isub>1#vs) frs
                     (I - pcs(compxE\<^isub>2 e\<^isub>1 pc (size vs)))" by fact
  have "P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^isub>1,(v\<^isub>1#vs,ls\<^isub>1,C,M,?pc\<^isub>1)#frs)" using BinOp\<^isub>1 by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^isub>2,(v\<^isub>2#v\<^isub>1#vs,ls\<^isub>2,C,M,?pc\<^isub>2)#frs)"
    using BinOp\<^isub>1.prems IH\<^isub>2 by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^isub>2,(w#vs,ls\<^isub>2,C,M,?pc\<^isub>2+1)#frs)"
    using BinOp\<^isub>1 by(cases bop) auto
  finally show ?case by (auto split: bop.splits simp:add_assoc)
next
  case BinOpThrow\<^isub>1\<^isub>1 thus ?case by(fastsimp)
next
  case (BinOpThrow\<^isub>2\<^isub>1 e\<^isub>1 h\<^isub>0 ls\<^isub>0 v\<^isub>1 h\<^isub>1 ls\<^isub>1 e\<^isub>2 e h\<^isub>2 ls\<^isub>2 bop)
  let ?pc = "pc + length(compE\<^isub>2 e\<^isub>1)"
  let ?\<sigma>\<^isub>1 = "(None,h\<^isub>1,(v\<^isub>1#vs,ls\<^isub>1,C,M,?pc)#frs)"
  have 1: "P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow> ?\<sigma>\<^isub>1"
    using BinOpThrow\<^isub>2\<^isub>1 by fastsimp
  show ?case (is "?N \<and> (?eq \<longrightarrow> (\<exists>pc\<^isub>2. ?H pc\<^isub>2))")
  proof
    show ?N by simp
  next
    { assume ?eq
      moreover
      have "PROP ?P e\<^isub>2 h\<^isub>1 ls\<^isub>1 (throw e) h\<^isub>2 ls\<^isub>2 C M ?pc v xa (v\<^isub>1#vs) frs
                     (I - pcs(compxE\<^isub>2 e\<^isub>1 pc (size vs)))" by fact
      ultimately obtain pc\<^isub>2 where
	pc\<^isub>2: "?pc \<le> pc\<^isub>2 \<and> pc\<^isub>2 < ?pc + size(compE\<^isub>2 e\<^isub>2) \<and>
              \<not> caught P pc\<^isub>2 h\<^isub>2 xa (compxE\<^isub>2 e\<^isub>2 ?pc (size vs + 1))" and
	2: "P \<turnstile> ?\<sigma>\<^isub>1 -jvm\<rightarrow> handle P C M xa h\<^isub>2 (v\<^isub>1#vs) ls\<^isub>2 pc\<^isub>2 frs"
	using BinOpThrow\<^isub>2\<^isub>1.prems by fastsimp
      have 3: "P \<turnstile> ?\<sigma>\<^isub>1 -jvm\<rightarrow> handle P C M xa h\<^isub>2 vs ls\<^isub>2 pc\<^isub>2 frs"
	using 2 BinOpThrow\<^isub>2\<^isub>1.prems pc\<^isub>2 by(auto simp:handle_Cons)
      have "?H pc\<^isub>2" using pc\<^isub>2 jvm_trans[OF 1 3] by auto
      hence "\<exists>pc\<^isub>2. ?H pc\<^isub>2" by iprover
    }
    thus "?eq \<longrightarrow> (\<exists>pc\<^isub>2. ?H pc\<^isub>2)" by iprover
  qed
next
  case (FAcc\<^isub>1 e h\<^isub>0 ls\<^isub>0 a h\<^isub>1 ls\<^isub>1 C fs F D w)
  let ?pc = "pc + length(compE\<^isub>2 e)"
  have "P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^isub>1,(Addr a#vs,ls\<^isub>1,C,M,?pc)#frs)" using FAcc\<^isub>1 by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^isub>1,(w#vs,ls\<^isub>1,C,M,?pc+1)#frs)"
    using FAcc\<^isub>1 by auto
  finally show ?case by auto
next
  case (FAccNull\<^isub>1 e h\<^isub>0 ls\<^isub>0 h\<^isub>1 ls\<^isub>1 F D)
  let ?pc = "pc + length(compE\<^isub>2 e)"
  let ?xa = "addr_of_sys_xcpt NullPointer"
  have "P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^isub>1,(Null#vs,ls\<^isub>1,C,M,?pc)#frs)" using FAccNull\<^isub>1 by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^isub>1 (Null#vs) ls\<^isub>1 ?pc frs"
    using FAccNull\<^isub>1.prems
    by(fastsimp simp:split_beta handle_def simp del: split_paired_Ex)
  also have "handle P C M ?xa h\<^isub>1 (Null#vs) ls\<^isub>1 ?pc frs =
             handle P C M ?xa h\<^isub>1 vs ls\<^isub>1 ?pc frs"
    using FAccNull\<^isub>1.prems by(auto simp add:handle_Cons)
  finally show ?case by (auto intro: exI[where x = ?pc])
next
  case FAccThrow\<^isub>1 thus ?case by fastsimp
next
  case (LAss\<^isub>1 e h\<^isub>0 ls\<^isub>0 w h\<^isub>1 ls\<^isub>1 i ls\<^isub>2)
  let ?pc = "pc + length(compE\<^isub>2 e)"
  have "P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^isub>1,(w#vs,ls\<^isub>1,C,M,?pc)#frs)" using LAss\<^isub>1 by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^isub>1,(Unit#vs,ls\<^isub>2,C,M,?pc+2)#frs)"
    using LAss\<^isub>1 by auto
  finally show ?case using LAss\<^isub>1 by auto
next
  case LAssThrow\<^isub>1 thus ?case by fastsimp
next
  case (FAss\<^isub>1 e\<^isub>1 h\<^isub>0 ls\<^isub>0 a h\<^isub>1 ls\<^isub>1 e\<^isub>2 w h\<^isub>2 ls\<^isub>2 C fs fs' F D h\<^isub>2')
  let ?pc\<^isub>1 = "pc + length(compE\<^isub>2 e\<^isub>1)"
  let ?pc\<^isub>2 = "?pc\<^isub>1 + length(compE\<^isub>2 e\<^isub>2)"
  have IH\<^isub>2: "PROP ?P e\<^isub>2 h\<^isub>1 ls\<^isub>1 (Val w) h\<^isub>2 ls\<^isub>2 C M ?pc\<^isub>1 w xa (Addr a#vs) frs
                     (I - pcs(compxE\<^isub>2 e\<^isub>1 pc (size vs)))" by fact
  have "P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^isub>1,(Addr a#vs,ls\<^isub>1,C,M,?pc\<^isub>1)#frs)" using FAss\<^isub>1 by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^isub>2,(w#Addr a#vs,ls\<^isub>2,C,M,?pc\<^isub>2)#frs)"
    using FAss\<^isub>1.prems IH\<^isub>2 by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^isub>2',(Unit#vs,ls\<^isub>2,C,M,?pc\<^isub>2+2)#frs)"
    using FAss\<^isub>1 by auto
  finally show ?case using FAss\<^isub>1 by (auto simp:add_assoc)
next
  case (FAssNull\<^isub>1 e\<^isub>1 h\<^isub>0 ls\<^isub>0 h\<^isub>1 ls\<^isub>1 e\<^isub>2 w h\<^isub>2 ls\<^isub>2 F D)
  let ?pc\<^isub>1 = "pc + length(compE\<^isub>2 e\<^isub>1)"
  let ?pc\<^isub>2 = "?pc\<^isub>1 + length(compE\<^isub>2 e\<^isub>2)"
  let ?xa = "addr_of_sys_xcpt NullPointer"
  have IH\<^isub>2: "PROP ?P e\<^isub>2 h\<^isub>1 ls\<^isub>1 (Val w) h\<^isub>2 ls\<^isub>2 C M ?pc\<^isub>1 w xa (Null#vs) frs
                     (I - pcs(compxE\<^isub>2 e\<^isub>1 pc (size vs)))" by fact
  have "P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^isub>1,(Null#vs,ls\<^isub>1,C,M,?pc\<^isub>1)#frs)" using FAssNull\<^isub>1 by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^isub>2,(w#Null#vs,ls\<^isub>2,C,M,?pc\<^isub>2)#frs)"
    using FAssNull\<^isub>1.prems IH\<^isub>2 by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^isub>2 (w#Null#vs) ls\<^isub>2 ?pc\<^isub>2 frs"
    using FAssNull\<^isub>1.prems
    by(fastsimp simp:split_beta handle_def simp del: split_paired_Ex)
  also have "handle P C M ?xa h\<^isub>2 (w#Null#vs) ls\<^isub>2 ?pc\<^isub>2 frs =
             handle P C M ?xa h\<^isub>2 vs ls\<^isub>2 ?pc\<^isub>2 frs"
    using FAssNull\<^isub>1.prems by(auto simp add:handle_Cons)
  finally show ?case by (auto intro: exI[where x = ?pc\<^isub>2])
next
  case (FAssThrow\<^isub>2\<^isub>1 e\<^isub>1 h\<^isub>0 ls\<^isub>0 w h\<^isub>1 ls\<^isub>1 e\<^isub>2 e' h\<^isub>2 ls\<^isub>2 F D)
  let ?pc\<^isub>1 = "pc + length(compE\<^isub>2 e\<^isub>1)"
  let ?\<sigma>\<^isub>1 = "(None,h\<^isub>1,(w#vs,ls\<^isub>1,C,M,?pc\<^isub>1)#frs)"
  have 1: "P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow> ?\<sigma>\<^isub>1"
    using FAssThrow\<^isub>2\<^isub>1 by fastsimp
  show ?case (is "?N \<and> (?eq \<longrightarrow> (\<exists>pc\<^isub>2. ?H pc\<^isub>2))")
  proof
    show ?N by simp
  next
    { assume ?eq
      moreover
      have "PROP ?P e\<^isub>2 h\<^isub>1 ls\<^isub>1 (throw e') h\<^isub>2 ls\<^isub>2 C M ?pc\<^isub>1 v xa (w#vs) frs
                    (I - pcs (compxE\<^isub>2 e\<^isub>1 pc (length vs)))" by fact
      ultimately obtain pc\<^isub>2 where
	pc\<^isub>2: "?pc\<^isub>1 \<le> pc\<^isub>2 \<and> pc\<^isub>2 < ?pc\<^isub>1 + size(compE\<^isub>2 e\<^isub>2) \<and>
              \<not> caught P pc\<^isub>2 h\<^isub>2 xa (compxE\<^isub>2 e\<^isub>2 ?pc\<^isub>1 (size vs + 1))" and
	2: "P \<turnstile> ?\<sigma>\<^isub>1 -jvm\<rightarrow> handle P C M xa h\<^isub>2 (w#vs) ls\<^isub>2 pc\<^isub>2 frs"
	using FAssThrow\<^isub>2\<^isub>1.prems by fastsimp
      have 3: "P \<turnstile> ?\<sigma>\<^isub>1 -jvm\<rightarrow> handle P C M xa h\<^isub>2 vs ls\<^isub>2 pc\<^isub>2 frs"
	using 2 FAssThrow\<^isub>2\<^isub>1.prems pc\<^isub>2 by(auto simp:handle_Cons)
      have "?H pc\<^isub>2" using pc\<^isub>2 jvm_trans[OF 1 3]	by auto
      hence "\<exists>pc\<^isub>2. ?H pc\<^isub>2" by iprover
    }
    thus "?eq \<longrightarrow> (\<exists>pc\<^isub>2. ?H pc\<^isub>2)" by iprover
  qed
next
  case FAssThrow\<^isub>1\<^isub>1 thus ?case by fastsimp
next
  case (Call\<^isub>1 e h\<^isub>0 ls\<^isub>0 a h\<^isub>1 ls\<^isub>1 es pvs h\<^isub>2 ls\<^isub>2 Ca fs M' Ts T body D ls\<^isub>2' f h\<^isub>3 ls\<^isub>3)
  have "P\<^isub>1 \<turnstile>\<^sub>1 \<langle>es,(h\<^isub>1, ls\<^isub>1)\<rangle> [\<Rightarrow>] \<langle>map Val pvs,(h\<^isub>2, ls\<^isub>2)\<rangle>" by fact
  hence [simp]: "length es = length pvs" by(auto dest:evals\<^isub>1_preserves_elen)
  let ?\<sigma>\<^isub>0 = "(None,h\<^isub>0,(vs, ls\<^isub>0, C,M,pc)#frs)"
  let ?pc\<^isub>1 = "pc + length(compE\<^isub>2 e)"
  let ?\<sigma>\<^isub>1 = "(None,h\<^isub>1,(Addr a # vs, ls\<^isub>1, C,M,?pc\<^isub>1)#frs)"
  let ?pc\<^isub>2 = "?pc\<^isub>1 + length(compEs\<^isub>2 es)"
  let ?frs\<^isub>2 = "(rev pvs @ Addr a # vs, ls\<^isub>2, C,M,?pc\<^isub>2)#frs"
  let ?\<sigma>\<^isub>2 = "(None,h\<^isub>2,?frs\<^isub>2)"
  let ?frs\<^isub>2' = "([], ls\<^isub>2', D,M',0) # ?frs\<^isub>2"
  let ?\<sigma>\<^isub>2' = "(None, h\<^isub>2, ?frs\<^isub>2')"
  have IH_es: "PROP ?Ps es h\<^isub>1 ls\<^isub>1 (map Val pvs) h\<^isub>2 ls\<^isub>2 C M ?pc\<^isub>1 pvs xa
                    (map Val pvs) (Addr a # vs) frs (I - pcs(compxE\<^isub>2 e pc (size vs)))" by fact
  have "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> ?\<sigma>\<^isub>1" using Call\<^isub>1 by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^isub>2" using IH_es Call\<^isub>1.prems by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^isub>2'"
    using Call\<^isub>1 by(auto simp add: nth_append compMb\<^isub>2_def)
  finally have 1: "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> ?\<sigma>\<^isub>2'".
  have "P\<^isub>1 \<turnstile> Ca sees M': Ts\<rightarrow>T = body in D" by fact
  then have M'_in_D: "P\<^isub>1 \<turnstile> D sees M': Ts\<rightarrow>T = body in D"
    by(rule sees_method_idemp) 
  hence M'_code: "compP\<^isub>2 P\<^isub>1,D,M',0 \<rhd> compE\<^isub>2 body @ [Return]"
    and M'_xtab: "compP\<^isub>2 P\<^isub>1,D,M' \<rhd> compxE\<^isub>2 body 0 0/{..<size(compE\<^isub>2 body)},0"
    by(rule beforeM, rule beforexM)
  have IH_body: "PROP ?P body h\<^isub>2 ls\<^isub>2' f h\<^isub>3 ls\<^isub>3 D M' 0 v xa [] ?frs\<^isub>2 ({..<size(compE\<^isub>2 body)})" by fact
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note 1
      also have "P \<turnstile> ?\<sigma>\<^isub>2' -jvm\<rightarrow>
                     (None,h\<^isub>3,([v],ls\<^isub>3,D,M',size(compE\<^isub>2 body))#?frs\<^isub>2)"
	using val IH_body Call\<^isub>1.prems M'_code M'_xtab
	by (fastsimp simp del:split_paired_Ex)
      also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None, h\<^isub>3, (v # vs, ls\<^isub>2, C,M,?pc\<^isub>2+1)#frs)"
	using Call\<^isub>1 M'_code M'_in_D by(auto simp: nth_append compMb\<^isub>2_def)
      finally show ?trans by(simp add:add_assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^isub>2. ?H pc\<^isub>2)")
    proof
      assume throw: ?throw
      with IH_body obtain pc\<^isub>2 where
	pc\<^isub>2: "0 \<le> pc\<^isub>2 \<and> pc\<^isub>2 < size(compE\<^isub>2 body) \<and>
              \<not> caught P pc\<^isub>2 h\<^isub>3 xa (compxE\<^isub>2 body 0 0)" and
	2: "P \<turnstile> ?\<sigma>\<^isub>2' -jvm\<rightarrow> handle P D M' xa h\<^isub>3 [] ls\<^isub>3 pc\<^isub>2 ?frs\<^isub>2"
	using Call\<^isub>1.prems M'_code M'_xtab
	by (fastsimp simp del:split_paired_Ex)
      have "handle P D M' xa h\<^isub>3 [] ls\<^isub>3 pc\<^isub>2 ?frs\<^isub>2 =
            handle P C M xa h\<^isub>3 (rev pvs @ Addr a # vs) ls\<^isub>2 ?pc\<^isub>2 frs"
	using pc\<^isub>2 M'_in_D by(auto simp add:handle_def)
      also have "\<dots> = handle P C M xa h\<^isub>3 vs ls\<^isub>2 ?pc\<^isub>2 frs"
	using Call\<^isub>1.prems by(auto simp add:handle_append handle_Cons)
      finally have "?H ?pc\<^isub>2" using pc\<^isub>2 jvm_trans[OF 1 2] by auto
      thus "\<exists>pc\<^isub>2. ?H pc\<^isub>2" by iprover
    qed
  qed
next
  case (CallParamsThrow\<^isub>1 e h\<^isub>0 ls\<^isub>0 w h\<^isub>1 ls\<^isub>1 es es' h\<^isub>2 ls\<^isub>2 pvs ex es'' M')
  let ?\<sigma>\<^isub>0 = "(None,h\<^isub>0,(vs, ls\<^isub>0, C,M,pc)#frs)"
  let ?pc\<^isub>1 = "pc + length(compE\<^isub>2 e)"
  let ?\<sigma>\<^isub>1 = "(None,h\<^isub>1,(w # vs, ls\<^isub>1, C,M,?pc\<^isub>1)#frs)"
  let ?pc\<^isub>2 = "?pc\<^isub>1 + length(compEs\<^isub>2 es)"
  have 1: "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> ?\<sigma>\<^isub>1" using CallParamsThrow\<^isub>1 by fastsimp
  show ?case (is "?N \<and> (?eq \<longrightarrow> (\<exists>pc\<^isub>2. ?H pc\<^isub>2))")
  proof
    show ?N by simp
  next
    { assume ?eq
      moreover
      have "PROP ?Ps es h\<^isub>1 ls\<^isub>1 es' h\<^isub>2 ls\<^isub>2 C M ?pc\<^isub>1 pvs xa es'' (w#vs) frs
        (I - pcs (compxE\<^isub>2 e pc (length vs)))" by fact
      ultimately have "\<exists>pc\<^isub>2.
	(?pc\<^isub>1 \<le> pc\<^isub>2 \<and> pc\<^isub>2 < ?pc\<^isub>1 + size(compEs\<^isub>2 es) \<and>
         \<not> caught P pc\<^isub>2 h\<^isub>2 xa (compxEs\<^isub>2 es ?pc\<^isub>1 (size vs + 1))) \<and>
	P \<turnstile> ?\<sigma>\<^isub>1 -jvm\<rightarrow> handle P C M xa h\<^isub>2 (w#vs) ls\<^isub>2 pc\<^isub>2 frs"
	(is "\<exists>pc\<^isub>2. ?PC pc\<^isub>2 \<and> ?Exec pc\<^isub>2")
	using CallParamsThrow\<^isub>1 by force
      then obtain pc\<^isub>2 where pc\<^isub>2: "?PC pc\<^isub>2" and 2: "?Exec pc\<^isub>2" by iprover
      have "?H pc\<^isub>2" using pc\<^isub>2 jvm_trans[OF 1 2] CallParamsThrow\<^isub>1
	by(auto simp:handle_Cons)
      hence "\<exists>pc\<^isub>2. ?H pc\<^isub>2" by iprover
    }
    thus "?eq \<longrightarrow> (\<exists>pc\<^isub>2. ?H pc\<^isub>2)" by iprover
  qed
next
  case (CallNull\<^isub>1 e h\<^isub>0 ls\<^isub>0 h\<^isub>1 ls\<^isub>1 es pvs h\<^isub>2 ls\<^isub>2 M')
  have "P\<^isub>1 \<turnstile>\<^sub>1 \<langle>es,(h\<^isub>1, ls\<^isub>1)\<rangle> [\<Rightarrow>] \<langle>map Val pvs,(h\<^isub>2, ls\<^isub>2)\<rangle>" by fact
  hence [simp]: "length es = length pvs" by(auto dest:evals\<^isub>1_preserves_elen)
  let ?pc\<^isub>1 = "pc + length(compE\<^isub>2 e)"
  let ?pc\<^isub>2 = "?pc\<^isub>1 + length(compEs\<^isub>2 es)"
  let ?xa = "addr_of_sys_xcpt NullPointer"
  have IH_es: "PROP ?Ps es h\<^isub>1 ls\<^isub>1 (map Val pvs) h\<^isub>2 ls\<^isub>2 C M ?pc\<^isub>1 pvs xa
                    (map Val pvs) (Null#vs) frs (I - pcs(compxE\<^isub>2 e pc (size vs)))" by fact
  have "P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^isub>1,(Null#vs,ls\<^isub>1,C,M,?pc\<^isub>1)#frs)" using CallNull\<^isub>1 by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^isub>2,(rev pvs@Null#vs,ls\<^isub>2,C,M,?pc\<^isub>2)#frs)"
    using CallNull\<^isub>1 IH_es by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^isub>2 (rev pvs@Null#vs) ls\<^isub>2 ?pc\<^isub>2 frs"
    using CallNull\<^isub>1.prems
    by(auto simp:split_beta handle_def nth_append simp del: split_paired_Ex)
  also have "handle P C M ?xa h\<^isub>2 (rev pvs@Null#vs) ls\<^isub>2 ?pc\<^isub>2 frs =
             handle P C M ?xa h\<^isub>2 vs ls\<^isub>2 ?pc\<^isub>2 frs"
    using CallNull\<^isub>1.prems by(auto simp:handle_Cons handle_append)
  finally show ?case by (auto intro: exI[where x = ?pc\<^isub>2])
next
  case CallObjThrow\<^isub>1 thus ?case by fastsimp
next
  case Block\<^isub>1 thus ?case by auto
next
  case (Seq\<^isub>1 e\<^isub>1 h\<^isub>0 ls\<^isub>0 w h\<^isub>1 ls\<^isub>1 e\<^isub>2 e\<^isub>2' h\<^isub>2 ls\<^isub>2)
  let ?pc\<^isub>1 = "pc + length(compE\<^isub>2 e\<^isub>1)"
  let ?\<sigma>\<^isub>0 = "(None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs)"
  let ?\<sigma>\<^isub>1 = "(None,h\<^isub>1,(vs,ls\<^isub>1,C,M,?pc\<^isub>1+1)#frs)"
  have "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> (None,h\<^isub>1,(w#vs,ls\<^isub>1,C,M,?pc\<^isub>1)#frs)"
    using Seq\<^isub>1 by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^isub>1" using Seq\<^isub>1 by auto
  finally have eval\<^isub>1: "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> ?\<sigma>\<^isub>1".
  let ?pc\<^isub>2 = "?pc\<^isub>1 + 1 + length(compE\<^isub>2 e\<^isub>2)"
  have IH\<^isub>2: "PROP ?P e\<^isub>2 h\<^isub>1 ls\<^isub>1 e\<^isub>2' h\<^isub>2 ls\<^isub>2 C M (?pc\<^isub>1+1) v xa vs frs
                     (I - pcs(compxE\<^isub>2 e\<^isub>1 pc (size vs)))" by fact
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note eval\<^isub>1
      also have "P \<turnstile> ?\<sigma>\<^isub>1 -jvm\<rightarrow> (None,h\<^isub>2,(v#vs,ls\<^isub>2,C,M,?pc\<^isub>2)#frs)"
	using val Seq\<^isub>1.prems IH\<^isub>2 by fastsimp
      finally show ?trans by(simp add:add_assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^isub>2. ?H pc\<^isub>2)")
    proof
      assume throw: ?throw
      then obtain pc\<^isub>2 where
	pc\<^isub>2: "?pc\<^isub>1+1 \<le> pc\<^isub>2 \<and> pc\<^isub>2 < ?pc\<^isub>2 \<and>
              \<not> caught P pc\<^isub>2 h\<^isub>2 xa (compxE\<^isub>2 e\<^isub>2 (?pc\<^isub>1+1) (size vs))" and
	eval\<^isub>2: "P \<turnstile> ?\<sigma>\<^isub>1 -jvm\<rightarrow> handle P C M xa h\<^isub>2 vs ls\<^isub>2 pc\<^isub>2 frs"
	using IH\<^isub>2 Seq\<^isub>1.prems by fastsimp
      have "?H pc\<^isub>2" using pc\<^isub>2 jvm_trans[OF eval\<^isub>1 eval\<^isub>2]	by auto
      thus "\<exists>pc\<^isub>2. ?H pc\<^isub>2" by iprover
    qed
  qed
next
  case SeqThrow\<^isub>1 thus ?case by fastsimp
next
  case (CondT\<^isub>1 e h\<^isub>0 ls\<^isub>0 h\<^isub>1 ls\<^isub>1 e\<^isub>1 e' h\<^isub>2 ls\<^isub>2 e\<^isub>2)
  let ?pc\<^isub>1 = "pc + length(compE\<^isub>2 e)"
  let ?\<sigma>\<^isub>0 = "(None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs)"
  let ?\<sigma>\<^isub>1 = "(None,h\<^isub>1,(vs,ls\<^isub>1,C,M,?pc\<^isub>1+1)#frs)"
  have "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> (None,h\<^isub>1,(Bool(True)#vs,ls\<^isub>1,C,M,?pc\<^isub>1)#frs)"
    using CondT\<^isub>1 by (fastsimp simp add: Int_Un_distrib)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^isub>1" using CondT\<^isub>1 by auto
  finally have eval\<^isub>1: "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> ?\<sigma>\<^isub>1".
  let ?pc\<^isub>1' = "?pc\<^isub>1 + 1 + length(compE\<^isub>2 e\<^isub>1)"
  let ?pc\<^isub>2' = "?pc\<^isub>1' + 1 + length(compE\<^isub>2 e\<^isub>2)"
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note eval\<^isub>1
      also have "P \<turnstile> ?\<sigma>\<^isub>1 -jvm\<rightarrow> (None,h\<^isub>2,(v#vs,ls\<^isub>2,C,M,?pc\<^isub>1')#frs)"
	using val CondT\<^isub>1 by(fastsimp simp:Int_Un_distrib)
      also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^isub>2,(v#vs,ls\<^isub>2,C,M,?pc\<^isub>2')#frs)"
	using CondT\<^isub>1 by(auto simp:add_assoc)
      finally show ?trans by(simp add:add_assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^isub>2. ?H pc\<^isub>2)")
    proof
      let ?d = "size vs"
      let ?I = "I - pcs(compxE\<^isub>2 e pc ?d) - pcs(compxE\<^isub>2 e\<^isub>2 (?pc\<^isub>1'+1) ?d)"
      assume throw: ?throw
      moreover
      have "PROP ?P e\<^isub>1 h\<^isub>1 ls\<^isub>1 e' h\<^isub>2 ls\<^isub>2 C M (?pc\<^isub>1+1) v xa vs frs ?I" by fact
      ultimately obtain pc\<^isub>2 where
	pc\<^isub>2: "?pc\<^isub>1+1 \<le> pc\<^isub>2 \<and> pc\<^isub>2 < ?pc\<^isub>1' \<and>
              \<not> caught P pc\<^isub>2 h\<^isub>2 xa (compxE\<^isub>2 e\<^isub>1 (?pc\<^isub>1+1) (size vs))" and
	eval\<^isub>2: "P \<turnstile> ?\<sigma>\<^isub>1 -jvm\<rightarrow> handle P C M xa h\<^isub>2 vs ls\<^isub>2 pc\<^isub>2 frs"
	using CondT\<^isub>1.prems by (fastsimp simp:Int_Un_distrib)
      have "?H pc\<^isub>2" using pc\<^isub>2 jvm_trans[OF eval\<^isub>1 eval\<^isub>2]	by auto
      thus "\<exists>pc\<^isub>2. ?H pc\<^isub>2" by iprover
    qed
  qed
next
  case (CondF\<^isub>1 e h\<^isub>0 ls\<^isub>0 h\<^isub>1 ls\<^isub>1 e\<^isub>2 e' h\<^isub>2 ls\<^isub>2 e\<^isub>1)
  let ?pc\<^isub>1 = "pc + length(compE\<^isub>2 e)"
  let ?pc\<^isub>2 = "?pc\<^isub>1 + 1 + length(compE\<^isub>2 e\<^isub>1)+ 1"
  let ?pc\<^isub>2' = "?pc\<^isub>2 + length(compE\<^isub>2 e\<^isub>2)"
  let ?\<sigma>\<^isub>0 = "(None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs)"
  let ?\<sigma>\<^isub>1 = "(None,h\<^isub>1,(vs,ls\<^isub>1,C,M,?pc\<^isub>2)#frs)"
  have "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> (None,h\<^isub>1,(Bool(False)#vs,ls\<^isub>1,C,M,?pc\<^isub>1)#frs)"
    using CondF\<^isub>1 by (fastsimp simp add: Int_Un_distrib)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^isub>1" using CondF\<^isub>1 by auto
  finally have eval\<^isub>1: "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> ?\<sigma>\<^isub>1".
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note eval\<^isub>1
      also have "P \<turnstile> ?\<sigma>\<^isub>1 -jvm\<rightarrow> (None,h\<^isub>2,(v#vs,ls\<^isub>2,C,M,?pc\<^isub>2')#frs)"
	using val CondF\<^isub>1 by(fastsimp simp:Int_Un_distrib)
      finally show ?trans by(simp add:add_assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^isub>2. ?H pc\<^isub>2)")
    proof
      let ?d = "size vs"
      let ?I = "I - pcs(compxE\<^isub>2 e pc ?d) - pcs(compxE\<^isub>2 e\<^isub>1 (?pc\<^isub>1+1) ?d)"
      assume throw: ?throw
      moreover
      have "PROP ?P e\<^isub>2 h\<^isub>1 ls\<^isub>1 e' h\<^isub>2 ls\<^isub>2 C M ?pc\<^isub>2 v xa vs frs ?I" by fact
      ultimately obtain pc\<^isub>2 where
	pc\<^isub>2: "?pc\<^isub>2 \<le> pc\<^isub>2 \<and> pc\<^isub>2 < ?pc\<^isub>2' \<and>
              \<not> caught P pc\<^isub>2 h\<^isub>2 xa (compxE\<^isub>2 e\<^isub>2 ?pc\<^isub>2 ?d)" and
	eval\<^isub>2: "P \<turnstile> ?\<sigma>\<^isub>1 -jvm\<rightarrow> handle P C M xa h\<^isub>2 vs ls\<^isub>2 pc\<^isub>2 frs"
	using CondF\<^isub>1.prems by(fastsimp simp:Int_Un_distrib)
      have "?H pc\<^isub>2" using pc\<^isub>2 jvm_trans[OF eval\<^isub>1 eval\<^isub>2]	by auto
      thus "\<exists>pc\<^isub>2. ?H pc\<^isub>2" by iprover
    qed
  qed
next
  case (CondThrow\<^isub>1 e h\<^isub>0 ls\<^isub>0 f h\<^isub>1 ls\<^isub>1 e\<^isub>1 e\<^isub>2)
  let ?d = "size vs"
  let ?xt\<^isub>1 = "compxE\<^isub>2 e\<^isub>1 (pc+size(compE\<^isub>2 e)+1) ?d"
  let ?xt\<^isub>2 = "compxE\<^isub>2 e\<^isub>2 (pc+size(compE\<^isub>2 e)+size(compE\<^isub>2 e\<^isub>1)+2) ?d"
  let ?I = "I - (pcs ?xt\<^isub>1 \<union> pcs ?xt\<^isub>2)"
  have "pcs(compxE\<^isub>2 e pc ?d) \<inter> pcs(?xt\<^isub>1 @ ?xt\<^isub>2) = {}"
    using CondThrow\<^isub>1.prems by (simp add:Int_Un_distrib)
  moreover have "PROP ?P e h\<^isub>0 ls\<^isub>0 (throw f) h\<^isub>1 ls\<^isub>1 C M pc v xa vs frs ?I" by fact
  ultimately show ?case using CondThrow\<^isub>1.prems by fastsimp
next
  case (WhileF\<^isub>1 e h\<^isub>0 ls\<^isub>0 h\<^isub>1 ls\<^isub>1 c)
  let ?pc = "pc + length(compE\<^isub>2 e)"
  let ?pc' = "?pc + length(compE\<^isub>2 c) + 3"
  have "P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow>
            (None,h\<^isub>1,(Bool False#vs,ls\<^isub>1,C,M,?pc)#frs)"
    using WhileF\<^isub>1 by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^isub>1,(vs,ls\<^isub>1,C,M,?pc')#frs)"
    using WhileF\<^isub>1 by (auto simp:add_assoc)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^isub>1,(Unit#vs,ls\<^isub>1,C,M,?pc'+1)#frs)"
    using WhileF\<^isub>1.prems by (auto simp:nat_number)
  finally show ?case by (simp add:add_assoc nat_number)
next
  case (WhileT\<^isub>1 e h\<^isub>0 ls\<^isub>0 h\<^isub>1 ls\<^isub>1 c v\<^isub>1 h\<^isub>2 ls\<^isub>2 e\<^isub>3 h\<^isub>3 ls\<^isub>3)
  let ?pc = "pc + length(compE\<^isub>2 e)"
  let ?pc' = "?pc + length(compE\<^isub>2 c) + 1"
  let ?\<sigma>\<^isub>0 = "(None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs)"
  let ?\<sigma>\<^isub>2 = "(None,h\<^isub>2,(vs,ls\<^isub>2,C,M,pc)#frs)"
  have "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> (None,h\<^isub>1,(Bool True#vs,ls\<^isub>1,C,M,?pc)#frs)"
    using WhileT\<^isub>1 by fastsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^isub>1,(vs,ls\<^isub>1,C,M,?pc+1)#frs)"
    using WhileT\<^isub>1.prems by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^isub>2,(v\<^isub>1#vs,ls\<^isub>2,C,M,?pc')#frs)"
    using WhileT\<^isub>1 by(fastsimp)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^isub>2" using WhileT\<^isub>1.prems by auto
  finally have 1: "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> ?\<sigma>\<^isub>2".
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note 1
      also have "P \<turnstile> ?\<sigma>\<^isub>2 -jvm\<rightarrow> (None,h\<^isub>3,(v#vs,ls\<^isub>3,C,M,?pc'+3)#frs)"
	using val WhileT\<^isub>1 by (auto simp add:add_assoc nat_number)
      finally show ?trans by(simp add:add_assoc nat_number)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^isub>2. ?H pc\<^isub>2)")
    proof
      assume throw: ?throw
      moreover
      have "PROP ?P (while (e) c) h\<^isub>2 ls\<^isub>2 e\<^isub>3 h\<^isub>3 ls\<^isub>3 C M pc v xa vs frs I" by fact
      ultimately obtain pc\<^isub>2 where
	pc\<^isub>2: "pc \<le> pc\<^isub>2 \<and> pc\<^isub>2 < ?pc'+3 \<and>
              \<not> caught P pc\<^isub>2 h\<^isub>3 xa (compxE\<^isub>2 (while (e) c) pc (size vs))" and
	2: "P \<turnstile> ?\<sigma>\<^isub>2 -jvm\<rightarrow> handle P C M xa h\<^isub>3 vs ls\<^isub>3 pc\<^isub>2 frs"
	using WhileT\<^isub>1.prems by (auto simp:add_assoc nat_number)
      have "?H pc\<^isub>2" using pc\<^isub>2 jvm_trans[OF 1 2] by auto
      thus "\<exists>pc\<^isub>2. ?H pc\<^isub>2" by iprover
    qed
  qed
next
  case WhileCondThrow\<^isub>1 thus ?case by fastsimp
next
  case (WhileBodyThrow\<^isub>1 e h\<^isub>0 ls\<^isub>0 h\<^isub>1 ls\<^isub>1 c e' h\<^isub>2 ls\<^isub>2)
  let ?pc\<^isub>1 = "pc + length(compE\<^isub>2 e)"
  let ?\<sigma>\<^isub>0 = "(None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs)"
  let ?\<sigma>\<^isub>1 = "(None,h\<^isub>1,(vs,ls\<^isub>1,C,M,?pc\<^isub>1+1)#frs)"
  have "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> (None,h\<^isub>1,(Bool(True)#vs,ls\<^isub>1,C,M,?pc\<^isub>1)#frs)"
    using WhileBodyThrow\<^isub>1 by (fastsimp simp add: Int_Un_distrib)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^isub>1" using  WhileBodyThrow\<^isub>1 by auto
  finally have eval\<^isub>1: "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> ?\<sigma>\<^isub>1".
  let ?pc\<^isub>1' = "?pc\<^isub>1 + 1 + length(compE\<^isub>2 c)"
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm by simp
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^isub>2. ?H pc\<^isub>2)")
    proof
      assume throw: ?throw
      moreover
      have "PROP ?P c h\<^isub>1 ls\<^isub>1 (throw e') h\<^isub>2 ls\<^isub>2 C M (?pc\<^isub>1+1) v xa vs frs
                    (I - pcs (compxE\<^isub>2 e pc (size vs)))" by fact
      ultimately obtain pc\<^isub>2 where
	pc\<^isub>2: "?pc\<^isub>1+1 \<le> pc\<^isub>2 \<and> pc\<^isub>2 < ?pc\<^isub>1' \<and>
              \<not> caught P pc\<^isub>2 h\<^isub>2 xa (compxE\<^isub>2 c (?pc\<^isub>1+1) (size vs))" and
	eval\<^isub>2: "P \<turnstile> ?\<sigma>\<^isub>1 -jvm\<rightarrow> handle P C M xa h\<^isub>2 vs ls\<^isub>2 pc\<^isub>2 frs"
	using WhileBodyThrow\<^isub>1.prems by (fastsimp simp:Int_Un_distrib)
      have "?H pc\<^isub>2" using pc\<^isub>2 jvm_trans[OF eval\<^isub>1 eval\<^isub>2]	by auto
      thus "\<exists>pc\<^isub>2. ?H pc\<^isub>2" by iprover
    qed
  qed
next
  case (Throw\<^isub>1 e h\<^isub>0 ls\<^isub>0 a h\<^isub>1 ls\<^isub>1)
  let ?pc = "pc + size(compE\<^isub>2 e)"
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm by simp
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^isub>1. ?H pc\<^isub>1)")
    proof
      assume ?throw
      hence "P \<turnstile> (None, h\<^isub>0, (vs, ls\<^isub>0, C, M, pc) # frs) -jvm\<rightarrow>
                 (None, h\<^isub>1, (Addr xa#vs, ls\<^isub>1, C, M, ?pc) # frs)"
	using Throw\<^isub>1 by fastsimp
      also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M xa h\<^isub>1 (Addr xa#vs) ls\<^isub>1 ?pc frs"
	using Throw\<^isub>1.prems by(auto simp add:handle_def)
      also have "handle P C M xa h\<^isub>1 (Addr xa#vs) ls\<^isub>1 ?pc frs =
                 handle P C M xa h\<^isub>1 vs ls\<^isub>1 ?pc frs"
	using Throw\<^isub>1.prems by(auto simp add:handle_Cons)
      finally have "?H ?pc" by simp
      thus "\<exists>pc\<^isub>1. ?H pc\<^isub>1" by iprover
    qed
  qed
next
  case (ThrowNull\<^isub>1 e h\<^isub>0 ls\<^isub>0 h\<^isub>1 ls\<^isub>1)
  let ?pc = "pc + size(compE\<^isub>2 e)"
  let ?xa = "addr_of_sys_xcpt NullPointer"
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm by simp
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^isub>1. ?H pc\<^isub>1)")
    proof
      assume throw: ?throw
      have "P \<turnstile> (None, h\<^isub>0, (vs, ls\<^isub>0, C, M, pc) # frs) -jvm\<rightarrow>
                 (None, h\<^isub>1, (Null#vs, ls\<^isub>1, C, M, ?pc) # frs)"
	using ThrowNull\<^isub>1 by fastsimp
      also have "P \<turnstile> \<dots> -jvm\<rightarrow>  handle P C M ?xa h\<^isub>1 (Null#vs) ls\<^isub>1 ?pc frs"
	using ThrowNull\<^isub>1.prems by(auto simp add:handle_def)
      also have "handle P C M ?xa h\<^isub>1 (Null#vs) ls\<^isub>1 ?pc frs =
                 handle P C M ?xa h\<^isub>1 vs ls\<^isub>1 ?pc frs"
	using ThrowNull\<^isub>1.prems by(auto simp add:handle_Cons)
      finally have "?H ?pc" using throw by simp
      thus "\<exists>pc\<^isub>1. ?H pc\<^isub>1" by iprover
    qed
  qed
next
  case ThrowThrow\<^isub>1 thus ?case by fastsimp
next
  case (Try\<^isub>1 e\<^isub>1 h\<^isub>0 ls\<^isub>0 v\<^isub>1 h\<^isub>1 ls\<^isub>1 Ci i e\<^isub>2)
  let ?pc\<^isub>1 = "pc + length(compE\<^isub>2 e\<^isub>1)"
  let ?pc\<^isub>1' = "?pc\<^isub>1 + 2 + length(compE\<^isub>2 e\<^isub>2)"
  have "P,C,M \<rhd> compxE\<^isub>2 (try e\<^isub>1 catch(Ci i) e\<^isub>2) pc (size vs) / I,size vs" by fact
  hence "P,C,M \<rhd> compxE\<^isub>2 e\<^isub>1 pc (size vs) /
                 {pc..<pc + length (compE\<^isub>2 e\<^isub>1)},size vs"
    using Try\<^isub>1.prems by (fastsimp simp:beforex_def split:split_if_asm)
  hence "P \<turnstile> (None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^isub>1,(v\<^isub>1#vs,ls\<^isub>1,C,M,?pc\<^isub>1)#frs)" using Try\<^isub>1 by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^isub>1,(v\<^isub>1#vs,ls\<^isub>1,C,M,?pc\<^isub>1')#frs)"
    using Try\<^isub>1.prems by auto
  finally show ?case by (auto simp:add_assoc)
next
  case (TryCatch\<^isub>1 e\<^isub>1 h\<^isub>0 ls\<^isub>0 a h\<^isub>1 ls\<^isub>1 D fs Ci i e\<^isub>2 e\<^isub>2' h\<^isub>2 ls\<^isub>2)
  let ?e = "try e\<^isub>1 catch(Ci i) e\<^isub>2"
  let ?xt = "compxE\<^isub>2 ?e pc (size vs)"
  let ?\<sigma>\<^isub>0 = "(None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs)"
  let ?ls\<^isub>1 = "ls\<^isub>1[i := Addr a]"
  let ?pc\<^isub>1 = "pc + length(compE\<^isub>2 e\<^isub>1)"
  let ?pc\<^isub>1' = "?pc\<^isub>1 + 2"
  let ?\<sigma>\<^isub>1 = "(None,h\<^isub>1,(vs,?ls\<^isub>1,C,M, ?pc\<^isub>1') # frs)"
  have I: "{pc..<pc + length (compE\<^isub>2 (try e\<^isub>1 catch(Ci i) e\<^isub>2))} \<subseteq> I"
   and beforex: "P,C,M \<rhd> ?xt/I,size vs" by fact+
  have "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> (None,h\<^isub>1,((Addr a)#vs,ls\<^isub>1,C,M, ?pc\<^isub>1+1) # frs)"
  proof -
    have "PROP ?P e\<^isub>1 h\<^isub>0 ls\<^isub>0 (Throw a) h\<^isub>1 ls\<^isub>1 C M pc w a vs frs {pc..<pc + length (compE\<^isub>2 e\<^isub>1)}"
      by fact
    moreover have "P,C,M \<rhd> compxE\<^isub>2 e\<^isub>1 pc (size vs)/{pc..<?pc\<^isub>1},size vs"
      using beforex I pcs_subset by(force elim!: beforex_appendD1)
    ultimately have
      "\<exists>pc\<^isub>1. pc \<le> pc\<^isub>1 \<and> pc\<^isub>1 < ?pc\<^isub>1 \<and>
             \<not> caught P pc\<^isub>1 h\<^isub>1 a (compxE\<^isub>2 e\<^isub>1 pc (size vs)) \<and>
             P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> handle P C M a h\<^isub>1 vs ls\<^isub>1 pc\<^isub>1 frs"
      using  TryCatch\<^isub>1.prems by auto
    then obtain pc\<^isub>1 where
      pc\<^isub>1_in_e\<^isub>1: "pc \<le> pc\<^isub>1" "pc\<^isub>1 < ?pc\<^isub>1" and
      pc\<^isub>1_not_caught: "\<not> caught P pc\<^isub>1 h\<^isub>1 a (compxE\<^isub>2 e\<^isub>1 pc (size vs))" and
      0: "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> handle P C M a h\<^isub>1 vs ls\<^isub>1 pc\<^isub>1 frs" by iprover
    from beforex obtain xt\<^isub>0 xt\<^isub>1
      where ex_tab: "ex_table_of P C M = xt\<^isub>0 @ ?xt @ xt\<^isub>1"
      and disj: "pcs xt\<^isub>0 \<inter> I = {}" by(auto simp:beforex_def)
    have hp: "h\<^isub>1 a = Some (D, fs)" "P\<^isub>1 \<turnstile> D \<preceq>\<^sup>* Ci" by fact+
    have "pc\<^isub>1 \<notin> pcs xt\<^isub>0" using pc\<^isub>1_in_e\<^isub>1 I disj by auto
    with pc\<^isub>1_in_e\<^isub>1 pc\<^isub>1_not_caught hp
    show ?thesis using ex_tab 0 by(simp add:handle_def matches_ex_entry_def)
  qed
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^isub>1" using TryCatch\<^isub>1 by auto
  finally have 1: "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> ?\<sigma>\<^isub>1" .
  let ?pc\<^isub>2 = "?pc\<^isub>1' + length(compE\<^isub>2 e\<^isub>2)"
  let ?I\<^isub>2 = "{?pc\<^isub>1' ..< ?pc\<^isub>2}"
  have "P,C,M \<rhd> compxE\<^isub>2 ?e pc (size vs) / I,size vs" by fact
  hence beforex\<^isub>2: "P,C,M \<rhd> compxE\<^isub>2 e\<^isub>2 ?pc\<^isub>1' (size vs) / ?I\<^isub>2, size vs"
    using I pcs_subset[of _ ?pc\<^isub>1'] by(auto elim!:beforex_appendD2)
  have IH\<^isub>2: "PROP ?P e\<^isub>2 h\<^isub>1 ?ls\<^isub>1 e\<^isub>2' h\<^isub>2 ls\<^isub>2 C M ?pc\<^isub>1' v xa vs frs ?I\<^isub>2" by fact
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note 1 also have "P \<turnstile> ?\<sigma>\<^isub>1 -jvm\<rightarrow> (None,h\<^isub>2,(v#vs,ls\<^isub>2,C,M,?pc\<^isub>2)#frs)"
	using val beforex\<^isub>2 IH\<^isub>2 TryCatch\<^isub>1.prems by auto
      finally show ?trans by(simp add:add_assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^isub>2. ?H pc\<^isub>2)")
    proof
      assume throw: ?throw
      then obtain pc\<^isub>2 where
	pc\<^isub>2: "?pc\<^isub>1+2 \<le> pc\<^isub>2 \<and> pc\<^isub>2 < ?pc\<^isub>2 \<and>
              \<not> caught P pc\<^isub>2 h\<^isub>2 xa (compxE\<^isub>2 e\<^isub>2 ?pc\<^isub>1' (size vs))" and
	2: "P \<turnstile> ?\<sigma>\<^isub>1 -jvm\<rightarrow> handle P C M xa h\<^isub>2 vs ls\<^isub>2 pc\<^isub>2 frs"
	using IH\<^isub>2 beforex\<^isub>2 TryCatch\<^isub>1.prems by auto
      have "?H pc\<^isub>2" using pc\<^isub>2 jvm_trans[OF 1 2]
	by (simp add:match_ex_entry) (fastsimp)
      thus "\<exists>pc\<^isub>2. ?H pc\<^isub>2" by iprover
    qed
  qed
next
  case (TryThrow\<^isub>1 e\<^isub>1 h\<^isub>0 ls\<^isub>0 a h\<^isub>1 ls\<^isub>1 D fs Ci i e\<^isub>2)
  let ?\<sigma>\<^isub>0 = "(None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs)"
  let ?pc\<^isub>1 = "pc + length(compE\<^isub>2 e\<^isub>1)"
  let ?e = "try e\<^isub>1 catch(Ci i) e\<^isub>2"
  let ?xt = "compxE\<^isub>2 ?e pc (size vs)"
  have I: "{pc..<pc + length (compE\<^isub>2 (try e\<^isub>1 catch(Ci i) e\<^isub>2))} \<subseteq> I"
   and beforex: "P,C,M \<rhd> ?xt/I,size vs" by fact+
  have "PROP ?P e\<^isub>1 h\<^isub>0 ls\<^isub>0 (Throw a) h\<^isub>1 ls\<^isub>1 C M pc w a vs frs {pc..<pc + length (compE\<^isub>2 e\<^isub>1)}" by fact
  moreover have "P,C,M \<rhd> compxE\<^isub>2 e\<^isub>1 pc (size vs)/{pc..<?pc\<^isub>1},size vs"
    using beforex I pcs_subset by(force elim!: beforex_appendD1)
    ultimately have
      "\<exists>pc\<^isub>1. pc \<le> pc\<^isub>1 \<and> pc\<^isub>1 < ?pc\<^isub>1 \<and>
             \<not> caught P pc\<^isub>1 h\<^isub>1 a (compxE\<^isub>2 e\<^isub>1 pc (size vs)) \<and>
             P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> handle P C M a h\<^isub>1 vs ls\<^isub>1 pc\<^isub>1 frs"
      using TryThrow\<^isub>1.prems by auto
    then obtain pc\<^isub>1 where
      pc\<^isub>1_in_e\<^isub>1: "pc \<le> pc\<^isub>1" "pc\<^isub>1 < ?pc\<^isub>1" and
      pc\<^isub>1_not_caught: "\<not> caught P pc\<^isub>1 h\<^isub>1 a (compxE\<^isub>2 e\<^isub>1 pc (size vs))" and
      0: "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> handle P C M a h\<^isub>1 vs ls\<^isub>1 pc\<^isub>1 frs" by iprover
  show ?case (is "?N \<and> (?eq \<longrightarrow> (\<exists>pc\<^isub>2. ?H pc\<^isub>2))")
  proof
    show ?N by simp
  next
    { assume ?eq
      with TryThrow\<^isub>1 pc\<^isub>1_in_e\<^isub>1 pc\<^isub>1_not_caught 0
      have "?H pc\<^isub>1" by (simp add:match_ex_entry) auto
      hence "\<exists>pc\<^isub>2. ?H pc\<^isub>2" by iprover
    }
    thus "?eq \<longrightarrow> (\<exists>pc\<^isub>2. ?H pc\<^isub>2)" by iprover
  qed
next
  case Nil\<^isub>1 thus ?case by simp
next
  case (Cons\<^isub>1 e h\<^isub>0 ls\<^isub>0 v h\<^isub>1 ls\<^isub>1 es fs h\<^isub>2 ls\<^isub>2)
  let ?pc\<^isub>1 = "pc + length(compE\<^isub>2 e)"
  let ?\<sigma>\<^isub>0 = "(None,h\<^isub>0,(vs,ls\<^isub>0,C,M,pc)#frs)"
  let ?\<sigma>\<^isub>1 = "(None,h\<^isub>1,(v#vs,ls\<^isub>1,C,M,?pc\<^isub>1)#frs)"
  have 1: "P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> ?\<sigma>\<^isub>1" using Cons\<^isub>1 by fastsimp
  let ?pc\<^isub>2 = "?pc\<^isub>1 + length(compEs\<^isub>2 es)"
  have IHs: "PROP ?Ps es h\<^isub>1 ls\<^isub>1 fs h\<^isub>2 ls\<^isub>2 C M ?pc\<^isub>1 (tl ws) xa es' (v#vs) frs
    (I - pcs (compxE\<^isub>2 e pc (length vs)))" by fact
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note 1
      also have "P \<turnstile> ?\<sigma>\<^isub>1 -jvm\<rightarrow> (None,h\<^isub>2,(rev(ws) @ vs,ls\<^isub>2,C,M,?pc\<^isub>2)#frs)"
	using val IHs Cons\<^isub>1.prems by fastsimp
      finally show ?trans by(simp add:add_assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^isub>2. ?H pc\<^isub>2)")
    proof
      assume throw: ?throw
      then obtain pc\<^isub>2 where
	pc\<^isub>2: "?pc\<^isub>1 \<le> pc\<^isub>2 \<and> pc\<^isub>2 < ?pc\<^isub>2 \<and>
              \<not> caught P pc\<^isub>2 h\<^isub>2 xa (compxEs\<^isub>2 es ?pc\<^isub>1 (size vs + 1))" and
	2: "P \<turnstile> ?\<sigma>\<^isub>1 -jvm\<rightarrow> handle P C M xa h\<^isub>2 (v#vs) ls\<^isub>2 pc\<^isub>2 frs"
	using IHs Cons\<^isub>1.prems
	by(fastsimp simp:Cons_eq_append_conv neq_Nil_conv)
      have "?H pc\<^isub>2" using Cons\<^isub>1.prems pc\<^isub>2 jvm_trans[OF 1 2]
	by (auto simp add: handle_Cons)
      thus "\<exists>pc\<^isub>2. ?H pc\<^isub>2" by iprover
    qed
  qed
next
  case ConsThrow\<^isub>1 thus ?case by (fastsimp simp:Cons_eq_append_conv)
qed
(*>*)


(*FIXME move! *)
lemma atLeast0AtMost[simp]: "{0::nat..n} = {..n}"
by auto

lemma atLeast0LessThan[simp]: "{0::nat..<n} = {..<n}"
by auto

fun exception :: "'a exp \<Rightarrow> addr option" where
  "exception (Throw a) = Some a"
| "exception e = None"


lemma comp\<^isub>2_correct:
assumes method: "P\<^isub>1 \<turnstile> C sees M:Ts\<rightarrow>T = body in C"
    and eval:   "P\<^isub>1 \<turnstile>\<^sub>1 \<langle>body,(h,ls)\<rangle> \<Rightarrow> \<langle>e',(h',ls')\<rangle>"
shows "compP\<^isub>2 P\<^isub>1 \<turnstile> (None,h,[([],ls,C,M,0)]) -jvm\<rightarrow> (exception e',h',[])"
(*<*)
      (is "_ \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> ?\<sigma>\<^isub>1")
proof -
  let ?P = "compP\<^isub>2 P\<^isub>1"
  have code: "?P,C,M,0 \<rhd> compE\<^isub>2 body" using beforeM[OF method] by auto
  have xtab: "?P,C,M \<rhd> compxE\<^isub>2 body 0 (size[])/{..<size(compE\<^isub>2 body)},size[]"
    using beforexM[OF method] by auto
  -- "Distinguish if e' is a value or an exception"
  { fix v assume [simp]: "e' = Val v"
    have "?P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> (None,h',[([v],ls',C,M,size(compE\<^isub>2 body))])"
      using Jcc[OF eval code xtab] by auto
    also have "?P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^isub>1" using beforeM[OF method] by auto
    finally have ?thesis .
  }
  moreover
  { fix a assume [simp]: "e' = Throw a"
    obtain pc where pc: "0 \<le> pc \<and> pc < size(compE\<^isub>2 body) \<and>
          \<not> caught ?P pc h' a (compxE\<^isub>2 body 0 0)"
    and 1: "?P \<turnstile> ?\<sigma>\<^isub>0 -jvm\<rightarrow> handle ?P C M a h' [] ls' pc []"
      using Jcc[OF eval code xtab] by fastsimp
    from pc have "handle ?P C M a h' [] ls' pc [] = ?\<sigma>\<^isub>1" using xtab method
      by(auto simp:handle_def compMb\<^isub>2_def)
    with 1 have ?thesis by simp
  } 
  ultimately show ?thesis using eval\<^isub>1_final[OF eval] by(auto simp:final_def)
qed
(*>*)

end

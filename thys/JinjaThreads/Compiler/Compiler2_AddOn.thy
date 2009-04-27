(*  Title:      JinjaThreads/Compiler/Compiler2_Addon.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Various additional lemmas} *}

theory Compiler2_AddOn imports Compiler2 Correctness1 "../Common/Conform" "../J/DefAss" "../Common/ExternalCallWF" begin

section{* Exception tables *}

constdefs
  pcs :: "ex_table \<Rightarrow> nat set"
  "pcs xt  \<equiv>  \<Union>(f,t,C,h,d) \<in> set xt. {f ..< t}"

lemma pcs_subset:
shows "\<And>pc d. pcs(compxE2 e pc d) \<subseteq> {pc..<pc+size(compE2 e)}"
  "\<And>pc d. pcs(compxEs2 es pc d) \<subseteq> {pc..<pc+size(compEs2 es)}" 
apply(induct e and es)
apply (simp_all add:pcs_def)
apply (fastsimp split:bop.splits)+
done

lemma pcs_Nil [simp]: "pcs [] = {}"
by(simp add:pcs_def)


lemma pcs_Cons [simp]: "pcs (x#xt) = {fst x ..< fst(snd x)} \<union> pcs xt"
by(auto simp add: pcs_def)


lemma pcs_append [simp]: "pcs(xt\<^isub>1 @ xt\<^isub>2) = pcs xt\<^isub>1 \<union> pcs xt\<^isub>2"
by(simp add:pcs_def)


lemma [simp]: "pc < pc\<^isub>0 \<or> pc\<^isub>0+size(compE2 e) \<le> pc \<Longrightarrow> pc \<notin> pcs(compxE2 e pc\<^isub>0 d)"
using pcs_subset by fastsimp

lemma [simp]: "pc < pc0 \<or> pc0+size(compEs2 es) \<le> pc \<Longrightarrow> pc \<notin> pcs(compxEs2 es pc0 d)"
using pcs_subset by fastsimp

lemma [simp]: "pc1 + size(compE2 e1) \<le> pc2 \<Longrightarrow> pcs(compxE2 e1 pc1 d1) \<inter> pcs(compxE2 e2 pc2 d2) = {}"
using pcs_subset by fastsimp

lemma [simp]: "pc\<^isub>1 + size(compE2 e) \<le> pc\<^isub>2 \<Longrightarrow> pcs(compxE2 e pc\<^isub>1 d\<^isub>1) \<inter> pcs(compxEs2 es pc\<^isub>2 d\<^isub>2) = {}"
using pcs_subset by fastsimp

lemma match_ex_table_append_not_pcs [simp]:
 "pc \<notin> pcs xt0 \<Longrightarrow> match_ex_table P C pc (xt0 @ xt1) = match_ex_table P C pc xt1"
by (induct xt0) (auto simp: matches_ex_entry_def)


lemma outside_pcs_not_matches_entry [simp]:
  "\<lbrakk> x \<in> set xt; pc \<notin> pcs xt \<rbrakk> \<Longrightarrow> \<not> matches_ex_entry P D pc x"
by(auto simp:matches_ex_entry_def pcs_def)


lemma outside_pcs_compxE2_not_matches_entry [simp]:
assumes xe: "xe \<in> set(compxE2 e pc d)" and outside: "pc' < pc \<or> pc+size(compE2 e) \<le> pc'"
shows "\<not> matches_ex_entry P C pc' xe"

proof
  assume "matches_ex_entry P C pc' xe"
  with xe have "pc' \<in> pcs(compxE2 e pc d)"
    by(force simp add:matches_ex_entry_def pcs_def)
  with outside show False by simp
qed


lemma outside_pcs_compxEs2_not_matches_entry [simp]:
assumes xe: "xe \<in> set(compxEs2 es pc d)" and outside: "pc' < pc \<or> pc+size(compEs2 es) \<le> pc'"
shows "\<not> matches_ex_entry P C pc' xe"

proof
  assume "matches_ex_entry P C pc' xe"
  with xe have "pc' \<in> pcs(compxEs2 es pc d)"
    by(force simp add:matches_ex_entry_def pcs_def)
  with outside show False by simp
qed


lemma match_ex_table_app[simp]:
  "\<forall>xte \<in> set xt\<^isub>1. \<not> matches_ex_entry P D pc xte \<Longrightarrow>
  match_ex_table P D pc (xt\<^isub>1 @ xt) = match_ex_table P D pc xt"
by(induct xt\<^isub>1) simp_all


lemma match_ex_table_eq_NoneI [simp]:
  "\<forall>x \<in> set xtab. \<not> matches_ex_entry P C pc x \<Longrightarrow>
  match_ex_table P C pc xtab = None"
using match_ex_table_app[where ?xt = "[]"] by fastsimp

lemma match_ex_table_not_pcs_None:
  "pc \<notin> pcs xt \<Longrightarrow> match_ex_table P C pc xt = None"
by(auto intro: match_ex_table_eq_NoneI)

lemma match_ex_entry:
  fixes start shows
  "matches_ex_entry P C pc (start, end, catch_type, handler) =
  (start \<le> pc \<and> pc < end \<and>  P \<turnstile> C \<preceq>\<^sup>* catch_type)"
by(simp add:matches_ex_entry_def)

lemma pcs_compxE2D [dest]:
  "pc \<in> pcs (compxE2 e pc' d) \<Longrightarrow> pc' \<le> pc \<and> pc < pc' + length (compE2 e)"
using pcs_subset by(fastsimp)

lemma pcs_compxEs2D [dest]:
  "pc \<in> pcs (compxEs2 es pc' d) \<Longrightarrow> pc' \<le> pc \<and> pc < pc' + length (compEs2 es)"
using pcs_subset by(fastsimp)


constdefs
  shift :: "nat \<Rightarrow> ex_table \<Rightarrow> ex_table"
  "shift n xt \<equiv> map (\<lambda>(from,to,C,handler,depth). (n+from,n+to,C,n+handler,depth)) xt"

lemma shift_0 [simp]: "shift 0 xt = xt"
by(induct xt)(auto simp:shift_def)

lemma shift_Nil [simp]: "shift n [] = []"
by(simp add:shift_def)

lemma shift_Cons_tuple [simp]:
  "shift n ((from, to, C, handler, depth) # xt) = (from + n, to + n, C, handler + n, depth) # shift n xt"
by(simp add: shift_def)

lemma shift_append [simp]: "shift n (xt\<^isub>1 @ xt\<^isub>2) = shift n xt\<^isub>1 @ shift n xt\<^isub>2"
by(simp add:shift_def)

lemma shift_shift [simp]: "shift m (shift n xt) = shift (m+n) xt"
by(simp add: shift_def map_compose[symmetric] split_def)

lemma shift_compxE2: "shift pc (compxE2 e pc' d) = compxE2 e (pc' + pc) d"
 and  shift_compxEs2: "shift pc (compxEs2 es pc' d) = compxEs2 es (pc' + pc) d"
apply(induct e and es arbitrary: pc pc' d and pc pc' d)
apply(auto simp:shift_def add_ac)
done

lemma compxE2_size_convs [simp]: "n \<noteq> 0 \<Longrightarrow> compxE2 e n d = shift n (compxE2 e 0 d)"
 and compxEs2_size_convs: "n \<noteq> 0 \<Longrightarrow> compxEs2 es n d = shift n (compxEs2 es 0 d)" 
by(simp_all add:shift_compxE2 shift_compxEs2)

lemma pcs_shift_conv [simp]: "pcs (shift n xt) = op + n ` pcs xt"
apply(auto simp add: shift_def pcs_def)
apply(rule_tac x="x-n" in image_eqI)
apply(auto)
apply(rule bexI)
 prefer 2
 apply(assumption)
apply(auto)
done

lemma image_plus_const_conv [simp]:
  fixes m :: nat
  shows "m \<in> op + n ` A \<longleftrightarrow> m \<ge> n \<and> m - n \<in> A"
by(force)

lemma match_ex_table_shift_eq_None_conv [simp]:
  "match_ex_table P C pc (shift n xt) = None \<longleftrightarrow> pc < n \<or> match_ex_table P C (pc - n) xt = None"
by(induct xt)(auto simp add: match_ex_entry split: split_if_asm)

lemma match_ex_table_shift_pc_None:
  "pc \<ge> n \<Longrightarrow> match_ex_table P C pc (shift n xt) = None \<longleftrightarrow> match_ex_table P C (pc - n) xt = None"
by(simp add: match_ex_table_shift_eq_None_conv)

lemma match_ex_table_shift_eq_Some_conv [simp]:
  "match_ex_table P C pc (shift n xt) = \<lfloor>(pc', d)\<rfloor> \<longleftrightarrow>
   pc \<ge> n \<and> pc' \<ge> n \<and> match_ex_table P C (pc - n) xt = \<lfloor>(pc' - n, d)\<rfloor>"
by(induct xt)(auto simp add: match_ex_entry split: split_if_asm)

lemma match_ex_table_shift:
 "match_ex_table P C pc xt = \<lfloor>(pc', d)\<rfloor> \<Longrightarrow> match_ex_table P C (n + pc) (shift n xt) = \<lfloor>(n + pc', d)\<rfloor>"
by(simp add: match_ex_table_shift_eq_Some_conv)

lemma match_ex_table_shift_pcD:
  "match_ex_table P C pc (shift n xt) = \<lfloor>(pc', d)\<rfloor> \<Longrightarrow> pc \<ge> n \<and> pc' \<ge> n \<and> match_ex_table P C (pc - n) xt = \<lfloor>(pc' - n, d)\<rfloor>"
by(simp add: match_ex_table_shift_eq_Some_conv)

lemma match_ex_table_pcsD: "match_ex_table P C pc xt = \<lfloor>(pc', D)\<rfloor> \<Longrightarrow> pc \<in> pcs xt"
by(induct xt)(auto split: split_if_asm simp add: match_ex_entry)




definition stack_xlift :: "nat \<Rightarrow> ex_table \<Rightarrow> ex_table"
where "stack_xlift n xt \<equiv> map (\<lambda>(from,to,C,handler,depth). (from, to, C, handler, n + depth)) xt"

lemma stack_xlift_0 [simp]: "stack_xlift 0 xt = xt"
by(induct xt, auto simp add: stack_xlift_def)

lemma stack_xlift_Nil [simp]: "stack_xlift n [] = []"
by(simp add: stack_xlift_def)

lemma stack_xlift_Cons_tuple [simp]:
  "stack_xlift n ((from, to, C, handler, depth) # xt) = (from, to, C, handler, depth + n) # stack_xlift n xt"
by(simp add: stack_xlift_def)

lemma stack_xlift_append [simp]: "stack_xlift n (xt @ xt') = stack_xlift n xt @ stack_xlift n xt'"
by(simp add: stack_xlift_def)

lemma stack_xlift_stack_xlift [simp]: "stack_xlift n (stack_xlift m xt) = stack_xlift (n + m) xt"
by(simp add: stack_xlift_def map_compose[symmetric] split_def)

lemma stack_xlift_compxE2: "stack_xlift n (compxE2 e pc d) = compxE2 e pc (n + d)"
  and stack_xlift_compxEs2: "stack_xlift n (compxEs2 es pc d) = compxEs2 es pc (n + d)"
by(induct e and es arbitrary: d pc and d pc)
  (auto simp add: shift_compxE2 simp del: compxE2_size_convs)

lemma compxE2_stack_xlift_convs [simp]: "d > 0 \<Longrightarrow> compxE2 e pc d = stack_xlift d (compxE2 e pc 0)"
  and compxEs2_stack_xlift_convs [simp]: "d > 0 \<Longrightarrow> compxEs2 es pc d = stack_xlift d (compxEs2 es pc 0)"
by(simp_all add: stack_xlift_compxE2 stack_xlift_compxEs2)

lemma stack_xlift_shift [simp]: "stack_xlift d (shift n xt) = shift n (stack_xlift d xt)"
by(induct xt)(auto)

lemma pcs_stack_xlift_conv [simp]: "pcs (stack_xlift n xt) = pcs xt"
by(auto simp add: pcs_def stack_xlift_def)

lemma match_ex_table_stack_xlift_eq_None_conv [simp]:
  "match_ex_table P C pc (stack_xlift d xt) = None \<longleftrightarrow> match_ex_table P C pc xt = None"
by(induct xt)(auto simp add: match_ex_entry)

lemma match_ex_table_stack_xlift_eq_Some_conv [simp]:
  "match_ex_table P C pc (stack_xlift n xt) = \<lfloor>(pc', d)\<rfloor> \<longleftrightarrow> d \<ge> n \<and> match_ex_table P C pc xt = \<lfloor>(pc', d - n)\<rfloor>"
by(induct xt)(auto simp add: match_ex_entry)

lemma match_ex_table_stack_xliftD:
  "match_ex_table P C pc (stack_xlift n xt) = \<lfloor>(pc', d)\<rfloor> \<Longrightarrow> d \<ge> n \<and> match_ex_table P C pc xt = \<lfloor>(pc', d - n)\<rfloor>"
by(simp)

lemma match_ex_table_stack_xlift:
  "match_ex_table P C pc xt = \<lfloor>(pc', d)\<rfloor> \<Longrightarrow> match_ex_table P C pc (stack_xlift n xt) = \<lfloor>(pc', n + d)\<rfloor>"
by simp


lemma match_ex_table_None_append [simp]:
  "match_ex_table P C pc xt = None
  \<Longrightarrow> match_ex_table P C pc (xt @ xt') = match_ex_table P C pc xt'"
by(induct xt, auto)

lemma match_ex_table_Some_append [simp]: 
  "match_ex_table P C pc xt = \<lfloor>(pc', d)\<rfloor> \<Longrightarrow> match_ex_table P C pc (xt @ xt') = \<lfloor>(pc', d)\<rfloor>"
by(induct xt)(auto)

lemma match_ex_table_append:
  "match_ex_table P C pc (xt @ xt') = (case match_ex_table P C pc xt of None \<Rightarrow> match_ex_table P C pc xt' 
                                                                  | Some pcd \<Rightarrow> Some pcd)"
by(auto)

lemma match_ex_table_pc_length_compE2:
  "match_ex_table P a pc (compxE2 e pc' d) = \<lfloor>pcd\<rfloor> \<Longrightarrow> pc' \<le> pc \<and> pc < length (compE2 e) + pc'"
  
  and match_ex_table_pc_length_compEs2:
  "match_ex_table P a pc (compxEs2 es pc' d) = \<lfloor>pcd\<rfloor> \<Longrightarrow> pc' \<le> pc \<and> pc < length (compEs2 es) + pc'"
using pcs_subset by(cases pcd, fastsimp dest!: match_ex_table_pcsD)+

lemma match_ex_table_compxE2_shift_conv:
  "f > 0 \<Longrightarrow> match_ex_table P C pc (compxE2 e f d) = \<lfloor>(pc', d')\<rfloor> \<longleftrightarrow> pc \<ge> f \<and> pc' \<ge> f \<and> match_ex_table P C (pc - f) (compxE2 e 0 d) = \<lfloor>(pc' - f, d')\<rfloor>"
by simp

lemma match_ex_table_compxEs2_shift_conv:
  "f > 0 \<Longrightarrow> match_ex_table P C pc (compxEs2 es f d) = \<lfloor>(pc', d')\<rfloor> \<longleftrightarrow> pc \<ge> f \<and> pc' \<ge> f \<and> match_ex_table P C (pc - f) (compxEs2 es 0 d) = \<lfloor>(pc' - f, d')\<rfloor>"
by(simp add: compxEs2_size_convs)

lemma match_ex_table_compxE2_stack_conv:
  "d > 0 \<Longrightarrow> match_ex_table P C pc (compxE2 e 0 d) = \<lfloor>(pc', d')\<rfloor> \<longleftrightarrow> d' \<ge> d \<and> match_ex_table P C pc (compxE2 e 0 0) = \<lfloor>(pc', d' - d)\<rfloor>"
by simp

lemma match_ex_table_compxEs2_stack_conv:
  "d > 0 \<Longrightarrow> match_ex_table P C pc (compxEs2 es 0 d) = \<lfloor>(pc', d')\<rfloor> \<longleftrightarrow> d' \<ge> d \<and> match_ex_table P C pc (compxEs2 es 0 0) = \<lfloor>(pc', d' - d)\<rfloor>"
by(simp add: compxEs2_stack_xlift_convs)


(* Eigene Einfuegungen spaeter ggf. verschieben *)

lemma compE2_blocks1 [simp]:
  "compE2 (blocks1 n Ts body) = compE2 body"
apply(induct n Ts body rule: blocks1.induct)
apply(auto)
done

lemma compxE2_blocks1 [simp]:
  "compxE2 (blocks1 n Ts body) = compxE2 body"
apply(induct n Ts body rule: blocks1.induct)
apply(auto intro!: ext)
done

lemma B_blocks1 [intro]: "\<B> body (n + length Ts) \<Longrightarrow> \<B> (blocks1 n Ts body) n"
apply(induct n Ts body rule: blocks1.induct)
apply(auto)
done

primrec env_exp :: "expr1 \<Rightarrow> env1"
  and env_exps :: "expr1 list \<Rightarrow> env1"
where
  "env_exp (new C) = []"
| "env_exp (newA T\<lfloor>e\<rceil>) = env_exp e"
| "env_exp (Cast U e) = env_exp e"
| "env_exp (Val V) = []"
| "env_exp (Var V) = []"
| "env_exp (V := e) = env_exp e"
| "env_exp (e1\<guillemotleft>bop\<guillemotright> e2) = (if is_val e1 then env_exp e2 else env_exp e1)"
| "env_exp (a\<lfloor>i\<rceil>) = (if is_val a then env_exp i else env_exp a)"
| "env_exp (a\<lfloor>i\<rceil> := e) = (if is_val a then if is_val i then env_exp e else env_exp i else env_exp a)"
| "env_exp (a\<bullet>length) = env_exp a"
| "env_exp (e\<bullet>F{D}) = env_exp e"
| "env_exp (e\<bullet>F{D} := e') = (if is_val e then env_exp e' else env_exp e)"
| "env_exp (e\<bullet>M(es)) = (if is_val e then env_exps es else env_exp e)"
| "env_exp {V:T=vo; e}\<^bsub>cr\<^esub> = T # env_exp e"
| "env_exp (sync\<^bsub>V\<^esub> (e1) e2) = env_exp e1"
| "env_exp (insync\<^bsub>V\<^esub> (a) e) = Class Object # env_exp e"
| "env_exp (e1;;e2) = env_exp e1"
| "env_exp (if (b) e1 else e2) = env_exp b"
| "env_exp (while (b) c) = []"
| "env_exp (throw e) = env_exp e"
| "env_exp (try e1 catch(C V) e2) = env_exp e1"
| "env_exps [] = []"
| "env_exps (e # es) = (if is_val e then env_exps es else env_exp e)"

definition lconf1 :: "'m prog \<Rightarrow> heap \<Rightarrow> nat set \<Rightarrow> locals1 \<Rightarrow> env1 \<Rightarrow> bool"   ("_,_,_ \<turnstile>1 _ '(:\<le>') _" [51,51,51,51] 50)
where
  "P,h,A \<turnstile>1 xs (:\<le>) Env \<equiv> (\<forall>i \<in> A. i < length Env \<and> i < length xs \<and> P,h \<turnstile> xs ! i :\<le> Env ! i)"

consts
 \<A>1  :: "expr1 \<Rightarrow> nat hyperset"
 \<A>s1 :: "expr1 list \<Rightarrow> nat hyperset" 

primrec
"\<A>1 (new C) = \<lfloor>{}\<rfloor>"
"\<A>1 (newA T\<lfloor>e\<rceil>) = \<A>1 e"
"\<A>1 (Cast U e) = \<A>1 e"
"\<A>1 (Val v) = \<lfloor>{}\<rfloor>"
"\<A>1 (e1 \<guillemotleft>bop\<guillemotright> e2) = \<A>1 e1 \<squnion> \<A>1 e2"
"\<A>1 (Var V) = \<lfloor>{}\<rfloor>"
"\<A>1 (LAss V e) = \<lfloor>{V}\<rfloor> \<squnion> \<A>1 e"
"\<A>1 (a\<lfloor>i\<rceil>) = \<A>1 a \<squnion> \<A>1 i"
"\<A>1 (a\<lfloor>i\<rceil> := e) = \<A>1 a \<squnion> \<A>1 i \<squnion> \<A>1 e"
"\<A>1 (a\<bullet>length) = \<A>1 a"
"\<A>1 (e\<bullet>F{D}) = \<A>1 e"
"\<A>1 (e\<bullet>F{D} := e') = \<A>1 e \<squnion> \<A>1 e'"
"\<A>1 (e\<bullet>M(es)) = \<A>1 e \<squnion> \<A>s1 es"
"\<A>1 ({V:T=vo; e}\<^bsub>cr\<^esub>) = \<A>1 e \<ominus> V"
"\<A>1 (sync\<^bsub>V\<^esub> (o') e) = \<A>1 o' \<squnion> (\<A>1 e \<ominus> V)"
"\<A>1 (insync\<^bsub>V\<^esub> (a) e) = \<A>1 e \<ominus> V"
"\<A>1 (e1;;e2) = \<A>1 e1 \<squnion> \<A>1 e2"
"\<A>1 (if (e) e1 else e2) =  \<A>1 e \<squnion> (\<A>1 e1 \<sqinter> \<A>1 e2)"
"\<A>1 (while (b) e) = \<A>1 b"
"\<A>1 (throw e) = None"
"\<A>1 (try e1 catch(C V) e2) = \<A>1 e1 \<sqinter> (\<A>1 e2 \<ominus> V)"

"\<A>s1 ([]) = \<lfloor>{}\<rfloor>"
"\<A>s1 (e#es) = \<A>1 e \<squnion> \<A>s1 es"


lemma As1_map_Val[simp]: "\<A>s1 (map Val vs) = \<lfloor>{}\<rfloor>"
by (induct vs) simp_all

lemma As1_append [simp]: "\<A>s1 (xs @ ys) = (\<A>s1 xs) \<squnion> (\<A>s1 ys)"
by(induct xs, auto simp add: hyperset_defs)


consts
 \<D>1  :: "nat \<Rightarrow> expr1 \<Rightarrow> nat hyperset \<Rightarrow> bool"
 \<D>s1 :: "nat \<Rightarrow> expr1 list \<Rightarrow> nat hyperset \<Rightarrow> bool"

primrec
"\<D>1 n (new C) A = True"
"\<D>1 n (newA T\<lfloor>e\<rceil>) A = \<D>1 n e A"
"\<D>1 n (Cast C e) A = \<D>1 n e A"
"\<D>1 n (Val v) A = True"
"\<D>1 n (e1 \<guillemotleft>bop\<guillemotright> e2) A = (\<D>1 n e1 A \<and> \<D>1 n e2 ((if (is_val e1) then A else A \<exclamdown> {0..<n}) \<squnion> \<A>1 e1))"
"\<D>1 n (Var V) A = (V \<in>\<in> A)"
"\<D>1 n (LAss V e) A = \<D>1 n e A"
"\<D>1 n (a\<lfloor>i\<rceil>) A = (\<D>1 n a A \<and> \<D>1 n i ((if is_val a then A else A \<exclamdown> {0..<n}) \<squnion> \<A>1 a))"
"\<D>1 n (a\<lfloor>i\<rceil> := e) A = (\<D>1 n a A \<and>
                         \<D>1 n i ((if is_val a then A else A \<exclamdown> {0..<n}) \<squnion> \<A>1 a) \<and>
                         \<D>1 n e ((if is_val a \<and> is_val i then A else A \<exclamdown> {0..<n}) \<squnion> \<A>1 a \<squnion> \<A>1 i))"
"\<D>1 n (a\<bullet>length) A = \<D>1 n a A"
"\<D>1 n (e\<bullet>F{D}) A = \<D>1 n e A"
"\<D>1 n (e\<^isub>1\<bullet>F{D}:=e\<^isub>2) A = (\<D>1 n e\<^isub>1 A \<and> \<D>1 n e\<^isub>2 ((if is_val e\<^isub>1 then A else A \<exclamdown> {0..<n}) \<squnion> \<A>1 e\<^isub>1))"
"\<D>1 n (e\<bullet>M(es)) A = (\<D>1 n e A \<and> \<D>s1 n es ((if is_val e then A else A \<exclamdown> {0..<n}) \<squnion> \<A>1 e))"
"\<D>1 n ({V:T=vo; e}\<^bsub>cr\<^esub>) A = (if vo = None then \<D>1 (Suc n) e A else \<D>1 (Suc n) e (A \<squnion> \<lfloor>{V}\<rfloor>))"
"\<D>1 n (sync\<^bsub>V\<^esub> (o') e) A = (\<D>1 n o' A \<and> \<D>1 (Suc n) e ((A \<exclamdown> {0..<n}) \<squnion> \<A>1 o'))"
  "\<D>1 n (insync\<^bsub>V\<^esub> (a) e) A = \<D>1 (Suc n) e A"
"\<D>1 n (e1;;e2) A = (\<D>1 n e1 A \<and> \<D>1 n e2 ((A \<exclamdown> {0..<n}) \<squnion> \<A>1 e1))"
"\<D>1 n (if (e) e1 else e2) A =
  (\<D>1 n e A \<and> \<D>1 n e1 ((A \<exclamdown> {0..<n}) \<squnion> \<A>1 e) \<and> \<D>1 n e2 ((A \<exclamdown> {0..<n}) \<squnion> \<A>1 e))"
"\<D>1 n (while (e) c) A = (\<D>1 n e (A \<exclamdown> {0..<n}) \<and> \<D>1 n c ((A \<exclamdown> {0..<n}) \<squnion> \<A>1 e))"
"\<D>1 n (throw e) A = \<D>1 n e A"
"\<D>1 n (try e1 catch(C V) e2) A = (\<D>1 n e1 A \<and> \<D>1 (Suc n) e2 ((A \<exclamdown> {0..<n}) \<squnion> \<lfloor>{V}\<rfloor>))"

"\<D>s1 n ([]) A = True"
"\<D>s1 n (e#es) A = (\<D>1 n e A \<and> \<D>s1 n es ((if is_val e then A else A \<exclamdown> {0..<n}) \<squnion> \<A>1 e))"

lemma D1_mono: "A \<sqsubseteq> A' \<Longrightarrow> \<D>1 n e A \<Longrightarrow> \<D>1 n e A'"
 and Ds1_mono: "A \<sqsubseteq> A' \<Longrightarrow> \<D>s1 n es A \<Longrightarrow> \<D>s1 n es A'"
apply(induct e and es arbitrary: A A' n and A A' n)
apply auto
apply(metis sqUn_lem sqSub_lem)+
done

(* And this is the order of premises preferred during application: *)
lemma D1_mono': "\<D>1 n e A \<Longrightarrow> A \<sqsubseteq> A' \<Longrightarrow> \<D>1 n e A'"
  and Ds1_mono': "\<D>s1 n es A \<Longrightarrow> A \<sqsubseteq> A' \<Longrightarrow> \<D>s1 n es A'" 
by(blast intro:D1_mono, blast intro:Ds1_mono)


lemma lconf1_hext_mono: "\<lbrakk> P,h,A \<turnstile>1 xs (:\<le>) Env; hext h h' \<rbrakk> \<Longrightarrow> P,h',A \<turnstile>1 xs (:\<le>) Env"
  unfolding lconf1_def by(auto intro: conf_hext)


theorem red1_preserves_hconf: "\<lbrakk> P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; P,E,hp s \<turnstile>1 e : T; P \<turnstile> hp s \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> hp s' \<surd>"
  and reds1_preserves_hconf: "\<lbrakk> P \<turnstile>1 \<langle>es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>; P,E,hp s \<turnstile>1 es [:] Ts; P \<turnstile> hp s \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> hp s' \<surd>"
proof (induct arbitrary: T E and Ts E rule: red1_reds1.inducts)
  case (Red1New h a C FDTs h' l T E)
  have new: "new_Addr h = Some a" and fields: "P \<turnstile> C has_fields FDTs" by fact+
  have h': "h' = h(a\<mapsto>(Obj C (init_fields FDTs)))" by fact
  have hconf: "P \<turnstile> hp (h, l) \<surd>" by fact
  from new have None: "h a = None" by(rule new_Addr_SomeD)
  moreover have "P,h \<turnstile> (Obj C (init_fields FDTs)) \<surd>"
    using fields by(rule oconf_init_fields)
  ultimately show "P \<turnstile> hp (h', l) \<surd>" using h' hconf by(simp)(rule hconf_new)
next
  case (Red1NewArray h a i h' T l T' E)
  have new: "new_Addr h = Some a"
    and h': "h' = h(a \<mapsto> Arr T (replicate (nat i) (default_val T)))"
    and hconf: "P \<turnstile> hp (h, l) \<surd>" by fact+
  have wt: "P,E,hp (h, l) \<turnstile>1 newA T\<lfloor>Val (Intg i)\<rceil> : T'" by fact
  from new have None: "h a = None" by(rule new_Addr_SomeD)
  moreover from wt have "is_type P T" by(auto)
  hence "P,h \<turnstile> (Arr T (replicate (nat i) (default_val T))) \<surd>"
    by -(rule oconf_init_arr)
  ultimately show "P \<turnstile> hp (h', l) \<surd>" using h' hconf by(simp)(rule hconf_new)
next
  case (Red1AAss h a T el i w U h' l T' E)
  let ?el' = "el[nat i := w]"
  have hconf: "P \<turnstile> hp (h, l) \<surd>" and ha: "h a = Some(Arr T el)"
    and "0 \<le> i" and "i < int (length el)"
    and "typeof\<^bsub>h\<^esub> w = \<lfloor>U\<rfloor>" and "P \<turnstile> U \<le> T"
    and h': "h' = h(a \<mapsto> Arr T (el[nat i := w]))"
    and wt: "P,E,hp (h,l) \<turnstile>1 addr a\<lfloor>Val (Intg i)\<rceil> := Val w : T'"  by fact+
  have "P,h \<turnstile> (Arr T ?el') \<surd>"
  proof (rule oconf_fupd_arr)
    from `typeof\<^bsub>h\<^esub> w = \<lfloor>U\<rfloor>` `P \<turnstile> U \<le> T` show "P,h \<turnstile> w :\<le> T" by (simp add: conf_def)
  next
    from `h a = \<lfloor>Arr T el\<rfloor>` `P \<turnstile> hp (h, l) \<surd>`
    show "P,h \<turnstile> Arr T el \<surd>" by (simp add: hconf_def)
  qed
  with hconf ha h' have "P \<turnstile> h(a\<mapsto>(Arr T (el[nat i := w]))) \<surd>" by - (rule hconf_upd_arr, auto)
  with h' show ?case by(simp del: fun_upd_apply)
next
  case (Red1FAss h a C fs F D v l T E)
  let ?fs' = "fs((F,D)\<mapsto>v)"
  have hconf: "P \<turnstile> hp(h, l) \<surd>" and ha: "h a = Some(Obj C fs)"
   and wt: "P,E,hp (h, l) \<turnstile>1 addr a\<bullet>F{D}:=Val v : T" by fact+
  from wt ha obtain TF Tv where typeofv: "typeof\<^bsub>h\<^esub> v = Some Tv"
    and has: "P \<turnstile> C has F:TF in D"
    and sub: "P \<turnstile> Tv \<le> TF" by auto
  have "P,h \<turnstile> (Obj C ?fs') \<surd>"
  proof (rule oconf_fupd[OF has])
    show "P,h \<turnstile> (Obj C fs) \<surd>" using hconf ha by(simp add:hconf_def)
    show "P,h \<turnstile> v :\<le> TF" using sub typeofv by(simp add:conf_def)
  qed
  with hconf ha show ?case by(simp del: fun_upd_apply)(rule hconf_upd_obj)
next
  case Red1CallExternal
  thus ?case by(auto split: heapobj.split_asm dest: external_call_hconf)
qed auto

lemma sqUn_lem2: "A \<sqsubseteq> A' \<Longrightarrow> B \<squnion> A \<sqsubseteq> B \<squnion> A'"
by(simp add:hyperset_defs) blast

lemma lconf1_upd:
  "\<lbrakk>P,h,A \<turnstile>1 xs (:\<le>) E; P,h \<turnstile> v :\<le> E ! V; V < length xs; V < length E \<rbrakk>
  \<Longrightarrow> P,h,insert V A \<turnstile>1 xs[V := v] (:\<le>) E"
apply(auto simp add:lconf1_def)
apply(case_tac "i = V")
apply(auto)
done

lemma lconf1_upd2 [simp]:
  "i \<ge> length E \<Longrightarrow> P,h,A \<turnstile>1 xs[i := v] (:\<le>) E \<longleftrightarrow> P,h,A \<turnstile>1 xs (:\<le>) E"
apply(auto simp add: lconf1_def)
done

lemma lconf1_append:
  "P,h,A \<turnstile>1 xs (:\<le>) E \<Longrightarrow> P,h,A \<turnstile>1 xs (:\<le>) E @ E'"
by(auto simp add: lconf1_def nth_append)

lemma env_exps_map_Val[simp]: "env_exps (map Val vs) = []"
apply(induct vs, auto)
done

lemma lconf1_subset_mono:
  "\<lbrakk> P,h,A \<turnstile>1 xs (:\<le>) E; A' \<subseteq> A \<rbrakk> \<Longrightarrow> P,h,A' \<turnstile>1 xs (:\<le>) E"
apply(auto simp add: lconf1_def)
done

lemma [simp]: "env_exps (map Val vs @ es) = env_exps es"
apply(induct vs, auto)
done

lemma env_exp_extRet2J [simp]: "env_exp (extRet2J va) = []"
by(cases va) simp_all

lemma \<D>1_extRet2J [simp]: "\<D>1 n (extRet2J va) A"
by(cases va) simp_all


theorem red1_preserves_lconf_defass:
  "\<lbrakk> P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; P,E,hp s \<turnstile>1 e:T;
     P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e;
     \<D>1 (length E) e \<lfloor>A\<rfloor>; \<B> e (length E) \<rbrakk>
  \<Longrightarrow> \<exists>A'. P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exp e' \<and> 
          \<D>1 (length E) e' \<lfloor>A'\<rfloor> \<and>
          \<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e' \<and> A \<inter> {0..<length E} \<subseteq> A'"
  (is "?red e s ta e' s' \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?concl e e' s' E A")
  
  and reds_preserves_lconf:
  "\<lbrakk> P \<turnstile>1 \<langle>es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>; P,E,hp s \<turnstile>1 es [:] Ts;
     P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exps es;
     \<D>s1 (length E) es \<lfloor>A\<rfloor>; \<B>s es (length E) \<rbrakk>
  \<Longrightarrow> \<exists>A'. P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exps es' \<and>
           \<D>s1 (length E) es' \<lfloor>A'\<rfloor> \<and>
           \<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>s1 es \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>s1 es' \<and> A \<inter> {0..<length E} \<subseteq> A'"
  (is "?reds es s ta es' s' \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?concls es es' s' E A")
proof(induct arbitrary: T E A and Ts E A rule: red1_reds1.inducts)
  case (Red1New h a C FDTs h' xs)
  from `new_Addr h = \<lfloor>a\<rfloor>` have "h a = None" by(rule new_Addr_SomeD)
  with `h' = h(a \<mapsto> Obj C (init_fields FDTs))`
  have "hext h h'" by(auto intro: hext_new simp del: fun_upd_apply)
  with `P,hp (h, xs),A \<turnstile>1 lcl (h, xs) (:\<le>) E @ env_exp (new C)`
  have "P,h',A \<turnstile>1 xs (:\<le>) E" by(auto simp add: lconf1_def dest: bspec intro: conf_hext)
  thus ?case by auto
next
  case Red1NewFail thus ?case by fastsimp
next
  case New1ArrayRed thus ?case
    by(fastsimp simp add: hyper_insert_comm intro: sqUn_lem2)
next
  case (Red1NewArray h a i h' T' xs)
  from `new_Addr h = \<lfloor>a\<rfloor>` have "h a = None" by(rule new_Addr_SomeD)
  with `h' = h(a \<mapsto> Arr T' (replicate (nat i) (default_val T')))`
  have "hext h h'" by(auto intro: hext_new simp del: fun_upd_apply)
  with `P,hp (h, xs),A \<turnstile>1 lcl (h, xs) (:\<le>) E @ env_exp (newA T'\<lfloor>Val (Intg i)\<rceil>)`
  have "P,h',A \<turnstile>1 xs (:\<le>) E" by(auto simp add: lconf1_def dest: bspec intro: conf_hext)
  thus ?case by auto
next
  case Red1NewArrayFail thus ?case by auto
next
  case Red1NewArrayNegative thus ?case by auto
next
  case Cast1Red thus ?case
    by(fastsimp simp add: hyper_insert_comm intro: sqUn_lem2)
next
  case Red1Cast thus ?case by auto
next
  case Red1CastFail thus ?case by auto
next
  case (Bin1OpRed1 e s ta e' s' bop e2)
  note IH = `\<And>T E A. \<lbrakk>P,E,hp s \<turnstile>1 e : T; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e; \<D>1 (length E) e \<lfloor>A\<rfloor>; \<B> e (length E)\<rbrakk>
             \<Longrightarrow> ?concl e e' s' E A`
  from `P,E,hp s \<turnstile>1 e \<guillemotleft>bop\<guillemotright> e2 : T` obtain T1 T2
    where wt1: "P,E,hp s \<turnstile>1 e : T1" and wt2: "P,E,hp s \<turnstile>1 e2 : T2" by auto
  from `P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>` have "\<not> is_val e" by auto
  with `\<D>1 (length E) (e \<guillemotleft>bop\<guillemotright> e2) \<lfloor>A\<rfloor>` have D1: "\<D>1 (length E) e \<lfloor>A\<rfloor>"
    and D2: "\<D>1 (length E) e2 (\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e)" by auto
  from `\<not> is_val e` `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (e \<guillemotleft>bop\<guillemotright> e2)`
  have "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by simp
  from IH[OF wt1 this D1] `\<B> (e \<guillemotleft>bop\<guillemotright> e2) (length E)`
  obtain A' where lconf': "P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exp e'"
    and D1': "\<D>1 (length E) e' \<lfloor>A'\<rfloor>" 
    and subs: "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e'"
    and inters: "A \<inter> {0..<length E} \<subseteq> A'" by auto
  from subs have subs2: "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 (e \<guillemotleft>bop\<guillemotright> e2) \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 (e' \<guillemotleft>bop\<guillemotright> e2)"
    by(auto simp add: hyperUn_assoc[symmetric] intro: sqUn_lem)
  moreover from D1' D2 subs have D': "\<D>1 (length E) (e' \<guillemotleft>bop\<guillemotright> e2) \<lfloor>A'\<rfloor>" by(auto intro: D1_mono')
  moreover from lconf' have "P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exp (e' \<guillemotleft>bop\<guillemotright> e2)"
    by(cases "is_val e'")(auto intro: lconf1_append)
  ultimately show ?case using inters by auto
next
  case Bin1OpRed2
  thus ?case by fastsimp
next
  case Red1BinOp thus ?case by fastsimp
next
  case Red1Var thus ?case by fastsimp
next
  case LAss1Red thus ?case
    by(fastsimp simp add: hyper_insert_comm intro: sqUn_lem2)
next
  case (Red1LAss V xs v h)
  from `P,E,hp (h, xs) \<turnstile>1 V:=Val v : T`
  have "P,h \<turnstile> v :\<le> E ! V" "V < length E" by(auto simp add: conf_def)
  moreover with `P,hp (h, xs),A \<turnstile>1 lcl (h, xs) (:\<le>) E @ env_exp (V:=Val v)` `V < length xs`
  have "P,h,insert V A \<turnstile>1 xs[V := v] (:\<le>) E @ env_exp unit" by(auto intro: lconf1_upd)
  ultimately show ?case by fastsimp
next
  case (AAcc1Red1 a s ta a' s' i)
  note IH = `\<And>T E A. \<lbrakk>P,E,hp s \<turnstile>1 a : T; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp a; \<D>1 (length E) a \<lfloor>A\<rfloor>; \<B> a (length E)\<rbrakk>
             \<Longrightarrow> ?concl a a' s' E A`
  from `P,E,hp s \<turnstile>1 a\<lfloor>i\<rceil> : T` obtain T1 T2
    where wt1: "P,E,hp s \<turnstile>1 a : T1" and wt2: "P,E,hp s \<turnstile>1 i : T2" by auto
  from `P \<turnstile>1 \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>` have a: "\<not> is_val a" by auto
  with `\<D>1 (length E) (a\<lfloor>i\<rceil>) \<lfloor>A\<rfloor>` have D1: "\<D>1 (length E) a \<lfloor>A\<rfloor>"
    and D2: "\<D>1 (length E) i (\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 a)" by auto
  from a `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (a\<lfloor>i\<rceil>)`
  have "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp a" by simp
  from IH[OF wt1 this D1] `\<B> (a\<lfloor>i\<rceil>) (length E)`
  obtain A' where lconf': "P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exp a'"
    and D1': "\<D>1 (length E) a' \<lfloor>A'\<rfloor>" 
    and subs: "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 a \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 a'"
    and inters: "A \<inter> {0..<length E} \<subseteq> A'" by auto
  from subs have subs2: "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 (a\<lfloor>i\<rceil>) \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 (a'\<lfloor>i\<rceil>)"
    by(auto simp add: hyperUn_assoc[symmetric] intro: sqUn_lem)
  moreover from D1' D2 subs have D': "\<D>1 (length E) (a'\<lfloor>i\<rceil>) \<lfloor>A'\<rfloor>" by(auto intro: D1_mono')
  moreover from lconf' have "P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exp (a'\<lfloor>i\<rceil>)"
    by(cases "is_val a'")(auto intro: lconf1_append)
  ultimately show ?case using inters by auto
next
  case AAcc1Red2 thus ?case by auto
next
  case Red1AAcc thus ?case by auto
next
  case Red1AAccNull thus ?case by auto
next
  case Red1AAccBounds thus ?case by auto
next
  case (AAss1Red1 a s ta a' s' i e)
  note IH = `\<And>T E A. \<lbrakk>P,E,hp s \<turnstile>1 a : T; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp a; \<D>1 (length E) a \<lfloor>A\<rfloor>; \<B> a (length E)\<rbrakk>
             \<Longrightarrow> ?concl a a' s' E A`
  from `P,E,hp s \<turnstile>1 a\<lfloor>i\<rceil> := e : T` obtain T1 T2 T3
    where wt1: "P,E,hp s \<turnstile>1 a : T1" and wt2: "P,E,hp s \<turnstile>1 i : T2" and wt3: "P,E,hp s \<turnstile>1 e : T3" by auto
  from `P \<turnstile>1 \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>` have a: "\<not> is_val a" by auto
  with `\<D>1 (length E) (a\<lfloor>i\<rceil> := e) \<lfloor>A\<rfloor>` have D1: "\<D>1 (length E) a \<lfloor>A\<rfloor>"
    and D2: "\<D>1 (length E) i (\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 a)" 
    and D3: "\<D>1 (length E) e (\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 a \<squnion> \<A>1 i)" by auto
  from a `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (a\<lfloor>i\<rceil> := e)`
  have "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp a" by simp
  from IH[OF wt1 this D1] `\<B> (a\<lfloor>i\<rceil> := e) (length E)`
  obtain A' where lconf': "P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exp a'"
    and D1': "\<D>1 (length E) a' \<lfloor>A'\<rfloor>" 
    and subs: "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 a \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 a'"
    and inters: "A \<inter> {0..<length E} \<subseteq> A'" by auto
  from subs have "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 (a\<lfloor>i\<rceil> := e) \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 (a'\<lfloor>i\<rceil> := e)"
    by(auto simp add: hyperUn_assoc[symmetric] intro: sqUn_lem)
  moreover from D1' D2 D3 subs a have D': "\<D>1 (length E) (a'\<lfloor>i\<rceil> := e) \<lfloor>A'\<rfloor>" by(auto elim!: D1_mono' intro: sqUn_lem)
  moreover from lconf' have "P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exp (a'\<lfloor>i\<rceil> := e)"
    by(cases "is_val a'")(auto intro: lconf1_append)
  ultimately show ?case using inters by auto
next
  case (AAss1Red2 i s ta i' s' a e)
  note IH = `\<And>T E A. \<lbrakk>P,E,hp s \<turnstile>1 i : T; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp i; \<D>1 (length E) i \<lfloor>A\<rfloor>; \<B> i (length E)\<rbrakk>
             \<Longrightarrow> ?concl i i' s' E A`
  from `P,E,hp s \<turnstile>1 Val a\<lfloor>i\<rceil> := e : T` obtain T1 T2 T3
    where wt1: "P,E,hp s \<turnstile>1 Val a : T1" and wt2: "P,E,hp s \<turnstile>1 i : T2" and wt3: "P,E,hp s \<turnstile>1 e : T3" by auto
  from `P \<turnstile>1 \<langle>i,s\<rangle> -ta\<rightarrow> \<langle>i',s'\<rangle>` have i: "\<not> is_val i" by auto
  with `\<D>1 (length E) (Val a\<lfloor>i\<rceil> := e) \<lfloor>A\<rfloor>` have D1: "\<D>1 (length E) i \<lfloor>A\<rfloor>"
    and D2: "\<D>1 (length E) e (\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 i)" by auto
  from i `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (Val a\<lfloor>i\<rceil> := e)`
  have "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp i" by simp
  from IH[OF wt2 this D1] `\<B> (Val a\<lfloor>i\<rceil> := e) (length E)`
  obtain A' where lconf': "P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exp i'"
    and D1': "\<D>1 (length E) i' \<lfloor>A'\<rfloor>" 
    and subs: "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 i \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 i'"
    and inters: "A \<inter> {0..<length E} \<subseteq> A'" by auto
  from subs have subs2: "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 (Val a\<lfloor>i\<rceil> := e) \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 (Val a\<lfloor>i'\<rceil> := e)"
    by(auto simp add: hyperUn_assoc[symmetric] intro: sqUn_lem)
  moreover from D1' D2 subs have D': "\<D>1 (length E) (Val a\<lfloor>i'\<rceil> := e) \<lfloor>A'\<rfloor>" by(auto intro: D1_mono')
  moreover from lconf' have "P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exp (Val a\<lfloor>i'\<rceil> := e)"
    by(auto intro: lconf1_append)
  ultimately show ?case using inters by auto
next
  case AAss1Red3 thus ?case by fastsimp
next
  case Red1AAssNull thus ?case by auto
next
  case Red1AAssBounds thus ?case by auto
next
  case Red1AAssStore thus ?case by auto
next
  case (Red1AAss h a T' el i w U h' l)
  from `h a = \<lfloor>Arr T' el\<rfloor>` `h' = h(a \<mapsto> Arr T' (el[nat i := w]))`
  have "hext h h'" by(auto intro: hext_upd_arr)
  with `P,hp (h, l),A \<turnstile>1 lcl (h, l) (:\<le>) E @ env_exp (addr a\<lfloor>Val (Intg i)\<rceil> := Val w)`
  have "P, h',A \<turnstile>1 l (:\<le>) E @ env_exp (addr a\<lfloor>Val (Intg i)\<rceil> := Val w)"
    by(auto simp add: lconf1_def dest: bspec intro: conf_hext)
  thus ?case by auto
next
  case ALength1Red thus ?case by fastsimp
next
  case Red1ALength thus ?case by auto
next
  case Red1ALengthNull thus ?case by auto
next
  case FAcc1Red thus ?case by auto
next
  case Red1FAcc thus ?case by auto
next
  case Red1FAccNull thus ?case by auto
next
  case (FAss1Red1 e s ta e' s' F D e2)
  note IH = `\<And>T E A. \<lbrakk>P,E,hp s \<turnstile>1 e : T; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e; \<D>1 (length E) e \<lfloor>A\<rfloor>; \<B> e (length E)\<rbrakk>
             \<Longrightarrow> ?concl e e' s' E A`
  from `P,E,hp s \<turnstile>1 e\<bullet>F{D} := e2 : T` obtain T1 T2
    where wt1: "P,E,hp s \<turnstile>1 e : T1" and wt2: "P,E,hp s \<turnstile>1 e2 : T2" by auto
  from `P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>` have "\<not> is_val e" by auto
  with `\<D>1 (length E) (e\<bullet>F{D} := e2) \<lfloor>A\<rfloor>` have D1: "\<D>1 (length E) e \<lfloor>A\<rfloor>"
    and D2: "\<D>1 (length E) e2 (\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e)" by auto
  from `\<not> is_val e` `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (e\<bullet>F{D} := e2)`
  have "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by simp
  from IH[OF wt1 this D1] `\<B> (e\<bullet>F{D} := e2) (length E)`
  obtain A' where lconf': "P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exp e'"
    and D1': "\<D>1 (length E) e' \<lfloor>A'\<rfloor>" 
    and subs: "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e'"
    and inters: "A \<inter> {0..<length E} \<subseteq> A'" by auto
  from subs have subs2: "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 (e\<bullet>F{D} := e2) \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 (e'\<bullet>F{D} := e2)"
    by(auto simp add: hyperUn_assoc[symmetric] intro: sqUn_lem)
  moreover from D1' D2 subs have D': "\<D>1 (length E) (e'\<bullet>F{D} := e2) \<lfloor>A'\<rfloor>" by(auto intro: D1_mono')
  moreover from lconf' have "P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exp (e'\<bullet>F{D} := e2)"
    by(cases "is_val e'")(auto intro: lconf1_append)
  ultimately show ?case using inters by auto
next
  case FAss1Red2 thus ?case by auto
next
  case (Red1FAss h a C fs F D v l)
  from `h a = \<lfloor>Obj C fs\<rfloor>` have "hext h (h(a \<mapsto> Obj C (fs((F, D) \<mapsto> v))))" by(rule hext_upd_obj)
  with `P,hp (h, l),A \<turnstile>1 lcl (h, l) (:\<le>) E @ env_exp (addr a\<bullet>F{D} := Val v)`
  have "P,h(a \<mapsto> Obj C (fs((F, D) \<mapsto> v))),A \<turnstile>1 l (:\<le>) E @ env_exp (addr a\<bullet>F{D} := Val v)"
    by(auto simp add: lconf1_def dest: bspec intro: conf_hext)
  thus ?case by(auto simp del: fun_upd_apply)
next
  case Red1FAssNull thus ?case by auto
next
  case Call1Obj thus ?case
    by(fastsimp intro: Ds1_mono' sqUn_lem lconf1_append simp add: hyperUn_assoc[symmetric] split: split_if_asm)
next
  case Call1Params thus ?case by fastsimp
next
  case (Red1CallExternal s a Ta M vs ta va h' ta' e' s')
  from `P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>` have "hext (hp s) h'" by(rule red_external_hext)
  with `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (addr a\<bullet>M(map Val vs))` have "P,h',A \<turnstile>1 lcl s (:\<le>) E"
    by(auto intro: lconf1_hext_mono)
  thus ?case using `e' = extRet2J va` `s' = (h', lcl s)` by(auto simp add: hyperset_defs)
next
  case Red1CallNull thus ?case by fastsimp
next
  case Block1RedNone thus ?case by(fastsimp simp add: hyperset_defs)
next
  case (Block1RedSome e h xs V v ta e' h' xs' Tv cr Te E A)
  note IH = `\<And>T E A. \<lbrakk>P,E,hp (h, xs[V := v]) \<turnstile>1 e : T; P,hp (h, xs[V := v]),A \<turnstile>1 lcl (h, xs[V := v]) (:\<le>) E @ env_exp e; \<D>1 (length E) e \<lfloor>A\<rfloor>; \<B> e (length E)\<rbrakk>
             \<Longrightarrow> ?concl e e' (h', xs') E A`
  from `\<B> {V:Tv=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub> (length E)` have [simp]: "V = length E" by simp
  from `P,E,hp (h, xs) \<turnstile>1 {V:Tv=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub> : Te` have wte: "P,(E @ [Tv]),hp (h, xs[V := v]) \<turnstile>1 e : Te" 
    and conf: "P,h \<turnstile> v :\<le> Tv" by(auto simp add: conf_def)
  from `P,hp (h, xs),A \<turnstile>1 lcl (h, xs) (:\<le>) E @ env_exp {V:Tv=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub>` `V < length xs` conf
  have "P,hp (h, xs[V := v]),insert V A \<turnstile>1 lcl (h, xs[V := v]) (:\<le>) (E @ [Tv]) @ env_exp e"
    by(auto intro: lconf1_upd)
  from IH[OF wte this] `\<D>1 (length E) {V:Tv=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub> \<lfloor>A\<rfloor>` `\<B> {V:Tv=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub> (length E)`
  obtain A' where lconf': "P,h',A' \<turnstile>1 xs' (:\<le>) (E @ [Tv]) @ env_exp e'"
    and De': "\<D>1 (length (E @ [Tv])) e' \<lfloor>A'\<rfloor>"
    and sub1: "\<lfloor>insert V A \<inter> {0..<length (E @ [Tv])}\<rfloor> \<squnion> \<A>1 e \<sqsubseteq> \<lfloor>A' \<inter> {0..<length (E @ [Tv])}\<rfloor> \<squnion> \<A>1 e'"
    and sub2: "insert V A \<inter> {0..<length (E @ [Tv])} \<subseteq> A'" by auto
  show ?case unfolding hp_conv lcl_conv conj_assoc[symmetric] 
  proof(rule exI conjI)+
    from lconf' show "P,h',A' \<turnstile>1 xs' (:\<le>) E @ env_exp {V:Tv=None; e'}\<^bsub>cr\<^esub>" by simp
  next
    from De' show "\<D>1 (length E) {V:Tv=None; e'}\<^bsub>cr\<^esub> \<lfloor>A'\<rfloor>" by simp
  next
    from sub1 show "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 {V:Tv=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub> \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 {V:Tv=None; e'}\<^bsub>cr\<^esub>"
      by(fastsimp simp add: hyperset_defs)
  next
    from sub2 show "A \<inter> {0..<length E} \<subseteq> A'" by(auto)
  qed
next
  case (Red1BlockNone V s Tv u cr Te E A)
  from `\<B> {V:Tv=None; Val u}\<^bsub>cr\<^esub> (length E)` have [simp]: "V = length E" by simp
  show ?case unfolding conj_assoc[symmetric]
  proof(rule exI conjI)+
    from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp {V:Tv=None; Val u}\<^bsub>cr\<^esub>`
    show "P,hp s,A - {V} \<turnstile>1 lcl s (:\<le>) E @ env_exp (Val u)"
      by(auto simp add: lconf1_def nth_append)
  qed auto
next
  case (Red1BlockSome V xs Tv v u cr h Te E A)
  from `\<B> {V:Tv=\<lfloor>v\<rfloor>; Val u}\<^bsub>cr\<^esub> (length E)` have [simp]: "V = length E" by simp
  show ?case unfolding conj_assoc[symmetric] hp_conv lcl_conv
  proof(rule exI conjI)+
    from `P,hp (h, xs),A \<turnstile>1 lcl (h, xs) (:\<le>) E @ env_exp {V:Tv=\<lfloor>v\<rfloor>; Val u}\<^bsub>cr\<^esub>`
    show "P,h,A - {V} \<turnstile>1 xs[V := v] (:\<le>) E @ env_exp (Val u)"
      by(auto simp add: lconf1_def nth_append)
  qed auto
next
  case (Synchronized1Red1 e s ta e' s' V e2)
  note IH = `\<And>T E A. \<lbrakk>P,E,hp s \<turnstile>1 e : T; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e; \<D>1 (length E) e \<lfloor>A\<rfloor>; \<B> e (length E)\<rbrakk>
             \<Longrightarrow> ?concl e e' s' E A`
  from `\<B> (sync\<^bsub>V\<^esub> (e) e2) (length E)` have [simp]: "V = length E" by simp
  from `\<D>1 (length E) (sync\<^bsub>V\<^esub> (e) e2) \<lfloor>A\<rfloor>` have D1: "\<D>1 (length E) e \<lfloor>A\<rfloor>" 
    and D2: "\<D>1 (Suc (length E)) e2 (\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e)" by auto
  from `P,E,hp s \<turnstile>1 sync\<^bsub>V\<^esub> (e) e2 : T` obtain Te where wte: "P,E,hp s \<turnstile>1 e : Te" by auto
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (sync\<^bsub>V\<^esub> (e) e2)`
  have "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by simp
  from IH[OF wte this D1] `\<B> (sync\<^bsub>V\<^esub> (e) e2) (length E)`
  obtain A' where lconf': "P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exp e'"
    and D1': "\<D>1 (length E) e' \<lfloor>A'\<rfloor>"
    and sub1: "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e'"
    and sub2: "A \<inter> {0..<length E} \<subseteq> A'" by auto
  show ?case unfolding conj_assoc[symmetric]
  proof(rule exI conjI)+
    from lconf' show "P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exp (sync\<^bsub>V\<^esub> (e') e2)" by simp
  next
    from sub1 D1' D2 show "\<D>1 (length E) (sync\<^bsub>V\<^esub> (e') e2) \<lfloor>A'\<rfloor>" by(auto intro: D1_mono')
  next
    from sub1 show "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 (sync\<^bsub>V\<^esub> (e) e2) \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 (sync\<^bsub>V\<^esub> (e') e2)"
      by(auto simp add: hyperUn_assoc[symmetric] intro: sqUn_lem)
  next
    from sub2 show "A \<inter> {0..<length E} \<subseteq> A'" .
  qed
next
  case Synchronized1Null thus ?case by fastsimp
next
  case (Lock1Synchronized h a arrobj  V xs e)
  from `\<B> (sync\<^bsub>V\<^esub> (addr a) e) (length E)` have [simp]: "V = length E" by simp
  from `V < length xs` `P,hp (h, xs),A \<turnstile>1 lcl (h, xs) (:\<le>) E @ env_exp (sync\<^bsub>V\<^esub> (addr a) e)`
  have "P,h,A \<inter> {0..<length E} \<turnstile>1 xs[length E := Addr a] (:\<le>) (E @ [Class Object]) @ env_exp e"
    by(auto simp add: lconf1_def nth_append)
  thus ?case using `\<D>1 (length E) (sync\<^bsub>V\<^esub> (addr a) e) \<lfloor>A\<rfloor>`
    by(auto simp add: Int_assoc)
next
  case (Synchronized1Red2 e s ta e' s' V a)
  note IH = `\<And>T E A. \<lbrakk>P,E,hp s \<turnstile>1 e : T; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e; \<D>1 (length E) e \<lfloor>A\<rfloor>; \<B> e (length E)\<rbrakk>
             \<Longrightarrow> ?concl e e' s' E A`
  from `\<B> (insync\<^bsub>V\<^esub> (a) e) (length E)` have B: "\<B> e (Suc (length E))" and [simp]: "V = length E" by auto
  from `P,E,hp s \<turnstile>1 insync\<^bsub>V\<^esub> (a) e : T` obtain T'
    where wte: "P,(E@[Class Object]),hp s \<turnstile>1 e : T" and wta: "P,E,hp s \<turnstile>1 addr a : T'" by auto
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (insync\<^bsub>V\<^esub> (a) e)`
  have "P,hp s,A \<turnstile>1 lcl s (:\<le>) (E @ [Class Object]) @ env_exp e" by simp
  from IH[OF wte this] `\<D>1 (length E) (insync\<^bsub>V\<^esub> (a) e) \<lfloor>A\<rfloor>` `\<B> (insync\<^bsub>V\<^esub> (a) e) (length E)`
  obtain A' where lconf': "P,hp s',A' \<turnstile>1 lcl s' (:\<le>) (E @ [Class Object]) @ env_exp e'"
    and De': "\<D>1 (length (E @ [Class Object])) e' \<lfloor>A'\<rfloor>"
    and subs1: "\<lfloor>A \<inter> {0..<Suc (length E)}\<rfloor> \<squnion> \<A>1 e \<sqsubseteq> \<lfloor>A' \<inter> {0..<Suc (length E)}\<rfloor> \<squnion> \<A>1 e'"
    and subs2: "A \<inter> {0..<Suc (length E)} \<subseteq> A'" by auto
  from subs1 have "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> (\<A>1 e \<ominus> length E) \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> (\<A>1 e' \<ominus> length E )"
    by(fastsimp simp add: hyperset_defs)
  thus ?case using lconf' De' subs2 by fastsimp
next
  case (Unlock1Synchronized xs V a' a v h)
  thus ?case 
    by -(rule_tac x="A \<inter> {0..<length E}" in exI, auto simp add: lconf1_def nth_append)
next
  case Seq1Red thus ?case
    by(fastsimp simp add: hyperUn_assoc[symmetric] intro: sqUn_lem D1_mono')
next
  case (Red1Seq v e s) thus ?case
    by -(rule_tac x="A \<inter> {0..<length E}" in exI, fastsimp simp add: lconf1_def hyperset_defs nth_append)
next
  case (Cond1Red b s ta b' s' e1 e2)
  note IH = `\<And>T E A. \<lbrakk>P,E,hp s \<turnstile>1 b : T; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp b; \<D>1 (length E) b \<lfloor>A\<rfloor>; \<B> b (length E)\<rbrakk>
             \<Longrightarrow> ?concl b b' s' E A`
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (if (b) e1 else e2)`
  have lconfb: "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp b" by simp
  from `\<D>1 (length E) (if (b) e1 else e2) \<lfloor>A\<rfloor>`
  have Db: "\<D>1 (length E) b \<lfloor>A\<rfloor>" and D1: "\<D>1 (length E) e1 (\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 b)"
    and D2: "\<D>1 (length E) e2 (\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 b)" by auto
  from `P,E,hp s \<turnstile>1 if (b) e1 else e2 : T` have "P,E,hp s \<turnstile>1 b : Boolean" by auto
  from IH[OF this lconfb Db] `\<B> (if (b) e1 else e2) (length E)`
  obtain A' where lconf': "P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exp b'"
    and Db': "\<D>1 (length E) b' \<lfloor>A'\<rfloor>"
    and subs1: "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 b \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 b'"
    and subs2: "A \<inter> {0..<length E} \<subseteq> A'" by auto
  from D1 D2 Db' subs1 have "\<D>1 (length E) (if (b') e1 else e2) \<lfloor>A'\<rfloor>" by(auto intro: D1_mono')
  with lconf' subs1 subs2 show ?case
    by(fastsimp simp add: hyperUn_assoc[symmetric] intro: sqUn_lem)
next
  case (Red1CondT e1 e2 s)
  note lconf = `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (if (true) e1 else e2)`
  hence "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e1" by(auto intro: lconf1_append)
  moreover from lconf have "A \<subseteq> {0..<length E}" by(auto simp add: lconf1_def)
  moreover have "\<lfloor>A\<rfloor> \<squnion> \<A>1 e1 \<sqinter> \<A>1 e2 \<sqsubseteq> \<lfloor>A\<rfloor> \<squnion> \<A>1 e1" by(auto simp add: hyperset_defs)
  ultimately show ?case using `\<D>1 (length E) (if (true) e1 else e2) \<lfloor>A\<rfloor>` by(auto simp add: Int_absorb2)
next
  case (Red1CondF e1 e2 s)
  note lconf = `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (if (false) e1 else e2)`
  hence "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e2" by(auto intro: lconf1_append)
  moreover from lconf have "A \<subseteq> {0..<length E}" by(auto simp add: lconf1_def)
  moreover have "\<lfloor>A\<rfloor> \<squnion> \<A>1 e1 \<sqinter> \<A>1 e2 \<sqsubseteq> \<lfloor>A\<rfloor> \<squnion> \<A>1 e2" by(auto simp add: hyperset_defs)
  ultimately show ?case using `\<D>1 (length E) (if (false) e1 else e2) \<lfloor>A\<rfloor>` by(auto simp add: Int_absorb2)
next
  case (Red1While b c s)
  note lconf = `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (while (b) c)`
  hence "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (if (b) (c;;while (b) c) else unit)" by(auto intro: lconf1_append)
  moreover from lconf have "A \<subseteq> {0..<length E}" by(auto simp add: lconf1_def)
  ultimately show ?case using `\<D>1 (length E) (while (b) c) \<lfloor>A\<rfloor>` `\<B> (while (b) c) (length E)`
    by(auto intro: D1_mono' simp add: hyperset_defs)
next
  case Throw1Red thus ?case by fastsimp
next
  case Red1ThrowNull thus ?case by fastsimp
next
  case (Try1Red e s ta e' s' C V e2)
  note IH = `\<And>T E A. \<lbrakk>P,E,hp s \<turnstile>1 e : T; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e; \<D>1 (length E) e \<lfloor>A\<rfloor>; \<B> e (length E)\<rbrakk>
             \<Longrightarrow> ?concl e e' s' E A`
  note B = `\<B> (try e catch(C V) e2) (length E)`
  hence [simp]: "V = length E" by simp
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (try e catch(C V) e2)`
  have lconfe: "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by simp
  from `\<D>1 (length E) (try e catch(C V) e2) \<lfloor>A\<rfloor>`
  have D1: "\<D>1 (length E) e \<lfloor>A\<rfloor>" and D2: "\<D>1 (Suc (length E)) e2 (\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<lfloor>{V}\<rfloor>)" by auto
  from `P,E,hp s \<turnstile>1 try e catch(C V) e2 : T` obtain U where "P,E,hp s \<turnstile>1 e : U" by auto
  from IH[OF this lconfe D1] B
  obtain A' where lconf': "P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exp e'"
    and D1': "\<D>1 (length E) e' \<lfloor>A'\<rfloor>"
    and subs1: "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e'"
    and subs2: "A \<inter> {0..<length E} \<subseteq> A'" by auto
  from D2 D1' subs2 have "\<D>1 (length E) (try e' catch(C V) e2) \<lfloor>A'\<rfloor>" by(auto intro: D1_mono')
  thus ?case using lconf' subs1 subs2 by(auto simp add: hyperset_defs)
next
  case Red1Try thus ?case by(auto simp add: hyperset_defs)
next
  case (Red1TryCatch h a D fs C V x e2)
  from `\<B> (try Throw a catch(C V) e2) (length E)` have [simp]: "V = length E" by simp
  from `P,hp (h, x),A \<turnstile>1 lcl (h, x) (:\<le>) E @ env_exp (try Throw a catch(C V) e2)`
    `V < length x` `h a = \<lfloor>Obj D fs\<rfloor>` `P \<turnstile> D \<preceq>\<^sup>* C`
  have "P,h,insert (length E) (A \<inter> {0..<length E}) \<turnstile>1 x[length E := Addr a] (:\<le>) E @ Class C # env_exp e2"
    by(auto simp add: lconf1_def conf_def nth_append)
  with `\<D>1 (length E) (try Throw a catch(C V) e2) \<lfloor>A\<rfloor>` show ?case
    by(auto simp add: hyperset_defs)
next
  case Red1TryFail thus ?case by(auto simp add: hyperset_defs)
next
  case (List1Red1 e s ta e' s' es)
  note IH = `\<And>T E A. \<lbrakk>P,E,hp s \<turnstile>1 e : T; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e; \<D>1 (length E) e \<lfloor>A\<rfloor>; \<B> e (length E)\<rbrakk>
             \<Longrightarrow> ?concl e e' s' E A`
  from `P,E,hp s \<turnstile>1 e # es [:] Ts` obtain Te Tes
    where wte: "P,E,hp s \<turnstile>1 e : Te" and wtes: "P,E,hp s \<turnstile>1 es [:] Tes" by auto
  from `P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>` have "\<not> is_val e" by auto
  with `\<D>s1 (length E) (e # es) \<lfloor>A\<rfloor>` have D1: "\<D>1 (length E) e \<lfloor>A\<rfloor>"
    and Des: "\<D>s1 (length E) es (\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e)" by auto
  from `\<not> is_val e` `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exps (e # es)`
  have "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by simp
  from IH[OF wte this D1] `\<B>s (e # es) (length E)`
  obtain A' where lconf': "P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exp e'"
    and D1': "\<D>1 (length E) e' \<lfloor>A'\<rfloor>" 
    and subs: "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e'"
    and inters: "A \<inter> {0..<length E} \<subseteq> A'" by auto
  from subs have subs2: "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>s1 (e # es) \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>s1 (e' # es)"
    by(auto simp add: hyperUn_assoc[symmetric] intro: sqUn_lem)
  moreover from D1' Des subs have D': "\<D>s1 (length E) (e' # es) \<lfloor>A'\<rfloor>" by(auto intro: Ds1_mono')
  moreover from lconf' have "P,hp s',A' \<turnstile>1 lcl s' (:\<le>) E @ env_exps (e' # es)"
    by(cases "is_val e'")(auto intro: lconf1_append)
  ultimately show ?case using inters by auto
next
  case List1Red2 thus ?case by fastsimp
next
  case Bin1OpThrow1 thus ?case by(fastsimp simp add: is_val_iff)
next
  case Bin1OpThrow2 thus ?case by(fastsimp simp add: is_val_iff)
next
  case LAss1Throw thus ?case by(fastsimp simp add: is_val_iff)
next
  case Call1ThrowObj thus ?case by(fastsimp simp add: is_val_iff)
next
  case Call1ThrowParams thus ?case by(fastsimp simp add: is_val_iff)
next
  case (Block1ThrowNone V s Tv a cr Te E A)
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp {V:Tv=None; Throw a}\<^bsub>cr\<^esub>`
  have "P,hp s,A \<inter> {0..<length E} \<turnstile>1 lcl s (:\<le>) E" by(auto simp add: lconf1_def nth_append)
  thus ?case by(auto)
next
  case (Block1ThrowSome V xs Tv v a cr h Te E A)
  from `\<B> {V:Tv=\<lfloor>v\<rfloor>; Throw a}\<^bsub>cr\<^esub> (length E)` have [simp]: "V = length E" by simp
  from `P,hp (h, xs),A \<turnstile>1 lcl (h, xs) (:\<le>) E @ env_exp {V:Tv=\<lfloor>v\<rfloor>; Throw a}\<^bsub>cr\<^esub>` `V < length xs`
  have "P,h,A \<inter> {0..<length E} \<turnstile>1 xs[V := v] (:\<le>) E" by(auto simp add: lconf1_def nth_append)
  thus ?case by(auto)
next
  case Synchronized1Throw1 thus ?case by fastsimp
next
  case (Synchronized1Throw2 xs V a' a ad h)
  from `\<B> (insync\<^bsub>V\<^esub> (a) Throw ad) (length E)` have [simp]: "V = length E" by simp
  from `P,hp (h, xs),A \<turnstile>1 lcl (h, xs) (:\<le>) E @ env_exp (insync\<^bsub>V\<^esub> (a) Throw ad)`
  have "P,h,A \<inter> {0..<length E} \<turnstile>1 xs[V := Addr a'] (:\<le>) E" by(auto simp add: lconf1_def nth_append)
  thus ?case by auto
next
  case Throw1Throw thus ?case by fastsimp
next
  case Seq1Throw thus ?case by fastsimp
next
  case Cond1Throw thus ?case by fastsimp
next
  case (Unlock1SynchronizedNull xs V a v h)
  from `\<B> (insync\<^bsub>V\<^esub> (a) Val v) (length E)` have [simp]: "V = length E" by simp
  from `P,hp (h, xs),A \<turnstile>1 lcl (h, xs) (:\<le>) E @ env_exp (insync\<^bsub>V\<^esub> (a) Val v)`
  have "P,h,A \<inter> {0..<length E} \<turnstile>1 xs (:\<le>) E" by(auto simp add: lconf1_def nth_append)
  thus ?case by auto
next
  case (Unlock1SynchronizedFail xs V a' a v h)
  from `\<B> (insync\<^bsub>V\<^esub> (a) Val v) (length E)` have [simp]: "V = length E" by simp
  from `P,hp (h, xs),A \<turnstile>1 lcl (h, xs) (:\<le>) E @ env_exp (insync\<^bsub>V\<^esub> (a) Val v)`
  have "P,h,A \<inter> {0..<length E} \<turnstile>1 xs (:\<le>) E" by(auto simp add: lconf1_def nth_append)
  thus ?case by auto
next
  case (Synchronized1Throw2Fail xs V a' a ad h)
  from `\<B> (insync\<^bsub>V\<^esub> (a) Throw ad) (length E)` have [simp]: "V = length E" by simp
  from `P,hp (h, xs),A \<turnstile>1 lcl (h, xs) (:\<le>) E @ env_exp (insync\<^bsub>V\<^esub> (a) Throw ad)`
  have "P,h,A \<inter> {0..<length E} \<turnstile>1 xs[V := Addr a'] (:\<le>) E" by(auto simp add: lconf1_def nth_append)
  thus ?case by auto
next
  case (Synchronized1Throw2Null xs V a ad h)
  from `\<B> (insync\<^bsub>V\<^esub> (a) Throw ad) (length E)` have [simp]: "V = length E" by simp
  from `P,hp (h, xs),A \<turnstile>1 lcl (h, xs) (:\<le>) E @ env_exp (insync\<^bsub>V\<^esub> (a) Throw ad)`
  have "P,h,A \<inter> {0..<length E} \<turnstile>1 xs[V := Addr a'] (:\<le>) E" by(auto simp add: lconf1_def nth_append)
  thus ?case by auto
next
  case New1ArrayThrow thus ?case by auto
next
  case Cast1Throw thus ?case by auto
next
  case (AAcc1Throw1 a i s)
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (Throw a\<lfloor>i\<rceil>)`
  have "P,hp s,A \<inter> {0..<length E} \<turnstile>1 lcl s (:\<le>) E" by(auto simp add: lconf1_def nth_append)
  thus ?case by(auto)
next
  case AAcc1Throw2 thus ?case by(auto)
next
  case (AAss1Throw1 a i e s)
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (Throw a\<lfloor>i\<rceil> := e)`
  have "P,hp s,A \<inter> {0..<length E} \<turnstile>1 lcl s (:\<le>) E" by(auto simp add: lconf1_def nth_append)
  thus ?case by(auto)
next
  case (AAss1Throw2 v a e s)
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (Val v\<lfloor>Throw a\<rceil> := e)`
  have "P,hp s,A \<inter> {0..<length E} \<turnstile>1 lcl s (:\<le>) E" by(auto simp add: lconf1_def nth_append)
  thus ?case by(auto)
next
  case AAss1Throw3 thus ?case by auto
next
  case ALength1Throw thus ?case by auto
next
  case FAcc1Throw thus ?case by auto
next
  case (FAss1Throw1 a F D e2 s)
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (Throw a\<bullet>F{D} := e2)`
  have "P,hp s,A \<inter> {0..<length E} \<turnstile>1 lcl s (:\<le>) E" by(auto simp add: lconf1_def nth_append)
  thus ?case by(auto)
next
  case FAss1Throw2 thus ?case by auto
qed


lemma wt_external_call: "conf_extRet P h va T \<Longrightarrow> \<exists>T'. P,E,h \<turnstile>1 extRet2J va : T' \<and> P \<turnstile> T' \<le> T"
by(cases va)(auto simp add: conf_def)

theorem assumes wf: "wf_prog wf_md P"
  shows subject_reduction1:
  "\<lbrakk> P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e;
     \<D>1 (length E) e \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 e : T; \<B> e (length E) \<rbrakk>
  \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T"

  and subjects_reduction1:
  "\<lbrakk> P \<turnstile>1 \<langle>es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>; P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exps es;
     \<D>s1 (length E) es \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 es [:] Ts; \<B>s es (length E) \<rbrakk> 
  \<Longrightarrow> \<exists>Ts'. P,E,hp s' \<turnstile>1 es' [:] Ts' \<and> P \<turnstile> Ts' [\<le>] Ts"
proof (induct arbitrary: T E A and Ts E A rule:red1_reds1.inducts)
  case Red1New
  thus ?case by fastsimp
next
  case Red1NewFail thus ?case
    by(fastsimp simp add: hconf_def dest: typeof_OutOfMemory split: heapobj.split_asm intro: xcpt_subcls_Throwable[OF _ wf])
next
  case New1ArrayRed thus ?case by fastsimp
next
  case Red1NewArray thus ?case by fastsimp
next
  case Red1NewArrayNegative thus ?case
    by(fastsimp simp add: hconf_def dest: typeof_NegativeArraySize split: heapobj.split_asm intro: xcpt_subcls_Throwable[OF _ wf])
next
  case Red1NewArrayFail thus ?case
    by(fastsimp simp add: hconf_def dest: typeof_OutOfMemory split: heapobj.split_asm intro: xcpt_subcls_Throwable[OF _ wf])
next
  case Cast1Red thus ?case by fastsimp
next
  case Red1Cast thus ?case by fastsimp
next
  case Red1CastFail thus ?case
    by(fastsimp simp add: hconf_def dest: typeof_ClassCast split: heapobj.split_asm intro: xcpt_subcls_Throwable[OF _ wf])
next
  case (Bin1OpRed1 e s ta e' s' bop e2)
  note red = `P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e;
                      \<D>1 (length E) e \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 e : T; \<B> e (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T`
  note wt = `P,E,hp s \<turnstile>1 e \<guillemotleft>bop\<guillemotright> e2 : T`
  note D = `\<D>1 (length E) (e \<guillemotleft>bop\<guillemotright> e2) \<lfloor>A\<rfloor>`
  from red have nval: "\<not> is_val e" by auto
  with `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (e \<guillemotleft>bop\<guillemotright> e2)`
  have lconfe: "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by auto
  have "P,E,hp s' \<turnstile>1 e' \<guillemotleft>bop\<guillemotright> e2 : T"
  proof (cases bop)
    case Eq
    note Eq[simp]
    from wt obtain T1 T2 where [simp]: "T = Boolean"
      and wt1: "P,E,hp s \<turnstile>1 e : T1" and wt2: "P,E,hp s \<turnstile>1 e2 : T2" by auto
    show ?thesis
      using WTrt1_hext_mono[OF wt2 red1_hext_incr[OF red]] IH[OF `P \<turnstile> hp s \<surd>` lconfe _ wt1]
	D `\<B> (e \<guillemotleft>bop\<guillemotright> e2) (length E)` by auto
  next
    case Add
    note Add[simp]
    from wt have [simp]: "T = Integer" and wt1: "P,E,hp s \<turnstile>1 e : Integer"
      and wt2: "P,E,hp s \<turnstile>1 e2 : Integer" by auto
    show ?thesis 
      using IH[OF `P \<turnstile> hp s \<surd>` lconfe _ wt1] WTrt1_hext_mono[OF wt2 red1_hext_incr[OF red]]
	D `\<B> (e \<guillemotleft>bop\<guillemotright> e2) (length E)` by auto
  qed
  thus ?case by auto
next
  case (Bin1OpRed2 e s ta e' s' v bop)
  note red = `P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e;
                      \<D>1 (length E) e \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 e : T; \<B> e (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T`
  note wt = `P,E,hp s \<turnstile>1 Val v \<guillemotleft>bop\<guillemotright> e : T`
  note D = `\<D>1 (length E) (Val v \<guillemotleft>bop\<guillemotright> e) \<lfloor>A\<rfloor>`
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (Val v \<guillemotleft>bop\<guillemotright> e)`
  have lconfe: "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by auto
  have "P,E,hp s' \<turnstile>1 (Val v) \<guillemotleft>bop\<guillemotright> e' : T"
  proof (cases bop)
    assume [simp]: "bop = Eq"
    from wt obtain T1 T2 where [simp]: "T = Boolean"
      and wt1: "P,E,hp s \<turnstile>1 Val v : T1" and wt2: "P,E,hp s \<turnstile>1 e : T2" by auto
    show ?thesis
      using IH[OF `P \<turnstile> hp s \<surd>` lconfe _ wt2] WTrt1_hext_mono[OF wt1 red1_hext_incr[OF red]]
	D `\<B> (Val v \<guillemotleft>bop\<guillemotright> e) (length E)` by auto
  next
    assume  [simp]: "bop = Add"
    from wt have [simp]: "T = Integer" and wt1: "P,E,hp s \<turnstile>1 Val v : Integer"
      and wt2: "P,E,hp s \<turnstile>1 e : Integer" by auto
    show ?thesis
      using IH[OF `P \<turnstile> hp s \<surd>` lconfe _  wt2] WTrt1_hext_mono[OF wt1 red1_hext_incr[OF red]]
	D `\<B> (Val v \<guillemotleft>bop\<guillemotright> e) (length E)` by auto
  qed
  thus ?case by auto
next
  case (Red1BinOp bop) thus ?case by (cases bop) auto
next
  case Red1Var thus ?case by(auto simp add: lconf1_def conf_def hyper_isin_def)
next
  case LAss1Red thus ?case by(fastsimp intro:widen_trans)
next
  case Red1LAss thus ?case by fastsimp
next
  case (AAcc1Red1 a s ta a' s' i)
  note red = `P \<turnstile>1 \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp a;
                      \<D>1 (length E) a \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 a : T; \<B> a (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 a' : T' \<and> P \<turnstile> T' \<le> T`
  note wt = `P,E,hp s \<turnstile>1 a\<lfloor>i\<rceil> : T`
  note D = `\<D>1 (length E) (a\<lfloor>i\<rceil>) \<lfloor>A\<rfloor>`
  note B = `\<B> (a\<lfloor>i\<rceil>) (length E)`
  from red have nval: "\<not> is_val a" by auto
  with `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (a\<lfloor>i\<rceil>)`
  have lconf: "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp a" by auto
  from wt have i: "P,E,hp s \<turnstile>1 i : Integer" by auto
  with red1_hext_incr[OF red] have i': "P,E,hp s' \<turnstile>1 i : Integer" by-(rule WTrt1_hext_mono)
  { assume "P,E,hp s \<turnstile>1 a : T\<lfloor>\<rceil>"
    from IH[OF `P \<turnstile> hp s \<surd>` lconf _ this] D B i'
    have ?case by(auto simp add: widen_Array) }
  moreover { assume "P,E,hp s \<turnstile>1 a: NT"
    from IH[OF `P \<turnstile> hp s \<surd>` lconf _ this] D B i'
    have ?case by auto }
  ultimately show ?case using wt by auto
next
  case (AAcc1Red2 i s ta i' s' a)
  note red = `P \<turnstile>1 \<langle>i,s\<rangle> -ta\<rightarrow> \<langle>i',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp i;
                      \<D>1 (length E) i \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 i : T; \<B> i (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 i' : T' \<and> P \<turnstile> T' \<le> T`
  note wt = `P,E,hp s \<turnstile>1 Val a\<lfloor>i\<rceil> : T`
  note D = `\<D>1 (length E) (Val a\<lfloor>i\<rceil>) \<lfloor>A\<rfloor>`
  note B = `\<B> (Val a\<lfloor>i\<rceil>) (length E)`
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (Val a\<lfloor>i\<rceil>)`
  have "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp i" by simp
  from IH[OF `P \<turnstile> hp s \<surd>` this, of Integer] wt D B
  have "P,E,hp s' \<turnstile>1 i' : Integer" by auto
  with wt show ?case by(fastsimp dest!: hext_arrD[OF red1_hext_incr[OF red]])
next
  case Red1AAccNull thus ?case
    by(fastsimp simp add: hconf_def dest: typeof_NullPointer split: heapobj.split_asm intro: xcpt_subcls_Throwable[OF _ wf])
next
  case Red1AAccBounds thus ?case
    by(fastsimp simp add: hconf_def dest: typeof_ArrayIndexOutOfBounds split: heapobj.split_asm intro: xcpt_subcls_Throwable[OF _ wf])
next
  case Red1AAcc thus ?case by(fastsimp dest: hconfD simp add: oconf_def conf_def)
next
  case (AAss1Red1 a s ta a' s' i e)
  note red = `P \<turnstile>1 \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp a;
                      \<D>1 (length E) a \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 a : T; \<B> a (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 a' : T' \<and> P \<turnstile> T' \<le> T`
  note wt = `P,E,hp s \<turnstile>1 a\<lfloor>i\<rceil> := e : T`
  note D = `\<D>1 (length E) (a\<lfloor>i\<rceil> := e) \<lfloor>A\<rfloor>`
  note B = `\<B> (a\<lfloor>i\<rceil> := e) (length E)`
  from red have nval: "\<not> is_val a" by auto
  with `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (a\<lfloor>i\<rceil> := e)`
  have lconf: "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp a" by auto
  from wt obtain Te where "P,E,hp s \<turnstile>1 i : Integer" "P,E,hp s \<turnstile>1 e : Te" and [simp]: "T = Void" by auto
  with red1_hext_incr[OF red] have i': "P,E,hp s' \<turnstile>1 i : Integer"
    and e': "P,E,hp s' \<turnstile>1 e : Te" by(blast intro: WTrt1_hext_mono)+
  { fix T
    assume "P,E,hp s \<turnstile>1 a : T\<lfloor>\<rceil>"
    from IH[OF `P \<turnstile> hp s \<surd>` lconf _ this] D B i' e' nval
    have ?case by(auto simp add: widen_Array) }
  moreover { assume "P,E,hp s \<turnstile>1 a: NT"
    from IH[OF `P \<turnstile> hp s \<surd>` lconf _ this] D B i' e' nval
    have ?case by auto }
  ultimately show ?case using wt by auto
next
  case (AAss1Red2 i s ta i' s' a e)
  note red = `P \<turnstile>1 \<langle>i,s\<rangle> -ta\<rightarrow> \<langle>i',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp i;
                      \<D>1 (length E) i \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 i : T; \<B> i (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 i' : T' \<and> P \<turnstile> T' \<le> T`
  note wt = `P,E,hp s \<turnstile>1 Val a\<lfloor>i\<rceil> := e : T`
  note D = `\<D>1 (length E) (Val a\<lfloor>i\<rceil> := e) \<lfloor>A\<rfloor>`
  note B = `\<B> (Val a\<lfloor>i\<rceil> := e) (length E)`
  from red have nval: "\<not> is_val i" by auto
  with `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (Val a\<lfloor>i\<rceil> := e)`
  have "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp i" by simp
  from IH[OF `P \<turnstile> hp s \<surd>` this, of Integer] wt D B
  have "P,E,hp s' \<turnstile>1 i' : Integer" by auto
  with wt show ?case
    by(fastsimp dest!: hext_arrD[OF red1_hext_incr[OF red]] intro: WTrt1_hext_mono[OF _ red1_hext_incr[OF red]])
next
  case (AAss1Red3 e s ta e' s' a i)
  note red = `P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e;
                      \<D>1 (length E) e \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 e : T; \<B> e (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T`
  note wt = `P,E,hp s \<turnstile>1 Val a\<lfloor>Val i\<rceil> := e : T`
  note D = `\<D>1 (length E) (Val a\<lfloor>Val i\<rceil> := e) \<lfloor>A\<rfloor>`
  note B = `\<B> (Val a\<lfloor>Val i\<rceil> := e) (length E)`
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (Val a\<lfloor>Val i\<rceil> := e)`
  have "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by simp
  from IH[OF `P \<turnstile> hp s \<surd>` this] wt D B
  show ?case
    by(fastsimp dest!: hext_arrD[OF red1_hext_incr[OF red]] intro: WTrt1_hext_mono[OF _ red1_hext_incr[OF red]])
next
  case Red1AAssNull thus ?case
    by(fastsimp simp add: hconf_def dest: typeof_NullPointer split: heapobj.split_asm intro: xcpt_subcls_Throwable[OF _ wf])
next
  case Red1AAssBounds thus ?case
    by(fastsimp simp add: hconf_def dest: typeof_ArrayIndexOutOfBounds split: heapobj.split_asm intro: xcpt_subcls_Throwable[OF _ wf])
next
  case Red1AAssStore thus ?case
    by(fastsimp simp add: hconf_def dest: typeof_ArrayStore split: heapobj.split_asm intro: xcpt_subcls_Throwable[OF _ wf])
next
  case Red1AAss  thus ?case by(auto simp del:fun_upd_apply)
next
  case ALength1Red thus ?case by(fastsimp simp add: widen_Array)
next
  case Red1ALength thus ?case by auto
next
  case Red1ALengthNull thus ?case
    by(fastsimp simp add: hconf_def dest: typeof_NullPointer split: heapobj.split_asm intro: xcpt_subcls_Throwable[OF _ wf])
next
  case (FAcc1Red e s ta e' s' F D)
  note red = `P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e;
                      \<D>1 (length E) e \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 e : T; \<B> e (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T`
  note wt = `P,E,hp s \<turnstile>1 e\<bullet>F{D} : T`
  note D = `\<D>1 (length E) (e\<bullet>F{D}) \<lfloor>A\<rfloor>`
  note B = `\<B> (e\<bullet>F{D}) (length E)`
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (e\<bullet>F{D})`
  have lconf: "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by simp
  { fix C
    assume wte: "P,E,hp s \<turnstile>1 e : Class C" and has: "P \<turnstile> C has F:T in D"
    from IH[OF `P \<turnstile> hp s \<surd>` lconf _ wte] D B obtain T'
      where wte': "P,E,hp s' \<turnstile>1 e' : T'" and sub: "P \<turnstile> T' \<le> Class C" by auto
    with has wf_Object_field_empty[OF wf] have ?case
      by(auto simp add: widen_Class intro: has_field_mono)(auto simp add: has_field_def dest: has_fields_fun) }
  moreover {
    assume "P,E,hp s \<turnstile>1 e : NT"
    from IH[OF `P \<turnstile> hp s \<surd>` lconf _ this] D B have ?case by auto }
  ultimately show ?case using wt by auto
next
  case Red1FAcc thus ?case
    by(fastsimp simp:hconf_def oconf_def conf_def has_field_def  dest:has_fields_fun)
next
  case Red1FAccNull thus ?case
    by(fastsimp simp add: hconf_def dest: typeof_NullPointer split: heapobj.split_asm intro: xcpt_subcls_Throwable[OF _ wf])
next
  case (FAss1Red1 e s ta e' s' F D e2)
  note red = `P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e;
                      \<D>1 (length E) e \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 e : T; \<B> e (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T`
  note wt = `P,E,hp s \<turnstile>1 e\<bullet>F{D} := e2 : T`
  note D = `\<D>1 (length E) (e\<bullet>F{D} := e2) \<lfloor>A\<rfloor>`
  note B = `\<B> (e\<bullet>F{D} := e2) (length E)`
  from red have nval: "\<not> is_val e" by auto
  with `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (e\<bullet>F{D} := e2)`
  have lconf: "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by simp
  { fix C TF T2
    assume wte: "P,E,hp s \<turnstile>1 e : Class C" and has: "P \<turnstile> C has F:TF in D"
      and wte2: "P,E,hp s \<turnstile>1 e2 : T2" and sub: "P \<turnstile> T2 \<le> TF" and T: "T = Void"
    from IH[OF `P \<turnstile> hp s \<surd>` lconf _ wte] D B obtain T'
      where "P,E,hp s' \<turnstile>1 e' : T'" "P \<turnstile> T' \<le> Class C" by auto
    with has wf_Object_field_empty[OF wf] WTrt1_hext_mono[OF wte2 red1_hext_incr[OF red]] sub T
    have ?case
      by(auto simp add: widen_Class intro: has_field_mono)(auto simp add: has_field_def dest: has_fields_fun) }
  moreover { fix T2
    assume wte: "P,E,hp s \<turnstile>1 e : NT" and wte2: "P,E,hp s \<turnstile>1 e2 : T2"
    from IH[OF `P \<turnstile> hp s \<surd>` lconf _ wte] D B wt nval WTrt1_hext_mono[OF wte2 red1_hext_incr[OF red]]
    have ?case by auto }
  ultimately show ?case using wt by auto
next
  case (FAss1Red2 e s ta e' s' v F D)
  note red = `P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e;
                      \<D>1 (length E) e \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 e : T; \<B> e (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T`
  note wt = `P,E,hp s \<turnstile>1 Val v\<bullet>F{D} := e : T`
  note D = `\<D>1 (length E) (Val v\<bullet>F{D} := e) \<lfloor>A\<rfloor>`
  note B = `\<B> (Val v\<bullet>F{D} := e) (length E)`
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (Val v\<bullet>F{D} := e)`
  have lconf: "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by simp
  { fix C TF T2
    assume wte: "P,E,hp s \<turnstile>1 Val v : Class C" and has: "P \<turnstile> C has F:TF in D"
      and wte2: "P,E,hp s \<turnstile>1 e : T2" and sub: "P \<turnstile> T2 \<le> TF" and T: "T = Void"
    from IH[OF `P \<turnstile> hp s \<surd>` lconf _ wte2] D B obtain T2'
      where "P,E,hp s' \<turnstile>1 e' : T2'" "P \<turnstile> T2' \<le> T2" by auto
    with has wf_Object_field_empty[OF wf] WTrt1_hext_mono[OF wte red1_hext_incr[OF red]] sub T
    have ?case by(auto intro: widen_trans) }
  moreover { fix T2
    assume wte: "P,E,hp s \<turnstile>1 Val v : NT" and wte2: "P,E,hp s \<turnstile>1 e : T2" and [simp]: "T = Void"
    from IH[OF `P \<turnstile> hp s \<surd>` lconf _ wte2] D B WTrt1_hext_mono[OF wte red1_hext_incr[OF red]]
    have ?case by auto }
  ultimately show ?case using wt by fastsimp
next
  case Red1FAss thus ?case by(auto simp del:fun_upd_apply)
next
  case Red1FAssNull thus ?case
    by(fastsimp simp add: hconf_def dest: typeof_NullPointer split: heapobj.split_asm intro: xcpt_subcls_Throwable[OF _ wf])
next
  case (Call1Obj e s ta e' s' M es)
  note red = `P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e;
                      \<D>1 (length E) e \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 e : T; \<B> e (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T`
  note D = `\<D>1 (length E) (e\<bullet>M(es)) \<lfloor>A\<rfloor>`
  note B = `\<B> (e\<bullet>M(es)) (length E)`
  from red have "\<not> is_val e" by auto
  with `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (e\<bullet>M(es))`
  have lconf': "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by simp
  from `P,E,hp s \<turnstile>1 e\<bullet>M(es) : T` show ?case
  proof cases
    case (WTrt1Call EE ee C MM ES Ts' T' mthd D Us)
    hence [simp]: "ee = e" "MM = M" "ES = es" "EE = E" "T' = T"
      and wte: "P,E,hp s \<turnstile>1 e : Class C"
      and sees: "P \<turnstile> C sees M: Ts'\<rightarrow>T = mthd in D"
      and wtes: "P,E,hp s \<turnstile>1 es [:] Us"
      and subs: "P \<turnstile> Us [\<le>] Ts'" 
      and iec: "\<not> is_external_call P (Class C) M (length es)" by auto 
    from IH[OF `P \<turnstile> hp s \<surd>` lconf' _ wte] D B
    obtain U where wte': "P,E,hp s' \<turnstile>1 e' : U" and UsubC: "P \<turnstile> U \<le> Class C" by auto
    { assume "U = NT"
      moreover have "P,E,hp s' \<turnstile>1 es [:] Us"
	by(rule WTrts1_hext_mono[OF wtes red1_hext_incr[OF red]])
      ultimately have ?thesis using wte' by(blast intro!:WTrt1CallNT) }
    moreover
    { fix C' assume UClass: "U = Class C'" and "subclass": "P \<turnstile> C' \<preceq>\<^sup>* C"
      have "P,E,hp s' \<turnstile>1 e' : Class C'" using wte' UClass by auto
      moreover obtain Ts'' T' meth' D'
	where sees': "P \<turnstile> C' sees M:Ts''\<rightarrow>T' = meth' in D'"
	and subs': "P \<turnstile> Ts' [\<le>] Ts''" and sub': "P \<turnstile> T' \<le> T"
	using Call_lemma[OF sees "subclass" wf] by auto
      moreover have "P,E,hp s' \<turnstile>1 es [:] Us"
	by(rule WTrts1_hext_mono[OF wtes red1_hext_incr[OF red]])
      moreover from sees' "subclass" have "\<not> is_external_call P (Class C') M (length es)"
	by(blast dest: external_call_not_sees_method[OF wf])
      ultimately have ?thesis
	using subs by(blast intro:WTrt1Call rtrancl_trans widens_trans) }
    moreover
    { fix A assume "U = A\<lfloor>\<rceil>"
      with UsubC have "C = Object" by(auto dest: Array_widen)
      with sees have False by(auto intro: wf_Object_method_empty[OF wf]) }
    ultimately show ?thesis using UsubC by(auto simp add:widen_Class)
  next
    case (WTrt1CallNT EE ee ES Ts' MM T')
    hence [simp]: "EE = E" "ee = e" "MM = M" "ES = es" "T' = T"
      and wte: "P,E,hp s \<turnstile>1 e : NT" and wtes: "P,E,hp s \<turnstile>1 es [:] Ts'" by auto
    from IH[OF `P \<turnstile> hp s \<surd>` lconf' _ wte] D B have "P,E,hp s' \<turnstile>1 e' : NT" by auto
    moreover have "P,E,hp s' \<turnstile>1 es [:] Ts'"
      by(rule WTrts1_hext_mono[OF wtes red1_hext_incr[OF red]])
    ultimately show ?thesis by(blast intro!:WTrt1CallNT)
  next
    case (WTrt1CallExternal EE ee TT ES Ts MM U)
    hence [simp]: "MM = M" "ee = e" "ES = es" "U = T"
      and wte: "P,E,hp s \<turnstile>1 e : TT" and wtes: "P,E,hp s \<turnstile>1 es [:] Ts"
      and wtext: "P \<turnstile> TT\<bullet>M(Ts) :: U" by auto
    from IH[OF `P \<turnstile> hp s \<surd>` lconf' _ wte] D B obtain T' where wte': "P,E,hp s' \<turnstile>1 e' : T'" 
      and T': "P \<turnstile> T' \<le> TT" by(auto)
    note wtes' = WTrts1_hext_mono[OF wtes red1_hext_incr[OF red]]
    show ?thesis
    proof(cases "T' = NT")
      case True
      with wte' wtes' show ?thesis by(blast intro: WTrt1CallNT)
    next
      case False
      with wtext T' have "\<exists>U'. P \<turnstile> T'\<bullet>M(Ts) :: U' \<and> P \<turnstile> U' \<le> U"
	by(blast intro: external_WTrt_widen_mono widens_refl)
      with wte' wtes' show ?thesis by auto
    qed
  qed simp_all
next
  case (Call1Params es s ta es' s' v M)
  note reds = `P \<turnstile>1 \<langle>es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>`
  note IH = `\<And>Ts E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exps es;
                       \<D>s1 (length E) es \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 es [:] Ts; \<B>s es (length E)\<rbrakk>
           \<Longrightarrow> \<exists>Ts'. P,E,hp s' \<turnstile>1 es' [:] Ts' \<and> P \<turnstile> Ts' [\<le>] Ts`
  note D = `\<D>1 (length E) (Val v\<bullet>M(es)) \<lfloor>A\<rfloor>`
  note B = `\<B> (Val v\<bullet>M(es)) (length E)`
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (Val v\<bullet>M(es))`
  have lconf': "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exps es" by simp
  from reds have "\<not> is_vals es" by(auto simp add: is_vals_conv)
  with `P,E,hp s \<turnstile>1 Val v\<bullet>M(es) : T` show ?case
  proof cases
    case (WTrt1Call EE e C MM ES Ts T' mthd D Us)
    hence [simp]: "EE = E" "e = Val v" "MM = M" "ES = es" "T' = T"
      and wte: "P,E,hp s \<turnstile>1 Val v : Class C"
      and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T' = mthd in D"
      and wtes: "P,E,hp s \<turnstile>1 es [:] Us"
      and sub: "P \<turnstile> Us [\<le>] Ts" 
      and iec: "\<not> is_external_call P (Class C) M (length es)" by auto
    from IH[OF `P \<turnstile> hp s \<surd>` lconf' _ wtes] D B
    obtain Us' where "P,E,hp s' \<turnstile>1 es' [:] Us'" "P \<turnstile> Us' [\<le>] Us" by auto
    moreover from wte have "P,E,hp s' \<turnstile>1 Val v : Class C"
      by(rule WTrt1_hext_mono)(rule reds1_hext_incr[OF reds])
    moreover from reds have "length es' = length es" by(rule reds1_preserves_elen)
    ultimately show ?thesis using iec sees sub by(fastsimp intro: widens_trans)
  next
    case (WTrt1CallNT EE e ES Ts MM T')
    hence [simp]: "EE = E" "e = Val v" "MM = M" "ES = es" "T' = T"
      and wte: "P,E,hp s \<turnstile>1 Val v : NT"
      and wtes: "P,E,hp s \<turnstile>1 es [:] Ts" by auto
    from IH[OF `P \<turnstile> hp s \<surd>` lconf' _ wtes] D B
    obtain Us' where "P,E,hp s' \<turnstile>1 es' [:] Us'" "P \<turnstile> Us' [\<le>] Ts" by auto
    moreover from wte have "P,E,hp s' \<turnstile>1 Val v : NT"
      by(rule WTrt1_hext_mono)(rule reds1_hext_incr[OF reds])
    ultimately show ?thesis by(fastsimp intro: widens_trans)
  next
    case (WTrt1CallExternal EE ee TT ES Ts MM U)
    hence [simp]: "MM = M" "ee = Val v" "ES = es" "U = T" "EE = E"
      and wte: "P,E,hp s \<turnstile>1 Val v : TT" and wtes: "P,E,hp s \<turnstile>1 es [:] Ts"
      and wtext: "P \<turnstile> TT\<bullet>M(Ts) :: U" by auto
    from IH[OF `P \<turnstile> hp s \<surd>` lconf' _ wtes] D B
    obtain Ts' where wtes': "P,E,hp s' \<turnstile>1 es' [:] Ts'" 
      and Ts': "P \<turnstile> Ts' [\<le>] Ts" by(auto)
    note wte' = WTrt1_hext_mono[OF wte reds1_hext_incr[OF reds]]
    show ?thesis
    proof(cases "TT = NT")
      case True
      with wte' wtes' show ?thesis by(blast intro: WTrt1CallNT)
    next
      case False
      with wtext Ts' have "\<exists>U'. P \<turnstile> TT\<bullet>M(Ts') :: U' \<and> P \<turnstile> U' \<le> U"
	by(blast intro: external_WTrt_widen_mono widens_refl)
      with wte' wtes' show ?thesis by auto
    qed
  qed(auto)
next
  case Red1CallExternal thus ?case
    by(auto split: heapobj.split_asm dest: red_external_conf_extRet[OF wf] intro: wt_external_call simp add: hconf_def)
next
  case Red1CallNull thus ?case
    by (unfold hconf_def) (fastsimp elim!:typeof_NullPointer simp add: xcpt_subcls_Throwable[OF _ wf])
next
  case (Block1RedNone e h x ta e' h' x' V Tv cr)
  note red = `P \<turnstile>1 \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp (h, x) \<surd>; P,hp (h, x),A \<turnstile>1 lcl (h, x) (:\<le>) E @ env_exp e;
                      \<D>1 (length E) e \<lfloor>A\<rfloor>; P,E,hp (h, x) \<turnstile>1 e : T; \<B> e (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp (h', x') \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T`
  note D = `\<D>1 (length E) {V:Tv=None; e}\<^bsub>cr\<^esub> \<lfloor>A\<rfloor>`
  note B = `\<B> {V:Tv=None; e}\<^bsub>cr\<^esub> (length E)`
  from `P,hp (h, x),A \<turnstile>1 lcl (h, x) (:\<le>) E @ env_exp {V:Tv=None; e}\<^bsub>cr\<^esub>`
  have lconf': "P,hp (h, x),A \<turnstile>1 lcl (h, x) (:\<le>) (E @ [Tv]) @ env_exp e" by simp
  from `P,E,hp (h, x) \<turnstile>1 {V:Tv=None; e}\<^bsub>cr\<^esub> : T` have wte: "P,(E@[Tv]),hp (h, x) \<turnstile>1 e : T" by auto
  from IH[OF `P \<turnstile> hp (h, x) \<surd>` lconf' _ wte] D B
  obtain T' where "P,(E @ [Tv]),hp (h', x') \<turnstile>1 e' : T'" "P \<turnstile> T' \<le> T" by auto
  thus ?case by auto
next
  case (Block1RedSome e h x V v ta e' h' x' Tv cr)
  note red = `P \<turnstile>1 \<langle>e,(h, x[V := v])\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp (h, x[V := v]) \<surd>; P,hp (h, x[V := v]),A \<turnstile>1 lcl (h, x[V := v]) (:\<le>) E @ env_exp e; 
                      \<D>1 (length E) e \<lfloor>A\<rfloor>; P,E,hp (h, x[V := v]) \<turnstile>1 e : T; \<B> e (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp (h', x') \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T`
  note D = `\<D>1 (length E) {V:Tv=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub> \<lfloor>A\<rfloor>`
  note B = `\<B> {V:Tv=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub> (length E)`
  hence [simp]: "V = length E" by simp
  from `P,E,hp (h, x) \<turnstile>1 {V:Tv=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub> : T` have wte: "P,(E@[Tv]),hp (h, x[V := v]) \<turnstile>1 e : T"
    and conf: "P,h \<turnstile> v :\<le> Tv" by(auto simp add: conf_def)
  from `P,hp (h, x),A \<turnstile>1 lcl (h, x) (:\<le>) E @ env_exp {V:Tv=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub>` `V < length x` conf
  have lconf': "P,hp (h, x[V := v]),insert V A \<turnstile>1 lcl (h, x[V := v]) (:\<le>) (E @ [Tv]) @ env_exp e"
    by(auto intro: lconf1_upd)
  from IH[OF _ lconf' _ wte] D B `P \<turnstile> hp (h, x) \<surd>` 
  obtain T' where "P,(E @ [Tv]),h' \<turnstile>1 e' : T'" "P \<turnstile> T' \<le> T" by auto
  thus ?case by auto
next
  case Red1BlockNone thus ?case by auto
next
  case Red1BlockSome thus ?case by auto
next
  case (Synchronized1Red1 e s ta e' s' V e2)
  note red = `P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e;
                      \<D>1 (length E) e \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 e : T; \<B> e (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T`
  note D = `\<D>1 (length E) (sync\<^bsub>V\<^esub> (e) e2) \<lfloor>A\<rfloor>`    
  note B = `\<B> (sync\<^bsub>V\<^esub> (e) e2) (length E)`
  hence [simp]: "V = length E" by simp
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (sync\<^bsub>V\<^esub> (e) e2)`
  have lconf': "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by simp
  from `P,E,hp s \<turnstile>1 sync\<^bsub>V\<^esub> (e) e2 : T` show ?case
  proof cases
    case (WTrt1Synchronized EE ee U ee2 T' V')
    hence [simp]: "EE = E" "ee = e" "V' = V" "ee2 = e2" "T' = T"
      and wte: "P,E,hp s \<turnstile>1 e : U"
      and U: "is_refT U" "U \<noteq> NT"
      and wte2: "P,(E @ [Class Object]),hp s \<turnstile>1 e2 : T" by auto
    from IH[OF `P \<turnstile> hp s \<surd>` lconf' _ wte] D B
    obtain U' where wte': "P,E,hp s' \<turnstile>1 e' : U'" and sub': "P \<turnstile> U' \<le> U" by auto
    from wte2 have wte2': "P,(E @ [Class Object]),hp s' \<turnstile>1 e2 : T"
      by(rule WTrt1_hext_mono)(rule red1_hext_incr[OF red])
    show ?thesis
    proof(cases "U' = NT")
      case True
      with wte2' wte' show ?thesis by auto
    next
      case False
      with sub' U have "is_refT U'" by(auto intro: widen_refT)
      with wte2' wte' False show ?thesis by auto
    qed
  next
    case (WTrt1SynchronizedNT EE ee E2 U V' T')
    hence [simp]: "EE = E" "ee = e" "V' = V" "E2 = e2" "T' = T"
      and wte: "P,E,hp s \<turnstile>1 e : NT"
      and wte2: "P,(E @ [Class Object]),hp s \<turnstile>1 e2 : U" by auto
    from IH[OF `P \<turnstile> hp s \<surd>` lconf' _ wte] D B have "P,E,hp s' \<turnstile>1 e' : NT" by auto
    moreover from wte2 have wte2': "P,(E @ [Class Object]),hp s' \<turnstile>1 e2 : U"
      by(rule WTrt1_hext_mono)(rule red1_hext_incr[OF red])
    ultimately show ?thesis by auto
  qed simp_all
next
  case Synchronized1Null thus ?case
    by (unfold hconf_def) (fastsimp elim!:typeof_NullPointer simp add: xcpt_subcls_Throwable[OF _ wf])
next
  case Lock1Synchronized thus ?case by(auto split: heapobj.split_asm)
next
  case (Synchronized1Red2 e s ta e' s' V a)
  note red = `P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e;
                      \<D>1 (length E) e \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 e : T; \<B> e (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T`
  note D = `\<D>1 (length E) (insync\<^bsub>V\<^esub> (a) e) \<lfloor>A\<rfloor>`
  note B = `\<B> (insync\<^bsub>V\<^esub> (a) e) (length E)`
  hence [simp]: "V = length E" by simp
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (insync\<^bsub>V\<^esub> (a) e)`
  have lconf': "P,hp s,A \<turnstile>1 lcl s (:\<le>) (E @ [Class Object]) @ env_exp e" by simp
  from `P,E,hp s \<turnstile>1 insync\<^bsub>V\<^esub> (a) e : T` obtain U
    where wta: "P,E,hp s \<turnstile>1 addr a : U" and wte: "P,(E @ [Class Object]),hp s \<turnstile>1 e : T" by auto
  from IH[OF `P \<turnstile> hp s \<surd>` lconf' _ wte] D B obtain T'
    where "P,E @ [Class Object] ,hp s' \<turnstile>1 e' : T'" "P \<turnstile> T' \<le> T" by auto
  moreover from wta have "P,E,hp s' \<turnstile>1 addr a : U"
    by(rule WTrt1_hext_mono)(rule red1_hext_incr[OF red])
  ultimately show ?case by auto
next
  case Unlock1Synchronized thus ?case
    by(auto split: heapobj.split_asm)
next
  case (Seq1Red e s ta e' s' e2)
  note red = `P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e;
                      \<D>1 (length E) e \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 e : T; \<B> e (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T`
  note D = `\<D>1 (length E) (e;; e2) \<lfloor>A\<rfloor>`
  note B = `\<B> (e;; e2) (length E)`
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (e;; e2)`
  have lconf': "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by simp
  from `P,E,hp s \<turnstile>1 e;; e2 : T` obtain U
    where wte1: "P,E,hp s \<turnstile>1 e : U" and wte2: "P,E,hp s \<turnstile>1 e2 : T" by auto
  from IH[OF `P \<turnstile> hp s \<surd>` lconf' _ wte1] D B obtain U'
    where "P,E,hp s' \<turnstile>1 e' : U'" "P \<turnstile> U' \<le> U" by auto
  moreover from wte2 have "P,E,hp s' \<turnstile>1 e2 : T"
    by(rule WTrt1_hext_mono)(rule red1_hext_incr[OF red])
  ultimately show ?case by auto
next
  case Red1Seq thus ?case by auto
next
  case (Cond1Red e s ta e' s' e1 e2)
  note red = `P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e;
                      \<D>1 (length E) e \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 e : T; \<B> e (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T`
  note D = `\<D>1 (length E) (if (e) e1 else e2) \<lfloor>A\<rfloor>`
  note B = `\<B> (if (e) e1 else e2) (length E)`
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (if (e) e1 else e2)`
  have lconf': "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by simp
  from `P,E,hp s \<turnstile>1 if (e) e1 else e2 : T` obtain T1 T2
    where wte: "P,E,hp s \<turnstile>1 e : Boolean"
    and wte1: "P,E,hp s \<turnstile>1 e1 : T1"
    and wte2: "P,E,hp s \<turnstile>1 e2 : T2"
    and comp: "P \<turnstile> T1 \<le> T2 \<or> P \<turnstile> T2 \<le> T1"
    and tt2: "P \<turnstile> T1 \<le> T2 \<longrightarrow> T = T2"
    and tt1: "P \<turnstile> T2 \<le> T1 \<longrightarrow> T = T1" by auto
  from IH[OF `P \<turnstile> hp s \<surd>` lconf' _ wte] D B have "P,E,hp s' \<turnstile>1 e' : Boolean" by auto
  moreover from wte1 have "P,E,hp s' \<turnstile>1 e1 : T1"
    by(rule WTrt1_hext_mono)(rule red1_hext_incr[OF red])
  moreover from wte2 have "P,E,hp s' \<turnstile>1 e2 : T2"
    by(rule WTrt1_hext_mono)(rule red1_hext_incr[OF red])
  ultimately show ?case using comp tt2 tt1 by auto
next
  case Red1CondT thus ?case by auto
next
  case Red1CondF thus ?case by auto
next
  case Red1While thus ?case by(fastsimp) 
next
  case (Throw1Red e s ta e' s')
  note red = `P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e;
                      \<D>1 (length E) e \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 e : T; \<B> e (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T`
  note D = `\<D>1 (length E) (throw e) \<lfloor>A\<rfloor>`
  note B = `\<B> (throw e) (length E)`
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (throw e)`
  have lconf': "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by simp
  from `P,E,hp s \<turnstile>1 throw e : T` obtain T'
    where wte: "P,E,hp s \<turnstile>1 e : T'"
    and throwable: "P \<turnstile> T' \<le> Class Throwable" by auto
  from IH[OF `P \<turnstile> hp s \<surd>` lconf' _ wte] B D
  obtain T'' where "P,E,hp s' \<turnstile>1 e' : T''" "P \<turnstile> T'' \<le> T'" by auto
  with throwable have "P \<turnstile> T'' \<le> Class Throwable" by(blast intro: widen_trans)
  with `P,E,hp s' \<turnstile>1 e' : T''` have "P,E,hp s' \<turnstile>1 throw e' : T" by auto
  thus ?case by auto
next 
  case Red1ThrowNull thus ?case
    by (unfold hconf_def) (fastsimp elim!:typeof_NullPointer simp add: xcpt_subcls_Throwable[OF _ wf])
next
  case (Try1Red e s ta e' s' C V e2)
  note red = `P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e;
                      \<D>1 (length E) e \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 e : T; \<B> e (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T`
  note D = `\<D>1 (length E) (try e catch(C V) e2) \<lfloor>A\<rfloor>`
  note B = `\<B> (try e catch(C V) e2) (length E)`
  from `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp (try e catch(C V) e2)`
  have lconf': "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by simp
  from `P,E,hp s \<turnstile>1 try e catch(C V) e2 : T` obtain U 
    where wte: "P,E,hp s \<turnstile>1 e : U"
    and wte2: "P,(E@[Class C]),hp s \<turnstile>1 e2 : T"
    and sub: "P \<turnstile> U \<le> T" by auto
  from IH[OF `P \<turnstile> hp s \<surd>` lconf' _ wte] D B obtain U'
    where "P,E,hp s' \<turnstile>1 e' : U'" "P \<turnstile> U' \<le> U" by auto
  moreover from wte2 have "P,(E@[Class C]),hp s' \<turnstile>1 e2 : T"
    by(rule WTrt1_hext_mono)(rule red1_hext_incr[OF red])
  ultimately show ?case using sub by(auto intro: widen_trans)
next
  case Red1Try thus ?case by auto
next
  case Red1TryFail thus ?case
    by(fastsimp intro: WTrt1Throw[OF WTrt1Val] simp: hconf_def)
next
  case (Red1TryCatch h a D fs C V x e2)
  from `P,E,hp (h, x) \<turnstile>1 try Throw a catch(C V) e2 : T`
  have "P,(E@[Class C]),h \<turnstile>1 e2 : T" by auto
  hence "P,E,h \<turnstile>1 {V:Class C=None; e2}\<^bsub>False\<^esub> : T" by auto
  thus ?case by auto
next
  case (List1Red1 e s ta e' s' es)
  note red = `P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `\<And>T E A. \<lbrakk>P \<turnstile> hp s \<surd>; P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e;
                      \<D>1 (length E) e \<lfloor>A\<rfloor>; P,E,hp s \<turnstile>1 e : T; \<B> e (length E)\<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T`
  note D = `\<D>s1 (length E) (e # es) \<lfloor>A\<rfloor>`
  note B = `\<B>s (e # es) (length E)`
  from red have "\<not> is_val e" by auto
  with `P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exps (e # es)`
  have lconf': "P,hp s,A \<turnstile>1 lcl s (:\<le>) E @ env_exp e" by simp
  from `P,E,hp s \<turnstile>1 e # es [:] Ts` obtain T Ts'
    where wte: "P,E,hp s \<turnstile>1 e : T" and wtes: "P,E,hp s \<turnstile>1 es [:] Ts'" 
    and [simp]: "Ts = T # Ts'" by auto
  from IH[OF `P \<turnstile> hp s \<surd>` lconf' _ wte] D B obtain T'
    where wte': "P,E,hp s' \<turnstile>1 e' : T'" and "P \<turnstile> T' \<le> T" by auto
  hence "P \<turnstile> (T' # Ts') [\<le>] Ts" by(auto intro: widens_refl)
  moreover from wtes have "P,E,hp s' \<turnstile>1 es [:] Ts'"
    by(rule WTrts1_hext_mono)(rule red1_hext_incr[OF red])
  ultimately show ?case using wte' by auto
next
  case List1Red2 thus ?case
    by(fastsimp dest: hext_typeof_mono[OF reds1_hext_incr])
next
  case Bin1OpThrow1 thus ?case by fastsimp
next
  case Bin1OpThrow2 thus ?case by fastsimp
next
  case LAss1Throw thus ?case by fastsimp
next
  case Call1ThrowObj thus ?case by fastsimp
next
  case Call1ThrowParams thus ?case by fastsimp
next
  case Unlock1SynchronizedNull thus ?case
    by(fastsimp simp add: hconf_def xcpt_subcls_Throwable[OF _ wf] elim: typeof_NullPointer)
next
  case Unlock1SynchronizedFail thus ?case
    by(fastsimp simp add: hconf_def xcpt_subcls_Throwable[OF _ wf] elim: typeof_IllegalMonitorState)
next
  case Synchronized1Throw2Null thus ?case
    by(fastsimp simp add: hconf_def xcpt_subcls_Throwable[OF _ wf] elim: typeof_NullPointer)
next
  case Synchronized1Throw2Fail thus ?case
    by(fastsimp simp add: hconf_def xcpt_subcls_Throwable[OF _ wf] elim: typeof_IllegalMonitorState)
qed(fastsimp)+

lemma length_inline_calls [simp]: "length (inline_calls e es) = length es"
by(induct es) auto

lemma assumes wf: "wf_prog wfmd P"
  and ha: "h a = \<lfloor>Obj C fs\<rfloor>"
  and seescall: "P \<turnstile> C sees M : Ts' \<rightarrow> T' = mthd in D"
  and wte1: "\<And>E. \<exists>T1. P,E,h \<turnstile>1 e1 : T1 \<and> P \<turnstile> T1 \<le> T'"
  shows WTrt1_inline_call:
  "\<lbrakk> P,E2,h \<turnstile>1 e2 : T2; call e2 = \<lfloor>(a, M, vs)\<rfloor> \<rbrakk>
  \<Longrightarrow> \<exists>T2'. P,E2,h \<turnstile>1 inline_call e1 e2 : T2' \<and> P \<turnstile> T2' \<le> T2"

  and WTrts1_inline_calls:
  "\<lbrakk> P,E2,h \<turnstile>1 es [:] Ts; calls es = \<lfloor>(a, M, vs)\<rfloor> \<rbrakk>
  \<Longrightarrow> \<exists>Ts'. P,E2,h \<turnstile>1 inline_calls e1 es [:] Ts' \<and> P \<turnstile> Ts' [\<le>] Ts"
proof(induct rule: WTrt1_WTrts1.inducts)
  case WTrt1New thus ?case by fastsimp
next
  case WTrt1NewArray thus ?case by fastsimp
next
  case WTrt1Cast thus ?case by fastsimp
next
  case WTrt1Val thus ?case by simp
next
  case WTrt1Var thus ?case by simp
next
  case WTrt1BinOpEq thus ?case by fastsimp
next
  case WTrt1BinOpAdd thus ?case by fastsimp
next
  case WTrt1LAss thus ?case by(fastsimp intro: widen_trans)
next
  case WTrt1AAcc thus ?case by(fastsimp simp add: widen_Array)
next
  case WTrt1AAccNT thus ?case by fastsimp
next
  case WTrt1AAss thus ?case by(fastsimp simp add: widen_Array)
next
  case WTrt1AAssNT thus ?case by fastsimp
next
  case WTrt1ALength thus ?case by(fastsimp simp add: widen_Array)
next
  case WTrt1ALengthNT thus ?case by fastsimp
next
  case WTrt1FAcc thus ?case using wf_Object_field_empty[OF wf] 
    by(auto simp add: widen_Class intro: has_field_mono)(auto simp add: has_field_def dest: has_fields_fun)
next
  case WTrt1FAccNT thus ?case by fastsimp
next
  case WTrt1FAss thus ?case using wf_Object_field_empty[OF wf]
    by(auto simp add: widen_Class intro: has_field_mono widen_trans)
      ((fastsimp intro: widen_trans has_field_mono)+,auto simp add: has_field_def dest: has_fields_fun)
next
  case WTrt1FAssNT thus ?case by fastsimp
next
  case (WTrt1Call E2 obj C M' es Ts' T m D  Ts)
  note IHo = `call obj = \<lfloor>(a, M, vs)\<rfloor> \<Longrightarrow> \<exists>T2'. P,E2,h \<turnstile>1 inline_call e1 obj : T2' \<and> P \<turnstile> T2' \<le> Class C`
  note IHp = `calls es = \<lfloor>(a, M, vs)\<rfloor> \<Longrightarrow> \<exists>Ts'. P,E2,h \<turnstile>1 inline_calls e1 es [:] Ts' \<and> P \<turnstile> Ts' [\<le>] Ts`
  note sees = `P \<turnstile> C sees M': Ts'\<rightarrow>T = m in D`
  note wto = `P,E2,h \<turnstile>1 obj : Class C`
  note wtp = `P,E2,h \<turnstile>1 es [:] Ts`
  note sub = `P \<turnstile> Ts [\<le>] Ts'`
  note iec = `\<not> is_external_call P (Class C) M' (length es)`
  from `call (obj\<bullet>M'(es)) = \<lfloor>(a, M, vs)\<rfloor>` show ?case
  proof(cases rule: call_callE)
    case CallObj
    with IHo obtain T2' where wto': "P,E2,h \<turnstile>1 inline_call e1 obj : T2'"
      and sub': "P \<turnstile> T2' \<le> Class C" by auto
    show ?thesis
    proof(cases "T2' = NT")
      case True
      with wtp wto' CallObj show ?thesis by auto
    next
      case False
      from sees have "C \<noteq> Object" by(auto dest: wf_Object_method_empty[OF wf])
      with sub' False obtain C' where [simp]: "T2' = Class C'" 
	and sub': "P \<turnstile> C' \<preceq>\<^sup>* C" by(auto simp add: widen_Class)
      with Call_lemma[OF sees sub' wf] obtain D' Ts'' T' m'
	where "P \<turnstile> C' sees M': Ts''\<rightarrow>T' = m' in D'"
	and "P \<turnstile> Ts' [\<le>] Ts''"
	and "P \<turnstile> T' \<le> T" by auto
      moreover hence "\<not> is_external_call P (Class C') M' (length es)"
	by(blast dest: external_call_not_sees_method[OF wf])
      moreover note sub wtp wto' CallObj
      ultimately show ?thesis by(auto intro: widens_trans)
    qed
  next
    case CallParams
    with wto IHp sees sub iec show ?thesis by(fastsimp intro: widens_trans)
  next
    case Call
    with sees wte1 seescall wto ha show ?thesis
      by(auto dest: sees_method_fun split: heapobj.split_asm)
  qed
next
  case (WTrt1CallNT E2 obj es Ts M' T)
  note IHo = `call obj = \<lfloor>(a, M, vs)\<rfloor> \<Longrightarrow> \<exists>T2'. P,E2,h \<turnstile>1 inline_call e1 obj : T2' \<and> P \<turnstile> T2' \<le> NT`
  note IHp = `calls es = \<lfloor>(a, M, vs)\<rfloor> \<Longrightarrow> \<exists>Ts'. P,E2,h \<turnstile>1 inline_calls e1 es [:] Ts' \<and> P \<turnstile> Ts' [\<le>] Ts`
  note wto = `P,E2,h \<turnstile>1 obj : NT`
  note wtp = `P,E2,h \<turnstile>1 es [:] Ts`
  from `call (obj\<bullet>M'(es)) = \<lfloor>(a, M, vs)\<rfloor>` show ?case
  proof(cases rule: call_callE)
    case CallObj
    with IHo wtp show ?thesis by auto
  next
    case CallParams
    with IHp wto show ?thesis by auto
  next
    case Call
    with wto have False by(auto split: heapobj.split_asm)
    thus ?thesis ..
  qed
next
  case (WTrt1CallExternal E e T es Ts M' U)
  note IHo = `call e = \<lfloor>(a, M, vs)\<rfloor> \<Longrightarrow> \<exists>T2'. P,E,h \<turnstile>1 inline_call e1 e : T2' \<and> P \<turnstile> T2' \<le> T`
  note IHp = `calls es = \<lfloor>(a, M, vs)\<rfloor> \<Longrightarrow> \<exists>Ts'. P,E,h \<turnstile>1 inline_calls e1 es [:] Ts' \<and> P \<turnstile> Ts' [\<le>] Ts`
  note wto = `P,E,h \<turnstile>1 e : T`
  note wtp = `P,E,h \<turnstile>1 es [:] Ts`
  note wtext = `P \<turnstile> T\<bullet>M'(Ts) :: U`
  from `call (e\<bullet>M'(es)) = \<lfloor>(a, M, vs)\<rfloor>` show ?case
  proof(cases rule: call_callE)
    case CallObj
    from IHo[OF this] obtain T' where wte: "P,E,h \<turnstile>1 inline_call e1 e : T'" "P \<turnstile> T' \<le> T" by auto
    show ?thesis
    proof(cases "T' = NT")
      case True
      with wte wtp CallObj show ?thesis by(auto split: heapobj.split_asm)
    next
      case False
      from external_WTrt_widen_mono[OF wtext `P \<turnstile> T' \<le> T` widens_refl this] `P,E,h \<turnstile>1 inline_call e1 e : T'` wtp CallObj
      show ?thesis by auto
    qed
  next
    case (CallParams v)
    from IHp[OF `calls es = \<lfloor>(a, M, vs)\<rfloor>`] obtain Ts'
      where wtes': "P,E,h \<turnstile>1 inline_calls e1 es [:] Ts'" "P \<turnstile> Ts' [\<le>] Ts" by blast
    show ?thesis
    proof(cases "T = NT")
      case True
      with wto wtes' CallParams show ?thesis by auto
    next
      case False
      from external_WTrt_widen_mono[OF wtext widen_refl `P \<turnstile> Ts' [\<le>] Ts` this] wtes' CallParams wto
      show ?thesis by auto
    qed
  next
    case Call
    with wto seescall ha external_WT_is_external_call[OF wtext] have False
      by(auto dest: external_call_not_sees_method[OF wf])
    thus ?thesis ..
  qed
next
  case WTrt1Block thus ?case by auto
next
  case (WTrt1Synchronized E2 e T e2 T2 V)
  from `call (sync\<^bsub>V\<^esub> (e) e2) = \<lfloor>(a, M, vs)\<rfloor>` `call e = \<lfloor>(a, M, vs)\<rfloor> \<Longrightarrow> \<exists>T2'. P,E2,h \<turnstile>1 inline_call e1 e : T2' \<and> P \<turnstile> T2' \<le> T`
  obtain T' where "P,E2,h \<turnstile>1 inline_call e1 e : T'" "P \<turnstile> T' \<le> T" by auto
  moreover with `is_refT T` have "is_refT T'" by(auto intro: widen_refT)
  ultimately show ?case using `P,(E2 @ [Class Object]),h \<turnstile>1 e2 : T2`
    by(cases "T' = NT")(auto)
next
  case WTrt1SynchronizedNT thus ?case by auto
next
  case WTrt1InSynchronized thus ?case by auto
next
  case WTrt1Seq thus ?case by auto
next
  case WTrt1Cond thus ?case by auto
next
  case WTrt1While thus ?case by auto
next
  case (WTrt1Throw E2 e T' T)
  from `call (throw e) = \<lfloor>(a, M, vs)\<rfloor>` `call e = \<lfloor>(a, M, vs)\<rfloor> \<Longrightarrow> \<exists>T2'. P,E2,h \<turnstile>1 inline_call e1 e : T2' \<and> P \<turnstile> T2' \<le> T'`
  obtain T'' where "P,E2,h \<turnstile>1 inline_call e1 e : T''" "P \<turnstile> T'' \<le> T'" by auto
  moreover with `P \<turnstile> T' \<le> Class Throwable` have "P \<turnstile> T'' \<le> Class Throwable" by(auto intro: widen_trans)
  ultimately show ?case by auto
next
  case WTrt1Try thus ?case by(auto intro: widen_trans)
next
  case WTrt1Nil thus ?case by simp
next
  case (WTrt1Cons E2 e T es Ts)
  note IH1 = `call e = \<lfloor>(a, M, vs)\<rfloor> \<Longrightarrow> \<exists>T2'. P,E2,h \<turnstile>1 inline_call e1 e : T2' \<and> P \<turnstile> T2' \<le> T`
  note IH2 = `calls es = \<lfloor>(a, M, vs)\<rfloor> \<Longrightarrow> \<exists>Ts'. P,E2,h \<turnstile>1 inline_calls e1 es [:] Ts' \<and> P \<turnstile> Ts' [\<le>] Ts`
  note wt1 = `P,E2,h \<turnstile>1 e : T`
  note wt2 = `P,E2,h \<turnstile>1 es [:] Ts`
  note call = `calls (e # es) = \<lfloor>(a, M, vs)\<rfloor>`
  show ?case
  proof(cases "is_val e")
    case True
    with call have "calls es = \<lfloor>(a, M, vs)\<rfloor>" by simp
    from IH2[OF this] obtain Ts' where "P,E2,h \<turnstile>1 inline_calls e1 es [:] Ts'" "P \<turnstile> Ts' [\<le>] Ts" by auto
    with wt1 True have "P,E2,h \<turnstile>1 inline_calls e1 (e # es) [:] T # Ts'" "P \<turnstile> (T # Ts') [\<le>] (T # Ts)" by auto
    thus ?thesis by blast
  next
    case False
    with call have "call e = \<lfloor>(a, M, vs)\<rfloor>" by simp
    from IH1[OF this] obtain T' where "P,E2,h \<turnstile>1 inline_call e1 e : T'" "P \<turnstile> T' \<le> T" by auto
    with wt2 False have "P,E2,h \<turnstile>1 inline_calls e1 (e # es) [:] T' # Ts" "P \<turnstile> (T' # Ts) [\<le>] (T # Ts)"
      by(auto intro: widens_refl)
    thus ?thesis by blast
  qed
qed

lemma clearInitBlock_cong1: "fst (clearInitBlock e xs) = fst (clearInitBlock e xs')"
  and clearInitBlocks_cong1: "fst (clearInitBlocks es xs) = fst (clearInitBlocks es xs')"
apply(induct e and es arbitrary: xs xs' and xs xs')
apply(auto simp add: split_beta)
done

lemma length_fst_clearInitBlocks [simp]: "length (fst (clearInitBlocks es xs)) = length es"
apply(induct es)
apply(auto simp add: split_def)
done

lemma WTrt1_clearInitBlock: "P,E,h \<turnstile>1 e : T \<Longrightarrow> P,E,h \<turnstile>1 fst (clearInitBlock e xs) : T"
  and WTrts1_clearInitBlocks: "P,E,h \<turnstile>1 es [:] Ts \<Longrightarrow> P,E,h \<turnstile>1 fst (clearInitBlocks es xs) [:] Ts"
apply(induct rule: WTrt1_WTrts1.inducts)
apply(auto simp add: split_beta)
apply(simp cong: clearInitBlock_cong1)
done

lemma env_exp_inline_call: "call e = \<lfloor>(a, M, vs)\<rfloor>  \<Longrightarrow> \<exists>E. env_exp (inline_call e' e) = env_exp e @ env_exp e' @ E"
  and env_exps_inline_calls: "calls es = \<lfloor>(a, M, vs)\<rfloor> \<Longrightarrow> \<exists>E. env_exps (inline_calls e' es) = env_exps es @ env_exp e' @ E"
apply(induct e and es)
apply(fastsimp simp add: is_vals_conv)+
done

lemma env_exp_clearInitBlock: "env_exp (fst (clearInitBlock e xs)) = env_exp e"
  and env_exps_clearInitBlocks: "env_exps (fst (clearInitBlocks es xs)) = env_exps es"
apply(induct e and es arbitrary: xs and xs)
apply(auto simp add: split_beta)
done

lemma is_val_clearInitBlock [simp]: "is_val (fst (clearInitBlock e xs)) = is_val e"
  and is_vals_clearInitBlocks [simp]: "is_vals (fst (clearInitBlocks es xs)) = is_vals es"
apply(induct e and es arbitrary: xs and xs)
apply(auto simp add: split_beta)
done

lemma A1_clearInitBlock [simp]: "\<A>1 (fst (clearInitBlock e xs)) = \<A>1 e"
  and As1_clearInitBlocks [simp]: "\<A>s1 (fst (clearInitBlocks es xs)) = \<A>s1 es"
apply(induct e and es arbitrary: xs and xs)
apply(auto simp add: split_beta)
done

lemma clearInitblock_lconf_defass:
  "\<lbrakk> P,E,h \<turnstile>1 e : T; P,h,A \<turnstile>1 xs (:\<le>) E @ env_exp e; \<D>1 (length E) e \<lfloor>A\<rfloor>;
     \<B> e (length E); length E + max_vars e \<le> length xs \<rbrakk> 
  \<Longrightarrow> \<exists>A'. P,h,A' \<turnstile>1 snd (clearInitBlock e xs) (:\<le>) E @ env_exp e \<and>
          \<D>1 (length E) (fst (clearInitBlock e xs)) \<lfloor>A'\<rfloor> \<and>
          \<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>1 e \<and> A \<inter> {0..<length E} \<subseteq> A'"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?concl e xs E A")
 
  and clearInitblocks_lconf_defass:
  "\<lbrakk> P,E,h \<turnstile>1 es [:] Ts; P,h,A \<turnstile>1 xs (:\<le>) E @ env_exps es; \<D>s1 (length E) es \<lfloor>A\<rfloor>; 
     \<B>s es (length E); length E + max_varss es \<le> length xs \<rbrakk> 
  \<Longrightarrow> \<exists>A'. P,h,A' \<turnstile>1 snd (clearInitBlocks es xs) (:\<le>) E @ env_exps es \<and>
          \<D>s1 (length E) (fst (clearInitBlocks es xs)) \<lfloor>A'\<rfloor> \<and>
          \<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> \<A>s1 es \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> \<A>s1 es \<and> A \<inter> {0..<length E} \<subseteq> A'"
proof(induct arbitrary: xs A and xs A rule: WTrt1_WTrts1.inducts)
  case (WTrt1Block E T e T' vo V cr)
  note IH = `\<And>A xs. \<lbrakk> P,h,A \<turnstile>1 xs (:\<le>) (E @ [T]) @ env_exp e; \<D>1 (length (E @ [T])) e \<lfloor>A\<rfloor>;
                      \<B> e (length (E @ [T])); length (E @ [T]) + max_vars e \<le> length xs\<rbrakk>
             \<Longrightarrow> ?concl e xs (E @ [T]) A`
  note D = `\<D>1 (length E) {V:T=vo; e}\<^bsub>cr\<^esub> \<lfloor>A\<rfloor>`
  note B = `\<B> {V:T=vo; e}\<^bsub>cr\<^esub> (length E)`
  hence [simp]: "V = length E" by simp
  note lconf = `P,h,A \<turnstile>1 xs (:\<le>) E @ env_exp {V:T=vo; e}\<^bsub>cr\<^esub>`
  hence lconf': "P,h,A \<turnstile>1 xs (:\<le>) (E @ [T]) @ env_exp e" by simp
  from `length E + max_vars {V:T=vo; e}\<^bsub>cr\<^esub> \<le> length xs`
  have len: "length (E @ [T]) + max_vars e \<le> length xs" by simp
  show ?case
  proof(cases vo)
    case None
    with IH[OF lconf' _ _ len] D B show ?thesis
      by(fastsimp simp add: split_beta hyperUn_assoc[symmetric] intro: sqUn_lem)
  next
    case (Some v)
    note Some[simp]
    from lconf' len `case vo of None \<Rightarrow> True | \<lfloor>v\<rfloor> \<Rightarrow> \<exists>T'. typeof\<^bsub>h\<^esub> v = \<lfloor>T'\<rfloor> \<and> P \<turnstile> T' \<le> T`
    have "P,h,(insert V A) \<turnstile>1 xs[V := v] (:\<le>) (E @ [T]) @ env_exp e"
      by(auto simp add: lconf1_def conf_def nth_list_update)
    from IH[OF this] D B len obtain A'
      where lconf': "P,h,A' \<turnstile>1 snd (clearInitBlock e (xs[V := v])) (:\<le>) (E @ [T]) @ env_exp e"
      and D': "\<D>1 (Suc (length E)) (fst (clearInitBlock e (xs[V := v]))) \<lfloor>A'\<rfloor>"
      and sub1: "\<lfloor>insert V A \<inter> {0..<Suc (length E)}\<rfloor> \<squnion> \<A>1 e \<sqsubseteq> \<lfloor>A' \<inter> {0..<Suc (length E)}\<rfloor> \<squnion> \<A>1 e"
      and sub2: "insert V A \<inter> {0..<Suc (length E)} \<subseteq> A'" by auto
    from sub1 have "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> (\<A>1 e \<ominus> length E) \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> (\<A>1 e \<ominus> length E)"
      by(auto simp add: hyperset_defs)
    with lconf' D' sub2 show ?thesis by(fastsimp simp add: split_beta)
  qed
next
  case (WTrt1InSynchronized E a T e T' V)
  note IH = `\<And>A xs. \<lbrakk> P,h,A \<turnstile>1 xs (:\<le>) (E @ [Class Object]) @ env_exp e; \<D>1 (length (E @ [Class Object])) e \<lfloor>A\<rfloor>;
                      \<B> e (length (E @ [Class Object])); length (E @ [Class Object]) + max_vars e \<le> length xs\<rbrakk>
             \<Longrightarrow> ?concl e xs (E @ [Class Object]) A`
  note D = `\<D>1 (length E) (insync\<^bsub>V\<^esub> (a) e) \<lfloor>A\<rfloor>`
  note B = `\<B> (insync\<^bsub>V\<^esub> (a) e) (length E)`
  hence [simp]: "V = length E" by simp
  note lconf = `P,h,A \<turnstile>1 xs (:\<le>) E @ env_exp (insync\<^bsub>V\<^esub> (a) e)`
  hence lconf': "P,h,A \<turnstile>1 xs (:\<le>) (E @ [Class Object]) @ env_exp e" by simp
  from `length E + max_vars (insync\<^bsub>V\<^esub> (a) e) \<le> length xs`
  have len: "length (E @ [Class Object]) + max_vars e \<le> length xs" by simp
  from IH[OF lconf' _ _ len] D B obtain A'
    where lconf': "P,h,A' \<turnstile>1 snd (clearInitBlock e xs) (:\<le>) E @ Class Object # env_exp e"
    and D': "\<D>1 (Suc (length E)) (fst (clearInitBlock e xs)) \<lfloor>A'\<rfloor>"
    and sub1: "\<lfloor>A \<inter> {0..<Suc (length E)}\<rfloor> \<squnion> \<A>1 e \<sqsubseteq> \<lfloor>A' \<inter> {0..<Suc (length E)}\<rfloor> \<squnion> \<A>1 e"
    and sub2: "A \<inter> {0..<Suc (length E)} \<subseteq> A'" by auto
  from sub1 have "\<lfloor>A \<inter> {0..<length E}\<rfloor> \<squnion> (\<A>1 e \<ominus> length E) \<sqsubseteq> \<lfloor>A' \<inter> {0..<length E}\<rfloor> \<squnion> (\<A>1 e \<ominus> length E)"
    by(auto simp add: hyperset_defs)
  with lconf' D' sub2 show ?case by(fastsimp simp add: split_beta)
qed(fastsimp simp add: split_beta hyperUn_assoc[symmetric] intro: D1_mono' Ds1_mono' sqUn_lem)+

lemma max_varss_map_Val [simp]: "max_varss (map Val vs) = 0"
apply(induct vs)
apply auto
done

lemma inline_call_eq_Val_A1 [dest]: "inline_call e' e = Val v \<Longrightarrow> \<A>1 e = \<lfloor>{}\<rfloor>"
by(cases e)(auto split: split_if_asm simp add: is_vals_conv)

lemma inline_calls_eq_Val_As1 [dest]: "inline_calls e' es = map Val vs \<Longrightarrow> \<A>s1 es = \<lfloor>{}\<rfloor>"
apply(induct es arbitrary: vs)
apply(auto split: split_if_asm simp add: is_vals_conv)
done

lemma hyperUn_comm [simp]: "A \<squnion> B = B \<squnion> A"
by(auto simp add: hyperset_defs)

lemma hyeprUn_leftComm [simp]: "A \<squnion> (B \<squnion> C) = B \<squnion> (A \<squnion> C)"
by(auto simp add: hyperset_defs)

lemma A1_inline_call [intro]: "\<A>1 e \<sqsubseteq> \<A>1 (inline_call e' e)"
  and As1_inline_calls [intro]: "\<A>s1 es \<sqsubseteq> \<A>s1 (inline_calls e' es)"
apply(induct e and es)
apply(auto intro: sqUn_lem simp add: is_vals_conv)
apply(auto simp add: hyperset_defs)
done

lemma [simp]: "\<lfloor>{}\<rfloor> \<squnion> B = B"
by(auto)

lemma [simp]: "A \<exclamdown> B \<sqsubseteq> A"
by(auto simp add: hyperset_defs)

lemma [simp]: "\<lfloor>{}\<rfloor> \<sqsubseteq> A"
by(auto simp add: hyperset_defs)

lemma Ds1_map_Val [simp]: "\<D>s1 n (map Val vs) A"
by(induct vs)auto

lemma assumes De': "\<And>n. \<D>1 n e' \<lfloor>{}\<rfloor>"
  shows defass_inline_call: "\<D>1 n e A \<Longrightarrow> \<D>1 n (inline_call e' e) A"
  and defass_inline_calls: "\<D>s1 n es A \<Longrightarrow> \<D>s1 n (inline_calls e' es) A"
proof(induct e and es arbitrary: n A and n A)
  case (AAss exp1 exp2 exp3)
  have "\<A>1 exp2 \<squnion> (\<A>1 exp1 \<squnion> (A \<exclamdown> {0..<n})) \<sqsubseteq> \<A>1 exp2 \<squnion> (\<A>1 (inline_call e' exp1) \<squnion> (A \<exclamdown> {0..<n}))"
    by(blast intro: sqUn_lem2 sqUn_lem)
  with AAss show ?case by(fastsimp intro: D1_mono' Ds1_mono' sqUn_lem)
next
  case Call thus ?case using De'
    by(fastsimp simp add: is_vals_conv intro: D1_mono' Ds1_mono' sqUn_lem)
qed(fastsimp intro: D1_mono' Ds1_mono' sqUn_lem)+

lemma WT1_expr_locks: "P,E \<turnstile>1 e :: T \<Longrightarrow> expr_locks e = (\<lambda>a. 0)"
  and WTs1_expr_lockss: "P,E \<turnstile>1 es [::] Ts \<Longrightarrow> expr_lockss es = (\<lambda>a. 0)"
apply(induct rule: WT1_WTs1.inducts)
apply(auto)
done

lemma expr_locks_blocks1 [simp]: "expr_locks (blocks1 n Ts e) = expr_locks e"
apply(induct Ts arbitrary: n)
apply(auto)
done

lemma WTrt1_blocks1 [intro]: "P,E @ Ts,h \<turnstile>1 e : T \<Longrightarrow> P,E,h \<turnstile>1 blocks1 (length E) Ts e : T"
proof(induct Ts arbitrary: E)
  case Nil thus ?case by simp
next
  case (Cons T' Ts)
  note IH = `\<And>E. P,E @ Ts,h \<turnstile>1 e : T \<Longrightarrow> P,E,h \<turnstile>1 blocks1 (length E) Ts e : T`
  from `P,E @ T' # Ts,h \<turnstile>1 e : T` have "P,(E @ [T']) @ Ts,h \<turnstile>1 e : T" by simp
  from IH[OF this] show ?case by auto
qed

lemma env_exp_blocks1 [simp]: "env_exp (blocks1 n Ts e) = Ts @ env_exp e"
apply(induct Ts arbitrary: n)
apply(auto)
done

lemma WTrts_map_Val_confs: "P,E,h \<turnstile>1 map Val vs [:] Ts \<Longrightarrow> P,h \<turnstile> vs [:\<le>] Ts"
apply(induct vs arbitrary: Ts)
apply(auto)
done

lemma D1_blocks1 [simp]: "\<D>1 n (blocks1 m Ts e) A = \<D>1 (n + length Ts) e A"
apply(induct Ts arbitrary: n m)
apply(auto)
done

lemma D1_None: "\<D>1 n e None = \<D>1 m e None"
  and Ds1_None: "\<D>s1 n es None = \<D>s1 m es None"
apply(induct e and es arbitrary: n m and n m)
apply(auto)
apply(blast)+
done

lemma D_D1_None: "\<D> e None \<Longrightarrow> \<D>1 n e None"
  and Ds_Ds1_None: "\<D>s es None \<Longrightarrow> \<D>s1 n es None"
apply(induct e and es)
apply(auto intro: D1_mono' cong: D1_None)
done

lemma [simp]: "syncvarss (map Val vs)"
by(induct vs) auto
lemma A_A1: "\<lbrakk> \<B> e n; syncvars e \<rbrakk> \<Longrightarrow> \<A> e = \<A>1 e"
  and As_As1: "\<lbrakk> \<B>s es n; syncvarss es \<rbrakk> \<Longrightarrow> \<A>s es = \<A>s1 es"
apply(induct e and es arbitrary: n and n)
apply(auto)
apply(fastsimp dest: A_fv simp add: hyperset_defs)+
done

lemma [simp]: "A \<exclamdown> B \<exclamdown> B = A \<exclamdown> B"
apply(auto simp add: hyperRestrict_def)
done

lemma restrict_lem: "C \<subseteq> D \<Longrightarrow> A \<squnion> B \<exclamdown> C \<sqsubseteq> B \<squnion> (A \<exclamdown> D)"
apply(auto simp add: hyperset_defs)
done

lemma restrict_lem2: "A \<subseteq> B \<Longrightarrow> C \<exclamdown> A \<sqsubseteq> C \<exclamdown> B"
by(auto simp add: hyperRestrict_def)

lemma fixes e :: "('a,'b) exp"
  and es :: "('a, 'b) exp list"
  shows D_fv: "\<D> e A \<Longrightarrow> \<D> e (A \<exclamdown> (fv e))"
  and Ds_fvs: "\<D>s es A \<Longrightarrow> \<D>s es (A \<exclamdown> (fvs es))"
proof(induct e and es arbitrary: A and A)
  case Var thus ?case by(simp add: hyperset_defs)
next
  case AAss thus ?case
    by(auto intro: D_mono' Ds_mono' restrict_lem2 restrict_lem restrict_lem3)
next
  case Block thus ?case by(fastsimp simp add: hyperset_defs intro: D_mono')
next
  case Synchronized thus ?case by(fastsimp simp add: hyperset_defs intro: D_mono')
next
  case InSynchronized thus ?case by(fastsimp simp add: hyperset_defs intro: D_mono')
next
  case TryCatch thus ?case by(fastsimp simp add: hyperset_defs intro: D_mono')
qed(auto intro: D_mono' Ds_mono' restrict_lem2 restrict_lem)

lemma D_D1: "\<lbrakk> \<B> e n; syncvars e; \<D> e A; fv e \<subseteq> {0..<n} \<rbrakk> \<Longrightarrow> \<D>1 n e (A \<exclamdown> {0..<n})"
  and Ds_Ds1: "\<lbrakk> \<B>s es n; syncvarss es; \<D>s es A; fvs es \<subseteq> {0..<n} \<rbrakk> \<Longrightarrow> \<D>s1 n es (A \<exclamdown> {0..<n})"
proof(induct e and es arbitrary: n A and n A)
  case Var thus ?case by(fastsimp simp add: hyperset_defs hyperRestrict_def)
next
  case AAss thus ?case
    by(fastsimp intro: Ds1_mono' D1_mono' restrict_lem restrict_lem2 restrict_lem3 simp add: A_A1)
next 
  case (Block V T vo e cr)
  note IH = `\<And>n A. \<lbrakk>\<B> e n; syncvars e; \<D> e A; fv e \<subseteq> {0..<n}\<rbrakk> \<Longrightarrow> \<D>1 n e (A \<exclamdown> {0..<n})`
  from `\<B> {V:T=vo; e}\<^bsub>cr\<^esub> n` have [simp]: "V = n" and B: "\<B> e (Suc n)" by auto
  from `fv {V:T=vo; e}\<^bsub>cr\<^esub> \<subseteq> {0..<n}` have fv: "fv e \<subseteq> {0..<Suc n}" by(auto)
  from `syncvars {V:T=vo; e}\<^bsub>cr\<^esub>` have sync: "syncvars e" by simp
  show ?case
  proof(cases vo)
    case None
    note None[simp]
    from `\<D> {V:T=vo; e}\<^bsub>cr\<^esub> A` have D: "\<D> e (A \<ominus> n)" by simp
    have "\<And>A. (A-{n}) \<inter> {0..<Suc n} = A \<inter> {0..<n}" by(auto)
    with IH[OF B sync D fv] have "\<D>1 (Suc n) e (A \<exclamdown> {0..<n})"
      by(clarsimp simp add: hyperset_defs)
    thus ?thesis by simp
  next
    case (Some v)
    note Some[simp]
    from `\<D> {V:T=vo; e}\<^bsub>cr\<^esub> A` have D: "\<D> e (A \<squnion> \<lfloor>{n}\<rfloor>)" by simp
    have "A \<squnion> \<lfloor>{n}\<rfloor> \<exclamdown> {0..<Suc n} = \<lfloor>{n}\<rfloor> \<squnion> (A \<exclamdown> {0..<n})" by(auto simp add: hyperset_defs)
    with IH[OF B sync D fv] show ?thesis by(simp)
  qed
next
  case (Synchronized V e1 e2)
  note IH1 = `\<And>n A. \<lbrakk>\<B> e1 n; syncvars e1; \<D> e1 A; fv e1 \<subseteq> {0..<n}\<rbrakk> \<Longrightarrow> \<D>1 n e1 (A \<exclamdown> {0..<n})`
  note IH2 = `\<And>n A. \<lbrakk>\<B> e2 n; syncvars e2; \<D> e2 A; fv e2 \<subseteq> {0..<n}\<rbrakk> \<Longrightarrow> \<D>1 n e2 (A \<exclamdown> {0..<n})`
  from `\<B> (sync\<^bsub>V\<^esub> (e1) e2) n` have [simp]: "V = n" and B1: "\<B> e1 n" and B2: "\<B> e2 (Suc n)" by auto
  from `fv (sync\<^bsub>V\<^esub> (e1) e2) \<subseteq> {0..<n}` have fv1: "fv e1 \<subseteq> {0..<n}" 
    and fv2: "fv e2 \<subseteq> {0..<n}" and fv2': "fv e2 \<subseteq> {0..<Suc n}" by auto
  from `\<D> (sync\<^bsub>V\<^esub> (e1) e2) A` have D1: "\<D> e1 A" and D2: "\<D> e2 (A \<squnion> \<A> e1)" by auto
  from `syncvars (sync\<^bsub>V\<^esub> (e1) e2)` have sync1: "syncvars e1"
    and sync2: "syncvars e2" and V: "V \<notin> fv e2" by auto
  from IH1[OF B1 sync1 D1 fv1] have "\<D>1 n e1 (A \<exclamdown> {0..<n})" .
  moreover from D2 have "\<D> e2 (A \<squnion> \<A> e1 \<exclamdown> fv e2)" by(rule D_fv)
  from IH2[OF B2 sync2 this fv2'] have D2': "\<D>1 (Suc n) e2 (A \<squnion> \<A> e1 \<exclamdown> fv e2 \<exclamdown> {0..<Suc n})" .
  from B1 sync1 fv2 have "A \<squnion> \<A> e1 \<exclamdown> fv e2 \<exclamdown> {0..<Suc n} \<sqsubseteq> \<A>1 e1 \<squnion> (A \<exclamdown> {0..<n})"
    by(auto simp add: hyperRestrict_def hyperset_defs A_A1)
  with D2' have "\<D>1 (Suc n) e2 (\<A>1 e1 \<squnion> (A \<exclamdown> {0..<n}))" by(rule D1_mono') 
  ultimately show ?case by simp
next
  case (InSynchronized V a e)
  note IH = `\<And>n A. \<lbrakk>\<B> e n; syncvars e; \<D> e A; fv e \<subseteq> {0..<n}\<rbrakk> \<Longrightarrow> \<D>1 n e (A \<exclamdown> {0..<n})`
  from `\<B> (insync\<^bsub>V\<^esub> (a) e) n` have [simp]: "V = n" and B: "\<B> e (Suc n)" by auto
  from `fv (insync\<^bsub>V\<^esub> (a) e) \<subseteq> {0..<n}` have fv: "fv e \<subseteq> {0..<n}" and fv': "fv e \<subseteq> {0..<Suc n}" by auto
  from `syncvars (insync\<^bsub>V\<^esub> (a) e)` have sync: "syncvars e" and V: "V \<notin> fv e" by auto
  from `\<D> (insync\<^bsub>V\<^esub> (a) e) A` have D1: "\<D> e A" by auto
  hence "\<D> e (A \<exclamdown> fv e)" by(rule D_fv)
  from IH[OF B sync this fv'] have "\<D>1 (Suc n) e (A \<exclamdown> fv e \<exclamdown> {0..<Suc n})" .
  moreover from fv have "A \<exclamdown> fv e \<exclamdown> {0..<Suc n} \<sqsubseteq> A \<exclamdown> {0..<n}"
    by(auto simp add: hyperset_defs hyperRestrict_def)
  ultimately show ?case by(auto intro: D1_mono')
next
  case (TryCatch e1 C V e2)
  note IH1 = `\<And>n A. \<lbrakk>\<B> e1 n; syncvars e1; \<D> e1 A; fv e1 \<subseteq> {0..<n}\<rbrakk> \<Longrightarrow> \<D>1 n e1 (A \<exclamdown> {0..<n})`
  note IH2 = `\<And>n A. \<lbrakk>\<B> e2 n; syncvars e2; \<D> e2 A; fv e2 \<subseteq> {0..<n}\<rbrakk> \<Longrightarrow> \<D>1 n e2 (A \<exclamdown> {0..<n})`
  from `\<B> (try e1 catch(C V) e2) n` have [simp]: "V = n"
    and B1: "\<B> e1 n" and B2: "\<B> e2 (Suc n)" by auto
  from `syncvars (try e1 catch(C V) e2)` have sync1: "syncvars e1" and sync2: "syncvars e2" by auto
  from `fv (try e1 catch(C V) e2) \<subseteq> {0..<n}` have fv1: "fv e1 \<subseteq> {0..<n}" and fv2: "fv e2 \<subseteq> {0..<Suc n}" by auto
  from `\<D> (try e1 catch(C V) e2) A` have D1: "\<D> e1 A" and D2: "\<D> e2 (\<lfloor>{n}\<rfloor> \<squnion> A)" by auto
  from IH1[OF B1 sync1 D1 fv1] IH2[OF B2 sync2 D2 fv2] show ?case
    by(auto simp add: hyperset_defs intro: D1_mono')
qed(fastsimp intro: Ds1_mono' D1_mono' restrict_lem simp add: A_A1)+

lemma assumes wf: "wf_prog wfmd P"
  and ha: "h a = \<lfloor>Obj C fs\<rfloor>"
  and sees: "P \<turnstile> C sees M : Ts \<rightarrow> T = meth in D"
  shows call_WTrt_vs_conform: "\<lbrakk> P,E,h \<turnstile>1 e : T'; call e = \<lfloor>(a, M, vs)\<rfloor> \<rbrakk> \<Longrightarrow> P,h \<turnstile> vs [:\<le>] Ts"
  and calls_WTrts_vs_conform: "\<lbrakk> P,E,h \<turnstile>1 es [:] Ts'; calls es = \<lfloor>(a, M, vs)\<rfloor> \<rbrakk> \<Longrightarrow> P,h \<turnstile> vs [:\<le>] Ts"
apply(induct rule: WTrt1_WTrts1.inducts)
apply(insert ha sees)
apply(auto split: split_if_asm heapobj.split_asm simp add: is_vals_conv confs_conv_map dest: sees_method_fun)
apply(auto dest: external_WT_is_external_call external_call_not_sees_method[OF wf])
done

lemma WT1_fv: "\<lbrakk> P,E \<turnstile>1 e :: T; \<B> e (length E); syncvars e \<rbrakk> \<Longrightarrow> fv e \<subseteq> {0..<length E}"
  and WTs1_fvs: "\<lbrakk> P,E \<turnstile>1 es [::] Ts; \<B>s es (length E); syncvarss es \<rbrakk> \<Longrightarrow> fvs es \<subseteq> {0..<length E}"
proof(induct rule: WT1_WTs1.inducts)
  case (WT1Synchronized E e1 T e2 T' V)
  note IH1 = `\<lbrakk>\<B> e1 (length E); syncvars e1\<rbrakk> \<Longrightarrow> fv e1 \<subseteq> {0..<length E}`
  note IH2 = `\<lbrakk>\<B> e2 (length (E @ [Class Object])); syncvars e2\<rbrakk> \<Longrightarrow> fv e2 \<subseteq> {0..<length (E @ [Class Object])}`
  from `\<B> (sync\<^bsub>V\<^esub> (e1) e2) (length E)` have [simp]: "V = length E"
    and B1: "\<B> e1 (length E)" and B2: "\<B> e2 (Suc (length E))" by auto
  from `syncvars (sync\<^bsub>V\<^esub> (e1) e2)` have sync1: "syncvars e1" and sync2: "syncvars e2" and V: "V \<notin> fv e2" by auto
  have "fv e2 \<subseteq> {0..<length E}"
  proof
    fix x
    assume x: "x \<in> fv e2"
    with V have "x \<noteq> length E" by auto
    moreover from IH2 B2 sync2 have "fv e2 \<subseteq> {0..<Suc (length E)}" by auto
    with x have "x < Suc (length E)" by auto
    ultimately show "x \<in> {0..<length E}" by auto
  qed
  with IH1[OF B1 sync1] show ?case by(auto)
next
  case (WT1Cond E e e1 T1 e2 T2 T)
  thus ?case by(auto del: subsetI)
qed fastsimp+

lemma blocks1_WT: "\<lbrakk> P,Env @ Ts \<turnstile>1 body :: T; set Ts \<subseteq> is_type P \<rbrakk> \<Longrightarrow> P,Env \<turnstile>1 blocks1 (length Env) Ts body :: T"
proof(induct n\<equiv>"length Env" Ts body arbitrary: Env rule: blocks1.induct)
  case 1 thus ?case by simp
next
  case (2 n T' Ts e)
  note IH = `\<And>Env. \<lbrakk>P,Env @ Ts \<turnstile>1 e :: T; set Ts \<subseteq> is_type P; Suc n = length Env\<rbrakk>
              \<Longrightarrow> P,Env \<turnstile>1 blocks1 (length Env) Ts e :: T`
  from `set (T' # Ts) \<subseteq> is_type P` have "set Ts \<subseteq> is_type P" "is_type P T'" by(auto simp add: mem_def)
  moreover from `P,Env @ T' # Ts \<turnstile>1 e :: T` have "P,(Env @ [T']) @ Ts \<turnstile>1 e :: T" by simp
  note IH[OF this] `n = length Env`
  ultimately show ?case by auto
qed



primrec jump_ok :: "instr list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where "jump_ok [] n n' = True"
| "jump_ok (x # xs) n n' = (jump_ok xs (Suc n) n' \<and> 
                           (case x of IfFalse m \<Rightarrow> - int n \<le> m \<and> m \<le> int (n' + length xs)
                                       | Goto m \<Rightarrow> - int n \<le> m \<and> m \<le> int (n' + length xs)
                                            | _ \<Rightarrow> True))"

lemma jump_ok_append [simp]:
  "jump_ok (xs @ xs') n n' \<longleftrightarrow> jump_ok xs n (n' + length xs') \<and> jump_ok xs' (n + length xs) n'"
apply(induct xs arbitrary: n)
 apply(simp)
apply(auto split: instr.split)
done

lemma jump_ok_GotoD:
  "\<lbrakk> jump_ok ins n n'; ins ! pc = Goto m; pc < length ins \<rbrakk> \<Longrightarrow> - int (pc + n) \<le> m \<and> m < int (length ins - pc + n')"
apply(induct ins arbitrary: n n' pc)
 apply(simp)
apply(clarsimp)
apply(case_tac pc)
apply(fastsimp)+
done

lemma jump_ok_IfFalseD:
  "\<lbrakk> jump_ok ins n n'; ins ! pc = IfFalse m; pc < length ins \<rbrakk> \<Longrightarrow> - int (pc + n) \<le> m \<and> m < int (length ins - pc + n')"
apply(induct ins arbitrary: n n' pc)
 apply(simp)
apply(clarsimp)
apply(case_tac pc)
apply(fastsimp)+
done

lemma compE2_jump_ok [intro!]: "jump_ok (compE2 e) n (Suc n')"
  and compEs2_jump_ok [intro!]: "jump_ok (compEs2 es) n (Suc n')"
apply(induct e and es arbitrary: n n' and n n')
apply(auto split: bop.split)
done

lemma WTs1_snoc_cases:
  assumes wt: "P,E \<turnstile>1 es @ [e] [::] Ts"
  obtains T Ts' where "P,E \<turnstile>1 es [::] Ts'" "P,E \<turnstile>1 e :: T"
proof -
  from wt have "\<exists>T Ts'. P,E \<turnstile>1 es [::] Ts' \<and> P,E \<turnstile>1 e :: T"
    by(induct es arbitrary: Ts) auto
  thus thesis by(auto intro: that)
qed

declare compxE2_size_convs[simp del] compxEs2_size_convs[simp del]
declare compxE2_stack_xlift_convs[simp del] compxEs2_stack_xlift_convs[simp del]

lemma compE2_not_Return: "Return \<notin> set (compE2 e)"
  and compEs2_not_Return: "Return \<notin> set (compEs2 es)"
apply(induct e and es)
apply(auto split: bop.splits)
done

declare compxE2_size_convs[simp] compxEs2_size_convs[simp]
declare compxE2_stack_xlift_convs[simp] compxEs2_stack_xlift_convs[simp]

lemma red1_max_vars: "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> max_vars e' \<le> max_vars e"
  and reds1_max_varss: "P \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> max_varss es' \<le> max_varss es"
apply(induct rule: red1_reds1.inducts)
apply auto
done

lemma WTrt1_callD: "\<lbrakk> P,E,h \<turnstile>1 e : T; call e = \<lfloor>(a, M, vs)\<rfloor> \<rbrakk> \<Longrightarrow> h a \<noteq> None \<and> (synthesized_call P h (a, M, vs) \<or> (\<exists>C fs. h a = \<lfloor>Obj C fs\<rfloor> \<and> P \<turnstile> C has M))"
  and WTrts1_callsD: "\<lbrakk> P,E,h \<turnstile>1 es [:] Ts; calls es = \<lfloor>(a, M, vs)\<rfloor> \<rbrakk> \<Longrightarrow> h a \<noteq> None \<and> (synthesized_call P h (a, M, vs) \<or> (\<exists>C fs. h a = \<lfloor>Obj C fs\<rfloor> \<and> P \<turnstile> C has M))"
apply(induct rule: WTrt1_WTrts1.inducts)
apply(auto split: split_if_asm heapobj.split_asm simp add: synthesized_call_conv is_vals_conv)
apply(fastsimp simp add: is_vals_conv has_method_def dest: external_WT_is_external_call map_eq_imp_length_eq')+
done

lemma assumes wf: "wf_prog wf_md P"
  and ha: "h a = \<lfloor>Obj C fs\<rfloor>"
  and sees: "P \<turnstile> C sees M:Ts'\<rightarrow>T' = meth in D"
  shows WTrt_call_sees_length_params: "\<lbrakk> P,E,h \<turnstile>1 e : T; call e = \<lfloor>(a, M, vs)\<rfloor> \<rbrakk> \<Longrightarrow> length vs = length Ts'"
  and WTrts_calls_sees_length_params: "\<lbrakk> P,E,h \<turnstile>1 es [:] Ts; calls es = \<lfloor>(a, M, vs)\<rfloor> \<rbrakk> \<Longrightarrow> length vs = length Ts'"
apply(induct rule: WTrt1_WTrts1.inducts)
apply(insert wf ha sees)
apply(auto split: split_if_asm heapobj.split_asm simp add: is_vals_conv)
apply(fastsimp dest: WTrts1_same_size sees_method_fun widens_lengthD map_eq_imp_length_eq')
apply(fastsimp dest: external_call_not_sees_method[OF wf] external_WT_is_external_call)
done

lemma nat_fun_sum_eq_conv:
  fixes f :: "'a \<Rightarrow> nat"
  shows "(\<lambda>a. f a + g a) = (\<lambda>a. 0) \<longleftrightarrow> f = (\<lambda>a .0) \<and> g = (\<lambda>a. 0)"
apply(auto simp add: expand_fun_eq)
done

lemma WTs1_append:
  assumes wt: "P,Env \<turnstile>1 es @ es' [::] Ts"
  obtains Ts' Ts'' where "P,Env \<turnstile>1 es [::] Ts'" "P,Env \<turnstile>1 es' [::] Ts''"
proof -
  from wt have "\<exists>Ts' Ts''. P,Env \<turnstile>1 es [::] Ts' \<and> P,Env \<turnstile>1 es' [::] Ts''"
    by(induct es arbitrary: Ts) auto
  thus ?thesis by(auto intro: that)
qed

lemma B_extRet2J [simp]: "\<B> (extRet2J va) n"
by(cases va) simp_all

lemma red1_preserves_B: "\<lbrakk> P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<B> e n\<rbrakk> \<Longrightarrow> \<B> e' n"
  and reds1_preserves_Bs: "\<lbrakk> P \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; \<B>s es n\<rbrakk> \<Longrightarrow> \<B>s es' n"
apply(induct arbitrary: n and n rule: red1_reds1.inducts)
apply(auto)
done

inductive exsconf :: "J1_prog \<Rightarrow> heap \<Rightarrow> ty \<Rightarrow> expr1 \<times> locals1 \<Rightarrow> bool"
for P :: J1_prog and h :: heap and T :: ty 
where 
exsconfI:
  "\<lbrakk> P,([Class C]),h \<turnstile>1 e : T'; P \<turnstile> T' \<le> T; P,h,A \<turnstile>1 xs (:\<le>) Class C # env_exp e;
     \<D>1 (Suc 0) e \<lfloor>A\<rfloor>; \<B> e (Suc 0); Suc (max_vars e) \<le> length xs \<rbrakk>
  \<Longrightarrow> exsconf P h T (e, xs)"

lemma red1_preserves_exsconf:
  assumes wf: "wf_prog wf_md P" and hconf: "P \<turnstile> h \<surd>"
  and exsconf: "exsconf P h T (e, xs)" and red: "P \<turnstile>1 \<langle>e, (h, xs)\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle>"
  shows "exsconf P h' T (e', xs')"
using exsconf
proof cases
  case (exsconfI C ee T' A XS)
  hence [simp]: "ee = e" "XS = xs"
    and wt: "P,([Class C]),h \<turnstile>1 e : T'" and sub: "P \<turnstile> T' \<le> T" and lconf: "P,h,A \<turnstile>1 xs (:\<le>) [Class C] @ env_exp e"
    and da: "\<D>1 (length [Class C]) e \<lfloor>A\<rfloor>" and B: "\<B> e (length [Class C])"
    and n: "Suc (max_vars e) \<le> length xs" by auto
  from subject_reduction1[OF wf red, simplified, OF hconf lconf da wt B] sub
  obtain T'' where "P,([Class C]),h' \<turnstile>1 e' : T''" "P \<turnstile> T'' \<le> T" by(auto intro: widen_trans)
  moreover from red1_preserves_lconf_defass[OF red, simplified, OF wt lconf da B]
  obtain A' where "P,h',A' \<turnstile>1 xs' (:\<le>) Class C # env_exp e'" "\<D>1 (Suc 0) e' \<lfloor>A'\<rfloor>" by auto
  moreover from red1_preserves_B[OF red B] have "\<B> e' (Suc 0)" by simp
  moreover from red1_max_vars[OF red] red1_preserves_len[OF red] n
    have "Suc (max_vars e') \<le> length xs'" by simp
  ultimately show ?thesis .. 
qed

lemma exsconf_hext_mono: "\<lbrakk> exsconf P h T exs; hext h h' \<rbrakk> \<Longrightarrow> exsconf P h' T exs"
by(auto elim!: exsconf.cases intro: exsconfI elim: WTrt1_hext_mono lconf1_hext_mono)

lemma B_clearInitBlock [simp]: "\<B> (fst (clearInitBlock e xs)) n \<longleftrightarrow> \<B> e n"
  and Bs_clearInitBlocks [simp]: "\<B>s (fst (clearInitBlocks es xs)) n \<longleftrightarrow> \<B>s es n"
by(induct e and es arbitrary: xs n and xs n)(auto simp add: split_beta)

lemma exsconf_clearInitBlock: 
  assumes exsconf: "exsconf P h T (e, xs)"
  shows "exsconf P h T (clearInitBlock e xs)"
using exsconf
proof(cases)
  case (exsconfI C e' T' A xs')
  hence [simp]: "e' = e" "xs' = xs"
    and wt: "P,([Class C]),h \<turnstile>1 e : T'" and sub: "P \<turnstile> T' \<le> T"
    and lconf: "P,h,A \<turnstile>1 xs (:\<le>) [Class C] @ env_exp e" 
    and da: "\<D>1 (length [Class C]) e \<lfloor>A\<rfloor>" and B: "\<B> e (length [Class C])"
    and len: "length [Class C] + max_vars e \<le> length xs" by simp_all
  from wt have "P,([Class C]),h \<turnstile>1 fst (clearInitBlock e xs) : T'" by(rule WTrt1_clearInitBlock)
  moreover note sub moreover from clearInitblock_lconf_defass[OF wt lconf da B len]
  obtain A' where "P,h,A' \<turnstile>1 snd (clearInitBlock e xs) (:\<le>) Class C # env_exp (fst (clearInitBlock e xs))"
    and "\<D>1 (Suc 0) (fst (clearInitBlock e xs)) \<lfloor>A'\<rfloor>" by(auto simp add: env_exp_clearInitBlock)
  moreover from B have "\<B> (fst (clearInitBlock e xs)) (Suc 0)" by simp
  moreover from len have "Suc (max_vars (fst (clearInitBlock e xs))) \<le> length (snd (clearInitBlock e xs))"
    by(simp add: max_vars_clearInitBlock clearInitBlock_length)
  ultimately have "exsconf P h T (fst (clearInitBlock e xs), snd (clearInitBlock e xs))" ..
  thus ?thesis by simp
qed

lemma B_inline_call: "\<lbrakk> \<B> e n; \<And>n. \<B> e' n \<rbrakk> \<Longrightarrow> \<B> (inline_call e' e) n"
  and Bs_inline_calls: "\<lbrakk> \<B>s es n; \<And>n. \<B> e' n \<rbrakk> \<Longrightarrow> \<B>s (inline_calls e' es) n"
by(induct e and es arbitrary: n and n) auto

lemma max_vars_inline_call: "max_vars (inline_call e' e) \<le> max_vars e + max_vars e'"
  and max_varss_inline_calls: "max_varss (inline_calls e' es) \<le> max_varss es + max_vars e'"
by(induct e and es) auto

lemma exsconf_inline_call:
  assumes wf: "wf_prog wf_md P"
  and ha: "h a = \<lfloor>Obj C fs\<rfloor>"
  and sees: "P \<turnstile> C sees M: Ts'\<rightarrow>T' = mthd in D"
  and exsconf: "exsconf P h T (e, xs)"
  and call: "call e = \<lfloor>(a, M, vs)\<rfloor>"
  and wt': "\<And>E. \<exists>T. P,E,h \<turnstile>1 e' : T \<and> P \<turnstile> T \<le> T'"
  and da': "\<And>n. \<D>1 n e' \<lfloor>{}\<rfloor>"
  and B': "\<And>n. \<B> e' n"
  and mv: "max_vars e' = 0"
  shows "exsconf P h T (inline_call e' e, xs)"
using exsconf
proof cases
  case (exsconfI C ee T' A xs')
  hence [simp]: "ee = e" "xs' = xs" and wt: "P,([Class C]),h \<turnstile>1 e : T'"
    and sub: "P \<turnstile> T' \<le> T" and lconf: "P,h,A \<turnstile>1 xs (:\<le>) [Class C] @ env_exp e"
    and da: "\<D>1 (length [Class C]) e \<lfloor>A\<rfloor>" and B: "\<B> e (length [Class C])"
    and len: "Suc 0 + max_vars e \<le> length xs" by simp_all
  from WTrt1_inline_call[OF wf ha sees wt' wt call] sub obtain T2'
    where "P,([Class C]),h \<turnstile>1 inline_call e' e : T2'" and "P \<turnstile> T2' \<le> T" by(auto intro: widen_trans)
  moreover from env_exp_inline_call[OF call, of e'] obtain Env
    where "env_exp (inline_call e' e) = env_exp e @ env_exp e' @ Env" ..
  with lconf have "P,h,A \<turnstile>1 xs (:\<le>) Class C # env_exp (inline_call e' e)"
    by(auto dest: lconf1_append)
  moreover from defass_inline_call[OF da' da] have "\<D>1 (Suc 0) (inline_call e' e) \<lfloor>A\<rfloor>" by simp
  moreover from B B' have "\<B> (inline_call e' e) (Suc 0)" by(auto dest: B_inline_call)
  moreover from len mv max_vars_inline_call[of e' e] 
  have "Suc (max_vars (inline_call e' e)) \<le> length xs" by simp
  ultimately show ?thesis ..
qed

lemma exsconf_inline_call_Val:
  assumes wf: "wf_prog wf_md P"
  and ha: "h a = \<lfloor>Obj C fs\<rfloor>"
  and sees: "P \<turnstile> C sees M: Ts'\<rightarrow>T' = mthd in D"
  and exsconf: "exsconf P h T (e, xs)"
  and call: "call e = \<lfloor>(a, M, vs)\<rfloor>"
  and conf: "P,h \<turnstile> v :\<le> T'"
  shows "exsconf P h T (inline_call (Val v) e, xs)"
proof(rule exsconf_inline_call[OF wf ha sees exsconf call])
  fix E from conf show "\<exists>T. P,E,h \<turnstile>1 Val v : T \<and> P \<turnstile> T \<le> T'" unfolding conf_def by auto
qed auto

lemma exsconf_inline_call_Throw:
  assumes wf: "wf_prog wf_md P"
  and ha: "h a = \<lfloor>Obj C fs\<rfloor>"
  and sees: "P \<turnstile> C sees M: Ts'\<rightarrow>T' = mthd in D"
  and exsconf: "exsconf P h T (e, xs)"
  and call: "call e = \<lfloor>(a, M, vs)\<rfloor>"
  and conf: "P,h \<turnstile> Addr a' :\<le> Class Throwable"
  shows "exsconf P h T (inline_call (Throw a') e, xs)"
proof(rule exsconf_inline_call[OF wf ha sees exsconf call])
  fix E from conf show "\<exists>T. P,E,h \<turnstile>1 Throw a' : T \<and> P \<turnstile> T \<le> T'" unfolding conf_def
    by(auto dest: Array_widen split: heapobj.split_asm)
qed auto

lemma exsconf_Call:
  assumes wf: "wf_J1_prog P"
  and len: "length Ts = length vs"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = body in D"
  and confa: "P,h \<turnstile> v :\<le> Class D"
  and confvs: "P,h \<turnstile> vs [:\<le>] Ts"
  and rest: "length rest = max_vars body"
  shows "exsconf P h T (blocks1 (Suc 0) Ts body, v # vs @ rest)"
proof -
  from sees_wf_mdecl[OF wf sees] obtain T' where wt: "P,[Class D] @ Ts \<turnstile>1 body :: T'"
    and sub: "P \<turnstile> T' \<le> T" and da: "\<D> body \<lfloor>{..length Ts}\<rfloor>" and B: "\<B> body (Suc (length Ts))"
    and type: "set Ts \<subseteq> is_type P" and sv: "syncvars body" by(fastsimp simp add: wf_mdecl_def mem_def)
  from blocks1_WT[OF wt type] have "P,[Class D] \<turnstile>1 blocks1 (Suc 0) Ts body :: T'" by simp
  hence "P,[Class D],h \<turnstile>1 blocks1 (Suc 0) Ts body : T'" by(rule WT1_imp_WTrt1)
  moreover note sub moreover from len confa confvs
  have "P,h,{..length Ts} \<turnstile>1 v # vs @ rest (:\<le>) Class D # env_exp (blocks1 (Suc 0) Ts body)"
    by(auto simp add: lconf1_def nth_append nth_Cons split: nat.split elim: list_all2_nthD)
  moreover from WT1_fv[OF wt _ sv] B have "fv body \<subseteq> {0..<Suc (length Ts)}" by simp
  with D_D1[OF B sv da] have "\<D>1 (Suc 0) (blocks1 (Suc 0) Ts body) \<lfloor>{..length Ts}\<rfloor>"
    by(auto intro: D1_mono')
  ultimately show ?thesis using rest
    by -(rule exsconfI, auto simp add: B len[symmetric] blocks1_max_vars)
qed


lemma max_stacks_ge_length: "max_stacks es \<ge> length es"
by(induct es, auto)

lemma pcs_stack_xlift: "pcs (stack_xlift n xt) = pcs xt"
by(auto simp add: stack_xlift_def pcs_def)




lemma compP_conf: "conf (compP f P) = conf P"
by(auto simp add: conf_def intro!: ext)

lemma compP_confs: "compP f P,h \<turnstile> vs [:\<le>] Ts \<longleftrightarrow> P,h \<turnstile> vs [:\<le>] Ts"
by(simp add: compP_conf)



lemma compP_has_method: "compP f P \<turnstile> C has M \<longleftrightarrow> P \<turnstile> C has M"
unfolding has_method_def
by(fastsimp dest: sees_method_compPD intro: sees_method_compP)

lemma red1_new_thread_heap: "\<lbrakk>P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t ex h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h = hp s'"
  and reds1_new_thread_heap: "\<lbrakk>P \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t ex h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h = hp s'"
apply(induct rule: red1_reds1.inducts)
apply(fastsimp dest: red_ext_new_thread_heap)+
done

lemma compE1_Goto_not_same: "\<lbrakk> compE2 e ! pc = Goto i; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> nat (int pc + i) \<noteq> pc"
  and compEs2_Goto_not_same: "\<lbrakk> compEs2 es ! pc = Goto i; pc < length (compEs2 es) \<rbrakk> \<Longrightarrow> nat (int pc + i) \<noteq> pc"
apply(induct e and es arbitrary: pc i and pc i)
apply(auto simp add: nth_Cons nth_append split: split_if_asm bop.split_asm nat.splits)
apply fastsimp+
done

lemma match_ex_table_compxE2_not_same: "match_ex_table P C pc (compxE2 e n d) = \<lfloor>(pc', d')\<rfloor> \<Longrightarrow> pc \<noteq> pc'"
  and match_ex_table_compxEs2_not_same:"match_ex_table P C pc (compxEs2 es n d) = \<lfloor>(pc', d')\<rfloor> \<Longrightarrow> pc \<noteq> pc'"
apply(induct e and es arbitrary: n d and n d)
apply(auto simp add: match_ex_table_append match_ex_entry simp del: compxE2_size_convs compxEs2_size_convs compxE2_stack_xlift_convs compxEs2_stack_xlift_convs split: split_if_asm)
done

lemma expr_ineqs [simp]: "Val v ;; e \<noteq> e" "if (e1) e else e2 \<noteq> e" "if (e1) e2 else e \<noteq> e"
by(induct e) auto

lemma red1_changes: "P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> e \<noteq> e'"
  and reds1_changes: "P \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> es \<noteq> es'"
proof(induct rule: red1_reds1.inducts)
  case (Red1CallExternal s a T M vs ta va h' ta' e' s')
  thus ?case by(cases va) auto
qed auto


end
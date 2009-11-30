(*  Title:      JinjaThreads/Compiler/Correctness1.thy
    Author:     Andreas Lochbihler, Tobias Nipkow
*)

header {* \isaheader{Correctness of Stage 1} *}

theory Correctness1 imports
  J1WellForm
  Compiler1
  "../J/DefAssPreservation"
  "../Framework/FWBisimulation"
  "../Common/ExternalCallWF"
begin

lemma [simp]:
  fixes e :: "('a, 'b) exp" and es :: "('a, 'b) exp list"
  shows \<tau>move0_compP: "\<tau>move0 (compP f P) h e = \<tau>move0 P h e"
  and \<tau>moves0_compP: "\<tau>moves0 (compP f P) h es = \<tau>moves0 P h es"
by(induct e and es) auto

lemma \<tau>Move0_compP [simp]: "\<tau>Move0 (compP f P) = \<tau>Move0 P"
by(intro ext) auto

lemma [simp]:
  fixes e :: "('a, 'b) exp" and es :: "('a, 'b) exp list"
  shows \<tau>move1_compP: "\<tau>move1 (compP f P) h e = \<tau>move1 P h e"
  and \<tau>moves1_compP: "\<tau>moves1 (compP f P) h es = \<tau>moves1 P h es"
by(induct e and es) auto

lemma \<tau>Move1_compP [simp]: "\<tau>Move1 (compP f P) = \<tau>Move1 P"
by(intro ext) auto

lemma index_le_lengthD: "index xs x < length xs \<Longrightarrow> x \<in> set xs"
by(erule contrapos_pp)(simp)

lemma not_hidden_index_nth: "\<lbrakk> i < length Vs; \<not> hidden Vs i \<rbrakk> \<Longrightarrow> index Vs (Vs ! i) = i"
by(induct Vs arbitrary: i)(auto split: split_if_asm nat.split_asm simp add: nth_Cons hidden_def)

lemma hidden_snoc_nth:
  assumes len: "i < length Vs"
  shows "hidden (Vs @ [Vs ! i]) i"
proof(cases "hidden Vs i")
  case True thus ?thesis by simp
next
  case False
  with len have "index Vs (Vs ! i) = i" by(rule not_hidden_index_nth)
  moreover from len have "hidden (Vs @ [Vs ! i]) (index Vs (Vs ! i))"
    by(auto intro: hidden_index)
  ultimately show ?thesis by simp
qed

lemma \<tau>red0r_preserves_defass:
  assumes wf: "wf_J_prog P"
  shows "\<lbrakk> \<tau>red0r extTA P h (e, xs) (e', xs'); \<D> e \<lfloor>dom xs\<rfloor> \<rbrakk> \<Longrightarrow> \<D> e' \<lfloor>dom xs'\<rfloor>"
by(induct rule: rtranclp_induct2)(auto dest: red_preserves_defass[OF wf])

lemma \<tau>red0t_preserves_defass:
  assumes wf: "wf_J_prog P"
  shows "\<lbrakk> \<tau>red0t extTA P h (e, xs) (e', xs'); \<D> e \<lfloor>dom xs\<rfloor> \<rbrakk> \<Longrightarrow> \<D> e' \<lfloor>dom xs'\<rfloor>"
by(rule \<tau>red0r_preserves_defass[OF wf])(rule tranclp_into_rtranclp)


section{*Correctness of program compilation *}

consts
  unmod :: "expr1 \<Rightarrow> nat \<Rightarrow> bool"
  unmods :: "expr1 list \<Rightarrow> nat \<Rightarrow> bool"
primrec
"unmod (new C) i = True"
"unmod (newA T\<lfloor>e\<rceil>) i = unmod e i"
"unmod (Cast C e) i = unmod e i"
"unmod (Val v) i = True"
"unmod (e1 \<guillemotleft>bop\<guillemotright> e2) i = (unmod e1 i \<and> unmod e2 i)"
"unmod (Var i) j = True"
"unmod (i:=e) j = (i \<noteq> j \<and> unmod e j)"
"unmod (a\<lfloor>i\<rceil>) j = (unmod a j \<and> unmod i j)"
"unmod (a\<lfloor>i\<rceil>:=e) j = (unmod a j \<and> unmod i j \<and> unmod e j)"
"unmod (a\<bullet>length) j = unmod a j"
"unmod (e\<bullet>F{D}) i = unmod e i"
"unmod (e1\<bullet>F{D}:=e2) i = (unmod e1 i \<and> unmod e2 i)"
"unmod (e\<bullet>M(es)) i = (unmod e i \<and> unmods es i)"
"unmod {j:T=vo; e} i = ((i = j \<longrightarrow> vo = None) \<and> unmod e i)"
"unmod (sync\<^bsub>V\<^esub> (o') e) i = (unmod o' i \<and> unmod e i \<and> i \<noteq> V)"
"unmod (insync\<^bsub>V\<^esub> (a) e) i = unmod e i"
"unmod (e1;;e2) i = (unmod e1 i \<and> unmod e2 i)"
"unmod (if (e) e\<^isub>1 else e\<^isub>2) i = (unmod e i \<and> unmod e\<^isub>1 i \<and> unmod e\<^isub>2 i)"
"unmod (while (e) c) i = (unmod e i \<and> unmod c i)"
"unmod (throw e) i = unmod e i"
"unmod (try e\<^isub>1 catch(C i) e\<^isub>2) j = (unmod e\<^isub>1 j \<and> (if i=j then False else unmod e\<^isub>2 j))"

"unmods ([]) i = True"
"unmods (e#es) i = (unmod e i \<and> unmods es i)"

lemma unmods_map_Val [simp]: "unmods (map Val vs) V"
by(induct vs) simp_all

lemma hidden_unmod: "hidden Vs i \<Longrightarrow> unmod (compE1 Vs e) i"
  and hidden_unmods: "hidden Vs i \<Longrightarrow> unmods (compEs1 Vs es) i"
apply(induct e and es arbitrary: Vs and Vs)
apply (simp_all add:hidden_inacc)
apply(auto simp add:hidden_def)
done

lemma unmod_extRet2J [simp]: "unmod (extRet2J va) i"
by(cases va) simp_all

lemma red1_preserves_unmod:
  "\<lbrakk> P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; unmod e i \<rbrakk> \<Longrightarrow> (lcl s') ! i = (lcl s) ! i"
  
  and reds1_preserves_unmod:
  "\<lbrakk> P \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; unmods es i \<rbrakk> \<Longrightarrow> (lcl s') ! i = (lcl s) ! i"
apply(induct rule: red1_reds1.inducts)
apply(auto split: split_if_asm)
done

lemma red1_unmod_preserved:
  "\<lbrakk> P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; unmod e i \<rbrakk> \<Longrightarrow> unmod e' i"
  and reds1_unmods_preserved:
  "\<lbrakk> P \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; unmods es i \<rbrakk> \<Longrightarrow> unmods es' i"
by(induct rule: red1_reds1.inducts)(auto split: split_if_asm)

lemma \<tau>red1't_unmod_preserved:
  "\<lbrakk> \<tau>red1't P h (e, xs) (e', xs'); unmod e i \<rbrakk> \<Longrightarrow> unmod e' i"
by(induct rule: tranclp_induct2)(auto intro: red1_unmod_preserved)

lemma \<tau>red1'r_unmod_preserved:
  "\<lbrakk> \<tau>red1'r P h (e, xs) (e', xs'); unmod e i \<rbrakk> \<Longrightarrow> unmod e' i"
by(induct rule: rtranclp_induct2)(auto intro: red1_unmod_preserved)

lemma \<tau>red1't_preserves_unmod: 
  "\<lbrakk>\<tau>red1't P h (e, xs) (e', xs'); unmod e i; i < length xs \<rbrakk>
  \<Longrightarrow> xs' ! i = xs ! i"
apply(induct rule: tranclp_induct2)
 apply(auto dest: red1_preserves_unmod)
apply(drule red1_preserves_unmod)
apply(erule (1) \<tau>red1't_unmod_preserved)
apply(drule \<tau>red1't_preserves_len)
apply auto
done

lemma \<tau>red1'r_preserves_unmod: 
  "\<lbrakk>\<tau>red1'r P h (e, xs) (e', xs'); unmod e i; i < length xs \<rbrakk>
  \<Longrightarrow> xs' ! i = xs ! i"
apply(induct rule: converse_rtranclp_induct2)
 apply(auto dest: red1_preserves_unmod red1_unmod_preserved red1_preserves_len)
apply(frule (1) red1_unmod_preserved)
apply(frule red1_preserves_len)
apply(frule (1) red1_preserves_unmod)
apply auto
done

lemma max_dest: "(n :: nat) + max a b \<le> c \<Longrightarrow> n + a \<le> c \<and> n + b \<le> c"
apply(auto simp add: max_def split: split_if_asm) 
done

declare max_dest [dest!]

lemma fv_unmod_compE1: "\<lbrakk> i < length Vs; Vs ! i \<notin> fv e \<rbrakk> \<Longrightarrow> unmod (compE1 Vs e) i"
  and fvs_unmods_compEs1: "\<lbrakk> i < length Vs; Vs ! i \<notin> fvs es \<rbrakk> \<Longrightarrow> unmods (compEs1 Vs es) i"
proof(induct e and es arbitrary: Vs and Vs)
  case (Block V ty vo exp)
  note IH = `\<And>Vs. \<lbrakk>i < length Vs; Vs ! i \<notin> fv exp \<rbrakk> \<Longrightarrow> unmod (compE1 Vs exp) i`
  note len = `i < length Vs`
  hence i: "i < length (Vs @ [V])" by simp
  show ?case
  proof(cases "Vs ! i = V")
    case True
    from len have "hidden (Vs @ [Vs ! i]) i" by(rule hidden_snoc_nth)
    with len True show ?thesis by(auto intro: hidden_unmod)
  next
    case False
    with `Vs ! i \<notin> fv {V:ty=vo; exp}` len have "(Vs @ [V]) ! i \<notin> fv exp"
      by(auto simp add: nth_append)
    from IH[OF i this] len show ?thesis by(auto)
  qed
next
  case (TryCatch e1 C V e2)
  note IH1 = `\<And>Vs. \<lbrakk>i < length Vs; Vs ! i \<notin> fv e1 \<rbrakk> \<Longrightarrow> unmod (compE1 Vs e1) i`
  note IH2 = `\<And>Vs. \<lbrakk>i < length Vs; Vs ! i \<notin> fv e2 \<rbrakk> \<Longrightarrow> unmod (compE1 Vs e2) i`
  note len = `i < length Vs`
  hence i: "i < length (Vs @ [V])" by simp
  have "unmod (compE1 (Vs @ [V]) e2) i"
  proof(cases "Vs ! i = V")
    case True
    from len have "hidden (Vs @ [Vs ! i]) i" by(rule hidden_snoc_nth)
    with len True show ?thesis by(auto intro: hidden_unmod)
  next
    case False
    with `Vs ! i \<notin> fv (try e1 catch(C V) e2)` len have "(Vs @ [V]) ! i \<notin> fv e2"
      by(auto simp add: nth_append)
    from IH2[OF i this] len show ?thesis by(auto)
  qed
  with IH1[OF len] `Vs ! i \<notin> fv (try e1 catch(C V) e2)` len show ?case by(auto)
qed(auto dest: index_le_lengthD simp add: nth_append)

lemma hidden_lengthD: "hidden Vs i \<Longrightarrow> i < length Vs"
by(simp add: hidden_def)

lemma fv_B_unmod: "\<lbrakk> V \<notin> fv e; \<B> e n; V < n \<rbrakk> \<Longrightarrow> unmod e V"
  and fvs_Bs_unmods: "\<lbrakk> V \<notin> fvs es; \<B>s es n; V < n \<rbrakk> \<Longrightarrow> unmods es V"
by(induct e and es arbitrary: n and n) auto


lemma assumes fin: "final e'"
  shows unmod_inline_call: "unmod (inline_call e' e) V \<longleftrightarrow> unmod e V"
  and unmods_inline_calls: "unmods (inline_calls e' es) V \<longleftrightarrow> unmods es V"
apply(induct e and es)
apply(insert fin)
apply(auto simp add: is_vals_conv)
done



lemma LAss_lem:
  "\<lbrakk>x \<in> set xs; size xs \<le> size ys \<rbrakk>
  \<Longrightarrow> m1 \<subseteq>\<^sub>m m2(xs[\<mapsto>]ys) \<Longrightarrow> m1(x\<mapsto>y) \<subseteq>\<^sub>m m2(xs[\<mapsto>]ys[index xs x := y])"
apply(simp add:map_le_def)
apply(simp add:fun_upds_apply index_less_aux eq_sym_conv)
done


lemma Block_lem:
fixes l :: "'a \<rightharpoonup> 'b"
assumes 0: "l \<subseteq>\<^sub>m [Vs [\<mapsto>] ls]"
    and 1: "l' \<subseteq>\<^sub>m [Vs [\<mapsto>] ls', V\<mapsto>v]"
    and hidden: "V \<in> set Vs \<Longrightarrow> ls ! index Vs V = ls' ! index Vs V"
    and size: "size ls = size ls'"    "size Vs < size ls'"
shows "l'(V := l V) \<subseteq>\<^sub>m [Vs [\<mapsto>] ls']"
proof -
  have "l'(V := l V) \<subseteq>\<^sub>m [Vs [\<mapsto>] ls', V\<mapsto>v](V := l V)"
    using 1 by(rule map_le_upd)
  also have "\<dots> = [Vs [\<mapsto>] ls'](V := l V)" by simp
  also have "\<dots> \<subseteq>\<^sub>m [Vs [\<mapsto>] ls']"
  proof (cases "l V")
    case None thus ?thesis by simp
  next
    case (Some w)
    hence "[Vs [\<mapsto>] ls] V = Some w"
      using 0 by(force simp add: map_le_def split:if_splits)
    hence VinVs: "V \<in> set Vs" and w: "w = ls ! index Vs V"
      using size by(auto simp add:fun_upds_apply split:if_splits)
    hence "w = ls' ! index Vs V" using hidden[OF VinVs] by simp
    hence "[Vs [\<mapsto>] ls'](V := l V) = [Vs [\<mapsto>] ls']"
      using Some size VinVs by(simp add:index_less_aux map_upds_upd_conv_index)
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

declare compEs1_conv_map [simp del]

section {* The delay bisimulation relation *}

text {* Delay bisimulation for expressions *}

inductive bisim :: "vname list \<Rightarrow> expr \<Rightarrow> expr1 \<Rightarrow> val list \<Rightarrow> bool"
  and bisims :: "vname list \<Rightarrow> expr list \<Rightarrow> expr1 list \<Rightarrow> val list \<Rightarrow> bool"
where
  bisimNew: "bisim Vs (new C) (new C) xs"
| bisimNewArray: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (newA T\<lfloor>e\<rceil>) (newA T\<lfloor>e'\<rceil>) xs"
| bisimCast: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (Cast T e) (Cast T e') xs"
| bisimVal: "bisim Vs (Val v) (Val v) xs"
| bisimBinOp1:
  "\<lbrakk> bisim Vs e e' xs; \<not> is_val e; \<not> contains_insync e'' \<rbrakk> \<Longrightarrow> bisim Vs (e \<guillemotleft>bop\<guillemotright> e'') (e' \<guillemotleft>bop\<guillemotright> compE1 Vs e'') xs"
| bisimBinOp2: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (Val v \<guillemotleft>bop\<guillemotright> e) (Val v \<guillemotleft>bop\<guillemotright> e') xs"
| bisimVar: "bisim Vs (Var V) (Var (index Vs V)) xs"
| bisimLAss: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (V:=e) (index Vs V:=e') xs"
| bisimAAcc1: "\<lbrakk> bisim Vs a a' xs; \<not> is_val a; \<not> contains_insync i \<rbrakk> \<Longrightarrow> bisim Vs (a\<lfloor>i\<rceil>) (a'\<lfloor>compE1 Vs i\<rceil>) xs"
| bisimAAcc2: "bisim Vs i i' xs \<Longrightarrow> bisim Vs (Val v\<lfloor>i\<rceil>) (Val v\<lfloor>i'\<rceil>) xs"
| bisimAAss1:
  "\<lbrakk> bisim Vs a a' xs; \<not> is_val a; \<not> contains_insync i; \<not> contains_insync e \<rbrakk>
  \<Longrightarrow> bisim Vs (a\<lfloor>i\<rceil>:=e) (a'\<lfloor>compE1 Vs i\<rceil>:=compE1 Vs e) xs"
| bisimAAss2: "\<lbrakk> bisim Vs i i' xs; \<not> is_val i; \<not> contains_insync e \<rbrakk> \<Longrightarrow> bisim Vs (Val v\<lfloor>i\<rceil>:=e) (Val v\<lfloor>i'\<rceil>:=compE1 Vs e) xs"
| bisimAAss3: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (Val v\<lfloor>Val i\<rceil> := e) (Val v\<lfloor>Val i\<rceil> := e') xs"
| bisimALength: "bisim Vs a a' xs \<Longrightarrow> bisim Vs (a\<bullet>length) (a'\<bullet>length) xs"
| bisimFAcc: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (e\<bullet>F{D}) (e'\<bullet>F{D}) xs"
| bisimFAss1: "\<lbrakk> bisim Vs e e' xs; \<not> is_val e; \<not> contains_insync e'' \<rbrakk> \<Longrightarrow> bisim Vs (e\<bullet>F{D}:=e'') (e'\<bullet>F{D}:=compE1 Vs e'') xs"
| bisimFAss2: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (Val v\<bullet>F{D} := e) (Val v\<bullet>F{D} := e') xs"
| bisimCallObj: "\<lbrakk> bisim Vs e e' xs; \<not> is_val e; \<not> contains_insyncs es \<rbrakk> \<Longrightarrow> bisim Vs (e\<bullet>M(es)) (e'\<bullet>M(compEs1 Vs es)) xs"
| bisimCallParams: "bisims Vs es es' xs \<Longrightarrow> bisim Vs (Val v\<bullet>M(es)) (Val v\<bullet>M(es')) xs"
| bisimBlockNone: "bisim (Vs@[V]) e e' xs \<Longrightarrow> bisim Vs {V:T=None; e} {(length Vs):T=None; e'} xs"
| bisimBlockSome: "\<lbrakk> bisim (Vs@[V]) e e' (xs[length Vs := v]) \<rbrakk> \<Longrightarrow> bisim Vs {V:T=\<lfloor>v\<rfloor>; e} {(length Vs):T=\<lfloor>v\<rfloor>; e'} xs"
| bisimBlockSomeNone: "\<lbrakk> bisim (Vs@[V]) e e' xs; xs ! (length Vs) = v \<rbrakk> \<Longrightarrow> bisim Vs {V:T=\<lfloor>v\<rfloor>; e} {(length Vs):T=None; e'} xs"
| bisimSynchronized:
  "\<lbrakk> bisim Vs o' o'' xs; \<not> contains_insync e \<rbrakk>
  \<Longrightarrow> bisim Vs (sync(o') e) (sync\<^bsub>length Vs\<^esub>(o'') (compE1 (Vs@[fresh_var Vs]) e)) xs"
| bisimInSynchronized:
  "\<lbrakk> bisim (Vs@[fresh_var Vs]) e e' xs; xs ! length Vs = Addr a \<rbrakk> \<Longrightarrow> bisim Vs (insync(a) e) (insync\<^bsub>length Vs\<^esub>(a) e') xs"
| bisimSeq: "\<lbrakk> bisim Vs e e' xs; \<not> contains_insync e'' \<rbrakk> \<Longrightarrow> bisim Vs (e;;e'') (e';;compE1 Vs e'') xs"
| bisimCond:
  "\<lbrakk> bisim Vs e e' xs; \<not> contains_insync e1; \<not> contains_insync e2 \<rbrakk>
  \<Longrightarrow> bisim Vs (if (e) e1 else e2) (if (e') (compE1 Vs e1) else (compE1 Vs e2)) xs"
| bisimWhile:
  "\<lbrakk> \<not> contains_insync b; \<not> contains_insync e \<rbrakk> \<Longrightarrow> bisim Vs (while (b) e) (while (compE1 Vs b) (compE1 Vs e)) xs"
| bisimThrow: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (throw e) (throw e') xs"
| bisimTryCatch:
  "\<lbrakk> bisim Vs e e' xs; \<not> contains_insync e'' \<rbrakk>
  \<Longrightarrow> bisim Vs (try e catch(C V) e'') (try e' catch(C (length Vs)) compE1 (Vs@[V]) e'') xs"

| bisimsNil: "bisims Vs [] [] xs"
| bisimsCons1: "\<lbrakk> bisim Vs e e' xs; \<not> is_val e; \<not> contains_insyncs es \<rbrakk> \<Longrightarrow> bisims Vs (e # es) (e' # compEs1 Vs es) xs"
| bisimsCons2: "bisims Vs es es' xs \<Longrightarrow> bisims Vs (Val v # es) (Val v # es') xs"

declare bisimNew [iff]
declare bisimVal [iff]
declare bisimVar [iff]
declare bisimWhile [iff]
declare bisimsNil [iff]

declare bisim_bisims.intros [intro!]
declare bisimsCons1 [rule del, intro] bisimsCons2 [rule del, intro]
  bisimBinOp1 [rule del, intro] bisimAAcc1 [rule del, intro]
  bisimAAss1 [rule del, intro] bisimAAss2 [rule del, intro]
  bisimFAss1 [rule del, intro]
  bisimCallObj [rule del, intro] 

inductive_cases bisim_safe_cases [elim!]:
  "bisim Vs (new C) e' xs"
  "bisim Vs (newA T\<lfloor>e\<rceil>) e' xs"
  "bisim Vs (Cast T e) e' xs"
  "bisim Vs (Val v) e' xs"
  "bisim Vs (Var V) e' xs"
  "bisim Vs (V:=e) e' xs"
  "bisim Vs (Val v\<lfloor>i\<rceil>) e' xs"
  "bisim Vs (Val v\<lfloor>Val v'\<rceil> := e) e' xs"
  "bisim Vs (a\<bullet>length) e' xs"
  "bisim Vs (e\<bullet>F{D}) e' xs"
  "bisim Vs (sync(o') e) e' xs"
  "bisim Vs (insync(a) e) e' xs"
  "bisim Vs (e;;e') e'' xs"
  "bisim Vs (if (b) e1 else e2) e' xs"
  "bisim Vs (while (b) e) e' xs"
  "bisim Vs (throw e) e' xs"
  "bisim Vs (try e catch(C V) e') e'' xs"
  "bisim Vs e' (new C) xs"
  "bisim Vs e' (newA T\<lfloor>e\<rceil>) xs"
  "bisim Vs e' (Cast T e) xs"
  "bisim Vs e' (Val v) xs"
  "bisim Vs e' (Var V) xs"
  "bisim Vs e' (V:=e) xs"
  "bisim Vs e' (Val v\<lfloor>i\<rceil>) xs"
  "bisim Vs e' (Val v\<lfloor>Val v'\<rceil> := e) xs"
  "bisim Vs e' (a\<bullet>length) xs"
  "bisim Vs e' (e\<bullet>F{D}) xs"
  "bisim Vs e' (sync\<^bsub>V\<^esub> (o') e) xs"
  "bisim Vs e' (insync\<^bsub>V\<^esub> (a) e) xs"
  "bisim Vs e'' (e;;e') xs"
  "bisim Vs e' (if (b) e1 else e2) xs"
  "bisim Vs e' (while (b) e) xs"
  "bisim Vs e' (throw e) xs"
  "bisim Vs e'' (try e catch(C V) e') xs"

inductive_cases bisim_cases [elim]:
  "bisim Vs (e1 \<guillemotleft>bop\<guillemotright> e2) e' xs"
  "bisim Vs (a\<lfloor>i\<rceil>) e' xs"
  "bisim Vs (a\<lfloor>i\<rceil>:=e) e' xs"
  "bisim Vs (e\<bullet>F{D}:=e') e'' xs"
  "bisim Vs (e\<bullet>M(es)) e' xs"
  "bisim Vs {V:T=vo; e} e' xs"
  "bisim Vs e' (e1 \<guillemotleft>bop\<guillemotright> e2) xs"
  "bisim Vs e' (a\<lfloor>i\<rceil>) xs"
  "bisim Vs e' (a\<lfloor>i\<rceil>:=e) xs"
  "bisim Vs e'' (e\<bullet>F{D}:=e') xs"
  "bisim Vs e' (e\<bullet>M(es)) xs"
  "bisim Vs e' {V:T=vo; e} xs"

inductive_cases bisims_safe_cases [elim!]:
  "bisims Vs [] es xs"
  "bisims Vs es [] xs"

inductive_cases bisims_cases [elim]:
  "bisims Vs (e # es) es' xs"
  "bisims Vs es' (e # es) xs"


lemma bisims_map_Val_conv [simp]: "bisims Vs (map Val vs) es xs = (es = map Val vs)"
apply(induct vs arbitrary: es)
 apply(fastsimp)
apply(simp)
apply(rule iffI)
apply(erule bisims_cases, auto)
done

lemma bisim_contains_insync: "bisim Vs e e' xs \<Longrightarrow> contains_insync e = contains_insync e'"
  and bisims_contains_insyncs: "bisims Vs es es' xs \<Longrightarrow> contains_insyncs es = contains_insyncs es'"
by(induct rule: bisim_bisims.inducts) auto

lemma bisims_map_Val_Throw: 
  "bisims Vs (map Val vs @ Throw a # es) es' xs \<longleftrightarrow> es' = map Val vs @ Throw a # compEs1 Vs es \<and> \<not> contains_insyncs es"
apply(induct vs arbitrary: es')
 apply(simp)
 apply(rule iffI)
  apply(erule bisims_cases)
   apply(clarsimp)
  apply(simp)
 apply(simp)
 apply(rule bisimsCons1)
   apply(fastsimp)
  apply(fastsimp)
 apply simp
apply(clarsimp)
apply(rule iffI)
 apply(erule bisims_cases)
  apply(simp)
 apply(simp)
apply(simp)
apply(rule bisimsCons2)
apply(simp)
done

lemma compE1_bisim [intro]: "\<lbrakk> fv e \<subseteq> set Vs; \<not> contains_insync e \<rbrakk> \<Longrightarrow> bisim Vs e (compE1 Vs e) xs"
  and compEs1_bisims [intro]: "\<lbrakk> fvs es \<subseteq> set Vs; \<not> contains_insyncs es \<rbrakk> \<Longrightarrow> bisims Vs es (compEs1 Vs es) xs"
proof(induct e and es arbitrary: Vs xs and Vs xs)
  case (BinOp exp1 bop exp2 Vs x)
  thus ?case by(cases "is_val exp1")(auto)
next
  case (AAcc exp1 exp2 Vs x)
  thus ?case by(cases "is_val exp1")(auto)
next
  case (AAss exp1 exp2 exp3 Vs x)
  thus ?case by(cases "is_val exp1", cases "is_val exp2", fastsimp+)
next
  case (FAss exp1 F D exp2 Vs x)
  thus ?case by(cases "is_val exp1", auto)
next
  case (Call obj M params Vs x)
  thus ?case by(cases "is_val obj")(auto)
next
  case (Block V T vo exp Vs xs)
  from `fv {V:T=vo; exp} \<subseteq> set Vs` have "fv exp \<subseteq> set (Vs@[V])" by(auto)
  with Block show ?case by(cases vo)(auto)
next
  case (Cons_exp exp list Vs x)
  thus ?case by(cases "is_val exp")(auto intro!: bisimsCons2)
qed(auto)

lemma bisim_hidden_unmod: "\<lbrakk> bisim Vs e e' xs; hidden Vs i \<rbrakk> \<Longrightarrow> unmod e' i"
  and bisims_hidden_unmods: "\<lbrakk> bisims Vs es es' xs; hidden Vs i \<rbrakk> \<Longrightarrow> unmods es' i"
by(induct rule: bisim_bisims.inducts)(auto intro: hidden_unmod hidden_unmods dest: hidden_inacc hidden_lengthD)

lemma bisim_fv_unmod: "\<lbrakk> bisim Vs e e' xs; i < length Vs; Vs ! i \<notin> fv e \<rbrakk> \<Longrightarrow> unmod e' i"
  and bisims_fvs_unmods: "\<lbrakk> bisims Vs es es' xs; i < length Vs; Vs ! i \<notin> fvs es \<rbrakk> \<Longrightarrow> unmods es' i"
proof(induct rule: bisim_bisims.inducts)
  case (bisimBlockNone Vs V e e' xs T)
  note len = `i < length Vs`
  have "unmod e' i"
  proof(cases "Vs ! i = V")
    case True
    from len have "hidden (Vs @ [Vs ! i]) i" by(rule hidden_snoc_nth)
    with len True `bisim (Vs @ [V]) e e' xs` show ?thesis by(auto intro: bisim_hidden_unmod)
  next
    case False
    with bisimBlockNone show ?thesis by(auto simp add: nth_append)
  qed
  thus ?case by simp
next
  case (bisimBlockSome Vs V e e' xs v T)
  note len = `i < length Vs`
  show ?case
  proof(cases "Vs ! i = V")
    case True
    from len have "hidden (Vs @ [Vs ! i]) i" by(rule hidden_snoc_nth)
    with len True `bisim (Vs @ [V]) e e' (xs[length Vs := v])`
    show ?thesis by(auto intro: bisim_hidden_unmod)
  next
    case False
    with bisimBlockSome show ?thesis by(auto simp add: nth_append)
  qed
next
  case (bisimBlockSomeNone Vs V e e' xs v T)
  note len = `i < length Vs`
  show ?case
  proof(cases "Vs ! i = V")
    case True
    from len have "hidden (Vs @ [Vs ! i]) i" by(rule hidden_snoc_nth)
    with len True `bisim (Vs @ [V]) e e' xs`
    show ?thesis by(auto intro: bisim_hidden_unmod)
  next
    case False
    with bisimBlockSomeNone show ?thesis by(auto simp add: nth_append)
  qed
qed(fastsimp dest: fv_unmod_compE1 fvs_unmods_compEs1 index_le_lengthD simp add: nth_append)+

lemma bisim_extRet2J [intro!]: "bisim Vs (extRet2J va) (extRet2J1 va) xs"
by(cases va) auto

lemma bisims_map_Val_conv2 [simp]: "bisims Vs es (map Val vs) xs = (es = map Val vs)"
apply(induct vs arbitrary: es)
apply(fastsimp elim!: bisims_cases)+
done

lemma bisims_map_Val_Throw2: 
  "bisims Vs es' (map Val vs @ Throw a # es) xs \<longleftrightarrow>
   (\<exists>es''. es' = map Val vs @ Throw a # es'' \<and> es = compEs1 Vs es'' \<and> \<not> contains_insyncs es'')"
apply(induct vs arbitrary: es')
 apply(simp)
 apply(rule iffI)
  apply(erule bisims_cases)
   apply(clarsimp)
  apply(simp)
 apply(clarsimp)
 apply(rule bisimsCons1)
   apply(fastsimp)
  apply(fastsimp)
 apply(assumption)
apply(clarsimp)
apply(rule iffI)
 apply(erule bisims_cases)
  apply(fastsimp)
 apply(simp)
apply(clarsimp)
apply(rule bisimsCons2)
apply(simp)
done


lemma hidden_bisim_unmod: "\<lbrakk> bisim Vs e e' xs; hidden Vs i \<rbrakk> \<Longrightarrow> unmod e' i"
  and hidden_bisims_unmods: "\<lbrakk> bisims Vs es es' xs; hidden Vs i \<rbrakk> \<Longrightarrow> unmods es' i"
apply(induct rule: bisim_bisims.inducts)
apply(auto simp add:hidden_inacc intro: hidden_unmod hidden_unmods)
apply(auto simp add: hidden_def)
done


text {* Delay bisimulation for call stacks *}

inductive bisim01 :: "expr \<Rightarrow> expr1 \<times> locals1 \<Rightarrow> bool"
where
  "\<lbrakk> bisim [] e e' xs; fv e = {}; \<D> e \<lfloor>{}\<rfloor>; max_vars e' \<le> length xs; call e = \<lfloor>aMvs\<rfloor>; call1 e' = \<lfloor>aMvs\<rfloor>; 
    this_Block_ok e; this_None_Block e' \<rbrakk>
  \<Longrightarrow> bisim01 e (e', xs)"

inductive bisim_list :: "expr list \<Rightarrow> (expr1 \<times> locals1) list \<Rightarrow> bool"
where
  bisim_listNil: "bisim_list [] []"
| bisim_listCons: 
  "\<lbrakk> bisim_list es exs'; bisim [] e e' xs; 
     fv e = {}; \<D> e \<lfloor>{}\<rfloor>;
     max_vars e' \<le> length xs;
     call e = \<lfloor>aMvs\<rfloor>; call1 e' = \<lfloor>aMvs\<rfloor> \<rbrakk>
  \<Longrightarrow> bisim_list (e # es) ((e', xs) # exs')"

inductive_cases bisim_list_cases [elim!]:
 "bisim_list [] exs'"
 "bisim_list (ex # exs) exs'"
 "bisim_list exs (ex' # exs')"

lemma bisim_list_list_all2_conv:
  "bisim_list es exs' \<longleftrightarrow> list_all2 bisim01 es exs'"
proof
  assume "bisim_list es exs'"
  thus "list_all2 bisim01 es exs'"
    by induct(auto intro!: bisim01.intros)
next
  assume "list_all2 bisim01 es exs'"
  thus "bisim_list es exs'"
    by(induct es arbitrary: exs')(auto intro!: bisim_listCons bisim_listNil elim!: bisim01.cases simp add: list_all2_Cons1)
qed

fun bisim_list1 :: "expr \<times> expr list \<Rightarrow> (expr1 \<times> locals1) \<times> (expr1 \<times> locals1) list \<Rightarrow> bool"
where
  "bisim_list1 (e, es) ((e1, xs1), exs1) \<longleftrightarrow> bisim_list es exs1 \<and> bisim [] e e1 xs1 \<and> fv e = {} \<and> \<D> e \<lfloor>{}\<rfloor> \<and> max_vars e1 \<le> length xs1"

lemma bisim_list1I[intro?]:
  "\<lbrakk> bisim_list es exs1; bisim [] e e1 xs1; fv e = {};
     \<D> e \<lfloor>{}\<rfloor>; max_vars e1 \<le> length xs1 \<rbrakk>
  \<Longrightarrow> bisim_list1 (e, es) ((e1, xs1), exs1)"
by simp

lemma bisim_list1E[elim?]:
  assumes "bisim_list1 (e, es) ((e1, xs1), exs1)"
  obtains "bisim_list es exs1" "bisim [] e e1 xs1" "fv e = {}" "\<D> e \<lfloor>{}\<rfloor>" "max_vars e1 \<le> length xs1"
using assms by auto

lemma bisim_list1_elim:
  assumes "bisim_list1 es' exs"
  obtains e es e1 xs1 exs1
  where "es' = (e, es)" "exs = ((e1, xs1), exs1)"
  and "bisim_list es exs1" "bisim [] e e1 xs1" "fv e = {}" "\<D> e \<lfloor>{}\<rfloor>" "max_vars e1 \<le> length xs1"
using assms by(cases es')(cases exs, fastsimp)

declare bisim_list1.simps [simp del]

definition bisim_red0_Red1 :: "((expr \<times> expr list) \<times> heap) \<Rightarrow> (((expr1 \<times> locals1) \<times> (expr1 \<times> locals1) list) \<times> heap) \<Rightarrow> bool"
where "bisim_red0_Red1 \<equiv> (\<lambda>(es, h) (exs, h'). bisim_list1 es exs \<and> h = h')"

lemma bisim_list_extTA2J0_extTA2J1:
  assumes wf: "wf_J_prog P"
  and sees: "P \<turnstile> C sees M:[]\<rightarrow>T = meth in D"
  and ha: "h a = \<lfloor>Obj C fs\<rfloor>"
  shows "bisim_list1 (extNTA2J0 P (C, M, a)) (extNTA2J1 (compP1 P) (C, M, a))"
proof -
  obtain pns body where "meth = (pns, body)" by(cases meth)
  with sees have sees: "P \<turnstile> C sees M:[]\<rightarrow>T = (pns, body) in D" by simp
  moreover let ?xs = "Addr a # replicate (max_vars body) undefined"
  let ?e' = "{0:Class D=None; compE1 (this # pns) body}"
  have "bisim_list1 ({this:Class D=\<lfloor>Addr a\<rfloor>; body}, [addr a\<bullet>M([])]) ((?e', ?xs), [(addr a\<bullet>M([]), [])])"
  proof
    show "bisim_list [addr a\<bullet>M([])] [(addr a\<bullet>M([]), [])]"
    proof
      show "bisim_list [] []" ..
      show "bisim [] (addr a\<bullet>M([])) (addr a\<bullet>M([])) []"
	by(rule bisimCallParams)(rule bisimsNil)
    qed auto
    from sees_wf_mdecl[OF wf_prog_wwf_prog[OF wf] sees] have "fv body \<subseteq> set [this]" "pns = []"
      by(auto simp add: wf_mdecl_def)
    thus "fv {this:Class D=\<lfloor>Addr a\<rfloor>; body} = {}" by simp
    from sees_wf_mdecl[OF wf sees] obtain T' where "P,[this \<mapsto> Class D] \<turnstile> body :: T'" "this \<notin> set pns"
      and "\<D> body \<lfloor>dom [this \<mapsto> Addr a]\<rfloor>" by(auto simp add: wf_mdecl_def)
    hence "\<not> contains_insync body" by(auto simp add: contains_insync_conv dest: WT_expr_locks)
    with `fv body \<subseteq> set [this]`
    have "bisim ([] @ [this]) body (compE1 (this # pns) body) ?xs"
      unfolding append.simps `pns = []` by(rule compE1_bisim)
    hence "bisim [] {this:Class D=\<lfloor>Addr a\<rfloor>; body} {length ([] :: String.literal list):Class D=None; compE1 (this # pns) body} ?xs"
      by(rule bisimBlockSomeNone)(simp)
    thus "bisim [] {this:Class D=\<lfloor>Addr a\<rfloor>; body} ?e' ?xs" by simp
    from `\<D> body \<lfloor>dom [this \<mapsto> Addr a]\<rfloor>` show "\<D> {this:Class D=\<lfloor>Addr a\<rfloor>; body} \<lfloor>{}\<rfloor>" by simp
    show "max_vars ?e' \<le> length ?xs" by simp
  qed
  ultimately show ?thesis by(simp)
qed

abbreviation ta_bisim01 :: "J0_thread_action \<Rightarrow> J1_thread_action \<Rightarrow> bool" where
  "ta_bisim01 \<equiv> ta_bisim bisim_red0_Red1"

subsection {* Correctness proof *}

lemma ta_bisim01_extTA2J0_extTA2J1:
  assumes wf: "wf_J_prog P"
  and nt: "\<And>n T C M a h. \<lbrakk> n < length \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n = NewThread T (C, M, a) h \<rbrakk> \<Longrightarrow> (\<exists>fs. h a = \<lfloor>Obj C fs\<rfloor>) \<and> (\<exists>T meth D. P \<turnstile> C sees M:[]\<rightarrow>T =meth in D)"
  shows "ta_bisim01 (extTA2J0 P ta) (extTA2J1 (compP1 P) ta)"
apply(simp add: ta_bisim_def)
apply(auto intro!: list_all2_all_nthI)
apply(case_tac "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n")
  apply(auto simp add: bisim_red0_Red1_def)
apply(drule (1) nt)
apply(clarify)
apply(erule (1) bisim_list_extTA2J0_extTA2J1[OF wf, simplified])
done

lemma red_external_ta_bisim01: 
  "\<lbrakk> wf_J_prog P; P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; h a \<noteq> None \<rbrakk> \<Longrightarrow> ta_bisim01 (extTA2J0 P ta) (extTA2J1 (compP1 P) ta)"
apply(rule ta_bisim01_extTA2J0_extTA2J1, assumption)
apply(drule (1) red_external_new_thread_sees, auto simp add: in_set_conv_nth)
apply(drule red_ext_new_thread_heap, auto simp add: in_set_conv_nth)
done


lemmas \<tau>red1't_expr =
  NewArray_\<tau>red1't_xt Cast_\<tau>red1't_xt BinOp_\<tau>red1't_xt1 BinOp_\<tau>red1't_xt2 LAss_\<tau>red1't
  AAcc_\<tau>red1't_xt1 AAcc_\<tau>red1't_xt2 AAss_\<tau>red1't_xt1 AAss_\<tau>red1't_xt2 AAss_\<tau>red1't_xt3
  ALength_\<tau>red1't_xt FAcc_\<tau>red1't_xt FAss_\<tau>red1't_xt1 FAss_\<tau>red1't_xt2 Call_\<tau>red1't_obj
  Call_\<tau>red1't_param Block_None_\<tau>red1't_xt Block_\<tau>red1't_Some Sync_\<tau>red1't_xt InSync_\<tau>red1't_xt
  Seq_\<tau>red1't_xt Cond_\<tau>red1't_xt Throw_\<tau>red1't_xt Try_\<tau>red1't_xt

lemmas \<tau>red1'r_expr =
  NewArray_\<tau>red1'r_xt Cast_\<tau>red1'r_xt BinOp_\<tau>red1'r_xt1 BinOp_\<tau>red1'r_xt2 LAss_\<tau>red1'r
  AAcc_\<tau>red1'r_xt1 AAcc_\<tau>red1'r_xt2 AAss_\<tau>red1'r_xt1 AAss_\<tau>red1'r_xt2 AAss_\<tau>red1'r_xt3
  ALength_\<tau>red1'r_xt FAcc_\<tau>red1'r_xt FAss_\<tau>red1'r_xt1 FAss_\<tau>red1'r_xt2 Call_\<tau>red1'r_obj
  Call_\<tau>red1'r_param Block_None_\<tau>red1'r_xt Block_\<tau>red1'r_Some Sync_\<tau>red1'r_xt InSync_\<tau>red1'r_xt
  Seq_\<tau>red1'r_xt Cond_\<tau>red1'r_xt Throw_\<tau>red1'r_xt Try_\<tau>red1'r_xt

definition sim_move01 :: 
  "J1_prog \<Rightarrow> J0_thread_action \<Rightarrow> expr \<Rightarrow> expr1 \<Rightarrow> heap \<Rightarrow> locals1 \<Rightarrow> external_thread_action \<Rightarrow> expr1 \<Rightarrow> heap \<Rightarrow> locals1 \<Rightarrow> bool"
where
  "sim_move01 P ta0 e0 e h xs ta e' h' xs' \<longleftrightarrow> \<not> final e0 \<and>
  (if \<tau>move0 P h e0 then h' = h \<and> ta0 = \<epsilon> \<and> ta = \<epsilon> \<and> \<tau>red1't P h (e, xs) (e', xs')
    else \<exists>e'' xs''. \<tau>red1'r P h (e, xs) (e'', xs'') \<and> P \<turnstile>1 \<langle>e'', (h, xs'')\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle> \<and> \<not> \<tau>move1 P h e'' \<and> \<not> IUF e'' ta e' \<and> ta_bisim01 ta0 (extTA2J1 P ta))"

definition sim_moves01 :: 
  "J1_prog \<Rightarrow> J0_thread_action \<Rightarrow> expr list \<Rightarrow> expr1 list \<Rightarrow> heap \<Rightarrow> locals1 \<Rightarrow> external_thread_action \<Rightarrow> expr1 list \<Rightarrow> heap \<Rightarrow> locals1 \<Rightarrow> bool"
where
  "sim_moves01 P ta0 es0 es h xs ta es' h' xs' \<longleftrightarrow> \<not> finals es0 \<and>
  (if \<tau>moves0 P h es0 then h' = h \<and> ta0 = \<epsilon> \<and> ta = \<epsilon> \<and> \<tau>reds1't P h (es, xs) (es', xs')
    else \<exists>es'' xs''. \<tau>reds1'r P h (es, xs) (es'', xs'') \<and> P \<turnstile>1 \<langle>es'', (h, xs'')\<rangle> [-ta\<rightarrow>] \<langle>es', (h', xs')\<rangle> \<and> \<not> \<tau>moves1 P h es'' \<and> \<not> IUFs es'' ta es' \<and> ta_bisim01 ta0 (extTA2J1 P ta))"

declare \<tau>red1't_expr [elim!] \<tau>red1'r_expr[elim!]

lemma sim_move01_expr:
  assumes "sim_move01 P ta0 e0 e h xs ta e' h' xs'"
  shows
  "sim_move01 P ta0 (newA T\<lfloor>e0\<rceil>) (newA T\<lfloor>e\<rceil>) h xs ta (newA T\<lfloor>e'\<rceil>) h' xs'"
  "sim_move01 P ta0 (Cast T e0) (Cast T e) h xs ta (Cast T e') h' xs'"
  "sim_move01 P ta0 (e0 \<guillemotleft>bop\<guillemotright> e2) (e \<guillemotleft>bop\<guillemotright> e2') h xs ta (e' \<guillemotleft>bop\<guillemotright> e2') h' xs'"
  "sim_move01 P ta0 (Val v \<guillemotleft>bop\<guillemotright> e0) (Val v \<guillemotleft>bop\<guillemotright> e) h xs ta (Val v \<guillemotleft>bop\<guillemotright> e') h' xs'"
  "sim_move01 P ta0 (V := e0) (V' := e) h xs ta (V' := e') h' xs'"
  "sim_move01 P ta0 (e0\<lfloor>e2\<rceil>) (e\<lfloor>e2'\<rceil>) h xs ta (e'\<lfloor>e2'\<rceil>) h' xs'"
  "sim_move01 P ta0 (Val v\<lfloor>e0\<rceil>) (Val v\<lfloor>e\<rceil>) h xs ta (Val v\<lfloor>e'\<rceil>) h' xs'"
  "sim_move01 P ta0 (e0\<lfloor>e2\<rceil> := e3) (e\<lfloor>e2'\<rceil> := e3') h xs ta (e'\<lfloor>e2'\<rceil> := e3') h' xs'"
  "sim_move01 P ta0 (Val v\<lfloor>e0\<rceil> := e3) (Val v\<lfloor>e\<rceil> := e3') h xs ta (Val v\<lfloor>e'\<rceil> := e3') h' xs'"
  "sim_move01 P ta0 (AAss (Val v) (Val v') e0) (AAss (Val v) (Val v') e) h xs ta (AAss (Val v) (Val v') e') h' xs'"
  "sim_move01 P ta0 (e0\<bullet>length) (e\<bullet>length) h xs ta (e'\<bullet>length) h' xs'"
  "sim_move01 P ta0 (e0\<bullet>F{D}) (e\<bullet>F'{D'}) h xs ta (e'\<bullet>F'{D'}) h' xs'"
  "sim_move01 P ta0 (FAss e0 F D e2) (FAss e F' D' e2') h xs ta (FAss e' F' D' e2') h' xs'"
  "sim_move01 P ta0 (FAss (Val v) F D e0) (FAss (Val v) F' D' e) h xs ta (FAss (Val v) F' D' e') h' xs'"
  "sim_move01 P ta0 (e0\<bullet>M(es)) (e\<bullet>M(es')) h xs ta (e'\<bullet>M(es')) h' xs'"
  "sim_move01 P ta0 ({V:T=vo; e0}) ({V':T=None; e}) h xs ta ({V':T=None; e'}) h' xs'"
  "sim_move01 P ta0 (sync(e0) e2) (sync\<^bsub>V'\<^esub>(e) e2') h xs ta (sync\<^bsub>V'\<^esub>(e') e2') h' xs'"
  "sim_move01 P ta0 (insync(a) e0) (insync\<^bsub>V'\<^esub>(a') e) h xs ta (insync\<^bsub>V'\<^esub>(a') e') h' xs'"
  "sim_move01 P ta0 (e0;;e2) (e;;e2') h xs ta (e';;e2') h' xs'"
  "sim_move01 P ta0 (if (e0) e2 else e3) (if (e) e2' else e3') h xs ta (if (e') e2' else e3') h' xs'"
  "sim_move01 P ta0 (throw e0) (throw e) h xs ta (throw e') h' xs'"
  "sim_move01 P ta0 (try e0 catch(C V) e2) (try e catch(C' V') e2') h xs ta (try e' catch(C' V') e2') h' xs'"
using assms
by(fastsimp simp add: sim_move01_def final_iff split: split_if_asm intro: red1_reds1.intros)+

lemma sim_moves01_expr:
  "sim_move01 P ta0 e0 e h xs ta e' h' xs' \<Longrightarrow> sim_moves01 P ta0 (e0 # es2) (e # es2') h xs ta (e' # es2') h' xs'"
  "sim_moves01 P ta0 es0 es h xs ta es' h' xs' \<Longrightarrow> sim_moves01 P ta0 (Val v # es0) (Val v # es) h xs ta (Val v # es') h' xs'"
apply(auto simp add: sim_move01_def sim_moves01_def final_iff finals_def Cons_eq_append_conv split: split_if_asm intro: red1_reds1.intros \<tau>red1't_inj_\<tau>reds1't \<tau>red1'r_inj_\<tau>reds1'r \<tau>reds1't_cons_\<tau>reds1't \<tau>reds1'r_cons_\<tau>reds1'r)
apply(force elim!: \<tau>red1'r_inj_\<tau>reds1'r List1Red1)
apply(force elim!: \<tau>reds1'r_cons_\<tau>reds1'r List1Red2)
done

lemma sim_move01_CallParams:
  "sim_moves01 P ta0 es0 es h xs ta es' h' xs' \<Longrightarrow> sim_move01 P ta0 (Val v\<bullet>M(es0)) (Val v\<bullet>M(es)) h xs ta (Val v\<bullet>M(es')) h' xs'"
by(fastsimp simp add: sim_move01_def sim_moves01_def intro: Call_\<tau>red1'r_param Call1Params)

lemma sim_move01_reds:
  "\<lbrakk> new_Addr h = \<lfloor>a\<rfloor>; P \<turnstile> C has_fields FDTs \<rbrakk>
  \<Longrightarrow> sim_move01 P \<epsilon> (new C) (new C) h xs \<epsilon> (addr a) (h(a\<mapsto>(Obj C (init_fields FDTs)))) xs"
  "new_Addr h = None \<Longrightarrow> sim_move01 P \<epsilon> (new C) (new C) h xs \<epsilon> (THROW OutOfMemory) h xs"
  "\<lbrakk> new_Addr h = \<lfloor>a\<rfloor>; i \<ge> 0; h' = h(a \<mapsto> (Arr T (replicate (nat i) (default_val T)))) \<rbrakk>
  \<Longrightarrow> sim_move01 P \<epsilon> (newA T\<lfloor>Val (Intg i)\<rceil>) (newA T\<lfloor>Val (Intg i)\<rceil>) h xs \<epsilon> (addr a) h' xs"
  "i < 0 \<Longrightarrow> sim_move01 P \<epsilon> (newA T\<lfloor>Val (Intg i)\<rceil>) (newA T\<lfloor>Val (Intg i)\<rceil>) h xs \<epsilon> (THROW NegativeArraySize) h xs"
  "\<lbrakk> new_Addr h = None; i \<ge> 0 \<rbrakk>
  \<Longrightarrow> sim_move01 P \<epsilon> (newA T\<lfloor>Val (Intg i)\<rceil>) (newA T\<lfloor>Val (Intg i)\<rceil>) h xs \<epsilon> (THROW OutOfMemory) h xs"
  "\<lbrakk> typeof\<^bsub>h\<^esub> v = \<lfloor>U\<rfloor>; P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> sim_move01 P \<epsilon> (Cast T (Val v)) (Cast T (Val v)) h xs \<epsilon> (Val v) h xs"
  "\<lbrakk> typeof\<^bsub>h\<^esub> v = \<lfloor>U\<rfloor>; \<not> P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> sim_move01 P \<epsilon> (Cast T (Val v)) (Cast T (Val v)) h xs \<epsilon> (THROW ClassCast) h xs"
  "binop bop v1 v2 = Some v \<Longrightarrow> sim_move01 P \<epsilon> ((Val v1) \<guillemotleft>bop\<guillemotright> (Val v2)) (Val v1 \<guillemotleft>bop\<guillemotright> Val v2) h xs \<epsilon> (Val v) h xs"
  "\<lbrakk> xs!V = v; V < size xs \<rbrakk> \<Longrightarrow> sim_move01 P \<epsilon> (Var V') (Var V) h xs \<epsilon> (Val v) h xs"
  "V < length xs \<Longrightarrow> sim_move01 P \<epsilon> (V' := Val v) (V := Val v) h xs \<epsilon> unit h (xs[V := v])"
  "sim_move01 P \<epsilon> (null\<lfloor>Val v\<rceil>) (null\<lfloor>Val v\<rceil>) h xs \<epsilon> (THROW NullPointer) h xs"
  "\<lbrakk> h a = \<lfloor>Arr T el\<rfloor>; i < 0 \<or> i \<ge> int (length el) \<rbrakk>
  \<Longrightarrow> sim_move01 P \<epsilon> (addr a\<lfloor>Val (Intg i)\<rceil>) ((addr a)\<lfloor>Val (Intg i)\<rceil>) h xs \<epsilon> (THROW ArrayIndexOutOfBounds) h xs"
  "\<lbrakk> h a = \<lfloor>Arr T el\<rfloor>; i \<ge> 0; i < int (length el) \<rbrakk>
  \<Longrightarrow> sim_move01 P \<epsilon> (addr a\<lfloor>Val (Intg i)\<rceil>) ((addr a)\<lfloor>Val (Intg i)\<rceil>) h xs \<epsilon> (Val (el ! nat i)) h xs"
  "sim_move01 P \<epsilon> (null\<lfloor>Val v\<rceil> := Val v') (null\<lfloor>Val v\<rceil> := Val v') h xs \<epsilon> (THROW NullPointer) h xs"
  "\<lbrakk> h a = \<lfloor>Arr T el\<rfloor>; i < 0 \<or> i \<ge> int (length el) \<rbrakk>
  \<Longrightarrow> sim_move01 P \<epsilon> (AAss (addr a) (Val (Intg i)) (Val v)) (AAss (addr a) (Val (Intg i)) (Val v)) h xs \<epsilon> (THROW ArrayIndexOutOfBounds) h xs"
 "\<lbrakk> h a = \<lfloor>Arr T el\<rfloor>; i \<ge> 0; i < int (length el); typeof\<^bsub>h\<^esub> v = \<lfloor>U\<rfloor>; \<not> (P \<turnstile> U \<le> T) \<rbrakk>
  \<Longrightarrow> sim_move01 P \<epsilon> (AAss (addr a) (Val (Intg i)) (Val v)) (AAss (addr a) (Val (Intg i)) (Val v)) h xs \<epsilon> (THROW ArrayStore) h xs"
  "\<lbrakk> h a = \<lfloor>Arr T el\<rfloor>; i \<ge> 0; i < int (length el); typeof\<^bsub>h\<^esub> v = Some U; P \<turnstile> U \<le> T; h' = h(a \<mapsto> (Arr T (el[nat i := v]))) \<rbrakk>
  \<Longrightarrow> sim_move01 P \<epsilon> (AAss (addr a) (Val (Intg i)) (Val v)) (AAss (addr a) (Val (Intg i)) (Val v)) h xs \<epsilon> unit h' xs"
  "h a = \<lfloor>Arr T elem\<rfloor> \<Longrightarrow> sim_move01 P \<epsilon> (addr a\<bullet>length) (addr a\<bullet>length) h xs \<epsilon> (Val (Intg (int (length elem)))) h xs"
  "sim_move01 P \<epsilon> (null\<bullet>length) (null\<bullet>length) h xs \<epsilon> (THROW NullPointer) h xs"
  "\<lbrakk> h a = \<lfloor>Obj C fs\<rfloor>; fs (F,D) = Some v \<rbrakk>
  \<Longrightarrow> sim_move01 P \<epsilon> (addr a\<bullet>F{D}) (addr a\<bullet>F{D}) h xs \<epsilon> (Val v) h xs"
  "sim_move01 P \<epsilon> (null\<bullet>F{D}) (null\<bullet>F{D}) h xs \<epsilon> (THROW NullPointer) h xs"
  "h a = \<lfloor>Obj C fs\<rfloor>
  \<Longrightarrow> sim_move01 P \<epsilon> (addr a\<bullet>F{D} := Val v) (addr a\<bullet>F{D} := Val v) h xs \<epsilon> unit (h(a \<mapsto> (Obj C (fs((F,D) \<mapsto> v))))) xs"
  "sim_move01 P \<epsilon> (null\<bullet>F{D} := Val v) (null\<bullet>F{D} := Val v) h xs \<epsilon> (THROW NullPointer) h xs"
  "sim_move01 P \<epsilon> ({V':T=vo; Val u}) ({V:T=None; Val u}) h xs \<epsilon> (Val u) h xs"
  "V < length xs \<Longrightarrow> sim_move01 P \<epsilon> (sync(null) e0) (sync\<^bsub>V\<^esub> (null) e1) h xs \<epsilon> (THROW NullPointer) h (xs[V := Null])"
  "sim_move01 P \<epsilon> (Val v;;e0) (Val v;; e1) h xs \<epsilon> e1 h xs"
  "sim_move01 P \<epsilon> (if (true) e0 else e0') (if (true) e1 else e1') h xs \<epsilon> e1 h xs"
  "sim_move01 P \<epsilon> (if (false) e0 else e0') (if (false) e1 else e1') h xs \<epsilon> e1' h xs"
  "sim_move01 P \<epsilon> (throw null) (throw null) h xs \<epsilon> (THROW NullPointer) h xs"
  "sim_move01 P \<epsilon> (try (Val v) catch(C V') e0) (try (Val v) catch(C V) e1) h xs \<epsilon> (Val v) h xs"
  "\<lbrakk> h a = \<lfloor>Obj D fs\<rfloor>; P \<turnstile> D \<preceq>\<^sup>* C; V < length xs \<rbrakk>
  \<Longrightarrow> sim_move01 P \<epsilon> (try (Throw a) catch(C V') e0) (try (Throw a) catch(C V) e1) h xs \<epsilon> ({V:Class C=None; e1}) h (xs[V := Addr a])"
  "sim_move01 P \<epsilon> (newA T\<lfloor>Throw a\<rceil>) (newA T\<lfloor>Throw a\<rceil>) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (Cast T (Throw a)) (Cast T (Throw a)) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> ((Throw a) \<guillemotleft>bop\<guillemotright> e0) ((Throw a) \<guillemotleft>bop\<guillemotright> e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (Val v \<guillemotleft>bop\<guillemotright> (Throw a)) (Val v \<guillemotleft>bop\<guillemotright> (Throw a)) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (V' := Throw a) (V := Throw a) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (Throw a\<lfloor>e0\<rceil>) (Throw a\<lfloor>e1\<rceil>) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (Val v\<lfloor>Throw a\<rceil>) (Val v\<lfloor>Throw a\<rceil>) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (Throw a\<lfloor>e0\<rceil> := e0') (Throw a\<lfloor>e1\<rceil> := e1') h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (Val v\<lfloor>Throw a\<rceil> := e0) (Val v\<lfloor>Throw a\<rceil> := e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (Val v\<lfloor>Val v'\<rceil> := Throw a) (Val v\<lfloor>Val v'\<rceil> := Throw a) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (Throw a\<bullet>length) (Throw a\<bullet>length) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (Throw a\<bullet>F{D}) (Throw a\<bullet>F{D}) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (Throw a\<bullet>F{D} := e0) (Throw a\<bullet>F{D} := e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (Val v\<bullet>F{D} := Throw a) (Val v\<bullet>F{D} := Throw a) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (Throw a\<bullet>M(es0)) (Throw a\<bullet>M(es1)) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (Val v\<bullet>M(map Val vs @ Throw a # es0)) (Val v\<bullet>M(map Val vs @ Throw a # es1)) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> ({V':T=vo; Throw a}) ({V:T=None; Throw a}) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (sync(Throw a) e0) (sync\<^bsub>V\<^esub>(Throw a) e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (Throw a;;e0) (Throw a;;e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (if (Throw a) e0 else e0') (if (Throw a) e1 else e1') h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P \<epsilon> (throw (Throw a)) (throw (Throw a)) h xs \<epsilon> (Throw a) h xs"
by(fastsimp simp add: sim_move01_def intro: red1_reds1.intros)+

lemma sim_move01_CallNull:
  "sim_move01 P \<epsilon> (null\<bullet>M(map Val vs)) (null\<bullet>M(map Val vs)) h xs \<epsilon> (THROW NullPointer) h xs"
by(fastsimp simp add: sim_move01_def map_eq_append_conv intro: red1_reds1.intros)

lemma sim_move01_SyncLocks:
  "\<lbrakk> h a = \<lfloor>arrobj\<rfloor>; V < length xs; ta0 = \<epsilon>\<lbrace>\<^bsub>l\<^esub> Lock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace>; ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub> Lock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace> \<rbrakk>
   \<Longrightarrow> sim_move01 P ta0 (sync(addr a) e0) (sync\<^bsub>V\<^esub> (addr a) e1) h xs ta (insync\<^bsub>V\<^esub> (a) e1) h (xs[V := Addr a])"
  "\<lbrakk> xs ! V = Addr a'; V < length xs; ta0 = \<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a' \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a'\<rbrace>; ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a'\<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a'\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move01 P ta0 (insync(a') (Val v)) (insync\<^bsub>V\<^esub> (a) (Val v)) h xs ta (Val v) h xs"
  "\<lbrakk> xs ! V = Addr a'; V < length xs; ta0 = \<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a' \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a'\<rbrace>; ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a' \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a'\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move01 P ta0 (insync(a') (Throw a'')) (insync\<^bsub>V\<^esub> (a) (Throw a'')) h xs ta (Throw a'') h xs"
by(fastsimp simp add: sim_move01_def ta_bisim_def expand_finfun_eq expand_fun_eq finfun_upd_apply  intro: red1_reds1.intros[simplified] split: split_if_asm)+

lemma sim_move01_TryFail:
  "\<lbrakk> h a = \<lfloor>Obj D fs\<rfloor>; \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> sim_move01 P \<epsilon> (try (Throw a) catch(C V') e0) (try (Throw a) catch(C V) e1) h xs \<epsilon> (Throw a) h xs"
by(auto simp add: sim_move01_def intro!: Red1TryFail)

lemma sim_move01_BlockSome:
  "\<lbrakk> sim_move01 P ta0 e0 e h (xs[V := v]) ta e' h' xs'; V < length xs \<rbrakk>
  \<Longrightarrow> sim_move01 P ta0 ({V':T=\<lfloor>v\<rfloor>; e0}) ({V:T=\<lfloor>v\<rfloor>; e}) h xs ta ({V:T=None; e'}) h' xs'"
  "V < length xs \<Longrightarrow> sim_move01 P \<epsilon> ({V':T=\<lfloor>v\<rfloor>; Val u}) ({V:T=\<lfloor>v\<rfloor>; Val u}) h xs \<epsilon> (Val u) h (xs[V := v])"
  "V < length xs \<Longrightarrow> sim_move01 P \<epsilon> ({V':T=\<lfloor>v\<rfloor>; Throw a}) ({V:T=\<lfloor>v\<rfloor>; Throw a}) h xs \<epsilon> (Throw a) h (xs[V := v])"
apply(fastsimp simp add: sim_move01_def intro: converse_rtranclp_into_rtranclp Block1Some Block1Red)
apply(fastsimp simp add: sim_move01_def intro!: \<tau>red1't_2step[OF Block1Some] \<tau>red1'r_1step[OF Block1Some] Red1Block Block1Throw)+
done

lemmas sim_move01_intros =
  sim_move01_expr sim_move01_reds sim_move01_CallNull sim_move01_TryFail sim_move01_BlockSome sim_move01_CallParams

declare sim_move01_intros[intro]

lemma sim_move01_preserves_len: "sim_move01 P ta0 e0 e h xs ta e' h' xs' \<Longrightarrow> length xs' = length xs"
by(fastsimp simp add: sim_move01_def split: split_if_asm dest: \<tau>red1'r_preserves_len \<tau>red1't_preserves_len red1_preserves_len)

lemma sim_move01_preserves_unmod:
  "\<lbrakk> sim_move01 P ta0 e0 e h xs ta e' h' xs'; unmod e i; i < length xs \<rbrakk> \<Longrightarrow> xs' ! i = xs ! i"
apply(auto simp add: sim_move01_def split: split_if_asm dest: \<tau>red1't_preserves_unmod)
apply(frule (2) \<tau>red1'r_preserves_unmod)
apply(frule (1) \<tau>red1'r_unmod_preserved)
apply(frule \<tau>red1'r_preserves_len)
apply(auto dest: red1_preserves_unmod)
done

lemma assumes wf: "wf_J_prog P"
  shows red1_simulates_red_aux:
  "\<lbrakk> extTA2J0 P,P \<turnstile> \<langle>e1, S\<rangle> -TA\<rightarrow> \<langle>e1', S'\<rangle>; bisim vs e1 e2 XS; fv e1 \<subseteq> set vs;
     lcl S \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e1 \<le> length XS;
     \<forall>aMvs. call e1 = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P (hp S) aMvs \<rbrakk>
  \<Longrightarrow> \<exists>ta e2' XS'. sim_move01 (compP1 P) TA e1 e2 (hp S) XS ta e2' (hp S') XS' \<and> bisim vs e1' e2' XS' \<and> lcl S' \<subseteq>\<^sub>m [vs [\<mapsto>] XS']"
  (is "\<lbrakk> _; _; _; _; _; ?synth e1 S \<rbrakk> \<Longrightarrow> ?concl e1 e2 S XS e1' S' TA vs")

  and reds1_simulates_reds_aux:
  "\<lbrakk> extTA2J0 P,P \<turnstile> \<langle>es1, S\<rangle> [-TA\<rightarrow>] \<langle>es1', S'\<rangle>; bisims vs es1 es2 XS; fvs es1 \<subseteq> set vs;
    lcl S \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_varss es1 \<le> length XS;
    \<forall>aMvs. calls es1 = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P (hp S) aMvs \<rbrakk>
  \<Longrightarrow> \<exists>ta es2' xs'. sim_moves01 (compP1 P) TA es1 es2 (hp S) XS ta es2' (hp S') xs' \<and> bisims vs es1' es2' xs' \<and> lcl S' \<subseteq>\<^sub>m [vs [\<mapsto>] xs']"
  (is "\<lbrakk> _; _; _; _; _; ?synths es1 S \<rbrakk> \<Longrightarrow> ?concls es1 es2 S XS es1' S' TA vs")
proof(induct arbitrary: vs e2 XS and vs es2 XS rule: red_reds.inducts)
  case (BinOpRed1 e s ta e' s' bop e2 Vs E2 xs)
  note IH = `\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
            ?synth e s \<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs`
  from `extTA2J0 P,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>` have "\<not> is_val e" by auto
  with `bisim Vs (e \<guillemotleft>bop\<guillemotright> e2) E2 xs` obtain E
    where "E2 = E \<guillemotleft>bop\<guillemotright> compE1 Vs e2" and "bisim Vs e E xs" and "\<not> contains_insync e2" by auto
  with IH[of Vs E xs] `fv (e \<guillemotleft>bop\<guillemotright> e2) \<subseteq> set Vs` `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]` `\<not> is_val e`
    `length Vs + max_vars (e \<guillemotleft>bop\<guillemotright> e2) \<le> length xs` `?synth (e \<guillemotleft>bop\<guillemotright> e2) s` `extTA2J0 P,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  show ?case by(cases "is_val e'")(fastsimp elim!: sim_move01_expr)+
next
  case (BinOpRed2 e s ta e' s' v bop Vs E2 xs)
  note IH = `\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
            ?synth e s \<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs`
  from `bisim Vs (Val v \<guillemotleft>bop\<guillemotright> e) E2 xs` obtain E
    where "E2 = Val v \<guillemotleft>bop\<guillemotright> E" and "bisim Vs e E xs" by auto
  with IH[of Vs E xs] `fv (Val v \<guillemotleft>bop\<guillemotright> e) \<subseteq> set Vs` `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]`
    `length Vs + max_vars (Val v \<guillemotleft>bop\<guillemotright> e) \<le> length xs` `?synth (Val v \<guillemotleft>bop\<guillemotright> e) s` `extTA2J0 P,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  show ?case by(fastsimp elim!: sim_move01_expr)
next
  case RedVar thus ?case
    by(fastsimp simp add: index_less_aux map_le_def fun_upds_apply intro!: exI dest: bspec)
next
  case RedLAss thus ?case
    by(fastsimp intro: index_less_aux LAss_lem intro!: exI simp del: fun_upd_apply)
next
  case (AAccRed1 a s ta a' s' i Vs E2 xs)
  note IH = `\<And>vs e2 XS. \<lbrakk>bisim vs a e2 XS; fv a \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars a \<le> length XS;
            ?synth a s \<rbrakk> \<Longrightarrow> ?concl a e2 s XS a' s' ta vs`
  from `extTA2J0 P,P \<turnstile> \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>` have "\<not> is_val a" by auto
  with `bisim Vs (a\<lfloor>i\<rceil>) E2 xs` obtain E
    where "E2 = E\<lfloor>compE1 Vs i\<rceil>" and "bisim Vs a E xs" and "\<not> contains_insync i" by auto
  with IH[of Vs E xs] `fv (a\<lfloor>i\<rceil>) \<subseteq> set Vs` `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]` `\<not> is_val a`
    `length Vs + max_vars (a\<lfloor>i\<rceil>) \<le> length xs` `?synth (a\<lfloor>i\<rceil>) s` `extTA2J0 P,P \<turnstile> \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>`
  show ?case by(cases "is_val a'")(fastsimp elim!: sim_move01_expr)+
next
  case (AAccRed2 i s ta i' s' a Vs E2 xs)
  note IH = `\<And>vs e2 XS. \<lbrakk>bisim vs i e2 XS; fv i \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars i \<le> length XS;
            ?synth i s \<rbrakk> \<Longrightarrow> ?concl i e2 s XS i' s' ta vs`
  from `bisim Vs (Val a\<lfloor>i\<rceil>) E2 xs` obtain E
    where "E2 = Val a\<lfloor>E\<rceil>" and "bisim Vs i E xs" by auto
  with IH[of Vs E xs] `fv (Val a\<lfloor>i\<rceil>) \<subseteq> set Vs` `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]`
    `length Vs + max_vars (Val a\<lfloor>i\<rceil>) \<le> length xs` `?synth (Val a\<lfloor>i\<rceil>) s` `extTA2J0 P,P \<turnstile> \<langle>i,s\<rangle> -ta\<rightarrow> \<langle>i',s'\<rangle>`
  show ?case by(fastsimp elim!: sim_move01_expr)
next
  case RedAAcc thus ?case by(force intro!: exI)
next
  case (AAssRed1 a s ta a' s' i e Vs E2 xs)
  note IH = `\<And>vs e2 XS. \<lbrakk>bisim vs a e2 XS; fv a \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars a \<le> length XS;
            ?synth a s \<rbrakk> \<Longrightarrow> ?concl a e2 s XS a' s' ta vs`
  from `extTA2J0 P,P \<turnstile> \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>` have "\<not> is_val a" by auto
  with `bisim Vs (a\<lfloor>i\<rceil>:=e) E2 xs` obtain E
    where E2: "E2 = E\<lfloor>compE1 Vs i\<rceil>:=compE1 Vs e" and "bisim Vs a E xs"
    and sync: "\<not> contains_insync i" "\<not> contains_insync e" by auto
  with IH[of Vs E xs] `fv (a\<lfloor>i\<rceil>:=e) \<subseteq> set Vs` `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]` `\<not> is_val a` `extTA2J0 P,P \<turnstile> \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>`
    `length Vs + max_vars (a\<lfloor>i\<rceil>:=e) \<le> length xs` `?synth (a\<lfloor>i\<rceil>:=e) s`
  obtain ta' e2' xs'
    where IH': "sim_move01 (compP1 P) ta a E (hp s) xs ta' e2' (hp s') xs'"
    "bisim Vs a' e2' xs'" "lcl s' \<subseteq>\<^sub>m [Vs [\<mapsto>] xs']"
    by auto
  show ?case
  proof(cases "is_val a'")
    case True
    from `fv (a\<lfloor>i\<rceil>:=e) \<subseteq> set Vs` sync
    have "bisim Vs i (compE1 Vs i) xs'" "bisim Vs e (compE1 Vs e) xs'" by auto
    with IH' E2 True sync  `\<not> is_val a` `extTA2J0 P,P \<turnstile> \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>` show ?thesis
      by(cases "is_val i")(fastsimp elim!: sim_move01_expr)+
  next
    case False with IH' E2 sync `\<not> is_val a` `extTA2J0 P,P \<turnstile> \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>`
    show ?thesis by(fastsimp elim!: sim_move01_expr)
  qed
next
  case (AAssRed2 i s ta i' s' a e Vs E2 xs)
  note IH = `\<And>vs e2 XS. \<lbrakk>bisim vs i e2 XS; fv i \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars i \<le> length XS;
            ?synth i s \<rbrakk> \<Longrightarrow> ?concl i e2 s XS i' s' ta vs`
  from `extTA2J0 P,P \<turnstile> \<langle>i,s\<rangle> -ta\<rightarrow> \<langle>i',s'\<rangle>` have "\<not> is_val i" by auto
  with `bisim Vs (Val a\<lfloor>i\<rceil> := e) E2 xs` obtain E
    where "E2 = Val a\<lfloor>E\<rceil>:=compE1 Vs e" and "bisim Vs i E xs" and "\<not> contains_insync e" by auto
  with IH[of Vs E xs] `fv (Val a\<lfloor>i\<rceil>:=e) \<subseteq> set Vs` `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]` `\<not> is_val i` `extTA2J0 P,P \<turnstile> \<langle>i,s\<rangle> -ta\<rightarrow> \<langle>i',s'\<rangle>`
    `length Vs + max_vars (Val a\<lfloor>i\<rceil>:=e) \<le> length xs` `?synth (Val a\<lfloor>i\<rceil>:=e) s`
  show ?case by(cases "is_val i'")(fastsimp elim!: sim_move01_expr)+
next
  case (AAssRed3 e s ta e' s' a i Vs E2 xs)
  note IH = `\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
            ?synth e s \<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs`
  from `bisim Vs (Val a\<lfloor>Val i\<rceil> := e) E2 xs` obtain E
    where "E2 = Val a\<lfloor>Val i\<rceil>:=E" and "bisim Vs e E xs" by auto
  with IH[of Vs E xs] `fv (Val a\<lfloor>Val i\<rceil>:=e) \<subseteq> set Vs` `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]` `extTA2J0 P,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
    `length Vs + max_vars (Val a\<lfloor>Val i\<rceil>:=e) \<le> length xs` `?synth (Val a\<lfloor>Val i\<rceil>:=e) s`
  show ?case by(fastsimp elim!: sim_move01_expr)
next
  case RedAAssStore thus ?case by(auto intro!: exI)
next
  case (FAssRed1 e s ta e' s' F D e2 Vs E2 xs)
  note IH = `\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
            ?synth e s \<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs`
  from `extTA2J0 P,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>` have "\<not> is_val e" by auto
  with `bisim Vs (e\<bullet>F{D} := e2) E2 xs` obtain E
    where "E2 = E\<bullet>F{D} := compE1 Vs e2" and "bisim Vs e E xs" and "\<not> contains_insync e2" by auto
  with IH[of Vs E xs] `fv (e\<bullet>F{D} := e2) \<subseteq> set Vs` `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]` `\<not> is_val e` `extTA2J0 P,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
    `length Vs + max_vars (e\<bullet>F{D} := e2) \<le> length xs` `?synth (e\<bullet>F{D} := e2) s`
  show ?case by(cases "is_val e'")(fastsimp elim!: sim_move01_expr)+
next
  case (FAssRed2 e s ta e' s' v F D Vs E2 xs)
  note IH = `\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
            ?synth e s \<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs`
  from `bisim Vs (Val v\<bullet>F{D} := e) E2 xs` obtain E
    where "E2 = Val v\<bullet>F{D} := E" and "bisim Vs e E xs" by auto
  with IH[of Vs E xs] `fv (Val v\<bullet>F{D} := e) \<subseteq> set Vs` `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]` `extTA2J0 P,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
    `length Vs + max_vars (Val v\<bullet>F{D} := e) \<le> length xs` `?synth (Val v\<bullet>F{D} := e) s`
  show ?case by(fastsimp elim!: sim_move01_expr)
next
  case (CallObj e s ta e' s' M es Vs E2 xs)
  note IH = `\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
            ?synth e s \<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs`
  from `extTA2J0 P,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>` have "\<not> is_val e" by auto
  with `bisim Vs (e\<bullet>M(es)) E2 xs` obtain E
    where "E2 = E\<bullet>M(compEs1 Vs es)" and "bisim Vs e E xs" and "\<not> contains_insyncs es" by(auto)
  with IH[of Vs E xs] `fv (e\<bullet>M(es)) \<subseteq> set Vs` `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]`
    `length Vs + max_vars (e\<bullet>M(es)) \<le> length xs` `?synth (e\<bullet>M(es)) s`
  show ?case by(cases "is_val e'")(fastsimp elim!: sim_move01_expr split: split_if_asm)+
next
  case (CallParams es s ta es' s' v M Vs E2 xs)
  note IH = `\<And>vs es2 XS. \<lbrakk>bisims vs es es2 XS; fvs es \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_varss es \<le> length XS;
            ?synths es s \<rbrakk> \<Longrightarrow> ?concls es es2 s XS es' s' ta vs`
  from `bisim Vs (Val v\<bullet>M(es)) E2 xs` obtain Es 
    where "E2 = Val v\<bullet>M(Es)" and "bisims Vs es Es xs" by auto
  moreover from `extTA2J0 P,P \<turnstile> \<langle>es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>` have "\<not> is_vals es" by auto
  with `?synth (Val v\<bullet>M(es)) s` have "?synths es s" by(auto)
  moreover note IH[of Vs Es xs] `fv (Val v\<bullet>M(es)) \<subseteq> set Vs` `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]` 
    `length Vs + max_vars (Val v\<bullet>M(es)) \<le> length xs`
  ultimately show ?case by(fastsimp elim!: sim_move01_CallParams)
next
  case (RedCall s a C fs M Ts T pns body D vs Vs E2 xs)
  from `hp s a = \<lfloor>Obj C fs\<rfloor>` have "call (addr a\<bullet>M(map Val vs)) = \<lfloor>(a, M, vs)\<rfloor>" by auto
  with `?synth (addr a\<bullet>M(map Val vs)) s` have "synthesized_call P (hp s) (a, M, vs)" by auto
  with `\<not> is_external_call P (Class C) M` `hp s a = \<lfloor>Obj C fs\<rfloor>` have False
    by(simp add: synthesized_call_conv)
  thus ?case ..
next
  case (RedCallExternal s a T M vs ta va h' ta' e' s' Vs E2 xs)
  from `bisim Vs (addr a\<bullet>M(map Val vs)) E2 xs` have "E2 = addr a\<bullet>M(map Val vs)" by auto
  moreover note `is_external_call P T M` `typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>T\<rfloor>` `ta' = extTA2J0 P ta`
    `e' = extRet2J va` `s' = (h', lcl s)` `P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>` `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]`
  moreover from `typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>T\<rfloor>` have "hp s a \<noteq> None" by auto
  with wf `P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>`
  have "ta_bisim01 (extTA2J0 P ta) (extTA2J1 (compP1 P) ta)" by(rule red_external_ta_bisim01)
  ultimately show ?case apply(cases va)
    apply(auto simp del: split_paired_Ex simp add: sim_move01_def map_eq_append_conv)
     apply(rule exI conjI)+
     apply(clarsimp, fastsimp intro: Red1CallExternal simp add: map_eq_append_conv simp del: split_paired_Ex)
    apply(rule exI conjI)+
    apply(clarsimp, fastsimp intro: Red1CallExternal simp add: map_eq_append_conv simp del: split_paired_Ex)
    done
next
  case (BlockRed e h x V vo ta e' h' x' T Vs E2 xs)
  note IH = `\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl (h, x(V := vo)) \<subseteq>\<^sub>m [vs [\<mapsto>] XS];
                         length vs + max_vars e \<le> length XS; ?synth e (h, (x(V := vo)))\<rbrakk>
            \<Longrightarrow> ?concl e e2 (h, x(V := vo)) XS e' (h', x') ta vs`
  note red = `extTA2J0 P,P \<turnstile> \<langle>e,(h, x(V := vo))\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>`
  note len = `length Vs + max_vars {V:T=vo; e} \<le> length xs`
  from `fv {V:T=vo; e} \<subseteq> set Vs` have fv: "fv e \<subseteq> set (Vs@[V])" by auto
  from `bisim Vs {V:T=vo; e} E2 xs` show ?case
  proof(cases rule: bisim_cases(6)[consumes 1, case_names BlockNone BlockSome BlockSomeNone])
    case (BlockNone E')
    with red IH[of "Vs@[V]" E' xs] fv `lcl (h, x) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]`
      `length Vs + max_vars {V:T=vo; e} \<le> length xs` `?synth {V:T=vo; e} (h, x)`
    obtain TA' e2' xs' where red': "sim_move01 (compP1 P) ta e E' h xs TA' e2' h' xs'"
      and bisim': "bisim (Vs @ [V]) e' e2' xs'" "x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']" by auto 
    from red' `length Vs + max_vars {V:T=vo; e} \<le> length xs`
    have "length (Vs@[V]) + max_vars e \<le> length xs'"
      by(fastsimp simp add: sim_move01_def dest: red1_preserves_len \<tau>red1't_preserves_len \<tau>red1'r_preserves_len split: split_if_asm)
    with `x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']` have "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] xs', V \<mapsto> xs' ! length Vs]" by(simp)
    moreover 
    { assume "V \<in> set Vs"
      hence "hidden (Vs @ [V]) (index Vs V)" by(rule hidden_index)
      with `bisim (Vs @ [V]) e E' xs` have "unmod E' (index Vs V)"
	by -(rule hidden_bisim_unmod)
      moreover from `length Vs + max_vars {V:T=vo; e} \<le> length xs` `V \<in> set Vs`
      have "index Vs V < length xs" by(auto intro: index_less_aux)
      ultimately have "xs ! index Vs V = xs' ! index Vs V"
	using sim_move01_preserves_unmod[OF red'] by(simp) }
    moreover from red' have "length xs = length xs'" by(rule sim_move01_preserves_len[symmetric])
    ultimately have rel: "x'(V := x V) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs']"
      using `lcl (h, x) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]` `length Vs + max_vars {V:T=vo; e} \<le> length xs`
      by(auto intro: Block_lem)
    show ?thesis
    proof(cases "x' V")
      case None
      with red' bisim' BlockNone len
      show ?thesis by(fastsimp simp del: split_paired_Ex fun_upd_apply intro: rel)
    next
      case (Some v)
      moreover
      with `x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']` have "[Vs @ [V] [\<mapsto>] xs'] V = \<lfloor>v\<rfloor>"
	by(auto simp add: map_le_def dest: bspec)
      moreover
      from `length Vs + max_vars {V:T=vo; e} \<le> length xs` have "length Vs < length xs" by auto
      ultimately have "xs' ! length Vs = v" using `length xs = length xs'` by(simp)
      with red' bisim' BlockNone Some len
      show ?thesis by(fastsimp simp del: fun_upd_apply intro: rel)
    qed
  next
    case (BlockSome E' v)
    with red IH[of "Vs@[V]" E' "xs[length Vs := v]"] fv `lcl (h, x) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]`
      `length Vs + max_vars {V:T=vo; e} \<le> length xs` `?synth {V:T=vo; e} (h, x)`
    obtain TA' e2' xs' where red': "sim_move01 (compP1 P) ta e E' h (xs[length Vs := v]) TA' e2' h' xs'"
      and bisim': "bisim (Vs @ [V]) e' e2' xs'" "x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']" by auto
    from red' `length Vs + max_vars {V:T=vo; e} \<le> length xs`
    have "length (Vs@[V]) + max_vars e \<le> length xs'" by(auto dest: sim_move01_preserves_len)
    with `x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']` have "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] xs', V \<mapsto> xs' ! length Vs]" by(simp)
    moreover 
    { assume "V \<in> set Vs"
      hence "hidden (Vs @ [V]) (index Vs V)" by(rule hidden_index)
      with `bisim (Vs @ [V]) e E' (xs[length Vs := v])` have "unmod E' (index Vs V)"
	by -(rule hidden_bisim_unmod)
      moreover from `length Vs + max_vars {V:T=vo; e} \<le> length xs` `V \<in> set Vs`
      have "index Vs V < length xs" by(auto intro: index_less_aux)
      moreover from `length Vs + max_vars {V:T=vo; e} \<le> length xs` `V \<in> set Vs`
      have "(xs[length Vs := v]) ! index Vs V = xs ! index Vs V" by(simp)
      ultimately have "xs ! index Vs V = xs' ! index Vs V"
	using sim_move01_preserves_unmod[OF red', of "index Vs V"] by(simp) }
    moreover from red' have "length xs = length xs'" by(auto dest: sim_move01_preserves_len)
    ultimately have rel: "x'(V := x V) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs']"
      using `lcl (h, x) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]` `length Vs + max_vars {V:T=vo; e} \<le> length xs`
      by(auto intro: Block_lem)
    from BlockSome red obtain v' where Some: "x' V = \<lfloor>v'\<rfloor>" by(auto dest!: red_lcl_incr)
    with `x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']` have "[Vs @ [V] [\<mapsto>] xs'] V = \<lfloor>v'\<rfloor>"
      by(auto simp add: map_le_def dest: bspec)
    moreover
    from `length Vs + max_vars {V:T=vo; e} \<le> length xs` have "length Vs < length xs" by auto
    ultimately have "xs' ! length Vs = v'" using `length xs = length xs'` by(simp)
    with red' bisim' BlockSome Some `length Vs < length xs`
    show ?thesis by(fastsimp simp del: fun_upd_apply intro: rel)
  next 
    case (BlockSomeNone E')
    with red IH[of "Vs@[V]" E' xs] fv `lcl (h, x) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]`
      `length Vs + max_vars {V:T=vo; e} \<le> length xs` `?synth {V:T=vo; e} (h, x)`
    obtain TA' e2' xs' where red': "sim_move01 (compP1 P) ta e E' h xs TA' e2' h' xs'"
      and IH': "bisim (Vs @ [V]) e' e2' xs'" "x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']" by auto
    from red' `length Vs + max_vars {V:T=vo; e} \<le> length xs`
    have "length (Vs@[V]) + max_vars e \<le> length xs'" by(auto dest: sim_move01_preserves_len)
    with `x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']` have "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] xs', V \<mapsto> xs' ! length Vs]" by(simp)
    moreover 
    { assume "V \<in> set Vs"
      hence "hidden (Vs @ [V]) (index Vs V)" by(rule hidden_index)
      with `bisim (Vs @ [V]) e E' xs` have "unmod E' (index Vs V)"
	by -(rule hidden_bisim_unmod)
      moreover from `length Vs + max_vars {V:T=vo; e} \<le> length xs` `V \<in> set Vs`
      have "index Vs V < length xs" by(auto intro: index_less_aux)
      moreover from `length Vs + max_vars {V:T=vo; e} \<le> length xs` `V \<in> set Vs`
      have "(xs[length Vs := v]) ! index Vs V = xs ! index Vs V" by(simp)
      ultimately have "xs ! index Vs V = xs' ! index Vs V"
	using sim_move01_preserves_unmod[OF red', of "index Vs V"] by(simp) }
    moreover from red' have "length xs = length xs'" by(auto dest: sim_move01_preserves_len)
    ultimately have rel: "x'(V := x V) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs']"
      using `lcl (h, x) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]` `length Vs + max_vars {V:T=vo; e} \<le> length xs`
      by(auto intro: Block_lem)
    from BlockSomeNone red obtain v' where Some: "x' V = \<lfloor>v'\<rfloor>" by(auto dest!: red_lcl_incr)
    with `x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']` have "[Vs @ [V] [\<mapsto>] xs'] V = \<lfloor>v'\<rfloor>"
      by(auto simp add: map_le_def dest: bspec)
    moreover
    from `length Vs + max_vars {V:T=vo; e} \<le> length xs` have "length Vs < length xs" by auto
    ultimately have "xs' ! length Vs = v'" using `length xs = length xs'` by(simp)
    with red' IH' BlockSomeNone Some `length Vs < length xs`
    show ?thesis by(fastsimp simp del: fun_upd_apply intro: rel)
  qed
next
  case (RedBlock V T vo u s Vs E2 xs)
  from `bisim Vs {V:T=vo; Val u} E2 xs` obtain vo'
    where [simp]: "E2 = {length Vs:T=vo'; Val u}" by auto
  from RedBlock show ?case
  proof(cases vo)
    case (Some v)
    with `bisim Vs {V:T=vo; Val u} E2 xs`
    have vo': "case vo' of None \<Rightarrow> xs ! length Vs = v | Some v' \<Rightarrow> v = v'" by auto
    have "sim_move01 (compP1 P) \<epsilon> {V:T=vo; Val u} E2 (hp s) xs \<epsilon> (Val u) (hp s) (xs[length Vs := v])"
    proof(cases vo')
      case None with vo'
      have "xs[length Vs := v] = xs" by auto
      thus ?thesis using Some None by auto
    next
      case Some
      from `length Vs + max_vars {V:T=vo; Val u} \<le> length xs` have "length Vs < length xs" by simp
      with vo' Some show ?thesis using `vo = Some v` by auto
    qed
    thus ?thesis using RedBlock by fastsimp
  qed fastsimp
next
  case SynchronizedNull thus ?case by fastsimp
next
  case (LockSynchronized s a arrobj e Vs E2 xs)
  from `bisim Vs (sync(addr a) e) E2 xs`
  have E2: "E2 = sync\<^bsub>length Vs\<^esub> (addr a) (compE1 (Vs@[fresh_var Vs]) e)" 
    and sync: "\<not> contains_insync e" by auto
  moreover have "fresh_var Vs \<notin> set Vs" by(rule fresh_var_fresh)
  with `fv (sync(addr a) e) \<subseteq> set Vs` have "fresh_var Vs \<notin> fv e" by auto
  from E2 `fv (sync(addr a) e) \<subseteq> set Vs` sync
  have "bisim (Vs@[fresh_var Vs]) e (compE1 (Vs@[fresh_var Vs]) e) (xs[length Vs := Addr a])"
    by(auto intro!: compE1_bisim)
  hence "bisim Vs (insync(a) e) (insync\<^bsub>length Vs\<^esub> (a) (compE1 (Vs@[fresh_var Vs]) e)) (xs[length Vs := Addr a])"
    using `fresh_var Vs \<notin> fv e` `length Vs + max_vars (sync(addr a) e) \<le> length xs` by auto
  moreover from `hp s a = \<lfloor>arrobj\<rfloor>` `length Vs + max_vars (sync(addr a) e) \<le> length xs`
  have "compP1 P \<turnstile>1 \<langle>sync\<^bsub>length Vs\<^esub> (addr a) (compE1 (Vs@[fresh_var Vs]) e), (hp s, xs)\<rangle>
        -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Lock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace>\<rightarrow>
        \<langle>insync\<^bsub>length Vs\<^esub> (a) (compE1 (Vs@[fresh_var Vs]) e), (hp s, xs[length Vs := Addr a])\<rangle>"
    by -(rule Lock1Synchronized, auto)
  hence "sim_move01 (compP1 P) \<epsilon>\<lbrace>\<^bsub>l\<^esub>Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace> (sync(addr a) e) E2 (hp s) xs \<epsilon>\<lbrace>\<^bsub>l\<^esub>Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace> (insync\<^bsub>length Vs\<^esub> (a) (compE1 (Vs@[fresh_var Vs]) e)) (hp s) (xs[length Vs := Addr a])"
    using E2 by(fastsimp simp add: sim_move01_def ta_bisim_def)
  moreover have "zip Vs (xs[length Vs := Addr a]) = (zip Vs xs)[length Vs := (arbitrary, Addr a)]"
    by(rule sym)(simp add: update_zip)
  hence "zip Vs (xs[length Vs := Addr a]) = zip Vs xs" by simp
  with `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]` have "lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs[length Vs := Addr a]]"
    by(auto simp add: map_le_def map_upds_def)
  ultimately show ?case using `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]` by fastsimp
next
  case (SynchronizedRed2 e s ta e' s' a Vs E2 xs)
  note IH = `\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
            ?synth e s \<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs`
  from `bisim Vs (insync(a) e) E2 xs` obtain E
    where E2: "E2 = insync\<^bsub>length Vs\<^esub> (a) E" and bisim: "bisim (Vs@[fresh_var Vs]) e E xs"
    and xsa: "xs ! length Vs = Addr a" by auto
  from `fv (insync(a) e) \<subseteq> set Vs` fresh_var_fresh[of Vs] have fv: "fresh_var Vs \<notin> fv e" by auto
  from `length Vs + max_vars (insync(a) e) \<le> length xs` have "length Vs < length xs" by simp
  { assume "lcl s (fresh_var Vs) \<noteq> None"
    then obtain v where "lcl s (fresh_var Vs) = \<lfloor>v\<rfloor>" by auto
    with `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]` have "[Vs [\<mapsto>] xs] (fresh_var Vs) = \<lfloor>v\<rfloor>" 
      by(auto simp add: map_le_def dest: bspec)
    hence "fresh_var Vs \<in> set Vs" 
      by(auto simp add: map_upds_def set_zip dest!: map_of_SomeD )
    moreover have "fresh_var Vs \<notin> set Vs" by(rule fresh_var_fresh)
    ultimately have False by contradiction }
  hence "lcl s (fresh_var Vs) = None" by(cases "lcl s (fresh_var Vs)", auto)
  hence "(lcl s)(fresh_var Vs := None) = lcl s" by(auto intro: ext)
  moreover from `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]`
  have "(lcl s)(fresh_var Vs := None) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs, fresh_var Vs \<mapsto> xs ! length Vs]" by(simp)
  ultimately have "lcl s \<subseteq>\<^sub>m [Vs @ [fresh_var Vs] [\<mapsto>] xs]"
    using `length Vs < length xs` by(auto)
  with IH[of "Vs@[fresh_var Vs]" E xs] `fv (insync(a) e) \<subseteq> set Vs` bisim
    `length Vs + max_vars (insync(a) e) \<le> length xs` `?synth (insync(a) e) s` 
  obtain TA' e2' xs' where IH': "sim_move01 (compP1 P) ta e E (hp s) xs TA' e2' (hp s') xs'"
    "bisim (Vs @ [fresh_var Vs]) e' e2' xs'" "lcl s' \<subseteq>\<^sub>m [Vs @ [fresh_var Vs] [\<mapsto>] xs']" by auto
  from `extTA2J0 P,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>` have "dom (lcl s') \<subseteq> dom (lcl s) \<union> fv e" by(auto dest: red_dom_lcl)
  with fv `lcl s (fresh_var Vs) = None` have "(fresh_var Vs) \<notin> dom (lcl s')" by auto
  hence "lcl s' (fresh_var Vs) = None" by auto
  moreover from IH' have "length xs = length xs'" by(auto dest: sim_move01_preserves_len)
  moreover note `lcl s' \<subseteq>\<^sub>m [Vs @ [fresh_var Vs] [\<mapsto>] xs']` `length Vs < length xs`
  ultimately have "lcl s' \<subseteq>\<^sub>m [Vs [\<mapsto>] xs']" by(auto simp add: map_le_def dest: bspec)
  moreover from bisim fv have "unmod E (length Vs)" by(auto intro: bisim_fv_unmod)
  with IH' `length Vs < length xs` have "xs ! length Vs = xs' ! length Vs"
    by(auto dest!: sim_move01_preserves_unmod)
  with xsa have "xs' ! length Vs = Addr a" by simp
  ultimately show ?case using IH' E2 by(fastsimp)
next
  case (UnlockSynchronized a v s Vs E2 xs)
  from `bisim Vs (insync(a) Val v) E2 xs` have E2: "E2 = insync\<^bsub>length Vs\<^esub> (a) Val v" 
    and xsa: "xs ! length Vs = Addr a" by auto
  moreover from `length Vs + max_vars (insync(a) Val v) \<le> length xs` xsa
  have "compP1 P \<turnstile>1 \<langle>insync\<^bsub>length Vs\<^esub> (a) (Val v), (hp s, xs)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace>\<rightarrow> \<langle>Val v, (hp s, xs)\<rangle>"
    by-(rule Unlock1Synchronized, auto)
  hence "sim_move01 (compP1 P) \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace> (insync(a) Val v) (insync\<^bsub>length Vs\<^esub> (a) Val v) (hp s) xs \<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace> (Val v) (hp s) xs"
    by(fastsimp simp add: sim_move01_def ta_bisim_def)
  ultimately show ?case using `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]` by fastsimp
next
  case (RedWhile b c s Vs E2 xs)
  from `bisim Vs (while (b) c) E2 xs` have "E2 = while (compE1 Vs b) (compE1 Vs c)"
    and sync: "\<not> contains_insync b" "\<not> contains_insync c" by auto
  moreover have "compP1 P \<turnstile>1 \<langle>while(compE1 Vs b) (compE1 Vs c), (hp s, xs)\<rangle> 
                 -\<epsilon>\<rightarrow> \<langle>if (compE1 Vs b) (compE1 Vs c;;while(compE1 Vs b) (compE1 Vs c)) else unit, (hp s, xs)\<rangle>"
    by(rule Red1While)
  hence "sim_move01 (compP1 P) \<epsilon> (while (b) c) (while (compE1 Vs b) (compE1 Vs c)) (hp s) xs \<epsilon> (if (compE1 Vs b) (compE1 Vs c;;while(compE1 Vs b) (compE1 Vs c)) else unit) (hp s) xs"
    by(auto simp add: sim_move01_def)
  moreover from `fv (while (b) c) \<subseteq> set Vs` sync
  have "bisim Vs (if (b) (c;; while (b) c) else unit)
                 (if (compE1 Vs b) (compE1 Vs (c;; while(b) c)) else (compE1 Vs unit)) xs"
    by -(rule bisimCond, auto)
  ultimately show ?case using `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]`
    by(simp)((rule exI)+, erule conjI, auto)
next
  case (RedTryCatch s a D fs C V e2 Vs E2 xs)
  thus ?case by(auto intro!: exI)(auto intro!: compE1_bisim)
next
  case RedTryFail thus ?case by(auto intro!: exI)
next
  case (ListRed1 e s ta e' s' es Vs ES2 xs)
  note IH = `\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
                         ?synth e s\<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs`
  from `extTA2J0 P,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>` have "\<not> is_val e" by auto
  with `bisims Vs (e # es) ES2 xs` obtain E' 
    where "bisim Vs e E' xs" and ES2: "ES2 = E' # compEs1 Vs es" 
    and sync: "\<not> contains_insyncs es" by(auto)
  with IH[of Vs E' xs] `fvs (e # es) \<subseteq> set Vs` `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]` `extTA2J0 P,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
    `length Vs + max_varss (e # es) \<le> length xs` `?synths (e # es) s` `\<not> is_val e`
  show ?case by(cases "is_val e'")(fastsimp elim!: sim_moves01_expr split: split_if_asm)+
next
  case (ListRed2 es s ta es' s' v Vs ES2 xs)
  thus ?case by(fastsimp elim!: bisims_cases elim!: sim_moves01_expr)
next
  case CallThrowParams thus ?case
    by(fastsimp elim!:bisim_cases simp add: bisims_map_Val_Throw)
next
  case (BlockThrow V T vo a s Vs e2 xs) thus ?case
    by(cases vo)(fastsimp elim!: bisim_cases)+
next    
  case (SynchronizedThrow2 a ad s Vs E2 xs)
  from `bisim Vs (insync(a) Throw ad) E2 xs` have "xs ! length Vs = Addr a" by auto
  with `length Vs + max_vars (insync(a) Throw ad) \<le> length xs`
  have "compP1 P \<turnstile>1 \<langle>insync\<^bsub>length Vs\<^esub> (a) Throw ad, (hp s, xs)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace>\<rightarrow> \<langle>Throw ad, (hp s, xs)\<rangle>"
    by-(rule Synchronized1Throw2, auto)
  hence "sim_move01 (compP1 P) \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace> (insync(a) Throw ad) (insync\<^bsub>length Vs\<^esub> (a) Throw ad) (hp s) xs \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace> (Throw ad) (hp s) xs"
    by(fastsimp simp add: sim_move01_def ta_bisim_def expand_fun_eq expand_finfun_eq finfun_upd_apply split: split_if_asm)
  moreover note `lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]` `bisim Vs (insync(a) Throw ad) E2 xs`
  ultimately show ?case by(fastsimp)
qed(fastsimp simp del: fun_upd_apply split: split_if_asm)+

declare max_dest [iff del]

lemma map_upds_Some_eq_nth_index:
  assumes "[Vs [\<mapsto>] vs] V = \<lfloor>v\<rfloor>" "length Vs \<le> length vs"
  shows "vs ! index Vs V = v"
proof -
  from `[Vs [\<mapsto>] vs] V = \<lfloor>v\<rfloor>` have "V \<in> set Vs"
    by -(rule classical, auto)
  with `[Vs [\<mapsto>] vs] V = \<lfloor>v\<rfloor>` `length Vs \<le> length vs` show ?thesis
  proof(induct Vs arbitrary: vs)
    case Nil thus ?case by simp
  next
    case (Cons x xs ys)
    note IH = `\<And>vs. \<lbrakk> [xs [\<mapsto>] vs] V = \<lfloor>v\<rfloor>; length xs \<le> length vs; V \<in> set xs \<rbrakk> \<Longrightarrow> vs ! index xs V = v`
    from `[x # xs [\<mapsto>] ys] V = \<lfloor>v\<rfloor>` obtain y Ys where "ys = y # Ys" by(cases ys, auto)
    with `length (x # xs) \<le> length ys` have "length xs \<le> length Ys" by simp
    show ?case
    proof(cases "V \<in> set xs")
      case True
      with `[x # xs [\<mapsto>] ys] V = \<lfloor>v\<rfloor>` `length xs \<le> length Ys` `ys = y # Ys`
      have "[xs [\<mapsto>] Ys] V = \<lfloor>v\<rfloor>"
	apply(auto simp add: map_upds_def map_of_eq_None_iff set_zip image_Collect split: split_if_asm)
	apply(clarsimp simp add: in_set_conv_decomp)
	apply(erule_tac x="length ys" in allE)
	by(simp)
      with IH[OF this `length xs \<le> length Ys` True] `ys = y # Ys` True
      show ?thesis by(simp)
    next
      case False with `V \<in> set (x # xs)` have "x = V" by auto
      with False `[x # xs [\<mapsto>] ys] V = \<lfloor>v\<rfloor>` `ys = y # Ys` have "y = v"
	by(auto)
      with False `x = V` `ys = y # Ys` 
      show ?thesis by(simp)
    qed
  qed
qed

declare split_paired_Ex [simp del]

lemmas \<tau>red0r_expr =
  NewArray_\<tau>red0r_xt Cast_\<tau>red0r_xt BinOp_\<tau>red0r_xt1 BinOp_\<tau>red0r_xt2 LAss_\<tau>red0r
  AAcc_\<tau>red0r_xt1 AAcc_\<tau>red0r_xt2 AAss_\<tau>red0r_xt1 AAss_\<tau>red0r_xt2 AAss_\<tau>red0r_xt3
  ALength_\<tau>red0r_xt FAcc_\<tau>red0r_xt FAss_\<tau>red0r_xt1 FAss_\<tau>red0r_xt2 Call_\<tau>red0r_obj
  Call_\<tau>red0r_param Block_\<tau>red0r_xt Sync_\<tau>red0r_xt InSync_\<tau>red0r_xt
  Seq_\<tau>red0r_xt Cond_\<tau>red0r_xt Throw_\<tau>red0r_xt Try_\<tau>red0r_xt

lemmas \<tau>red0t_expr =
  NewArray_\<tau>red0t_xt Cast_\<tau>red0t_xt BinOp_\<tau>red0t_xt1 BinOp_\<tau>red0t_xt2 LAss_\<tau>red0t
  AAcc_\<tau>red0t_xt1 AAcc_\<tau>red0t_xt2 AAss_\<tau>red0t_xt1 AAss_\<tau>red0t_xt2 AAss_\<tau>red0t_xt3
  ALength_\<tau>red0t_xt FAcc_\<tau>red0t_xt FAss_\<tau>red0t_xt1 FAss_\<tau>red0t_xt2 Call_\<tau>red0t_obj
  Call_\<tau>red0t_param Block_\<tau>red0t_xt Sync_\<tau>red0t_xt InSync_\<tau>red0t_xt
  Seq_\<tau>red0t_xt Cond_\<tau>red0t_xt Throw_\<tau>red0t_xt Try_\<tau>red0t_xt

declare \<tau>red0r_expr [elim!]
declare \<tau>red0t_expr [elim!]

primrec countInitBlock :: "('a, 'b) exp \<Rightarrow> nat"
  and countInitBlocks :: "('a, 'b) exp list \<Rightarrow> nat"
where 
  "countInitBlock (new C) = 0"
| "countInitBlock (newA T\<lfloor>e\<rceil>) = countInitBlock e"
| "countInitBlock (Cast T e) = countInitBlock e"
| "countInitBlock (Val v) = 0"
| "countInitBlock (Var V) = 0"
| "countInitBlock (V := e) = countInitBlock e"
| "countInitBlock (e \<guillemotleft>bop\<guillemotright> e') = countInitBlock e + countInitBlock e'"
| "countInitBlock (a\<lfloor>i\<rceil>) = countInitBlock a + countInitBlock i"
| "countInitBlock (AAss a i e) = countInitBlock a + countInitBlock i + countInitBlock e"
| "countInitBlock (a\<bullet>length) = countInitBlock a"
| "countInitBlock (e\<bullet>F{D}) = countInitBlock e"
| "countInitBlock (FAss e F D e') = countInitBlock e + countInitBlock e'"
| "countInitBlock (e\<bullet>M(es)) = countInitBlock e + countInitBlocks es"
| "countInitBlock ({V:T=vo; e}) = (case vo of None \<Rightarrow> 0 | Some v \<Rightarrow> 1) + countInitBlock e"
| "countInitBlock (sync\<^bsub>V'\<^esub> (e) e') = countInitBlock e + countInitBlock e'"
| "countInitBlock (insync\<^bsub>V'\<^esub> (ad) e) = countInitBlock e"
| "countInitBlock (e;;e') = countInitBlock e + countInitBlock e'"
| "countInitBlock (if (e) e1 else e2) = countInitBlock e + countInitBlock e1 + countInitBlock e2"
| "countInitBlock (while(b) e) = countInitBlock b + countInitBlock e"
| "countInitBlock (throw e) = countInitBlock e"
| "countInitBlock (try e catch(C V) e') = countInitBlock e + countInitBlock e'"

| "countInitBlocks [] = 0"
| "countInitBlocks (e # es) = countInitBlock e + countInitBlocks es"


definition sim_move10 :: 
  "J_prog \<Rightarrow> external_thread_action \<Rightarrow> expr1 \<Rightarrow> expr1 \<Rightarrow> expr \<Rightarrow> heap \<Rightarrow> locals \<Rightarrow> J0_thread_action \<Rightarrow> expr \<Rightarrow> heap \<Rightarrow> locals \<Rightarrow> bool"
where
  "sim_move10 P ta1 e1 e1' e h xs ta e' h' xs' \<longleftrightarrow> \<not> final e1 \<and>
  (if \<tau>move1 P h e1 then (\<tau>red0t (extTA2J0 P) P h (e, xs) (e', xs') \<or> countInitBlock e1' < countInitBlock e1 \<and> e' = e \<and> xs' = xs) \<and> h' = h \<and> ta1 = \<epsilon> \<and> ta = \<epsilon>
    else \<exists>e'' xs''. \<tau>red0r (extTA2J0 P) P h (e, xs) (e'', xs'') \<and> extTA2J0 P,P \<turnstile> \<langle>e'', (h, xs'')\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle> \<and> no_call P h e'' \<and> \<not> \<tau>move0 P h e'' \<and> ta_bisim01 ta (extTA2J1 (compP1 P) ta1))"

definition sim_moves10 :: 
  "J_prog \<Rightarrow> external_thread_action \<Rightarrow> expr1 list \<Rightarrow> expr1 list \<Rightarrow> expr list \<Rightarrow> heap \<Rightarrow> locals \<Rightarrow> J0_thread_action \<Rightarrow> expr list \<Rightarrow> heap \<Rightarrow> locals \<Rightarrow> bool"
where
  "sim_moves10 P ta1 es1 es1' es h xs ta es' h' xs' \<longleftrightarrow> \<not> finals es1 \<and>
  (if \<tau>moves1 P h es1 then (\<tau>reds0t (extTA2J0 P) P h (es, xs) (es', xs') \<or> countInitBlocks es1' < countInitBlocks es1 \<and> es' = es \<and> xs' = xs) \<and> h' = h \<and> ta1 = \<epsilon> \<and> ta = \<epsilon>
    else \<exists>es'' xs''. \<tau>reds0r (extTA2J0 P) P h (es, xs) (es'', xs'') \<and> extTA2J0 P,P \<turnstile> \<langle>es'', (h, xs'')\<rangle> [-ta\<rightarrow>] \<langle>es', (h', xs')\<rangle> \<and> no_calls P h es'' \<and> \<not> \<tau>moves0 P h es'' \<and> ta_bisim01 ta (extTA2J1 (compP1 P) ta1))"

lemma sim_move10_expr:
  assumes "sim_move10 P ta1 e1 e1' e h xs ta e' h' xs'"
  shows
  "sim_move10 P ta1 (newA T\<lfloor>e1\<rceil>) (newA T\<lfloor>e1'\<rceil>) (newA T\<lfloor>e\<rceil>) h xs ta (newA T\<lfloor>e'\<rceil>) h' xs'"
  "sim_move10 P ta1 (Cast T e1) (Cast T e1') (Cast T e) h xs ta (Cast T e') h' xs'"
  "sim_move10 P ta1 (e1 \<guillemotleft>bop\<guillemotright> e2) (e1' \<guillemotleft>bop\<guillemotright> e2) (e \<guillemotleft>bop\<guillemotright> e2') h xs ta (e' \<guillemotleft>bop\<guillemotright> e2') h' xs'"
  "sim_move10 P ta1 (Val v \<guillemotleft>bop\<guillemotright> e1) (Val v \<guillemotleft>bop\<guillemotright> e1') (Val v \<guillemotleft>bop\<guillemotright> e) h xs ta (Val v \<guillemotleft>bop\<guillemotright> e') h' xs'"
  "sim_move10 P ta1 (V := e1) (V := e1') (V' := e) h xs ta (V' := e') h' xs'"
  "sim_move10 P ta1 (e1\<lfloor>e2\<rceil>) (e1'\<lfloor>e2\<rceil>) (e\<lfloor>e2'\<rceil>) h xs ta (e'\<lfloor>e2'\<rceil>) h' xs'"
  "sim_move10 P ta1 (Val v\<lfloor>e1\<rceil>) (Val v\<lfloor>e1'\<rceil>) (Val v\<lfloor>e\<rceil>) h xs ta (Val v\<lfloor>e'\<rceil>) h' xs'"
  "sim_move10 P ta1 (e1\<lfloor>e2\<rceil> := e3) (e1'\<lfloor>e2\<rceil> := e3) (e\<lfloor>e2'\<rceil> := e3') h xs ta (e'\<lfloor>e2'\<rceil> := e3') h' xs'"
  "sim_move10 P ta1 (Val v\<lfloor>e1\<rceil> := e3) (Val v\<lfloor>e1'\<rceil> := e3) (Val v\<lfloor>e\<rceil> := e3') h xs ta (Val v\<lfloor>e'\<rceil> := e3') h' xs'"
  "sim_move10 P ta1 (AAss (Val v) (Val v') e1) (AAss (Val v) (Val v') e1') (AAss (Val v) (Val v') e) h xs ta (AAss (Val v) (Val v') e') h' xs'"
  "sim_move10 P ta1 (e1\<bullet>length) (e1'\<bullet>length) (e\<bullet>length) h xs ta (e'\<bullet>length) h' xs'"
  "sim_move10 P ta1 (e1\<bullet>F{D}) (e1'\<bullet>F{D}) (e\<bullet>F'{D'}) h xs ta (e'\<bullet>F'{D'}) h' xs'"
  "sim_move10 P ta1 (FAss e1 F D e2) (FAss e1' F D e2) (FAss e F' D' e2') h xs ta (FAss e' F' D' e2') h' xs'"
  "sim_move10 P ta1 (FAss (Val v) F D e1) (FAss (Val v) F D e1') (FAss (Val v) F' D' e) h xs ta (FAss (Val v) F' D' e') h' xs'"
  "sim_move10 P ta1 (e1\<bullet>M(es)) (e1'\<bullet>M(es)) (e\<bullet>M(es')) h xs ta (e'\<bullet>M(es')) h' xs'"
  "sim_move10 P ta1 (sync\<^bsub>V\<^esub>(e1) e2) (sync\<^bsub>V\<^esub>(e1') e2) (sync(e) e2') h xs ta (sync(e') e2') h' xs'"
  "sim_move10 P ta1 (insync\<^bsub>V\<^esub>(a) e1) (insync\<^bsub>V\<^esub>(a) e1') (insync(a') e) h xs ta (insync(a') e') h' xs'"
  "sim_move10 P ta1 (e1;;e2) (e1';;e2) (e;;e2') h xs ta (e';;e2') h' xs'"
  "sim_move10 P ta1 (if (e1) e2 else e3) (if (e1') e2 else e3) (if (e) e2' else e3') h xs ta (if (e') e2' else e3') h' xs'"
  "sim_move10 P ta1 (throw e1) (throw e1') (throw e) h xs ta (throw e') h' xs'"
  "sim_move10 P ta1 (try e1 catch(C V) e2) (try e1' catch(C V) e2) (try e catch(C' V') e2') h xs ta (try e' catch(C' V') e2') h' xs'"
using assms
by-(clarsimp simp add: sim_move10_def final_iff,rule conjI,force,fastsimp intro: red_reds.intros)+

lemma sim_moves10_expr:
  "sim_move10 P ta1 e1 e1' e h xs ta e' h' xs' \<Longrightarrow> sim_moves10 P ta1 (e1 # es2) (e1' # es2) (e # es2') h xs ta (e' # es2') h' xs'"
  "sim_moves10 P ta1 es1 es1' es h xs ta es' h' xs' \<Longrightarrow> sim_moves10 P ta1 (Val v # es1) (Val v # es1') (Val v # es) h xs ta (Val v # es') h' xs'"
unfolding sim_moves10_def sim_move10_def final_iff finals_def
apply(auto simp add: Cons_eq_append_conv)
apply(fastsimp intro!: \<tau>red0r_inj_\<tau>reds0r \<tau>reds0r_cons_\<tau>reds0r \<tau>red0t_inj_\<tau>reds0t \<tau>reds0t_cons_\<tau>reds0t ListRed1 ListRed2)+
done

lemma sim_move10_CallParams:
  "sim_moves10 P ta1 es1 es1' es h xs ta es' h' xs' \<Longrightarrow> sim_move10 P ta1 (Val v\<bullet>M(es1)) (Val v\<bullet>M(es1')) (Val v\<bullet>M(es)) h xs ta (Val v\<bullet>M(es')) h' xs'"
by(fastsimp simp add: sim_move10_def sim_moves10_def intro: Call_\<tau>red0r_param Call_\<tau>red0t_param CallParams)

lemma sim_move10_Block:
  "sim_move10 P ta1 e1 e1' e h (xs(V' := vo)) ta e' h' xs'
  \<Longrightarrow> sim_move10 P ta1 ({V:T=None; e1}) ({V:T=None; e1'}) ({V':T=vo; e}) h xs ta ({V':T=xs' V'; e'}) h' (xs'(V' := xs V'))"
proof -
  assume "sim_move10 P ta1 e1 e1' e h (xs(V' := vo)) ta e' h' xs'"
  moreover {
    fix e'' xs''
    assume "extTA2J0 P,P \<turnstile> \<langle>e'',(h, xs'')\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>"
    hence "extTA2J0 P,P \<turnstile> \<langle>e'',(h, xs''(V' := xs V', V' := xs'' V'))\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>" by simp
    from BlockRed[OF this, of T]
    have "extTA2J0 P,P \<turnstile> \<langle>{V':T=xs'' V'; e''},(h, xs''(V' := xs V'))\<rangle> -ta\<rightarrow> \<langle>{V':T=xs' V'; e'},(h', xs'(V' := xs V'))\<rangle>"
      by simp }
  ultimately show ?thesis
    by(fastsimp simp add: sim_move10_def final_iff split: split_if_asm)
qed

lemma sim_move10_reds:
  "\<lbrakk> new_Addr h = \<lfloor>a\<rfloor>; P \<turnstile> C has_fields FDTs \<rbrakk>
  \<Longrightarrow> sim_move10 P \<epsilon> (new C) e1' (new C) h xs \<epsilon> (addr a) (h(a\<mapsto>(Obj C (init_fields FDTs)))) xs"
  "new_Addr h = None \<Longrightarrow> sim_move10 P \<epsilon> (new C) e1' (new C) h xs \<epsilon> (THROW OutOfMemory) h xs"
  "\<lbrakk> new_Addr h = \<lfloor>a\<rfloor>; i \<ge> 0; h' = h(a \<mapsto> (Arr T (replicate (nat i) (default_val T)))) \<rbrakk>
  \<Longrightarrow> sim_move10 P \<epsilon> (newA T\<lfloor>Val (Intg i)\<rceil>) e1' (newA T\<lfloor>Val (Intg i)\<rceil>) h xs \<epsilon> (addr a) h' xs"
  "i < 0 \<Longrightarrow> sim_move10 P \<epsilon> (newA T\<lfloor>Val (Intg i)\<rceil>) e1' (newA T\<lfloor>Val (Intg i)\<rceil>) h xs \<epsilon> (THROW NegativeArraySize) h xs"
  "\<lbrakk> new_Addr h = None; i \<ge> 0 \<rbrakk>
  \<Longrightarrow> sim_move10 P \<epsilon> (newA T\<lfloor>Val (Intg i)\<rceil>) e1' (newA T\<lfloor>Val (Intg i)\<rceil>) h xs \<epsilon> (THROW OutOfMemory) h xs"
  "\<lbrakk> typeof\<^bsub>h\<^esub> v = \<lfloor>U\<rfloor>; P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> sim_move10 P \<epsilon> (Cast T (Val v)) e1' (Cast T (Val v)) h xs \<epsilon> (Val v) h xs"
  "\<lbrakk> typeof\<^bsub>h\<^esub> v = \<lfloor>U\<rfloor>; \<not> P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> sim_move10 P \<epsilon> (Cast T (Val v)) e1' (Cast T (Val v)) h xs \<epsilon> (THROW ClassCast) h xs"
  "binop bop v1 v2 = Some v \<Longrightarrow> sim_move10 P \<epsilon> ((Val v1) \<guillemotleft>bop\<guillemotright> (Val v2)) e1' (Val v1 \<guillemotleft>bop\<guillemotright> Val v2) h xs \<epsilon> (Val v) h xs"
  "xs V = \<lfloor>v\<rfloor> \<Longrightarrow> sim_move10 P \<epsilon> (Var V') e1' (Var V) h xs \<epsilon> (Val v) h xs"
  "sim_move10 P \<epsilon> (V' := Val v) e1' (V := Val v) h xs \<epsilon> unit h (xs(V \<mapsto> v))"
  "sim_move10 P \<epsilon> (null\<lfloor>Val v\<rceil>) e1' (null\<lfloor>Val v\<rceil>) h xs \<epsilon> (THROW NullPointer) h xs"
  "\<lbrakk> h a = \<lfloor>Arr T el\<rfloor>; i < 0 \<or> i \<ge> int (length el) \<rbrakk>
  \<Longrightarrow> sim_move10 P \<epsilon> (addr a\<lfloor>Val (Intg i)\<rceil>) e1' ((addr a)\<lfloor>Val (Intg i)\<rceil>) h xs \<epsilon> (THROW ArrayIndexOutOfBounds) h xs"
  "\<lbrakk> h a = \<lfloor>Arr T el\<rfloor>; i \<ge> 0; i < int (length el) \<rbrakk>
  \<Longrightarrow> sim_move10 P \<epsilon> (addr a\<lfloor>Val (Intg i)\<rceil>) e1' ((addr a)\<lfloor>Val (Intg i)\<rceil>) h xs \<epsilon> (Val (el ! nat i)) h xs"
  "sim_move10 P \<epsilon> (null\<lfloor>Val v\<rceil> := Val v') e1' (null\<lfloor>Val v\<rceil> := Val v') h xs \<epsilon> (THROW NullPointer) h xs"
  "\<lbrakk> h a = \<lfloor>Arr T el\<rfloor>; i < 0 \<or> i \<ge> int (length el) \<rbrakk>
  \<Longrightarrow> sim_move10 P \<epsilon> (AAss (addr a) (Val (Intg i)) (Val v)) e1' (AAss (addr a) (Val (Intg i)) (Val v)) h xs \<epsilon> (THROW ArrayIndexOutOfBounds) h xs"
 "\<lbrakk> h a = \<lfloor>Arr T el\<rfloor>; i \<ge> 0; i < int (length el); typeof\<^bsub>h\<^esub> v = \<lfloor>U\<rfloor>; \<not> (P \<turnstile> U \<le> T) \<rbrakk>
  \<Longrightarrow> sim_move10 P \<epsilon> (AAss (addr a) (Val (Intg i)) (Val v)) e1' (AAss (addr a) (Val (Intg i)) (Val v)) h xs \<epsilon> (THROW ArrayStore) h xs"
  "\<lbrakk> h a = \<lfloor>Arr T el\<rfloor>; i \<ge> 0; i < int (length el); typeof\<^bsub>h\<^esub> v = Some U; P \<turnstile> U \<le> T; h' = h(a \<mapsto> (Arr T (el[nat i := v]))) \<rbrakk>
  \<Longrightarrow> sim_move10 P \<epsilon> (AAss (addr a) (Val (Intg i)) (Val v)) e1' (AAss (addr a) (Val (Intg i)) (Val v)) h xs \<epsilon> unit h' xs"
  "h a = \<lfloor>Arr T elem\<rfloor> \<Longrightarrow> sim_move10 P \<epsilon> (addr a\<bullet>length) e1' (addr a\<bullet>length) h xs \<epsilon> (Val (Intg (int (length elem)))) h xs"
  "sim_move10 P \<epsilon> (null\<bullet>length) e1' (null\<bullet>length) h xs \<epsilon> (THROW NullPointer) h xs"
  "\<lbrakk> h a = \<lfloor>Obj C fs\<rfloor>; fs (F,D) = Some v \<rbrakk>
  \<Longrightarrow> sim_move10 P \<epsilon> (addr a\<bullet>F{D}) e1' (addr a\<bullet>F{D}) h xs \<epsilon> (Val v) h xs"
  "sim_move10 P \<epsilon> (null\<bullet>F{D}) e1' (null\<bullet>F{D}) h xs \<epsilon> (THROW NullPointer) h xs"
  "h a = \<lfloor>Obj C fs\<rfloor>
  \<Longrightarrow> sim_move10 P \<epsilon> (addr a\<bullet>F{D} := Val v) e1' (addr a\<bullet>F{D} := Val v) h xs \<epsilon> unit (h(a \<mapsto> (Obj C (fs((F,D) \<mapsto> v))))) xs"
  "sim_move10 P \<epsilon> (null\<bullet>F{D} := Val v) e1' (null\<bullet>F{D} := Val v) h xs \<epsilon> (THROW NullPointer) h xs"
  "sim_move10 P \<epsilon> ({V':T=None; Val u}) e1' ({V:T=vo; Val u}) h xs \<epsilon> (Val u) h xs"
  "sim_move10 P \<epsilon> ({V':T=\<lfloor>v\<rfloor>; e}) ({V':T=None; e}) ({V:T=vo; e'}) h xs \<epsilon> ({V:T=vo; e'}) h xs"
  "sim_move10 P \<epsilon> (sync\<^bsub>V'\<^esub>(null) e0) e1' (sync(null) e1) h xs \<epsilon> (THROW NullPointer) h xs"
  "sim_move10 P \<epsilon> (Val v;;e0) e1' (Val v;; e1) h xs \<epsilon> e1 h xs"
  "sim_move10 P \<epsilon> (if (true) e0 else e0') e1' (if (true) e1 else e2) h xs \<epsilon> e1 h xs"
  "sim_move10 P \<epsilon> (if (false) e0 else e0') e1' (if (false) e1 else e2) h xs \<epsilon> e2 h xs"
  "sim_move10 P \<epsilon> (throw null) e1' (throw null) h xs \<epsilon> (THROW NullPointer) h xs"
  "sim_move10 P \<epsilon> (try (Val v) catch(C V') e0) e1' (try (Val v) catch(C V) e1) h xs \<epsilon> (Val v) h xs"
  "\<lbrakk> h a = \<lfloor>Obj D fs\<rfloor>; P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> sim_move10 P \<epsilon> (try (Throw a) catch(C V') e0) e1' (try (Throw a) catch(C V) e1) h xs \<epsilon> ({V:Class C=\<lfloor>Addr a\<rfloor>; e1}) h xs"
  "sim_move10 P \<epsilon> (newA T\<lfloor>Throw a\<rceil>) e1' (newA T\<lfloor>Throw a\<rceil>) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (Cast T (Throw a)) e1' (Cast T (Throw a)) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> ((Throw a) \<guillemotleft>bop\<guillemotright> e0) e1' ((Throw a) \<guillemotleft>bop\<guillemotright> e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (Val v \<guillemotleft>bop\<guillemotright> (Throw a)) e1' (Val v \<guillemotleft>bop\<guillemotright> (Throw a)) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (V' := Throw a) e1' (V := Throw a) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (Throw a\<lfloor>e0\<rceil>) e1' (Throw a\<lfloor>e1\<rceil>) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (Val v\<lfloor>Throw a\<rceil>) e1' (Val v\<lfloor>Throw a\<rceil>) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (Throw a\<lfloor>e0\<rceil> := e0') e1' (Throw a\<lfloor>e1\<rceil> := e2) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (Val v\<lfloor>Throw a\<rceil> := e0) e1' (Val v\<lfloor>Throw a\<rceil> := e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (Val v\<lfloor>Val v'\<rceil> := Throw a) e1' (Val v\<lfloor>Val v'\<rceil> := Throw a) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (Throw a\<bullet>length) e1' (Throw a\<bullet>length) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (Throw a\<bullet>F{D}) e1' (Throw a\<bullet>F{D}) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (Throw a\<bullet>F{D} := e0) e1' (Throw a\<bullet>F{D} := e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (Val v\<bullet>F{D} := Throw a) e1' (Val v\<bullet>F{D} := Throw a) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (Throw a\<bullet>M(es0)) e1' (Throw a\<bullet>M(es1)) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (Val v\<bullet>M(map Val vs @ Throw a # es0)) e1' (Val v\<bullet>M(map Val vs @ Throw a # es1)) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> ({V':T=None; Throw a}) e1' ({V:T=vo; Throw a}) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (sync\<^bsub>V'\<^esub>(Throw a) e0) e1' (sync(Throw a) e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (Throw a;;e0) e1' (Throw a;;e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (if (Throw a) e0 else e0') e1' (if (Throw a) e1 else e2) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P \<epsilon> (throw (Throw a)) e1' (throw (Throw a)) h xs \<epsilon> (Throw a) h xs"
by(fastsimp simp add: sim_move10_def no_calls_def no_call_def intro: red_reds.intros)+

lemma sim_move10_CallNull:
  "sim_move10 P \<epsilon> (null\<bullet>M(map Val vs)) e1' (null\<bullet>M(map Val vs)) h xs \<epsilon> (THROW NullPointer) h xs"
by(fastsimp simp add: sim_move10_def map_eq_append_conv intro: RedCallNull)

lemma sim_move10_SyncLocks:
  "\<lbrakk> h a = \<lfloor>arrobj\<rfloor>; ta1 = \<epsilon>\<lbrace>\<^bsub>l\<^esub> Lock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace>; ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub> Lock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace> \<rbrakk>
   \<Longrightarrow> sim_move10 P ta1 (sync\<^bsub>V\<^esub>(addr a) e0) e1' (sync(addr a) e1) h xs ta (insync(a) e1) h xs"
  "\<lbrakk> ta1 = \<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace>; ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move10 P ta1 (insync\<^bsub>V\<^esub>(a') (Val v)) e1' (insync(a) (Val v)) h xs ta (Val v) h xs"
  "\<lbrakk> ta1 = \<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace>; ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move10 P ta1 (insync\<^bsub>V\<^esub>(a') (Throw a'')) e1' (insync(a) (Throw a'')) h xs ta (Throw a'') h xs"
by(fastsimp simp add: sim_move10_def ta_bisim_def intro: red_reds.intros[simplified])+

lemma sim_move10_TryFail:
  "\<lbrakk> h a = \<lfloor>Obj D fs\<rfloor>; \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> sim_move10 P \<epsilon> (try (Throw a) catch(C V') e0) e1' (try (Throw a) catch(C V) e1) h xs \<epsilon> (Throw a) h xs"
by(auto simp add: sim_move10_def intro!: RedTryFail)

lemmas sim_move10_intros =
  sim_move10_expr sim_move10_reds sim_move10_CallNull sim_move10_TryFail sim_move10_Block sim_move10_CallParams

lemma sim_move10_preserves_defass:
  assumes wf: "wf_J_prog P"
  shows "\<lbrakk> sim_move10 P ta1 e1 e1' e h xs ta e' h' xs'; \<D> e \<lfloor>dom xs\<rfloor> \<rbrakk> \<Longrightarrow> \<D> e' \<lfloor>dom xs'\<rfloor>"
by(auto simp add: sim_move10_def split: split_if_asm dest!: \<tau>red0r_preserves_defass[OF wf] \<tau>red0t_preserves_defass[OF wf] red_preserves_defass[OF wf])

declare sim_move10_intros[intro]

lemma assumes wf: "wf_J_prog P"
  shows red_simulates_red1_aux:
  "\<lbrakk> compP1 P \<turnstile>1 \<langle>e1, S\<rangle> -TA\<rightarrow> \<langle>e1', S'\<rangle>; bisim vs e2 e1 (lcl S); fv e2 \<subseteq> set vs;
     x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl S]; length vs + max_vars e1 \<le> length (lcl S);
     \<D> e2 \<lfloor>dom x\<rfloor>; \<not> IUF e1 TA e1' \<rbrakk>
  \<Longrightarrow> \<exists>ta e2' x'. sim_move10 P TA e1 e1' e2 (hp S) x ta e2' (hp S') x' \<and> bisim vs e2' e1' (lcl S') \<and> x' \<subseteq>\<^sub>m [vs [\<mapsto>] lcl S']"
  (is "\<lbrakk> _; _; _; _; _; _; _ \<rbrakk> \<Longrightarrow> ?concl e1 e1' e2 S x TA S' e1' vs")

  and reds_simulates_reds1_aux:
  "\<lbrakk> compP1 P \<turnstile>1 \<langle>es1, S\<rangle> [-TA\<rightarrow>] \<langle>es1', S'\<rangle>; bisims vs es2 es1 (lcl S); fvs es2 \<subseteq> set vs;
     x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl S]; length vs + max_varss es1 \<le> length (lcl S);
     \<D>s es2 \<lfloor>dom x\<rfloor>; \<not> IUFs es1 TA es1' \<rbrakk>
  \<Longrightarrow> \<exists>ta es2' x'. sim_moves10 P TA es1 es1' es2 (hp S) x ta es2' (hp S') x' \<and> bisims vs es2' es1' (lcl S') \<and> x' \<subseteq>\<^sub>m [vs [\<mapsto>] lcl S']"
  (is "\<lbrakk> _; _; _; _; _; _; _ \<rbrakk> \<Longrightarrow> ?concls es1 es1' es2 S x TA S' es1' vs")
proof(induct arbitrary: vs e2 x and vs es2 x rule: red1_reds1.inducts)
  case (Bin1OpRed1 e s ta e' s' bop e2 Vs E2 X)
  note IH = `\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>; \<not> IUF e ta e'\<rbrakk>
             \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs`
  from `compP1 P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>` have "\<not> is_val e" by auto
  with `bisim Vs E2 (e \<guillemotleft>bop\<guillemotright> e2) (lcl s)` obtain E E2'
    where E2: "E2 = E \<guillemotleft>bop\<guillemotright> E2'" "e2 = compE1 Vs E2'" and "bisim Vs E e (lcl s)"
    and sync: "\<not> contains_insync E2'"
    by(auto elim!: bisim_cases)
  moreover from `\<not> IUF (e \<guillemotleft>bop\<guillemotright> e2) ta (e' \<guillemotleft>bop\<guillemotright> e2)` have "\<not> IUF e ta e'" by auto
  moreover note IH[of Vs E X] `fv E2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]`
    `length Vs + max_vars (e \<guillemotleft>bop\<guillemotright> e2) \<le> length (lcl s)` `\<D> E2 \<lfloor>dom X\<rfloor>`
  ultimately obtain TA' e2' x' where "sim_move10 P ta e e' E (hp s) X TA' e2' (hp s') x'"
    "bisim Vs e2' e' (lcl s')" "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by(auto)
  with E2 `fv E2 \<subseteq> set Vs` sync show ?case by(cases "is_val e2'")(auto intro: BinOpRed1)
next
  case (Bin1OpRed2 e s ta e' s' v bop Vs E2 X)
  note IH = `\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>; \<not> IUF e ta e'\<rbrakk>
              \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs`
  from `bisim Vs E2 (Val v \<guillemotleft>bop\<guillemotright> e) (lcl s)` obtain E 
    where E2: "E2 = Val v \<guillemotleft>bop\<guillemotright> E" and "bisim Vs E e (lcl s)" by(auto)
  moreover from `\<not> IUF (Val v \<guillemotleft>bop\<guillemotright> e) ta (Val v \<guillemotleft>bop\<guillemotright> e')` have "\<not> IUF e ta e'" by auto
  moreover note IH[of Vs E X] `fv E2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]`
    `length Vs + max_vars (Val v \<guillemotleft>bop\<guillemotright> e) \<le> length (lcl s)` `\<D> E2 \<lfloor>dom X\<rfloor>` E2
  ultimately show ?case by(auto intro: BinOpRed2)
next
  case (Red1Var s V v Vs E2 X)
  from `bisim Vs E2 (Var V) (lcl s)` `fv E2 \<subseteq> set Vs`
  obtain V' where "E2 = Var V'" "V' = Vs ! V" "V = index Vs V'" by(clarify, simp)
  from `E2 = Var V'` `\<D> E2 \<lfloor>dom X\<rfloor>`
  obtain v' where "X V' = \<lfloor>v'\<rfloor>" by(auto simp add: hyperset_defs)
  with `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]` have "[Vs [\<mapsto>] lcl s] V' = \<lfloor>v'\<rfloor>" by(rule map_le_SomeD)
  with `length Vs + max_vars (Var V) \<le> length (lcl s)`
  have "lcl s ! (index Vs V') = v'" by(auto intro: map_upds_Some_eq_nth_index)
  with `V = index Vs V'` `lcl s ! V = v` have "v = v'" by simp
  with `X V' = \<lfloor>v'\<rfloor>` `E2 = Var V'` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]`
  show ?case by(fastsimp intro: RedVar)
next
  case (LAss1Red e s ta e' s' V Vs E2 X)
  note IH = `\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>; \<not> IUF e ta e'\<rbrakk>
            \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs`
  from `bisim Vs E2 (V:=e) (lcl s)` obtain E V'
    where E2: "E2 = (V':=E)" "V = index Vs V'" and "bisim Vs E e (lcl s)" by auto
  with IH[of Vs E X] `fv E2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]` `\<not> IUF (V:=e) ta (V:=e')`
    `length Vs + max_vars (V:=e) \<le> length (lcl s)` `\<D> E2 \<lfloor>dom X\<rfloor>`
    E2 show ?case by(auto intro: LAssRed)
next
  case (Red1LAss V l v h Vs E2 X)
  from `bisim Vs E2 (V:=Val v) (lcl (h, l))` obtain V' where "E2 = (V' := Val v)" "V = index Vs V'" by(auto)
  moreover with `fv E2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl (h, l)]` `length Vs + max_vars (V:=Val v) \<le> length (lcl (h, l))`
  have "X(V' \<mapsto> v) \<subseteq>\<^sub>m [Vs [\<mapsto>] l[index Vs V' := v]]" by(auto intro: LAss_lem)
  ultimately show ?case by(auto intro: RedLAss simp del: fun_upd_apply)
next
  case (AAcc1Red1 a s ta a' s' i Vs E2 X)
  note IH = `\<And>vs e2 x. \<lbrakk> bisim vs e2 a (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars a \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>; \<not> IUF a ta a'\<rbrakk>
             \<Longrightarrow> ?concl a a' e2 s x ta s' a' vs`
  from `compP1 P \<turnstile>1 \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>` have "\<not> is_val a" by auto
  with `bisim Vs E2 (a\<lfloor>i\<rceil>) (lcl s)` obtain E E2'
    where E2: "E2 = E\<lfloor>E2'\<rceil>" "i = compE1 Vs E2'" and "bisim Vs E a (lcl s)"
    and sync: "\<not> contains_insync E2'" by(fastsimp)
  moreover from `\<not> IUF (a\<lfloor>i\<rceil>) ta (a'\<lfloor>i\<rceil>)` have "\<not> IUF a ta a'" by auto
  moreover note IH[of Vs E X] `fv E2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]`
    `length Vs + max_vars (a\<lfloor>i\<rceil>) \<le> length (lcl s)` `\<D> E2 \<lfloor>dom X\<rfloor>`
  ultimately obtain TA' e2' x' where "sim_move10 P ta a a' E (hp s) X TA' e2' (hp s') x'"
    "bisim Vs e2' a' (lcl s')" "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by(auto)
  with E2 `fv E2 \<subseteq> set Vs` sync show ?case
    by(cases "is_val e2'")(auto intro: AAccRed1)
next
  case (AAcc1Red2 i s ta i' s' a Vs E2 X)
  note IH = `\<And>vs e2 x. \<lbrakk> bisim vs e2 i (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars i \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>; \<not> IUF i ta i'\<rbrakk>
            \<Longrightarrow> ?concl i i' e2 s x ta s' i' vs`
  from `bisim Vs E2 (Val a\<lfloor>i\<rceil>) (lcl s)` obtain E 
    where E2: "E2 = Val a\<lfloor>E\<rceil>" and "bisim Vs E i (lcl s)" by(auto)
  moreover from `\<not> IUF (Val a\<lfloor>i\<rceil>) ta (Val a\<lfloor>i'\<rceil>)` have "\<not> IUF i ta i'" by auto
  moreover note IH[of Vs E X] `fv E2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]` E2
    `length Vs + max_vars (Val a\<lfloor>i\<rceil>) \<le> length (lcl s)` `\<D> E2 \<lfloor>dom X\<rfloor>`
  ultimately show ?case by(auto intro: AAccRed2)
next
  case Red1AAcc thus ?case by(fastsimp intro: RedAAcc simp del: fun_upd_apply)
next
  case (AAss1Red1 a s ta a' s' i e Vs E2 X)
  note IH = `\<And>vs e2 x. \<lbrakk> bisim vs e2 a (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars a \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>; \<not> IUF a ta a' \<rbrakk>
             \<Longrightarrow> ?concl a a' e2 s x ta s' a' vs`
  from `compP1 P \<turnstile>1 \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>` have "\<not> is_val a" by auto
  with `bisim Vs E2 (a\<lfloor>i\<rceil>:=e) (lcl s)` obtain E E2' E2''
    where E2: "E2 = E\<lfloor>E2'\<rceil>:=E2''" "i = compE1 Vs E2'" "e = compE1 Vs E2''" and "bisim Vs E a (lcl s)"
    and sync: "\<not> contains_insync E2'" "\<not> contains_insync E2''" by(fastsimp)
  moreover from `\<not> IUF (a\<lfloor>i\<rceil> := e) ta (a'\<lfloor>i\<rceil> := e)` have "\<not> IUF a ta a'" by auto
  moreover note IH[of Vs E X] `fv E2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]`
    `length Vs + max_vars (a\<lfloor>i\<rceil>:=e) \<le> length (lcl s)` `\<D> E2 \<lfloor>dom X\<rfloor>`
  ultimately obtain TA' e2' x' where IH': "sim_move10 P ta a a' E (hp s) X TA' e2' (hp s') x'"
    "bisim Vs e2' a' (lcl s')" "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by(auto)
  show ?case
  proof(cases "is_val e2'")
    case True
    from E2 `fv E2 \<subseteq> set Vs` sync have "bisim Vs E2' i (lcl s')" "bisim Vs E2'' e (lcl s')" by auto
    with IH' E2 True sync show ?thesis
      by(cases "is_val E2'")(fastsimp intro: AAssRed1)+
  next
    case False with IH' E2 sync show ?thesis by(auto intro: AAssRed1)
  qed
next
  case (AAss1Red2 i s ta i' s' a e Vs E2 X)
  note IH = `\<And>vs e2 x. \<lbrakk> bisim vs e2 i (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars i \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>; \<not> IUF i ta i'\<rbrakk>
            \<Longrightarrow> ?concl i i' e2 s x ta s' i' vs`
  from `compP1 P \<turnstile>1 \<langle>i,s\<rangle> -ta\<rightarrow> \<langle>i',s'\<rangle>` have "\<not> is_val i" by auto
  with `bisim Vs E2 (Val a\<lfloor>i\<rceil>:=e) (lcl s)` obtain E E2'
    where E2: "E2 = Val a\<lfloor>E\<rceil>:=E2'" "e = compE1 Vs E2'" and "bisim Vs E i (lcl s)"
    and sync: "\<not> contains_insync E2'" by(fastsimp)
  moreover from `\<not> IUF (Val a\<lfloor>i\<rceil> := e) ta (Val a\<lfloor>i'\<rceil> := e)` have "\<not> IUF i ta i'" by auto
  moreover note IH[of Vs E X] `fv E2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]`
    `length Vs + max_vars (Val a\<lfloor>i\<rceil>:=e) \<le> length (lcl s)` `\<D> E2 \<lfloor>dom X\<rfloor>`
  ultimately obtain TA' e2' x' where "sim_move10 P ta i i' E (hp s) X TA' e2' (hp s') x'"
    "bisim Vs e2' i' (lcl s')" "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by(auto)
  with E2 `fv E2 \<subseteq> set Vs` sync show ?case
    by(cases "is_val e2'")(auto intro: AAssRed2)
next
  case (AAss1Red3 e s ta e' s' a i Vs E2 X)
  note IH = `\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>; \<not> IUF e ta e'\<rbrakk>
            \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs`
  from `bisim Vs E2 (Val a\<lfloor>Val i\<rceil>:=e) (lcl s)` obtain E
    where E2: "E2 = Val a\<lfloor>Val i\<rceil>:=E" and "bisim Vs E e (lcl s)" by(fastsimp)
  moreover from `\<not> IUF (Val a\<lfloor>Val i\<rceil> := e) ta (Val a\<lfloor>Val i\<rceil> := e')` have "\<not> IUF e ta e'" by auto
  moreover note IH[of Vs E X] `fv E2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]` E2
    `length Vs + max_vars (Val a\<lfloor>Val i\<rceil>:=e) \<le> length (lcl s)` `\<D> E2 \<lfloor>dom X\<rfloor>`
  ultimately show ?case by(auto intro: AAssRed3)
next
  case Red1AAssStore thus ?case by(auto)((rule exI conjI)+, auto)
next
  case Red1AAss thus ?case by(fastsimp simp del: fun_upd_apply)
next 
  case (FAss1Red1 e s ta e' s' F D e2 Vs E2 X)
  note IH = `\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>; \<not> IUF e ta e' \<rbrakk>
             \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs`
  from `compP1 P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>` have "\<not> is_val e" by auto
  with `bisim Vs E2 (e\<bullet>F{D}:=e2) (lcl s)` obtain E E2'
    where E2: "E2 = E\<bullet>F{D}:=E2'" "e2 = compE1 Vs E2'" and "bisim Vs E e (lcl s)" 
    and sync: "\<not> contains_insync E2'" by(fastsimp)
  with IH[of Vs E X] `fv E2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]` `\<not> IUF (e\<bullet>F{D} := e2) ta (e'\<bullet>F{D} := e2)`
    `length Vs + max_vars (e\<bullet>F{D}:=e2) \<le> length (lcl s)` `\<D> E2 \<lfloor>dom X\<rfloor>`
  obtain TA' e2' x' where "sim_move10 P ta e e' E (hp s) X TA' e2' (hp s') x'"
    "bisim Vs e2' e' (lcl s')" "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by(fastsimp)
  with E2 `fv E2 \<subseteq> set Vs` sync show ?case by(cases "is_val e2'")(auto intro: FAssRed1)
next 
  case (FAss1Red2 e s ta e' s' v F D Vs E2 X)
  note IH = `\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>; \<not> IUF e ta e' \<rbrakk>
            \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs`
  from `bisim Vs E2 (Val v\<bullet>F{D}:=e) (lcl s)` obtain E
    where E2: "E2 = (Val v\<bullet>F{D}:=E)" and "bisim Vs E e (lcl s)" by(fastsimp)
  with IH[of Vs E X] `fv E2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]` `\<not> IUF (Val v\<bullet>F{D} := e) ta (Val v\<bullet>F{D} := e')`
    `length Vs + max_vars (Val v\<bullet>F{D}:=e) \<le> length (lcl s)` `\<D> E2 \<lfloor>dom X\<rfloor>`
    E2 show ?case by(fastsimp intro: FAssRed2)
next
  case (Call1Obj e s ta e' s' M es Vs E2 X)
  note IH = `\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
            x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s);
            \<D> e2 \<lfloor>dom x\<rfloor>; \<not> IUF e ta e' \<rbrakk> \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs` 
  from `compP1 P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>` `bisim Vs E2 (e\<bullet>M(es)) (lcl s)`
  obtain E es' where E2: "E2 = E\<bullet>M(es')" "es = compEs1 Vs es'" and "bisim Vs E e (lcl s)"
    and sync: "\<not> contains_insyncs es'" by(auto elim!: bisim_cases)
  with IH[of Vs E X] `fv E2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]` `\<not> IUF (e\<bullet>M(es)) ta (e'\<bullet>M(es))`
    `length Vs + max_vars (e\<bullet>M(es)) \<le> length (lcl s)` `\<D> E2 \<lfloor>dom X\<rfloor>`
  obtain TA' e2' x' where IH': "sim_move10 P ta e e' E (hp s) X TA' e2' (hp s') x'"
    "bisim Vs e2' e' (lcl s')" "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by(fastsimp)
  with E2 `fv E2 \<subseteq> set Vs` `E2 = E\<bullet>M(es')` sync show ?case
    by(cases "is_val e2'")(auto intro: CallObj)
next
  case (Call1Params es s ta es' s' v M Vs E2 X)
  note IH = `\<And>vs es2 x. \<lbrakk> bisims vs es2 es (lcl s); fvs es2 \<subseteq> set vs;
            x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_varss es \<le> length (lcl s); \<D>s es2 \<lfloor>dom x\<rfloor>; \<not> IUFs es ta es'\<rbrakk> 
           \<Longrightarrow> ?concls es es' es2 s x ta s' es' vs`
  from `bisim Vs E2 (Val v\<bullet>M(es)) (lcl s)` obtain Es
    where "E2 = Val v \<bullet>M(Es)" "bisims Vs Es es (lcl s)" by(auto)
  with IH[of Vs Es X] `fv E2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]` `\<not> IUF (Val v\<bullet>M(es)) ta (Val v\<bullet>M(es'))`
    `length Vs + max_vars (Val v\<bullet>M(es)) \<le> length (lcl s)` `\<D> E2 \<lfloor>dom X\<rfloor>`
    `E2 = Val v \<bullet>M(Es)` show ?case by(fastsimp intro: CallParams)
next
  case (Red1CallExternal s a T M vs ta va h' e' s' Vs E2 X)
  from `bisim Vs E2 (addr a\<bullet>M(map Val vs)) (lcl s)` have E2: "E2 = addr a\<bullet>M(map Val vs)" by auto
  moreover from `is_external_call (compP1 P) T M`
  have "is_external_call P T M" by simp
  moreover from `compP1 P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>`
  have "P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>" by simp
  moreover from `typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>T\<rfloor>` have "hp s a \<noteq> None" by auto
  with wf `P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>` have "ta_bisim01 (extTA2J0 P ta) (extTA2J1 (compP1 P) ta)"
    by(rule red_external_ta_bisim01)
  moreover note `typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>T\<rfloor>` `e' = extRet2J1 va` `s' = (h', lcl s)`
  ultimately show ?case using `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]` 
    apply(auto simp add: sim_move10_def)
    apply(rule exI conjI)+
    apply clarify
    apply(rule conjI, clarsimp simp add: map_eq_append_conv)
    apply(fastsimp intro: RedCallExternal simp add: map_eq_append_conv synthesized_call_def)
    done
next
  case (Block1Red e h x ta e' h' x' V T Vs E2 X)
  note IH = `\<And>vs e2 xa. \<lbrakk> bisim vs e2 e (lcl (h, x)); fv e2 \<subseteq> set vs; xa \<subseteq>\<^sub>m [vs [\<mapsto>] lcl (h, x)];
                       length vs + max_vars e \<le> length (lcl (h, x)); \<D> e2 \<lfloor>dom xa\<rfloor>; \<not> IUF e ta e'\<rbrakk>
             \<Longrightarrow> ?concl e e' e2 (h, x) xa ta (h', x') e' vs` 
  from `compP1 P \<turnstile>1 \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>`
  have "length x = length x'" by(auto dest: red1_preserves_len)
  with `length Vs + max_vars {V:T=None; e} \<le> length (lcl (h, x))`
  have "length Vs < length x'" by simp
  from `bisim Vs E2 {V:T=None; e} (lcl (h, x))`
  show ?case
  proof(cases rule: bisim_cases(12)[consumes 1, case_names BlockNone BlockSome BlockSomeNone])
    case (BlockNone V' E)
    with `fv E2 \<subseteq> set Vs` have "fv E \<subseteq> set (Vs@[V'])" by auto
    with IH[of "Vs@[V']" E "X(V' := None)"] BlockNone `fv E2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl (h, x)]`
      `length Vs + max_vars {V:T=None; e} \<le> length (lcl (h, x))` `\<D> E2 \<lfloor>dom X\<rfloor>` `\<not> IUF {V:T=None; e} ta {V:T=None; e'}`
    obtain TA' e2' X' where IH': "sim_move10 P ta e e' E h (X(V' := None)) TA' e2' h' X'"
      "bisim (Vs @ [V']) e2' e' x'" "X' \<subseteq>\<^sub>m [Vs @ [V'] [\<mapsto>] x']"
      by(fastsimp simp del: fun_upd_apply)
    { assume "V' \<in> set Vs"
      hence "hidden (Vs @ [V']) (index Vs V')" by(rule hidden_index)
      with `bisim (Vs @ [V']) E e (lcl (h, x))` have "unmod e (index Vs V')"
	by(auto intro: hidden_bisim_unmod)
      moreover from `length Vs + max_vars {V:T=None; e} \<le> length (lcl (h, x))` `V' \<in> set Vs`
      have "index Vs V' < length x" by(auto intro: index_less_aux)
      ultimately have "x ! index Vs V' = x' ! index Vs V'"
	using red1_preserves_unmod[OF `compP1 P \<turnstile>1 \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>`]
	by(simp) }
    with `length Vs + max_vars {V:T=None; e} \<le> length (lcl (h, x))` 
      `X' \<subseteq>\<^sub>m [Vs @ [V'] [\<mapsto>] x']` `length x = length x'` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl (h, x)]`
    have rel: "X'(V' := X V') \<subseteq>\<^sub>m [Vs [\<mapsto>] x']" by(auto intro: Block_lem)

    show ?thesis
    proof(cases "X' V'")
      case None
      with BlockNone IH' rel show ?thesis by(fastsimp intro: BlockRed)
    next
      case (Some v)
      with `X' \<subseteq>\<^sub>m [Vs @ [V'] [\<mapsto>] x']` `length Vs < length x'`
      have "x' ! length Vs = v" by(auto dest: map_le_SomeD)
      with BlockNone IH' rel Some show ?thesis by(fastsimp intro: BlockRed)
    qed
  next
    case BlockSome thus ?thesis by simp
  next
    case (BlockSomeNone V' E)
    with `fv E2 \<subseteq> set Vs` have "fv E \<subseteq> set (Vs@[V'])" by auto
    with IH[of "Vs@[V']" E "X(V' \<mapsto> x ! length Vs)"] BlockSomeNone `fv E2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl (h, x)]`
      `length Vs + max_vars {V:T=None; e} \<le> length (lcl (h, x))` `\<D> E2 \<lfloor>dom X\<rfloor>` `\<not> IUF {V:T=None; e} ta {V:T=None; e'}`
    obtain TA' e2' X' where IH': "sim_move10 P ta e e' E h (X(V' \<mapsto> x ! length Vs)) TA' e2' h' X'"
      "bisim (Vs @ [V']) e2' e' x'" "X' \<subseteq>\<^sub>m [Vs @ [V'] [\<mapsto>] x']"
      by(fastsimp simp del: fun_upd_apply)
    { assume "V' \<in> set Vs"
      hence "hidden (Vs @ [V']) (index Vs V')" by(rule hidden_index)
      with `bisim (Vs @ [V']) E e (lcl (h, x))` have "unmod e (index Vs V')"
	by(auto intro: hidden_bisim_unmod)
      moreover from `length Vs + max_vars {V:T=None; e} \<le> length (lcl (h, x))` `V' \<in> set Vs`
      have "index Vs V' < length x" by(auto intro: index_less_aux)
      ultimately have "x ! index Vs V' = x' ! index Vs V'"
	using red1_preserves_unmod[OF `compP1 P \<turnstile>1 \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>`]
	by(simp) }
    with `length Vs + max_vars {V:T=None; e} \<le> length (lcl (h, x))` 
      `X' \<subseteq>\<^sub>m [Vs @ [V'] [\<mapsto>] x']` `length x = length x'` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl (h, x)]`
    have rel: "X'(V' := X V') \<subseteq>\<^sub>m [Vs [\<mapsto>] x']" by(auto intro: Block_lem)
    from `sim_move10 P ta e e' E h (X(V' \<mapsto> x ! length Vs)) TA' e2' h' X'`
    obtain v' where "X' V' = \<lfloor>v'\<rfloor>"
      by(auto simp: sim_move10_def split: split_if_asm dest!: \<tau>red0t_lcl_incr \<tau>red0r_lcl_incr red_lcl_incr subsetD)
    with `X' \<subseteq>\<^sub>m [Vs @ [V'] [\<mapsto>] x']` `length Vs < length x'`
    have "x' ! length Vs = v'" by(auto dest: map_le_SomeD)
    with BlockSomeNone IH' rel `X' V' = \<lfloor>v'\<rfloor>`
    show ?thesis by(fastsimp intro: BlockRed)
  qed
next
  case(Block1Some V xs T v e h)
  from `bisim vs e2 {V:T=\<lfloor>v\<rfloor>; e} (lcl (h, xs))` obtain e' V' where "e2 = {V':T=\<lfloor>v\<rfloor>; e'}"
    and "V = length vs" "bisim (vs @ [V']) e' e (xs[length vs := v])" by(fastsimp)
  moreover have "sim_move10 P \<epsilon> {length vs:T=\<lfloor>v\<rfloor>; e} {length vs:T=None; e} {V':T=\<lfloor>v\<rfloor>; e'} h x \<epsilon> {V':T=\<lfloor>v\<rfloor>; e'} h x"
    by(auto)
  moreover from `bisim (vs @ [V']) e' e (xs[length vs := v])`
    `length vs + max_vars {V:T=\<lfloor>v\<rfloor>; e} \<le> length (lcl (h, xs))`
  have "bisim vs {V':T=\<lfloor>v\<rfloor>; e'} {length vs:T=None; e} (xs[length vs := v])" by auto
  moreover from `x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl (h, xs)]` `length vs + max_vars {V:T=\<lfloor>v\<rfloor>; e} \<le> length (lcl (h, xs))`
  have "x \<subseteq>\<^sub>m [vs [\<mapsto>] xs[length vs := v]]" by auto
  ultimately show ?case by auto
next
  case (Lock1Synchronized h a arrobj V xs e Vs E2 X)
  note len = `length Vs + max_vars (sync\<^bsub>V\<^esub> (addr a) e) \<le> length (lcl (h, xs))`
  from `bisim Vs E2 (sync\<^bsub>V\<^esub> (addr a) e) (lcl (h, xs))` obtain E
    where E2: "E2 = sync(addr a) E" "e = compE1 (Vs@[fresh_var Vs]) E" 
    and sync: "\<not> contains_insync E" and [simp]: "V = length Vs" by auto
  moreover from `h a = \<lfloor>arrobj\<rfloor>`
  have "extTA2J0 P,P \<turnstile> \<langle>sync(addr a) E, (h, X)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Lock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace>\<rightarrow> \<langle>insync(a) E, (h, X)\<rangle>"
    by-(rule LockSynchronized, auto)
  moreover from `fv E2 \<subseteq> set Vs` fresh_var_fresh[of Vs] sync len
  have "bisim Vs (insync(a) E) (insync\<^bsub>length Vs\<^esub> (a) e) (xs[length Vs := Addr a])"
    unfolding `e = compE1 (Vs@[fresh_var Vs]) E` `E2 = sync(addr a) E`
    by -(rule bisimInSynchronized,rule compE1_bisim, auto)
  moreover have "zip Vs (xs[length Vs := Addr a]) = (zip Vs xs)[length Vs := (arbitrary, Addr a)]"
    by(rule sym)(simp add: update_zip)
  hence "zip Vs (xs[length Vs := Addr a]) = zip Vs xs" by simp
  with `X \<subseteq>\<^sub>m [Vs [\<mapsto>] (lcl (h, xs))]` have "X \<subseteq>\<^sub>m [Vs [\<mapsto>] xs[length Vs := Addr a]]"
    by(auto simp add: map_le_def map_upds_def)
  ultimately show ?case using `h a = \<lfloor>arrobj\<rfloor>` by(fastsimp intro: sim_move10_SyncLocks)
next
  case (Synchronized1Red2 e s ta e' s' V a Vs E2 X)
  note IH = `\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
            x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s);
            \<D> e2 \<lfloor>dom x\<rfloor>; \<not> IUF e ta e' \<rbrakk> \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs` 
  from `bisim Vs E2 (insync\<^bsub>V\<^esub> (a) e) (lcl s)` obtain E
    where E2: "E2 = insync(a) E" and bisim: "bisim (Vs@[fresh_var Vs]) E e (lcl s)"
    and xsa: "lcl s ! length Vs = Addr a" and [simp]: "V = length Vs" by auto
  with `fv E2 \<subseteq> set Vs` fresh_var_fresh[of Vs] have fv: "(fresh_var Vs) \<notin> fv E" by auto
  from `length Vs + max_vars (insync\<^bsub>V\<^esub> (a) e) \<le> length (lcl s)` have "length Vs < length (lcl s)" by simp
  { assume "X (fresh_var Vs) \<noteq> None"
    then obtain v where "X (fresh_var Vs) = \<lfloor>v\<rfloor>" by auto
    with `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]` have "[Vs [\<mapsto>] lcl s] (fresh_var Vs) = \<lfloor>v\<rfloor>" 
      by(auto simp add: map_le_def dest: bspec)
    hence "(fresh_var Vs) \<in> set Vs" 
      by(auto simp add: map_upds_def set_zip dest!: map_of_SomeD )
    moreover have "(fresh_var Vs) \<notin> set Vs" by(rule fresh_var_fresh)
    ultimately have False by contradiction }
  hence "X (fresh_var Vs) = None" by(cases "X (fresh_var Vs)", auto)
  hence "X(fresh_var Vs := None) = X" by(auto intro: ext)
  moreover from `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]`
  have "X(fresh_var Vs := None) \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s, (fresh_var Vs) \<mapsto> (lcl s) ! length Vs]" by(simp)
  ultimately have "X \<subseteq>\<^sub>m [Vs @ [fresh_var Vs] [\<mapsto>] lcl s]"
    using `length Vs < length (lcl s)` by(auto)
  moreover from `\<not> IUF (insync\<^bsub>V\<^esub> (a) e) ta (insync\<^bsub>V\<^esub> (a) e')` have "\<not> IUF e ta e'" by(auto)
  moreover note IH[of "Vs@[fresh_var Vs]" E X] bisim E2 `fv E2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]` 
    `length Vs + max_vars (insync\<^bsub>V\<^esub> (a) e) \<le> length (lcl s)` `\<D> E2 \<lfloor>dom X\<rfloor>`
  ultimately obtain TA' e2' x' where IH': "sim_move10 P ta e e' E (hp s) X TA' e2' (hp s') x'"
    "bisim (Vs @ [fresh_var Vs]) e2' e' (lcl s')" "x' \<subseteq>\<^sub>m [Vs @ [fresh_var Vs] [\<mapsto>] lcl s']" by auto
  hence "dom x' \<subseteq> dom X \<union> fv E"
    apply(auto simp add: sim_move10_def dest: \<tau>red0r_dom_lcl[OF wf_prog_wwf_prog[OF wf]] \<tau>red0t_dom_lcl[OF wf_prog_wwf_prog[OF wf]] split: split_if_asm)
    apply(frule red_dom_lcl)
    apply(frule \<tau>red0r_dom_lcl[OF wf_prog_wwf_prog[OF wf]])
    apply(frule \<tau>red0r_fv_subset[OF wf_prog_wwf_prog[OF wf]])
    apply(simp, blast)
    done
  with fv `X (fresh_var Vs) = None` have "(fresh_var Vs) \<notin> dom x'" by auto
  hence "x' (fresh_var Vs) = None" by auto
  moreover from `compP1 P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  have "length (lcl s) = length (lcl s')" by(auto dest: red1_preserves_len)
  moreover note `x' \<subseteq>\<^sub>m [Vs @ [fresh_var Vs] [\<mapsto>] lcl s']` `length Vs < length (lcl s)`
  ultimately have "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by(auto simp add: map_le_def dest: bspec)
  moreover from bisim fv have "unmod e (length Vs)" by(auto intro: bisim_fv_unmod)
  with `compP1 P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>` `length Vs < length (lcl s)` have "lcl s ! length Vs = lcl s' ! length Vs"
    by(auto dest!: red1_preserves_unmod)
  with xsa have "lcl s' ! length Vs = Addr a" by simp
  ultimately show ?case using IH' E2 by(auto intro: SynchronizedRed2)
next
  case (Unlock1Synchronized xs V a' a v h Vs E2 X)
  from `bisim Vs E2 (insync\<^bsub>V\<^esub> (a) Val v) (lcl (h, xs))`
  have E2: "E2 = insync(a) Val v" "V = length Vs" "xs ! length Vs = Addr a" by auto
  moreover with `xs ! V = Addr a'` have [simp]: "a' = a" by simp
  have "extTA2J0 P,P \<turnstile> \<langle>insync(a) (Val v), (h, X)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace>\<rightarrow> \<langle>Val v, (h, X)\<rangle>"
    by(rule UnlockSynchronized)
  ultimately show ?case using `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl (h, xs)]` by(fastsimp intro: sim_move10_SyncLocks)
next
  case (Unlock1SynchronizedNull xs V a v h Vs E2 X)
  from `bisim Vs E2 (insync\<^bsub>V\<^esub> (a) Val v) (lcl (h, xs))`
  have "V = length Vs" "xs ! length Vs = Addr a" by(auto)
  with `xs ! V = Null` have False by simp
  thus ?case ..
next
  case (Unlock1SynchronizedFail xs V A' a' v h Vs E2 X)
  from `bisim Vs E2 (insync\<^bsub>V\<^esub> (a') Val v) (lcl (h, xs))` `xs ! V = Addr A'` have "A' = a'" by auto
  with `\<not> IUF (insync\<^bsub>V\<^esub> (a') Val v) \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>A'\<rbrace> (THROW IllegalMonitorState)`
  have False by(auto simp del: ta_update_locks.simps)
  thus ?case ..
next
  case (Red1While b c s Vs E2 X)
  from `bisim Vs E2 (while (b) c) (lcl s)` obtain B C
    where E2: "E2 = while (B) C" "b = compE1 Vs B" "c = compE1 Vs C" 
    and sync: "\<not> contains_insync B" "\<not> contains_insync C" by auto
  moreover have "extTA2J0 P,P \<turnstile> \<langle>while (B) C, (hp s, X)\<rangle> -\<epsilon>\<rightarrow> \<langle>if (B) (C;;while (B) C) else unit, (hp s, X)\<rangle>"
    by(rule RedWhile)
  hence "sim_move10 P \<epsilon> (while (compE1 Vs B) (compE1 Vs C)) (if (compE1 Vs B) (compE1 Vs C;;while (compE1 Vs B) (compE1 Vs C)) else unit) (while (B) C) (hp s) X \<epsilon> (if (B) (C;;while (B) C) else unit) (hp s) X"
    by(auto simp add: sim_move10_def)
  moreover from `fv E2 \<subseteq> set Vs` E2 sync
  have "bisim Vs (if (B) (C;; while (B) C) else unit)
                 (if (compE1 Vs B) (compE1 Vs (C;; while(B) C)) else (compE1 Vs unit)) (lcl s)"
    by -(rule bisimCond, auto)
  ultimately show ?case using `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]`
    by(simp)(rule exI, rule exI, rule exI, erule conjI, auto)
next
  case (Red1TryCatch h a D fs C V x e2 Vs E2 X)
  from `bisim Vs E2 (try Throw a catch(C V) e2) (lcl (h, x))`
  obtain E2' V' where "E2 = try Throw a catch(C V') E2'" "V = length Vs" "e2 = compE1 (Vs @ [V']) E2'"
    and sync: "\<not> contains_insync E2'" by(auto)
  with `fv E2 \<subseteq> set Vs` have "fv E2' \<subseteq> set (Vs @[V'])" by auto
  with `e2 = compE1 (Vs @ [V']) E2'`  sync have "bisim (Vs @[V']) E2' e2 (x[V := Addr a])"
    by(auto intro!: compE1_bisim)
  with `V = length Vs` `length Vs + max_vars (try Throw a catch(C V) e2) \<le> length (lcl (h, x))`
  have "bisim Vs {V':Class C=\<lfloor>Addr a\<rfloor>; E2'} {length Vs:Class C=None; e2} (x[V := Addr a])"
    by(auto intro: bisimBlockSomeNone)
  moreover from `length Vs + max_vars (try Throw a catch(C V) e2) \<le> length (lcl (h, x))`
  have "[Vs [\<mapsto>] x[length Vs := Addr a]] = [Vs [\<mapsto>] x]" by simp
  with `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl (h, x)]` have "X \<subseteq>\<^sub>m [Vs [\<mapsto>] x[length Vs := Addr a]]" by simp
  moreover note `e2 = compE1 (Vs @ [V']) E2'` `E2 = try Throw a catch(C V') E2'`
    `h a = \<lfloor>Obj D fs\<rfloor>` `compP1 P \<turnstile> D \<preceq>\<^sup>* C` `V = length Vs`
  ultimately show ?case by(auto intro!: exI)
next
  case Red1TryFail thus ?case by(auto intro!: exI sim_move10_TryFail)
next
  case (List1Red1 e s ta e' s' es Vs ES2 X)
  note IH = `\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
            x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>; \<not> IUF e ta e'\<rbrakk>
           \<Longrightarrow> \<exists>TA' e2' x'. sim_move10 P ta e e' e2 (hp s) x TA' e2' (hp s') x' \<and> 
                 bisim vs e2' e' (lcl s') \<and> x' \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s']`
  from `bisims Vs ES2 (e # es) (lcl s)` `compP1 P \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  obtain E ES where "ES2 = E # ES" "\<not> is_val E" "es = compEs1 Vs ES" "bisim Vs E e (lcl s)"
    and sync: "\<not> contains_insyncs ES" by(auto elim!: bisims_cases)
  with IH[of Vs E X] `fvs ES2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]` `\<not> IUFs (e # es) ta (e' # es)`
    `length Vs + max_varss (e # es) \<le> length (lcl s)` `\<D>s ES2 \<lfloor>dom X\<rfloor>`
  obtain TA' e2' x' where IH': "sim_move10 P ta e e' E (hp s) X TA' e2' (hp s') x'"
    "bisim Vs e2' e' (lcl s')" "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by fastsimp
  show ?case
  proof(cases "is_val e2'")
    case False
    with IH' `ES2 = E # ES` `es = compEs1 Vs ES` sync show ?thesis by(auto intro: sim_moves10_expr)
  next
    case True
    from `fvs ES2 \<subseteq> set Vs` `ES2 = E # ES` `es = compEs1 Vs ES` sync
    have "bisims Vs ES es (lcl s')" by(auto intro: compEs1_bisims)
    with IH' True `ES2 = E # ES` `es = compEs1 Vs ES` show ?thesis by(auto intro: sim_moves10_expr)
  qed
next
  case (List1Red2 es s ta es' s' v Vs ES2 X)
  note IH = `\<And>vs es2 x. \<lbrakk>bisims vs es2 es (lcl s); fvs es2 \<subseteq> set vs;
            x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_varss es \<le> length (lcl s); \<D>s es2 \<lfloor>dom x\<rfloor>; \<not> IUFs es ta es'\<rbrakk>
           \<Longrightarrow> \<exists>TA' es2' x'. sim_moves10 P ta es es' es2 (hp s) x TA' es2' (hp s') x' \<and> bisims vs es2' es' (lcl s') \<and> x' \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s']`
  from `bisims Vs ES2 (Val v # es) (lcl s)` obtain ES where "ES2 = Val v # ES" "bisims Vs ES es (lcl s)"
    by(auto elim!: bisims_cases)
  with IH[of Vs ES X] `fvs ES2 \<subseteq> set Vs` `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]` `\<not> IUFs (Val v # es) ta (Val v # es')`
    `length Vs + max_varss (Val v # es) \<le> length (lcl s)` `\<D>s ES2 \<lfloor>dom X\<rfloor>`
    `ES2 = Val v # ES` show ?case by(fastsimp intro: sim_moves10_expr)
next
  case Call1ThrowParams
  thus ?case by(fastsimp intro: CallThrowParams elim!: bisim_cases simp add: bisims_map_Val_Throw2)
next
  case (Synchronized1Throw2 xs V a' a ad h Vs E2 X)
  from `bisim Vs E2 (insync\<^bsub>V\<^esub> (a) Throw ad) (lcl (h, xs))`
  have "xs ! length Vs = Addr a" and "V = length Vs" by auto
  with `xs ! V = Addr a'` have [simp]: "a' = a" by simp
  have "extTA2J0 P,P \<turnstile> \<langle>insync(a) Throw ad, (h, X)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace>\<rightarrow> \<langle>Throw ad, (h, X)\<rangle>"
    by(rule SynchronizedThrow2)
  with `X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl (h, xs)]` `bisim Vs E2 (insync\<^bsub>V\<^esub> (a) Throw ad) (lcl (h, xs))`
  show ?case by(auto intro: sim_move10_SyncLocks intro!: exI)
next
  case (Synchronized1Throw2Null xs V a a' h Vs E2 X)
  from `bisim Vs E2 (insync\<^bsub>V\<^esub> (a) Throw a') (lcl (h, xs))`
  have "V = length Vs" "xs ! length Vs = Addr a" by(auto)
  with `xs ! V = Null` have False by simp
  thus ?case ..
next
  case (Synchronized1Throw2Fail xs V A' a' a h Vs E2 X)
  from `bisim Vs E2 (insync\<^bsub>V\<^esub> (a') Throw a) (lcl (h, xs))` `xs ! V = Addr A'` have "A' = a'" by auto
  with `\<not> IUF (insync\<^bsub>V\<^esub> (a') Throw a) \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>A'\<rbrace> (THROW IllegalMonitorState)`
  have False by(auto simp del: ta_update_locks.simps)
  thus ?case ..
qed(simp_all del: fun_upd_apply, (fastsimp intro: red_reds.intros simp del: fun_upd_apply simp add: finfun_upd_apply)+)


lemma bisim_max_vars: "bisim Vs e e' xs \<Longrightarrow> max_vars e = max_vars e'"
  and bisims_max_varss: "bisims Vs es es' xs \<Longrightarrow> max_varss es = max_varss es'"
apply(induct rule: bisim_bisims.inducts)
apply(auto simp add: max_vars_compE1 max_varss_compEs1)
done

lemma bisim_call: "bisim Vs e e' xs \<Longrightarrow> call e = call e'"
  and bisims_calls: "bisims Vs es es' xs \<Longrightarrow> calls es = calls es'"
apply(induct rule: bisim_bisims.inducts)
apply(auto simp add: is_vals_conv)
done

lemma bisim_call_None_call1: "\<lbrakk> bisim Vs e e' xs; call e = None \<rbrakk> \<Longrightarrow> call1 e' = None"
  and bisims_calls_None_calls1: "\<lbrakk> bisims Vs es es' xs; calls es = None \<rbrakk> \<Longrightarrow> calls1 es' = None"
by(induct rule: bisim_bisims.inducts)(auto simp add: is_vals_conv split: split_if_asm)

lemma bisim_call_Some_call1:
  "\<lbrakk> bisim Vs e e' xs; call e = \<lfloor>aMvs\<rfloor>; length Vs + max_vars e' \<le> length xs \<rbrakk>
  \<Longrightarrow> \<exists>e'' xs'. \<tau>red1'r P h (e', xs) (e'', xs') \<and> call1 e'' = \<lfloor>aMvs\<rfloor> \<and> 
               bisim Vs e e'' xs' \<and> take (length Vs) xs = take (length Vs) xs'"

  and bisims_calls_Some_calls1:
  "\<lbrakk> bisims Vs es es' xs; calls es = \<lfloor>aMvs\<rfloor>; length Vs + max_varss es' \<le> length xs \<rbrakk> 
  \<Longrightarrow> \<exists>es'' xs'. \<tau>reds1'r P h (es', xs) (es'', xs') \<and> calls1 es'' = \<lfloor>aMvs\<rfloor> \<and> 
                bisims Vs es es'' xs' \<and> take (length Vs) xs = take (length Vs) xs'"
proof(induct rule: bisim_bisims.inducts)
  case bisimCallParams thus ?case
    by(fastsimp simp add: is_vals_conv split: split_if_asm)
next
  case bisimBlockNone thus ?case by(fastsimp intro: take_eq_take_le_eq)
next
  case (bisimBlockSome Vs V e e' xs v T)
  from `length Vs + max_vars {length Vs:T=\<lfloor>v\<rfloor>; e'} \<le> length xs`
  have "\<tau>red1'r P h ({length Vs:T=\<lfloor>v\<rfloor>; e'}, xs) ({length Vs:T=None; e'}, xs[length Vs := v])"
    by(auto intro!: \<tau>red1'r_1step Block1Some)
  also from bisimBlockSome obtain e'' xs'
    where "\<tau>red1'r P h (e', xs[length Vs := v]) (e'', xs')"
    and "call1 e'' = \<lfloor>aMvs\<rfloor>" "bisim (Vs @ [V]) e e'' xs'" 
    and "take (length (Vs @ [V])) (xs[length Vs := v]) = take (length (Vs @ [V])) xs'" by auto
  hence "\<tau>red1'r P h ({length Vs:T=None; e'}, xs[length Vs := v]) ({length Vs:T=None; e''}, xs')" by auto
  also from `call1 e'' = \<lfloor>aMvs\<rfloor>` have "call1 {length Vs:T=None; e''} = \<lfloor>aMvs\<rfloor>" by simp
  moreover from `take (length (Vs @ [V])) (xs[length Vs := v]) = take (length (Vs @ [V])) xs'`
  have "take (length Vs) xs = take (length Vs) xs'"
    by(auto dest: take_eq_take_le_eq[where m="length Vs"] simp add: take_list_update_beyond)
  moreover {
    have "xs' ! length Vs = take (length (Vs @ [V])) xs' ! length Vs" by simp
    also note `take (length (Vs @ [V])) (xs[length Vs := v]) = take (length (Vs @ [V])) xs'`[symmetric]
    also have "take (length (Vs @ [V])) (xs[length Vs := v]) ! length Vs = v"
      using `length Vs + max_vars {length Vs:T=\<lfloor>v\<rfloor>; e'} \<le> length xs` by simp
    finally have "bisim Vs {V:T=\<lfloor>v\<rfloor>; e} {length Vs:T=None; e''} xs'"
      using `bisim (Vs @ [V]) e e'' xs'` by auto }
  ultimately show ?case by blast
next
  case (bisimBlockSomeNone Vs V e e' xs v T)
  then obtain e'' xs' where "\<tau>red1'r P h (e', xs) (e'', xs')" "call1 e'' = \<lfloor>aMvs\<rfloor>" "bisim (Vs @ [V]) e e'' xs'"
    and "take (length (Vs @ [V])) xs = take (length (Vs @ [V])) xs'" by auto
  hence "\<tau>red1'r P h ({length Vs:T=None; e'}, xs) ({length Vs:T=None; e''}, xs')" by auto
  moreover from `call1 e'' = \<lfloor>aMvs\<rfloor>` have "call1 ({length Vs:T=None; e''}) = \<lfloor>aMvs\<rfloor>" by simp
  moreover from `take (length (Vs @ [V])) xs = take (length (Vs @ [V])) xs'`
  have "take (length Vs) xs = take (length Vs) xs'" by(auto intro: take_eq_take_le_eq)
  moreover {
    have "xs' ! length Vs = take (length (Vs @ [V])) xs' ! length Vs" by simp
    also note `take (length (Vs @ [V])) xs = take (length (Vs @ [V])) xs'`[symmetric]
    also have "take (length (Vs @ [V])) xs ! length Vs = v" using `xs ! length Vs = v` by simp
    finally have "bisim Vs {V:T=\<lfloor>v\<rfloor>; e} {length Vs:T=None; e''} xs'"
      using `bisim (Vs @ [V]) e e'' xs'` by auto }
  ultimately show ?case by blast
next
  case (bisimInSynchronized Vs e e' xs a)
  then obtain e'' xs' where "\<tau>red1'r P h (e', xs) (e'', xs')" "call1 e'' = \<lfloor>aMvs\<rfloor>" "bisim (Vs @ [fresh_var Vs]) e e'' xs'"
    and "take (Suc (length Vs)) xs = take (Suc (length Vs)) xs'" by auto
  hence "\<tau>red1'r P h (insync\<^bsub>length Vs\<^esub> (a) e', xs) (insync\<^bsub>length Vs\<^esub> (a) e'', xs')" by auto
  moreover from `call1 e'' = \<lfloor>aMvs\<rfloor>` have "call1 (insync\<^bsub>length Vs\<^esub> (a) e'') = \<lfloor>aMvs\<rfloor>" by simp
  moreover from `take (Suc (length Vs)) xs = take (Suc (length Vs)) xs'`
  have "take (length Vs) xs = take (length Vs) xs'" by(auto intro: take_eq_take_le_eq)
  moreover {
    have "xs' ! length Vs = take (Suc (length Vs)) xs' ! length Vs" by simp
    also note `take (Suc (length Vs)) xs = take (Suc (length Vs)) xs'`[symmetric]
    also have "take (Suc (length Vs)) xs ! length Vs = Addr a"
      using `xs ! length Vs = Addr a` by simp
    finally have "bisim Vs (insync(a) e) (insync\<^bsub>length Vs\<^esub> (a) e'') xs'"
      using `bisim (Vs @ [fresh_var Vs]) e e'' xs'` by auto }
  ultimately show ?case by blast
next
  case bisimsCons1 thus ?case by(fastsimp intro!: \<tau>red1'r_inj_\<tau>reds1'r)
next
  case bisimsCons2 thus ?case by(fastsimp intro!: \<tau>reds1'r_cons_\<tau>reds1'r)
qed fastsimp+

lemma bisim_call1_Some_call:
  "\<lbrakk> bisim Vs e e' xs; call1 e' = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> call e = \<lfloor>aMvs\<rfloor>"

  and bisims_calls1_Some_calls:
  "\<lbrakk> bisims Vs es es' xs; calls1 es' = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> calls es = \<lfloor>aMvs\<rfloor>"
by(induct rule: bisim_bisims.inducts)(auto simp add: is_vals_conv split: split_if_asm)

lemma blocks_bisim: 
  assumes bisim: "bisim (Vs @ pns) e e' xs"
  and length: "length vs = length pns" "length Ts = length pns"
  and xs: "\<forall>i. i < length vs \<longrightarrow> xs ! (i + length Vs) = vs ! i"
  shows "bisim Vs (blocks (pns, Ts, vs, e)) (blocks1 (length Vs) Ts e') xs"
using bisim length xs
proof(induct pns Ts vs e arbitrary: e' Vs rule: blocks.induct)
  case (5 V Vs T Ts v vs e e' VS)
  note IH = `\<And>e' Vsa. \<lbrakk>bisim (Vsa @ Vs) e e' xs;
                       length vs = length Vs; length Ts = length Vs; \<forall>i<length vs. xs ! (i + length Vsa) = vs ! i\<rbrakk>
           \<Longrightarrow> bisim Vsa (blocks (Vs, Ts, vs, e)) (blocks1 (length Vsa) Ts e') xs`
  note xs = `\<forall>i<length (v # vs). xs ! (i + length VS) = (v # vs) ! i`
  hence xs': "\<forall>i<length vs. xs ! (i + length (VS @ [V])) = vs ! i" and v: "xs ! length VS = v" by(auto)
  from `bisim (VS @ V # Vs) e e' xs` have "bisim ((VS @ [V]) @ Vs) e e' xs" by simp
  from IH[OF this _ _ xs'] `length (v # vs) = length (V # Vs)` `length (T # Ts) = length (V # Vs)`
  have "bisim (VS @ [V]) (blocks (Vs, Ts, vs, e)) (blocks1 (length (VS @ [V])) Ts e') xs"
    by auto
  hence "bisim VS ({V:T=\<lfloor>v\<rfloor>; blocks (Vs, Ts, vs, e)}) {length VS:T=None; blocks1 (length (VS @ [V])) Ts e'} xs"
    using v by(rule bisimBlockSomeNone)
  thus ?case by simp
qed(auto)

lemma blocks_max_vars:
  "\<lbrakk> length vs = length pns; length Ts = length pns \<rbrakk> \<Longrightarrow> max_vars (blocks (pns, Ts, vs, e)) = max_vars e + length pns"
by(induct pns Ts vs e rule: blocks.induct)(auto)

lemma blocks1_max_vars:
  "max_vars (blocks1 n Ts e) = max_vars e + length Ts"
by(induct n Ts e rule: blocks1.induct)(auto)

lemma fixes e :: "('a,'b) exp" and es :: "('a,'b) exp list"
  shows inline_call_max_vars: "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> max_vars (inline_call e' e) \<le> max_vars e + max_vars e'"
  and inline_calls_max_varss: "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> max_varss (inline_calls e' es) \<le> max_varss es + max_vars e'"
by(induct e and es)(auto)

lemma assumes "final E" "bisim VS E E' xs"
  shows inline_call_compE1: "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> inline_call E' (compE1 Vs e) = compE1 Vs (inline_call E e)"
  and inline_calls_compEs1: "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> inline_calls E' (compEs1 Vs es) = compEs1 Vs (inline_calls E es)"
proof(induct e and es arbitrary: Vs and Vs)
  case (Call obj M params Vs)
  note IHobj = `\<And>Vs. call obj = \<lfloor>aMvs\<rfloor> \<Longrightarrow> inline_call E' (compE1 Vs obj) = compE1 Vs (inline_call E obj)`
  note IHparams = `\<And>Vs. calls params = \<lfloor>aMvs\<rfloor> \<Longrightarrow> inline_calls E' (compEs1 Vs params) = compEs1 Vs (inline_calls E params)`
  obtain a M' vs where [simp]: "aMvs = (a, M', vs)" by (cases aMvs, auto)
  with `call (obj\<bullet>M(params)) = \<lfloor>aMvs\<rfloor>` have "call (obj\<bullet>M(params)) = \<lfloor>(a, M', vs)\<rfloor>" by simp
  thus ?case
  proof(induct rule: call_callE)
    case CallObj
    with IHobj[of Vs] have "inline_call E' (compE1 Vs obj) = compE1 Vs (inline_call E obj)" by auto
    with CallObj show ?case by auto
  next
    case (CallParams v)
    with IHparams[of Vs] have "inline_calls E' (compEs1 Vs params) = compEs1 Vs (inline_calls E params)" by auto
    with CallParams show ?case by(auto simp add: is_vals_conv)
  next
    case Call
    with `final E` `bisim VS E E' xs` show ?case by(auto simp add: is_vals_conv)
  qed
qed(auto split: split_if_asm)

lemma assumes bisim: "bisim VS E E' XS"
  and final: "final E"
  shows bisim_inline_call:
  "\<lbrakk> bisim Vs e e' xs; call e = \<lfloor>aMvs\<rfloor>; fv e \<subseteq> set Vs \<rbrakk>
  \<Longrightarrow> bisim Vs (inline_call E e) (inline_call E' e') xs"
  
  and bisims_inline_calls: 
  "\<lbrakk> bisims Vs es es' xs; calls es = \<lfloor>aMvs\<rfloor>; fvs es \<subseteq> set Vs \<rbrakk>
  \<Longrightarrow> bisims Vs (inline_calls E es) (inline_calls E' es') xs"
proof(induct rule: bisim_bisims.inducts)
  case (bisimBinOp1 Vs e e' xs bop e'')
  thus ?case by(cases "is_val (inline_call E e)")(fastsimp)+
next
  case (bisimAAcc1 Vs a a' xs i)
  thus ?case by(cases "is_val (inline_call E a)")(fastsimp)+
next
  case (bisimAAss1 Vs a a' xs i e)
  thus ?case by(cases "is_val (inline_call E a)", cases "is_val i")(fastsimp)+
next
  case (bisimAAss2 Vs i i' xs a e)
  thus ?case by(cases "is_val (inline_call E i)")(fastsimp)+
next
  case (bisimFAss1 Vs e e' xs F D e'')
  thus ?case by(cases "is_val (inline_call E e)")(fastsimp)+
next
  case (bisimCallObj Vs e e' xs es M)
  obtain a M' vs where "aMvs = (a, M', vs)" by(cases aMvs, auto)
  with `call (e\<bullet>M(es)) = \<lfloor>aMvs\<rfloor>` have "call (e\<bullet>M(es)) = \<lfloor>(a, M', vs)\<rfloor>"  by simp
  thus ?case
  proof(induct rule: call_callE)
    case CallObj
    with `fv (e\<bullet>M(es)) \<subseteq> set Vs` `aMvs = (a, M', vs)`
      `\<lbrakk>call e = \<lfloor>aMvs\<rfloor>; fv e \<subseteq> set Vs\<rbrakk> \<Longrightarrow> bisim Vs (inline_call E e) (inline_call E' e') xs`
    have IH': "bisim Vs (inline_call E e) (inline_call E' e') xs" by(auto)
    with `bisim Vs e e' xs` `fv (e\<bullet>M(es)) \<subseteq> set Vs` CallObj `\<not> contains_insyncs es` show ?thesis
      by(cases "is_val (inline_call E e)")(fastsimp)+
  next
    case (CallParams v)
    hence "inline_calls E' (compEs1 Vs es) = compEs1 Vs (inline_calls E es)"
      by -(rule inline_calls_compEs1[OF final bisim])
    moreover from `fv (e\<bullet>M(es)) \<subseteq> set Vs` final fvs_inline_calls[OF `calls es = \<lfloor>(a, M', vs)\<rfloor>`, of E]
    have "fvs (inline_calls E es) \<subseteq> set Vs" by(auto elim!: final.cases)
    moreover note CallParams `bisim Vs e e' xs` `fv (e\<bullet>M(es)) \<subseteq> set Vs` `\<not> contains_insyncs es` final
    ultimately show ?case by(auto simp add: is_vals_conv final_iff)
  next
    case Call
    with final bisim `bisim Vs e e' xs` show ?case by(auto simp add: is_vals_conv)
  qed
next
  case (bisimCallParams Vs es es' xs v M)
  obtain a M' vs where [simp]: "aMvs = (a, M', vs)" by(cases aMvs, auto)
  with `call (Val v\<bullet>M(es)) = \<lfloor>aMvs\<rfloor>` have "call (Val v\<bullet>M(es)) = \<lfloor>(a, M', vs)\<rfloor>"  by simp
  thus ?case
  proof(induct rule: call_callE)
    case CallObj thus ?case by simp
  next
    case (CallParams v')
    with ` \<lbrakk>calls es = \<lfloor>aMvs\<rfloor>; fvs es \<subseteq> set Vs\<rbrakk> \<Longrightarrow> bisims Vs (inline_calls E es) (inline_calls E' es') xs` `fv (Val v\<bullet>M(es)) \<subseteq> set Vs`
    have "bisims Vs (inline_calls E es) (inline_calls E' es') xs" by(auto)
    with final bisim `bisims Vs es es' xs` show ?case by(auto simp add: is_vals_conv)
  next
    case Call
    with final bisim `bisims Vs es es' xs` show ?case by(auto)
  qed
next
  case (bisimsCons1 Vs e e' xs es)
  thus ?case by(cases "is_val (inline_call E e)")(fastsimp)+
qed(fastsimp)+


declare hyperUn_ac [simp del]

lemma A_inline_call: "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<A> e \<sqsubseteq> \<A> (inline_call e' e)"
  and As_inline_calls: "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow>  \<A>s es \<sqsubseteq> \<A>s (inline_calls e' es)"
proof(induct e and es)
  case (Call obj M params)
  obtain a M' vs where [simp]: "aMvs = (a, M', vs)" by(cases aMvs, auto)
  with `call (obj\<bullet>M(params)) = \<lfloor>aMvs\<rfloor>` have "call (obj\<bullet>M(params)) = \<lfloor>(a, M', vs)\<rfloor>"  by simp
  thus ?case
  proof(induct rule: call_callE)
    case CallObj
    with `call obj = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<A> obj \<sqsubseteq> \<A> (inline_call e' obj)`
    show ?case by(auto intro: sqUn_lem)
  next
    case CallParams
    with `calls params = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<A>s params \<sqsubseteq> \<A>s (inline_calls e' params)`
    show ?case by(auto intro: sqUn_lem)
  next
    case Call
    thus ?case by(auto simp add: hyperset_defs)
  qed
next
  case (Block V ty vo exp)
  thus ?case by(fastsimp intro: diff_lem)
next
  case throw thus ?case by(simp add: hyperset_defs)
next
  case TryCatch thus ?case by(auto intro: sqInt_lem)
qed(fastsimp intro: sqUn_lem sqUn_lem2)+

lemma assumes "\<D> e' \<lfloor>{}\<rfloor>"
  shows defass_inline_call: "\<lbrakk> call e = \<lfloor>aMvs\<rfloor>; \<D> e A \<rbrakk> \<Longrightarrow> \<D> (inline_call e' e) A"
  and defasss_inline_calls: "\<lbrakk> calls es = \<lfloor>aMvs\<rfloor>; \<D>s es A \<rbrakk> \<Longrightarrow> \<D>s (inline_calls e' es) A"
proof(induct e and es arbitrary: A and A)
  case (Call obj M params A)
  obtain a M' vs where [simp]: "aMvs = (a, M', vs)" by(cases aMvs, auto)
  with `call (obj\<bullet>M(params)) = \<lfloor>aMvs\<rfloor>` have "call (obj\<bullet>M(params)) = \<lfloor>(a, M', vs)\<rfloor>"  by simp
  thus ?case
  proof(induct rule: call_callE)
    case CallObj
    with `\<D> (obj\<bullet>M(params)) A` `\<lbrakk>call obj = \<lfloor>aMvs\<rfloor>; \<D> obj A\<rbrakk> \<Longrightarrow> \<D> (inline_call e' obj) A`
    have "\<D> (inline_call e' obj) A" by simp
    moreover from A_inline_call[OF CallObj, of e']
    have "A \<squnion> \<A> obj \<sqsubseteq> A \<squnion> \<A> (inline_call e' obj)" by(rule sqUn_lem2)
    with `\<D> (obj\<bullet>M(params)) A` have "\<D>s params (A \<squnion> \<A> (inline_call e' obj))" by(auto elim: Ds_mono')
    ultimately show ?case using CallObj by auto
  next
    case (CallParams v)
    with `\<D> (obj\<bullet>M(params)) A` `\<lbrakk>calls params = \<lfloor>aMvs\<rfloor>; \<D>s params A\<rbrakk> \<Longrightarrow> \<D>s (inline_calls e' params) A`
    have "\<D>s (inline_calls e' params) A" by(simp)
    with CallParams show ?case by(auto)
  next
    case Call
    with `\<D> e' \<lfloor>{}\<rfloor>` show ?case by(auto elim!: D_mono' simp add: hyperset_defs)
  qed
next
  case (Cons_exp exp exps A)
  show ?case
  proof(cases "is_val exp")
    case True
    with `\<D>s (exp # exps) A` `\<lbrakk>calls exps = \<lfloor>aMvs\<rfloor>; \<D>s exps A\<rbrakk> \<Longrightarrow> \<D>s (inline_calls e' exps) A` 
      `calls (exp # exps) = \<lfloor>aMvs\<rfloor>`
    have "\<D>s (inline_calls e' exps) A" by(auto)
    with True show ?thesis by(auto)
  next
    case False
    with `\<lbrakk>call exp = \<lfloor>aMvs\<rfloor>; \<D> exp A\<rbrakk> \<Longrightarrow> \<D> (inline_call e' exp) A` `calls (exp # exps) = \<lfloor>aMvs\<rfloor>` `\<D>s (exp # exps) A`
    have "\<D> (inline_call e' exp) A" by auto
    moreover from False `calls (exp # exps) = \<lfloor>aMvs\<rfloor>` have "\<A> exp \<sqsubseteq> \<A> (inline_call e' exp)"
      by(auto intro: A_inline_call)
    hence "A \<squnion> \<A> exp \<sqsubseteq> A \<squnion> \<A> (inline_call e' exp)" by(rule sqUn_lem2)
    with `\<D>s (exp # exps) A` have "\<D>s exps (A \<squnion> \<A> (inline_call e' exp))"
      by(auto intro: Ds_mono')
    ultimately show ?thesis using False by(auto)
  qed
qed(fastsimp split: split_if_asm elim: D_mono' intro: sqUn_lem2 sqUn_lem A_inline_call)+

lemma \<B>: "size Vs = n \<Longrightarrow> \<B> (compE1 Vs e) n"
and \<B>s: "size Vs = n \<Longrightarrow> \<B>s (compEs1 Vs es) n"
apply(induct e and es arbitrary: Vs n and Vs n)
apply auto
done

lemma bisim_B: "bisim Vs e E xs \<Longrightarrow> \<B> E (length Vs)"
  and bisims_Bs: "bisims Vs es Es xs \<Longrightarrow> \<B>s Es (length Vs)"
apply(induct rule: bisim_bisims.inducts)
apply(auto intro: \<B> \<B>s)
done

lemma map_upds_xchg_snd:
  "\<lbrakk> length xs \<le> length ys; length xs \<le> length zs; \<forall>i. i < length xs \<longrightarrow> ys ! i = zs ! i \<rbrakk>
  \<Longrightarrow> f(xs [\<mapsto>] ys) = f(xs [\<mapsto>] zs)"
proof(induct xs arbitrary: ys zs f)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  note IH = `\<And>f ys zs. \<lbrakk> length xs \<le> length ys; length xs \<le> length zs; \<forall>i<length xs. ys ! i = zs ! i\<rbrakk>
             \<Longrightarrow> f(xs [\<mapsto>] ys) = f(xs [\<mapsto>] zs)`
  note leny = `length (x # xs) \<le> length ys`
  note lenz = `length (x # xs) \<le> length zs`
  note nth = `\<forall>i<length (x # xs). ys ! i = zs ! i`
  from lenz obtain z zs' where zs [simp]: "zs = z # zs'" by(cases zs, auto)
  from leny obtain y ys' where ys [simp]: "ys = y # ys'" by(cases ys, auto)
  from lenz leny nth have "(f(x \<mapsto> y))(xs [\<mapsto>] ys') = (f(x \<mapsto> y))(xs [\<mapsto>] zs')"
    by-(rule IH, auto)
  moreover from nth have "y = z" by auto
  ultimately show ?case by(simp add: map_upds_def)
qed


lemma [simp]:
  fixes e :: "('a, 'b) exp" and es :: "('a, 'b) exp list"
  shows IUF_extTA2J1: "IUF e (convert_extTA f ta) e' \<longleftrightarrow> IUF e ta e'"
  and IUFs_extTA2J1: "IUFs es (convert_extTA f ta) es' \<longleftrightarrow> IUFs es ta es'"
proof -
  have "IUF e (convert_extTA f ta) e' \<Longrightarrow> IUF e ta e'"
    and "IUFs es (convert_extTA f ta) es' \<Longrightarrow> IUFs es ta es'"
  proof(induct e ta'\<equiv>"convert_extTA f ta" e' and es ta'\<equiv>"convert_extTA f ta" es' rule: IUF_IUFs.inducts)
    case (IUFFail e v a l)
    from `\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace> = convert_extTA f ta` have "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>" by(cases ta) auto
    with `final e` show ?case by(clarify)
  qed auto
  moreover
  have "IUF e ta e' \<Longrightarrow> IUF e (convert_extTA f ta) e'"
    and "IUFs es ta es' \<Longrightarrow> IUFs es (convert_extTA f ta) es'"
  proof(induct rule: IUF_IUFs.inducts)
    case (IUFFail e v a l)
    have eq: "convert_extTA f \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace> = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>" by simp
    from IUFFail show ?case by(subst eq) clarify
  qed auto
  ultimately show "IUF e (convert_extTA f ta) e' \<longleftrightarrow> IUF e ta e'"
    and "IUFs es (convert_extTA f ta) es' \<longleftrightarrow> IUFs es ta es'" by blast+
qed

lemma sim_move01_into_Red1:
  "sim_move01 P ta e E' h xs ta' e2' h' xs'
  \<Longrightarrow> if \<tau>Move0 P h (e, es1)
      then \<tau>Red1't P h ((E', xs), exs2) ((e2', xs'), exs2) \<and> ta = \<epsilon> \<and> h = h'
      else \<exists>ex2' exs2' ta'. \<tau>Red1'r P h ((E', xs), exs2) (ex2', exs2') \<and>
                           P \<turnstile>1 \<langle>ex2'/exs2',h\<rangle> -ta'\<rightarrow> \<langle>(e2', xs')/exs2,h'\<rangle> \<and>
                           \<not> \<tau>Move1 P h (ex2', exs2') \<and> \<not> IUFL ex2' exs2' ta' (e2', xs') exs2 \<and>
                           ta_bisim01 ta ta'"
apply(auto simp add: sim_move01_def IUFL_def intro: \<tau>red1't_into_\<tau>Red1't \<tau>red1'r_into_\<tau>Red1'r red1Red)
 apply(rule exI conjI)+
  apply(rule \<tau>red1'r_into_\<tau>Red1'r)
 apply(fastsimp simp add: IUFL_def intro: red1Red)
apply(rule exI conjI)+
apply(auto intro: red1Red)
done

lemma sim_move01_max_vars_decr:
  "sim_move01 P ta e0 e h xs ta' e' h' xs' \<Longrightarrow> max_vars e' \<le> max_vars e"
by(fastsimp simp add: sim_move01_def split: split_if_asm dest: \<tau>red1't_max_vars red1_max_vars_decr \<tau>red1'r_max_vars)

lemma Red1_simulates_red0:
  assumes wf: "wf_J_prog P"
  and red: "P \<turnstile>0 \<langle>e1/es1, h\<rangle> -ta\<rightarrow> \<langle>e1'/es1', h'\<rangle>"
  and bisiml: "bisim_list1 (e1, es1) (ex2, exs2)"
  shows "\<exists>ex2'' exs2''. bisim_list1 (e1', es1') (ex2'', exs2'') \<and>
        (if \<tau>Move0 P h (e1, es1)
         then \<tau>Red1't (compP1 P) h (ex2, exs2) (ex2'', exs2'') \<and> ta = \<epsilon> \<and> h = h'
         else \<exists>ex2' exs2' ta'. \<tau>Red1'r (compP1 P) h (ex2, exs2) (ex2', exs2') \<and> 
                               compP1 P \<turnstile>1 \<langle>ex2'/exs2', h\<rangle> -ta'\<rightarrow> \<langle>ex2''/exs2'', h'\<rangle> \<and>
                               \<not> \<tau>Move1 P h (ex2', exs2') \<and> \<not> IUFL ex2' exs2' ta' ex2'' exs2'' \<and> ta_bisim01 ta ta')"
  (is "\<exists>ex2'' exs2'' . _ \<and> ?red ex2'' exs2''")
using red
proof(cases)
  case (red0Red e H TA e' H' XS' es)
  hence e1: "e1 = e" and e1': "e1' = e'"
    and [simp]: "H = h" "TA = ta" "es = es1" "H' = h'" "es1' = es1"
    and red: "extTA2J0 P,P \<turnstile> \<langle>e,(h, empty)\<rangle> -TA\<rightarrow> \<langle>e',(h', XS')\<rangle>"
    and notsynth: "\<forall>aMvs. call e = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P h aMvs" by simp_all
  from bisiml e1 obtain E xs where ex2: "ex2 = (E, xs)"
    and bisim: "bisim [] e E xs" and fv: "fv e1 = {}" 
    and length: "max_vars E \<le> length xs" and bsl: "bisim_list es exs2"
    and D: "\<D> e1 \<lfloor>{}\<rfloor>" by(auto elim!: bisim_list1_elim)
  from bisim_max_vars[OF bisim] length red1_simulates_red_aux[OF wf red bisim] fv e1 notsynth
  obtain ta' e2' xs' where sim: "sim_move01 (compP1 P) TA e E h xs ta' e2' h' xs'"
    and bisim': "bisim [] e' e2' xs'" and XS': "XS' \<subseteq>\<^sub>m empty" by auto
  from sim_move01_into_Red1[OF sim, of es1 exs2]
  have "?red (e2', xs') exs2" unfolding e1 ex2 by auto
  moreover {
    note bsl bisim' moreover
    from fv e1 red_fv_subset[OF wf_prog_wwf_prog[OF wf] red]
    have "fv e' = {}" by simp
    moreover from red D e1 have "\<D> e' \<lfloor>dom XS'\<rfloor>"
      by(auto dest: red_preserves_defass[OF wf] split: split_if_asm)
    with red_dom_lcl[OF red] `fv e1 = {}` e1 have "\<D> e' \<lfloor>{}\<rfloor>"
      by(auto elim!: D_mono' simp add: hyperset_defs)
    moreover from sim have "length xs = length xs'" "max_vars e2' \<le> max_vars E"
      by(auto dest: sim_move01_preserves_len sim_move01_max_vars_decr)
    with length have length': "max_vars e2' \<le> length xs'" by(auto)
    ultimately have "bisim_list1 (e1', es) ((e2', xs'), exs2)" unfolding e1' by(rule bisim_list1I) }
  ultimately show ?thesis using ex2 by(simp split del: split_if)(rule exI conjI|assumption)+
next
  case (red0Call e a M vs H C fs Ts T pns body D es)
  hence [simp]: "es1 = es" "H = h" "ta = \<epsilon>" "h' = h" 
    and es1': "es1' = e # es"
    and e1: "e1 = e"
    and e1': "e1' = blocks (this#pns, Class D#Ts, Addr a#vs, body)"
    and call: "call e = \<lfloor>(a, M, vs)\<rfloor>"
    and ha: "h a = \<lfloor>Obj C fs\<rfloor>"
    and nec: "\<not> is_external_call P (Class C) M"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D"
    and len: "length vs = length pns" "length Ts = length pns" by simp_all
  from bisiml e1 obtain E xs where ex2: "ex2 = (E, xs)"
    and bisim: "bisim [] e E xs" and fv: "fv e1 = {}" 
    and length: "max_vars E \<le> length xs" and bsl: "bisim_list es exs2"
    and D: "\<D> e1 \<lfloor>{}\<rfloor>" by(auto elim!: bisim_list1_elim)
  
  from bisim_call_Some_call1[OF bisim call, of "compP1 P" h] length
  obtain e' xs' where red: "\<tau>red1'r (compP1 P) h (E, xs) (e', xs')"
    and "call1 e' = \<lfloor>(a, M, vs)\<rfloor>" "bisim [] e e' xs'" 
    and "take 0 xs = take 0 xs'" by auto
    
  let ?e1' = "blocks (this#pns, Class D#Ts, Addr a#vs, body)"
  let ?e2' = "blocks1 0 (Class D#Ts) (compE1 (this # pns) body)"
  let ?xs2' = "Addr a # vs @ replicate (max_vars (compE1 (this # pns) body))  undefined"
  let ?exs2' = "(e', xs') # exs2"

  have "\<tau>Red1'r (compP1 P) h ((E, xs), exs2) ((e', xs'), exs2)"
    using red by(rule \<tau>red1'r_into_\<tau>Red1'r)
  moreover {
    note `call1 e' = \<lfloor>(a, M, vs)\<rfloor>` 
    moreover note ha
    moreover from nec have "\<not> is_external_call (compP1 P) (Class C) M" by simp
    moreover have "compP1 P \<turnstile> C sees M:Ts \<rightarrow> T = (\<lambda>(pns, body). compE1 (this # pns) body) (pns, body) in D"
      using sees unfolding compP1_def by(rule sees_method_compP)
    hence sees': "compP1 P \<turnstile> C sees M:Ts \<rightarrow> T = compE1 (this # pns) body in D" by simp
    moreover from len have "length vs = length Ts" by simp
    ultimately have "compP1 P \<turnstile>1 \<langle>(e', xs')/exs2,h\<rangle> -\<epsilon>\<rightarrow> \<langle>(?e2', ?xs2')/?exs2', h\<rangle>" by(rule red1Call) 
    moreover have "\<tau>Move1 P h ((e', xs'), exs2)" using `call1 e' = \<lfloor>(a, M, vs)\<rfloor>` nec ha
      by(auto simp add: \<tau>move1_not_call1 synthesized_call_def)
    moreover have "\<not> IUFL (e', xs') exs2 \<epsilon> (?e2', ?xs2') ?exs2'" by(simp add: IUFL_def)
    ultimately have "\<tau>Red1' (compP1 P) h ((e', xs'), exs2) ((?e2', ?xs2'), ?exs2')" by auto }
  ultimately have "\<tau>Red1't (compP1 P) h ((E, xs), exs2) ((?e2', ?xs2'), ?exs2')" by(rule rtranclp_into_tranclp1)
  moreover
  
  from bsl `bisim [] e e' xs'` have "bisim_list (e1 # es) ?exs2'" using fv D unfolding e1
  proof(rule bisim_listCons)
    from red have "length xs' = length xs" by(rule \<tau>red1'r_preserves_len)
    moreover from red have "max_vars e' \<le> max_vars E" by(rule \<tau>red1'r_max_vars)
    ultimately show "max_vars e' \<le> length xs'" using length by simp
    from `call e = \<lfloor>(a, M, vs)\<rfloor>` show "call e = \<lfloor>(a, M, vs)\<rfloor>" by simp
    from `call1 e' = \<lfloor>(a, M, vs)\<rfloor>` show "call1 e' = \<lfloor>(a, M, vs)\<rfloor>" by simp
  qed
  hence "bisim_list1 (e1', es1') ((?e2', ?xs2'), ?exs2')"
    unfolding e1' es1' e1
  proof(rule bisim_list1I)
    from wf_prog_wwf_prog[OF wf] `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D`
    have "wf_mdecl wwf_J_mdecl P D (M,Ts,T,pns,body)" by(rule sees_wf_mdecl)
    hence fv': "fv body \<subseteq> set pns \<union> {this}" by(auto simp add: wf_mdecl_def)
    moreover from `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D` have "\<not> contains_insync body"
      by(auto dest!: sees_wf_mdecl[OF wf] WT_expr_locks simp add: wf_mdecl_def contains_insync_conv)
    ultimately have "bisim ([this] @ pns) body (compE1 ([this] @ pns) body) ?xs2'"
      by -(rule compE1_bisim, auto)
    with `length vs = length pns` `length Ts = length pns`
    have "bisim ([] @ [this]) (blocks (pns, Ts, vs, body)) (blocks1 (Suc 0) Ts (compE1 (this # pns) body)) ?xs2'"
      by -(drule blocks_bisim,auto simp add: nth_append)
    from bisimBlockSomeNone[OF this, of "Addr a" "Class D"]
    show "bisim [] ?e1' ?e2' ?xs2'" by simp
    from fv' len show "fv ?e1' = {}" by auto

    from wf `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D`
    have "wf_mdecl wf_J_mdecl P D (M,Ts,T,pns,body)" by(rule sees_wf_mdecl)
    hence "\<D> body \<lfloor>set pns \<union> {this}\<rfloor>" by(auto simp add: wf_mdecl_def)
    with `length vs = length pns` `length Ts = length pns`
    have "\<D> (blocks (pns, Ts, vs, body)) \<lfloor>dom [this \<mapsto> Addr a]\<rfloor>" by(auto)
    thus "\<D> ?e1' \<lfloor>{}\<rfloor>" by auto
    
    from len show "max_vars ?e2' \<le> length ?xs2'" by(auto simp add: blocks1_max_vars)
  qed
  moreover have "\<tau>Move0 P h (e1, es1)" using call e1 nec ha
    by(auto simp add: \<tau>move0_callD synthesized_call_def)
  ultimately show ?thesis using ex2 `call e = \<lfloor>(a, M, vs)\<rfloor>` 
    by(simp del: \<tau>Move1.simps)(rule exI conjI|assumption)+
next
  case (red0Return e' e es H)
  hence e1: "e1 = e'" and es1: "es1 = e # es" and e1': "e1' = inline_call e' e"
    and [simp]: "H = h" "ta = \<epsilon>" "es1' = es" "h' = h"
    and fin: "final e'" by(simp_all)
  from bisiml e1 es1 obtain E' xs' E xs exs' aMvs where ex2: "ex2 = (E', xs')" and exs2: "exs2 = (E, xs) # exs'"
    and bisim': "bisim [] e' E' xs'"
    and bisim: "bisim [] e E xs"
    and fv: "fv e = {}"
    and length: "max_vars E \<le> length xs"
    and bisiml: "bisim_list es exs'"
    and D: "\<D> e \<lfloor>{}\<rfloor>"
    and call: "call e = \<lfloor>aMvs\<rfloor>"
    and call1: "call1 E = \<lfloor>aMvs\<rfloor>"
    by(fastsimp elim: bisim_list1_elim)
  let ?e2' = "inline_call E' E"

  from `final e'` bisim' have "final E'" by(auto)
  hence red': "compP1 P \<turnstile>1 \<langle>ex2/exs2, H\<rangle> -\<epsilon>\<rightarrow> \<langle>(?e2', xs)/exs', H\<rangle>"
    unfolding ex2 exs2 by(rule red1Return)
  moreover have "\<not> IUFL ex2 exs2 \<epsilon> (?e2', xs) exs'" using exs2 by(simp add: IUFL_def)
  moreover have "\<tau>Move0 P h (e1, es1) = \<tau>Move1 P h ((E', xs'), exs2)"
    using e1 `final e'` `final E'` by auto
  moreover {
    note bisiml
    moreover
    from bisim' fin bisim
    have "bisim [] (inline_call e' e) (inline_call E' E) xs"
      using call by(rule bisim_inline_call)(simp add: fv)
    moreover from fv_inline_call[OF call, of e'] fv fin 
    have "fv (inline_call e' e) = {}" by auto
    moreover from fin have "\<D> e' \<lfloor>{}\<rfloor>" by auto
    hence "\<D> (inline_call e' e) \<lfloor>{}\<rfloor>"
      using call D by(rule defass_inline_call)
    moreover from `call1 E = \<lfloor>aMvs\<rfloor>`
    have "max_vars ?e2' \<le> max_vars E + max_vars E'" by(rule inline_call_max_vars1)
    with `final E'` length have "max_vars ?e2' \<le> length xs" by(auto elim!: final.cases)
    ultimately have "bisim_list1 (inline_call e' e, es) ((?e2', xs), exs')"
      by(rule bisim_list1I) }
  ultimately show ?thesis using e1' `final e'` `final E'` e1 ex2 
    apply(simp del: \<tau>Move0.simps \<tau>Move1.simps)
    apply(rule exI conjI impI|assumption)+
     apply(rule tranclp.r_into_trancl, simp)
    apply blast
    done
qed


lemma sim_move10_into_red0:
  assumes wwf: "wwf_J_prog P"
  and sim: "sim_move10 P ta e2 e2' e h empty ta' e' h' x'"
  and fv: "fv e = {}"
  shows "if \<tau>move1 P h e2
         then (\<tau>Red0t P h (e, es) (e', es) \<or> countInitBlock e2' < countInitBlock e2 \<and> e' = e \<and> x' = empty) \<and> ta = \<epsilon> \<and> h = h'
         else \<exists>e'' ta'. \<tau>Red0r P h (e, es) (e'', es) \<and>
                        P \<turnstile>0 \<langle>e''/es,h\<rangle> -ta'\<rightarrow> \<langle>e'/es,h'\<rangle> \<and>
                        \<not> \<tau>Move0 P h (e'', es) \<and> ta_bisim01 ta' (extTA2J1 (compP1 P) ta)"
proof(cases "\<tau>move1 P h e2")
  case True
  with sim have "\<not> final e2"
    and red: "\<tau>red0t (extTA2J0 P) P h (e, empty) (e', x') \<or>
              countInitBlock e2' < countInitBlock e2 \<and> e' = e \<and> x' = empty"
    and [simp]: "h' = h" "ta = \<epsilon>" "ta' = \<epsilon>" by(simp_all add: sim_move10_def)
  from red have "\<tau>Red0t P h (e, es) (e', es) \<or>
                 countInitBlock e2' < countInitBlock e2 \<and> e' = e \<and> x' = empty"
  proof
    assume red: "\<tau>red0t (extTA2J0 P) P h (e, empty) (e', x')"
    from \<tau>red0t_fv_subset[OF wwf red] \<tau>red0t_dom_lcl[OF wwf red] fv
    have "dom x' \<subseteq> {}" by(auto split: split_if_asm)
    hence "x' = empty" by auto
    with red have "\<tau>red0t (extTA2J0 P) P h (e, empty) (e', empty)" by simp
    with wwf have "\<tau>Red0t P h (e, es) (e', es)"
      using fv by(rule \<tau>red0t_into_\<tau>Red0t)
    thus ?thesis ..
  qed simp
  with True show ?thesis by simp
next
  case False
  with sim obtain e'' xs'' where "\<not> final e2"
    and \<tau>red: "\<tau>red0r (extTA2J0 P) P h (e, empty) (e'', xs'')"
    and red: "extTA2J0 P,P \<turnstile> \<langle>e'',(h, xs'')\<rangle> -ta'\<rightarrow> \<langle>e',(h', x')\<rangle>"
    and "\<not> \<tau>move0 P h e''" "ta_bisim01 ta' (extTA2J1 (compP1 P) ta)" "no_call P h e''"
    by(auto simp add: sim_move10_def)
  from \<tau>red0r_fv_subset[OF wwf \<tau>red] \<tau>red0r_dom_lcl[OF wwf \<tau>red] fv
  have "dom xs'' \<subseteq> {}" by(auto)
  hence "xs'' = empty" by(auto)
  with \<tau>red have "\<tau>red0r (extTA2J0 P) P h (e, empty) (e'', empty)" by simp
  with wwf have "\<tau>Red0r P h (e, es) (e'', es)"
    using fv by(rule \<tau>red0r_into_\<tau>Red0r)
  moreover from red `xs'' = empty`
  have "extTA2J0 P,P \<turnstile> \<langle>e'',(h, empty)\<rangle> -ta'\<rightarrow> \<langle>e',(h', x')\<rangle>" by simp
  from red0Red[OF this] `no_call P h e''` 
  have "P \<turnstile>0 \<langle>e''/es,h\<rangle> -ta'\<rightarrow> \<langle>e'/es,h'\<rangle>" by(simp add: no_call_def)
  moreover from `\<not> \<tau>move0 P h e''` red
  have "\<not> \<tau>Move0 P h (e'', es)" by auto
  ultimately show ?thesis using False `ta_bisim01 ta' (extTA2J1 (compP1 P) ta)`
    by(simp del: \<tau>Move0.simps) blast
qed

lemma red0_simulates_Red1:
  assumes wf: "wf_J_prog P"
  and red: "compP1 P \<turnstile>1 \<langle>ex2/exs2, h\<rangle> -ta\<rightarrow> \<langle>ex2'/exs2', h'\<rangle>"
  and bisiml: "bisim_list1 (e, es) (ex2, exs2)"
  and IUFL: "\<not> IUFL ex2 exs2 ta ex2' exs2'"
  shows "\<exists>e' es'. bisim_list1 (e', es') (ex2', exs2') \<and>
                 (if \<tau>Move1 P h (ex2, exs2)
                  then (\<tau>Red0t P h (e, es) (e', es') \<or> countInitBlock (fst ex2') < countInitBlock (fst ex2) \<and> exs2' = exs2 \<and> e' = e \<and> es' = es) \<and>
                        ta = \<epsilon> \<and> h = h'
                  else \<exists>e'' es'' ta'. \<tau>Red0r P h (e, es) (e'', es'') \<and>
                                      P \<turnstile>0 \<langle>e''/es'', h\<rangle> -ta'\<rightarrow> \<langle>e'/es', h'\<rangle> \<and>
                                      \<not> \<tau>Move0 P h (e'', es'') \<and> ta_bisim01 ta' ta)"
  (is "\<exists>e' es' . _ \<and> ?red e' es'")
using red
proof(cases)
  case (red1Red E H xs TA E' H' xs' exs)
  hence red: "compP1 P \<turnstile>1 \<langle>E,(H, xs)\<rangle> -TA\<rightarrow> \<langle>E',(H', xs')\<rangle>" and ex2: "ex2 = (E, xs)"
    and ex2': "ex2' = (E', xs')"
    and [simp]: "ta = extTA2J1 (compP1 P) TA" "h = H" "exs2 = exs" "exs2' = exs" "h' = H'" by simp_all
  from bisiml ex2 have bisim: "bisim [] e E xs" and fv: "fv e = {}"
    and length: "max_vars E \<le> length xs" and bsl: "bisim_list es exs"
    and D: "\<D> e \<lfloor>{}\<rfloor>" by(auto elim: bisim_list1_elim)
  from IUFL ex2 ex2' have IUF: "\<not> IUF E TA E'" by(auto simp add: IUFL_def)
  from red_simulates_red1_aux[OF wf red, simplified, OF bisim, of empty] fv length IUF D
  obtain TA' e2' x' where red': "sim_move10 P TA E E' e H empty TA' e2' H' x'"
    and bisim'': "bisim [] e2' E' xs'" and lcl': "x' \<subseteq>\<^sub>m empty" by auto
  from red have "\<not> final E" by auto
  with sim_move10_into_red0[OF wf_prog_wwf_prog[OF wf] red', of es] fv ex2 ex2'
  have red'': "?red e2' es" by fastsimp
  moreover {
    note bsl bisim''
    moreover from red' fv have "fv e2' = {}"
      by(fastsimp simp add: sim_move10_def split: split_if_asm dest: \<tau>red0r_fv_subset[OF wf_prog_wwf_prog[OF wf]] \<tau>red0t_fv_subset[OF wf_prog_wwf_prog[OF wf]] red_fv_subset[OF wf_prog_wwf_prog[OF wf]])
    moreover from red' have "dom x' \<subseteq> dom (empty) \<union> fv e"
      unfolding sim_move10_def
      apply(auto split: split_if_asm del: subsetI dest: \<tau>red0r_dom_lcl[OF wf_prog_wwf_prog[OF wf]] \<tau>red0t_dom_lcl[OF wf_prog_wwf_prog[OF wf]])
      apply(frule \<tau>red0r_fv_subset[OF wf_prog_wwf_prog[OF wf]])
      apply(auto dest!: \<tau>red0r_dom_lcl[OF wf_prog_wwf_prog[OF wf]] red_dom_lcl del: subsetI, blast)[1]
      done
    with fv have "dom x' \<subseteq> {}" by(auto)
    hence "x' = empty" by(auto)
    with D red' have "\<D> e2' \<lfloor>{}\<rfloor>"
      by(auto dest!: sim_move10_preserves_defass[OF wf] split: split_if_asm)
    moreover from red have "length xs' = length xs" by(auto dest: red1_preserves_len)
    with red1_max_vars[OF red] length
    have "max_vars E' \<le> length xs'" by simp
    ultimately have "bisim_list1 (e2', es) ((E', xs'), exs)"
      by(rule bisim_list1I) }
  ultimately show ?thesis using ex2'
    by(clarsimp split: split_if_asm)(rule exI conjI|assumption|simp)+
next
  case (red1Call E a M vs H C fs Ts T body D xs exs)
  hence [simp]: "ex2 = (E, xs)" "exs2 = exs" "h = H" "ta = \<epsilon>" "h' = H"
    and ex2': "ex2' = (blocks1 0 (Class D#Ts) body, Addr a # vs @ replicate (max_vars body) undefined)"
    and exs': "exs2' = (E, xs) # exs"
    and call: "call1 E = \<lfloor>(a, M, vs)\<rfloor>" and ha: "H a = \<lfloor>Obj C fs\<rfloor>"
    and nec: "\<not> is_external_call (compP1 P) (Class C) M"
    and sees: "compP1 P \<turnstile> C sees M: Ts\<rightarrow>T = body in D"
    and len: "length vs = length Ts" by simp_all
  let ?e2' = "blocks1 0 (Class D#Ts) body"
  let ?xs2' = "Addr a # vs @ replicate (max_vars body) undefined"
  from bisiml have bisim: "bisim [] e E xs" and fv: "fv e = {}"
    and length: "max_vars E \<le> length xs" and bsl: "bisim_list es exs"
    and D: "\<D> e \<lfloor>{}\<rfloor>" by(auto elim: bisim_list1_elim)

  from bisim `call1 E = \<lfloor>(a, M, vs)\<rfloor>`
  have "call e = \<lfloor>(a, M, vs)\<rfloor>" by(rule bisim_call1_Some_call)
  moreover note ha
  moreover from `\<not> is_external_call (compP1 P) (Class C) M`
  have "\<not> is_external_call P (Class C) M" by simp
  moreover from `compP1 P \<turnstile> C sees M: Ts\<rightarrow>T = body in D`
  obtain pns Jbody where sees': "P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, Jbody) in D"
    and body: "body = compE1 (this # pns) Jbody"
    by(auto dest: sees_method_compPD)
  let ?e' = "blocks(this#pns, Class D#Ts, Addr a#vs, Jbody)"
  note sees' moreover from wf sees' have "length Ts = length pns"
    by(auto dest!: sees_wf_mdecl simp add: wf_mdecl_def)
  with len have "length vs = length pns" "length Ts = length pns" by simp_all
  ultimately have red': "P \<turnstile>0 \<langle>e/es, H\<rangle> -\<epsilon>\<rightarrow> \<langle>?e'/e#es, H\<rangle>" by(rule red0Call)
  moreover from `call e = \<lfloor>(a, M, vs)\<rfloor>` ha `\<not> is_external_call P (Class C) M`
  have "\<tau>Move0 P h (e, es)" by(auto simp add: \<tau>move0_callD synthesized_call_def)
  ultimately have "\<tau>Red0t P H (e, es) (?e', e#es)" by auto
  moreover
  from bsl bisim fv D length `call e = \<lfloor>(a, M, vs)\<rfloor>` `call1 E = \<lfloor>(a, M, vs)\<rfloor>`
  have "bisim_list (e # es) ((E, xs) # exs)" by(rule bisim_list.intros)
  hence "bisim_list1 (?e', e # es) (ex2', (E, xs) # exs)" unfolding ex2'
  proof(rule bisim_list1I)
    from wf_prog_wwf_prog[OF wf] sees'
    have "wf_mdecl wwf_J_mdecl P D (M,Ts,T,pns,Jbody)" by(rule sees_wf_mdecl)
    hence "fv Jbody \<subseteq> set pns \<union> {this}" by(auto simp add: wf_mdecl_def)
    moreover from sees' have "\<not> contains_insync Jbody"
      by(auto dest!: sees_wf_mdecl[OF wf] WT_expr_locks simp add: wf_mdecl_def contains_insync_conv)
    ultimately have "bisim ([] @ this # pns) Jbody (compE1 ([] @ this # pns) Jbody) ?xs2'"
      by -(rule compE1_bisim, auto)
    with `length vs = length Ts` `length Ts = length pns` body
    have "bisim [] (blocks (this # pns, Class D # Ts, Addr a # vs, Jbody)) (blocks1 (length ([] :: vname list)) (Class D # Ts) body) ?xs2'"
      by -(rule blocks_bisim, auto simp add: nth_append nth_Cons')
    thus "bisim [] ?e' ?e2' ?xs2'" by simp
    from `length vs = length Ts` `length Ts = length pns` `fv Jbody \<subseteq> set pns \<union> {this}`
    show "fv ?e' = {}" by auto
    from wf sees'
    have "wf_mdecl wf_J_mdecl P D (M,Ts,T,pns,Jbody)" by(rule sees_wf_mdecl)
    hence "\<D> Jbody \<lfloor>set pns \<union> {this}\<rfloor>" by(auto simp add: wf_mdecl_def)
    with `length vs = length Ts` `length Ts = length pns`
    have "\<D> (blocks (pns, Ts, vs, Jbody)) \<lfloor>dom [this \<mapsto> Addr a]\<rfloor>" by(auto)
    thus "\<D> ?e' \<lfloor>{}\<rfloor>" by simp
    from len show "max_vars ?e2' \<le> length ?xs2'" by(simp add: blocks1_max_vars)
  qed
  moreover have "\<tau>Move1 P h (ex2, exs2)" using ha `call1 E = \<lfloor>(a, M, vs)\<rfloor>` `\<not> is_external_call (compP1 P) (Class C) M`
    by(auto simp add: \<tau>move1_not_call1 synthesized_call_def)
  ultimately show ?thesis using exs'
    by(simp del: \<tau>Move1.simps \<tau>Move0.simps)(rule exI conjI rtranclp.rtrancl_refl|assumption)+
next
  case (red1Return E' x' E x exs H)
  hence [simp]: "h = H" "ta = \<epsilon>" "exs2' = exs" "h' = H"
    and ex2: "ex2 = (E', x')" and exs2: "exs2 = (E, x) # exs"
    and ex2': "ex2' = (inline_call E' E, x)"
    and fin: "final E'" by simp_all
  from bisiml ex2 exs2 obtain e' es' aMvs where es: "es = e' # es'"
    and bsl: "bisim_list es' exs"
    and bisim: "bisim [] e E' x'"
    and bisim': "bisim [] e' E x"
    and fv: "fv e' = {}"
    and length: "max_vars E \<le> length x"
    and D: "\<D> e' \<lfloor>{}\<rfloor>"
    and call: "call e' = \<lfloor>aMvs\<rfloor>"
    and call1: "call1 E = \<lfloor>aMvs\<rfloor>"
    by(fastsimp elim!: bisim_list1_elim)
  
  from `final E'` bisim have fin': "final e" by(auto)
  hence "P \<turnstile>0 \<langle>e/e' # es',H\<rangle> -\<epsilon>\<rightarrow> \<langle>inline_call e e'/es',H\<rangle>" by(rule red0Return)
  moreover from bisim fin' bisim' call
  have "bisim [] (inline_call e e') (inline_call E' E) x"
    by(rule bisim_inline_call)(simp add: fv)
  with bsl have "bisim_list1 (inline_call e e', es') (ex2', exs)" unfolding ex2'
  proof(rule bisim_list1I)
    from fin' fv_inline_call[OF call, of e] fv show "fv (inline_call e e') = {}" by auto
    from fin' have "\<D> e \<lfloor>{}\<rfloor>" by auto
    thus "\<D> (inline_call e e') \<lfloor>{}\<rfloor>" using call D by(rule defass_inline_call)
    
    from call1_imp_call[OF call1]
    have "max_vars (inline_call E' E) \<le> max_vars E + max_vars E'"
      by(rule inline_call_max_vars)
    with fin length show "max_vars (inline_call E' E) \<le> length x" by(auto elim!: final.cases)
  qed
  moreover have "\<tau>Move1 P h (ex2, exs2) = \<tau>Move0 P h (e, es)" using ex2 call1 call fin fin' by(auto)
  ultimately show ?thesis using es
    by(simp del: \<tau>Move1.simps \<tau>Move0.simps) blast
qed


lemma bisim_expr_locks_eq: "bisim Vs e e' xs \<Longrightarrow> expr_locks e = expr_locks e'"
  and bisims_expr_lockss_eq: "bisims Vs es es' xs \<Longrightarrow> expr_lockss es = expr_lockss es'"
by(induct rule: bisim_bisims.inducts)(auto intro!: ext)

lemma bisim_list_expr_lockss_eq: "bisim_list es exs' \<Longrightarrow> expr_lockss es = expr_lockss (map fst exs')"
apply(induct rule: bisim_list.induct)
apply(auto dest: bisim_expr_locks_eq)
done

interpretation red0_Red1_FWwbase:
  FWdelay_bisimulation_base final_expr0 "mred0 P" final_expr1 "mred1 (compP1 P)" "bisim_red0_Red1" "\<tau>MOVE0 P" "\<tau>MOVE1 (compP1 P)" for P
.

lemma \<tau>Red1't_into_Red1'_\<tau>mthr_silent_movet:
  "\<tau>Red1't P h (ex2, exs2) (ex2'', exs2'') \<Longrightarrow> Red1'_\<tau>mthr.silent_movet P ((ex2, exs2), h) ((ex2'', exs2''), h)"
apply(induct rule: tranclp_induct2)
 apply clarsimp
 apply(rule tranclp.r_into_trancl)
 apply(simp add: Red1'_\<tau>mthr.silent_move_iff)
apply(erule tranclp.trancl_into_trancl)
apply(simp add: Red1'_\<tau>mthr.silent_move_iff)
done

lemmas \<tau>Red1't_into_Red1'_\<tau>mthr_silent_moves = tranclp_into_rtranclp[OF \<tau>Red1't_into_Red1'_\<tau>mthr_silent_movet]

lemma \<tau>Red0r_into_red0_\<tau>mthr_silent_moves:
  "\<tau>Red0r P h (e, es) (e'', es'') \<Longrightarrow> red0_\<tau>mthr.silent_moves P ((e, es), h) ((e'', es''), h)"
apply(induct rule: rtranclp_induct2)
 apply blast
apply(erule rtranclp.rtrancl_into_rtrancl)
apply(simp add: red0_\<tau>mthr.silent_move_iff)
done

lemma \<tau>Red0t_into_red0_\<tau>mthr_silent_movet:
  "\<tau>Red0t P h (e, es) (e'', es'') \<Longrightarrow> red0_\<tau>mthr.silent_movet P ((e, es), h) ((e'', es''), h)"
apply(induct rule: tranclp_induct2)
apply(fastsimp simp add: red0_\<tau>mthr.silent_move_iff elim: tranclp.trancl_into_trancl)+
done

lemma \<tau>Red1'r_into_Red1'_\<tau>mthr_silent_moves:
  "\<tau>Red1'r P h (ex, exs) (ex', exs') \<Longrightarrow> Red1'_\<tau>mthr.silent_moves P ((ex, exs), h) ((ex', exs'), h)"
apply(induct rule: rtranclp_induct2)
 apply blast
apply(erule rtranclp.rtrancl_into_rtrancl)
apply(simp add: Red1'_\<tau>mthr.silent_move_iff)
done

lemma delay_bisimulation_red0_Red1: 
  assumes wf: "wf_J_prog P"
  shows "delay_bisimulation_measure (mred0 P) (mred1' (compP1 P)) bisim_red0_Red1 (ta_bisim bisim_red0_Red1) (\<tau>MOVE0 P) (\<tau>MOVE1 (compP1 P)) (\<lambda>es es'. False) (\<lambda>(((e', xs'), exs'), h') (((e, xs), exs), h). countInitBlock e'< countInitBlock e)"
  (is "delay_bisimulation_measure _ _ _ _ _ _ ?\<mu>1 ?\<mu>2")
proof(unfold_locales)
  fix s1 s2 s1'
  assume "bisim_red0_Red1 s1 s2" "red0_\<tau>mthr.silent_move P s1 s1'"
  moreover obtain ex1 exs1 h1 where s1: "s1 = ((ex1, exs1), h1)" by(cases s1, auto)
  moreover obtain ex1' exs1' h1' where s1': "s1' = ((ex1', exs1'), h1')" by(cases s1', auto)
  moreover obtain ex2 exs2 h2 where s2: "s2 = ((ex2, exs2), h2)" by(cases s2, auto)
  ultimately have bisim: "bisim_list1 (ex1, exs1) (ex2, exs2)"
    and heap: "h1 = h2"
    and red: "P \<turnstile>0 \<langle>ex1/exs1,h1\<rangle> -\<epsilon>\<rightarrow> \<langle>ex1'/exs1',h1'\<rangle>"
    and \<tau>: "\<tau>Move0 P h1 (ex1, exs1)"
    by(auto simp add: bisim_red0_Red1_def red0_\<tau>mthr.silent_move_iff)
  from Red1_simulates_red0[OF wf red bisim] \<tau>
  obtain ex2'' exs2'' where bisim': "bisim_list1 (ex1', exs1') (ex2'', exs2'')" 
    and red': "\<tau>Red1't (compP1 P) h1 (ex2, exs2) (ex2'', exs2'')"
    and [simp]: "h1' = h1" by auto
  from \<tau>Red1't_into_Red1'_\<tau>mthr_silent_movet[OF red'] bisim' heap
  have "\<exists>s2'. Red1'_\<tau>mthr.silent_movet (compP1 P) s2 s2' \<and> bisim_red0_Red1 s1' s2'"
    unfolding s2 s1' by(auto simp add: bisim_red0_Red1_def)
  thus "bisim_red0_Red1 s1' s2 \<and> ?\<mu>1^++ s1' s1 \<or> (\<exists>s2'. Red1'_\<tau>mthr.silent_movet (compP1 P) s2 s2' \<and> bisim_red0_Red1 s1' s2')" ..
next
  fix s1 s2 s2'
  assume "bisim_red0_Red1 s1 s2" "Red1'_\<tau>mthr.silent_move (compP1 P) s2 s2'"
  moreover obtain ex1 exs1 h1 where s1: "s1 = ((ex1, exs1), h1)" by(cases s1, auto)
  moreover obtain ex2 exs2 h2 where s2: "s2 = ((ex2, exs2), h2)" by(cases s2, auto)
  moreover obtain ex2' exs2' h2' where s2': "s2' = ((ex2', exs2'), h2')" by(cases s2', auto)
  ultimately have bisim: "bisim_list1 (ex1, exs1) (ex2, exs2)"
    and heap: "h1 = h2"
    and red: "compP1 P \<turnstile>1 \<langle>ex2/exs2,h2\<rangle> -\<epsilon>\<rightarrow> \<langle>ex2'/exs2',h2'\<rangle>"
    and \<tau>: "\<tau>Move1 P h2 (ex2, exs2)"
    and IUF: "\<not> IUFL ex2 exs2 (\<epsilon>:: J1_thread_action) ex2' exs2'"
    by(fastsimp simp add: bisim_red0_Red1_def Red1'_\<tau>mthr.silent_move_iff)+
  from red0_simulates_Red1[OF wf red bisim IUF] \<tau>
  obtain e' es' where bisim': "bisim_list1 (e', es') (ex2', exs2')"
    and red': "\<tau>Red0t P h2 (ex1, exs1) (e', es') \<or> 
               countInitBlock (fst ex2') < countInitBlock (fst ex2) \<and> exs2' = exs2 \<and> e' = ex1 \<and> es' = exs1"
    and [simp]: "h2' = h2" by auto
  from red'
  show "bisim_red0_Red1 s1 s2' \<and> ?\<mu>2^++ s2' s2 \<or> (\<exists>s1'. red0_\<tau>mthr.silent_movet P s1 s1' \<and> bisim_red0_Red1 s1' s2')"
    (is "?refl \<or> ?step")
  proof
    assume "\<tau>Red0t P h2 (ex1, exs1) (e', es')"
    from \<tau>Red0t_into_red0_\<tau>mthr_silent_movet[OF this] bisim' heap
    have ?step unfolding s1 s2' by(auto simp add: bisim_red0_Red1_def)
    thus ?thesis ..
  next
    assume "countInitBlock (fst ex2') < countInitBlock (fst ex2) \<and> exs2' = exs2 \<and> e' = ex1 \<and> es' = exs1"
    hence ?refl using bisim' heap unfolding s1 s2' s2
      by (auto simp add: bisim_red0_Red1_def split_beta)
    thus ?thesis ..
  qed
next
  fix s1 s2 ta1 s1'
  assume "bisim_red0_Red1 s1 s2"  and "mred0 P s1 ta1 s1'" and \<tau>: "\<not> \<tau>MOVE0 P s1 ta1 s1'"
  moreover obtain ex1 exs1 h1 where s1: "s1 = ((ex1, exs1), h1)" by(cases s1, auto)
  moreover obtain ex1' exs1' h1' where s1': "s1' = ((ex1', exs1'), h1')" by(cases s1', auto)
  moreover obtain ex2 exs2 h2 where s2: "s2 = ((ex2, exs2), h2)" by(cases s2, auto)
  ultimately have heap: "h2 = h1"
    and bisim: "bisim_list1 (ex1, exs1) (ex2, exs2)"
    and red: "P \<turnstile>0 \<langle>ex1/exs1,h1\<rangle> -ta1\<rightarrow> \<langle>ex1'/exs1',h1'\<rangle>"
    by(auto simp add: bisim_red0_Red1_def)
  from \<tau> have "\<not> \<tau>Move0 P h1 (ex1, exs1)" unfolding s1
    using red by(auto elim!: red0.cases dest: red_\<tau>_taD)
  with Red1_simulates_red0[OF wf red bisim]
  obtain ex2'' exs2'' ex2' exs2' ta'
    where bisim': "bisim_list1 (ex1', exs1') (ex2'', exs2'')"
    and red': "\<tau>Red1'r (compP1 P) h1 (ex2, exs2) (ex2', exs2')"
    and red'': "compP1 P \<turnstile>1 \<langle>ex2'/exs2',h1\<rangle> -ta'\<rightarrow> \<langle>ex2''/exs2'',h1'\<rangle>"
    and \<tau>': "\<not> \<tau>Move1 P h1 (ex2', exs2')"
    and IUF: "\<not> IUFL ex2' exs2' ta' ex2'' exs2''"
    and ta: "ta_bisim01 ta1 ta'" by auto
  from red'' IUF have "mred1' (compP1 P) ((ex2', exs2'), h1) ta' ((ex2'', exs2''), h1')" by auto
  moreover from \<tau>' have "\<not> \<tau>MOVE1 (compP1 P) ((ex2', exs2'), h1) ta' ((ex2'', exs2''), h1')" by simp
  moreover from red' have "Red1'_\<tau>mthr.silent_moves (compP1 P) s2 ((ex2', exs2'), h1)"
    unfolding s2 heap by(rule \<tau>Red1'r_into_Red1'_\<tau>mthr_silent_moves)
  moreover from bisim' have "bisim_red0_Red1 ((ex1', exs1'), h1') ((ex2'', exs2''), h1')"
    by(auto simp add: bisim_red0_Red1_def)
  ultimately
  show "\<exists>s2' s2'' ta2. Red1'_\<tau>mthr.silent_moves (compP1 P) s2 s2' \<and>  mred1' (compP1 P) s2' ta2 s2'' \<and>
             \<not> \<tau>MOVE1 (compP1 P) s2' ta2 s2'' \<and> bisim_red0_Red1 s1' s2'' \<and> ta_bisim01 ta1 ta2"
    using ta unfolding s1' by blast
next
  fix s1 s2 ta2 s2'
  assume "bisim_red0_Red1 s1 s2"  and "mred1' (compP1 P) s2 ta2 s2'" and \<tau>: "\<not> \<tau>MOVE1 (compP1 P) s2 ta2 s2'"
  moreover obtain ex1 exs1 h1 where s1: "s1 = ((ex1, exs1), h1)" by(cases s1, auto)
  moreover obtain ex2 exs2 h2 where s2: "s2 = ((ex2, exs2), h2)" by(cases s2, auto)
  moreover obtain ex2' exs2' h2' where s2': "s2' = ((ex2', exs2'), h2')" by(cases s2', auto)
  ultimately have heap: "h2 = h1"
    and bisim: "bisim_list1 (ex1, exs1) (ex2, exs2)"
    and red: "compP1 P \<turnstile>1 \<langle>ex2/exs2,h1\<rangle> -ta2\<rightarrow> \<langle>ex2'/exs2',h2'\<rangle>"
    and IUF: "\<not> IUFL ex2 exs2 ta2 ex2' exs2'"
    by(auto simp add: bisim_red0_Red1_def)
  from \<tau> heap have "\<not> \<tau>Move1 P h2 (ex2, exs2)" unfolding s2
    using red by(fastsimp elim!: Red1.cases dest: red1_\<tau>_taD)
  with red0_simulates_Red1[OF wf red bisim IUF]
  obtain e' es' e'' es'' ta'
    where bisim': "bisim_list1 (e', es') (ex2', exs2')"
    and red': "\<tau>Red0r P h1 (ex1, exs1) (e'', es'')"
    and red'': "P \<turnstile>0 \<langle>e''/es'',h1\<rangle> -ta'\<rightarrow> \<langle>e'/es',h2'\<rangle>"
    and \<tau>': "\<not> \<tau>Move0 P h1 (e'', es'')"
    and ta: "ta_bisim01 ta' ta2" using heap by auto
  from red'' have "mred0 P ((e'', es''), h1) ta' ((e', es'), h2')" by auto
  moreover from red' have "red0_\<tau>mthr.silent_moves P ((ex1, exs1), h1) ((e'', es''), h1)"
    by(rule \<tau>Red0r_into_red0_\<tau>mthr_silent_moves)
  moreover from \<tau>' have "\<not> \<tau>MOVE0 P ((e'', es''), h1) ta' ((e', es'), h2')" by simp
  moreover from bisim' have "bisim_red0_Red1 ((e', es'), h2') ((ex2', exs2'), h2')"
    by(auto simp add: bisim_red0_Red1_def)
  ultimately
  show "\<exists>s1' s1'' ta1. red0_\<tau>mthr.silent_moves P s1 s1' \<and>
             mred0 P s1' ta1 s1'' \<and> \<not> \<tau>MOVE0 P s1' ta1 s1'' \<and>
             bisim_red0_Red1 s1'' s2' \<and> ta_bisim01 ta1 ta2"
    using ta unfolding s1 s2' by blast
next
  show "wfP ?\<mu>1" by auto
next
  have "wf (measure countInitBlock)" ..
  hence "wf (inv_image (measure countInitBlock) (\<lambda>(((e', xs'), exs'), h'). e'))" ..
  also have "inv_image (measure countInitBlock) (\<lambda>(((e', xs'), exs'), h'). e') = {(s2', s2). ?\<mu>2 s2' s2}"
    by(simp add: inv_image_def split_beta)
  finally show "wfP ?\<mu>2" by(simp add: wfP_def)
qed

subsection{*Preservation of well-formedness*}

text{* The compiler preserves well-formedness. Is less trivial than it
may appear. We start with two simple properties: preservation of
well-typedness *}

lemma length_compEs2 [simp]: "length (compEs1 Vs es) = length es"
by(induct es) simp_all

lemma assumes wf: "wf_prog wfmd P"
  shows compE1_pres_wt: "\<lbrakk> P,[Vs[\<mapsto>]Ts] \<turnstile> e :: U; size Ts = size Vs \<rbrakk> \<Longrightarrow> compP f P,Ts \<turnstile>1 compE1 Vs e :: U"
  and compEs1_pres_wt: "\<lbrakk> P,[Vs[\<mapsto>]Ts] \<turnstile> es [::] Us; size Ts = size Vs \<rbrakk> \<Longrightarrow> compP f P,Ts \<turnstile>1 compEs1 Vs es [::] Us"
proof(induct e and es arbitrary: Vs Ts U and Vs Ts Us)
  case Var thus ?case by(fastsimp simp:map_upds_apply_eq_Some split:split_if_asm)
next
  case LAss thus ?case by(fastsimp simp:map_upds_apply_eq_Some split:split_if_asm)
next
  case Call thus ?case by(fastsimp dest: sees_method_compP[where f = f])
next
  case Block thus ?case by(fastsimp simp:nth_append)
next
  case (Synchronized V exp1 exp2 Vs Ts U)
  note IH1 = `\<And>Vs Ts U. \<lbrakk>P,[Vs [\<mapsto>] Ts] \<turnstile> exp1 :: U;
    length Ts = length Vs\<rbrakk> \<Longrightarrow> compP f P,Ts \<turnstile>1 compE1 Vs exp1 :: U`
  note IH2 = `\<And>Vs Ts U. \<lbrakk>P,[Vs [\<mapsto>] Ts] \<turnstile> exp2 :: U; length Ts = length Vs\<rbrakk> \<Longrightarrow> compP f P,Ts \<turnstile>1 compE1 Vs exp2 :: U`
  note length = `length Ts = length Vs`
  from `P,[Vs [\<mapsto>] Ts] \<turnstile> sync\<^bsub>V\<^esub> (exp1) exp2 :: U`
  obtain U1 where wt1: "P,[Vs [\<mapsto>] Ts] \<turnstile> exp1 :: U1"
    and wt2: "P,[Vs [\<mapsto>] Ts] \<turnstile> exp2 :: U"
    and U1: "is_refT U1" "U1 \<noteq> NT"
    by(auto)
  from IH1[of Vs Ts U1] wt1 length
  have wt1': "compP f P,Ts \<turnstile>1 compE1 Vs exp1 :: U1" by simp
  from length fresh_var_fresh[of Vs] have "[Vs [\<mapsto>] Ts] \<subseteq>\<^sub>m [Vs @ [fresh_var Vs] [\<mapsto>] Ts @ [Class Object]]"
    by(auto simp add: map_le_def fun_upd_def)
  with wt2 have "P,[Vs@[fresh_var Vs] [\<mapsto>] Ts @ [Class Object]] \<turnstile> exp2 :: U"
    by(rule wt_env_mono)
  with length IH2[of "Vs@[fresh_var Vs]" "Ts @ [Class Object]" U]
  have "compP f P,Ts @ [Class Object] \<turnstile>1 compE1 (Vs @ [fresh_var Vs]) exp2 :: U" by simp
  with wt1' U1 show ?case by(auto)
next 
  case (TryCatch exp1 C V exp2)
  note IH1 = `\<And>Vs Ts U. \<lbrakk>P,[Vs [\<mapsto>] Ts] \<turnstile> exp1 :: U; length Ts = length Vs\<rbrakk> \<Longrightarrow> compP f P,Ts \<turnstile>1 compE1 Vs exp1 :: U`
  note IH2 = `\<And>Vs Ts U. \<lbrakk>P,[Vs [\<mapsto>] Ts] \<turnstile> exp2 :: U; length Ts = length Vs\<rbrakk> \<Longrightarrow> compP f P,Ts \<turnstile>1 compE1 Vs exp2 :: U`
  note length = `length Ts = length Vs`
  with `P,[Vs [\<mapsto>] Ts] \<turnstile> try exp1 catch(C V) exp2 :: U`
  have wt1: "P,[Vs [\<mapsto>] Ts] \<turnstile> exp1 :: U" and wt2: "P,[(Vs@[V]) [\<mapsto>] (Ts@[Class C])] \<turnstile> exp2 :: U"
    and C: "P \<turnstile> C \<preceq>\<^sup>* Throwable" by(auto simp add: nth_append)
  from wf have "is_class P Throwable"
    by(auto simp add: wf_prog_def wf_syscls_def is_class_def class_def map_of_SomeI)
  with C have "is_class P C" by(rule subcls_is_class1)
  with IH1[OF wt1 length] IH2[OF wt2] length show ?case by(auto)
qed(fastsimp)+


text{*\noindent and the correct block numbering: *}


text{* The main complication is preservation of definite assignment
@{term"\<D>"}. *}

lemma image_index: "A \<subseteq> set(xs@[x]) \<Longrightarrow> index (xs @ [x]) ` A =
  (if x \<in> A then insert (size xs) (index xs ` (A-{x})) else index xs ` A)"
(*<*)
apply(auto simp:image_def)
   apply(rule bexI)
    prefer 2 apply blast
   apply simp
  apply(rule ccontr)
  apply(erule_tac x=xa in ballE)
   prefer 2 apply blast
  apply(fastsimp simp add:neq_commute)
 apply(subgoal_tac "x \<noteq> xa")
  prefer 2 apply blast
 apply(fastsimp simp add:neq_commute)
apply(subgoal_tac "x \<noteq> xa")
 prefer 2 apply blast
apply(force)
done
(*>*)


lemma A_compE1_None[simp]: "\<A> e = None \<Longrightarrow> \<A> (compE1 Vs e) = None"
  and As_compEs1_None: "\<A>s es = None \<Longrightarrow> \<A>s (compEs1 Vs es) = None"
apply(induct e and es arbitrary: Vs and Vs)
apply(auto simp:hyperset_defs)
done

lemma A_compE1: "\<lbrakk> \<A> e = \<lfloor>A\<rfloor>; fv e \<subseteq> set Vs \<rbrakk> \<Longrightarrow> \<A> (compE1 Vs e) = \<lfloor>index Vs ` A\<rfloor>"
  and As_compEs1: "\<lbrakk> \<A>s es = \<lfloor>A\<rfloor>; fvs es \<subseteq> set Vs \<rbrakk> \<Longrightarrow> \<A>s (compEs1 Vs es) = \<lfloor>index Vs ` A\<rfloor>"
proof(induct e and es arbitrary: A Vs and A Vs)
  case (Block V' T vo e)
  hence "fv e \<subseteq> set (Vs@[V'])" by fastsimp
  moreover obtain B where "\<A> e = \<lfloor>B\<rfloor>"
    using Block.prems by(simp add: hyperset_defs)
  moreover from calculation have "B \<subseteq> set (Vs@[V'])" by(auto dest!:A_fv)
  ultimately show ?case using Block
    by(auto simp add: hyperset_defs image_index)
next
  case (Synchronized V exp1 exp2 A Vs)
  have IH1: "\<And>A Vs. \<lbrakk>\<A> exp1 = \<lfloor>A\<rfloor>; fv exp1 \<subseteq> set Vs\<rbrakk> \<Longrightarrow> \<A> (compE1 Vs exp1) = \<lfloor>index Vs ` A\<rfloor>" by fact
  have IH2: "\<And>A Vs. \<lbrakk>\<A> exp2 = \<lfloor>A\<rfloor>; fv exp2 \<subseteq> set Vs\<rbrakk> \<Longrightarrow> \<A> (compE1 Vs exp2) = \<lfloor>index Vs ` A\<rfloor>" by fact
  from `fv (sync\<^bsub>V\<^esub> (exp1) exp2) \<subseteq> set Vs` 
  have fv1: "fv exp1 \<subseteq> set Vs"
    and fv2: "fv exp2 \<subseteq> set Vs" by auto
  from `\<A> (sync\<^bsub>V\<^esub> (exp1) exp2) = \<lfloor>A\<rfloor>` have A: "\<A> exp1 \<squnion> \<A> exp2 = \<lfloor>A\<rfloor>" by(simp)
  then obtain A1 A2 where A1: "\<A> exp1 = \<lfloor>A1\<rfloor>" and A2: "\<A> exp2 = \<lfloor>A2\<rfloor>" by(auto simp add: hyperset_defs)
  from A2 fv2 have "A2 \<subseteq> set Vs" by(auto dest: A_fv del: subsetI)
  with fresh_var_fresh[of Vs] have "(fresh_var Vs) \<notin> A2" by(auto)
  from fv2 have "fv exp2 \<subseteq> set (Vs @ [fresh_var Vs])" by auto
  with IH2[OF A2, of "Vs @ [fresh_var Vs]"]
  have "\<A> (compE1 (Vs @ [fresh_var Vs]) exp2) = \<lfloor>index (Vs @ [fresh_var Vs]) ` A2\<rfloor>"
    by(auto)
  with IH1[OF A1 fv1] A[symmetric] `A2 \<subseteq> set Vs` `(fresh_var Vs) \<notin> A2` A1 A2 show ?case
    by(auto simp add: image_index)
next
  case (InSynchronized V a exp A Vs)
  have IH: "\<And>A Vs. \<lbrakk>\<A> exp = \<lfloor>A\<rfloor>; fv exp \<subseteq> set Vs\<rbrakk> \<Longrightarrow> \<A> (compE1 Vs exp) = \<lfloor>index Vs ` A\<rfloor>" by fact
  from `\<A> (insync\<^bsub>V\<^esub> (a) exp) = \<lfloor>A\<rfloor>` have A: "\<A> exp = \<lfloor>A\<rfloor>" by simp
  from `fv (insync\<^bsub>V\<^esub> (a) exp) \<subseteq> set Vs` have fv: "fv exp \<subseteq> set Vs" by simp
  from A fv have "A \<subseteq> set Vs" by(auto dest: A_fv del: subsetI)
  with fresh_var_fresh[of Vs] have "(fresh_var Vs) \<notin> A" by(auto)
  from fv IH[OF A, of "Vs @ [fresh_var Vs]"]
  have " \<A> (compE1 (Vs @ [fresh_var Vs]) exp) = \<lfloor>index (Vs @ [fresh_var Vs]) ` A\<rfloor>" by simp
  with `A \<subseteq> set Vs` `(fresh_var Vs) \<notin> A` show ?case by(simp add: image_index)
next
  case (TryCatch e1 C V' e2)
  hence fve2: "fv e2 \<subseteq> set (Vs@[V'])" by auto
  show ?case
  proof (cases "\<A> e1")
    assume A1: "\<A> e1 = None"
    then obtain A2 where A2: "\<A> e2 = \<lfloor>A2\<rfloor>" using TryCatch
      by(simp add:hyperset_defs)
    hence "A2 \<subseteq> set (Vs@[V'])" using TryCatch.prems A_fv[OF A2] by simp blast
    thus ?thesis using TryCatch fve2 A1 A2
      by(auto simp add:hyperset_defs image_index)
  next
    fix A1 assume A1: "\<A> e1 =  \<lfloor>A1\<rfloor>"
    show ?thesis
    proof (cases  "\<A> e2")
      assume A2: "\<A> e2 = None"
      then show ?case using TryCatch A1 by(simp add:hyperset_defs)
    next
      fix A2 assume A2: "\<A> e2 = \<lfloor>A2\<rfloor>"
      have "A1 \<subseteq> set Vs" using TryCatch.prems A_fv[OF A1] by simp blast
      moreover
      have "A2 \<subseteq> set (Vs@[V'])" using TryCatch.prems A_fv[OF A2] by simp blast
      ultimately show ?thesis using TryCatch A1 A2
	by(fastsimp simp add: hyperset_defs image_index
	  Diff_subset_conv inj_on_image_Int[OF inj_on_index])
    qed
  qed
next
  case (Cond e e1 e2)
  { assume "\<A> e = None \<or> \<A> e1 = None \<or> \<A> e2 = None"
    hence ?case using Cond by(auto simp add:hyperset_defs image_Un)
  }
  moreover
  { fix A A1 A2
    assume "\<A> e = \<lfloor>A\<rfloor>" and A1: "\<A> e1 = \<lfloor>A1\<rfloor>" and A2: "\<A> e2 = \<lfloor>A2\<rfloor>"
    moreover
    have "A1 \<subseteq> set Vs" using Cond.prems A_fv[OF A1] by simp blast
    moreover
    have "A2 \<subseteq> set Vs" using Cond.prems A_fv[OF A2] by simp blast
    ultimately have ?case using Cond
      by(auto simp add:hyperset_defs image_Un
	  inj_on_image_Int[OF inj_on_index])
  }
  ultimately show ?case by fastsimp
qed (auto simp add:hyperset_defs)

lemma  fixes e :: "('a,'b) exp" and es :: "('a,'b) exp list"
  shows D_None [iff]: "\<D> e None"
  and Ds_None [iff]: "\<D>s es None"
by(induct e and es)(simp_all)

lemma D_index_compE1: "\<lbrakk> A \<subseteq> set Vs; fv e \<subseteq> set Vs \<rbrakk> \<Longrightarrow> \<D> e \<lfloor>A\<rfloor> \<Longrightarrow> \<D> (compE1 Vs e) \<lfloor>index Vs ` A\<rfloor>"
  and Ds_index_compEs1: "\<lbrakk> A \<subseteq> set Vs; fvs es \<subseteq> set Vs \<rbrakk> \<Longrightarrow> \<D>s es \<lfloor>A\<rfloor> \<Longrightarrow> \<D>s (compEs1 Vs es) \<lfloor>index Vs ` A\<rfloor>"
proof(induct e and es arbitrary: A Vs and A Vs)
  case (BinOp e1 bop e2)
  hence IH1: "\<D> (compE1 Vs e1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e1")
    case None thus ?thesis using BinOp by simp
  next
    case (Some A1)
    have indexA1: "\<A> (compE1 Vs e1) = \<lfloor>index Vs ` A1\<rfloor>"
      using A_compE1[OF Some] BinOp.prems  by auto
    have "A \<union> A1 \<subseteq> set Vs" using BinOp.prems A_fv[OF Some] by auto
    hence "\<D> (compE1 Vs e2) \<lfloor>index Vs ` (A \<union> A1)\<rfloor>" using BinOp Some by auto
    hence "\<D> (compE1 Vs e2) \<lfloor>index Vs ` A \<union> index Vs ` A1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH1 indexA1 by auto
  qed
next
  case (AAcc a i A Vs)
  have IH1: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv a \<subseteq> set Vs; \<D> a \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs a) \<lfloor>index Vs ` A\<rfloor>" by fact
  have IH2: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv i \<subseteq> set Vs; \<D> i \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs i) \<lfloor>index Vs ` A\<rfloor>" by fact
  from `\<D> (a\<lfloor>i\<rceil>) \<lfloor>A\<rfloor>` have D1: "\<D> a \<lfloor>A\<rfloor>" and D2: "\<D> i (\<lfloor>A\<rfloor> \<squnion> \<A> a)" by auto
  from `fv (a\<lfloor>i\<rceil>) \<subseteq> set Vs` have fv1: "fv a \<subseteq> set Vs" and fv2: "fv i \<subseteq> set Vs" by auto
  show ?case
  proof(cases "\<A> a")
    case None thus ?thesis using AAcc by simp
  next
    case (Some A1)
    with fv1 have "\<A> (compE1 Vs a) = \<lfloor>index Vs ` A1\<rfloor>" by-(rule A_compE1)
    moreover from A_fv[OF Some] fv1 `A \<subseteq> set Vs` have "A \<union> A1 \<subseteq> set Vs" by auto
    from IH2[OF this fv2] Some D2 have "\<D> (compE1 Vs i) \<lfloor>index Vs ` A \<union> index Vs ` A1\<rfloor>"
      by(simp add: image_Un)
    ultimately show ?thesis using IH1[OF `A \<subseteq> set Vs` fv1 D1] by(simp)
  qed
next
  case (AAss a i e A Vs)
  have IH1: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv a \<subseteq> set Vs; \<D> a \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs a) \<lfloor>index Vs ` A\<rfloor>" by fact
  have IH2: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv i \<subseteq> set Vs; \<D> i \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs i) \<lfloor>index Vs ` A\<rfloor>" by fact
  have IH3: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv e \<subseteq> set Vs; \<D> e \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs e) \<lfloor>index Vs ` A\<rfloor>" by fact
  from `\<D> (a\<lfloor>i\<rceil>:=e) \<lfloor>A\<rfloor>` have D1: "\<D> a \<lfloor>A\<rfloor>" and D2: "\<D> i (\<lfloor>A\<rfloor> \<squnion> \<A> a)" 
    and D3: "\<D> e (\<lfloor>A\<rfloor> \<squnion> \<A> a \<squnion> \<A> i)" by auto
  from `fv (a\<lfloor>i\<rceil> := e) \<subseteq> set Vs`
  have fv1: "fv a \<subseteq> set Vs" and fv2: "fv i \<subseteq> set Vs" and fv3: "fv e \<subseteq> set Vs" by auto
  show ?case
  proof(cases "\<A> a")
    case None thus ?thesis using AAss by simp
  next
    case (Some A1)
    with fv1 have A1: "\<A> (compE1 Vs a) = \<lfloor>index Vs ` A1\<rfloor>" by-(rule A_compE1)
    from A_fv[OF Some] fv1 `A \<subseteq> set Vs` have "A \<union> A1 \<subseteq> set Vs" by auto
    from IH2[OF this fv2] Some D2 have D2': "\<D> (compE1 Vs i) \<lfloor>index Vs ` A \<union> index Vs ` A1\<rfloor>"
      by(simp add: image_Un)
    show ?thesis
    proof(cases "\<A> i")
      case None thus ?thesis using AAss D2' Some A1 by simp
    next
      case (Some A2)
      with fv2 have A2: "\<A> (compE1 Vs i) = \<lfloor>index Vs ` A2\<rfloor>" by-(rule A_compE1)
      moreover from A_fv[OF Some] fv2 `A \<union> A1 \<subseteq> set Vs` have "A \<union> A1 \<union> A2 \<subseteq> set Vs" by auto
      from IH3[OF this fv3] Some `\<A> a = \<lfloor>A1\<rfloor>` D3
      have "\<D> (compE1 Vs e) \<lfloor>index Vs ` A \<union> index Vs ` A1 \<union> index Vs ` A2\<rfloor>" by(simp add: image_Un)
      ultimately show ?thesis using IH1[OF `A \<subseteq> set Vs` fv1 D1] D2' A1 A2 by(simp)
    qed
  qed
next
  case (FAss e1 F D e2)
  hence IH1: "\<D> (compE1 Vs e1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e1")
    case None thus ?thesis using FAss by simp
  next
    case (Some A1)
    have indexA1: "\<A> (compE1 Vs e1) = \<lfloor>index Vs ` A1\<rfloor>"
      using A_compE1[OF Some] FAss.prems  by auto
    have "A \<union> A1 \<subseteq> set Vs" using FAss.prems A_fv[OF Some] by auto
    hence "\<D> (compE1 Vs e2) \<lfloor>index Vs ` (A \<union> A1)\<rfloor>" using FAss Some by auto
    hence "\<D> (compE1 Vs e2) \<lfloor>index Vs ` A \<union> index Vs ` A1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH1 indexA1 by auto
  qed
next
  case (Call e1 M es)
  hence IH1: "\<D> (compE1 Vs e1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e1")
    case None thus ?thesis using Call by simp
  next
    case (Some A1)
    have indexA1: "\<A> (compE1 Vs e1) = \<lfloor>index Vs ` A1\<rfloor>"
      using A_compE1[OF Some] Call.prems  by auto
    have "A \<union> A1 \<subseteq> set Vs" using Call.prems A_fv[OF Some] by auto
    hence "\<D>s (compEs1 Vs es) \<lfloor>index Vs ` (A \<union> A1)\<rfloor>" using Call Some by auto
    hence "\<D>s (compEs1 Vs es) \<lfloor>index Vs ` A \<union> index Vs ` A1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH1 indexA1 by auto
  qed
next
  case (Synchronized V exp1 exp2 A Vs)
  have IH1: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv exp1 \<subseteq> set Vs; \<D> exp1 \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs exp1) \<lfloor>index Vs ` A\<rfloor>" by fact
  have IH2: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv exp2 \<subseteq> set Vs; \<D> exp2 \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs exp2) \<lfloor>index Vs ` A\<rfloor>" by fact
  from `\<D> (sync\<^bsub>V\<^esub> (exp1) exp2) \<lfloor>A\<rfloor>` have D1: "\<D> exp1 \<lfloor>A\<rfloor>" and D2: "\<D> exp2 (\<lfloor>A\<rfloor> \<squnion> \<A> exp1)" by auto
  from `fv (sync\<^bsub>V\<^esub> (exp1) exp2) \<subseteq> set Vs` have fv1: "fv exp1 \<subseteq> set Vs" and fv2: "fv exp2 \<subseteq> set Vs" by auto
  show ?case
  proof(cases "\<A> exp1")
    case None thus ?thesis using Synchronized by(simp)
  next
    case (Some A1)
    with fv1 have A1: "\<A> (compE1 Vs exp1) = \<lfloor>index Vs ` A1\<rfloor>" by-(rule A_compE1)
    from A_fv[OF Some] fv1 `A \<subseteq> set Vs` have "A \<union> A1 \<subseteq> set Vs" by auto
    hence "A \<union> A1 \<subseteq> set (Vs @ [fresh_var Vs])" by simp
    from IH2[OF this] fv2 Some D2
    have D2': "\<D> (compE1 (Vs @ [fresh_var Vs]) exp2) \<lfloor>index (Vs @ [fresh_var Vs]) ` (A \<union> A1)\<rfloor>"
      by(simp)
    moreover from fresh_var_fresh[of Vs] `A \<union> A1 \<subseteq> set Vs`
    have "(fresh_var Vs) \<notin> A \<union> A1" by auto
    with `A \<union> A1 \<subseteq> set Vs`
    have "index (Vs @ [fresh_var Vs]) ` (A \<union> A1) = index Vs ` A \<union> index Vs ` A1"
      by(simp add: image_index image_Un)
    ultimately show ?thesis using IH1[OF `A \<subseteq> set Vs` fv1 D1] D2' A1 by(simp)
  qed
next
  case (InSynchronized V a e A Vs)
  have IH: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv e \<subseteq> set Vs; \<D> e \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs e) \<lfloor>index Vs ` A\<rfloor>" by fact
  from IH[of A "Vs @ [fresh_var Vs]"] `A \<subseteq> set Vs` `fv (insync\<^bsub>V\<^esub> (a) e) \<subseteq> set Vs` `\<D> (insync\<^bsub>V\<^esub> (a) e) \<lfloor>A\<rfloor>`
  have "\<D> (compE1 (Vs @ [fresh_var Vs]) e) \<lfloor>index (Vs @ [fresh_var Vs]) ` A\<rfloor>" by(auto)
  moreover from fresh_var_fresh[of Vs] `A \<subseteq> set Vs` have "(fresh_var Vs) \<notin> A" by auto
  with `A \<subseteq> set Vs` have "index (Vs @ [fresh_var Vs]) ` A = index Vs ` A" by(simp add: image_index)
  ultimately show ?case by(simp)
next
  case (TryCatch e1 C V e2)
  have "\<lbrakk> A\<union>{V} \<subseteq> set(Vs@[V]); fv e2 \<subseteq> set(Vs@[V]); \<D> e2 \<lfloor>A\<union>{V}\<rfloor>\<rbrakk> \<Longrightarrow>
        \<D> (compE1 (Vs@[V]) e2) \<lfloor>index (Vs@[V]) ` (A\<union>{V})\<rfloor>" by fact
  hence "\<D> (compE1 (Vs@[V]) e2) \<lfloor>index (Vs@[V]) ` (A\<union>{V})\<rfloor>"
    using TryCatch.prems by(simp add:Diff_subset_conv)
  moreover have "index (Vs@[V]) ` A \<subseteq> index Vs ` A \<union> {size Vs}"
    using TryCatch.prems by(auto simp add: image_index split:split_if_asm)
  ultimately show ?case using TryCatch by(auto simp:hyperset_defs elim!:D_mono')
next
  case (Seq e1 e2)
  hence IH1: "\<D> (compE1 Vs e1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e1")
    case None thus ?thesis using Seq by simp
  next
    case (Some A1)
    have indexA1: "\<A> (compE1 Vs e1) = \<lfloor>index Vs ` A1\<rfloor>"
      using A_compE1[OF Some] Seq.prems  by auto
    have "A \<union> A1 \<subseteq> set Vs" using Seq.prems A_fv[OF Some] by auto
    hence "\<D> (compE1 Vs e2) \<lfloor>index Vs ` (A \<union> A1)\<rfloor>" using Seq Some by auto
    hence "\<D> (compE1 Vs e2) \<lfloor>index Vs ` A \<union> index Vs ` A1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH1 indexA1 by auto
  qed
next
  case (Cond e e1 e2)
  hence IH1: "\<D> (compE1 Vs e) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e")
    case None thus ?thesis using Cond by simp
  next
    case (Some B)
    have indexB: "\<A> (compE1 Vs e) = \<lfloor>index Vs ` B\<rfloor>"
      using A_compE1[OF Some] Cond.prems  by auto
    have "A \<union> B \<subseteq> set Vs" using Cond.prems A_fv[OF Some] by auto
    hence "\<D> (compE1 Vs e1) \<lfloor>index Vs ` (A \<union> B)\<rfloor>"
      and "\<D> (compE1 Vs e2) \<lfloor>index Vs ` (A \<union> B)\<rfloor>"
      using Cond Some by auto
    hence "\<D> (compE1 Vs e1) \<lfloor>index Vs ` A \<union> index Vs ` B\<rfloor>"
      and "\<D> (compE1 Vs e2) \<lfloor>index Vs ` A \<union> index Vs ` B\<rfloor>"
      by(simp add: image_Un)+
    thus ?thesis using IH1 indexB by auto
  qed
next
  case (While e1 e2)
  hence IH1: "\<D> (compE1 Vs e1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e1")
    case None thus ?thesis using While by simp
  next
    case (Some A1)
    have indexA1: "\<A> (compE1 Vs e1) = \<lfloor>index Vs ` A1\<rfloor>"
      using A_compE1[OF Some] While.prems  by auto
    have "A \<union> A1 \<subseteq> set Vs" using While.prems A_fv[OF Some] by auto
    hence "\<D> (compE1 Vs e2) \<lfloor>index Vs ` (A \<union> A1)\<rfloor>" using While Some by auto
    hence "\<D> (compE1 Vs e2) \<lfloor>index Vs ` A \<union> index Vs ` A1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH1 indexA1 by auto
  qed
next
  case (Block V T vo e A Vs)
  have IH: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv e \<subseteq> set Vs; \<D> e \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs e) \<lfloor>index Vs ` A\<rfloor>" by fact
  from `fv {V:T=vo; e} \<subseteq> set Vs` have fv: "fv e \<subseteq> set (Vs @ [V])" by auto
  show ?case
  proof(cases vo)
    case None
    with `\<D> {V:T=vo; e} \<lfloor>A\<rfloor>` have D: "\<D> e \<lfloor>A - {V}\<rfloor>" by(auto)
    from `A \<subseteq> set Vs` have "A - {V} \<subseteq> set (Vs @ [V])" by auto
    from IH[OF this fv D] have "\<D> (compE1 (Vs @ [V]) e) \<lfloor>index (Vs @ [V]) ` (A - {V})\<rfloor>" .
    moreover from `A \<subseteq> set Vs` have size: "size Vs \<notin> index Vs ` A" by(auto simp add: image_def)
    hence "\<lfloor>index Vs ` (A - {V})\<rfloor> \<sqsubseteq> \<lfloor>index Vs ` A\<rfloor>" by(auto simp add: hyperset_defs)
    ultimately have "\<D> (compE1 (Vs @ [V]) e) \<lfloor>index Vs ` A\<rfloor>" using `A - {V} \<subseteq> set (Vs @ [V])`
      by(simp add: image_index)(erule D_mono', auto)
    thus ?thesis using None size by(simp)
  next
    case (Some v)
    with `\<D> {V:T=vo; e} \<lfloor>A\<rfloor>` have D: "\<D> e \<lfloor>insert V A\<rfloor>" by(auto)
    from `A \<subseteq> set Vs` have "insert V A \<subseteq> set (Vs @ [V])" by auto
    from IH[OF this fv D] have "\<D> (compE1 (Vs @ [V]) e) \<lfloor>index (Vs @ [V]) ` insert V A\<rfloor>" by simp
    moreover from `A \<subseteq> set Vs` have "index (Vs @ [V]) ` insert V A \<subseteq> insert (length Vs) (index Vs ` A)"
      by(auto simp add: image_index)
    ultimately show ?thesis using Some by(auto elim!: D_mono' simp add: hyperset_defs)
  qed
next
  case (Cons_exp e1 es)
  hence IH1: "\<D> (compE1 Vs e1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e1")
    case None thus ?thesis using Cons_exp by simp
  next
    case (Some A1)
    have indexA1: "\<A> (compE1 Vs e1) = \<lfloor>index Vs ` A1\<rfloor>"
      using A_compE1[OF Some] Cons_exp.prems  by auto
    have "A \<union> A1 \<subseteq> set Vs" using Cons_exp.prems A_fv[OF Some] by auto
    hence "\<D>s (compEs1 Vs es) \<lfloor>index Vs ` (A \<union> A1)\<rfloor>" using Cons_exp Some by auto
    hence "\<D>s (compEs1 Vs es) \<lfloor>index Vs ` A \<union> index Vs ` A1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH1 indexA1 by auto
  qed
qed (simp_all add:hyperset_defs)

lemma index_image_set: "distinct xs \<Longrightarrow> index xs ` set xs = {..<size xs}"
by(induct xs rule:rev_induct) (auto simp add: image_index)

lemma D_compE1:
  "\<lbrakk> \<D> e \<lfloor>set Vs\<rfloor>; fv e \<subseteq> set Vs; distinct Vs \<rbrakk> \<Longrightarrow> \<D> (compE1 Vs e) \<lfloor>{..<length Vs}\<rfloor>"
by(fastsimp dest!: D_index_compE1[OF subset_refl] simp add:index_image_set)

lemma D_compE1':
  assumes "\<D> e \<lfloor>set(V#Vs)\<rfloor>" and "fv e \<subseteq> set(V#Vs)" and "distinct(V#Vs)"
  shows "\<D> (compE1 (V#Vs) e) \<lfloor>{..length Vs}\<rfloor>"
proof -
  have "{..size Vs} = {..<size(V#Vs)}" by auto
  thus ?thesis using prems by (simp only:)(rule D_compE1)
qed

lemma fv_compE1: "fv e \<subseteq> set Vs \<Longrightarrow> fv (compE1 Vs e) = (index Vs) ` (fv e)"
  and fvs_compEs1: "fvs es \<subseteq> set Vs \<Longrightarrow> fvs (compEs1 Vs es) = (index Vs) ` (fvs es)"
proof(induct e and es arbitrary: Vs and Vs)
  case (Block V ty vo exp)
  have IH: "\<And>Vs. fv exp \<subseteq> set Vs \<Longrightarrow> fv (compE1 Vs exp) = index Vs ` fv exp" by fact
  from `fv {V:ty=vo; exp} \<subseteq> set Vs` have fv': "fv exp \<subseteq> set (Vs @ [V])" by auto
  from IH[OF this] have IH': "fv (compE1 (Vs @ [V]) exp) = index (Vs @ [V]) ` fv exp" .
  have "fv (compE1 (Vs @ [V]) exp) - {length Vs} = index Vs ` (fv exp - {V})"
  proof(rule equalityI[OF subsetI subsetI])
    fix x
    assume x: "x \<in> fv (compE1 (Vs @ [V]) exp) - {length Vs}"
    hence "x \<noteq> length Vs" by simp
    from x IH' have "x \<in> index (Vs @ [V]) ` fv exp" by simp
    thus "x \<in> index Vs ` (fv exp - {V})"
    proof(rule imageE)
      fix y
      assume [simp]: "x = index (Vs @ [V]) y"
	and y: "y \<in> fv exp"
      have "y \<noteq> V"
      proof
	assume [simp]: "y = V"
	hence "x = length Vs" by simp
	with `x \<noteq> length Vs` show False by contradiction
      qed
      moreover with fv' y have "y \<in> set Vs" by auto
      ultimately have "index (Vs @ [V]) y = index Vs y" by(simp)
      thus ?thesis using y `y \<noteq> V` by auto
    qed
  next
    fix x
    assume x: "x \<in> index Vs ` (fv exp - {V})"
    thus "x \<in> fv (compE1 (Vs @ [V]) exp) - {length Vs}"
    proof(rule imageE)
      fix y
      assume [simp]: "x = index Vs y"
	and y: "y \<in> fv exp - {V}"
      with fv' have "y \<in> set Vs" "y \<noteq> V" by auto
      hence "index Vs y = index (Vs @ [V]) y" by simp
      with y have "x \<in> index (Vs @ [V]) ` fv exp" by auto
      thus ?thesis using IH' `y \<in> set Vs` by simp
    qed
  qed
  thus ?case by simp
next
  case (Synchronized V exp1 exp2)
  have IH1: "\<And>Vs. fv exp1 \<subseteq> set Vs \<Longrightarrow> fv (compE1 Vs exp1) = index Vs ` fv exp1" 
    and IH2: "\<And>Vs. fv exp2 \<subseteq> set Vs \<Longrightarrow> fv (compE1 Vs exp2) = index Vs ` fv exp2" by fact+
  from `fv (sync\<^bsub>V\<^esub> (exp1) exp2) \<subseteq> set Vs` have fv1: "fv exp1 \<subseteq> set Vs"
    and fv2: "fv exp2 \<subseteq> set Vs" by auto
  from fv2 have fv2': "fv exp2 \<subseteq> set (Vs @ [fresh_var Vs])" by auto
  have "index (Vs @ [fresh_var Vs]) ` fv exp2 = index Vs ` fv exp2"
  proof(rule equalityI[OF subsetI subsetI])
    fix x
    assume x: "x \<in> index (Vs @ [fresh_var Vs]) ` fv exp2"
    thus "x \<in> index Vs ` fv exp2"
    proof(rule imageE)
      fix y
      assume [simp]: "x = index (Vs @ [fresh_var Vs]) y"
	and y: "y \<in> fv exp2"
      from y fv2 have "y \<in> set Vs" by auto
      moreover hence "y \<noteq> (fresh_var Vs)" by(auto simp add: fresh_var_fresh)
      ultimately show ?thesis using y by(auto)
    qed
  next
    fix x
    assume x: "x \<in> index Vs ` fv exp2"
    thus "x \<in> index (Vs @ [fresh_var Vs]) ` fv exp2"
    proof(rule imageE)
      fix y
      assume [simp]: "x = index Vs y"
	and y: "y \<in> fv exp2"
      from y fv2 have "y \<in> set Vs" by auto
      moreover hence "y \<noteq> (fresh_var Vs)" by(auto simp add: fresh_var_fresh)
      ultimately have "index Vs y = index (Vs @ [fresh_var Vs]) y" by simp
      thus ?thesis using y by(auto)
    qed
  qed
  with IH1[OF fv1] IH2[OF fv2'] show ?case by(auto)
next
  case (InSynchronized V a exp)
  have IH: "\<And>Vs. fv exp \<subseteq> set Vs \<Longrightarrow> fv (compE1 Vs exp) = index Vs ` fv exp" by fact
  from `fv (insync\<^bsub>V\<^esub> (a) exp) \<subseteq> set Vs` have fv: "fv exp \<subseteq> set Vs" by simp
  hence fv': "fv exp \<subseteq> set (Vs @ [fresh_var Vs])" by auto
  have "index (Vs @ [fresh_var Vs]) ` fv exp = index Vs ` fv exp"
  proof(rule equalityI[OF subsetI subsetI])
    fix x
    assume "x \<in> index (Vs @ [fresh_var Vs]) ` fv exp"
    thus "x \<in> index Vs ` fv exp"
    proof(rule imageE)
      fix y
      assume [simp]: "x = index (Vs @ [fresh_var Vs]) y"
	and y: "y \<in> fv exp"
      from y fv have "y \<in> set Vs" by auto
      moreover hence "y \<noteq> (fresh_var Vs)" by(auto simp add: fresh_var_fresh)
      ultimately have "index (Vs @ [fresh_var Vs]) y = index Vs y" by simp
      thus ?thesis using y by simp
    qed
  next
    fix x
    assume "x \<in> index Vs ` fv exp"
    thus "x \<in> index (Vs @ [fresh_var Vs]) ` fv exp"
    proof(rule imageE)
      fix y
      assume [simp]: "x = index Vs y"
	and y: "y \<in> fv exp"
      from y fv have "y \<in> set Vs" by auto
      moreover hence "y \<noteq> (fresh_var Vs)" by(auto simp add: fresh_var_fresh)
      ultimately have "index Vs y = index (Vs @ [fresh_var Vs]) y" by simp
      thus ?thesis using y by auto
    qed
  qed
  with IH[OF fv'] show ?case by simp
next
  case (TryCatch exp1 C V exp2)
  have IH1: "\<And>Vs. fv exp1 \<subseteq> set Vs \<Longrightarrow> fv (compE1 Vs exp1) = index Vs ` fv exp1" 
    and IH2: "\<And>Vs. fv exp2 \<subseteq> set Vs \<Longrightarrow> fv (compE1 Vs exp2) = index Vs ` fv exp2" by fact+
  from `fv (try exp1 catch(C V) exp2) \<subseteq> set Vs` have fv1: "fv exp1 \<subseteq> set Vs"
    and fv2: "fv exp2 \<subseteq> set (Vs @ [V])" by auto
  have "index (Vs @ [V]) ` fv exp2 - {length Vs} = index Vs ` (fv exp2 - {V})" 
  proof(rule equalityI[OF subsetI subsetI])
    fix x
    assume x: "x \<in> index (Vs @ [V]) ` fv exp2 - {length Vs}"
    hence "x \<noteq> length Vs" by simp
    from x have "x \<in> index (Vs @ [V]) ` fv exp2" by auto
    thus "x \<in> index Vs ` (fv exp2 - {V})"
    proof(rule imageE)
      fix y
      assume [simp]: "x = index (Vs @ [V]) y"
	and y: "y \<in> fv exp2"
      have "y \<noteq> V"
      proof
	assume [simp]: "y = V"
	hence "x = length Vs" by simp
	with `x \<noteq> length Vs` show False by contradiction
      qed
      moreover with fv2 y have "y \<in> set Vs" by auto
      ultimately have "index (Vs @ [V]) y = index Vs y" by(simp)
      thus ?thesis using y `y \<noteq> V` by auto
    qed
  next
    fix x
    assume x: "x \<in> index Vs ` (fv exp2 - {V})"
    thus "x \<in> index (Vs @ [V]) ` fv exp2 - {length Vs}"
    proof(rule imageE)
      fix y
      assume [simp]: "x = index Vs y"
	and y: "y \<in> fv exp2 - {V}"
      with fv2 have "y \<in> set Vs" "y \<noteq> V" by auto
      hence "index Vs y = index (Vs @ [V]) y" by simp
      with y have "x \<in> index (Vs @ [V]) ` fv exp2" by auto
      thus ?thesis using `y \<in> set Vs` by simp
    qed
  qed
  with IH1[OF fv1] IH2[OF fv2] show ?case by auto
qed(auto)
  
  
lemma syncvars_compE1: "fv e \<subseteq> set Vs \<Longrightarrow> syncvars (compE1 Vs e)"
  and syncvarss_compEs1: "fvs es \<subseteq> set Vs \<Longrightarrow> syncvarss (compEs1 Vs es)"
proof(induct e and es arbitrary: Vs and Vs)
  case (Block V ty vo exp)
  from `fv {V:ty=vo; exp} \<subseteq> set Vs` have "fv exp \<subseteq> set (Vs @ [V])" by auto
  from `\<And>Vs. fv exp \<subseteq> set Vs \<Longrightarrow> syncvars (compE1 Vs exp)`[OF this] show ?case by(simp)
next
  case (Synchronized V exp1 exp2)
  note IH1 = `\<And>Vs. fv exp1 \<subseteq> set Vs \<Longrightarrow> syncvars (compE1 Vs exp1)`
  note IH2 = `\<And>Vs. fv exp2 \<subseteq> set Vs \<Longrightarrow> syncvars (compE1 Vs exp2)`
  from `fv (sync\<^bsub>V\<^esub> (exp1) exp2) \<subseteq> set Vs` have fv1: "fv exp1 \<subseteq> set Vs"
    and fv2: "fv exp2 \<subseteq> set Vs" and fv2': "fv exp2 \<subseteq> set (Vs @ [fresh_var Vs])" by auto
  have "length Vs \<notin> index (Vs @ [fresh_var Vs]) ` fv exp2"
  proof
    assume "length Vs \<in> index (Vs @ [fresh_var Vs]) ` fv exp2"
    thus False
    proof(rule imageE)
      fix x
      assume x: "length Vs = index (Vs @ [fresh_var Vs]) x"
	and x': "x \<in> fv exp2"
      from x' fv2 have "x \<in> set Vs" "x \<noteq> (fresh_var Vs)" by(auto simp add: fresh_var_fresh)
      with x show ?thesis by(simp)
    qed
  qed
  with IH1[OF fv1] IH2[OF fv2'] fv2' show ?case by(simp add: fv_compE1)
next
  case (InSynchronized V a exp)
  note IH = `\<And>Vs. fv exp \<subseteq> set Vs \<Longrightarrow> syncvars (compE1 Vs exp)`
  from `fv (insync\<^bsub>V\<^esub> (a) exp) \<subseteq> set Vs` have fv: "fv exp \<subseteq> set Vs"
    and fv': "fv exp \<subseteq> set (Vs @ [fresh_var Vs])" by auto
  have "length Vs \<notin> index (Vs @ [fresh_var Vs]) ` fv exp"
  proof
    assume "length Vs \<in> index (Vs @ [fresh_var Vs]) ` fv exp"
    thus False
    proof(rule imageE)
      fix x
      assume x: "length Vs = index (Vs @ [fresh_var Vs]) x"
	and x': "x \<in> fv exp"
      from x' fv have "x \<in> set Vs" "x \<noteq> (fresh_var Vs)" by(auto simp add: fresh_var_fresh)
      with x show ?thesis by(simp)
    qed
  qed
  with IH[OF fv'] fv' show ?case by(simp add: fv_compE1)
next
  case (TryCatch exp1 C V exp2)
  note IH1 = `\<And>Vs. fv exp1 \<subseteq> set Vs \<Longrightarrow> syncvars (compE1 Vs exp1)`
  note IH2 = `\<And>Vs. fv exp2 \<subseteq> set Vs \<Longrightarrow> syncvars (compE1 Vs exp2)`
  from `fv (try exp1 catch(C V) exp2) \<subseteq> set Vs` have fv1: "fv exp1 \<subseteq> set Vs"
    and fv2: "fv exp2 \<subseteq> set (Vs @ [V])" by auto
  from IH1[OF fv1] IH2[OF fv2] show ?case by auto
qed auto

lemma compP1_pres_wf: "wf_J_prog P \<Longrightarrow> wf_J1_prog (compP1 P)"
apply simp
apply(rule wf_prog_compPI)
 prefer 2 apply assumption
apply(case_tac m)
apply(simp add:wf_mdecl_def wf_J1_mdecl_def wf_J_mdecl)
apply(clarify)
apply(frule WT_fv)
apply(fastsimp intro!: compE1_pres_wt D_compE1' \<B> syncvars_compE1)
done

end

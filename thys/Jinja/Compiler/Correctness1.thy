(*  Title:      Jinja/Compiler/Correctness1.thy
    ID:         $Id: Correctness1.thy,v 1.7 2007-08-12 16:28:15 makarius Exp $
    Author:     Tobias Nipkow
    Copyright   TUM 2003
*)

header {* \isaheader{Correctness of Stage 1} *}

theory Correctness1
imports J1WellForm Compiler1
begin

section{*Correctness of program compilation *}

consts
  unmod :: "expr\<^isub>1 \<Rightarrow> nat \<Rightarrow> bool"
  unmods :: "expr\<^isub>1 list \<Rightarrow> nat \<Rightarrow> bool"
primrec
"unmod (new C) i = True"
"unmod (Cast C e) i = unmod e i"
"unmod (Val v) i = True"
"unmod (e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) i = (unmod e\<^isub>1 i \<and> unmod e\<^isub>2 i)"
"unmod (Var i) j = True"
"unmod (i:=e) j = (i \<noteq> j \<and> unmod e j)"
"unmod (e\<bullet>F{D}) i = unmod e i"
"unmod (e\<^isub>1\<bullet>F{D}:=e\<^isub>2) i = (unmod e\<^isub>1 i \<and> unmod e\<^isub>2 i)"
"unmod (e\<bullet>M(es)) i = (unmod e i \<and> unmods es i)"
"unmod {j:T; e} i = unmod e i"
"unmod (e\<^isub>1;;e\<^isub>2) i = (unmod e\<^isub>1 i \<and>  unmod e\<^isub>2 i)"
"unmod (if (e) e\<^isub>1 else e\<^isub>2) i = (unmod e i \<and> unmod e\<^isub>1 i \<and> unmod e\<^isub>2 i)"
"unmod (while (e) c) i = (unmod e i \<and> unmod c i)"
"unmod (throw e) i = unmod e i"
"unmod (try e\<^isub>1 catch(C i) e\<^isub>2) j = (unmod e\<^isub>1 j \<and> (if i=j then False else unmod e\<^isub>2 j))"

"unmods ([]) i = True"
"unmods (e#es) i = (unmod e i \<and> unmods es i)"

lemma hidden_unmod: "\<And>Vs. hidden Vs i \<Longrightarrow> unmod (compE\<^isub>1 Vs e) i" and
 "\<And>Vs. hidden Vs i \<Longrightarrow> unmods (compEs\<^isub>1 Vs es) i"
(*<*)
apply(induct e and es)
apply (simp_all add:hidden_inacc)
apply(auto simp add:hidden_def)
done
(*>*)


lemma eval\<^isub>1_preserves_unmod:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,(h,ls)\<rangle> \<Rightarrow> \<langle>e',(h',ls')\<rangle>; unmod e i; i < size ls \<rbrakk>
  \<Longrightarrow> ls ! i = ls' ! i"
and "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>es,(h,ls)\<rangle> [\<Rightarrow>] \<langle>es',(h',ls')\<rangle>; unmods es i; i < size ls \<rbrakk>
      \<Longrightarrow> ls ! i = ls' ! i"
(*<*)
apply(induct rule:eval\<^isub>1_evals\<^isub>1_inducts)
apply(auto dest!:eval\<^isub>1_preserves_len split:split_if_asm)
done
(*>*)


lemma LAss_lem:
  "\<lbrakk>x \<in> set xs; size xs \<le> size ys \<rbrakk>
  \<Longrightarrow> m\<^isub>1 \<subseteq>\<^sub>m m\<^isub>2(xs[\<mapsto>]ys) \<Longrightarrow> m\<^isub>1(x\<mapsto>y) \<subseteq>\<^sub>m m\<^isub>2(xs[\<mapsto>]ys[index xs x := y])"
(*<*)
apply(simp add:map_le_def);
apply(simp add:fun_upds_apply index_less_aux eq_sym_conv)
done
(*>*)
lemma Block_lem:
fixes l :: "'a \<rightharpoonup> 'b"
assumes 0: "l \<subseteq>\<^sub>m [Vs [\<mapsto>] ls]"
    and 1: "l' \<subseteq>\<^sub>m [Vs [\<mapsto>] ls', V\<mapsto>v]"
    and hidden: "V \<in> set Vs \<Longrightarrow> ls ! index Vs V = ls' ! index Vs V"
    and size: "size ls = size ls'"    "size Vs < size ls'"
shows "l'(V := l V) \<subseteq>\<^sub>m [Vs [\<mapsto>] ls']"
(*<*)
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
(*>*)

(*<*)
declare fun_upd_apply[simp del]
(*>*)


text{*\noindent The main theorem: *}

theorem assumes wf: "wwf_J_prog P"
shows eval\<^isub>1_eval: "P \<turnstile> \<langle>e,(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle>
  \<Longrightarrow> (\<And>Vs ls. \<lbrakk> fv e \<subseteq> set Vs;  l \<subseteq>\<^sub>m [Vs[\<mapsto>]ls]; size Vs + max_vars e \<le> size ls \<rbrakk>
       \<Longrightarrow> \<exists>ls'. compP\<^isub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^isub>1 Vs e,(h,ls)\<rangle> \<Rightarrow> \<langle>fin\<^isub>1 e',(h',ls')\<rangle> \<and> l' \<subseteq>\<^sub>m [Vs[\<mapsto>]ls'])"
(*<*)
  (is "_ \<Longrightarrow> (\<And>Vs ls. PROP ?P e h l e' h' l' Vs ls)"
   is "_ \<Longrightarrow> (\<And>Vs ls. \<lbrakk> _; _; _ \<rbrakk> \<Longrightarrow> \<exists>ls'. ?Post e h l e' h' l' Vs ls ls')")
(*>*)

and evals\<^isub>1_evals: "P \<turnstile> \<langle>es,(h,l)\<rangle> [\<Rightarrow>] \<langle>es',(h',l')\<rangle>
    \<Longrightarrow> (\<And>Vs ls. \<lbrakk> fvs es \<subseteq> set Vs;  l \<subseteq>\<^sub>m [Vs[\<mapsto>]ls]; size Vs + max_varss es \<le> size ls \<rbrakk>
         \<Longrightarrow> \<exists>ls'. compP\<^isub>1 P \<turnstile>\<^sub>1 \<langle>compEs\<^isub>1 Vs es,(h,ls)\<rangle> [\<Rightarrow>] \<langle>compEs\<^isub>1 Vs es',(h',ls')\<rangle> \<and>
                      l' \<subseteq>\<^sub>m [Vs[\<mapsto>]ls'])"
(*<*)
  (is "_ \<Longrightarrow> (\<And>Vs ls. PROP ?Ps es h l es' h' l' Vs ls)"
   is "_ \<Longrightarrow> (\<And>Vs ls. \<lbrakk> _; _; _\<rbrakk> \<Longrightarrow> \<exists>ls'. ?Posts es h l es' h' l' Vs ls ls')")
proof (induct rule:eval_evals_inducts)
  case Nil thus ?case by(fastsimp intro!:Nil\<^isub>1)
next
  case (Cons e h l v h' l' es es' h\<^isub>2 l\<^isub>2)
  have "PROP ?P e h l (Val v) h' l' Vs ls" by fact
  with Cons.prems
  obtain ls' where 1: "?Post e h l (Val v) h' l' Vs ls ls'"
    "size ls = size ls'" by(auto intro!:eval\<^isub>1_preserves_len)
  have "PROP ?Ps es h' l' es' h\<^isub>2 l\<^isub>2 Vs ls'" by fact
  with 1 Cons.prems
  obtain ls\<^isub>2 where 2: "?Posts es h' l' es' h\<^isub>2 l\<^isub>2 Vs ls' ls\<^isub>2" by(auto)
  from 1 2 Cons show ?case by(auto intro!:Cons\<^isub>1)
next
  case ConsThrow thus ?case
    by(fastsimp intro!:ConsThrow\<^isub>1 dest: eval_final)
next
  case (Block e h l V e' h' l' T)
  let ?Vs = "Vs @ [V]"
  have IH:
  "\<lbrakk>fv e \<subseteq> set ?Vs; l(V := None) \<subseteq>\<^sub>m [?Vs [\<mapsto>] ls];
    size ?Vs + max_vars e \<le> size ls\<rbrakk>
   \<Longrightarrow> \<exists>ls'. compP\<^isub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^isub>1 ?Vs e,(h,ls)\<rangle> \<Rightarrow> \<langle>fin\<^isub>1 e',(h', ls')\<rangle> \<and>
             l' \<subseteq>\<^sub>m [?Vs [\<mapsto>] ls']" and
  fv: "fv {V:T; e} \<subseteq> set Vs" and rel: "l \<subseteq>\<^sub>m [Vs [\<mapsto>] ls]" and
  len: "length Vs + max_vars {V:T; e} \<le> length ls" by fact+
  have len': "length Vs < length ls" using len by auto
  have "fv e \<subseteq> set ?Vs" using fv by auto
  moreover have "l(V := None) \<subseteq>\<^sub>m [?Vs [\<mapsto>] ls]" using rel len' by simp
  moreover have "size ?Vs + max_vars e \<le> size ls" using len by simp
  ultimately obtain ls' where
   1: "compP\<^isub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^isub>1 ?Vs e,(h,ls)\<rangle> \<Rightarrow> \<langle>fin\<^isub>1 e',(h',ls')\<rangle>"
   and rel': "l' \<subseteq>\<^sub>m [?Vs [\<mapsto>] ls']" using IH by blast
  have [simp]: "length ls = length ls'" by(rule eval\<^isub>1_preserves_len[OF 1])
  show "\<exists>ls'. compP\<^isub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^isub>1 Vs {V:T; e},(h,ls)\<rangle> \<Rightarrow> \<langle>fin\<^isub>1 e',(h',ls')\<rangle>
              \<and> l'(V := l V) \<subseteq>\<^sub>m [Vs [\<mapsto>] ls']" (is "\<exists>ls'. ?R ls'")
  proof
    show "?R ls'"
    proof
      show "compP\<^isub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^isub>1 Vs {V:T; e},(h,ls)\<rangle> \<Rightarrow> \<langle>fin\<^isub>1 e',(h',ls')\<rangle>"
	using 1 by(simp add:Block\<^isub>1)
    next
      show "l'(V := l V) \<subseteq>\<^sub>m [Vs [\<mapsto>] ls']"
      proof -
	have "l' \<subseteq>\<^sub>m [Vs [\<mapsto>] ls', V \<mapsto> ls' ! length Vs]"
	  using len' rel' by simp
	moreover
	{ assume VinVs: "V \<in> set Vs"
	  hence "hidden (Vs @ [V]) (index Vs V)" by(rule hidden_index)
	  hence "unmod (compE\<^isub>1 (Vs @ [V]) e) (index Vs V)"
	    by(rule hidden_unmod)
	  moreover have "index Vs V < length ls"
	    using len' VinVs by(simp add:index_less_aux)
	  ultimately have "ls ! index Vs V = ls' ! index Vs V"
	    by(rule eval\<^isub>1_preserves_unmod[OF 1])
	}
	ultimately show ?thesis using Block_lem[OF rel] len' by auto
      qed
    qed
  qed
next
  case (TryThrow e' h l a h' l' D fs C V e\<^isub>2)
  have "PROP ?P e' h l (Throw a) h' l' Vs ls" by fact
  with TryThrow.prems
  obtain ls' where 1: "?Post e' h l (Throw a) h' l' Vs ls ls'"  by(auto)
  show ?case using 1 TryThrow.hyps by(auto intro!:eval\<^isub>1_evals\<^isub>1.TryThrow\<^isub>1)
next
  case (TryCatch e\<^isub>1 h l a h\<^isub>1 l\<^isub>1 D fs C e\<^isub>2 V e' h\<^isub>2 l\<^isub>2)
  let ?e = "try e\<^isub>1 catch(C V) e\<^isub>2"
  have IH\<^isub>1: "\<lbrakk>fv e\<^isub>1 \<subseteq> set Vs; l \<subseteq>\<^sub>m [Vs [\<mapsto>] ls];
              size Vs + max_vars e\<^isub>1 \<le> length ls\<rbrakk>
          \<Longrightarrow> \<exists>ls\<^isub>1. compP\<^isub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^isub>1 Vs e\<^isub>1,(h,ls)\<rangle> \<Rightarrow>
                                \<langle>fin\<^isub>1 (Throw a),(h\<^isub>1,ls\<^isub>1)\<rangle> \<and>
                    l\<^isub>1 \<subseteq>\<^sub>m [Vs [\<mapsto>] ls\<^isub>1]" and
    fv: "fv ?e \<subseteq> set Vs" and
    rel: "l \<subseteq>\<^sub>m [Vs [\<mapsto>] ls]" and
    len: "length Vs + max_vars ?e \<le> length ls" by fact+
  have "fv e\<^isub>1 \<subseteq> set Vs" using fv by auto
  moreover have "length Vs + max_vars e\<^isub>1 \<le> length ls" using len by(auto)
  ultimately obtain ls\<^isub>1 where
    1: "compP\<^isub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^isub>1 Vs e\<^isub>1,(h,ls)\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^isub>1,ls\<^isub>1)\<rangle>"
    and rel\<^isub>1: "l\<^isub>1 \<subseteq>\<^sub>m [Vs [\<mapsto>] ls\<^isub>1]" using IH\<^isub>1 rel by fastsimp
  from 1 have [simp]: "size ls = size ls\<^isub>1" by(rule eval\<^isub>1_preserves_len)
  let ?Vs = "Vs @ [V]" let ?ls = "(ls\<^isub>1[size Vs:=Addr a])"
  have IH\<^isub>2: "\<lbrakk>fv e\<^isub>2 \<subseteq> set ?Vs; l\<^isub>1(V \<mapsto> Addr a) \<subseteq>\<^sub>m [?Vs [\<mapsto>] ?ls];
              length ?Vs + max_vars e\<^isub>2 \<le> length ?ls\<rbrakk> \<Longrightarrow> \<exists>ls\<^isub>2.
       compP\<^isub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^isub>1 ?Vs e\<^isub>2,(h\<^isub>1,?ls)\<rangle> \<Rightarrow> \<langle>fin\<^isub>1 e',(h\<^isub>2, ls\<^isub>2)\<rangle> \<and>
       l\<^isub>2 \<subseteq>\<^sub>m [?Vs [\<mapsto>] ls\<^isub>2]" by fact
  have len\<^isub>1: "size Vs < size ls\<^isub>1" using len by(auto)
  have "fv e\<^isub>2 \<subseteq> set ?Vs" using fv by auto
  moreover have "l\<^isub>1(V \<mapsto> Addr a) \<subseteq>\<^sub>m [?Vs [\<mapsto>] ?ls]" using rel\<^isub>1 len\<^isub>1 by simp
  moreover have "length ?Vs + max_vars e\<^isub>2 \<le> length ?ls" using len by(auto)
  ultimately obtain ls\<^isub>2 where
    2: "compP\<^isub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^isub>1 ?Vs e\<^isub>2,(h\<^isub>1,?ls)\<rangle> \<Rightarrow> \<langle>fin\<^isub>1 e',(h\<^isub>2, ls\<^isub>2)\<rangle>"
    and rel\<^isub>2: "l\<^isub>2 \<subseteq>\<^sub>m [?Vs [\<mapsto>] ls\<^isub>2]"  using IH\<^isub>2 by blast
  from 2 have [simp]: "size ls\<^isub>1 = size ls\<^isub>2"
    by(fastsimp dest: eval\<^isub>1_preserves_len)
  show "\<exists>ls\<^isub>2. compP\<^isub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^isub>1 Vs ?e,(h,ls)\<rangle> \<Rightarrow> \<langle>fin\<^isub>1 e',(h\<^isub>2,ls\<^isub>2)\<rangle> \<and>
              l\<^isub>2(V := l\<^isub>1 V) \<subseteq>\<^sub>m [Vs [\<mapsto>] ls\<^isub>2]"  (is "\<exists>ls\<^isub>2. ?R ls\<^isub>2")
  proof
    show "?R ls\<^isub>2"
    proof
      have hp: "h\<^isub>1 a = Some (D, fs)" by fact
      have "P \<turnstile> D \<preceq>\<^sup>* C" by fact hence caught: "compP\<^isub>1 P \<turnstile> D \<preceq>\<^sup>* C" by simp
      from TryCatch\<^isub>1[OF 1 _ caught len\<^isub>1 2, OF hp]
      show "compP\<^isub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^isub>1 Vs ?e,(h,ls)\<rangle> \<Rightarrow> \<langle>fin\<^isub>1 e',(h\<^isub>2,ls\<^isub>2)\<rangle>" by simp
    next
      show "l\<^isub>2(V := l\<^isub>1 V) \<subseteq>\<^sub>m [Vs [\<mapsto>] ls\<^isub>2]"
      proof -
	have "l\<^isub>2 \<subseteq>\<^sub>m [Vs [\<mapsto>] ls\<^isub>2, V \<mapsto> ls\<^isub>2 ! length Vs]"
	  using len\<^isub>1 rel\<^isub>2 by simp
	moreover
	{ assume VinVs: "V \<in> set Vs"
	  hence "hidden (Vs @ [V]) (index Vs V)" by(rule hidden_index)
	  hence "unmod (compE\<^isub>1 (Vs @ [V]) e\<^isub>2) (index Vs V)"
	    by(rule hidden_unmod)
	  moreover have "index Vs V < length ?ls"
	    using len\<^isub>1 VinVs by(simp add:index_less_aux)
	  ultimately have "?ls ! index Vs V = ls\<^isub>2 ! index Vs V"
	    by(rule eval\<^isub>1_preserves_unmod[OF 2])
	  moreover have "index Vs V < size Vs" using VinVs by simp
	  ultimately have "ls\<^isub>1 ! index Vs V = ls\<^isub>2 ! index Vs V"
	    using len\<^isub>1 by(simp del:size_index_conv)
	}
	ultimately show ?thesis using Block_lem[OF rel\<^isub>1] len\<^isub>1  by simp
      qed
    qed
  qed
next
  case Try thus ?case by(fastsimp intro!:Try\<^isub>1)
next
  case Throw thus ?case by(fastsimp intro!:Throw\<^isub>1)
next
  case ThrowNull thus ?case by(fastsimp intro!:ThrowNull\<^isub>1)
next
  case ThrowThrow thus ?case  by(fastsimp intro!:ThrowThrow\<^isub>1)
next
  case (CondT e h l h\<^isub>1 l\<^isub>1 e\<^isub>1 e' h\<^isub>2 l\<^isub>2 e\<^isub>2)
  have "PROP ?P e h l true h\<^isub>1 l\<^isub>1 Vs ls" by fact
  with CondT.prems
  obtain ls\<^isub>1 where 1: "?Post e h l true h\<^isub>1 l\<^isub>1 Vs ls ls\<^isub>1"
    "size ls = size ls\<^isub>1"  by(auto intro!:eval\<^isub>1_preserves_len)
  have "PROP ?P e\<^isub>1 h\<^isub>1 l\<^isub>1 e' h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1" by fact
  with 1 CondT.prems
  obtain ls\<^isub>2 where 2: "?Post e\<^isub>1 h\<^isub>1 l\<^isub>1 e' h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1 ls\<^isub>2"  by(auto)
  from 1 2 show ?case by(auto intro!:CondT\<^isub>1)
next
  case (CondF e h l h\<^isub>1 l\<^isub>1 e\<^isub>2 e' h\<^isub>2 l\<^isub>2 e\<^isub>1 Vs ls)
  have "PROP ?P e h l false h\<^isub>1 l\<^isub>1 Vs ls" by fact
  with CondF.prems
  obtain ls\<^isub>1 where 1: "?Post e h l false h\<^isub>1 l\<^isub>1 Vs ls ls\<^isub>1"
    "size ls = size ls\<^isub>1"  by(auto intro!:eval\<^isub>1_preserves_len)
  have "PROP ?P e\<^isub>2 h\<^isub>1 l\<^isub>1 e' h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1" by fact
  with 1 CondF.prems
  obtain ls\<^isub>2 where 2: "?Post e\<^isub>2 h\<^isub>1 l\<^isub>1 e' h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1 ls\<^isub>2"  by(auto)
  from 1 2 show ?case by(auto intro!:CondF\<^isub>1)
next
  case CondThrow thus ?case by(fastsimp intro!:CondThrow\<^isub>1)
next
  case (Seq e h l v h\<^isub>1 l\<^isub>1 e\<^isub>1 e' h\<^isub>2 l\<^isub>2)
  have "PROP ?P e h l (Val v) h\<^isub>1 l\<^isub>1 Vs ls" by fact
  with Seq.prems
  obtain ls\<^isub>1 where 1: "?Post e h l (Val v) h\<^isub>1 l\<^isub>1 Vs ls ls\<^isub>1"
    "size ls = size ls\<^isub>1"  by(auto intro!:eval\<^isub>1_preserves_len)
  have "PROP ?P e\<^isub>1 h\<^isub>1 l\<^isub>1 e' h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1" by fact
  with 1 Seq.prems
  obtain ls\<^isub>2 where 2: "?Post e\<^isub>1 h\<^isub>1 l\<^isub>1 e' h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1 ls\<^isub>2"  by(auto)
  from 1 2 Seq show ?case by(auto intro!:Seq\<^isub>1)
next
  case SeqThrow thus ?case by(fastsimp intro!:SeqThrow\<^isub>1)
next
  case WhileF thus ?case by(fastsimp intro!:eval\<^isub>1_evals\<^isub>1.intros)
next
  case (WhileT e h l h\<^isub>1 l\<^isub>1 c v h\<^isub>2 l\<^isub>2 e' h\<^isub>3 l\<^isub>3)
  have "PROP ?P e h l true h\<^isub>1 l\<^isub>1 Vs ls" by fact
  with WhileT.prems
  obtain ls\<^isub>1 where 1: "?Post e h l true h\<^isub>1 l\<^isub>1 Vs ls ls\<^isub>1"
    "size ls = size ls\<^isub>1"   by(auto intro!:eval\<^isub>1_preserves_len)
  have "PROP ?P c h\<^isub>1 l\<^isub>1 (Val v) h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1" by fact
  with 1 WhileT.prems
  obtain ls\<^isub>2 where 2: "?Post c h\<^isub>1 l\<^isub>1 (Val v) h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1 ls\<^isub>2"
    "size ls\<^isub>1 = size ls\<^isub>2"    by(auto intro!:eval\<^isub>1_preserves_len)
  have "PROP ?P (While (e) c) h\<^isub>2 l\<^isub>2 e' h\<^isub>3 l\<^isub>3 Vs ls\<^isub>2" by fact
  with 1 2 WhileT.prems
  obtain ls\<^isub>3 where 3: "?Post (While (e) c) h\<^isub>2 l\<^isub>2 e' h\<^isub>3 l\<^isub>3 Vs ls\<^isub>2 ls\<^isub>3" by(auto)
  from 1 2 3 show ?case by(auto intro!:WhileT\<^isub>1)
next
  case (WhileBodyThrow e h l h\<^isub>1 l\<^isub>1 c e' h\<^isub>2 l\<^isub>2)
  have "PROP ?P e h l true h\<^isub>1 l\<^isub>1 Vs ls" by fact
  with WhileBodyThrow.prems
  obtain ls\<^isub>1 where 1: "?Post e h l true h\<^isub>1 l\<^isub>1 Vs ls ls\<^isub>1"
    "size ls = size ls\<^isub>1"    by(auto intro!:eval\<^isub>1_preserves_len)
  have "PROP ?P c h\<^isub>1 l\<^isub>1 (throw e') h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1" by fact
  with 1 WhileBodyThrow.prems
  obtain ls\<^isub>2 where 2: "?Post c h\<^isub>1 l\<^isub>1 (throw e') h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1 ls\<^isub>2" by auto
  from 1 2 show ?case by(auto intro!:WhileBodyThrow\<^isub>1)
next
  case WhileCondThrow thus ?case by(fastsimp intro!:WhileCondThrow\<^isub>1)
next
  case New thus ?case by(fastsimp intro:eval\<^isub>1_evals\<^isub>1.intros)
next
  case NewFail thus ?case by(fastsimp intro:eval\<^isub>1_evals\<^isub>1.intros)
next
  case Cast thus ?case by(fastsimp intro:eval\<^isub>1_evals\<^isub>1.intros)
next
  case CastNull thus ?case by(fastsimp intro:eval\<^isub>1_evals\<^isub>1.intros)
next
  case CastThrow thus ?case by(fastsimp intro:eval\<^isub>1_evals\<^isub>1.intros)
next
  case (CastFail e h l a h\<^isub>1 l\<^isub>1 D fs C)
  have "PROP ?P e h l (addr a) h\<^isub>1 l\<^isub>1 Vs ls" by fact
  with CastFail.prems
  obtain ls\<^isub>1 where 1: "?Post e h l (addr a) h\<^isub>1 l\<^isub>1 Vs ls ls\<^isub>1" by auto
  show ?case using 1 CastFail.hyps
    by(auto intro!:CastFail\<^isub>1[where D=D])
next
  case Val thus ?case by(fastsimp intro:eval\<^isub>1_evals\<^isub>1.intros)
next
  case (BinOp e h l v\<^isub>1 h\<^isub>1 l\<^isub>1 e\<^isub>1 v\<^isub>2 h\<^isub>2 l\<^isub>2 bop v)
  have "PROP ?P e h l (Val v\<^isub>1) h\<^isub>1 l\<^isub>1 Vs ls" by fact
  with BinOp.prems
  obtain ls\<^isub>1 where 1: "?Post e h l (Val v\<^isub>1) h\<^isub>1 l\<^isub>1 Vs ls ls\<^isub>1"
    "size ls = size ls\<^isub>1"    by(auto intro!:eval\<^isub>1_preserves_len)
  have "PROP ?P e\<^isub>1 h\<^isub>1 l\<^isub>1 (Val v\<^isub>2) h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1" by fact
  with 1 BinOp.prems
  obtain ls\<^isub>2 where 2: "?Post e\<^isub>1 h\<^isub>1 l\<^isub>1 (Val v\<^isub>2) h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1 ls\<^isub>2"  by(auto)
  from 1 2 BinOp show ?case by(auto intro!:BinOp\<^isub>1)
next
  case (BinOpThrow2 e\<^isub>0 h l v\<^isub>1 h\<^isub>1 l\<^isub>1 e\<^isub>1 e h\<^isub>2 l\<^isub>2 bop)
  have "PROP ?P e\<^isub>0 h l (Val v\<^isub>1) h\<^isub>1 l\<^isub>1 Vs ls" by fact
  with BinOpThrow2.prems
  obtain ls\<^isub>1 where 1: "?Post e\<^isub>0 h l (Val v\<^isub>1) h\<^isub>1 l\<^isub>1 Vs ls ls\<^isub>1"
    "size ls = size ls\<^isub>1"    by(auto intro!:eval\<^isub>1_preserves_len)
  have "PROP ?P e\<^isub>1 h\<^isub>1 l\<^isub>1 (throw e) h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1" by fact
  with 1 BinOpThrow2.prems
  obtain ls\<^isub>2 where 2: "?Post e\<^isub>1 h\<^isub>1 l\<^isub>1 (throw e) h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1 ls\<^isub>2"  by(auto)
  from 1 2 BinOpThrow2 show ?case by(auto intro!:BinOpThrow\<^isub>2\<^isub>1)
next
  case BinOpThrow1 thus ?case  by(fastsimp intro!:eval\<^isub>1_evals\<^isub>1.intros)
next
  case Var thus ?case
    by(force intro!:Var\<^isub>1 simp add:index_less_aux map_le_def fun_upds_apply)
next
  case LAss thus ?case
    by(fastsimp simp add: index_less_aux LAss_lem intro:eval\<^isub>1_evals\<^isub>1.intros
                dest:eval\<^isub>1_preserves_len)
next
  case LAssThrow thus ?case by(fastsimp intro:eval\<^isub>1_evals\<^isub>1.intros)
next
  case FAcc thus ?case by(fastsimp intro:eval\<^isub>1_evals\<^isub>1.intros)
next
  case FAccNull thus ?case by(fastsimp intro:eval\<^isub>1_evals\<^isub>1.intros)
next
  case FAccThrow thus ?case by(fastsimp intro:eval\<^isub>1_evals\<^isub>1.intros)
next
  case (FAss e\<^isub>1 h l a h\<^isub>1 l\<^isub>1 e\<^isub>2 v h\<^isub>2 l\<^isub>2 C fs fs' F D h\<^isub>2')
  have "PROP ?P e\<^isub>1 h l (addr a) h\<^isub>1 l\<^isub>1 Vs ls" by fact
  with FAss.prems
  obtain ls\<^isub>1 where 1: "?Post e\<^isub>1 h l (addr a) h\<^isub>1 l\<^isub>1 Vs ls ls\<^isub>1"
    "size ls = size ls\<^isub>1"    by(auto intro!:eval\<^isub>1_preserves_len)
  have "PROP ?P e\<^isub>2 h\<^isub>1 l\<^isub>1 (Val v) h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1" by fact
  with 1 FAss.prems
  obtain ls\<^isub>2 where 2: "?Post e\<^isub>2 h\<^isub>1 l\<^isub>1 (Val v) h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1 ls\<^isub>2"  by(auto)
  from 1 2 FAss show ?case by(auto intro!:FAss\<^isub>1)
next
  case (FAssNull e\<^isub>1 h l h\<^isub>1 l\<^isub>1 e\<^isub>2 v h\<^isub>2 l\<^isub>2 F D)
  have "PROP ?P e\<^isub>1 h l null h\<^isub>1 l\<^isub>1 Vs ls" by fact
  with FAssNull.prems
  obtain ls\<^isub>1 where 1: "?Post e\<^isub>1 h l null h\<^isub>1 l\<^isub>1 Vs ls ls\<^isub>1"
    "size ls = size ls\<^isub>1"    by(auto intro!:eval\<^isub>1_preserves_len)
  have "PROP ?P e\<^isub>2 h\<^isub>1 l\<^isub>1 (Val v) h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1" by fact
  with 1 FAssNull.prems
  obtain ls\<^isub>2 where 2: "?Post e\<^isub>2 h\<^isub>1 l\<^isub>1 (Val v) h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1 ls\<^isub>2" by(auto)
  from 1 2 FAssNull show ?case by(auto intro!:FAssNull\<^isub>1)
next
  case FAssThrow1 thus ?case by(fastsimp intro:eval\<^isub>1_evals\<^isub>1.intros)
next
  case (FAssThrow2 e\<^isub>1 h l v h\<^isub>1 l\<^isub>1 e\<^isub>2 e h\<^isub>2 l\<^isub>2 F D)
  have "PROP ?P e\<^isub>1 h l (Val v) h\<^isub>1 l\<^isub>1 Vs ls" by fact
  with FAssThrow2.prems
  obtain ls\<^isub>1 where 1: "?Post e\<^isub>1 h l (Val v) h\<^isub>1 l\<^isub>1 Vs ls ls\<^isub>1"
    "size ls = size ls\<^isub>1"   by(auto intro!:eval\<^isub>1_preserves_len)
  have "PROP ?P e\<^isub>2 h\<^isub>1 l\<^isub>1 (throw e) h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1" by fact
  with 1 FAssThrow2.prems
  obtain ls\<^isub>2 where 2: "?Post e\<^isub>2 h\<^isub>1 l\<^isub>1 (throw e) h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1 ls\<^isub>2"  by(auto)
  from 1 2 FAssThrow2 show ?case by(auto intro!:FAssThrow\<^isub>2\<^isub>1)
next
  case (CallNull e h l h\<^isub>1 l\<^isub>1 es vs h\<^isub>2 l\<^isub>2 M)
  have "PROP ?P e h l null h\<^isub>1 l\<^isub>1 Vs ls" by fact
  with CallNull.prems
  obtain ls\<^isub>1 where 1: "?Post e h l null h\<^isub>1 l\<^isub>1 Vs ls ls\<^isub>1"
    "size ls = size ls\<^isub>1"    by(auto intro!:eval\<^isub>1_preserves_len)
  have "PROP ?Ps es h\<^isub>1 l\<^isub>1 (map Val vs) h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1" by fact
  with 1 CallNull.prems
  obtain ls\<^isub>2 where 2: "?Posts es h\<^isub>1 l\<^isub>1 (map Val vs) h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1 ls\<^isub>2" by(auto)
  from 1 2 CallNull show ?case
    by (auto simp add: map_compose[symmetric] comp_def elim!: CallNull\<^isub>1)
next
  case CallObjThrow thus ?case  by(fastsimp intro:eval\<^isub>1_evals\<^isub>1.intros)
next
  case (CallParamsThrow e h l v h\<^isub>1 l\<^isub>1 es vs ex es' h\<^isub>2 l\<^isub>2 M)
  have "PROP ?P e h l (Val v) h\<^isub>1 l\<^isub>1 Vs ls" by fact
  with CallParamsThrow.prems
  obtain ls\<^isub>1 where 1: "?Post e h l (Val v) h\<^isub>1 l\<^isub>1 Vs ls ls\<^isub>1"
    "size ls = size ls\<^isub>1"    by(auto intro!:eval\<^isub>1_preserves_len)
  have "PROP ?Ps es h\<^isub>1 l\<^isub>1 (map Val vs @ throw ex # es') h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1" by fact
  with 1 CallParamsThrow.prems
  obtain ls\<^isub>2 where 2: "?Posts es h\<^isub>1 l\<^isub>1 (map Val vs @ throw ex # es') h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1 ls\<^isub>2" by(auto)
  from 1 2 CallParamsThrow show ?case
    by (auto simp add: map_compose[symmetric] comp_def
             elim!: CallParamsThrow\<^isub>1 dest!:evals_final)
next
  case (Call e h l a h\<^isub>1 l\<^isub>1 es vs h\<^isub>2 l\<^isub>2 C fs M Ts T pns body D l\<^isub>2' b' h\<^isub>3 l\<^isub>3)
  have "PROP ?P e h l (addr a) h\<^isub>1 l\<^isub>1 Vs ls" by fact
  with Call.prems
  obtain ls\<^isub>1 where 1: "?Post e h l (addr a) h\<^isub>1 l\<^isub>1 Vs ls ls\<^isub>1"
    "size ls = size ls\<^isub>1"    by(auto intro!:eval\<^isub>1_preserves_len)
  have "PROP ?Ps es h\<^isub>1 l\<^isub>1 (map Val vs) h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1" by fact
  with 1 Call.prems
  obtain ls\<^isub>2 where 2: "?Posts es h\<^isub>1 l\<^isub>1 (map Val vs) h\<^isub>2 l\<^isub>2 Vs ls\<^isub>1 ls\<^isub>2"
    "size ls\<^isub>1 = size ls\<^isub>2"    by(auto intro!:evals\<^isub>1_preserves_len)
  let ?Vs = "this#pns"
  let ?ls = "Addr a # vs @ replicate (max_vars body) arbitrary"
  have mdecl: "P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D" by fact
  have fv_body: "fv body \<subseteq> set ?Vs" and wf_size: "size Ts = size pns"
    using wf mdecl by(auto dest!:sees_wf_mdecl simp:wf_mdecl_def)
  have mdecl\<^isub>1: "compP\<^isub>1 P \<turnstile> C sees M: Ts\<rightarrow>T = (compE\<^isub>1 ?Vs body) in D"
    using sees_method_compP[OF mdecl, of "\<lambda>(pns,e). compE\<^isub>1 (this#pns) e"]
    by(simp)
  have [simp]: "l\<^isub>2' = [this \<mapsto> Addr a, pns [\<mapsto>] vs]" by fact
  have Call_size: "size vs = size pns" by fact
  have "PROP ?P body h\<^isub>2 l\<^isub>2' b' h\<^isub>3 l\<^isub>3 ?Vs ?ls" by fact
  with 1 2 fv_body Call_size Call.prems
  obtain ls\<^isub>3 where 3: "?Post body h\<^isub>2 l\<^isub>2' b' h\<^isub>3 l\<^isub>3 ?Vs ?ls ls\<^isub>3"  by(auto)
  have hp: "h\<^isub>2 a = Some (C, fs)" by fact
  from 1 2 3 hp mdecl\<^isub>1 wf_size Call_size show ?case
    by(fastsimp simp add: map_compose[symmetric] comp_def
                intro!: Call\<^isub>1 dest!:evals_final)
qed
(*>*)


subsection{*Preservation of well-formedness*}

text{* The compiler preserves well-formedness. Is less trivial than it
may appear. We start with two simple properties: preservation of
well-typedness *}

lemma compE\<^isub>1_pres_wt: "\<And>Vs Ts U.
  \<lbrakk> P,[Vs[\<mapsto>]Ts] \<turnstile> e :: U; size Ts = size Vs \<rbrakk>
  \<Longrightarrow> compP f P,Ts \<turnstile>\<^sub>1 compE\<^isub>1 Vs e :: U"
and  "\<And>Vs Ts Us.
  \<lbrakk> P,[Vs[\<mapsto>]Ts] \<turnstile> es [::] Us; size Ts = size Vs \<rbrakk>
  \<Longrightarrow> compP f P,Ts \<turnstile>\<^sub>1 compEs\<^isub>1 Vs es [::] Us"
(*<*)
apply(induct e and es)
apply clarsimp
apply(fastsimp)
apply clarsimp
apply(fastsimp split:bop.splits)
apply (fastsimp simp:map_upds_apply_eq_Some split:split_if_asm)
apply (fastsimp simp:map_upds_apply_eq_Some split:split_if_asm)
apply (fastsimp)
apply (fastsimp)
apply (fastsimp dest!: sees_method_compP[where f = f])
apply (fastsimp simp:nth_append)
apply (fastsimp)
apply (fastsimp)
apply (fastsimp)
apply (fastsimp)
apply (fastsimp simp:nth_append)
apply simp
apply (fastsimp)
done
(*>*)

text{*\noindent and the correct block numbering: *}

lemma \<B>: "\<And>Vs n. size Vs = n \<Longrightarrow> \<B> (compE\<^isub>1 Vs e) n"
and \<B>s: "\<And>Vs n. size Vs = n \<Longrightarrow> \<B>s (compEs\<^isub>1 Vs es) n"
(*<*)by(induct e and es) simp_all(*>*)

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


lemma A_compE\<^isub>1_None[simp]:
      "\<And>Vs. \<A> e = None \<Longrightarrow> \<A> (compE\<^isub>1 Vs e) = None"
and "\<And>Vs. \<A>s es = None \<Longrightarrow> \<A>s (compEs\<^isub>1 Vs es) = None"
(*<*)by(induct e and es)(auto simp:hyperset_defs)(*>*)


lemma A_compE\<^isub>1:
      "\<And>A Vs. \<lbrakk> \<A> e = \<lfloor>A\<rfloor>; fv e \<subseteq> set Vs \<rbrakk> \<Longrightarrow> \<A> (compE\<^isub>1 Vs e) = \<lfloor>index Vs ` A\<rfloor>"
and "\<And>A Vs. \<lbrakk> \<A>s es = \<lfloor>A\<rfloor>; fvs es \<subseteq> set Vs \<rbrakk> \<Longrightarrow> \<A>s (compEs\<^isub>1 Vs es) = \<lfloor>index Vs ` A\<rfloor>"
(*<*)
proof(induct e and es)
  case (Block V' T e)
  hence "fv e \<subseteq> set (Vs@[V'])" by fastsimp
  moreover obtain B where "\<A> e = \<lfloor>B\<rfloor>"
    using Block.prems by(simp add: hyperset_defs)
  moreover from calculation have "B \<subseteq> set (Vs@[V'])" by(auto dest!:A_fv)
  ultimately show ?case using Block
    by(auto simp add: hyperset_defs image_index)
next
  case (TryCatch e\<^isub>1 C V' e\<^isub>2)
  hence fve\<^isub>2: "fv e\<^isub>2 \<subseteq> set (Vs@[V'])" by auto
  show ?case
  proof (cases "\<A> e\<^isub>1")
    assume A\<^isub>1: "\<A> e\<^isub>1 = None"
    then obtain A\<^isub>2 where A\<^isub>2: "\<A> e\<^isub>2 = \<lfloor>A\<^isub>2\<rfloor>" using TryCatch
      by(simp add:hyperset_defs)
    hence "A\<^isub>2 \<subseteq> set (Vs@[V'])" using TryCatch.prems A_fv[OF A\<^isub>2] by simp blast
    thus ?thesis using TryCatch fve\<^isub>2 A\<^isub>1 A\<^isub>2
      by(auto simp add:hyperset_defs image_index)
  next
    fix A\<^isub>1 assume A\<^isub>1: "\<A> e\<^isub>1 =  \<lfloor>A\<^isub>1\<rfloor>"
    show ?thesis
    proof (cases  "\<A> e\<^isub>2")
      assume A\<^isub>2: "\<A> e\<^isub>2 = None"
      then show ?case using TryCatch A\<^isub>1 by(simp add:hyperset_defs)
    next
      fix A\<^isub>2 assume A\<^isub>2: "\<A> e\<^isub>2 = \<lfloor>A\<^isub>2\<rfloor>"
      have "A\<^isub>1 \<subseteq> set Vs" using TryCatch.prems A_fv[OF A\<^isub>1] by simp blast
      moreover
      have "A\<^isub>2 \<subseteq> set (Vs@[V'])" using TryCatch.prems A_fv[OF A\<^isub>2] by simp blast
      ultimately show ?thesis using TryCatch A\<^isub>1 A\<^isub>2
	by(fastsimp simp add: hyperset_defs image_index
	  Diff_subset_conv inj_on_image_Int[OF inj_on_index])
    qed
  qed
next
  case (Cond e e\<^isub>1 e\<^isub>2)
  { assume "\<A> e = None \<or> \<A> e\<^isub>1 = None \<or> \<A> e\<^isub>2 = None"
    hence ?case using Cond by(auto simp add:hyperset_defs image_Un)
  }
  moreover
  { fix A A\<^isub>1 A\<^isub>2
    assume "\<A> e = \<lfloor>A\<rfloor>" and A\<^isub>1: "\<A> e\<^isub>1 = \<lfloor>A\<^isub>1\<rfloor>" and A\<^isub>2: "\<A> e\<^isub>2 = \<lfloor>A\<^isub>2\<rfloor>"
    moreover
    have "A\<^isub>1 \<subseteq> set Vs" using Cond.prems A_fv[OF A\<^isub>1] by simp blast
    moreover
    have "A\<^isub>2 \<subseteq> set Vs" using Cond.prems A_fv[OF A\<^isub>2] by simp blast
    ultimately have ?case using Cond
      by(auto simp add:hyperset_defs image_Un
	  inj_on_image_Int[OF inj_on_index])
  }
  ultimately show ?case by fastsimp
qed (auto simp add:hyperset_defs)
(*>*)


lemma D_None[iff]: "\<D> (e::'a exp) None" and [iff]: "\<D>s (es::'a exp list) None"
(*<*)by(induct e and es)(simp_all)(*>*)


lemma D_index_compE\<^isub>1:
      "\<And>A Vs. \<lbrakk> A \<subseteq> set Vs; fv e \<subseteq> set Vs \<rbrakk> \<Longrightarrow>
                \<D> e \<lfloor>A\<rfloor> \<Longrightarrow> \<D> (compE\<^isub>1 Vs e) \<lfloor>index Vs ` A\<rfloor>"
and "\<And>A Vs. \<lbrakk> A \<subseteq> set Vs; fvs es \<subseteq> set Vs \<rbrakk> \<Longrightarrow>
                \<D>s es \<lfloor>A\<rfloor> \<Longrightarrow> \<D>s (compEs\<^isub>1 Vs es) \<lfloor>index Vs ` A\<rfloor>"
(*<*)
proof(induct e and es)
  case (BinOp e\<^isub>1 bop e\<^isub>2)
  hence IH\<^isub>1: "\<D> (compE\<^isub>1 Vs e\<^isub>1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e\<^isub>1")
    case None thus ?thesis using BinOp by simp
  next
    case (Some A\<^isub>1)
    have indexA\<^isub>1: "\<A> (compE\<^isub>1 Vs e\<^isub>1) = \<lfloor>index Vs ` A\<^isub>1\<rfloor>"
      using A_compE\<^isub>1[OF Some] BinOp.prems  by auto
    have "A \<union> A\<^isub>1 \<subseteq> set Vs" using BinOp.prems A_fv[OF Some] by auto
    hence "\<D> (compE\<^isub>1 Vs e\<^isub>2) \<lfloor>index Vs ` (A \<union> A\<^isub>1)\<rfloor>" using BinOp Some by auto
    hence "\<D> (compE\<^isub>1 Vs e\<^isub>2) \<lfloor>index Vs ` A \<union> index Vs ` A\<^isub>1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH\<^isub>1 indexA\<^isub>1 by auto
  qed
next
  case (FAss e\<^isub>1 F D e\<^isub>2)
  hence IH\<^isub>1: "\<D> (compE\<^isub>1 Vs e\<^isub>1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e\<^isub>1")
    case None thus ?thesis using FAss by simp
  next
    case (Some A\<^isub>1)
    have indexA\<^isub>1: "\<A> (compE\<^isub>1 Vs e\<^isub>1) = \<lfloor>index Vs ` A\<^isub>1\<rfloor>"
      using A_compE\<^isub>1[OF Some] FAss.prems  by auto
    have "A \<union> A\<^isub>1 \<subseteq> set Vs" using FAss.prems A_fv[OF Some] by auto
    hence "\<D> (compE\<^isub>1 Vs e\<^isub>2) \<lfloor>index Vs ` (A \<union> A\<^isub>1)\<rfloor>" using FAss Some by auto
    hence "\<D> (compE\<^isub>1 Vs e\<^isub>2) \<lfloor>index Vs ` A \<union> index Vs ` A\<^isub>1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH\<^isub>1 indexA\<^isub>1 by auto
  qed
next
  case (Call e\<^isub>1 M es)
  hence IH\<^isub>1: "\<D> (compE\<^isub>1 Vs e\<^isub>1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e\<^isub>1")
    case None thus ?thesis using Call by simp
  next
    case (Some A\<^isub>1)
    have indexA\<^isub>1: "\<A> (compE\<^isub>1 Vs e\<^isub>1) = \<lfloor>index Vs ` A\<^isub>1\<rfloor>"
      using A_compE\<^isub>1[OF Some] Call.prems  by auto
    have "A \<union> A\<^isub>1 \<subseteq> set Vs" using Call.prems A_fv[OF Some] by auto
    hence "\<D>s (compEs\<^isub>1 Vs es) \<lfloor>index Vs ` (A \<union> A\<^isub>1)\<rfloor>" using Call Some by auto
    hence "\<D>s (compEs\<^isub>1 Vs es) \<lfloor>index Vs ` A \<union> index Vs ` A\<^isub>1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH\<^isub>1 indexA\<^isub>1 by auto
  qed
next
  case (TryCatch e\<^isub>1 C V e\<^isub>2)
  have "\<lbrakk> A\<union>{V} \<subseteq> set(Vs@[V]); fv e\<^isub>2 \<subseteq> set(Vs@[V]); \<D> e\<^isub>2 \<lfloor>A\<union>{V}\<rfloor>\<rbrakk> \<Longrightarrow>
        \<D> (compE\<^isub>1 (Vs@[V]) e\<^isub>2) \<lfloor>index (Vs@[V]) ` (A\<union>{V})\<rfloor>" by fact
  hence "\<D> (compE\<^isub>1 (Vs@[V]) e\<^isub>2) \<lfloor>index (Vs@[V]) ` (A\<union>{V})\<rfloor>"
    using TryCatch.prems by(simp add:Diff_subset_conv)
  moreover have "index (Vs@[V]) ` A \<subseteq> index Vs ` A \<union> {size Vs}"
    using TryCatch.prems by(auto simp add: image_index split:split_if_asm)
  ultimately show ?case using TryCatch by(auto simp:hyperset_defs elim!:D_mono')
next
  case (Seq e\<^isub>1 e\<^isub>2)
  hence IH\<^isub>1: "\<D> (compE\<^isub>1 Vs e\<^isub>1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e\<^isub>1")
    case None thus ?thesis using Seq by simp
  next
    case (Some A\<^isub>1)
    have indexA\<^isub>1: "\<A> (compE\<^isub>1 Vs e\<^isub>1) = \<lfloor>index Vs ` A\<^isub>1\<rfloor>"
      using A_compE\<^isub>1[OF Some] Seq.prems  by auto
    have "A \<union> A\<^isub>1 \<subseteq> set Vs" using Seq.prems A_fv[OF Some] by auto
    hence "\<D> (compE\<^isub>1 Vs e\<^isub>2) \<lfloor>index Vs ` (A \<union> A\<^isub>1)\<rfloor>" using Seq Some by auto
    hence "\<D> (compE\<^isub>1 Vs e\<^isub>2) \<lfloor>index Vs ` A \<union> index Vs ` A\<^isub>1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH\<^isub>1 indexA\<^isub>1 by auto
  qed
next
  case (Cond e e\<^isub>1 e\<^isub>2)
  hence IH\<^isub>1: "\<D> (compE\<^isub>1 Vs e) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e")
    case None thus ?thesis using Cond by simp
  next
    case (Some B)
    have indexB: "\<A> (compE\<^isub>1 Vs e) = \<lfloor>index Vs ` B\<rfloor>"
      using A_compE\<^isub>1[OF Some] Cond.prems  by auto
    have "A \<union> B \<subseteq> set Vs" using Cond.prems A_fv[OF Some] by auto
    hence "\<D> (compE\<^isub>1 Vs e\<^isub>1) \<lfloor>index Vs ` (A \<union> B)\<rfloor>"
      and "\<D> (compE\<^isub>1 Vs e\<^isub>2) \<lfloor>index Vs ` (A \<union> B)\<rfloor>"
      using Cond Some by auto
    hence "\<D> (compE\<^isub>1 Vs e\<^isub>1) \<lfloor>index Vs ` A \<union> index Vs ` B\<rfloor>"
      and "\<D> (compE\<^isub>1 Vs e\<^isub>2) \<lfloor>index Vs ` A \<union> index Vs ` B\<rfloor>"
      by(simp add: image_Un)+
    thus ?thesis using IH\<^isub>1 indexB by auto
  qed
next
  case (While e\<^isub>1 e\<^isub>2)
  hence IH\<^isub>1: "\<D> (compE\<^isub>1 Vs e\<^isub>1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e\<^isub>1")
    case None thus ?thesis using While by simp
  next
    case (Some A\<^isub>1)
    have indexA\<^isub>1: "\<A> (compE\<^isub>1 Vs e\<^isub>1) = \<lfloor>index Vs ` A\<^isub>1\<rfloor>"
      using A_compE\<^isub>1[OF Some] While.prems  by auto
    have "A \<union> A\<^isub>1 \<subseteq> set Vs" using While.prems A_fv[OF Some] by auto
    hence "\<D> (compE\<^isub>1 Vs e\<^isub>2) \<lfloor>index Vs ` (A \<union> A\<^isub>1)\<rfloor>" using While Some by auto
    hence "\<D> (compE\<^isub>1 Vs e\<^isub>2) \<lfloor>index Vs ` A \<union> index Vs ` A\<^isub>1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH\<^isub>1 indexA\<^isub>1 by auto
  qed
next
  case (Block V T e)
  have "\<lbrakk> A-{V} \<subseteq> set(Vs@[V]); fv e \<subseteq> set(Vs@[V]); \<D> e \<lfloor>A-{V}\<rfloor> \<rbrakk> \<Longrightarrow>
        \<D> (compE\<^isub>1 (Vs@[V]) e) \<lfloor>index (Vs@[V]) ` (A-{V})\<rfloor>" by fact
  hence "\<D> (compE\<^isub>1 (Vs@[V]) e) \<lfloor>index (Vs@[V]) ` (A-{V})\<rfloor>"
    using Block.prems by(simp add:Diff_subset_conv)
  moreover have "size Vs \<notin> index Vs ` A"
    using Block.prems by(auto simp add:image_def)
  ultimately show ?case using Block
    by(auto simp add: image_index Diff_subset_conv hyperset_defs elim!: D_mono')
next
  case (Cons_exp e\<^isub>1 es)
  hence IH\<^isub>1: "\<D> (compE\<^isub>1 Vs e\<^isub>1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e\<^isub>1")
    case None thus ?thesis using Cons_exp by simp
  next
    case (Some A\<^isub>1)
    have indexA\<^isub>1: "\<A> (compE\<^isub>1 Vs e\<^isub>1) = \<lfloor>index Vs ` A\<^isub>1\<rfloor>"
      using A_compE\<^isub>1[OF Some] Cons_exp.prems  by auto
    have "A \<union> A\<^isub>1 \<subseteq> set Vs" using Cons_exp.prems A_fv[OF Some] by auto
    hence "\<D>s (compEs\<^isub>1 Vs es) \<lfloor>index Vs ` (A \<union> A\<^isub>1)\<rfloor>" using Cons_exp Some by auto
    hence "\<D>s (compEs\<^isub>1 Vs es) \<lfloor>index Vs ` A \<union> index Vs ` A\<^isub>1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH\<^isub>1 indexA\<^isub>1 by auto
  qed
qed (simp_all add:hyperset_defs)
(*>*)


lemma index_image_set: "distinct xs \<Longrightarrow> index xs ` set xs = {..<size xs}"
(*<*)by(induct xs rule:rev_induct) (auto simp add: image_index)(*>*)


lemma D_compE\<^isub>1:
  "\<lbrakk> \<D> e \<lfloor>set Vs\<rfloor>; fv e \<subseteq> set Vs; distinct Vs \<rbrakk> \<Longrightarrow> \<D> (compE\<^isub>1 Vs e) \<lfloor>{..<length Vs}\<rfloor>"
(*<*)by(fastsimp dest!: D_index_compE\<^isub>1[OF subset_refl] simp add:index_image_set)(*>*)


lemma D_compE\<^isub>1':
assumes "\<D> e \<lfloor>set(V#Vs)\<rfloor>" and "fv e \<subseteq> set(V#Vs)" and "distinct(V#Vs)"
shows "\<D> (compE\<^isub>1 (V#Vs) e) \<lfloor>{..length Vs}\<rfloor>"
(*<*)
proof -
  have "{..size Vs} = {..<size(V#Vs)}" by auto
  thus ?thesis using prems by (simp only:)(rule D_compE\<^isub>1)
qed
(*>*)


lemma compP\<^isub>1_pres_wf: "wf_J_prog P \<Longrightarrow> wf_J\<^isub>1_prog (compP\<^isub>1 P)"
(*<*)
apply simp
apply(rule wf_prog_compPI)
 prefer 2 apply assumption
apply(case_tac m)
apply(simp add:wf_mdecl_def wf_J\<^isub>1_mdecl_def wf_J_mdecl)
apply(clarify)
apply(frule WT_fv)
apply(fastsimp intro!: compE\<^isub>1_pres_wt D_compE\<^isub>1' \<B>)
done
(*>*)


end

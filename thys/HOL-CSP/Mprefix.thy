(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP - A Shallow Embedding of CSP in  Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Burkhart Wolff.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : A Combined CSP Theory
 *
 * Copyright (c) 2009 Université Paris-Sud, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************\<close>
(*>*)


section\<open> The Multi-Prefix Operator Definition \<close>

theory  Mprefix 
imports Process 
begin 

subsection\<open> The Definition and some Consequences \<close>

lift_definition   Mprefix     :: "['a set,'a => 'a process] => 'a process"
  is "\<lambda>A P. ({(tr,ref). tr = [] \<and> ref Int (ev ` A) = {}} \<union>
             {(tr,ref). tr \<noteq> [] \<and> hd tr \<in> (ev ` A) \<and> 
                        (\<exists> a. ev a = (hd tr)\<and>(tl tr,ref)\<in>\<F>(P a))},
             {d. d \<noteq> [] \<and>  hd d  \<in> (ev ` A) \<and> (\<exists> a. ev a = hd d \<and> tl d \<in> \<D> (P a))})"
proof -
  show \<open>is_process ({(tr, ref). tr = [] \<and> ref \<inter> ev ` (A :: 'a set) = {}} \<union>
                    {(tr, ref). tr \<noteq> [] \<and> hd tr \<in> ev ` A \<and> 
                                (\<exists>a. ev a = hd tr \<and> (tl tr, ref) \<in> \<F> (P a))},
                    {d. d \<noteq> [] \<and> hd d \<in> ev ` A \<and> (\<exists>a. ev a = hd d \<and> tl d \<in> \<D> (P a))}) \<close> 
    (is \<open>is_process(?f, ?d)\<close>) for A P
proof  (simp only: is_process_def FAILURES_def DIVERGENCES_def
                   Product_Type.fst_conv Product_Type.snd_conv,
        intro conjI allI impI)
    show "([],{}) \<in> ?f" by(simp)
next  
    fix    s:: "'a event list" fix X::"'a event set"
    assume H : "(s, X) \<in> ?f"
    show       "front_tickFree s"
               apply(insert H, auto simp:  front_tickFree_def tickFree_def
                                    dest!:list_nonMt_append)
               apply(rename_tac aa ta x, case_tac "ta", auto simp: front_tickFree_charn
                                    dest! : is_processT2[rule_format])
               apply(simp add: tickFree_def)
               done 
next
    fix s t :: "'a event list" 
    assume     "(s @ t, {}) \<in> ?f"
    then show  "(s, {}) \<in> ?f"
               by(auto elim: is_processT3[rule_format])
next
    fix    s:: "'a event list" fix X Y::"'a event set"
    assume     "(s, Y) \<in> ?f \<and> X \<subseteq> Y"
    then show  "(s, X) \<in> ?f"
               by(auto intro: is_processT4[rule_format])
next
    fix    s:: "'a event list" fix X Y::"'a event set"
    assume     "(s, X) \<in> ?f \<and> (\<forall> c. c\<in>Y \<longrightarrow> (s @ [c], {}) \<notin> ?f)"
    then show  "(s, X \<union> Y) \<in> ?f "
               by(auto intro!: is_processT1 is_processT5[rule_format]) 
next
    fix s::    "'a event list" fix X::"'a event set"
    assume     "(s @ [tick], {}) \<in> ?f"
    then show  "(s, X - {tick}) \<in> ?f"
               by(cases s, auto dest!: is_processT6[rule_format])
next
    fix s t::  "'a event list" fix X::"'a event set"
    assume     "s \<in>  ?d \<and> tickFree s \<and> front_tickFree t"
    then show  "s @ t \<in> ?d"
               by(auto intro!: is_processT7_S, cases s, simp_all)
next
    fix s::    "'a event list" fix X::"'a event set"
    assume     "s \<in> ?d"
    then show  "(s, X) \<in> ?f"
               by(auto simp: is_processT8_S)
next
    fix s::    "'a event list" 
    assume     "s @ [tick] \<in> ?d"
    then show  "s \<in> ?d"
               apply(auto)
               apply(cases s, simp_all)
               apply(cases s, auto intro: is_processT9[rule_format])
               done

           qed
         qed


syntax
  "_Mprefix" :: "[pttrn,'a set,'a process] \<Rightarrow> 'a process"	(\<open>(3\<box>(_/\<in>_)/ \<rightarrow> (_))\<close>[0,0,64]64)

term "Ball A (\<lambda>x. P)"

syntax_consts
  "_Mprefix" \<rightleftharpoons> Mprefix

translations
  "\<box>x\<in>A \<rightarrow> P" \<rightleftharpoons> "CONST Mprefix A (\<lambda>x. P)"

text\<open>Syntax Check:\<close>
term \<open>\<box>x\<in>A \<rightarrow> \<box>y\<in>A \<rightarrow> \<box>z\<in>A \<rightarrow> P z x y = Q\<close>


(* bizarre exercise in style proposed by Makarius... *)
lemma is_process_REP_Mprefix'  :
     "is_process ({(tr,ref). tr=[] \<and>  ref \<inter> (ev ` A) = {}} \<union>
                  {(tr,ref). tr \<noteq> [] \<and> hd tr \<in> (ev ` A) \<and>
                        (\<exists> a. ev a = (hd tr) \<and> (tl tr,ref) \<in> \<F>(P a))},
                  {d. d \<noteq>  [] \<and>  hd d \<in> (ev ` A) \<and>
                        (\<exists> a. ev a = hd d  \<and> tl d \<in> \<D>(P a))})"
 (is "is_process(?f, ?d)")
proof  (simp only:is_process_def FAILURES_def DIVERGENCES_def
                  Product_Type.fst_conv Product_Type.snd_conv,
        intro conjI allI impI,goal_cases)
  case 1
    show "([],{}) \<in> ?f" by(simp)
next  
  case (2 s X) 
    assume H : "(s, X) \<in> ?f"
    have       "front_tickFree s"
      apply(insert H, auto simp:  front_tickFree_def tickFree_def
                           dest!:list_nonMt_append)
      apply(rename_tac aa ta x, case_tac "ta", auto simp: front_tickFree_charn
                           dest! : is_processT2[rule_format])
      apply(simp add: tickFree_def)
      done    
    then show "front_tickFree s"  by(auto) 
next
  case (3 s t) 
    assume H : "(s @ t, {}) \<in> ?f"
    show "(s, {}) \<in> ?f" using H  by(auto elim: is_processT3[rule_format])
next
  case (4 s X Y) 
    assume H1: "(s, Y) \<in> ?f \<and> X \<subseteq> Y"
    then show "(s, X) \<in> ?f"  by(auto intro: is_processT4[rule_format])
next
  case (5 s X Y)   
    assume  "(s, X) \<in> ?f \<and> (\<forall> c. c\<in>Y \<longrightarrow> (s @ [c], {}) \<notin> ?f)"
    then show "(s, X \<union> Y) \<in> ?f"  by(auto intro!: is_processT1 is_processT5[rule_format]) 
next
  case (6 s X)   
    assume  "(s @ [tick], {}) \<in> ?f"   
    then show "(s, X - {tick}) \<in> ?f"  by(cases s, auto dest!: is_processT6[rule_format])
next
  case (7 s t) 
    assume H1 : "s \<in>  ?d \<and> tickFree s \<and> front_tickFree t"
    have 7:     "s @ t \<in> ?d"
      using H1  by(auto intro!: is_processT7_S, cases s, simp_all)
    then show "s @ t \<in> ?d" using H1  by(auto)
next
  case (8 s X)   
    assume H : "s \<in> ?d"
    then show "(s, X) \<in> ?f" using H by(auto simp: is_processT8_S)
next
  case (9 s)  
    assume H: "s @ [tick] \<in> ?d"
    then have 9:   "s \<in> ?d"
       apply(auto)
       apply(cases s, simp_all)
       apply(cases s, auto intro: is_processT9[rule_format])
       done
    then show "s \<in> ?d" by(auto)
qed

   
lemma Rep_Abs_Mprefix'' : 
assumes H1 : "f = {(tr, ref). tr = [] \<and> ref \<inter> ev ` A = {}} \<union>
                  {(tr, ref). tr \<noteq> [] \<and> hd tr \<in> ev ` A 
                             \<and> (\<exists>a. ev a = hd tr \<and> (tl tr, ref) \<in> \<F> (P a))}"
    and H2 : "d = {d. d \<noteq>  [] \<and>  hd d \<in> (ev ` A) \<and> 
                     (\<exists> a. ev a = hd d  \<and> tl d \<in> \<D>(P a))}"
  shows "Rep_process (Abs_process (f,d)) = (f,d)"
  using Abs_process_inverse H1 H2 is_process_REP_Mprefix' by blast



subsection \<open> Projections in Prefix \<close>

lemma F_Mprefix : 
  "\<F> (\<box> x \<in> A \<rightarrow> P x) = {(tr,ref). tr=[] \<and>  ref \<inter> (ev ` A) = {}} \<union>
                         {(tr,ref). tr \<noteq> [] \<and> hd tr \<in> (ev ` A) \<and> 
                                   (\<exists> a. ev a = (hd tr) \<and> (tl tr,ref) \<in> \<F>(P a))}"
  by (subst Failures.rep_eq, simp add: Mprefix.rep_eq FAILURES_def)

lemma D_Mprefix:
  "\<D> (\<box> x \<in> A \<rightarrow> P x) = {d. d \<noteq>  [] \<and>  hd d \<in> (ev ` A) \<and> 
                             (\<exists> a. ev a = hd d  \<and> tl d \<in> \<D>(P a))}"
  by (subst Divergences.rep_eq, simp add: Mprefix.rep_eq DIVERGENCES_def)


lemma T_Mprefix:
  "\<T> (\<box> x \<in> A \<rightarrow> P x)={s. s=[] \<or> (\<exists> a. a\<in>A \<and> s\<noteq>[] \<and> hd s = ev a \<and> tl s \<in> \<T>(P a))}"
  by (subst Traces.rep_eq, auto simp add: TRACES_def Failures.rep_eq[symmetric] F_Mprefix)
     (use F_T T_F in \<open>blast+\<close>)
  

subsection \<open> Basic Properties \<close>

lemma tick_T_Mprefix [simp]: "[tick] \<notin> \<T> (\<box> x \<in> A \<rightarrow> P x)"
  by(simp add:T_Mprefix)


lemma Nil_Nin_D_Mprefix [simp]: "[] \<notin> \<D> (\<box> x \<in> A \<rightarrow> P x)"
  by(simp add: D_Mprefix)

subsection\<open> Proof of Continuity Rule \<close>

subsubsection\<open> Backpatch Isabelle 2009-1\<close>

\<comment>\<open>re-introduced from Isabelle/HOLCF 2009-1; clearly
   a derived concept, but still a useful shortcut\<close>

definition
  contlub :: "('a::cpo \<Rightarrow> 'b::cpo) \<Rightarrow> bool" 
  where
  "contlub f = (\<forall>Y. chain Y \<longrightarrow> f (\<Squnion> i. Y i) = (\<Squnion> i. f (Y i)))"

lemma contlubE:
  "\<lbrakk>contlub f; chain Y\<rbrakk> \<Longrightarrow> f (\<Squnion> i. Y i) = (\<Squnion> i. f (Y i))"
  by (simp add: contlub_def)


lemma monocontlub2cont: "\<lbrakk>monofun f; contlub f\<rbrakk> \<Longrightarrow> cont f"
apply (rule contI)
apply (rule thelubE)
apply (erule (1) ch2ch_monofun)
apply (erule (1) contlubE [symmetric])
done

lemma contlubI:
  "(\<And>Y. chain Y \<Longrightarrow> f (\<Squnion> i. Y i) = (\<Squnion> i. f (Y i))) \<Longrightarrow> contlub f"
by (simp add: contlub_def)


lemma cont2contlub: "cont f \<Longrightarrow> contlub f"
apply (rule contlubI)
apply (rule po_class.lub_eqI [symmetric])
apply (erule (1) contE)
done


subsubsection\<open> Core of Proof  \<close>

lemma mono_Mprefix1:
"\<forall>a\<in>A. P a \<sqsubseteq> Q a \<Longrightarrow> \<D> (Mprefix A Q) \<subseteq> \<D> (Mprefix A P)"
  apply(auto simp: D_Mprefix) using le_approx1 by blast

lemma mono_Mprefix2:
"\<forall>x\<in>A. P x \<sqsubseteq> Q x \<Longrightarrow>
 \<forall>s. s \<notin> \<D> (Mprefix A P) \<longrightarrow> Ra (Mprefix A P) s = Ra (Mprefix A Q) s"          
  apply (auto simp: Ra_def D_Mprefix F_Mprefix) using proc_ord2a by blast+

lemma mono_Mprefix3 :
assumes H:"\<forall>x\<in>A. P x \<sqsubseteq> Q x"
shows " min_elems (\<D> (Mprefix A P)) \<subseteq> \<T> (Mprefix A Q)"
proof(auto simp: min_elems_def D_Mprefix T_Mprefix image_def, goal_cases)
  case (1 x a)
  with H[rule_format, of a, OF 1(2)] show ?case 
    apply(auto dest!: le_approx3 simp: min_elems_def)
    apply(subgoal_tac "\<forall>t. t \<in> \<D> (P a) \<longrightarrow> \<not> t < tl x", auto)
    apply(rename_tac t, erule_tac x="(ev a)#t" in allE, auto)
    using less_cons hd_Cons_tl by metis
qed

lemma mono_Mprefix0:
"\<forall>x\<in>A. P x \<sqsubseteq> Q x \<Longrightarrow> Mprefix A P \<sqsubseteq> Mprefix A Q" 
apply(simp add: le_approx_def mono_Mprefix1 mono_Mprefix3)
apply(rule mono_Mprefix2)
apply(auto simp: le_approx_def)
done


lemma mono_Mprefix[simp]: "monofun(Mprefix A)"
by(auto simp: below_fun_def monofun_def mono_Mprefix0)


lemma proc_ord2_set: 
"P \<sqsubseteq> Q \<Longrightarrow> {(s, X). s \<notin> \<D> P \<and> (s, X) \<in> \<F> P} = {(s, X). s \<notin> \<D> P \<and> (s, X) \<in> \<F> Q}"
by(auto simp: le_approx2)


lemma proc_ord_proc_eq_spec: "P \<sqsubseteq> Q \<Longrightarrow> \<D> P \<subseteq> \<D> Q \<Longrightarrow> P = Q"
by (metis (mono_tags, lifting) below_antisym below_refl le_approx_def subset_antisym)


lemma Mprefix_chainpreserving: "chain Y \<Longrightarrow> chain (\<lambda>i. Mprefix A (Y i))"
apply(rule chainI, rename_tac i)
apply(frule_tac i="i" in chainE)
by(simp add: mono_Mprefix0 fun_belowD)


lemma limproc_is_thelub_fun: 
assumes     "chain S" 
shows       "(Lub S c) = lim_proc (range (\<lambda>x. (S x c)))"
proof -
  have    "\<And>xa. chain (\<lambda>x. S x xa)"
                  using `chain S` by(auto intro!: chainI  simp: chain_def fun_belowD )
  then     show ?thesis  by (metis contlub_lambda limproc_is_thelub)
qed


lemma contlub_Mprefix : "contlub(%P. Mprefix A P)"
proof(rule contlubI, rule proc_ord_proc_eq_spec)
   fix Y   :: "nat \<Rightarrow> 'a \<Rightarrow> 'a process" 
   assume C : "chain Y" 
   have   C': "\<And>xa. chain (\<lambda>x. Y x xa)"
                 apply(insert C,rule chainI)
                 by(auto simp: chain_def fun_belowD)
   show       "Mprefix A (\<Squnion> i. Y i) \<sqsubseteq> (\<Squnion> i. Mprefix A (Y i))"
                 by(auto simp: Process.le_approx_def F_Mprefix D_Mprefix T_Mprefix C C'
                               Mprefix_chainpreserving limproc_is_thelub limproc_is_thelub_fun
                               D_T D_LUB D_LUB_2 F_LUB T_LUB_2 Ra_def min_elems_def)
next
   fix Y   :: "nat \<Rightarrow> 'a \<Rightarrow> 'a process" 
   assume C : "chain Y" 
   show       "\<D> (Mprefix A (\<Squnion> i. Y i)) \<subseteq> \<D> (\<Squnion> i. Mprefix A (Y i))"
                 apply(auto simp: Process.le_approx_def F_Mprefix D_Mprefix T_Mprefix 
                                  C Mprefix_chainpreserving limproc_is_thelub D_LUB_2)
                 by (meson C fun_below_iff in_mono is_ub_thelub le_approx1)
qed



lemma Mprefix_cont [simp]: 
"(\<And>x. cont (f x)) \<Longrightarrow> cont (\<lambda>y. \<box> z \<in>  A \<rightarrow> f z y)"
apply(rule_tac f = "\<lambda>z y. (f y z)" in cont_compose)
apply(rule monocontlub2cont)
apply(auto intro: mono_Mprefix contlub_Mprefix cont2cont_lambda)
done


subsection\<open> High-level Syntax for Read and Write \<close>

text\<open> The following syntax introduces the usual channel notation for CSP.
Slightly deviating from conventional wisdom, we view a channel not as a tag in
a pair, rather than as a function of type @{typ "'a\<Rightarrow>'b"}. This paves the way
for \emph{typed} channels over a common universe of events. \<close>

definition  read     :: "['a \<Rightarrow> 'b,'a set, 'a \<Rightarrow> 'b process] \<Rightarrow> 'b process"
where      "read c A P  \<equiv> Mprefix(c ` A) (P o (inv_into A c))"
definition "write"    :: "['a \<Rightarrow> 'b, 'a, 'b process] \<Rightarrow> 'b process"
where      "write c a P \<equiv> Mprefix {c a} (\<lambda> x. P)"
definition  write0   :: "['a, 'a process] \<Rightarrow> 'a process"
where      "write0 a P \<equiv> Mprefix {a} (\<lambda> x. P)"


syntax
  "_read"   :: "[id, pttrn, 'a process] => 'a process"
                                        (\<open>(3(_\<^bold>?_) /\<rightarrow> _)\<close> [0,0,78] 78)
  "_readX"  :: "[id, pttrn, bool,'a process] => 'a process"
                                        (\<open>(3(_\<^bold>?_)\<^bold>|_ /\<rightarrow> _)\<close> [0,0,78] 78)
  "_readS"  :: "[id, pttrn, 'b set,'a process] => 'a process"
                                        (\<open>(3(_\<^bold>?_)\<in>_ /\<rightarrow> _)\<close> [0,0,78] 78)
  "_write"  :: "[id, 'b, 'a process] => 'a process"
                                        (\<open>(3(_\<^bold>!_) /\<rightarrow> _)\<close> [0,0,78] 78)
  "_writeS" :: "['a, 'a process] => 'a process"
                                        (\<open>(3_ /\<rightarrow> _)\<close> [0,78]78)

syntax_consts
  "_read" "_readX" "_readS" \<rightleftharpoons> read and
  "_write" \<rightleftharpoons> "write" and
  "_writeS" \<rightleftharpoons> write0

subsection\<open>CSP$_M$-Style Syntax for Communication Primitives\<close>
translations
  "_read c p P"     \<rightleftharpoons> "CONST read c CONST UNIV (\<lambda>p. P)"
  "_write c p P"    \<rightleftharpoons> "CONST write c p P"
  "_readX c p b P"  => "CONST read c {p. b} (\<lambda>p. P)"
  "_writeS a P"     \<rightleftharpoons> "CONST write0 a P"
  "_readS c p A P"  => "CONST read c A (\<lambda>p. P)"

text\<open>Syntax Check:\<close>
term\<open> d\<^bold>?y \<rightarrow> c\<^bold>!x \<rightarrow> P = Q\<close>


lemma read_cont[simp]: "cont P \<Longrightarrow> cont (\<lambda>y. read c A (P y))"
  unfolding read_def o_def
  by (rule Mprefix_cont) (rule cont2cont_fun) 


lemma read_cont'[simp]: "(\<And>x. cont (f x)) \<Longrightarrow> cont (\<lambda>y. c\<^bold>?x \<rightarrow> f x y)" by simp


lemma write_cont[simp]: "cont (P::('b::cpo \<Rightarrow> 'a process))  \<Longrightarrow> cont(\<lambda>x. (c\<^bold>!a \<rightarrow> P x))"
by(simp add:write_def)


corollary write0_cont_lub : "contlub(Mprefix {a})"
  using contlub_Mprefix by blast


lemma write0_contlub : "contlub(write0 a)"
  unfolding write0_def contlub_def
proof (auto)
  fix Y :: "nat \<Rightarrow> 'a process"
  assume   "chain Y"
  have * : "chain (\<lambda>i. (\<lambda>_. Y i)::'b \<Rightarrow> 'a process)"
           by (meson \<open>chain Y\<close> fun_below_iff po_class.chain_def)
  have **: "(\<lambda>x. Lub Y) = Lub (\<lambda>i. (\<lambda>_. Y i))"
           by(rule ext,metis * ch2ch_fun limproc_is_thelub limproc_is_thelub_fun lub_eq)
  show "Mprefix {a} (\<lambda>x. Lub Y) = (\<Squnion>i. Mprefix {a} (\<lambda>x. Y i))"
    apply(subst **, subst contlubE[OF contlub_Mprefix])
    by (simp_all add: *)
qed
  
lemma write0_cont[simp]: "cont (P::('b::cpo \<Rightarrow> 'a process)) \<Longrightarrow> cont(\<lambda>x. (a \<rightarrow> P x))"
by(simp add:write0_def)

end

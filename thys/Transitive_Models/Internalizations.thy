section\<open>Aids to internalize formulas\<close>

theory Internalizations
  imports
    "ZF-Constructible.DPow_absolute"
    Synthetic_Definition
    Nat_Miscellanea
begin

hide_const (open) Order.pred

definition
  infinity_ax :: "(i \<Rightarrow> o) \<Rightarrow> o" where
  "infinity_ax(M) \<equiv>
      (\<exists>I[M]. (\<exists>z[M]. empty(M,z) \<and> z\<in>I) \<and> (\<forall>y[M]. y\<in>I \<longrightarrow> (\<exists>sy[M]. successor(M,y,sy) \<and> sy\<in>I)))"

definition
  wellfounded_trancl :: "[i=>o,i,i,i] => o" where
  "wellfounded_trancl(M,Z,r,p) \<equiv>
      \<exists>w[M]. \<exists>wx[M]. \<exists>rp[M].
               w \<in> Z & pair(M,w,p,wx) & tran_closure(M,r,rp) & wx \<in> rp"

lemma empty_intf :
  "infinity_ax(M) \<Longrightarrow>
  (\<exists>z[M]. empty(M,z))"
  by (auto simp add: empty_def infinity_ax_def)

lemma Transset_intf :
  "Transset(M) \<Longrightarrow>  y\<in>x \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M"
  by (simp add: Transset_def,auto)

definition
  choice_ax :: "(i\<Rightarrow>o) \<Rightarrow> o" where
  "choice_ax(M) \<equiv> \<forall>x[M]. \<exists>a[M]. \<exists>f[M]. ordinal(M,a) \<and> surjection(M,a,x,f)"

lemma (in M_basic) choice_ax_abs :
  "choice_ax(M) \<longleftrightarrow> (\<forall>x[M]. \<exists>a[M]. \<exists>f[M]. Ord(a) \<and> f \<in> surj(a,x))"
  unfolding choice_ax_def
  by simp

txt\<open>Setting up notation for internalized formulas\<close>

abbreviation
  dec10  :: i   ("10") where "10 \<equiv> succ(9)"
abbreviation
  dec11  :: i   ("11") where "11 \<equiv> succ(10)"
abbreviation
  dec12  :: i   ("12") where "12 \<equiv> succ(11)"
abbreviation
  dec13  :: i   ("13") where "13 \<equiv> succ(12)"
abbreviation
  dec14  :: i   ("14") where "14 \<equiv> succ(13)"
abbreviation
  dec15  :: i   ("15") where "15 \<equiv> succ(14)"
abbreviation
  dec16  :: i   ("16") where "16 \<equiv> succ(15)"
abbreviation
  dec17  :: i   ("17") where "17 \<equiv> succ(16)"
abbreviation
  dec18  :: i   ("18") where "18 \<equiv> succ(17)"
abbreviation
  dec19  :: i   ("19") where "19 \<equiv> succ(18)"
abbreviation
  dec20  :: i   ("20") where "20 \<equiv> succ(19)"
abbreviation
  dec21  :: i   ("21") where "21 \<equiv> succ(20)"
abbreviation
  dec22  :: i   ("22") where "22 \<equiv> succ(21)"
abbreviation
  dec23  :: i   ("23") where "23 \<equiv> succ(22)"
abbreviation
  dec24  :: i   ("24") where "24 \<equiv> succ(23)"
abbreviation
  dec25  :: i   ("25") where "25 \<equiv> succ(24)"
abbreviation
  dec26  :: i   ("26") where "26 \<equiv> succ(25)"
abbreviation
  dec27  :: i   ("27") where "27 \<equiv> succ(26)"
abbreviation
  dec28  :: i   ("28") where "28 \<equiv> succ(27)"
abbreviation
  dec29  :: i   ("29") where "29 \<equiv> succ(28)"

notation Member (\<open>\<cdot>_ \<in>/ _\<cdot>\<close>)
notation Equal (\<open>\<cdot>_ =/ _\<cdot>\<close>)
notation Nand (\<open>\<cdot>\<not>'(_ \<and>/ _')\<cdot>\<close>)
notation And (\<open>\<cdot>_ \<and>/ _\<cdot>\<close>)
notation Or (\<open>\<cdot>_ \<or>/ _\<cdot>\<close>)
notation Iff (\<open>\<cdot>_ \<leftrightarrow>/ _\<cdot>\<close>)
notation Implies (\<open>\<cdot>_ \<rightarrow>/ _\<cdot>\<close>)
notation Neg (\<open>\<cdot>\<not>_\<cdot>\<close>)
notation Forall (\<open>'(\<cdot>\<forall>(/_)\<cdot>')\<close>)
notation Exists (\<open>'(\<cdot>\<exists>(/_)\<cdot>')\<close>)

notation subset_fm (\<open>\<cdot>_ \<subseteq>/ _\<cdot>\<close>)
notation succ_fm (\<open>\<cdot>succ'(_') is _\<cdot>\<close>)
notation empty_fm (\<open>\<cdot>_ is empty\<cdot>\<close>)
notation fun_apply_fm (\<open>\<cdot>_`_ is _\<cdot>\<close>)
notation big_union_fm (\<open>\<cdot>\<Union>_ is _\<cdot>\<close>)
notation upair_fm (\<open>\<cdot>{_,_} is _ \<cdot>\<close>)
notation ordinal_fm (\<open>\<cdot>_ is ordinal\<cdot>\<close>)


notation pair_fm (\<open>\<cdot>\<langle>_,_\<rangle> is _ \<cdot>\<close>)
notation composition_fm (\<open>\<cdot>_ \<circ> _ is _ \<cdot>\<close>)
notation domain_fm (\<open>\<cdot>dom'(_') is _ \<cdot>\<close>)
notation range_fm (\<open>\<cdot>ran'(_') is _ \<cdot>\<close>)
notation union_fm (\<open>\<cdot>_ \<union> _ is _ \<cdot>\<close>)
notation image_fm (\<open>\<cdot>_ `` _ is _ \<cdot>\<close>)
notation pre_image_fm (\<open>\<cdot>_ -`` _ is _ \<cdot>\<close>)
notation field_fm (\<open>\<cdot>fld'(_') is _ \<cdot>\<close>)
notation cons_fm (\<open>\<cdot>cons'(_,_') is _ \<cdot>\<close>)
notation number1_fm (\<open>\<cdot>_ is the number one\<cdot>\<close>)
notation function_fm (\<open>\<cdot>_ is funct\<cdot>\<close>)
notation relation_fm (\<open>\<cdot>_ is relat\<cdot>\<close>)
notation restriction_fm (\<open>\<cdot>_ \<restriction> _ is _ \<cdot>\<close>)
notation transset_fm (\<open>\<cdot>_ is transitive\<cdot>\<close>)
notation limit_ordinal_fm (\<open>\<cdot>_ is limit\<cdot>\<close>)
notation finite_ordinal_fm (\<open>\<cdot>_ is finite ord\<cdot>\<close>)
notation omega_fm (\<open>\<cdot>_ is \<omega>\<cdot>\<close>)
notation cartprod_fm (\<open>\<cdot>_ \<times> _ is _\<cdot>\<close>)
notation Memrel_fm (\<open>\<cdot>Memrel'(_') is _\<cdot>\<close>)
notation quasinat_fm (\<open>\<cdot>_ is qnat\<cdot>\<close>)
  (* notation rtran_closure_mem_fm (\<open>\<cdot>{_,_} is _ \<cdot>\<close>)
notation rtran_closure_fm (\<open>\<cdot>{_,_} is _ \<cdot>\<close>)
notation tran_closure_fm (\<open>\<cdot>_ is  \<cdot>\<close>)
notation order_isomorphism_fm (\<open>\<cdot>{_,_} is _ \<cdot>\<close>) *)
notation Inl_fm (\<open>\<cdot>Inl'(_') is _ \<cdot>\<close>)
notation Inr_fm (\<open>\<cdot>Inr'(_') is _ \<cdot>\<close>)
notation pred_set_fm (\<open>\<cdot>_-predecessors of _ are _\<cdot>\<close>)


abbreviation
  fm_typedfun :: "[i,i,i] \<Rightarrow> i" (\<open>\<cdot>_ : _ \<rightarrow> _\<cdot>\<close>) where
  "fm_typedfun(f,A,B) \<equiv> typed_function_fm(A,B,f)"

abbreviation
  fm_surjection :: "[i,i,i] \<Rightarrow> i" (\<open>\<cdot>_ surjects _ to _\<cdot>\<close>) where
  "fm_surjection(f,A,B) \<equiv> surjection_fm(A,B,f)"

abbreviation
  fm_injection :: "[i,i,i] \<Rightarrow> i" (\<open>\<cdot>_ injects _ to _\<cdot>\<close>) where
  "fm_injection(f,A,B) \<equiv> injection_fm(A,B,f)"

abbreviation
  fm_bijection :: "[i,i,i] \<Rightarrow> i" (\<open>\<cdot>_ bijects _ to _\<cdot>\<close>) where
  "fm_bijection(f,A,B) \<equiv> bijection_fm(A,B,f)"

text\<open>We found it useful to have slightly different versions of some
results in ZF-Constructible:\<close>
lemma nth_closed :
  assumes "env\<in>list(A)" "0\<in>A"
  shows "nth(n,env)\<in>A"
  using assms unfolding nth_def by (induct env; simp)

lemma conj_setclass_model_iff_sats [iff_sats]:
  "[| 0 \<in> A; nth(i,env) = x; env \<in> list(A);
       P \<longleftrightarrow> sats(A,p,env); env \<in> list(A) |]
       ==> (P \<and> (##A)(x)) \<longleftrightarrow> sats(A, p, env)"
  "[| 0 \<in> A; nth(i,env) = x; env \<in> list(A);
       P \<longleftrightarrow> sats(A,p,env); env \<in> list(A) |]
       ==> ((##A)(x) \<and> P) \<longleftrightarrow> sats(A, p, env)"
  using nth_closed[of env A i]
  by auto

lemma conj_mem_model_iff_sats [iff_sats]:
  "[| 0 \<in> A; nth(i,env) = x; env \<in> list(A);
       P \<longleftrightarrow> sats(A,p,env); env \<in> list(A) |]
       ==> (P \<and> x \<in> A) \<longleftrightarrow> sats(A, p, env)"
  "[| 0 \<in> A; nth(i,env) = x; env \<in> list(A);
       P \<longleftrightarrow> sats(A,p,env); env \<in> list(A) |]
       ==> (x \<in> A \<and> P) \<longleftrightarrow> sats(A, p, env)"
  using nth_closed[of env A i]
  by auto

(* lemma [iff_sats]:
      "[| 0 \<in> A; nth(i,env) = x; env \<in> list(A);
       P \<longleftrightarrow> sats(A,p,env); env \<in> list(A) |]
       ==> (x \<in> A \<longleftrightarrow> P) \<longleftrightarrow> sats(A, p, env)"
      "[| 0 \<in> A; nth(i,env) = x; env \<in> list(A);
       P \<longleftrightarrow> sats(A,p,env); env \<in> list(A) |]
       ==> (P \<longleftrightarrow> x \<in> A) \<longleftrightarrow> sats(A, p, env)"

      "[| 0 \<in> A; nth(i,env) = x; env \<in> list(A);
       P \<longleftrightarrow> sats(A,p,env); env \<in> list(A) |]
       ==> (x \<in> A \<longrightarrow> P) \<longleftrightarrow> sats(A, p, env)"

  using nth_closed[of env A i]
  by auto *)

lemma mem_model_iff_sats [iff_sats]:
  "[| 0 \<in> A; nth(i,env) = x; env \<in> list(A)|]
       ==> (x\<in>A) \<longleftrightarrow> sats(A, Exists(Equal(0,0)), env)"
  using nth_closed[of env A i]
  by auto

lemma subset_iff_sats[iff_sats]:
  "nth(i, env) = x \<Longrightarrow> nth(j, env) = y \<Longrightarrow> i\<in>nat \<Longrightarrow> j\<in>nat \<Longrightarrow>
   env \<in> list(A) \<Longrightarrow> subset(##A, x, y) \<longleftrightarrow> sats(A, subset_fm(i, j), env)"
  using sats_subset_fm' by simp

lemma not_mem_model_iff_sats [iff_sats]:
  "[| 0 \<in> A; nth(i,env) = x; env \<in> list(A)|]
       ==> (\<forall> x . x \<notin> A) \<longleftrightarrow> sats(A, Neg(Exists(Equal(0,0))), env)"
  by auto

lemma top_iff_sats [iff_sats]:
  "env \<in> list(A) \<Longrightarrow> 0 \<in> A \<Longrightarrow> sats(A, Exists(Equal(0,0)), env)"
  by auto

lemma prefix1_iff_sats[iff_sats]:
  assumes
    "x \<in> nat" "env \<in> list(A)" "0 \<in> A" "a \<in> A"
  shows
    "a = nth(x,env) \<longleftrightarrow> sats(A, Equal(0,x+\<^sub>\<omega>1), Cons(a,env))"
    "nth(x,env) = a \<longleftrightarrow> sats(A, Equal(x+\<^sub>\<omega>1,0), Cons(a,env))"
    "a \<in> nth(x,env) \<longleftrightarrow> sats(A, Member(0,x+\<^sub>\<omega>1), Cons(a,env))"
    "nth(x,env) \<in> a \<longleftrightarrow> sats(A, Member(x+\<^sub>\<omega>1,0), Cons(a,env))"
  using assms nth_closed
  by simp_all

lemma prefix2_iff_sats[iff_sats]:
  assumes
    "x \<in> nat" "env \<in> list(A)" "0 \<in> A" "a \<in> A" "b \<in> A"
  shows
    "b = nth(x,env) \<longleftrightarrow> sats(A, Equal(1,x+\<^sub>\<omega>2), Cons(a,Cons(b,env)))"
    "nth(x,env) = b \<longleftrightarrow> sats(A, Equal(x+\<^sub>\<omega>2,1), Cons(a,Cons(b,env)))"
    "b \<in> nth(x,env) \<longleftrightarrow> sats(A, Member(1,x+\<^sub>\<omega>2), Cons(a,Cons(b,env)))"
    "nth(x,env) \<in> b \<longleftrightarrow> sats(A, Member(x+\<^sub>\<omega>2,1), Cons(a,Cons(b,env)))"
  using assms nth_closed
  by simp_all

lemma prefix3_iff_sats[iff_sats]:
  assumes
    "x \<in> nat" "env \<in> list(A)" "0 \<in> A" "a \<in> A" "b \<in> A" "c \<in> A"
  shows
    "c = nth(x,env) \<longleftrightarrow> sats(A, Equal(2,x+\<^sub>\<omega>3), Cons(a,Cons(b,Cons(c,env))))"
    "nth(x,env) = c \<longleftrightarrow> sats(A, Equal(x+\<^sub>\<omega>3,2), Cons(a,Cons(b,Cons(c,env))))"
    "c \<in> nth(x,env) \<longleftrightarrow> sats(A, Member(2,x+\<^sub>\<omega>3), Cons(a,Cons(b,Cons(c,env))))"
    "nth(x,env) \<in> c \<longleftrightarrow> sats(A, Member(x+\<^sub>\<omega>3,2), Cons(a,Cons(b,Cons(c,env))))"
  using assms nth_closed
  by simp_all

lemmas FOL_sats_iff = sats_Nand_iff sats_Forall_iff sats_Neg_iff sats_And_iff
  sats_Or_iff sats_Implies_iff sats_Iff_iff sats_Exists_iff

lemma nth_ConsI: "\<lbrakk>nth(n,l) = x; n \<in> nat\<rbrakk> \<Longrightarrow> nth(succ(n), Cons(a,l)) = x"
  by simp

lemmas nth_rules = nth_0 nth_ConsI nat_0I nat_succI
lemmas sep_rules = nth_0 nth_ConsI FOL_iff_sats function_iff_sats
  fun_plus_iff_sats successor_iff_sats
  omega_iff_sats FOL_sats_iff Replace_iff_sats

text\<open>Also a different compilation of lemmas (term\<open>sep_rules\<close>) used in formula
 synthesis\<close>
lemmas fm_defs =
  omega_fm_def limit_ordinal_fm_def empty_fm_def typed_function_fm_def
  pair_fm_def upair_fm_def domain_fm_def function_fm_def succ_fm_def
  cons_fm_def fun_apply_fm_def image_fm_def big_union_fm_def union_fm_def
  relation_fm_def composition_fm_def field_fm_def ordinal_fm_def range_fm_def
  transset_fm_def subset_fm_def Replace_fm_def

lemmas formulas_def [fm_definitions] = fm_defs
  is_iterates_fm_def iterates_MH_fm_def is_wfrec_fm_def is_recfun_fm_def is_transrec_fm_def
  is_nat_case_fm_def quasinat_fm_def number1_fm_def ordinal_fm_def finite_ordinal_fm_def
  cartprod_fm_def sum_fm_def Inr_fm_def Inl_fm_def
  formula_functor_fm_def
  Memrel_fm_def transset_fm_def subset_fm_def pre_image_fm_def restriction_fm_def
  list_functor_fm_def tl_fm_def quasilist_fm_def Cons_fm_def Nil_fm_def

lemmas sep_rules' [iff_sats]  = nth_0 nth_ConsI FOL_iff_sats function_iff_sats
  fun_plus_iff_sats omega_iff_sats

lemmas  more_iff_sats [iff_sats] = rtran_closure_iff_sats tran_closure_iff_sats
  is_eclose_iff_sats Inl_iff_sats Inr_iff_sats fun_apply_iff_sats cartprod_iff_sats
  Collect_iff_sats

end
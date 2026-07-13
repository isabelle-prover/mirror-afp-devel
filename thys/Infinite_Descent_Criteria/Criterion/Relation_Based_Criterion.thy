(*Certified Infinite Descent Criteria in Isabelle/HOL *)
(*Authors: Jamie Wright, Liron Cohen, Reuben Rowe and Andrei Popescu*)

(* Relation-Based Criterion for the Infinite Descent Property *)
subsection "Relation-based Criterion"

text \<open>Infinite Descent also admits an equivalent \emph{relation-based}
characterization.
This was first described in the context of size-change termination~\cite{LeeJB01} and later generalized and  refined~\cite{InfiniteDescent}.
The key idea is to summarize each finite path using a sloped relation, resulting in a finite abstraction that can be computed via a fixed-point computation.
Infinite Descent can then be decided by checking a simple condition on the sloped relations that summarize loops.\<close>

theory Relation_Based_Criterion
  imports VLA_Criterion
begin

lemma pigeonhole_infinite_seq:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes "finite (range f)"
  shows "\<exists>i j. i < j \<and> f i = f j"
proof (rule ccontr)
  assume "\<not> (\<exists>i j. i < j \<and> f i = f j)"
  hence "inj f" unfolding inj_on_def by (metis linorder_cases)
  hence "infinite (range f)" using finite_imageD infinite_UNIV_nat by blast
  with assms show "HOL.False" by contradiction
qed

context Sloped_Graph
begin

(* ======================================================================== *)
(* 1. OPERATIONS ON SLOPED RELATIONS                                        *)
(* ======================================================================== *)

definition MaxSl :: "slope set \<Rightarrow> slope" where 
"MaxSl sll \<equiv> if Decr \<in> sll then Decr else Main"

lemma MaxSl_singl[simp]: "MaxSl {sl} = sl"
unfolding MaxSl_def by (cases sl, auto)

definition leqSl ::  "('pos \<Rightarrow> 'pos \<Rightarrow> slope \<Rightarrow> bool) \<Rightarrow> 
   ('pos \<Rightarrow> 'pos \<Rightarrow> slope \<Rightarrow> bool) \<Rightarrow> bool"
where 
"leqSl P1 P2 \<equiv> \<forall>h h' sl1. P1 h h' sl1 \<longrightarrow> (\<exists>sl2. sl1 \<le> sl2 \<and> P2 h h' sl2)"

definition lessSl ::  "('pos \<Rightarrow> 'pos \<Rightarrow> slope \<Rightarrow> bool) \<Rightarrow> 
   ('pos \<Rightarrow> 'pos \<Rightarrow> slope \<Rightarrow> bool) \<Rightarrow> bool"
where "lessSl P1 P2 \<equiv> leqSl P1 P2 \<and> P1 \<noteq> P2"

lemma leqSl_refl: "leqSl P P" 
unfolding leqSl_def by auto

lemma leqSl_trans: "leqSl P1 P2 \<Longrightarrow> leqSl P2 P3 \<Longrightarrow> leqSl P1 P3" 
unfolding leqSl_def  
  by (meson dual_order.trans)

lemma leqSl_antisym_aux: 
assumes P12: "{P1,P2} \<subseteq> SlopedRels" and 12: "leqSl P1 P2" and 21: "leqSl P2 P1"
and 0: "P1 h h' sl"
shows "P2 h h' sl" 
proof-
  obtain sll where 1: "sl \<le> sll" and 11: "P2 h h' sll"
  using 0 12 unfolding leqSl_def by blast
  then obtain slll where 2: "sll \<le> slll" and 22: "P1 h h' slll"
  using 21 unfolding leqSl_def by blast
  have "sl = slll" using P12 0 22 unfolding SlopedRels_def by auto
  hence "sl = sll" using 1 2 by auto  
  thus ?thesis using 11 by auto
qed

lemma leqSl_antisym: 
assumes P12: "{P1,P2} \<subseteq> SlopedRels" and 12: "leqSl P1 P2" and 21: "leqSl P2 P1"
shows "P1 = P2"
using leqSl_antisym_aux assms  
  by fastforce

lemma lessSl_antisym: "{P1,P2} \<subseteq> SlopedRels \<Longrightarrow> \<not> (lessSl P1 P2 \<and> leqSl P2 P1)" 
using leqSl_antisym lessSl_def by auto 

lemma lessSl_trans: "{P1,P2,P3} \<subseteq> SlopedRels \<Longrightarrow> lessSl P1 P2 \<Longrightarrow> lessSl P2 P3 \<Longrightarrow> lessSl P1 P3" 
unfolding leqSl_def lessSl_def by (metis dual_order.trans insert_subset leqSl_antisym leqSl_def)


inductive transSl :: "('pos \<Rightarrow> 'pos \<Rightarrow> slope \<Rightarrow> bool) \<Rightarrow> ('pos \<Rightarrow> 'pos \<Rightarrow> slope \<Rightarrow> bool)" 
for K :: "'pos \<Rightarrow> 'pos \<Rightarrow> slope \<Rightarrow> bool" where 
 Base: "K P P' sl \<Longrightarrow> transSl K P P' sl"
|Step: "transSl K P P' sl1 \<Longrightarrow> K P' P'' sl2 \<Longrightarrow> transSl K P P'' (MaxSl {sl1,sl2})"

lemma transSl_mono: assumes "leqSl P Q"
shows "leqSl (transSl P) (transSl Q)"
unfolding le_fun_def leqSl_def apply clarsimp
subgoal for h1 h2 sl apply (induct rule: transSl.induct)
  subgoal using assms leqSl_def transSl.Base by metis
  subgoal  
    by (smt (verit, best) MaxSl_singl assms insert_absorb2 leqSl_def 
    less_eq_slope.elims(3) slope.exhaust transSl.Step) . .

definition initFrag :: 
"('pos \<Rightarrow> 'pos \<Rightarrow> slope \<Rightarrow> bool) set \<Rightarrow> ('pos \<Rightarrow> 'pos \<Rightarrow> slope \<Rightarrow> bool) set \<Rightarrow> bool"
where 
"initFrag LL' LL \<equiv> \<forall>R\<in> LL. \<exists>R' \<in> LL'. leqSl R' R"

lemma initFrag_Un: "initFrag L (LL1 \<union> LL2) \<longleftrightarrow> initFrag L LL1 \<and> initFrag L LL2"
unfolding initFrag_def by auto

lemma initFrag_trans: "initFrag L1 L2 \<Longrightarrow> initFrag L2 L3 \<Longrightarrow> initFrag L1 L3"
unfolding initFrag_def by (meson leqSl_trans)

definition Dt where 
"Dt LL \<equiv> {R \<in> LL. \<not> (\<exists>R' \<in> LL. lessSl R' R)}"

lemma Dt_incl: "Dt LL \<subseteq> LL" unfolding Dt_def by auto

lemma Dt_aux: "\<And>LL LL'. LL \<subseteq> LL' \<Longrightarrow> Dt LL \<subseteq> LL'" unfolding Dt_def by auto

lemma initFrag_Dt: 
assumes LL: "LL \<subseteq> SlopedRels" and f_LL: "finite LL"
shows "initFrag (Dt LL) LL"
unfolding initFrag_def proof safe
  fix R assume R[simp]: "R \<in> LL" 
  define f where "f = rec_nat R (\<lambda>n R. if R \<in> Dt LL then R else (SOME R'. R'\<in> LL \<and> lessSl R' R ))"
  have f: "f 0 = R" 
    "\<And>n. f (Suc n) = 
       (if f n \<in> Dt LL  then f n else (SOME R'. R' \<in> LL \<and> lessSl R' (f n)))"
  unfolding f_def by auto

  have ff: "\<And>n. f n \<in> LL \<and> 
     ((f n \<in> Dt LL \<and> f (Suc n) = f n) \<or> 
      (f n \<notin> Dt LL \<and> f (Suc n) \<in> LL \<and> lessSl (f (Suc n)) (f n)))"
  subgoal for n apply (induct n)    
    subgoal by (simp add: f Dt_def) (metis (no_types, lifting) someI)
    subgoal by (simp add: f Dt_def) (metis (no_types, lifting) someI) . . 

  hence f_UNIV_LL: "f ` UNIV \<subseteq> LL" by auto

  {assume "\<forall>n. f n \<notin> Dt LL"
   hence "\<forall>n. lessSl (f (Suc n)) (f n)" using ff by auto
   hence "\<forall>n i. lessSl (f (Suc (n+i))) (f n)" apply safe
    subgoal for n i apply(induct i, simp_all) 
   by (metis (no_types, opaque_lifting) assms(1) 
     empty_subsetI ff insert_subset leqSl_trans lessSl_antisym lessSl_def order_trans) .
   hence "inj f" unfolding inj_def lessSl_def  
     by (metis le_neq_implies_less less_natE nat_le_linear) 
   hence "HOL.False" using f_LL f_UNIV_LL  
     using infinite_iff_countable_subset by blast
  }
  then obtain n where n: "f n \<in> Dt LL" by auto

  hence "\<forall>n. leqSl (f (Suc n)) (f n)" using ff unfolding lessSl_def 
    by (metis leqSl_refl)
  hence "\<forall>n i. leqSl (f (Suc (n+i))) (f n)" apply safe
    subgoal for n i apply(induct i, simp_all) 
   by (metis (no_types, opaque_lifting) leqSl_trans) .
  hence 1: "leqSl (f (n)) R"  
    by (metis add_0 f(1) f(2) n)

  show "\<exists>R'\<in>Dt LL. leqSl R' R"
  apply(rule bexI[of _ "f n"])
     using ff n 1 unfolding lessSl_def by auto 
qed


(* ======================================================================== *)
(* 2. THE ORDINARY COMPOSITION CLOSURE (Ccl)                                *)
(* ======================================================================== *)

definition ccompSl :: "('pos \<Rightarrow> 'pos \<Rightarrow> slope \<Rightarrow> bool) \<Rightarrow> ('pos \<Rightarrow> 'pos \<Rightarrow> slope \<Rightarrow> bool) \<Rightarrow> 
  'pos \<Rightarrow> 'pos \<Rightarrow> slope \<Rightarrow> bool" 
where 
"ccompSl K1 K2 P P' sl \<equiv> \<exists>P'' sl1 sl2. sl = MaxSl {sl1, sl2} \<and> K1 P P'' sl1 \<and> K2 P'' P' sl2"

lemma finite_slope_set: "finite (S::slope set)"
by (metis (full_types) finite.simps insert_iff rev_finite_subset slope.exhaust subsetI)

lemma ccompSl_mono: "leqSl P1 Q1 \<Longrightarrow> leqSl P2 Q2 \<Longrightarrow> leqSl (ccompSl P1 P2) (ccompSl Q1 Q2)"
unfolding ccompSl_def le_fun_def MaxSl_def leqSl_def
by (smt (z3) insert_iff less_eq_slope.simps(3) slope.exhaust)

lemma ccompSl_SlopeRels: 
  "{P,P'} \<subseteq> SlopedRels \<Longrightarrow> ccompSl P P' \<in> SlopedRels"
  unfolding SlopedRels_def ccompSl_def MaxSl_def oops

fun Ccl_iter :: "nat \<Rightarrow> 'node \<Rightarrow> 'node \<Rightarrow> ('pos \<Rightarrow> 'pos \<Rightarrow> slope \<Rightarrow> bool) set" where 
 "Ccl_iter 0 nd nd' = (if {nd,nd'} \<subseteq> Node \<and> edge nd nd' then {\<lambda>P P' sl. RR (nd,P) (nd',P') sl} else {})"
|"Ccl_iter (Suc i) nd nd' = 
  Ccl_iter i nd nd' \<union> 
  {ccompSl K1 K2 | K1 K2 nd''. nd'' \<in> Node \<and> K1 \<in> Ccl_iter i nd nd'' \<and> K2 \<in> Ccl_iter i nd'' nd'}"

lemma Ccl_iter_nodes: "nd \<notin> Node \<or> nd' \<notin> Node  \<Longrightarrow> Ccl_iter i nd nd' = {}"
  apply(induct i arbitrary: nd nd') by auto 


lemma Ccl_iter_PosOf: 
"K \<in> Ccl_iter i nd nd' \<Longrightarrow> K P P' sl \<Longrightarrow> P \<in> PosOf nd \<and> P' \<in> PosOf nd'"
apply(cases "{nd,nd'} \<subseteq> Node")
  subgoal apply(induct i arbitrary: nd nd' K sl P P')
    using RR_PosOf by (auto split: if_splits simp: ccompSl_def) 
  subgoal using Ccl_iter_nodes by auto .

lemma Ccl_iter_Suc_mono: "Ccl_iter i nd nd' \<subseteq> Ccl_iter (Suc i) nd nd'"
by auto

lemma Ccl_iter_mono: "i \<le> j \<Longrightarrow> Ccl_iter i nd nd' \<subseteq> Ccl_iter j nd nd'"
apply(induct j)
  subgoal by auto
  subgoal using Ccl_iter_Suc_mono le_SucE by blast .

lemma Ccl_iter_Suc_stable: 
assumes "Ccl_iter (Suc i) = Ccl_iter i"
shows "Ccl_iter (Suc (Suc i)) = Ccl_iter i" 
using assms unfolding fun_eq_iff Ccl_iter.simps(2) by auto 

lemma Ccl_iter_stable: 
assumes 1: "Ccl_iter (Suc i) = Ccl_iter i" and 2: "j \<ge> i"
shows "Ccl_iter j = Ccl_iter i" 
using assms apply(induct "j-i" arbitrary: j i)
  subgoal by auto   
  subgoal for x j   
    by (metis Suc_diff_le Suc_leD diff_diff_cancel diff_le_self Ccl_iter_Suc_stable) .

lemma Ccl_iter_su_PosOf: 
"Ccl_iter i nd nd' \<subseteq> 
 {R . \<forall>h h' sl. (h,h') \<notin> PosOf nd \<times> PosOf nd' \<longrightarrow> \<not> R h h' sl}"
apply(induct i arbitrary: nd nd') 
  using RR_PosOf Ccl_iter_PosOf ccompSl_def by auto

lemma finite_PosOf_prod: 
assumes "nd \<in> Node" "nd' \<in> Node"
shows "finite {R . \<forall>h h' sl. (h::'pos,h'::'pos) \<notin> PosOf nd \<times> PosOf nd' 
                    \<longrightarrow> \<not> R h h' (sl::slope)}"
(is "finite ?A")
proof-
  define f where "f \<equiv> \<lambda>R. {(h::'pos,h'::'pos,sl::slope) | h h' sl. R h h' sl }"
  have 2: "inj_on f ?A"
    unfolding inj_on_def f_def by fastforce 
  have 3: "f ` ?A \<subseteq> Pow (PosOf nd \<times> PosOf nd' \<times> (UNIV::slope set))"
    (is "_ \<subseteq> ?B")
    unfolding f_def by auto
  have "finite ?B" unfolding finite_Pow_iff apply(intro finite_cartesian_product)
    using PosOf_finite assms finite_slope_set by auto
  thus ?thesis using 2 3 by (meson inj_on_finite)
qed

lemma finite_Ccl_iter:
shows "finite (Ccl_iter i nd nd')"  
by (metis (no_types, lifting) Ccl_iter_nodes Ccl_iter_su_PosOf 
     finite.simps finite_PosOf_prod rev_finite_subset)


lemma Ccl_iter_Suc_stops: 
"\<exists>i. Ccl_iter (Suc i) = Ccl_iter i"
proof-
  {assume "\<forall>i. \<exists>nd nd'. Ccl_iter (Suc i) nd nd' \<noteq> Ccl_iter i nd nd'"
   hence "\<forall>i. \<exists>nd nd'. (nd,nd') \<in> Node \<times> Node \<and> Ccl_iter (Suc i) nd nd' \<noteq> Ccl_iter i nd nd'"
      by (metis Ccl_iter_nodes SigmaI)
   hence "\<forall>i. \<exists>ndd. ndd \<in> Node \<times> Node \<and> Ccl_iter (Suc i) (fst ndd) (snd ndd) \<noteq> Ccl_iter i (fst ndd) (snd ndd)"
     by (metis fst_eqD snd_eqD)
   then obtain ndi where 0: 
   "\<forall>i.  ndi i \<in> Node \<times> Node \<and> 
         Ccl_iter (Suc i) (fst (ndi (i::nat))) (snd (ndi i)) \<noteq> Ccl_iter i (fst (ndi i)) (snd (ndi i))"
     by metis
   hence r: "range ndi \<subseteq> Node \<times> Node" unfolding image_def by blast
   hence "finite (range ndi)" by (simp add: Node_finite finite_subset)
   moreover have "{{i. ndi i = ndd} | ndd . ndd \<in> range ndi} = 
     (\<lambda>ndd. {i. ndi i = ndd}) ` (range ndi)" (is "?A = _") by auto
   ultimately have 1: "finite ?A" by simp
   have "UNIV = \<Union> ?A" 
    by auto (metis (mono_tags) mem_Collect_eq range_eqI surj_pair)
   then obtain ndd where ndd: "ndd \<in> range ndi" and inf: "infinite {i. ndi i = ndd}" 
     using finite_Union[OF 1] by auto
   hence ndd_in: "ndd \<in> Node \<times> Node" using r by auto
   define nd nd' where "nd = fst ndd" and "nd' = snd ndd" 
   define I where "I = {i. ndi i = ndd}"
   have nd_nd': "nd \<in> Node \<and> nd' \<in> Node" and I: "infinite I" using inf unfolding I_def 
     using ndd_in unfolding nd_def nd'_def by auto 
   
   hence "\<forall>i\<in>I. \<exists> R. R \<in> Ccl_iter (Suc i) nd nd' \<and> R \<notin> Ccl_iter i nd nd'"
    using Ccl_iter_mono "0" I_def nd'_def nd_def by fastforce
   then obtain Ri where 0: "\<forall>i\<in>I. Ri i \<in> Ccl_iter (Suc i) nd nd' \<and> Ri i \<notin> Ccl_iter i nd nd'"
    by metis
   hence "\<forall>i j. {i,j} \<subseteq> I \<and> i < j \<longrightarrow> Ri i \<noteq> Ri j"  
     by (metis Ccl_iter_mono in_mono insert_subset less_eq_Suc_le) 
   hence "inj_on Ri I"  
     by (metis (mono_tags, opaque_lifting) empty_subsetI insert_subset linorder_inj_onI nle_le)
   hence "infinite (image Ri I)" using I finite_imageD by blast
   moreover have "image Ri I \<subseteq> 
   {R . \<forall>h h' sl. (h::'pos,h'::'pos) \<notin> PosOf nd \<times> PosOf nd' 
                    \<longrightarrow> \<not> R h h' (sl::slope)}" (is "_ \<subseteq> ?A")
     using 0  Ccl_iter_su_PosOf by blast 
   moreover have "finite ?A" 
     using nd_nd' finite_PosOf_prod by presburger
   ultimately have "HOL.False"  
     by (meson infinite_super)
  }
  thus ?thesis by blast
qed

lemma Ccl_iter_stops: "\<exists>i. \<forall>j \<ge> i. Ccl_iter j = Ccl_iter i"
using Ccl_iter_Suc_stops apply safe
subgoal for i apply (rule exI[of _ i])
using Ccl_iter_stable by blast .

definition Ccl :: "'node \<Rightarrow> 'node \<Rightarrow> ('pos \<Rightarrow> 'pos \<Rightarrow> slope \<Rightarrow> bool) set" where 
"Ccl nd nd' \<equiv> \<Union>i. Ccl_iter i nd nd'"


lemma Ccl_nodes: "nd \<notin> Node \<or> nd' \<notin> Node \<Longrightarrow> Ccl nd nd' = {}"
by (simp add: Ccl_def Ccl_iter_nodes)

lemma Ccl_eq_some_Ccl_iter: "\<exists>i. Ccl = Ccl_iter i"
proof-
  obtain i where 0: "\<forall>j \<ge> i. Ccl_iter j = Ccl_iter i" 
  using Ccl_iter_stops by auto
  hence 00: "Ccl_iter (Suc i) = Ccl_iter i" 
  using le_Suc_eq by blast
  have "\<And>j nd nd'. Ccl_iter j nd nd' \<subseteq> Ccl_iter i nd nd'"
  subgoal for j nd nd' apply(induct j arbitrary: nd nd') 
    subgoal using Ccl_iter_mono by blast
    subgoal by simp (smt (verit, ccfv_threshold) "00" Ccl_iter.simps(2) UnCI in_mono 
         mem_Collect_eq subsetI) . .
  thus ?thesis unfolding Ccl_def apply(intro exI[of _ i]) 
  by fastforce
qed

lemma Ccl_RR[simp,intro!]:
"{nd,nd'} \<subseteq> Node \<Longrightarrow> edge nd nd' \<Longrightarrow> (\<lambda>P P' sl. RR (nd,P) (nd',P') sl) \<in> Ccl nd nd'"
unfolding Ccl_def 
by simp (metis empty_subsetI insert_subset Ccl_iter.simps(1) order_refl)

lemma Ccl_ccompSl[intro]:
"nd'' \<in> Node \<Longrightarrow> K1 \<in> Ccl nd nd'' \<Longrightarrow> K2 \<in> Ccl nd'' nd'
 \<Longrightarrow> ccompSl K1 K2 \<in> Ccl nd nd'" 
unfolding Ccl_def apply clarsimp
  subgoal for i j apply(rule exI[of _ "Suc (max i j)"]) 
  by simp (metis in_mono Ccl_iter_mono max.cobounded1 max.cobounded2) .


definition "TransitiveLoopingCcl \<equiv> \<forall>nd\<in>Node. \<forall>K\<in>Ccl nd nd. (\<exists>P. transSl K P P Decr)"

(* ======================================================================== *)
(* 3. THE DOWNWARD CLOSURE (Dcl)                                            *)
(* ======================================================================== *)

definition "compSl K1 K2 P P' sl \<equiv> 
  (\<exists>P'' sl1 sl2. sl = MaxSl {sl1, sl2} \<and> K1 P P'' sl1 \<and> K2 P'' P' sl2) \<and> 
  sl = Max {sl. \<exists>P'' sl1 sl2. sl = MaxSl {sl1, sl2} \<and> K1 P P'' sl1 \<and> K2 P'' P' sl2}"

lemma compSl_SlopeRels: 
"{P,P'} \<subseteq> SlopedRels \<Longrightarrow> compSl P P' \<in> SlopedRels"
unfolding SlopedRels_def compSl_def MaxSl_def by auto

lemma compSl_leqSl_ccompSl: "leqSl (compSl K1 K2) (ccompSl K1 K2)"
unfolding leqSl_def compSl_def ccompSl_def MaxSl_def by auto

lemma ccompSl_leqSl_compSl: "leqSl (ccompSl K1 K2) (compSl K1 K2)"
unfolding leqSl_def proof safe
  fix h h' sl assume "ccompSl K1 K2 h h' sl"
  then obtain P'' sl1 sl2 where 0: "sl = MaxSl {sl1, sl2}"
  "K1 h P'' sl1 \<and> K2 P'' h' sl2" unfolding ccompSl_def by auto
  let ?A = "{sl. \<exists>P'' sl1 sl2. sl = MaxSl {sl1, sl2} \<and> K1 h P'' sl1 \<and> K2 P'' h' sl2}"
  define sll where sll: "sll = Max ?A"
  have 1: "sl \<le> sll" unfolding sll apply(rule Max_ge)
  using 0 finite_slope_set by auto
  have 2: "sll \<in> ?A" unfolding sll apply(rule Max_in) using 0 finite_slope_set by auto
  show "\<exists>sll\<ge>sl. compSl K1 K2 h h' sll" unfolding compSl_def
  apply(rule exI[of _ sll]) using 0 1 2 unfolding sll by auto
qed

fun Dcl_iter :: "nat \<Rightarrow> 'node \<Rightarrow> 'node \<Rightarrow> ('pos \<Rightarrow> 'pos \<Rightarrow> slope \<Rightarrow> bool) set" where 
 "Dcl_iter 0 nd nd' = (if {nd,nd'} \<subseteq> Node \<and> edge nd nd' then {\<lambda>P P' sl. RR (nd,P) (nd',P') sl} else {})"
|"Dcl_iter (Suc i) nd nd' = 
  Dt (Dcl_iter i nd nd' \<union> 
  {compSl K1 K2 | K1 K2 nd''. nd'' \<in> Node \<and> K1 \<in> Dcl_iter i nd nd'' \<and> K2 \<in> Dcl_iter i nd'' nd'})"

lemma finite_compSl_set:
fixes D E::"'node \<Rightarrow> ('pos\<Rightarrow>'pos\<Rightarrow>slope\<Rightarrow>bool) set"
assumes fin: "\<And>nd''. finite (D nd'') \<and> finite (E nd'')"
shows "finite
  {compSl K1 K2 |K1 K2.
   \<exists>nd''. nd'' \<in> Node \<and> K1 \<in> D nd'' \<and> K2 \<in> E nd''}"
(is "finite ?A")
proof-
  let ?B = "\<Union> { D nd'' \<times> E nd'' | nd''. nd'' \<in> Node}"
  define f where "f \<equiv> \<lambda> (K_1_K_2::('pos\<Rightarrow>'pos\<Rightarrow>slope\<Rightarrow>bool)\<times>('pos\<Rightarrow>'pos\<Rightarrow>slope\<Rightarrow>bool)). 
    compSl (fst K_1_K_2) (snd K_1_K_2)"
  have "?A \<subseteq> f ` ?B" unfolding f_def image_def apply safe
    subgoal for _ K1 K2 nd'' apply(rule bexI[of _ "(K1, K2)"]) by auto .
  moreover have "finite ?B" apply(rule finite_Union)
    subgoal using Node_finite by auto
    subgoal using fin by blast . 
  ultimately show "finite ?A"  
    by (meson finite_imageI finite_subset)
qed

lemma finite_Dcl_iter: "finite (Dcl_iter i nd nd')" 
apply(induct i arbitrary: nd nd')
  subgoal by auto
  subgoal for i nd nd' apply (auto intro!: finite_subset[OF Dt_incl] 
    finite_compSl_set[of "Dcl_iter i nd" "\<lambda>nd''. Dcl_iter i nd'' nd'"]) . .

lemma finite_compSl_Dcl_iter:
"finite {compSl K1 K2 |K1 K2. \<exists>nd''. nd'' \<in> Node \<and> K1 \<in> Dcl_iter i nd nd'' \<and> K2 \<in> Dcl_iter i nd'' nd'}"
apply(rule finite_compSl_set) by (simp add: finite_Dcl_iter)

lemma Dcl_iter_SlopedRels: "Dcl_iter i nd nd' \<subseteq> SlopedRels"
proof(induct i arbitrary: nd nd')
  case 0 thus ?case using RR_SlopeRels by auto  
next
  case (Suc i)
  thus ?case using compSl_SlopeRels Dt_incl by simp (blast intro: Dt_aux)
qed


lemma Dcl_iter_subseqI:
  assumes "\<And>R h h' sl. R \<in> Dcl_iter (Suc i) nd nd' \<Longrightarrow>
           (h, h') \<notin> PosOf nd \<times> PosOf nd' \<Longrightarrow>
           R h h' sl \<Longrightarrow>
           HOL.False"
shows "Dcl_iter (Suc i) nd nd' \<subseteq> {R. \<forall>h h' sl. (h, h') \<notin> PosOf nd \<times> PosOf nd' \<longrightarrow> \<not> R h h' sl}"
  using assms by auto

lemma Dcl_iter_su_PosOf: 
"Dcl_iter i nd nd' \<subseteq> 
 {R . \<forall>h h' sl. (h,h') \<notin> PosOf nd \<times> PosOf nd' \<longrightarrow> \<not> R h h' sl}"
proof (induct i arbitrary: nd nd')
  case 0 thus ?case using RR_PosOf by auto
next
  case (Suc i nd nd')
  show ?case
  proof (rule Dcl_iter_subseqI)
    fix R h h' sl
    assume R_in: "R \<in> Dcl_iter (Suc i) nd nd'" 
       and h_notin: "(h, h') \<notin> PosOf nd \<times> PosOf nd'" 
       and R_h: "R h h' sl"
       
    from R_in have "R \<in> Dt (Dcl_iter i nd nd' \<union> {compSl K1 K2 |K1 K2 nd''. nd'' \<in> Node \<and> K1 \<in> Dcl_iter i nd nd'' \<and> K2 \<in> Dcl_iter i nd'' nd'})"
      by simp
    hence "R \<in> Dcl_iter i nd nd' \<union> {compSl K1 K2 |K1 K2 nd''. nd'' \<in> Node \<and> K1 \<in> Dcl_iter i nd nd'' \<and> K2 \<in> Dcl_iter i nd'' nd'}"
      using Dt_incl by blast
    thus "HOL.False"
    proof
      assume "R \<in> Dcl_iter i nd nd'"
      with Suc[of nd nd'] h_notin R_h show "HOL.False" by blast
    next
      assume "R \<in> {compSl K1 K2 |K1 K2 nd''. nd'' \<in> Node \<and> K1 \<in> Dcl_iter i nd nd'' \<and> K2 \<in> Dcl_iter i nd'' nd'}"
      then obtain K1 K2 nd'' where "R = compSl K1 K2" 
        and "K1 \<in> Dcl_iter i nd nd''" 
        and "K2 \<in> Dcl_iter i nd'' nd'" by blast
      with R_h obtain P'' sl1 sl2 where "K1 h P'' sl1" and "K2 P'' h' sl2"
        unfolding compSl_def by blast
      
      have "h \<in> PosOf nd" 
        using `K1 \<in> Dcl_iter i nd nd''` `K1 h P'' sl1` Suc[of nd nd''] by blast
      moreover have "h' \<in> PosOf nd'" 
        using `K2 \<in> Dcl_iter i nd'' nd'` `K2 P'' h' sl2` Suc[of nd'' nd'] by blast
      ultimately have "(h, h') \<in> PosOf nd \<times> PosOf nd'" by simp
      with h_notin show "HOL.False" by contradiction
    qed
  qed
qed

lemma Dcl_iter_nodes_out:
  "nd \<notin> Node \<or> nd' \<notin> Node \<Longrightarrow> Dcl_iter i nd nd' = {}"
  apply(induct i arbitrary: nd nd')
  subgoal by auto
  subgoal by (auto simp add: Dt_def) .


lemma initFrag_Dt_trans: 
"L \<subseteq> SlopedRels \<Longrightarrow> finite L \<Longrightarrow> initFrag L L' \<Longrightarrow> initFrag (Dt L) L'"
using initFrag_Dt initFrag_trans by blast

lemma Dt_initFrag_aux: "initFrag LL LL' \<Longrightarrow> initFrag LL (Dt LL')"
  using Dt_incl initFrag_def by auto

lemma initFrag_Un_left: "initFrag LL LL' \<Longrightarrow> initFrag (LL \<union> KK) LL'"
using initFrag_def by auto


(* ======================================================================== *)
(* 4. MUTUAL INITIAL FRAGMENTS AND Dcl_iter STABILIZATION                   *)
(* ======================================================================== *)

lemma Dcl_iter_initFrag_Ccl_iter: "initFrag (Dcl_iter i nd nd') (Ccl_iter i nd nd')"
proof(induct i arbitrary: nd nd')
  case 0 thus ?case unfolding initFrag_def leqSl_def by auto
next
  case(Suc i nd nd')
  show ?case unfolding Ccl_iter.simps initFrag_Un proof safe
    have "initFrag
     (Dcl_iter i nd nd' \<union>
      {compSl K1 K2 |K1 K2.
       \<exists>nd''. nd'' \<in> Node \<and> K1 \<in> Dcl_iter i nd nd'' \<and> K2 \<in> Dcl_iter i nd'' nd'})
     (Ccl_iter i nd nd')"
      using Suc by (meson initFrag_Un_left)

    then show "initFrag (Dcl_iter (Suc i) nd nd') (Ccl_iter i nd nd')"
      using Suc unfolding initFrag_Un 
      using finite_compSl_Dcl_iter finite_Dcl_iter initFrag_trans Dcl_iter_SlopedRels
      by(auto intro!: initFrag_Dt_trans compSl_SlopeRels,(blast+))
  next
    note 1 = Dcl_iter.simps(2)[of i nd nd'] 
    show "initFrag (Dcl_iter (Suc i) nd nd')
      {ccompSl K1 K2 | K1 K2 nd''. nd'' \<in> Node \<and> K1 \<in> Ccl_iter i nd nd'' \<and> K2 \<in> Ccl_iter i nd'' nd'}"
      unfolding 1
      apply(rule initFrag_Dt_trans)
        subgoal using Dcl_iter_SlopedRels by (auto intro!: compSl_SlopeRels)
        subgoal unfolding finite_Un using finite_Dcl_iter finite_compSl_Dcl_iter by auto
        subgoal unfolding initFrag_def 
          apply(intro ballI, clarsimp) 
          apply(drule Suc[unfolded initFrag_def, rule_format])+
          apply safe 
          subgoal for K1 K2 nd'' K1' K2' apply(rule bexI[of _ "compSl K1' K2'"]) 
             by (auto simp: ccompSl_mono,meson compSl_leqSl_ccompSl ccompSl_mono leqSl_trans) . . 
  qed
qed

lemma Ccl_iter_initFrag_Dcl_iter: "initFrag (Ccl_iter i nd nd') (Dcl_iter i nd nd')"
proof(induct i arbitrary: nd nd')
  case 0 thus ?case unfolding initFrag_def leqSl_def by auto
next
  case(Suc i nd nd')
  show ?case unfolding Dcl_iter.simps apply(rule Dt_initFrag_aux) 
  unfolding initFrag_Un proof safe
    show "initFrag (Ccl_iter (Suc i) nd nd') (Dcl_iter i nd nd')" apply simp 
    apply(rule initFrag_Un_left) using Suc by auto 
  next
    note 1 = Dcl_iter.simps(2)[of i nd nd'] 
    show "initFrag (Ccl_iter (Suc i) nd nd')
      {compSl K1 K2 | K1 K2 nd''. nd'' \<in> Node \<and> K1 \<in> Dcl_iter i nd nd'' \<and> K2 \<in> Dcl_iter i nd'' nd'}"
      unfolding 1 apply simp unfolding initFrag_def 
      apply(intro ballI, clarsimp)
      apply(drule Suc[unfolded initFrag_def, rule_format])+
      apply safe subgoal for K1 K2 nd'' K1' K2'
      apply(rule bexI[of _ "ccompSl K1' K2'"])
        subgoal by (meson ccompSl_leqSl_compSl ccompSl_mono compSl_leqSl_ccompSl leqSl_trans)  
        subgoal by  auto . .
  qed
qed



lemma Dcl_iter_finite_range:
  assumes "nd \<in> Node" "nd' \<in> Node"
  shows "finite (range (\<lambda>i. Dcl_iter i nd nd'))"
proof -
  let ?S = "{R. (\<forall>h h' (sl::slope). (h, h') \<notin> PosOf nd \<times> PosOf nd' \<longrightarrow> \<not> R h h' sl)}"
  have "range (\<lambda>i. Dcl_iter i nd nd') \<subseteq> Pow ?S"
    using Dcl_iter_su_PosOf by blast
  moreover have "finite (Pow ?S)"
    unfolding finite_Pow_iff using finite_PosOf_prod[OF assms] .
  ultimately show ?thesis by (metis (mono_tags, lifting) rev_finite_subset)
qed

lemma Dcl_iter_finite_range_all:
  "finite (range (\<lambda>i. Dcl_iter i nd nd'))"
proof (cases "nd \<in> Node \<and> nd' \<in> Node")
  case True thus ?thesis using Dcl_iter_finite_range by auto
next
  case False
  hence "\<forall>i. Dcl_iter i nd nd' = {}" using Dcl_iter_nodes_out by auto
  hence "range (\<lambda>i. Dcl_iter i nd nd') = {{}}" by auto
  thus ?thesis by simp
qed

lemma Dt_idem: "Dt (Dt X) = Dt X"
  unfolding Dt_def by auto

lemma Dcl_iter_thin_0: "Dt (Dcl_iter 0 nd nd') = Dcl_iter 0 nd nd'"
proof (cases "{nd,nd'} \<subseteq> Node \<and> edge nd nd'")
  case True
  hence "Dcl_iter 0 nd nd' = {\<lambda>P P' sl. RR (nd, P) (nd', P') sl}" by simp
  thus ?thesis unfolding Dt_def lessSl_def leqSl_def by auto
next
  case False
  hence "Dcl_iter 0 nd nd' = {}" by simp
  thus ?thesis unfolding Dt_def by auto
qed

lemma Dcl_iter_thin: "Dt (Dcl_iter i nd nd') = Dcl_iter i nd nd'"
proof (cases i)
  case 0 thus ?thesis using Dcl_iter_thin_0 by simp
next
  case (Suc n)
  have "Dcl_iter (Suc n) nd nd' = Dt (Dcl_iter n nd nd' \<union> {compSl K1 K2 |K1 K2 nd''. nd'' \<in> Node \<and> K1 \<in> Dcl_iter n nd nd'' \<and> K2 \<in> Dcl_iter n nd'' nd'})"
    by simp
  thus ?thesis using Dt_idem Suc by simp
qed

lemma Dcl_iter_initFrag_Suc:
  "initFrag (Dcl_iter (Suc i) nd nd') (Dcl_iter i nd nd')"
proof -
  let ?X = "Dcl_iter i nd nd' \<union> {compSl K1 K2 |K1 K2 nd''. nd'' \<in> Node \<and> K1 \<in> Dcl_iter i nd nd'' \<and> K2 \<in> Dcl_iter i nd'' nd'}"
  have "?X \<subseteq> SlopedRels" 
    using Dcl_iter_SlopedRels compSl_SlopeRels by blast
  moreover have "finite ?X"
    using finite_Dcl_iter finite_compSl_Dcl_iter by auto
  ultimately have "initFrag (Dt ?X) ?X"
    using initFrag_Dt by blast
  thus ?thesis
    unfolding Dcl_iter.simps initFrag_Un by blast
qed

lemma Dcl_iter_initFrag_le:
  "i \<le> j \<Longrightarrow> initFrag (Dcl_iter j nd nd') (Dcl_iter i nd nd')"
  apply(induct j)
  subgoal by (simp add: initFrag_def leqSl_refl)
  subgoal for j 
    using Ccl_iter_initFrag_Dcl_iter Dcl_iter_initFrag_Ccl_iter
      Dcl_iter_initFrag_Suc initFrag_trans le_Suc_eq
    by blast .

lemma Dt_initFrag_antisym:
  assumes "A \<subseteq> SlopedRels" "B \<subseteq> SlopedRels"
  and "Dt A = A" "Dt B = B"
  and AB: "initFrag A B" and BA: "initFrag B A"
  shows "A = B"
proof (rule subset_antisym; rule subsetI)
  fix R assume "R \<in> A"
  from `R \<in> A` BA obtain R' where "R' \<in> B" and "leqSl R' R" unfolding initFrag_def by blast
  from `R' \<in> B` AB obtain R'' where "R'' \<in> A" and "leqSl R'' R'" unfolding initFrag_def by blast
  have "leqSl R'' R" using `leqSl R'' R'` `leqSl R' R` leqSl_trans by blast
  have "R'' = R" 
  proof (rule ccontr)
    assume "R'' \<noteq> R"
    hence "lessSl R'' R" using `leqSl R'' R` unfolding lessSl_def by simp
    with `R'' \<in> A` `R \<in> A` have "R \<notin> Dt A" unfolding Dt_def by blast
    with `Dt A = A` `R \<in> A` show "HOL.False" by simp
  qed
  hence "leqSl R R'" using `leqSl R'' R'` by simp
  have "R = R'" using `leqSl R R'` `leqSl R' R` `R \<in> A` `R' \<in> B` assms(1,2) leqSl_antisym by blast
  thus "R \<in> B" using `R' \<in> B` by simp
next
  fix R assume "R \<in> B"
  from `R \<in> B` AB obtain R' where "R' \<in> A" and "leqSl R' R" unfolding initFrag_def by blast
  from `R' \<in> A` BA obtain R'' where "R'' \<in> B" and "leqSl R'' R'" unfolding initFrag_def by blast
  have "leqSl R'' R" using `leqSl R'' R'` `leqSl R' R` leqSl_trans by blast
  have "R'' = R" 
  proof (rule ccontr)
    assume "R'' \<noteq> R"
    hence "lessSl R'' R" using `leqSl R'' R` unfolding lessSl_def by simp
    with `R'' \<in> B` `R \<in> B` have "R \<notin> Dt B" unfolding Dt_def by blast
    with `Dt B = B` `R \<in> B` show "HOL.False" by simp
  qed
  hence "leqSl R R'" using `leqSl R'' R'` by simp
  have "R = R'" using `leqSl R R'` `leqSl R' R` `R \<in> B` `R' \<in> A` assms(1,2) leqSl_antisym by blast
  thus "R \<in> A" using `R' \<in> A` by simp
qed

lemma Dcl_iter_Suc_stops_pair: "\<exists>i. Dcl_iter (Suc i) nd nd' = Dcl_iter i nd nd'"
proof -
  have "finite (range (\<lambda>i. Dcl_iter i nd nd'))" by (rule Dcl_iter_finite_range_all)
  then obtain i j where "i < j" and eq: "Dcl_iter i nd nd' = Dcl_iter j nd nd'"
    using pigeonhole_infinite_seq by blast
  
  have "initFrag (Dcl_iter j nd nd') (Dcl_iter (Suc i) nd nd')"
    using `i < j` Dcl_iter_initFrag_le Suc_leI by blast
  moreover have "initFrag (Dcl_iter (Suc i) nd nd') (Dcl_iter i nd nd')"
    using Dcl_iter_initFrag_Suc by simp
  ultimately have BA: "initFrag (Dcl_iter i nd nd') (Dcl_iter (Suc i) nd nd')"
    unfolding eq[symmetric] by simp
    
  have AB: "initFrag (Dcl_iter (Suc i) nd nd') (Dcl_iter i nd nd')"
    using Dcl_iter_initFrag_Suc by simp
    
  have "Dcl_iter i nd nd' \<subseteq> SlopedRels" and "Dcl_iter (Suc i) nd nd' \<subseteq> SlopedRels"
    using Dcl_iter_SlopedRels by blast+
  moreover have "Dt (Dcl_iter i nd nd') = Dcl_iter i nd nd'" 
    and "Dt (Dcl_iter (Suc i) nd nd') = Dcl_iter (Suc i) nd nd'"
    using Dcl_iter_thin by blast+
  ultimately have "Dcl_iter (Suc i) nd nd' = Dcl_iter i nd nd'"
    using Dt_initFrag_antisym[of "Dcl_iter (Suc i) nd nd'" "Dcl_iter i nd nd'"] AB BA by simp
  thus ?thesis by blast
qed

lemma Dcl_iter_eq_implies_Suc_eq:
  assumes "i < j" "Dcl_iter i nd nd' = Dcl_iter j nd nd'"
  shows "Dcl_iter (Suc i) nd nd' = Dcl_iter i nd nd'"
proof -
  have "initFrag (Dcl_iter j nd nd') (Dcl_iter (Suc i) nd nd')"
    using \<open>i < j\<close> Dcl_iter_initFrag_le Suc_leI by blast
  moreover have "initFrag (Dcl_iter (Suc i) nd nd') (Dcl_iter i nd nd')"
    using Dcl_iter_initFrag_Suc by simp
  ultimately have BA: "initFrag (Dcl_iter i nd nd') (Dcl_iter (Suc i) nd nd')"
    unfolding assms(2)[symmetric] by simp
  have AB: "initFrag (Dcl_iter (Suc i) nd nd') (Dcl_iter i nd nd')"
    using Dcl_iter_initFrag_Suc by simp
  have "Dcl_iter i nd nd' \<subseteq> SlopedRels" and "Dcl_iter (Suc i) nd nd' \<subseteq> SlopedRels"
    using Dcl_iter_SlopedRels by blast+
  moreover have "Dt (Dcl_iter i nd nd') = Dcl_iter i nd nd'" 
    and "Dt (Dcl_iter (Suc i) nd nd') = Dcl_iter (Suc i) nd nd'"
    using Dcl_iter_thin by blast+
  ultimately show ?thesis
    using Dt_initFrag_antisym[of "Dcl_iter (Suc i) nd nd'" "Dcl_iter i nd nd'"] AB BA by simp
qed

lemma Dcl_iter_Suc_stops: "\<exists>i. Dcl_iter (Suc i) = Dcl_iter i"
proof (rule ccontr)
  assume "\<not>(\<exists>i. Dcl_iter (Suc i) = Dcl_iter i)"
  hence "\<forall>i. \<exists>nd nd'. Dcl_iter (Suc i) nd nd' \<noteq> Dcl_iter i nd nd'" by (metis ext)
  hence "\<forall>i. \<exists>ndd. ndd \<in> Node \<times> Node \<and> Dcl_iter (Suc i) (fst ndd) (snd ndd) \<noteq> Dcl_iter i (fst ndd) (snd ndd)"
    by (metis Dcl_iter_nodes_out SigmaI fst_eqD snd_eqD)
  then obtain ndi where ndi: "\<forall>i. ndi i \<in> Node \<times> Node \<and> Dcl_iter (Suc i) (fst (ndi i)) (snd (ndi i)) \<noteq> Dcl_iter i (fst (ndi i)) (snd (ndi i))"
    by metis
    
  have "range ndi \<subseteq> Node \<times> Node" using ndi by blast
  hence "finite (range ndi)" using Node_finite finite_cartesian_product by (metis rev_finite_subset)
  
  have "UNIV = (\<Union>ndd \<in> range ndi. {i. ndi i = ndd})" by auto
  moreover have "finite (range ndi)" by fact
  ultimately obtain ndd where "ndd \<in> range ndi" and inf_I: "infinite {i. ndi i = ndd}"
    using infinite_UNIV_nat finite_Union by (metis (no_types, lifting) finite_UN_I)
  
  define nd nd' I where "nd = fst ndd" and "nd' = snd ndd" and "I = {i. ndi i = ndd}"
  have I_prop: "\<forall>i\<in>I. Dcl_iter (Suc i) nd nd' \<noteq> Dcl_iter i nd nd'"
    using I_def nd_def nd'_def ndi by auto
    
  have "I = (\<Union>R \<in> (\<lambda>i. Dcl_iter i nd nd') ` I. {k\<in>I. Dcl_iter k nd nd' = R})" by auto
  moreover have "finite ((\<lambda>i. Dcl_iter i nd nd') ` I)"
    using Dcl_iter_finite_range_all[of nd nd'] 
    by (metis Set.basic_monos(1) range_subsetD finite_subset image_subset_iff)
  ultimately obtain R where "R \<in> (\<lambda>i. Dcl_iter i nd nd') ` I" and inf_R: "infinite {k\<in>I. Dcl_iter k nd nd' = R}"
  proof -
    { assume "\<forall>R \<in> (\<lambda>i. Dcl_iter i nd nd') ` I. finite {k\<in>I. Dcl_iter k nd nd' = R}"
      hence "finite (\<Union>R\<in>(\<lambda>i. Dcl_iter i nd nd') ` I. {k\<in>I. Dcl_iter k nd nd' = R})"
        using \<open>finite ((\<lambda>i. Dcl_iter i nd nd') ` I)\<close> by blast
      hence "finite I"
        using \<open>I = (\<Union>R\<in>(\<lambda>i. Dcl_iter i nd nd') ` I. {k\<in>I. Dcl_iter k nd nd' = R})\<close> by simp
      hence "HOL.False"
        using inf_I I_def by simp }
    thus ?thesis
      using that by blast
  qed
    
  from inf_R have "\<forall>m. \<exists>n\<ge>m. n \<in> {k\<in>I. Dcl_iter k nd nd' = R}" 
    by (simp add: infinite_nat_iff_unbounded_le)
  then obtain i where i_in: "i \<in> I" and i_R: "Dcl_iter i nd nd' = R"
    by blast
    
  have "\<exists>j \<ge> Suc i. j \<in> {k\<in>I. Dcl_iter k nd nd' = R}" 
    using \<open>\<forall>m. \<exists>n\<ge>m. n \<in> {k\<in>I. Dcl_iter k nd nd' = R}\<close> by blast
  then obtain j where j_in: "j \<in> I" and j_R: "Dcl_iter j nd nd' = R" and "i < j"
    by auto
    
  have eq: "Dcl_iter i nd nd' = Dcl_iter j nd nd'" using i_R j_R by simp
  
  have "Dcl_iter (Suc i) nd nd' = Dcl_iter i nd nd'" 
    using \<open>i < j\<close> eq Dcl_iter_eq_implies_Suc_eq by blast
  thus "HOL.False" using I_prop i_in by simp
qed

lemma Dcl_iter_Suc_stable:
  assumes "Dcl_iter (Suc i) = Dcl_iter i"
  shows "Dcl_iter (Suc (Suc i)) = Dcl_iter i"
  using assms unfolding fun_eq_iff Dcl_iter.simps(2) by auto

lemma Dcl_iter_stable:
  assumes "Dcl_iter (Suc i) = Dcl_iter i" and "j \<ge> i"
  shows "Dcl_iter j = Dcl_iter i"
  using assms apply(induct "j-i" arbitrary: j i)
  subgoal by auto
  subgoal for x j
    by (metis Suc_diff_le Suc_leD diff_diff_cancel diff_le_self Dcl_iter_Suc_stable)
  done

lemma Dcl_iter_stops: "\<exists>k. \<forall>j \<ge> k. Dcl_iter j = Dcl_iter k"
  using Dcl_iter_Suc_stops Dcl_iter_stable by blast

definition Dcl :: "'node \<Rightarrow> 'node \<Rightarrow> ('pos \<Rightarrow> 'pos \<Rightarrow> slope \<Rightarrow> bool) set" where 
"Dcl nd nd' \<equiv> Dcl_iter (LEAST k. \<forall>j \<ge> k. Dcl_iter j = Dcl_iter k) nd nd'"

lemma Dcl_eq_some_Dcl_iter: "\<exists>i. \<forall>j \<ge> i. Dcl = Dcl_iter j"
proof -
  obtain k where k_def: "\<forall>j \<ge> k. Dcl_iter j = Dcl_iter k" using Dcl_iter_stops by blast
  let ?k_least = "LEAST k. \<forall>j \<ge> k. Dcl_iter j = Dcl_iter k"
  have "\<forall>j \<ge> ?k_least. Dcl_iter j = Dcl_iter ?k_least"
    using k_def LeastI[of "\<lambda>k. \<forall>j \<ge> k. Dcl_iter j = Dcl_iter k"] by blast
  thus ?thesis unfolding Dcl_def fun_eq_iff by blast
qed

lemma Dcl_initFrag_Ccl: "initFrag (Dcl nd nd') (Ccl nd nd')"
proof -
  obtain k_dcl where k_dcl: "\<forall>j\<ge>k_dcl. Dcl = Dcl_iter j" using Dcl_eq_some_Dcl_iter by blast
  obtain k_ccl where k_ccl: "Ccl = Ccl_iter k_ccl" using Ccl_eq_some_Ccl_iter by blast
  define max_k where "max_k \<equiv> max k_dcl k_ccl"
  have 1: "Dcl nd nd' = Dcl_iter max_k nd nd'" using k_dcl max_k_def by (simp add: fun_eq_iff)
  have 2: "Ccl_iter k_ccl nd nd' \<subseteq> Ccl_iter max_k nd nd'" using Ccl_iter_mono max_k_def by auto
  have 3: "Ccl nd nd' = Ccl_iter k_ccl nd nd'" using k_ccl by simp
  moreover have "Ccl nd nd' = Ccl_iter max_k nd nd'" 
    using 2 3 unfolding Ccl_def by auto
  ultimately show ?thesis using Dcl_iter_initFrag_Ccl_iter[of max_k] 1 by metis
qed

lemma Ccl_initFrag_Dcl: "initFrag (Ccl nd nd') (Dcl nd nd')"
proof -
  obtain k_dcl where k_dcl: "\<forall>j\<ge>k_dcl. Dcl = Dcl_iter j" using Dcl_eq_some_Dcl_iter by blast
  obtain k_ccl where k_ccl: "Ccl = Ccl_iter k_ccl" using Ccl_eq_some_Ccl_iter by blast
  define max_k where "max_k \<equiv> max k_dcl k_ccl"
  have 1: "Dcl nd nd' = Dcl_iter max_k nd nd'" using k_dcl max_k_def by (simp add: fun_eq_iff)
  have 2: "Ccl_iter k_ccl nd nd' \<subseteq> Ccl_iter max_k nd nd'" using Ccl_iter_mono max_k_def by auto
  have 3: "Ccl nd nd' = Ccl_iter k_ccl nd nd'" using k_ccl by simp 
  moreover have "Ccl nd nd' = Ccl_iter max_k nd nd'" 
    using 2 3 unfolding Ccl_def by auto
  ultimately show ?thesis using Ccl_iter_initFrag_Dcl_iter[of max_k] 1 by metis 
qed

(* ======================================================================== *)
(* 5. CONNECTION BETWEEN RELATIONAL ABSTRACTION AND INFINITE DESCENT        *)
(* ======================================================================== *)

definition "TransitiveLooping \<equiv> \<forall>nd\<in>Node. \<forall>K\<in>Dcl nd nd. (\<exists>P. transSl K P P Decr)"

lemma TransitiveLooping_iff_TransitiveLoopingCcl:
"TransitiveLooping \<longleftrightarrow> TransitiveLoopingCcl"
proof standard 
  assume 1: "TransitiveLooping"
  show "TransitiveLoopingCcl"
  unfolding TransitiveLoopingCcl_def proof safe
    fix nd K assume nd: "nd \<in> Node" and "K \<in> Ccl nd nd"
    moreover have "initFrag (Dcl nd nd) (Ccl nd nd)"
    using Dcl_initFrag_Ccl by blast
    ultimately obtain K' where le: "leqSl K' K" and "K' \<in> Dcl nd nd"
    unfolding initFrag_def by auto
    then obtain P where "transSl K' P P Decr" using 1 nd unfolding TransitiveLooping_def by auto
    with le have "transSl K P P Decr" 
      using transSl_mono 
      by (metis leqSl_def less_eq_slope.elims(2) slope.distinct(1))
    thus "\<exists>P. transSl K P P Decr" ..
  qed
next
  assume 1: "TransitiveLoopingCcl"
  show "TransitiveLooping"
  unfolding TransitiveLooping_def proof safe
    fix nd K assume nd: "nd \<in> Node" and "K \<in> Dcl nd nd"
    moreover have "initFrag (Ccl nd nd) (Dcl nd nd)"
    using Ccl_initFrag_Dcl by blast
    ultimately obtain K' where le: "leqSl K' K" and "K' \<in> Ccl nd nd"
    unfolding initFrag_def by auto
    then obtain P where "transSl K' P P Decr" using 1 nd unfolding TransitiveLoopingCcl_def by auto
    with le have "transSl K P P Decr" 
      using transSl_mono
      by (metis leqSl_def less_eq_slope.elims(2) slope.distinct(1))
    thus "\<exists>P. transSl K P P Decr" ..
  qed 
qed


(****)
(**MORE GRAPH NOTIONS***)
(****)


(* 4. THE CONNECTION BETWEEN THE RELATIONAL ABSTRACTION AND THE 
POSITION-LABELING OF EXPLICIT (I)PATHS *)

(* Descending position-labelling Pl of ndl according to the indicated slopes sll.
This generalizes the descentPath with adding explicit slope tracking
*)

definition descentPathSl :: "'node list \<Rightarrow> 'pos list \<Rightarrow> slope list \<Rightarrow> bool" where 
"descentPathSl ndl Pl sll \<equiv> 
 length Pl = length ndl \<and> length sll = length ndl-1 \<and> 
 (\<forall>i<length ndl-1. RR (ndl!i,Pl!i) (ndl!(Suc i),Pl!(Suc i)) (sll!i))"

lemma descentPathSl_append: 
assumes w: "descentPathSl ndl1 Pl1 sll1" "descentPathSl ndl2 Pl2 sll2" and l: "last ndl1 = hd ndl2" "last Pl1 = hd Pl2"
and lndl: "length ndl1 \<ge> 2" "length ndl2 \<ge> 2"
shows "descentPathSl (ndl1 @ tl ndl2) (Pl1 @ tl Pl2) (sll1 @ sll2)"
proof-
  have lPPl: "length Pl1 = length ndl1"  "length Pl2 = length ndl2"
  using w(1) w(2) descentPathSl_def by auto
  hence lPl: "length Pl1 \<ge> 2"  "length Pl2 \<ge> 2" using lndl by auto
  have lssll: "length sll1 = length ndl1 - 1"  "length sll2 = length ndl2 - 1" 
  using w(1) w(2) descentPathSl_def by auto
  hence lsll: "length sll1 \<ge> 1"  "length sll2 \<ge> 1" using lndl by auto
  have [simp]: "hd ndl2 = ndl2!0" "hd (tl ndl2) = ndl2!(Suc 0)" 
               "hd Pl2 = Pl2!0" "hd (tl Pl2) = Pl2!(Suc 0)"
               "hd sll2 = sll2!0" 
        apply (metis diff_is_0_eq' hd_conv_nth length_0_conv lsll(2) lssll(2) not_one_le_zero zero_le_one)
    apply (metis One_nat_def Suc_le_eq hd_conv_nth length_greater_0_conv length_tl lsll(2) lssll(2) List.nth_tl)
    apply (metis diff_is_0_eq' hd_conv_nth lPPl(2) list.size(3) lsll(2) lssll(2) not_one_le_zero zero_le_one)
    apply (metis One_nat_def Suc_le_eq hd_conv_nth lPPl(2) length_greater_0_conv length_tl lsll(2) lssll(2) List.nth_tl)
    by (metis hd_conv_nth length_0_conv lsll(2) not_one_le_zero)

  show ?thesis unfolding descentPathSl_def apply safe
    subgoal using assms unfolding descentPathSl_def by simp
    subgoal using assms unfolding descentPathSl_def by auto
    subgoal for i proof-
      assume ii: "i < length (ndl1 @ tl ndl2) - 1"
      show "RR ((ndl1 @ tl ndl2) ! i, (Pl1 @ tl Pl2) ! i) ((ndl1 @ tl ndl2) ! Suc i, 
                 (Pl1 @ tl Pl2) ! Suc i) ((sll1 @ sll2) ! i)"
      proof(cases "i < length ndl1-1")
        case True 
        thus ?thesis using assms unfolding descentPathSl_def 
        by simp
      next
        case False note i = False
        show ?thesis 
        proof(cases "i = length ndl1-1")
          case True
          hence 1: "(ndl1 @ tl ndl2) ! i = last ndl1" 
          by (metis One_nat_def diff_Suc_less last_conv_nth length_greater_0_conv less_imp_diff_less 
             less_le_trans lsll(1) lssll(1) not_less nth_append zero_less_Suc)
          have 2: "(Pl1 @ tl Pl2) ! i = last Pl1" 
          by (metis One_nat_def Suc_n_not_le_n True add_diff_inverse_nat lPPl(1) last_conv_nth lessI 
              list.size(3) lsll(1) lssll(1) nat_diff_split nth_append plus_1_eq_Suc)
          have 3: "(ndl1 @ tl ndl2) ! Suc i = hd (tl ndl2)" unfolding nth_append  
          by (metis (full_types) True add_diff_inverse_nat cancel_comm_monoid_add_class.diff_cancel 
             hd_conv_nth le_imp_less_Suc length_tl less_not_refl3 list.size(3) lsll 
             lssll nat_diff_split plus_1_eq_Suc)
          have 4: "(Pl1 @ tl Pl2) ! Suc i = hd (tl Pl2)" unfolding nth_append 
          by (metis (full_types) True add_diff_inverse_nat cancel_comm_monoid_add_class.diff_cancel hd_conv_nth 
              lPPl(1) lPPl(2) le_imp_less_Suc length_tl less_not_refl3 
              list.size(3) lsll lssll nat_diff_split plus_1_eq_Suc)
          have 5: "(sll1 @ sll2) ! i = hd sll2" 
          by (metis True hd_Cons_tl length_greater_0_conv less_le_trans less_numeral_extra(1) 
              lsll(2) lssll(1) nth_append_length)
          show ?thesis using w(2) lsll(2) unfolding 1 2 3 4 5 l descentPathSl_def by auto
        next
          case False hence i: "i \<ge> length ndl1" "i \<ge> length Pl1" using i lPPl by auto
          hence [simp]: "\<not> i < length sll1" using lssll(1) by linarith
          define j where j: "j \<equiv> Suc (i - length ndl1)"
          have [simp]: "tl ndl2 ! (i - length ndl1) = ndl2!j"  
          by (metis Suc_leD Suc_le_mono add_diff_inverse_nat hd_Cons_tl j list.size(3) lsll(2) 
            lssll(2) nat_diff_split not_one_le_zero nth_Cons_Suc plus_1_eq_Suc)
          have [simp]: "tl Pl2 ! (i - length Pl1) = Pl2!j"  
          by (metis diff_Suc_1 diff_is_0_eq hd_Cons_tl j lPPl(1) lPPl(2) 
            list.size(3) lsll(2) lssll(2) not_less_eq_eq nth_Cons_Suc zero_diff)
          have [simp]: "tl ndl2 ! (Suc i - length ndl1) = ndl2!(Suc j)"  
            by (metis Suc_diff_le Suc_leD Suc_le_mono add_diff_inverse_nat hd_Cons_tl i(1) j list.size(3) 
             lsll(2) lssll(2) nat_diff_split not_one_le_zero nth_Cons_Suc plus_1_eq_Suc)
          have [simp]: "tl Pl2 ! (Suc i - length Pl1) = Pl2!(Suc j)"  
            by (metis Suc_diff_le hd_Cons_tl i(2) j lPPl(1) lPPl(2) length_greater_0_conv length_tl less_le_trans 
            less_numeral_extra(1) lsll(2) lssll(2) nth_Cons_Suc tl_Nil)
          have [simp]: "sll2 ! (i - length sll1) = sll2!j"  
            using Suc_diff_le i(1) j lsll(1) lssll(1) 
            by (metis One_nat_def Suc_n_minus_m_eq le_simps(3) zero_less_diff)
          have "j < length ndl2 - 1" unfolding j using ii i(1) by auto
          thus ?thesis unfolding nth_append using i w(2) unfolding descentPathSl_def by simp
        qed
      qed
    qed . 
qed

lemma descentPathSl_append_invert_singl: 
assumes "pathG ndl" "descentPathSl (ndl @ [nd]) Pl' sll'"
shows "\<exists>Pl P sll sl. 
  descentPathSl ndl Pl sll \<and> Pl' = Pl @ [P] \<and> sll' = sll @ [sl] \<and> RR (last ndl,last Pl) (nd,P) sl"
proof-
  obtain P Pl where Pl': "Pl' = Pl @ [P]" using assms unfolding descentPathSl_def  
  by (metis append_butlast_last_id append_is_Nil_conv length_0_conv not_Cons_self2)
  obtain sl sll where sll': "sll' = sll @ [sl]" using assms unfolding descentPathSl_def Pl'  apply simp
  by (metis Graph.not_path_Nil append_Nil2 append_butlast_last_id append_eq_append_conv 
        length_append_singleton length_butlast)
  show ?thesis apply(intro exI[of _ P] exI[of _ Pl] exI[of _ sl] exI[of _ sll])
  unfolding Pl' sll' using assms unfolding descentPathSl_def 
  by (smt One_nat_def Pl' Suc_mono append_is_Nil_conv diff_Suc_1 last_conv_nth length_0_conv 
        length_append_singleton lessI less_SucI nth_append nth_append_length sll')
qed
  
lemma descentPathSl_append_invert: 
assumes p1: "pathG ndl1" and "pathG ndl2" "last ndl1 = hd ndl2" "descentPathSl (ndl1 @ (tl ndl2)) Pl sll"
shows "\<exists>Pl1 Pl2 sll1 sll2. last Pl1 = hd Pl2 \<and>
  descentPathSl ndl1 Pl1 sll1 \<and> descentPathSl ndl2 Pl2 sll2 \<and> Pl = Pl1 @ (tl Pl2) \<and> sll = sll1 @ sll2"
using assms(2-4) proof (induction arbitrary: Pl sll)
  case (Base nd nd' Pl Sll)
  then show ?case using descentPathSl_append_invert_singl[OF p1 Base(4)[simplified]] apply safe
    subgoal for Pl1 P2 sll1 sl2
    apply(rule exI[of _ Pl1]) apply(rule exI[of _ "[last Pl1,P2]"])
    apply(rule exI[of _ sll1]) apply(rule exI[of _ "[sl2]"]) 
    by (simp add: descentPathSl_def) .  
next
  case (Step nd2 ndl2 Pl' sll')
  have 0: "last ndl1 = hd ndl2" using Step by (metis hd_append not_path_Nil)  
  obtain P2 Pl where Pl': "Pl' = Pl @ [P2]" 
  by (metis Nil_is_append_conv Step.hyps(2) Step.prems(2) 
      length_0_conv list.distinct(1) not_path_Nil rev_exhaust tl_append2 descentPathSl_def)
  have l: "length Pl = length (ndl1 @ tl ndl2)" 
  by (metis Pl' Step.hyps(2) Step.prems(2) append.assoc butlast_snoc length_butlast not_path_Nil 
      tl_append2 descentPathSl_def)
  have "sll' \<noteq> []"
  using Step.prems(2) unfolding Pl' 
  by (metis One_nat_def Step.hyps Step.prems(1)
       append_is_Nil_conv diff_is_0_eq hd_Cons_tl list.size(3) not_Cons_self2 
       not_less_eq_eq numeral_2_eq_2 p1 pathG.Step path_append_last path_length_ge2 descentPathSl_def)
  then obtain sl2 sll where sll': "sll' = sll @ [sl2]" using rev_exhaust by blast
  have 1: "descentPathSl (ndl1 @ tl ndl2) Pl sll" using Step.prems(2) unfolding Pl' sll' unfolding descentPathSl_def apply safe
    subgoal using l by auto
    subgoal using l by auto
    subgoal for i apply(cases "i < length ndl1")
      subgoal using One_nat_def Step.hyps(2) Suc_mono add_diff_cancel_left' append.assoc butlast_snoc l 
         List.length_append List.length_tl less_SucI not_path_Nil nth_butlast plus_1_eq_Suc tl_append2
        by (smt (verit, ccfv_SIG) length_append_singleton)

      subgoal by (smt One_nat_def Step.hyps(2) Step.prems(2) Suc_mono add_diff_cancel_left' append.assoc 
         butlast_snoc length_append length_append_singleton 
         less_SucI not_path_Nil nth_butlast plus_1_eq_Suc sll' tl_append2 descentPathSl_def l) . .
  from Step.IH[OF 0 1] obtain Pl1 Pl2 sll1 sll2 where 
  la: "last Pl1 = hd Pl2" and w: "descentPathSl ndl1 Pl1 sll1" "descentPathSl ndl2 Pl2 sll2" 
  and Pl: "Pl = Pl1 @ tl Pl2" and sll: "sll = sll1 @ sll2" by auto 
  have lndl: "length ndl1 \<ge> 2"  "length ndl2 \<ge> 2" by (simp_all add: Step.hyps(2) p1 path_length_ge2)
  have lPPl: "length Pl1 = length ndl1"  "length Pl2 = length ndl2"
  using w(1) w(2) descentPathSl_def by auto
  hence lPl: "length Pl1 \<ge> 2"  "length Pl2 \<ge> 2" using lndl by auto
  have lssll: "length sll1 = length ndl1 - 1"  "length sll2 = length ndl2 - 1" 
  using w(1) w(2) descentPathSl_def by auto
  hence lsll: "length sll1 \<ge> 1"  "length sll2 \<ge> 1" using lndl by auto
  have [simp]: "\<not> length ndl1 + length ndl2 - 2 < length ndl1" using lndl by linarith
  have [simp]: "\<not> length ndl1 + length ndl2 - 2 < length Pl1" using w(1) descentPathSl_def by auto
  have [simp]: "length ndl1 + length ndl2 - Suc (Suc (length Pl1)) < length Pl2 - Suc 0" 
    using lPPl(1) lPPl(2) lndl(2) by linarith
  have [simp]: "\<not> Suc (length ndl1 + length ndl2 - 2) < length ndl1" 
    using Suc_lessD \<open>\<not> length ndl1 + length ndl2 - 2 < length ndl1\<close> by blast
  have [simp]: "\<not> Suc (length ndl1 + length ndl2 - 2) < length Pl1"  
    by (simp add: lPPl(1))
  have [simp]: "\<not> length ndl1 + length ndl2 - Suc (length Pl1) < length Pl2 - Suc 0" 
   by (simp add: lPPl(1) lPPl(2))
  have [simp]: "\<not> length ndl1 + length ndl2 - 2 < length sll1" 
    using less_diff_conv lssll(1) by auto
  have [simp]: "\<not> length ndl1 + length ndl2 - Suc (Suc (length sll1)) < length sll2"
    using lndl(1) lssll(1) lssll(2) by auto


  have a:"\<not> Suc (length ndl1 + length ndl2 - 2) < length ndl1"
          "\<not> length ndl1 + length ndl2 - Suc (Suc (length sll1)) < length sll2" 
          \<open>\<not> length ndl1 + length ndl2 - 2 < length ndl1\<close> 
          \<open>\<not> length ndl1 + length ndl2 - 2 < length sll1\<close> by simp_all


  have aux:  "RR (last ndl2, last Pl2) (nd2, P2) sl2"
  using Step.prems(2) unfolding Pl' sll' Pl sll descentPathSl_def apply clarsimp  
  apply(erule allE[of _ "length ndl1 + length ndl2 - 2"])  
  unfolding nth_append 
  using One_nat_def Suc_diff_Suc Suc_le_lessD add_diff_cancel_left' butlast_snoc diff_Suc_Suc 
      lPPl(1) last_conv_nth last_tl length_greater_0_conv length_tl lessI less_add_Suc1 less_add_same_cancel1 
      lsll(2) lssll(2) nth_append_length nth_butlast numeral_2_eq_2 plus_1_eq_Suc tl_append2
      List.nth_append by (smt (z3) a)

  show ?case 
  apply(rule exI[of _ "Pl1"]) apply(rule exI[of _ "Pl2 @ [P2]"])
  apply(rule exI[of _ sll1]) apply(rule exI[of _ "sll2 @ [sl2]"]) 
  apply safe
    subgoal by (metis Graph.not_path_Nil Step.hyps(2) hd_append2 la length_greater_0_conv w(2) descentPathSl_def)
    subgoal using w(1) by blast
    subgoal unfolding descentPathSl_def apply safe
      subgoal using w(2) descentPathSl_def by auto
      subgoal by (metis Step.hyps(2) length_append_singleton length_tl not_path_Nil tl_append2 w(2) descentPathSl_def) 
      subgoal for i apply(subst nth_append)  apply(cases "i < length ndl2-1")
        subgoal using w unfolding descentPathSl_def by simp 
        subgoal by simp (metis (no_types, lifting) One_nat_def Suc_pred aux butlast_snoc gr_implies_not0 
           last_conv_nth length_greater_0_conv 
           not_less_less_Suc_eq nth_append_length nth_butlast w(2) descentPathSl_def zero_less_Suc) . .
    subgoal by (metis Pl Pl' Step.hyps(2) append_eq_append_conv2 lPPl(2) length_0_conv not_path_Nil tl_append2)
    subgoal by (simp add: sll sll') . 
qed 

lemma descentPathSl_wfLabL: 
assumes "pathG ndl" and "descentPathSl ndl Pl sll"
shows "wfLabL ndl Pl"
using assms unfolding descentPathSl_def wfLabL_def 
by (metis (no_types, lifting) Nitpick.size_list_simp(2) RR_PosOf length_tl 
      less_Suc_eq not_less numeral_2_eq_2 path_length_ge2)

(* There is a correspondence between sloped relations and paths, in the sense that 
each sloped relation between two nodes nd and nd' tracks the position-persistence of 
a path between these two nodes. This is why I call the correspondence "tracksPers". 
*)

definition tracksPers :: "('pos \<Rightarrow> 'pos \<Rightarrow> slope \<Rightarrow> bool) \<Rightarrow> 'node list \<Rightarrow> bool" where 
"tracksPers K ndl \<equiv> 
  (\<forall> Pl sll. descentPathSl ndl Pl sll \<longrightarrow> K (hd Pl) (last Pl) (MaxSl (set sll))) \<and> 
  (\<forall>P P' sl. K P P' sl \<longrightarrow> (\<exists>Pl sll. descentPathSl ndl Pl sll \<and> hd Pl = P \<and> last Pl = P' \<and> sl = MaxSl (set sll)))"

(* The correspondence is both left- and right- total, in the sense that:
-- each path corresponds to a sloped relation,
-- each sloped relation corresponds to a path.
*)

proposition tracksPers_leftTotal: 
assumes ndl: "pathG ndl" 
shows "\<exists> K \<in> Ccl (hd ndl) (last ndl). tracksPers K ndl"
using ndl proof induct
  case (Base nd nd')
  show ?case apply(rule bexI[of _ "\<lambda>P P' sl. RR (nd,P) (nd',P') sl"])
    subgoal unfolding tracksPers_def apply safe
      subgoal for Pl sll unfolding descentPathSl_def MaxSl_def   
      by simp (metis (full_types) One_nat_def diff_Suc_1 hd_conv_nth in_set_conv_nth 
        last_conv_nth less_one list.size(3) old.nat.distinct(2) slope.exhaust)
      subgoal for P P' sl apply(intro exI[of _ "[P,P']"] exI[of _ "[sl]"])
       unfolding descentPathSl_def by auto .
    subgoal using Base by auto .
next
  case (Step nd ndl)
  then obtain K where K: "K\<in>Ccl (hd ndl) (last ndl)" and cor: "tracksPers K ndl" by auto

  have lndl: "length ndl \<ge> 2" using Step.hyps(2) path_iff_nth by blast
  have [simp]: "hd (ndl @ [nd]) = hd ndl"  
  by (metis Graph.not_path_Nil Step.hyps(2) hd_append2)

  define K1 where "K1 \<equiv> \<lambda>P P' sl. RR (last ndl,P) (nd,P') sl"
  have K1: "K1 \<in> Ccl (last ndl) nd" unfolding K1_def apply(rule Ccl_RR) 
    using Step Ccl_nodes `edge (last ndl) nd` by blast+
  show ?case apply(rule bexI[of _ "ccompSl K K1"])
    subgoal unfolding tracksPers_def proof safe
      fix Pl' sll' assume "descentPathSl (ndl @ [nd]) Pl' sll'"
      then obtain P Pl sl sll where w: "descentPathSl ndl Pl sll"
      and 1: "Pl' = Pl @ [P]" "sll' = sll @ [sl]" and edge: "RR (last ndl, last Pl) (nd, P) sl" 
      using descentPathSl_append_invert_singl[OF `pathG ndl`] by blast
      have lPl: "length Pl \<ge> 2" using w by (simp add: lndl descentPathSl_def)

      have 2: "hd Pl' = hd Pl" "last Pl' = P" unfolding 1 
        subgoal 
        by (metis Cons_eq_appendI Step.hyps(2) length_0_conv list.exhaust_sel list.sel(1) not_path_Nil w descentPathSl_def) 
        subgoal by simp .
      
      from w have K: "K (hd Pl) (last Pl) (MaxSl (set sll))" using cor unfolding tracksPers_def by auto
      show "ccompSl K K1 (hd Pl') (last Pl') (MaxSl (set sll'))"
      unfolding ccompSl_def apply(rule exI[of _ "last Pl"])
      apply(rule exI[of _ "MaxSl (set sll)"]) apply(rule exI[of _ sl]) apply safe
        subgoal unfolding 1 MaxSl_def by auto
        subgoal unfolding 2 by fact
        subgoal unfolding K1_def 2 by fact . 
    next
      fix P P' sl assume 0: "ccompSl K K1 P P' sl"
      then obtain P'' sl1 sl2 where sl: "sl = MaxSl {sl1, sl2}" 
      and K: "K P P'' sl1" and "K1 P'' P' sl2" unfolding ccompSl_def by auto
      hence edge: "RR (last ndl, P'') (nd, P') sl2" unfolding K1_def by simp
      obtain Pl sll where w: "descentPathSl ndl Pl sll" and 1: "hd Pl = P" "last Pl = P''" "sl1 = MaxSl (set sll)" 
      using K cor unfolding tracksPers_def by blast
      show "\<exists>Pl' sll'. descentPathSl (ndl @ [nd]) Pl' sll' \<and> hd Pl' = P \<and> last Pl' = P' \<and> sl = MaxSl (set sll')"
      apply(intro exI[of _ "Pl @ [P']"] exI[of _ "sll @ [sl2]"]) apply safe
        subgoal using w unfolding descentPathSl_def 
        by simp (smt "1"(2) One_nat_def Step.hyps(2) Suc_lessI Suc_pred edge butlast_snoc last_conv_nth 
            length_greater_0_conv less_Suc_eq not_path_Nil nth_append_length nth_butlast)
        subgoal by (metis 1(1) Step.hyps(2) hd_append2 length_greater_0_conv not_path_Nil w descentPathSl_def)
        subgoal by simp
        subgoal unfolding 1 sl unfolding MaxSl_def by auto . 
    qed
    subgoal using Ccl_ccompSl[OF _ K K1] using K Ccl_nodes by auto .
qed 

proposition tracksPers_rightTotal: 
assumes "K \<in> Ccl nd nd'"
shows "\<exists>ndl. pathG ndl \<and> hd ndl = nd \<and> last ndl = nd' \<and> tracksPers K ndl"
proof-
  obtain i where "K\<in>Ccl_iter i nd nd'" using assms unfolding Ccl_def by auto
  thus ?thesis proof(induction i arbitrary: K nd nd')
    case (0 K nd nd')
    hence K : "K = (\<lambda>P P'. RR (nd, P) (nd', P'))" and edge: "{nd,nd'} \<subseteq> Node" "edge nd nd'" by (auto split: if_splits)
    show ?case apply(intro exI[of _"[nd,nd']"]) apply safe
      subgoal using Base edge by (simp add: path_two_incl)
      subgoal by simp
      subgoal by simp
      subgoal unfolding tracksPers_def apply safe
        subgoal for Pl sll unfolding descentPathSl_def K  
        by simp (metis (full_types) MaxSl_def One_nat_def diff_Suc_1 hd_conv_nth 
          in_set_conv_nth last_conv_nth less_one list.size(3) nat.distinct(1) slope.exhaust)
        subgoal for P P' sl apply(intro exI[of _ "[P,P']"] exI[of _ "[sl]"])  
        unfolding descentPathSl_def K by simp . .
  next
    case (Suc i K nd nd') 
    show ?case proof(cases "K \<in> Ccl_iter i nd nd'")
      case True
      show ?thesis using Suc.IH[OF True] .
    next
      case False
      with `K \<in> Ccl_iter (Suc i) nd nd'` obtain K1 K2 nd'' where 
      K: "K = ccompSl K1 K2" and nd'': "nd'' \<in> Node" 
      and K1: "K1 \<in> Ccl_iter i nd nd''" and K2: "K2 \<in> Ccl_iter i nd'' nd'" 
      by auto
      from Suc.IH[OF K1] Suc.IH[OF K2] obtain ndl1 ndl2 where 
      ndl1: "pathG ndl1" "hd ndl1 = nd" "last ndl1 = nd''" and cor1: "tracksPers K1 ndl1" and 
      ndl2: "pathG ndl2" "hd ndl2 = nd''" "last ndl2 = nd'" and cor2: "tracksPers K2 ndl2"
      by auto
      define ndl where "ndl \<equiv> ndl1 @ tl ndl2"

      show ?thesis apply(rule exI[of _ ndl]) apply safe
        subgoal by (metis ndl_def list.exhaust_sel ndl1(1) ndl1(3) ndl2(1) ndl2(2) not_path_Nil path_append_last)
        subgoal by (metis  ndl_def hd_append ndl1(1) ndl1(2) not_path_Nil)
        subgoal by (metis append_Nil2 append_butlast_last_id hd_Cons_tl last_appendR last_tl ndl1(1) ndl1(3) 
                      ndl2(1) ndl2(2) ndl2(3) ndl_def not_path_Nil)
        subgoal unfolding tracksPers_def proof safe
          fix Pl sll assume w: "descentPathSl ndl Pl sll"
          from descentPathSl_append_invert[OF ndl1(1) ndl2(1) _ w[unfolded ndl_def]]
          obtain Pl1 Pl2 sll1 sll2 where 
          w1: "descentPathSl ndl1 Pl1 sll1" and w2: "descentPathSl ndl2 Pl2 sll2" and 
          4: "last Pl1 = hd Pl2" "Pl = Pl1 @ (tl Pl2)" "sll = sll1 @ sll2" 
          using ndl1(3) ndl2(2) by auto
          from w1 cor1 have K1: "K1 (hd Pl1) (last Pl1) (MaxSl (set sll1))" unfolding tracksPers_def by auto
          from w2 cor2 have K2: "K2 (hd Pl2) (last Pl2) (MaxSl (set sll2))" unfolding tracksPers_def by auto

          show "K (hd Pl) (last Pl) (MaxSl (set sll))" unfolding K ccompSl_def 
          apply(rule exI[of _ "last Pl1"]) 
          apply(rule exI[of _ "MaxSl (set sll1)"]) apply(rule exI[of _ "MaxSl (set sll2)"]) 
          apply safe
            subgoal unfolding 4 MaxSl_def by simp

            subgoal by (metis "4"(2) K1 hd_append2 list.size(3) ndl1(1) not_less path_length_ge2 pos2 w1 descentPathSl_def)
            subgoal by (metis "4"(1) "4"(2) K2 append_Nil2 hd_Cons_tl last_ConsL last_appendR last_tl 
                 list.size(3) ndl2(1) not_less path_length_ge2 pos2 w2 descentPathSl_def) . 
        next
          fix P P' sl assume "K P P' sl"
          then obtain P'' sl1 sl2 where sl: "sl = MaxSl {sl1, sl2}" 
          and K: "K1 P P'' sl1" "K2 P'' P' sl2" unfolding K ccompSl_def by auto
          from K(1) obtain Pl1 sll1 where 
          1: "descentPathSl ndl1 Pl1 sll1" "hd Pl1 = P" "last Pl1 = P''" "sl1 = MaxSl (set sll1)"
          using cor1 unfolding tracksPers_def by blast
          from K(2) obtain Pl2 sll2 where 
          2: "descentPathSl ndl2 Pl2 sll2" "hd Pl2 = P''" "last Pl2 = P'" "sl2 = MaxSl (set sll2)"
          using cor2 unfolding tracksPers_def by blast

          show "\<exists>Pl sll. descentPathSl ndl Pl sll \<and> hd Pl = P \<and> last Pl = P' \<and> sl = MaxSl (set sll)" 
          apply(intro exI[of _ "Pl1 @ tl Pl2"] exI[of _ "sll1 @ sll2"]) apply safe
            subgoal using 1(1) 2(1) 1(3) 2(2) 
            by (simp add: ndl1(1) ndl1(3) ndl2(1) ndl2(2) ndl_def path_length_ge2 descentPathSl_append)
            subgoal by (metis 1(1,2) hd_append2 length_0_conv ndl1(1) not_path_Nil descentPathSl_def)
            subgoal by (metis 1(3) 2(1-3) append_Nil2 hd_Cons_tl last_ConsL last_appendR last_tl 
                    length_0_conv ndl2(1) not_path_Nil descentPathSl_def)
            subgoal unfolding sl 1 2 MaxSl_def by simp . 
        qed .
    qed
  qed
qed

(*  *)


(* Auxiliary notion that generalises descentPath, to be used in inductive proofs. 
"descentPathParam ndl Pl sl" states something equivalent to the existence of a choice 
of slopes, all \<le> sl and including sl (i.e., of which sl is the maximum), such that 
the positions in Pl associated to the nodes in ndl decrease according to these slopes.  
*)
definition "descentPathParam ndl Pl sl \<equiv>
(\<forall>i. Suc i < length ndl \<longrightarrow>
     RR (ndl ! i, Pl ! i) (ndl ! Suc i, Pl ! Suc i) Main \<or>
     \<not> RR (ndl ! i, Pl ! i) (ndl ! Suc i, Pl ! Suc i) Main \<and> 
       RR (ndl ! i, Pl ! i) (ndl ! Suc i, Pl ! Suc i) Decr \<and> sl = Decr) 
 \<and>
(\<exists>i. Suc i < length ndl \<and> RR (ndl ! i, Pl ! i) (ndl ! Suc i, Pl ! Suc i) sl)"

lemma descentPath_descentPathParam: 
"descentPath ndl Pl \<longleftrightarrow> descentPathParam ndl Pl Decr"
using descentPathParam_def descentPath_def by auto 

lemma descentPathSl_descentPathParam: 
assumes "pathG ndl" and "descentPathSl ndl Pl sll"
shows "descentPathParam ndl Pl (MaxSl (set sll))"
using assms unfolding descentPathSl_def descentPathParam_def MaxSl_def 
using assms unfolding descentPathSl_def descentPathParam_def MaxSl_def 
apply safe
  subgoal by (metis (full_types) Nitpick.size_list_simp(2) 
  One_nat_def Suc_less_eq length_tl not_path_Nil slope.exhaust)
  subgoal by (metis (full_types) Suc_lessE diff_Suc_1 in_set_conv_nth slope.exhaust) 
  subgoal by (smt Nitpick.size_list_simp(2) One_nat_def Suc_n_not_le_n diff_Suc_less 
             in_set_conv_nth length_greater_0_conv length_tl less_trans_Suc not_path_Nil 
             numeral_2_eq_2 path_length_ge2 slope.exhaust) .
 
lemma descentPathParam_append: 
assumes ndl: "ndl1 \<noteq> []" "ndl2 \<noteq> []""length ndl1 = length Pl1" "length ndl2 = length Pl2"
and d: "descentPathParam ndl1 Pl1 sl1" "descentPathParam ndl2 Pl2 sl2"
and l: "last ndl1 = hd ndl2" "last Pl1 = hd Pl2"
shows "descentPathParam (ndl1 @ (tl ndl2)) (Pl1 @ (tl Pl2)) (MaxSl {sl1,sl2})"
proof-
  define ndl Pl sl where "ndl \<equiv> ndl1 @ tl ndl2" and "Pl \<equiv> Pl1 @ tl Pl2" and "sl \<equiv> MaxSl {sl1,sl2}"
  have sl_Decr[simp]: "sl = Decr \<longleftrightarrow> sl1 = Decr \<or> sl2 = Decr"
  unfolding sl_def MaxSl_def using slope.exhaust by auto
  show ?thesis 
  unfolding descentPathParam_def ndl_def[symmetric] Pl_def[symmetric] sl_def[symmetric] 
  proof(intro allI conjI impI)
    fix i assume "Suc i < length ndl"
    show "RR (ndl ! i, Pl ! i) (ndl ! Suc i, Pl ! Suc i) Main \<or>
         \<not> RR (ndl ! i, Pl ! i) (ndl ! Suc i, Pl ! Suc i) Main \<and>
         RR (ndl ! i, Pl ! i) (ndl ! Suc i, Pl ! Suc i) Decr \<and> sl = Decr"
    proof(cases "Suc i < length ndl1")
      case True
      hence 1: "RR (ndl1 ! i, Pl1 ! i) (ndl1 ! Suc i, Pl1 ! Suc i) Main \<or>
         \<not> RR (ndl1 ! i, Pl1 ! i) (ndl1 ! Suc i, Pl1 ! Suc i) Main \<and>
         RR (ndl1 ! i, Pl1 ! i) (ndl1 ! Suc i, Pl1 ! Suc i) Decr \<and> sl1 = Decr"
      using d(1) unfolding descentPathParam_def by auto 
      have 2: "ndl1 ! (Suc i) = ndl ! (Suc i)" "Pl1 ! (Suc i) = Pl ! (Suc i)" 
               "ndl1 ! i = ndl ! i" "Pl1 ! i = Pl ! i" 
      apply (metis True ndl(3) ndl_def nth_append)
      apply (metis Pl_def True ndl(3) nth_append)
      apply (metis Suc_lessD True ndl(3) ndl_def nth_append)
      by (metis Pl_def Suc_lessD True ndl(3) nth_append)
      show ?thesis using 1 unfolding 2 by auto
    next
      case False 
      show ?thesis proof(cases "i < length ndl1")
        case True hence i: "i = length ndl1 - Suc 0" using False by linarith
        have 2: "ndl ! (Suc i) = ndl2 ! (Suc 0)" "Pl ! (Suc i) = Pl2 ! (Suc 0)" 
                "ndl ! i = ndl2 ! 0" "Pl ! i = Pl2 ! 0" 
        apply (metis False Suc_diff_Suc diff_self_eq_0 i length_greater_0_conv 
           list.exhaust_sel minus_nat.diff_0 ndl(1) ndl(2) ndl_def nth_Cons_Suc nth_append)
          apply(metis False Pl_def Suc_lessI True \<open>Suc i < length ndl\<close> append_Nil2 
           cancel_comm_monoid_add_class.diff_cancel length_greater_0_conv length_tl ndl(3) ndl(4) 
           ndl_def nth_append nth_tl assms(2))
        apply (metis One_nat_def True hd_conv_nth i l(1) last_conv_nth ndl(1) ndl(2) ndl_def nth_append)
        by (metis One_nat_def Pl_def True hd_conv_nth i l(2) last_conv_nth length_0_conv ndl nth_append)
        have "Suc 0 < length ndl2"  using False \<open>Suc i < length ndl\<close> ndl_def by auto
        thus ?thesis using d(2) unfolding 2 descentPathParam_def by auto
      next
        case False 
        define j where "j \<equiv> Suc (i-length ndl1)"
        have 2: "ndl ! i = ndl2 ! j" "Pl ! i = Pl2 ! j" 
                 "ndl ! (Suc i) = ndl2 ! (Suc j)" 
                 "Pl ! (Suc i) = Pl2 ! (Suc j)"
        unfolding j_def 
        apply (metis False hd_Cons_tl ndl(2) ndl_def nth_Cons_Suc nth_append)
        apply (metis False Pl_def hd_Cons_tl length_0_conv ndl(2) ndl(3) ndl(4) nth_Cons_Suc nth_append)
        apply (metis False Suc_diff_le Suc_lessD hd_Cons_tl ndl(2) ndl_def not_less nth_Cons_Suc nth_append)
        by (metis (mono_tags, lifting) False Pl_def Suc_diff_le Suc_lessD hd_Cons_tl length_0_conv 
                 ndl(2) ndl(3) ndl(4) not_less nth_Cons_Suc nth_append)
        have "Suc j < length ndl2" using False \<open>Suc i < length ndl\<close> j_def ndl_def by auto 
        thus ?thesis using d(2) unfolding 2 descentPathParam_def by auto
      qed
    qed
  next
    show "\<exists>i. Suc i < length ndl \<and> RR (ndl ! i, Pl ! i) (ndl ! Suc i, Pl ! Suc i) sl"
    proof(cases "sl = sl1")
      case True 
      obtain i where "Suc i < length ndl1 \<and> RR (ndl1 ! i, Pl1 ! i) (ndl1 ! Suc i, Pl1 ! Suc i) sl1"
      using d(1) descentPathParam_def by auto
      thus ?thesis apply(intro exI[of _ i]) 
      by (metis Pl_def Suc_lessD add_lessD1 length_append ndl(3) ndl_def not_less_eq nth_append True)
    next
      case False note sl = False
      hence sl: "sl = sl2" unfolding sl_def MaxSl_def by(cases sl1, auto)
      obtain i where si: "Suc i < length ndl2 \<and> RR (ndl2 ! i, Pl2 ! i) (ndl2 ! Suc i, Pl2 ! Suc i) sl2"
      using d(2) descentPathParam_def by auto
      show ?thesis proof(cases "i=0")
        case True
        define j where "j \<equiv> (length ndl1 + i - Suc 0)"
        have 2: "ndl ! j = ndl2 ! i" "Pl ! j = Pl2 ! i"
                "ndl ! (Suc j) = ndl2 ! (Suc i)" "Pl ! (Suc j) = Pl2 ! (Suc i)"
        unfolding j_def
        apply (metis True Nat.add_0_right One_nat_def diff_less hd_conv_nth l(1) last_conv_nth length_greater_0_conv 
            ndl(1,2) ndl_def not_less_eq not_less_zero nth_append)              
        apply (metis True Nat.add_0_right One_nat_def Pl_def diff_Suc_less hd_conv_nth l(2) last_conv_nth length_greater_0_conv 
                 ndl  nth_append)
        apply (metis True Nat.add_0_right Nitpick.size_list_simp(2) One_nat_def length_tl list.exhaust_sel ndl(1) ndl(2) ndl_def 
                 nth_Cons_Suc nth_append_length_plus)
        by (metis True Nat.add_0_right Nitpick.size_list_simp(2) Pl_def diff_add_zero length_tl 
                 ndl(1,3,4) not_add_less1 nth_append nth_tl plus_1_eq_Suc si zero_less_diff list.sel(2))
        have "Suc j < length ndl" using j_def ndl(1) ndl_def si by auto
        thus ?thesis apply(intro exI[of _ j]) using si unfolding 2 sl by auto 
      next
        case False
        define j where "j \<equiv> length ndl1 + i - Suc 0"
        have "ndl ! j = (tl ndl2) ! (i - Suc 0)" "Pl ! j = Pl2 ! i"
        and 2: "ndl ! (Suc j) = ndl2 ! (Suc i)" "Pl ! (Suc j) = Pl2 ! (Suc i)"
        unfolding j_def 
        apply (metis False Nat.add_diff_assoc One_nat_def Suc_pred diff_add_zero diff_is_0_eq 
                less_Suc_eq ndl_def nth_append_length_plus plus_1_eq_Suc zero_less_Suc)
        apply (metis False Nat.add_diff_assoc Pl_def Suc_leI Suc_pred length_0_conv list.exhaust_sel 
               nat_neq_iff ndl(2-4) not_less_eq nth_Cons_Suc nth_append_length_plus zero_less_Suc)
        apply (metis Nitpick.size_list_simp(2) Suc_less_eq Suc_pred add_diff_cancel_left' add_gr_0 
          length_greater_0_conv ndl(1) ndl(2) ndl_def not_add_less1 nth_append nth_tl si)
        by (metis Nitpick.size_list_simp(2) Pl_def Suc_less_eq Suc_pred add_diff_cancel_left' 
         add_gr_0 length_greater_0_conv ndl not_add_less1 nth_append nth_tl si)
        hence 3: "ndl ! j = ndl2 ! i" "Pl ! j = Pl2 ! i" 
        unfolding j_def
        apply (metis False Nitpick.size_list_simp(2) Suc_lessD Suc_pred less_Suc_eq ndl(2) nth_tl si zero_less_Suc)
        using \<open>Pl ! j = Pl2 ! i\<close> j_def by blast             
        have "Suc j < length ndl" using j_def ndl(1) ndl_def si by auto
        thus ?thesis apply(intro exI[of _ j]) using si unfolding 2 3 sl by auto 
      qed
    qed
  qed
qed
     
lemma tracksPers_transSl_impl_ex_descentPath_repeat: 
assumes ndl: "cycleG ndl" and tr: "tracksPers K ndl" and P: "transSl K P P' sl"
shows "\<exists> Pl n. n \<noteq> 0 \<and> wfLabL (repeat n (butlast ndl) @ [last ndl]) Pl \<and> 
               descentPathParam (repeat n (butlast ndl) @ [last ndl]) Pl sl \<and> 
               hd Pl = P \<and> last Pl = P'" 
proof-
  have ndlNe[simp]: "ndl \<noteq> []" and pndl[simp]: "pathG ndl" 
  and ndlhl[simp]: "hd ndl = last ndl"
  using cycleG_def ndl not_path_Nil by auto
  show ?thesis using P proof(induction)
    case (Base P P' sl)
    then obtain Pl sll where Pl: "descentPathSl ndl Pl sll" "hd Pl = P" "last Pl = P'"
    and sl: "sl = MaxSl (set sll)" using tr unfolding tracksPers_def by blast
    then show ?case apply(intro exI[of _ Pl] exI[of _ "Suc 0"])
    using descentPathSl_wfLabL descentPathSl_descentPathParam by auto
  next
    case (Step P P' sl1 P'' sl2)
    then obtain Pl1 n1 where n1: "n1 \<noteq> 0" and Pl: 
    "wfLabL (repeat n1 (butlast ndl) @ [last ndl]) Pl1"
    "descentPathParam (repeat n1 (butlast ndl) @ [last ndl]) Pl1 sl1"
    "hd Pl1 = P" "last Pl1 = P'" by auto
    from `K P' P'' sl2`
    obtain Pl2 sll2 where "descentPathSl ndl Pl2 sll2" and htPl2: "hd Pl2 = P'" "last Pl2 = P''"
    and sl2: "sl2 = MaxSl (set sll2)" using tr unfolding tracksPers_def by blast
    hence Pl2: "wfLabL ndl Pl2" "descentPathParam ndl Pl2 sl2"
    using descentPathSl_wfLabL descentPathSl_descentPathParam by auto  

    have 0: "repeat (Suc n1) (butlast ndl) @ [last ndl] = 
             (repeat n1 (butlast ndl) @ [last ndl]) @ tl ndl"
    unfolding repeat_Suc2 
    by (metis append.assoc append_Cons append_Nil 
     append_butlast_last_id list.exhaust_sel ndlNe ndlhl)

    have Pl1facts[simp]: "length Pl1 = Suc (n1 * (length ndl - Suc 0))"
    using Pl(1) wfLabL_def by auto

    have Pl2facts[simp]: "Pl2 \<noteq> []" "length Pl2 = length ndl" 
      "length (tl Pl2) = length ndl - Suc 0"
    using \<open>descentPathSl ndl Pl2 sll2\<close> descentPathSl_def by  auto

    show ?case apply(intro exI[of _ "Pl1 @ tl Pl2"] exI[of _ "Suc n1"]) apply safe
      subgoal unfolding 0 apply(subst wfLabL_append)
        subgoal by simp
        subgoal by simp
        subgoal apply safe
          subgoal by fact
          subgoal using Pl2(1) ndlNe wfLabL_tl by blast . .
      subgoal unfolding 0  apply(rule descentPathParam_append) 
        subgoal by simp
        subgoal by simp
        subgoal by simp
        subgoal by simp
        subgoal by fact  
        subgoal by fact 
        subgoal by simp
        subgoal by (simp add: Pl(4) htPl2(1)) .
      subgoal by (metis Pl(3) Pl1facts hd_append list.size(3) old.nat.distinct(2))
      subgoal by (metis Pl(4) Pl2facts(1) append.right_neutral 
       htPl2(1) htPl2(2) last.simps last_appendR list.exhaust_sel) .
  qed
qed

lemma tracksPers_transSl_impl_ex_descentPathSlS: 
assumes ndl: "cycleG ndl" and tr: "tracksPers K ndl" and K: "(\<exists>P. transSl K P P Decr)"
shows "\<exists> Ps. descentIpathS (srepeat (butlast ndl)) Ps"
using cycle_descentPath_repeat_imp_descentIPathS_srepeat[OF ndl]
using tracksPers_transSl_impl_ex_descentPath_repeat[OF ndl tr, where sl = Decr]
using K unfolding descentPath_descentPathParam[symmetric] by metis 

lemma wfLabL_descentPathParam_append_inverse: 
fixes ndl1 ndl2
defines "ndl \<equiv> ndl1 @ tl ndl2"
assumes ndl: "length ndl1 \<ge> 2" "length ndl2 \<ge> 2" "last ndl1 = hd ndl2"
and w: "wfLabL ndl Pl" and d: "descentPathParam ndl Pl sl"
shows "\<exists>Pl1 Pl2 sl1 sl2. 
  Pl = Pl1 @ (tl Pl2) \<and> sl = MaxSl {sl1,sl2} \<and> last Pl1 = hd Pl2 \<and> 
  wfLabL ndl1 Pl1 \<and> descentPathParam ndl1 Pl1 sl1 \<and> 
  wfLabL ndl2 Pl2 \<and> descentPathParam ndl2 Pl2 sl2"
proof-
  have "ndl1 \<noteq> []" "ndl2 \<noteq> []" using ndl by force+ 
  note ndl = this ndl(3) ndl(1,2)
  define l1 where l1: "l1 \<equiv> length ndl1"  
  define Pl1 Pl2 where Pl1: "Pl1 \<equiv> take l1 Pl" and Pl2: "Pl2 \<equiv> drop (l1-Suc 0) Pl" 
  have lPl: "length Pl = length ndl1 + length ndl2 - Suc 0" 
  using w unfolding wfLabL_def by (simp add: ndl_def Suc_leI ndl(2))
  have Plne: "Pl \<noteq> []" "Pl1 \<noteq> []" "Pl2 \<noteq> []"
  using Suc_diff_Suc lPl ndl(1) ndl(2) apply fastforce
  apply (metis Pl1 Suc_pred add_pos_pos l1 lPl length_greater_0_conv list.size(3) ndl(1-2) one_is_add take_eq_Nil)
  by (metis Pl2 Suc_pred add_diff_cancel_left' add_pos_pos diff_Suc_Suc l1 lPl length_drop 
    length_greater_0_conv ndl(1) ndl(2)) 
  have lPl1: "length Pl1 = l1"  
  by (metis Pl1 Suc_pred add_diff_cancel_left' add_gr_0 drop_all l1 lPl length_drop 
     length_greater_0_conv length_take min.absorb2 ndl(2) not_less_eq_eq)
  have lPl2: "length Pl2 = length ndl2" by (simp add: Pl2 l1 lPl ndl(1))
    
  have Pl: "Pl = Pl1 @ tl Pl2"  
  by (metis One_nat_def Pl1 Pl2 Suc_pred' append_take_drop_id drop_Suc l1 length_greater_0_conv ndl(1) tl_drop)
  have lstPl1: "last Pl1 = Pl!(l1-Suc 0)"  
  by (metis One_nat_def Pl Plne(2) diff_less lPl1 last_conv_nth length_greater_0_conv lessI nth_append)
  have hdPl2: "hd Pl2 = Pl!(l1-Suc 0)" using Pl2 Plne(3) drop_all hd_drop_conv_nth not_less by blast
  have lh: "last Pl1 = hd Pl2" by (simp add: hdPl2 lstPl1)

  have s0l1: "0 < l1" "Suc 0 < l1" using assms(2) l1 by linarith+
  have s0l2: "0 < length ndl2" "Suc 0 < length ndl2" using assms(3) by auto
  have s0l: "0 < length ndl" "Suc 0 < length ndl" using l1 ndl_def s0l1 by auto

  have Pli[simp]: "\<And>i. i < l1 \<Longrightarrow> Pl1 ! i = Pl ! i" "\<And>i. i < l1 \<Longrightarrow> ndl1 ! i = ndl ! i"
  "\<And>i. i < length ndl2 \<Longrightarrow> Pl2 ! i = Pl ! (l1 + i - Suc 0)"
  "\<And>i. i < length ndl2 \<Longrightarrow> ndl2 ! i = ndl ! (l1 + i - Suc 0)"
  subgoal by (simp add: Pl1 l1 ndl_def nth_append)
  subgoal by (simp add: Pl1 l1 ndl_def nth_append) 
  subgoal for i using Pl1 Pl2 Plne(2) Plne(3) by auto
  subgoal for i unfolding ndl_def apply(cases "i=0")
    subgoal apply(subst nth_append)  
    by simp (metis One_nat_def Plne(2) diff_Suc_1 gr0_implies_Suc hd_conv_nth l1 lPl1 last_conv_nth 
         length_greater_0_conv less_Suc_eq ndl(3)) 
    subgoal apply(subst nth_append) 
    by simp (metis One_nat_def Suc_eq_plus1 Suc_pred add_diff_cancel_left add_gr_0 hd_Cons_tl l1 
         less_add_same_cancel1 ndl(2) not_less_eq nth_Cons_Suc) . . 

  have "wfLabL ndl1 Pl1" using w lPl1 unfolding wfLabL_def by (metis l1 ndl_def Pl add_strict_mono lPl less_diff_conv nth_append_left s0l2(2))
  have "wfLabL ndl2 Pl2" using w Pl2 Pli(2) lPl2 s0l1 unfolding wfLabL_def by (auto simp add: lPl2) 

  show ?thesis proof(rule exI[of _ Pl1], rule exI[of _ Pl2]) 
    show "\<exists>sl1 sl2. 
      Pl = Pl1 @ (tl Pl2) \<and> sl = MaxSl {sl1,sl2} \<and> last Pl1 = hd Pl2 \<and> 
      wfLabL ndl1 Pl1 \<and> descentPathParam ndl1 Pl1 sl1 \<and> 
      wfLabL ndl2 Pl2 \<and> descentPathParam ndl2 Pl2 sl2"
    proof(cases sl)
      case Main note sl = Main[simp]
      have 0: "\<And>ii. Suc ii < length ndl \<Longrightarrow> RR (ndl ! ii, Pl ! ii) (ndl ! Suc ii, Pl ! Suc ii) Main"
      using d unfolding descentPathParam_def by (simp add: Pl l1 lPl1 lPl2 ndl_def)
      show ?thesis proof(intro exI[of _ Main], safe) 
        show "Pl = Pl1 @ tl Pl2" "last Pl1 = hd Pl2" "wfLabL ndl1 Pl1" "wfLabL ndl2 Pl2" by fact+
        show "sl = MaxSl {Main, Main}" unfolding MaxSl_def by simp
        show "descentPathParam ndl1 Pl1 Main" unfolding descentPathParam_def apply(intro conjI allI impI)
          subgoal for i unfolding l1[symmetric]  
          by (smt "0" Pl Pli(1,2) Suc_lessD Suc_less_eq Suc_pred add_gr_0 l1 lPl lPl1 lPl2 length_append 
          length_greater_0_conv length_tl less_add_same_cancel1 less_trans_Suc ndl(2) ndl_def)  
          subgoal apply(rule exI[of _ 0]) apply safe
            subgoal using ndl by linarith
            subgoal using 0[of 0] using s0l1 s0l by (simp add: l1) . .     
        show "descentPathParam ndl2 Pl2 Main" unfolding descentPathParam_def apply(intro conjI allI impI)
          subgoal for i by simp (smt "0" Nat.add_diff_assoc2 One_nat_def Pl Suc_leI add_Suc_right add_eq_if 
            l1 lPl lPl1 lPl2 length_append length_tl nat_add_left_cancel_less ndl_def not_gr_zero s0l1(1)) 
          subgoal apply(rule exI[of _ 0]) apply safe
            subgoal using ndl by linarith
            subgoal using 0[of 0] using s0l2 s0l  
            by simp (metis "0" One_nat_def Suc_pred l1 length_append length_tl 
             less_Suc_eq less_add_same_cancel1 ndl_def plus_1_eq_Suc s0l1(1)) . .
        qed
      next
        case Decr note sl = Decr
        then obtain ii where 
        ii: "Suc ii < length ndl" "RR (ndl ! ii, Pl ! ii) (ndl ! Suc ii, Pl ! Suc ii) Decr" 
        using d unfolding descentPathParam_def by auto
        (* have lii: "length ndl1 + Suc (Suc ii - length ndl1) - Suc 0 = Suc ii" apply simp sledgehammer *)
        define sl1 sl2 where 
        "sl1 \<equiv> if (\<exists>i. Suc i  <length ndl1 \<and> RR (ndl1 ! i, Pl1 ! i) (ndl1 ! Suc i, Pl1 ! Suc i) Decr) 
             then Decr else Main" and 
        "sl2 \<equiv> if (\<exists>i. Suc i < length ndl2 \<and> RR (ndl2 ! i, Pl2 ! i) (ndl2 ! Suc i, Pl2 ! Suc i) Decr) 
             then Decr else Main"
        have sl12: "sl1 = Decr \<or> sl2 = Decr"
        using ii apply (cases "ii < l1")
          subgoal apply (cases "Suc ii = l1")
            subgoal apply(subgoal_tac "sl2 = Decr") 
              subgoal by simp 
              subgoal using s0l2(2) unfolding sl2_def by (auto intro!: exI[of _ "0"]) .                 
            subgoal apply(subgoal_tac "sl1 = Decr") 
              subgoal by simp           
              subgoal using Suc_lessD l1 unfolding sl1_def by (auto intro!: exI[of _ ii]) . .
            subgoal apply(subgoal_tac "sl2 = Decr") 
              subgoal by simp
                subgoal using Suc_lessD l1 unfolding sl2_def  
                by (auto intro!: exI[of _ "Suc ii - l1"],simp add: ndl_def) . .

        show ?thesis proof(rule exI[of _ sl1], rule exI[of _ sl2], safe) 
          show "Pl = Pl1 @ tl Pl2" "last Pl1 = hd Pl2" "wfLabL ndl1 Pl1" "wfLabL ndl2 Pl2" by fact+
          show "sl = MaxSl {sl1, sl2}" using sl12 sl unfolding MaxSl_def by auto
          have 1: "\<And>i. Suc i < length ndl1 \<Longrightarrow>
                    RR (ndl1 ! i, Pl1 ! i) (ndl1 ! Suc i, Pl1 ! Suc i) Main \<or>
                    \<not> RR (ndl1 ! i, Pl1 ! i) (ndl1 ! Suc i, Pl1 ! Suc i) Main \<and>
                    RR (ndl1 ! i, Pl1 ! i) (ndl1 ! Suc i, Pl1 ! Suc i) Decr \<and> sl1 = Decr"
          using d sl unfolding sl1_def unfolding l1[symmetric] unfolding descentPathParam_def 
          by (smt Pl Suc_lessD Suc_less_eq Suc_pred add_gr_0 l1 lPl lPl1 lPl2 
              length_append length_tl less_add_same_cancel1 less_trans_Suc ndl_def nth_append s0l2(1))
          show "descentPathParam ndl1 Pl1 sl1" unfolding descentPathParam_def apply(intro conjI allI impI)
            subgoal by fact 
            subgoal apply (cases sl1)
              subgoal using 1 l1 s0l1(2) by blast
              subgoal using sl1_def slope.distinct(1) by presburger . .
          have 2: "\<And>i. Suc i < length ndl2 \<Longrightarrow>
              RR (ndl2 ! i, Pl2 ! i) (ndl2 ! Suc i, Pl2 ! Suc i) Main \<or>
              \<not> RR (ndl2 ! i, Pl2 ! i) (ndl2 ! Suc i, Pl2 ! Suc i) Main \<and>
              RR (ndl2 ! i, Pl2 ! i) (ndl2 ! Suc i, Pl2 ! Suc i) Decr \<and> sl2 = Decr"
          using d sl unfolding sl2_def unfolding l1[symmetric] unfolding descentPathParam_def  
          by simp (smt Nat.add_diff_assoc Nat.add_diff_assoc2 wfLabL_def Suc_pred add_diff_cancel_left' 
                 add_gr_0 l1 lPl le_add1 nat_add_left_cancel_less plus_1_eq_Suc s0l1(1) w)
          show "descentPathParam ndl2 Pl2 sl2" unfolding descentPathParam_def apply(intro conjI allI impI)
            subgoal by fact
            subgoal apply (cases sl2)
              subgoal using 2 s0l2(2) by blast
              subgoal using sl2_def slope.distinct(1) by presburger . .               
      qed
    qed
  qed
qed

lemma wfLabL_descentPathParam_imp_descentPathSl:
assumes w: "wfLabL ndl Pl" and d: "descentPathParam ndl Pl sl"  
shows "\<exists>sll. descentPathSl ndl Pl sll \<and> sl = MaxSl (set sll)"
proof-
  have l[simp]: "length Pl = length ndl" 
  using assms(1) wfLabL_def by auto
   
  define sll where "sll = 
  fToList (length ndl - Suc 0) 
   (\<lambda>i. if RR (ndl!i,Pl!i) (ndl!(Suc i),Pl!(Suc i)) sl then sl else 
        if RR (ndl!i,Pl!i) (ndl!(Suc i),Pl!(Suc i)) Main then Main else Decr
   )"
  have lsll[simp]: "length sll = length ndl - Suc 0" unfolding sll_def by simp
  have sll: 
  "\<And>i. i < length ndl - Suc 0 \<Longrightarrow> 
       RR (ndl!i,Pl!i) (ndl!(Suc i),Pl!(Suc i)) sl \<Longrightarrow> sll!i = sl"
  "\<And>i. i < length ndl - Suc 0 \<Longrightarrow> 
        RR (ndl!i,Pl!i) (ndl!(Suc i),Pl!(Suc i)) Main \<Longrightarrow>
       \<not>RR (ndl!i,Pl!i) (ndl!(Suc i),Pl!(Suc i)) Decr
        \<Longrightarrow> sll!i = Main"
  "\<And>i. i < length ndl - Suc 0 \<Longrightarrow> 
       \<not>RR (ndl!i,Pl!i) (ndl!(Suc i),Pl!(Suc i)) Main \<Longrightarrow>
        RR (ndl!i,Pl!i) (ndl!(Suc i),Pl!(Suc i)) Decr
        \<Longrightarrow> sll!i = Decr"  
  unfolding sll_def using slope.exhaust by auto

  show ?thesis apply(rule exI[of _ sll]) apply safe
    subgoal unfolding descentPathSl_def apply safe
      subgoal by fact
      subgoal by simp
      subgoal using d sll(2,3) unfolding descentPathParam_def  
      by (metis (full_types) One_nat_def add.commute less_diff_conv plus_1_eq_Suc 
            slope.exhaust) .
    subgoal using d sll(1) unfolding descentPathParam_def MaxSl_def 
    by (smt Nitpick.size_list_simp(2) One_nat_def Suc_less_eq add_lessD1 
        in_set_conv_nth length_greater_0_conv length_tl lsll plus_1_eq_Suc slope.exhaust) .
qed
     
lemma ex_descentPath_repeat_impl_tracksPers_transSl: 
assumes ndl: "cycleG ndl" and tr: "tracksPers K ndl" and n: "n \<noteq> 0" and  
Pl: "wfLabL (repeat n (butlast ndl) @ [last ndl]) Pl" 
    "descentPathParam (repeat n (butlast ndl) @ [last ndl]) Pl sl" 
shows "transSl K (hd Pl) (last Pl) sl"
proof-
  have ndlNe[simp]: "ndl \<noteq> []" and pndl[simp]: "pathG ndl" 
  and ndlhl[simp]: "hd ndl = last ndl"
  using cycleG_def ndl not_path_Nil by auto
  have tlndl[simp]: "tl ndl \<noteq> []" 
    by (metis hd_Cons_tl ndlNe not_path_singl pndl)
  show ?thesis using n Pl proof(induction n arbitrary: Pl sl)
    case (0 Pl sl)
    then show ?case by auto
  next
    case (Suc n1 Pl sl) 
    have 0: "repeat (Suc n1) (butlast ndl) @ [last ndl] = 
             (repeat n1 (butlast ndl) @ [last ndl]) @ tl ndl"
    unfolding repeat_Suc2 
    by (metis append.assoc append_Cons append_Nil 
     append_butlast_last_id list.exhaust_sel ndlNe ndlhl)

    define ndll where "ndll \<equiv> repeat n1 (butlast ndl) @ [last ndl]"
    
    have ndll[simp]: "ndll \<noteq> []" and lndll: "last ndll = hd ndl" 
    using ndll_def apply blast by (simp add: ndll_def)
  
    show ?case proof(cases "n1=0")
      case True
      hence 0: "repeat (Suc n1) (butlast ndl) @ [last ndl] = ndl" by simp
      hence "wfLabL ndl Pl" "descentPathParam ndl Pl sl" using Suc by auto
      then obtain sll where "descentPathSl ndl Pl sll" and sl: "sl = MaxSl (set sll)" 
      using wfLabL_descentPathParam_imp_descentPathSl by blast
      hence "K (hd Pl) (last Pl) sl" using tr unfolding tracksPers_def by auto
      thus ?thesis by (intro transSl.Base)
    next
      case False

      have [simp]: "2 \<le> length ndl" "2 \<le> length ndll"
      using cycle_iff_nth ndl unfolding ndll_def using False by auto

      obtain Pl1 sl1 Pl2 sl2 where Pl: "Pl = Pl1 @ tl Pl2"
      and sl: "sl = MaxSl {sl1, sl2}" and l: "last Pl1 = hd Pl2"
      and Pl1: "wfLabL ndll Pl1" "descentPathParam ndll Pl1 sl1" 
      and Pl2: "wfLabL ndl Pl2" "descentPathParam ndl Pl2 sl2" 
      using wfLabL_descentPathParam_append_inverse[OF _ _ lndll 
             Suc.prems(2,3)[unfolded 0 ndll_def[symmetric]]] by auto
      then obtain sll2 where "descentPathSl ndl Pl2 sll2" and sl2: "sl2 = MaxSl (set sll2)"
      using wfLabL_descentPathParam_imp_descentPathSl by blast
      hence K2: "K (hd Pl2) (last Pl2) sl2" using tr unfolding tracksPers_def by auto

      have ne: "Pl1 \<noteq> [] \<and> tl Pl2 \<noteq> []" using Pl1(1) Pl2(1) wfLabL_def 
      by (metis length_greater_0_conv ndlNe ndll tlndl wfLabL_tl) 
      have h12: "hd Pl1 = hd Pl" "last Pl2 = last Pl"
      unfolding Pl by (auto simp: ne last_tl)

      from Suc.IH[unfolded ndll_def[symmetric], OF False Pl1]
      have K1: "transSl K (hd Pl1) (last Pl1) sl1" . 
      show ?thesis using transSl.Step[OF K1[unfolded l] K2, unfolded sl[symmetric] h12] .
    qed 
  qed
qed 

lemma tracksPers_ex_descentPathSlS_impl_loopsDecr: 
assumes ndl: "cycleG ndl" and tr: "tracksPers K ndl" 
and d: "descentIpathS (srepeat (butlast ndl)) Ps"
shows "\<exists>P. transSl K P P Decr" 
using cycle_descentIPathS_srepeat_imp_descentPath_repeat[OF ndl d]
using ex_descentPath_repeat_impl_tracksPers_transSl[OF ndl tr, where sl = Decr]
unfolding descentPath_descentPathParam[symmetric] by metis

lemma tracksPers_transSl_iff_ex_descentIpathS: 
assumes "cycleG ndl" "tracksPers K ndl"
shows "(\<exists>P. transSl K P P Decr) \<longleftrightarrow> (\<exists> Ps. descentIpathS (srepeat (butlast ndl)) Ps)"
using assms Node_finite tracksPers_transSl_impl_ex_descentPathSlS tracksPers_ex_descentPathSlS_impl_loopsDecr 
by blast

definition "allOmegaCyclesDescendS \<equiv> 
  \<forall>ndl. cycleG ndl \<longrightarrow> (\<exists> Ps. descentIpathS (srepeat (butlast ndl)) Ps)"

(**************************************************)
(**************************************************)
(**************************************************)
(**************************************************)
(**************************************************)

proposition TransitiveLoopingCcl_iff_allOmegaCyclesDescendS:
"TransitiveLoopingCcl \<longleftrightarrow> allOmegaCyclesDescendS"
using tracksPers_transSl_iff_ex_descentIpathS
unfolding TransitiveLoopingCcl_def allOmegaCyclesDescendS_def 
using Ccl_nodes cycleG_def tracksPers_leftTotal Node_finite
by (metis (no_types, opaque_lifting) empty_iff tracksPers_rightTotal)

lemma InfiniteDescent_imp_InfiniteDescent: 
assumes "InfiniteDescent"
shows "allOmegaCyclesDescendS"
using InfiniteDescent_def allOmegaCyclesDescendS_def assms cycle_srepeat_ipath 
srepeat_cycle_descentIpath_imp_descentIpath by blast

proposition allOmegaCyclesDescendS_implies_InfiniteDescent:
"allOmegaCyclesDescendS \<longrightarrow> InfiniteDescent" 
proof(rule impI, rule ccontr, unfold VLA_Criterion)
  assume omega: allOmegaCyclesDescendS and
         lang_inc:"\<not> NBA.language Paut\<^sub>V \<subseteq> NBA.language Taut\<^sub>V"
  then obtain v u where lasso_in:"v @- srepeat u \<in> NBA.language Paut\<^sub>V"
                    and lasso_nin:"v @- srepeat u \<notin> NBA.language Taut\<^sub>V" 
                    and u_ne:"u \<noteq>[]"
    apply-by(drule prop1'[OF alpha_subseq_PTaut\<^sub>V finite_Nodes_Paut\<^sub>V finite_Nodes_Taut\<^sub>V], elim exE conjE)

  also have alw_Node:"alw (holdsS Node) (v @- srepeat u)"
            and ipath:"ipath (v @- srepeat u)" 
    using lasso_in unfolding Paut\<^sub>V_lang ipath_def by auto

  have nn:"2 \<le> length v + length (u @ [hd u])" using u_ne by (cases u, auto) 

  have path_v:"pathG (v @ u @ [hd u])"
    using ipath_stake_path[OF ipath nn]
    unfolding stake_add[symmetric] stake_len_append sdrop_shift_length' 
              length_append_singleton stake_Suc stake_cycle_eq[OF u_ne] 
              srepeat_snth[OF u_ne] hd_conv_nth[OF u_ne] by auto

  have "cycleG (u @ [hd u])"
    unfolding cycleG_def using u_ne path_appendR[OF path_v] by auto

  then obtain Ps where descentS:"descentIpathS (srepeat u) Ps"
    using omega unfolding allOmegaCyclesDescendS_def by auto
  hence descent:"descentIpath (srepeat u) Ps" using descentIpathS_imp_descentIpath by auto

  then obtain Ps' where Ps':"descentIpath (v @- srepeat u) Ps'"
    using descentIpath_sdrop_any[of "length v", of "v @- srepeat u" Ps] 
    unfolding sdrop_shift_length' by auto

  thus "HOL.False" using lasso_nin alw_Node unfolding Taut\<^sub>V_lang by auto 
qed

corollary Relation_Based_Criterion: 
"InfiniteDescent \<longleftrightarrow> TransitiveLoopingCcl"
using allOmegaCyclesDescendS_implies_InfiniteDescent InfiniteDescent_imp_InfiniteDescent 
TransitiveLoopingCcl_iff_allOmegaCyclesDescendS by blast

theorem Relation_Based_Criterion': 
"InfiniteDescent \<longleftrightarrow> TransitiveLooping"
using TransitiveLooping_iff_TransitiveLoopingCcl Relation_Based_Criterion 
by fastforce

end (* context Sloped_Graph *)
end
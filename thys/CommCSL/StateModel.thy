subsection \<open>Extended Heaps\<close>

theory StateModel
  imports FractionalHeap "HOL-Library.Multiset"
begin

type_synonym loc = nat
type_synonym val = nat

text \<open>We store the initial value with the unique guard\<close>

type_synonym f_heap = "(loc, val) fract_heap"
type_synonym 'a gs_heap = "(prat \<times> 'a multiset) option"
type_synonym ('i, 'a) gu_heap = "'i \<Rightarrow> 'a list option"

(* 'a = type of action, 'v = type of value *)
type_synonym ('i, 'a) heap = "f_heap \<times> 'a gs_heap \<times> ('i, 'a) gu_heap"

type_synonym  var   = string                (*r Variables *)
type_synonym  normal_heap  = "(nat \<rightharpoonup> nat)"        (*r Heaps *)
type_synonym  store = "(var \<Rightarrow> nat)"        (*r Stacks *)

fun get_fh where "get_fh x = fst x"
fun get_gs where "get_gs x = fst (snd x)"
fun get_gu where "get_gu x = snd (snd x)"

text \<open>Two "heaps" are compatible iff:
1. The fractional heaps have the same common values and sum to at most 1
2. The unique guard heaps are disjoint
3. The shared guards permissions sum to at most 1\<close>

definition compatible :: "('i, 'a) heap \<Rightarrow> ('i, 'a) heap \<Rightarrow> bool" (infixl "##" 60) where
  "h ## h' \<longleftrightarrow> compatible_fract_heaps (get_fh h) (get_fh h') \<and> (\<forall>k. get_gu h k = None \<or> get_gu h' k = None)
  \<and> (\<forall>p p'. get_gs h = Some p \<and> get_gs h' = Some p' \<longrightarrow> pgte pwrite (padd (fst p) (fst p')))"

lemma compatibleI:
  assumes "compatible_fract_heaps (get_fh h) (get_fh h')"
      and "\<And>k. get_gu h k = None \<or> get_gu h' k = None"
      and "\<And>p p'. get_gs h = Some p \<and> get_gs h' = Some p' \<Longrightarrow> pgte pwrite (padd (fst p) (fst p'))"
    shows "h ## h'"
  using assms(1) assms(2) assms(3) compatible_def by blast


fun add_gu_single where
  "add_gu_single None x = x"
| "add_gu_single x None = x"

definition add_gu where
  "add_gu u1 u2 k = add_gu_single (u1 k) (u2 k)"

lemma comp_add_gu_comm:
  assumes "\<And>k. h k = None \<or> h' k = None"
  shows "add_gu h h' = add_gu h' h"
proof (rule ext)
  fix k show "add_gu h h' k = add_gu h' h k"
    by (metis add_gu_def add_gu_single.simps(1) add_gu_single.simps(2) assms not_None_eq)
qed

fun add_gs :: "(prat \<times> 'a multiset) option \<Rightarrow> (prat \<times> 'a multiset) option \<Rightarrow> (prat \<times> 'a multiset) option"
  where
  "add_gs None x = x"
| "add_gs x None = x"
| "add_gs (Some p) (Some p') = Some (padd (fst p) (fst p'), snd p + snd p')"

lemma add_gs_cancellative:
  assumes "add_gs a x = add_gs b x"
  shows "a = b"
  apply (cases x)
   apply (metis add_gs.elims assms not_None_eq)
  apply (cases a)
  apply (cases b)
  apply simp
   apply (metis add_gs.simps(1) add_gs.simps(3) assms fst_conv not_pgte_charact option.sel padd_comm pgt_implies_pgte sum_larger)
  apply (cases b)
  apply (metis add_gs.simps(1) add_gs.simps(3) assms fst_conv not_pgte_charact option.sel padd_comm pgt_implies_pgte sum_larger)
proof -
  fix xx aa bb assume "x = Some xx" "a = Some aa" "b = Some bb"
  then have "fst aa = fst bb"
    using assms padd_cancellative[of "padd (fst aa) (fst xx)"]
     Pair_inject add_gs.simps(3) option.inject by auto
  moreover have "snd aa = snd bb"
    using add_left_cancel[of "snd xx" "snd aa" "snd bb"]
    using \<open>a = Some aa\<close> \<open>b = Some bb\<close> \<open>x = Some xx\<close> assms by auto
  ultimately show "a = b"
    by (simp add: \<open>a = Some aa\<close> \<open>b = Some bb\<close> prod_eq_iff)
qed

lemma add_gs_comm:
  "add_gs a b = add_gs b a"
proof (cases a)
  case None
  then show ?thesis
    by (metis add_gs.elims add_gs.simps(1) add_gs.simps(2))
next
  case (Some aa)
  then have "a = Some aa" by simp
  then show ?thesis
  proof (cases b)
    case None
    then show ?thesis
      using Some by force
  next
    case (Some bb)
    moreover have "padd (fst aa) (fst bb) = padd (fst bb) (fst aa) \<and> snd aa + snd bb = snd bb + snd aa"
      using padd_comm by force
    ultimately show ?thesis
      using \<open>a = Some aa\<close> by force
  qed
qed

lemma compatible_fheaps_comm:
  assumes "compatible_fract_heaps a b"
  shows "add_fh a b = add_fh b a"
proof (rule ext)
  fix x show "add_fh a b x = add_fh b a x"
  proof (cases "a x")
    case None
    then show ?thesis
      by (metis add_fh_def add_fh_def fadd_options.simps(1) fadd_options.simps(2) option.exhaust_sel)
  next
    case (Some aa)
    then have "a x = Some aa" by simp
    then show ?thesis
    proof (cases "b x")
      case None
      then show ?thesis
        by (simp add: Some add_fh_def)
    next
      case (Some bb)
      then show ?thesis
        using \<open>a x = Some aa\<close> add_fh_def[of a b] add_fh_def[of b a] assms compatible_fract_heapsE(2) fadd_options.simps(3) padd_comm
        by (metis (full_types))
    qed
  qed
qed

fun plus :: "('i, 'a) heap option \<Rightarrow> ('i, 'a) heap option \<Rightarrow> ('i, 'a) heap option" (infixl "\<oplus>" 63) where
  "None \<oplus> _ = None"
| "_ \<oplus> None = None"
| "Some h1 \<oplus> Some h2 = (if h1 ## h2 then Some (add_fh (get_fh h1) (get_fh h2), add_gs (get_gs h1) (get_gs h2), add_gu (get_gu h1) (get_gu h2)) else None)"

lemma plus_extract:
  assumes "Some x = Some a \<oplus> Some b"
  shows "get_fh x = add_fh (get_fh a) (get_fh b)"
    and "get_gs x = add_gs (get_gs a) (get_gs b)"
    and "get_gu x = add_gu (get_gu a) (get_gu b)"
    apply (metis assms eq_fst_iff get_fh.simps option.inject option.simps(3) plus.simps(3))
   apply (metis assms fst_eqD get_gs.simps option.distinct(1) option.inject plus.simps(3) snd_conv)
  by (metis assms get_gu.elims option.distinct(1) option.sel plus.simps(3) snd_conv)

lemma compatible_eq:
  "Some a \<oplus> Some b = None \<longleftrightarrow> \<not> a ## b"
  by simp

lemma compatible_comm:
  "a ## b \<longleftrightarrow> b ## a"
proof -
  have "\<And>a b. a ## b \<Longrightarrow> b ## a"
  proof -
    fix a b assume asm0: "a ## b"
    show "b ## a"
    proof (rule compatibleI)
      show "compatible_fract_heaps (get_fh b) (get_fh a)"
        using asm0 compatible_def compatible_fract_heaps_comm by blast
      show "\<And>k. get_gu b k = None \<or> get_gu a k = None"
        by (meson asm0 compatible_def)
      show "\<And>p p'. get_gs b = Some p \<and> get_gs a = Some p' \<Longrightarrow> pgte pwrite (padd (fst p) (fst p'))"
        by (metis asm0 compatible_def padd_comm)
    qed
  qed
  then show ?thesis
    by blast
qed

lemma heap_ext:
  assumes "get_fh a = get_fh b"
      and "get_gs a = get_gs b"
      and "get_gu a = get_gu b"
    shows "a = b"
  by (metis assms(1) assms(2) assms(3) get_fh.simps get_gs.simps get_gu.elims prod.expand)

lemma plus_comm:
  "a \<oplus> b = b \<oplus> a"
proof -
  have r: "\<And>x a b. Some x = Some a \<oplus> Some b \<Longrightarrow> Some x = Some b \<oplus> Some a"
  proof -
    fix x a b assume asm0: "Some x = Some a \<oplus> Some b"
    then obtain y where "Some y = Some b \<oplus> Some a"
      by (metis compatible_comm plus.simps(3))
    have "x = y"
    proof (rule heap_ext)
      show "get_fh x = get_fh y"
        by (metis \<open>Some y = Some b \<oplus> Some a\<close> asm0 compatible_def compatible_eq compatible_fheaps_comm plus_extract(1))
      show "get_gs x = get_gs y"
        by (metis \<open>Some y = Some b \<oplus> Some a\<close> add_gs_comm asm0 plus_extract(2))
      show "get_gu x = get_gu y" using comp_add_gu_comm[of "get_gu x" "get_gu y"]
        by (metis \<open>Some y = Some b \<oplus> Some a\<close> asm0 comp_add_gu_comm compatible_def compatible_eq plus_extract(3))
    qed
    then show "Some x = Some b \<oplus> Some a"
      by (simp add: \<open>Some y = Some b \<oplus> Some a\<close>)
  qed
  then show ?thesis
  proof (cases "a \<oplus> b")
    case None
    then show ?thesis
      by (metis (no_types, opaque_lifting) compatible_comm compatible_eq plus.elims)
  next
    case (Some ab)
    then have "a = Some (the a) \<and> b = Some (the b)"
      by (metis option.collapse option.distinct(1) plus.simps(1) plus.simps(2))
    then show ?thesis
      by (metis \<open>\<And>x b a. Some x = Some a \<oplus> Some b \<Longrightarrow> Some x = Some b \<oplus> Some a\<close> plus.elims)
  qed
qed


lemma asso2:
  assumes "Some a \<oplus> Some b = Some ab"
      and "\<not> b ## c"
    shows "\<not> ab ## c"
proof (cases "compatible_fract_heaps (get_fh b) (get_fh c)")
  case True
  then have "(\<exists>k. get_gu b k \<noteq> None \<and> get_gu c k \<noteq> None)
  \<or> (\<exists>p p'. get_gs b = Some p \<and> get_gs c = Some p' \<and> pgt (padd (fst p) (fst p')) pwrite)"
    by (metis assms(2) compatible_def not_pgte_charact)
  then show ?thesis
  proof (cases "\<exists>k. get_gu b k \<noteq> None \<and> get_gu c k \<noteq> None")
    case True
    then obtain k where "get_gu b k \<noteq> None \<and> get_gu c k \<noteq> None"
      by auto
    then have "get_gu ab k \<noteq> None"
      using add_gu_def[of "get_gu a" "get_gu b"] add_gu_single.simps(1) assms(1) compatible_def compatible_eq option.distinct(1) plus_extract(3)
      by metis
    then show ?thesis
      by (meson \<open>get_gu b k \<noteq> None \<and> get_gu c k \<noteq> None\<close> compatible_def)
  next
    case False
    then obtain p p' where "get_gs b = Some p \<and> get_gs c = Some p' \<and> pgt (padd (fst p) (fst p')) pwrite"
      using \<open>(\<exists>k. get_gu b k \<noteq> None \<and> get_gu c k \<noteq> None) \<or> (\<exists>p p'. get_gs b = Some p \<and> get_gs c = Some p' \<and> pgt (padd (fst p) (fst p')) pwrite)\<close> by blast
    moreover have "get_gs ab = add_gs (get_gs a) (Some p)"
      by (metis assms(1) calculation plus_extract(2))
    then show ?thesis
    proof (cases "get_gs a")
      case None
      then show ?thesis
        by (metis \<open>get_gs ab = add_gs (get_gs a) (Some p)\<close> add_gs.simps(1) calculation compatible_def not_pgte_charact)
    next
      case (Some pa)
      then have "get_gs ab = Some (padd (fst pa) (fst p), snd pa + snd p)"
        using \<open>get_gs ab = add_gs (get_gs a) (Some p)\<close> by auto
      then have "pgte (padd (fst pa) (fst p)) (fst p)"
        using padd_comm pgt_implies_pgte sum_larger by presburger
      then have "pgt (padd (padd (fst pa) (fst p)) (fst p')) pwrite"
        using calculation padd.rep_eq pgt.rep_eq pgte.rep_eq by auto
      then show ?thesis
        by (metis \<open>get_gs ab = Some (padd (fst pa) (fst p), snd pa + snd p)\<close> calculation compatible_def fst_conv not_pgte_charact)
    qed
  qed
next
  case False
  then show ?thesis
  proof (cases "compatible_fractions (get_fh b) (get_fh c)")
    case True
    then have "\<not> same_values (get_fh b) (get_fh c)"
      using False compatible_fract_heaps_def by blast
    then obtain l pb pc where "get_fh b l = Some pb" "get_fh c l = Some pc" "snd pc \<noteq> snd pb"
      using same_values_def by fastforce
    then obtain pab where "get_fh ab l = Some pab" "snd pab = snd pb"
      apply (cases "get_fh a l")
       apply (metis (no_types, lifting) add_fh_def assms(1) fadd_options.simps(2) plus_comm plus_extract(1))
      using add_fh_def[of "get_fh b" "get_fh a" l] assms(1) fadd_options.simps(3) plus_comm plus_extract(1) snd_conv
      by metis
    then show ?thesis
      by (metis \<open>get_fh c l = Some pc\<close> \<open>snd pc \<noteq> snd pb\<close> compatible_def compatible_fract_heapsE(2))
  next
    case False
    then obtain pb pc l where "get_fh b l = Some pb" "get_fh c l = Some pc" "pgt (padd (fst pb) (fst pc)) pwrite"
      using compatible_fractions_def not_pgte_charact by blast

    then show ?thesis
    proof (cases "get_fh a l")
      case None
      then have "get_fh ab l = Some pb"
        by (metis (no_types, lifting) \<open>get_fh b l = Some pb\<close> add_fh_def assms(1) fadd_options.simps(1) plus_extract(1))
      then show ?thesis
        by (meson \<open>get_fh c l = Some pc\<close> \<open>pgt (padd (fst pb) (fst pc)) pwrite\<close> compatible_def compatible_fract_heaps_def compatible_fractions_def not_pgte_charact)
    next
      case (Some pa)
      then obtain pab where "get_fh ab l = Some pab" "fst pab = padd (fst pa) (fst pb)"
        by (metis (mono_tags, opaque_lifting) \<open>get_fh b l = Some pb\<close> add_fh_def assms(1) fadd_options.simps(3) fst_conv plus_extract(1))
      then have "pgte (fst pab) (fst pb)"
        by (metis padd_comm pgt_implies_pgte sum_larger)
      then have "pgt (padd (fst pab) (fst pc)) pwrite"
        using \<open>pgt (padd (fst pb) (fst pc)) pwrite\<close> padd.rep_eq pgt.rep_eq pgte.rep_eq by force
      then show ?thesis
        by (meson \<open>get_fh ab l = Some pab\<close> \<open>get_fh c l = Some pc\<close> compatible_def compatible_fract_heapsE(1) not_pgte_charact)
    qed
  qed
qed

lemma plus_extract_point_fh:
  assumes "Some x = Some a \<oplus> Some b"
      and "get_fh a l = Some pa"
      and "get_fh b l = Some pb"
    shows "snd pa = snd pb \<and> pgte pwrite (padd (fst pa) (fst pb)) \<and> get_fh x l = Some (padd (fst pa) (fst pb), snd pa)"
  using add_fh_def[of "get_fh a" "get_fh b"] assms(1) assms(2) assms(3) compatible_def[of a b] compatible_eq
    compatible_fract_heapsE(1)[of "get_fh a" "get_fh b"] compatible_fract_heapsE(2)[of "get_fh a" "get_fh b"]
    fadd_options.simps(3)[of pa pb] option.distinct(1) plus_extract(1)[of x a b]
  by metis

lemma asso1:
  assumes "Some a \<oplus> Some b = Some ab"
      and "Some b \<oplus> Some c = Some bc"
    shows "Some ab \<oplus> Some c = Some a \<oplus> Some bc"
proof (cases "Some ab \<oplus> Some c")
  case None
  then show ?thesis
  proof (cases "compatible_fract_heaps (get_fh ab) (get_fh c)")
    case True
    then have r: "(\<exists>k. get_gu ab k \<noteq> None \<and> get_gu c k \<noteq> None) \<or> (\<exists>p p'. get_gs ab = Some p \<and> get_gs c = Some p'
      \<and> pgt (padd (fst p) (fst p')) pwrite)"
      by (metis None compatible_def compatible_eq not_pgte_charact)
    then show ?thesis
    proof (cases "\<exists>k. get_gu ab k \<noteq> None \<and> get_gu c k \<noteq> None")
      case True
      then obtain k where "get_gu ab k \<noteq> None \<and> get_gu c k \<noteq> None"
        by presburger
      then have "get_gu a k \<noteq> None \<or> get_gu b k \<noteq> None"
        by (metis (no_types, lifting) add_gu_def add_gu_single.simps(1) assms(1) plus_extract(3))
      then show ?thesis
        by (metis \<open>get_gu ab k \<noteq> None \<and> get_gu c k \<noteq> None\<close> assms(2) asso2 compatible_def compatible_eq option.discI plus_comm)
    next
      case False
      then obtain pab pc where "get_gs ab = Some pab \<and> get_gs c = Some pc
      \<and> pgt (padd (fst pab) (fst pc)) pwrite"
        using r by blast
      then show ?thesis
        apply (cases "get_gs a")
         apply (metis add_gs.simps(1) assms(1) assms(2) compatible_def compatible_eq not_pgte_charact option.discI plus_extract(2))
        apply (cases "get_gs b")
         apply (metis add_gs.simps(1) add_gs.simps(2) assms(1) assms(2) compatible_def compatible_eq not_pgte_charact plus_extract(2))
      proof -
        fix pa pb assume "get_gs ab = Some pab \<and> get_gs c = Some pc \<and> pgt (padd (fst pab) (fst pc)) pwrite"
        "get_gs a = Some pa" "get_gs b = Some pb"
        then have "pab = (padd (fst pa) (fst pb), snd pa + snd pb)"
          by (metis add_gs.simps(3) assms(1) option.sel plus_extract(2))
        then show "Some ab \<oplus> Some c = Some a \<oplus> Some bc"
          using None \<open>get_gs a = Some pa\<close> \<open>get_gs ab = Some pab \<and> get_gs c = Some pc \<and> pgt (padd (fst pab) (fst pc)) pwrite\<close>
            \<open>get_gs b = Some pb\<close> add_gs.simps(3) assms(2) compatible_def[of a bc]
            compatible_eq fst_conv not_pgte_charact[of pwrite "padd (fst pab) (fst pc)"] padd_asso plus_extract(2)
          by metis
      qed
    qed
  next
    case False
    then show ?thesis
    proof (cases "compatible_fractions (get_fh ab) (get_fh c)")
      case True
      then have "\<not>same_values (get_fh ab) (get_fh c)"
        using False compatible_fract_heaps_def
        by blast

      then obtain l pab pc where "get_fh ab l = Some pab" "get_fh c l = Some pc" "snd pab \<noteq> snd pc"
        using same_values_def by blast
        
      then show ?thesis
        apply (cases "get_fh a l")
        
         apply (metis (no_types, lifting) add_fh_def assms(1) assms(2) compatible_def compatible_eq compatible_fract_heapsE(2) fadd_options.simps(1) option.distinct(1) plus_extract(1))

      proof -
        fix pa assume "get_fh ab l = Some pab" "get_fh c l = Some pc" "snd pab \<noteq> snd pc" "get_fh a l = Some pa"
        moreover have "same_values (get_fh a) (get_fh b)"
          by (metis assms(1) compatible_def compatible_fract_heaps_def option.discI plus.simps(3))
        ultimately have "snd pa = snd pab"
          apply (cases "get_fh b l")
           apply (metis (no_types, lifting) add_fh_def assms(1) fadd_options.simps(2) option.inject plus_extract(1))
          by (metis (no_types, lifting) add_fh_def assms(1) fadd_options.simps(3) option.sel plus_extract(1) snd_eqD)
        then show ?thesis
          by (metis (full_types) None \<open>get_fh a l = Some pa\<close> \<open>get_fh c l = Some pc\<close> \<open>snd pab \<noteq> snd pc\<close> assms(2) asso2 compatible_def compatible_eq compatible_fract_heapsE(2) plus_comm)
      qed
    next
      case False
      then obtain l pab pc where "get_fh ab l = Some pab" "get_fh c l = Some pc" "pgt (padd (fst pab) (fst pc)) pwrite"
        using compatible_fractions_def not_pgte_charact by blast
      then show ?thesis
      proof (cases "get_fh a l")
        case None
        then have "get_fh b l = Some pab"
          by (metis (no_types, lifting) \<open>get_fh ab l = Some pab\<close> add_fh_def assms(1) fadd_options.simps(1) plus_extract(1))
        then show ?thesis
          by (metis \<open>get_fh c l = Some pc\<close> \<open>pgt (padd (fst pab) (fst pc)) pwrite\<close> assms(2) compatible_def compatible_fract_heapsE(1) not_pgte_charact option.simps(3) plus.simps(3))
      next
        case (Some pa)
        then have "get_fh a l = Some pa" by simp
        then show ?thesis
        proof (cases "get_fh b l")
          case None
          then have "pa = pab"
            by (metis (no_types, lifting) Some \<open>get_fh ab l = Some pab\<close> add_fh_def assms(1) fadd_options.simps(2) option.inject plus_extract(1))
          then show ?thesis
            by (metis Some \<open>get_fh ab l = Some pab\<close> \<open>get_fh c l = Some pc\<close> \<open>pgt (padd (fst pab) (fst pc)) pwrite\<close> assms(2) asso2 compatible_def compatible_fract_heapsE(1) not_pgte_charact padd_comm plus.simps(3) plus_comm)
        next
          case (Some pb)
          then have "fst pab = padd (fst pa) (fst pb)"
            using \<open>get_fh a l = Some pa\<close> \<open>get_fh ab l = Some pab\<close> add_fh_def[of "get_fh a" "get_fh b"] assms(1) compatible_def compatible_eq
                compatible_fract_heapsE(2)[of "get_fh a" "get_fh b"] fadd_options.simps(3)
                fst_apfst option.discI option.sel plus_extract(1)[of ab a b] prod.collapse snd_apfst
            by force
          then have "pgt (padd (fst pa) (padd (fst pb) (fst pc))) pwrite"
            using \<open>pgt (padd (fst pab) (fst pc)) pwrite\<close> padd_asso by auto
          moreover obtain pbc where "get_fh bc l = Some pbc" "fst pbc = padd (fst pb) (fst pc)"
            by (metis (no_types, opaque_lifting) Some \<open>get_fh c l = Some pc\<close> add_fh_def assms(2) fadd_options.simps(3) fst_conv plus_extract(1))
          ultimately show ?thesis
            by (metis None \<open>get_fh a l = Some pa\<close> compatible_def compatible_eq compatible_fract_heapsE(1) not_pgte_charact)
        qed
      qed
    qed
  qed
next
  case (Some x)
  then have "Some ab \<oplus> Some c = Some x" by simp
  have "a ## bc"
  proof (rule compatibleI)
    show "compatible_fract_heaps (get_fh a) (get_fh bc)"
    proof (rule compatible_fract_heapsI)
      fix l pa pbc assume asm0: "get_fh a l = Some pa \<and> get_fh bc l = Some pbc"
      have "pgte pwrite (padd (fst pa) (fst pbc)) \<and> snd pa = snd pbc"
      proof (cases "get_fh c l")
        case None
        then have "get_fh b l = Some pbc"
          by (metis (no_types, lifting) add_fh_def asm0 assms(2) fadd_options.elims option.discI plus_extract(1))
        then show ?thesis
          by (metis (no_types, lifting) asm0 assms(1) compatible_def compatible_eq compatible_fract_heapsE(1) compatible_fract_heapsE(2) option.discI)
      next
        case (Some pc)
        then have "get_fh c l = Some pc" by simp
        then show ?thesis
        proof (cases "get_fh b l")
          case None
          then have "get_fh ab l = Some pa"
            by (metis (no_types, lifting) add_fh_def asm0 assms(1) fadd_options.simps(2) plus_extract(1))
          moreover have "pbc = pc"
            by (metis (no_types, lifting) None Some add_fh_def asm0 assms(2) fadd_options.simps(2) option.inject plus_comm plus_extract(1))
          ultimately show ?thesis
            by (metis (no_types, lifting) Some \<open>Some ab \<oplus> Some c = Some x\<close> compatible_def compatible_eq compatible_fract_heapsE(1) compatible_fract_heapsE(2) option.discI)
        next
          case (Some pb)
          then obtain pab where "get_fh ab l = Some pab" "fst pab = padd (fst pa) (fst pb)" "snd pab = snd pa" 
            by (metis (mono_tags, opaque_lifting) add_fh_def asm0 assms(1) fadd_options.simps(3) fst_conv plus_extract(1) snd_conv)
          then have "pgte pwrite (padd (padd (fst pa) (fst pb)) (fst pc))"
            by (metis \<open>Some ab \<oplus> Some c = Some x\<close> \<open>get_fh c l = Some pc\<close> compatible_def compatible_eq compatible_fract_heapsE(1) option.distinct(1))
          then have "pgte pwrite (padd (fst pa) (fst pbc))"
            by (metis (no_types, lifting) Some \<open>get_fh c l = Some pc\<close> add_fh_def asm0 assms(2) fadd_options.simps(3) fst_conv option.sel padd_asso plus_extract(1))
          moreover have "snd pa = snd pb"
            by (metis Some asm0 assms(1) compatible_def compatible_fract_heapsE(2) option.simps(3) plus.simps(3))
          then have "snd pa = snd pbc"
            by (metis (no_types, opaque_lifting) Some \<open>get_fh c l = Some pc\<close> add_fh_def asm0 assms(2) fadd_options.simps(3) option.sel plus_extract(1) snd_conv)
          ultimately show ?thesis by blast
        qed
      qed
      then show "pgte pwrite (padd (fst pa) (fst pbc))"
        by auto
      show "snd pa = snd pbc"
        by (simp add: \<open>pgte pwrite (padd (fst pa) (fst pbc)) \<and> snd pa = snd pbc\<close>)
    qed

    show "\<And>k. get_gu a k = None \<or> get_gu bc k = None"
    proof -
      fix k show "get_gu a k = None \<or> get_gu bc k = None"     
      proof (cases "get_gu a k")
        case (Some aa)
        then have "get_gu b k = None \<or> get_gu c k = None"
          by (metis assms(2) compatible_def compatible_eq option.discI)
        then show ?thesis
          using Some \<open>Some ab \<oplus> Some c = Some x\<close> add_gu_def[of "get_gu a" "get_gu b"]
            add_gu_def[of "get_gu b" "get_gu c"] add_gu_single.simps(1) add_gu_single.simps(2)
            assms(1) assms(2) compatible_def compatible_eq option.distinct(1) plus_extract(3)
          by metis
      qed (simp)
    qed
    fix pa pbc assume "get_gs a = Some pa \<and> get_gs bc = Some pbc"
    show "pgte pwrite (padd (fst pa) (fst pbc)) "
    proof (cases "get_gs b")
      case None
      then show ?thesis by (metis Some \<open>get_gs a = Some pa \<and> get_gs bc = Some pbc\<close> add_gs.simps(1) add_gs.simps(2) assms(1) assms(2) compatible_def compatible_eq option.discI plus_extract(2))
    next
      case (Some pb)
      then have "get_gs b = Some pb" by simp
      then show ?thesis
      proof (cases "get_gs c")
        case None
        then show ?thesis
          by (metis Some \<open>get_gs a = Some pa \<and> get_gs bc = Some pbc\<close> add_gs.simps(2) assms(1) assms(2) compatible_def compatible_eq option.distinct(1) plus_extract(2))
      next
        case (Some pc)
        then have "padd (fst pa) (fst pbc) = padd (fst pa) (padd (fst pb) (fst pc))"
          by (metis (no_types, lifting) \<open>get_gs a = Some pa \<and> get_gs bc = Some pbc\<close> \<open>get_gs b = Some pb\<close> add_gs.simps(3) assms(2) fst_conv option.sel plus_extract(2))
        also have "... = padd (padd (fst pa) (fst pb)) (fst pc)"
          using padd_asso by force
        moreover obtain pab where "get_gs ab = Some pab"
          by (metis \<open>get_gs a = Some pa \<and> get_gs bc = Some pbc\<close> \<open>get_gs b = Some pb\<close> add_gs.simps(3) assms(1) plus_extract(2))
        then have "pgte pwrite (padd (fst pab) (fst pc))"
          by (metis Some \<open>Some ab \<oplus> Some c = Some x\<close> compatible_def compatible_eq option.simps(3))
        ultimately show ?thesis
          by (metis (no_types, lifting) \<open>get_gs a = Some pa \<and> get_gs bc = Some pbc\<close> \<open>get_gs ab = Some pab\<close> \<open>get_gs b = Some pb\<close> add_gs.simps(3) assms(1) fst_conv option.sel plus_extract(2))
      qed
    qed

  qed
  then obtain y where "Some y = Some a \<oplus> Some bc"
    by simp
  moreover have "x = y"
  proof (rule heap_ext)
    show "get_gu x = get_gu y"
    proof (rule ext)
      fix k show "get_gu x k = get_gu y k"
        apply (cases "get_gu a k")
        using Some add_gu_def[of "get_gu a"] add_gu_def[of "get_gu b"] add_gu_def[of "get_gu ab"]
          add_gu_single.simps(1) assms(1) assms(2) calculation
          plus_extract(3)[of ab a b] plus_extract(3)[of bc b c] plus_extract(3)[of y a bc] plus_extract(3)[of x ab c]
        apply simp
        apply (cases "get_gu b k")
        using Some add_gu_def[of "get_gu a"] add_gu_def[of "get_gu b"] add_gu_def[of "get_gu ab"]
          add_gu_single.simps(1) assms(1) assms(2) calculation
          plus_extract(3)[of ab a b] plus_extract(3)[of bc b c] plus_extract(3)[of y a bc] plus_extract(3)[of x ab c]
            add_gu_single.simps(1) add_gu_single.simps(2) assms(1) assms(2) calculation
        apply simp
        by (metis assms(1) compatible_def compatible_eq option.simps(3))
    qed
    show "get_gs x = get_gs y"
      apply (cases "get_gs a")
       apply (metis (mono_tags, lifting) Some add_gs.simps(1) assms(1) assms(2) calculation plus_extract(2))
      apply (cases "get_gs b")
       apply (metis (mono_tags, lifting) Some add_gs.simps(1) add_gs.simps(2) assms(1) assms(2) calculation plus_extract(2))
      apply (cases "get_gs c")
       apply (metis Some add_gs.simps(1) assms(1) assms(2) calculation plus_comm plus_extract(2))
    proof -
      fix ga gb gc assume asm0: "get_gs a = Some ga" "get_gs b = Some gb" "get_gs c = Some gc"
      then obtain gab gbc where r: "get_gs ab = Some gab" "get_gs bc = gbc"
        by (metis add_gs.simps(3) assms(1) plus_extract(2))
      then have "get_gs x = Some (padd (padd (fst ga) (fst gb)) (fst gc), (snd ga + snd gb) + snd gc)"
        by (metis (no_types, lifting) Some add_gs.simps(3) asm0(1) asm0(2) asm0(3) assms(1) fst_conv plus_extract(2) snd_conv)
      moreover have "get_gs y = Some (padd (fst ga) (padd (fst gb) (fst gc)), snd ga + (snd gb + snd gc))"
        by (metis (mono_tags, opaque_lifting) \<open>Some y = Some a \<oplus> Some bc\<close> add_gs.simps(3) asm0(1) asm0(2) asm0(3) assms(2) fst_conv plus_extract(2) prod.exhaust_sel snd_conv)
      ultimately show "get_gs x = get_gs y"
        by (simp add: padd_asso)
    qed
    show "get_fh x = get_fh y"
      by (metis Some add_fh_asso assms(1) assms(2) calculation plus_extract(1))
  qed
  ultimately show ?thesis using Some by presburger
qed

lemma simpler_asso:
  "(Some a \<oplus> Some b) \<oplus> Some c = Some a \<oplus> (Some b \<oplus> Some c)"
proof (cases "Some a \<oplus> Some b")
  case None
  then show ?thesis
    by (metis (no_types, opaque_lifting) asso2 compatible_eq option.exhaust plus.simps(1) plus_comm)
next
  case (Some ab)
  then have ab: "Some ab = Some a \<oplus> Some b" by simp
  then show ?thesis
  proof (cases "Some b \<oplus> Some c")
    case None
    then show ?thesis
      by (metis Some asso2 compatible_eq plus.simps(2))
  next
    case (Some bc)
    then show ?thesis
      by (metis ab asso1)
  qed
qed

lemma plus_asso:
  "(a \<oplus> b) \<oplus> c = a \<oplus> (b \<oplus> c)"
proof (cases a)
  case (Some aa)
  then have aa: "a = Some aa" by simp
  then show ?thesis
  proof (cases b)
    case (Some bb)
    then have bb: "b = Some bb" by simp
    then show ?thesis
    proof (cases c)
      case None
      then show ?thesis
        by (simp add: plus_comm)
    next
      case (Some cc)
      then show ?thesis
        using aa bb simpler_asso by blast
    qed
  qed (simp)
qed (simp)

definition larger :: "('i, 'a) heap \<Rightarrow> ('i, 'a) heap \<Rightarrow> bool" (infixl "\<succeq>" 55) where
  "a \<succeq> b \<longleftrightarrow> (\<exists>c. Some a = Some b \<oplus> Some c)"

lemma larger_trans:
  assumes "a \<succeq> b"
      and "b \<succeq> c"
    shows "a \<succeq> c"
proof -
  obtain r1 where "Some a = Some b \<oplus> Some r1"
    using assms(1) larger_def by blast
  moreover obtain r2 where "Some b = Some c \<oplus> Some r2"
    using assms(2) larger_def by blast
  moreover obtain r where "Some r = Some r1 \<oplus> Some r2"
    by (metis (no_types, opaque_lifting) calculation(1) calculation(2) not_Some_eq plus.simps(1) plus_asso plus_comm)
  ultimately show ?thesis
    by (metis larger_def plus_comm simpler_asso)
qed

lemma comp_smaller:
  assumes "a ## b"
      and "Some b = Some c \<oplus> Some d"
    shows "a ## c"
  by (metis assms(1) assms(2) option.distinct(1) plus.simps(1) plus.simps(3) plus_asso)

lemma full_sguard_sum_same:
  assumes "get_gs a = Some (pwrite, sargs)"
      and "Some h = Some a \<oplus> Some b"
    shows "get_gs h = Some (pwrite, sargs)"
proof (cases "get_gs b")
  case None
  then show ?thesis
    by (metis add_gs.simps(2) assms(1) assms(2) fst_conv get_gs.elims option.sel option.simps(3) plus.simps(3) snd_eqD)
next
  case (Some a)
  then show ?thesis
    by (metis assms(1) assms(2) compatible_def compatible_eq fst_eqD not_pgte_charact option.simps(3) sum_larger)
qed

lemma full_uguard_sum_same:
  assumes "get_gu a k = Some uargs"
      and "Some h = Some a \<oplus> Some b"
    shows "get_gu h k = Some uargs"
proof (cases "get_gu b k")
  case None
  then show ?thesis
    by (metis (no_types, lifting) add_gu_def add_gu_single.simps(2) assms(1) assms(2) plus_extract(3))
next
  case (Some a)
  then show ?thesis
    by (metis assms(1) assms(2) compatible_def compatible_eq option.simps(3))
qed

lemma smaller_more_compatible:
  assumes "a ## b"
      and "a \<succeq> c"
    shows "c ## b"
  by (meson assms(1) assms(2) comp_smaller compatible_comm larger_def)

lemma equiv_sum_get_fh:
  assumes "get_fh a = get_fh a'"
      and "get_fh b = get_fh b'"
      and "Some x = Some a \<oplus> Some b"
      and "Some x' = Some a' \<oplus> Some b'"
    shows "get_fh x = get_fh x'"
  by (metis assms(1) assms(2) assms(3) assms(4) fst_eqD get_fh.elims option.discI option.sel plus.simps(3))


lemma addition_cancellative:
  assumes "Some a = Some b \<oplus> Some c"
      and "Some a = Some b' \<oplus> Some c"
    shows "b = b'"
proof (rule heap_ext)
  show "get_gu b = get_gu b'"
  proof (rule ext)
    fix k show "get_gu b k = get_gu b' k"
    apply (cases "get_gu a k")
     apply (metis assms(1) assms(2) full_uguard_sum_same not_Some_eq)
      apply (cases "get_gu b k")
      using add_gu_def[of "get_gu b" "get_gu c"]
        add_gu_single.simps(1)[of "get_gu c k"] assms(1) assms(2) compatible_def[of b c] compatible_def[of b' c]
        option.inject option.simps(3) plus.elims plus_extract(3)[of a b c]
      apply metis
  proof -
    fix ga gb assume "get_gu a k = Some ga" "get_gu b k = Some gb"
    then have "get_gu c k = None"
      by (metis assms(1) compatible_def compatible_eq option.simps(3))
    then show "get_gu b k = get_gu b' k"
      by (metis (no_types, opaque_lifting) add_gu_def add_gu_single.simps(1) assms(1) assms(2) plus_comm plus_extract(3))
    qed
  qed
  show "get_gs b = get_gs b'"
    by (metis add_gs_cancellative assms(1) assms(2) plus_extract(2))
  show "get_fh b = get_fh b'"
  proof (rule ext)
    fix l show "get_fh b l = get_fh b' l"
    proof (cases "get_fh a l")
      case None
      then have "get_fh b l = None"
        by (metis (no_types, lifting) add_fh_def assms(1) fadd_options.elims option.distinct(1) plus_extract(1))
      then show ?thesis
        by (metis (no_types, opaque_lifting) None add_fh_def assms(2) fadd_options.elims option.distinct(1) plus_extract(1))
    next
      case (Some aa)
      then have "get_fh a l = Some aa" by simp
      then show ?thesis
      proof (cases "get_fh c l")
        case None
        then show ?thesis
          by (metis (no_types, lifting) add_fh_def assms(1) assms(2) fadd_options.simps(1) plus_comm plus_extract(1))
      next
        case (Some cc)
        then have "get_fh c l = Some cc" by simp
        then show ?thesis using fadd_options_cancellative
          by (metis (no_types, opaque_lifting) add_fh_def assms(1) assms(2) plus_extract(1))
      qed
    qed
  qed
qed

lemma addition_cancellative3:
  assumes "Some x = Some a \<oplus> Some b \<oplus> Some c"
      and "Some x = Some a' \<oplus> Some b \<oplus> Some c"
    shows "a = a'"
proof -
  obtain ab ab' where "Some ab = Some a \<oplus> Some b" "Some ab' = Some a' \<oplus> Some b"
    by (metis assms(1) assms(2) not_Some_eq plus.simps(1))
  then have "ab = ab'"
    by (metis addition_cancellative assms(1) assms(2))
  then show ?thesis
    using \<open>Some ab = Some a \<oplus> Some b\<close> \<open>Some ab' = Some a' \<oplus> Some b\<close> addition_cancellative by blast
qed

lemma larger3:
  assumes "Some x = Some a \<oplus> Some b \<oplus> Some c"
  shows "x \<succeq> b"
proof -
  obtain ab where "Some ab = Some a \<oplus> Some b"
    by (metis assms not_Some_eq plus.simps(1))
  then show ?thesis
    by (metis (no_types, opaque_lifting) assms larger_def larger_trans plus_comm)
qed





lemma add_get_fh:
  assumes "Some x = Some a \<oplus> Some b"
  shows "get_fh x = add_fh (get_fh a) (get_fh b)"
  by (metis assms fst_conv get_fh.elims option.discI option.sel plus.simps(3))

lemma sum_gs_one_none:
  assumes "Some x = Some a \<oplus> Some b"
      and "get_gs b = None"
    shows "get_gs x = get_gs a"
  by (metis add_gs.simps(1) assms(1) assms(2) plus_comm plus_extract(2))

lemma sum_gs_one_some:
  assumes "Some x = Some a \<oplus> Some b"
      and "get_gs a = Some (pa, ma)"
      and "get_gs b = Some (pb, mb)"
    shows "get_gs x = Some (padd pa pb, ma + mb)"
  by (metis add_gs.simps(3) assms(1) assms(2) assms(3) fst_conv plus_extract(2) snd_conv)



definition empty_heap :: "('i, 'a) heap" where
  "empty_heap = (Map.empty, None, \<lambda>k. None)"


lemma dom_normalize:
  "dom h = dom (normalize h)"
  by (meson FractionalHeap.normalize_eq(1) domIff subsetI subset_antisym)

lemma sum_second_none_get_fh:
  assumes "Some x = Some a \<oplus> Some b"
      and "get_fh b l = None"
    shows "get_fh x l = get_fh a l"
proof (cases "get_fh a l")
  case None
  then show ?thesis
    by (metis (no_types, opaque_lifting) add_fh_def add_get_fh assms(1) assms(2) fadd_options.simps(1))
next
  case (Some aa)
  then show ?thesis
    by (metis (no_types, lifting) add_fh_def add_get_fh assms(1) assms(2) fadd_options.simps(2))
qed

lemma sum_first_none_get_fh:
  assumes "Some x = Some a \<oplus> Some b"
      and "get_fh a l = None"
    shows "get_fh x l = get_fh b l"
  by (metis assms(1) assms(2) plus_comm sum_second_none_get_fh)


lemma dom_sum_two:
  assumes "Some x = Some a \<oplus> Some b"
  shows "dom (get_fh x) = dom (get_fh a) \<union> dom (get_fh b)"
  by (metis add_get_fh assms compatible_def compatible_dom_sum compatible_eq option.distinct(1))

lemma dom_three_sum:
  assumes "Some x = Some a \<oplus> Some b \<oplus> Some c"
  shows "dom (get_fh x) = dom (get_fh a) \<union> dom (get_fh b) \<union> dom (get_fh c)"
proof -
  obtain ab where "Some ab = Some a \<oplus> Some b"
    by (metis assms not_Some_eq plus.simps(1))
  then have "Some x = Some ab \<oplus> Some c"
    using assms by presburger
  then have "dom (get_fh x) = dom (get_fh ab) \<union> dom (get_fh c)"
    by (meson dom_sum_two)
  then show ?thesis
    by (metis \<open>Some ab = Some a \<oplus> Some b\<close> dom_sum_two)
qed

lemma addition_smaller_domain:
  assumes "Some a = Some b \<oplus> Some c"
  shows "dom (get_fh b) \<subseteq> dom (get_fh a)"
  by (metis (no_types, opaque_lifting) Un_subset_iff assms dom_sum_two order_refl)

lemma one_value_sum_same:
  assumes "Some x = Some a \<oplus> Some b"
      and "get_fh a l = Some (\<pi>, v)"
    shows "\<exists>\<pi>'. get_fh x l = Some (\<pi>', v)"
  using assms(1) assms(2) not_Some_eq plus_extract_point_fh[of x a _ l "(\<pi>, v)"] snd_eqD sum_second_none_get_fh[of x a]
  by metis

lemma compatible_last_two:
  assumes "Some x = Some a \<oplus> Some b \<oplus> Some c"
  shows "b ## c"
  by (metis assms compatible_eq option.discI plus.simps(2) plus_asso)

lemma add_fh_map_empty:
  "add_fh h Map.empty = h"
proof (rule ext)
  fix x show "add_fh h Map.empty x = h x"
    by (metis add_fh_def fadd_options.simps(1) fadd_options.simps(2) not_None_eq)
qed

end

(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


(*
  Structures supporting CTypes.
  Primarily sets up types, defines pointers and the raw heap view.
*)

theory CTypesBase
imports
  Addr_Type
begin

section "Type setup"

type_synonym byte = "8 word"

type_synonym memory = "addr \<Rightarrow> byte"
type_synonym 'a mem_upd = "addr \<Rightarrow> 'a \<Rightarrow> memory \<Rightarrow> memory"
type_synonym 'a mem_read = "addr \<Rightarrow> memory \<Rightarrow> 'a"

class unit_class =
  assumes there_is_only_one: "x = y"

instantiation unit :: unit_class
begin
instance by (intro_classes, simp)
end

subsection "Pointers"

datatype 'a ptr = Ptr addr

abbreviation
  NULL :: "'a ptr" where
  "NULL \<equiv> Ptr 0"

ML \<open>
structure Ptr_Syntax =
struct

  val show_ptr_types = Attrib.setup_config_bool @{binding show_ptr_types} (K true)

  fun ptr_tr' cnst ctxt typ ts = if Config.get ctxt show_ptr_types then
      case Term.strip_type typ of
        ([@{typ addr}], Type (@{type_name "ptr"}, [T])) =>
          list_comb
            (Syntax.const cnst $ Syntax_Phases.term_of_typ ctxt T
            , ts)
        | _ => raise Match
  else raise Match

  fun ptr_coerce_tr' cnst ctxt typ ts = if Config.get ctxt show_ptr_types then
      case Term.strip_type typ of
        ([Type (@{type_name ptr}, [S])], Type (@{type_name "ptr"}, [T])) =>
          list_comb
            (Syntax.const cnst $ Syntax_Phases.term_of_typ ctxt S
                               $ Syntax_Phases.term_of_typ ctxt T
            , ts)
        | _ => raise Match
  else raise Match
end
\<close>

syntax
  "_Ptr" :: "type \<Rightarrow> logic" (\<open>(1PTR/(1'(_')))\<close>)
syntax_consts
  "_Ptr" == Ptr
translations
  "PTR('a)" => "CONST Ptr :: (addr \<Rightarrow> 'a ptr)"
typed_print_translation
  \<open> [(@{const_syntax Ptr}, Ptr_Syntax.ptr_tr' @{syntax_const "_Ptr"})] \<close>

primrec
  ptr_val :: "'a ptr \<Rightarrow> addr"
where
  ptr_val_def: "ptr_val (Ptr a) = a"

primrec
  ptr_coerce :: "'a ptr \<Rightarrow> 'b ptr" where
  "ptr_coerce (Ptr a) = Ptr a"

syntax
  "_Ptr_coerce" :: "type \<Rightarrow> type \<Rightarrow> logic" (\<open>(1PTR'_COERCE/(1'(_ \<rightarrow> _')))\<close>)
syntax_consts
  "_Ptr_coerce" == ptr_coerce
translations
  "PTR_COERCE('a \<rightarrow> 'b)" => "CONST ptr_coerce :: ('a ptr \<Rightarrow> 'b ptr)"
typed_print_translation
  \<open> [(@{const_syntax ptr_coerce}, Ptr_Syntax.ptr_coerce_tr' @{syntax_const "_Ptr_coerce"})] \<close>

definition
  (* no ctype/memtype-class constraints on these so as to allow comparison of
     void * pointers, which are represented as Isabelle type unit ptr *)
  ptr_less :: "'a ptr \<Rightarrow> 'a ptr \<Rightarrow> bool" (infixl \<open><\<^sub>p\<close> 50) where
  "p <\<^sub>p q \<equiv> ptr_val p < ptr_val q"

definition
  ptr_le :: "'a ptr \<Rightarrow> 'a ptr \<Rightarrow> bool" (infixl \<open>\<le>\<^sub>p\<close> 50) where
  "p \<le>\<^sub>p q \<equiv> ptr_val p \<le> ptr_val q"

instantiation ptr :: (type) ord
begin

definition
  ptr_less_def': "p < q \<equiv> p <\<^sub>p q"
definition
  ptr_le_def': "p \<le> q \<equiv> p \<le>\<^sub>p q"

instance ..

end

lemma ptr_val_case: "ptr_val p = (case p of Ptr v \<Rightarrow> v)"
  by (cases p) simp

instantiation ptr :: (type) linorder
begin
instance
  by (intro_classes)
     (unfold ptr_le_def' ptr_le_def ptr_less_def' ptr_less_def ptr_val_case,
      auto split: ptr.splits)
end

subsection "Raw heap"

text \<open>A raw map from addresses to bytes\<close>

type_synonym heap_mem = "addr \<Rightarrow> byte"

text \<open>For heap \<^term>\<open>h\<close>, pointer \<^term>\<open>p\<close> and nat \<^term>\<open>n\<close>, \<^term>\<open>heap_list h n p\<close> returns the list
        of bytes in the heap taken from addresses \<open>{p..+n}\<close>\<close>

primrec
  heap_list :: "heap_mem \<Rightarrow> nat \<Rightarrow> addr \<Rightarrow> byte list"
where
  heap_list_base: "heap_list h 0 p = []"
| heap_list_rec:  "heap_list h (Suc n) p = h p # heap_list h n (p + 1)"


section "Intervals"

text \<open>
  For word \<^term>\<open>a\<close> and nat \<^term>\<open>b\<close>, \<open>{a..+b}\<close> is the set of words \<^term>\<open>x\<close>,
  with \<^term>\<open>unat (x - a) < b\<close>.\<close>

definition
  intvl :: "'a::len word \<times> nat \<Rightarrow> 'a::len word set" where
  "intvl x \<equiv> {z. \<exists>k. z = fst x + of_nat k \<and> k < snd x}"

abbreviation
  "intvl_abbr" :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word set" (\<open>{_..+_}\<close>) where
  "{a..+b} \<equiv> intvl (a,b)"


section "\<open>dt_tuple\<close>: a reimplementation of 3 item tuples"

datatype
    ('a, 'b, 'c) dt_tuple = DTuple (dt_fst: 'a) (dt_snd: 'b) (dt_trd: 'c)

lemma dt_prj_simps[simp]:
  "dt_fst (DTuple a b c) = a"
  "dt_snd (DTuple a b c) = b"
  "dt_trd (DTuple a b c) = c"
  by (auto)

lemma split_DTuple_All:
  "(\<forall>x. P x) = (\<forall>a b c. P (DTuple a b c))"
  apply (rule iffI; clarsimp) 
  subgoal for x by (cases x, simp) 
  done

lemma surjective_dt_tuple:
  "p = DTuple (dt_fst p) (dt_snd p) (dt_trd p)"
  by (cases p) simp

lemma split_DTuple_all[no_atp]: "(\<And>x. PROP P x) \<equiv> (\<And>a b c. PROP P (DTuple a b c))"
proof
  fix a b c
  assume "\<And>x. PROP P x"
  then show "PROP P (DTuple a b c)" .
next
  fix x
  assume "\<And>a b c. PROP P (DTuple a b c)"
  from \<open>PROP P (DTuple (dt_fst x) (dt_snd x) (dt_trd x))\<close> show "PROP P x" by simp
qed

type_synonym normalisor = "byte list \<Rightarrow> byte list"


section "Properties of pointers"

lemma Ptr_ptr_val [simp]:
  "Ptr (ptr_val p) = p"
  by (cases p) simp

lemma ptr_val_ptr_coerce [simp]:
  "ptr_val (ptr_coerce p) = ptr_val p"
  by (cases p) simp

lemma Ptr_ptr_coerce [simp]:
  "Ptr (ptr_val p) = ptr_coerce p"
  by (cases p) simp

lemma ptr_coerce_id [simp]:
  "ptr_coerce p = p"
  by (cases p) simp

lemma ptr_coerce_idem [simp]:
  "ptr_coerce (ptr_coerce p) = ptr_coerce p"
  by (cases p) simp

lemma ptr_val_inj [simp]:
  "(ptr_val p = ptr_val q) = (p = q)"
  by (cases p, cases q) auto

lemma ptr_coerce_NULL [simp]:
  "(ptr_coerce p = NULL) = (p = NULL)"
  by (cases p) simp

lemma NULL_ptr_val:
  "(p = NULL) = (ptr_val p = 0)"
  by (cases p) simp

lemma ptr_NULL_conv: "ptr_coerce NULL = NULL"
  by simp

instantiation ptr :: (type) finite
begin
instance
  by (intro_classes)
     (auto intro!: finite_code finite_imageD [where f=ptr_val] injI)
end

section "Properties of the raw heap"

lemma heap_list_length [simp]:
  "length (heap_list h n p) = n"
  by (induct n arbitrary: p) auto

lemma heap_list_split:
  shows "k \<le> n \<Longrightarrow> heap_list h n x = heap_list h k x @ heap_list h (n - k) (x + of_nat k)"
proof (induct n arbitrary: k x)
  case 0 thus ?case by simp
next
  case (Suc n) thus ?case
    by (cases k, auto simp: ac_simps)
qed

lemma heap_list_split2:
  "heap_list h (x + y) p = heap_list h x p @ heap_list h y (p + of_nat x)"
  by (subst heap_list_split [where k=x], auto)


section "Properties of intervals"

lemma intvlI:
  "x < n \<Longrightarrow> p + of_nat x \<in> {p..+n}"
  by (force simp: intvl_def)

lemma intvlD:
  "q \<in> {p..+n} \<Longrightarrow> \<exists>k. q = p + of_nat k \<and> k < n"
  by (force simp: intvl_def)

lemma intvl_empty [simp]:
  "{p..+0} = {}"
  by (fast dest: intvlD)

lemma intvl_Suc:
  "q \<in> {p..+Suc 0} \<Longrightarrow> p = q"
  by (force dest: intvlD)

lemma intvl_self:
  "0 < n \<Longrightarrow> x \<in> {x..+n}"
  by (force simp: intvl_def)

lemma intvl_start_inter:
  "\<lbrakk> 0 < m; 0 < n \<rbrakk> \<Longrightarrow> {p..+m} \<inter> {p..+n} \<noteq> {}"
  by (force simp: disjoint_iff_not_equal dest: intvl_self)

lemma intvl_overflow:
  assumes "2^len_of TYPE('a) \<le> n"
  shows "{(p::'a::len word)..+n} = UNIV"
proof -
  have witness:
    "\<And>x. x = p + of_nat (unat (x - p)) \<and> unat (x - p) < n"
    using assms by simp unat_arith
  show ?thesis unfolding intvl_def by (auto intro!: witness)
qed

lemma intvl_self_offset:
  fixes p::"'a::len word"
  assumes a: "2^len_of TYPE('a) - n < x" and b: "x < 2^len_of TYPE('a)" and
      c: "(p::'a::len word) \<notin> {p + of_nat x..+n}"
  shows False
proof -
  let ?j = "2^len_of TYPE('a) - x"
  from b have b': "of_nat x + of_nat ?j  = (0::'a::len word)" using of_nat_2p by auto
  moreover from a b have "?j < n" by arith
  with b b' c show  ?thesis by (force simp: intvl_def)
qed

lemma intvl_mem_offset:
  "\<lbrakk> q \<in> {p..+unat x}; q \<notin> {p..+unat y}; unat y \<le> unat x \<rbrakk> \<Longrightarrow>
      q \<in> {p + y..+unat x - unat y}"
  apply (clarsimp simp: intvl_def) 
  subgoal for k 
    apply (rule exI [where x="k - unat y"]) 
    apply auto
    done
  done


lemma intvl_plus_sub_offset:
  "x \<in> {p + y..+q - unat y} \<Longrightarrow> x \<in> {p..+q}"
  apply (clarsimp simp: intvl_def) 
  subgoal for k 
    apply (rule exI [where x="k + unat y"]) 
    apply auto
    done
  done

lemma intvl_plus_sub_Suc:
  "x \<in> {p + 1..+q - Suc 0} \<Longrightarrow> x \<in> {p..+q}"
  by (rule intvl_plus_sub_offset [where y=1], simp)

lemma intvl_neq_start:
  "\<lbrakk> (q::'a::len word) \<in> {p..+n}; p \<noteq> q \<rbrakk> \<Longrightarrow> q \<in> {p + 1..+n - Suc 0}"
  apply (clarsimp simp: intvl_def)
  by (metis One_nat_def Suc_eq_plus1_left add.commute gr0_conv_Suc
      less_diff_conv of_nat_Suc of_nat_gt_0)

lemmas unat_simps' =
  word_arith_nat_defs word_unat.eq_norm len_of_addr_card mod_less

lemma intvl_offset_nmem:
  "\<lbrakk> q \<in> {(p::'a::len word)..+unat x}; y \<le>  2^len_of TYPE('a) - unat x \<rbrakk> \<Longrightarrow>
      q \<notin> {p + x..+y}"
  apply (clarsimp simp: intvl_def)
  apply (simp only: unat_simps')
  apply (subst (asm) word_unat.Abs_inject)
    apply (auto simp: unats_def)
  done

lemma intvl_Suc_nmem' [simp]:
  "n < 2^len_of TYPE('a) \<Longrightarrow> (p::'a::len word) \<notin> {p + 1..+n - Suc 0}"
  by (clarsimp simp: intvl_def)
     (unat_arith, simp add: unat_simps' take_bit_nat_eq_self)

lemma intvl_Suc_nmem'':
  "n \<le> 2^len_of TYPE('a) \<Longrightarrow> (p::'a::len word) \<notin> {p + 1..+n - Suc 0}"
  by (simp add: intvl_offset_nmem intvl_self)

lemma intvl_start_le:
  "x \<le> y \<Longrightarrow> {p..+x} \<subseteq> {p..+y}"
  by (force simp: intvl_def)

lemma intvl_sub_eq:
  assumes "x \<le> y"
  shows "{p + x..+unat (y - x)} = {p..+unat y} - {p..+unat x}"
proof -
  have "unat y - unat x \<le> 2 ^ len_of TYPE('a) - unat x"
    by (insert unat_lt2p [of y], arith)
  moreover have "x \<le> y" by fact
  moreover hence "unat (y - x) = unat y - unat x"
    by (simp add: word_le_nat_alt, unat_arith)
  ultimately show ?thesis
    by (force dest: intvl_offset_nmem intvl_mem_offset elim: intvl_plus_sub_offset
              simp: word_le_nat_alt)

qed

lemma intvl_disj_offset:
  "{x + a..+c} \<inter> {x + b..+d} = {} = ({a..+c} \<inter> {b..+d} = {})"
  by (force simp: intvl_def)

lemma intvl_sub_offset:
  "unat x+y \<le> z \<Longrightarrow> {k+x..+y} \<subseteq> {k..+z}"
  apply(clarsimp simp: intvl_def)
  subgoal for k
  apply(rule exI [where x="unat x +  k"])
    apply clarsimp
    done
  done


lemma disjnt_intvl_offsetp[simp]:
  "disjnt {a + x ..+ n} {a + y ..+ m} \<longleftrightarrow> disjnt {x ..+ n} {y ..+ m}"
  by (simp add: disjnt_def intvl_disj_offset)

lemma intvl_eq_of_nat_Ico_add: "{of_nat n::'a::len word..+ m} = of_nat ` {n ..< n + m}"
  by (force simp: image_iff intvl_def Bex_def nat_le_iff_add simp flip: of_nat_add)

lemma intvl_le:
  assumes  "n2 + off1 \<le> n1"
  shows "{p + of_nat off1..+n2} \<subseteq> {p..+n1}"
  using assms
  by (auto simp add: intvl_def)
    (metis add.commute add_mono_thms_linordered_field(1) less_le_trans word_of_nat_plus)

lemma intvl_disj_left:
  fixes a b :: addr
  assumes a_n: "unat a + n \<le> unat b" and b_m: "unat b + m \<le> addr_card + unat a"
  shows "{a ..+ n} \<inter> {b ..+ m} = {}"
proof (safe dest!: intvlD intro!: empty_iff[THEN iffD2])
  fix i j assume i: "i < n" and j: "j < m" and eq: "a + of_nat i = b + of_nat j"
  have a_i_eq: "unat (a + of_nat i) = unat a + of_nat i"
    using a_n i
    by (metis (mono_tags, lifting) Abs_fnat_hom_add add_left_mono le_unat_uoi
            less_or_eq_imp_le of_nat_id word_unat.Rep_inverse)
  from a_n b_m have n_m: "n + m \<le> addr_card"
    by simp
  show False
  proof cases
    assume "unat b + j < addr_card"
    then have "unat (b + of_nat j) = unat b + of_nat j"
      by (metis len_of_addr_card of_nat_add of_nat_id unat_of_nat_eq word_unat.Rep_inverse)
    with eq a_i_eq have "unat a + i = unat b + j"
      unfolding word_unat_eq_iff by simp
    with a_n i show False by simp
  next
    assume "\<not> unat b + j < addr_card"
    with j n_m have "unat (b + of_nat j) + addr_card = unat b + j"
      unfolding addr_card_def card_word unat_arith_simps(5)
      by (simp add: unat_of_nat_eq)
    then have "unat a + i + addr_card = unat b + j"
      using a_i_eq eq unfolding word_unat_eq_iff by simp
    with b_m j show False by simp
  qed
qed

end

(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Port of Anthony Fox's HOL4 realisation of John Harrison's paper
   in TPHOLs 2005 on finite cartesian products *)

theory Arrays
imports
  "HOL-Library.Numeral_Type"
  "Match_Cterm"
  "ML_Infer_Instantiate"
begin

definition has_size :: "'a set \<Rightarrow> nat \<Rightarrow> bool" where
   "has_size s n = (finite s \<and> card s = n)"

\<comment> \<open>If @{typ 'a} is not finite, there is no @{term "n < CARD('a)"}\<close>
definition finite_index :: "nat \<Rightarrow> 'a::finite" where
  "finite_index = (SOME f. \<forall>x. \<exists>!n. n < CARD('a) \<and> f n = x)"

lemma card_image_inj:
  "\<lbrakk> finite S; \<And>x y. \<lbrakk> x \<in> S; y \<in> S; f x = f y \<rbrakk> \<Longrightarrow> x = y \<rbrakk> \<Longrightarrow> card (f ` S) = card S"
  by (induct rule: finite_induct) (auto simp: card_insert_if)

lemma has_size_image_inj:
  "\<lbrakk> has_size S n; \<And>x y. x \<in> S \<and> y \<in> S \<and> f x = f y \<Longrightarrow> x = y \<rbrakk> \<Longrightarrow> has_size (f ` S) n"
  by (simp add: has_size_def card_image_inj)

lemma has_size_0[simp]:
  "has_size S 0 = (S = {})"
  by (auto simp: has_size_def)

lemma has_size_suc:
  "has_size S (Suc n) = (S \<noteq> {} \<and> (\<forall>a. a \<in> S \<longrightarrow> has_size (S - {a}) n))"
  unfolding has_size_def
  by (metis Diff_empty Suc_not_Zero bot_least card_Suc_Diff1 card_gt_0_iff finite_Diff_insert
            nat.inject neq0_conv subsetI subset_antisym)

lemma has_index:
  "\<lbrakk> finite S; card S = n \<rbrakk> \<Longrightarrow>
   (\<exists>f. (\<forall>m. m < n \<longrightarrow> f m \<in> S) \<and> (\<forall>x. x\<in>S \<longrightarrow> (\<exists>!m. m < n \<and> f m = x)))"
proof (induct n arbitrary: S)
  case 0 thus ?case by (auto simp: card_eq_0_iff)
next
  case (Suc n)
  then obtain b B where
    S: "S = insert b B \<and> b \<notin> B \<and> card B = n \<and> (n = 0 \<longrightarrow> B = {})"
    by (auto simp: card_Suc_eq)
  with \<open>finite S\<close> Suc.hyps [of B]
  obtain f where IH: "(\<forall>m<n. f m \<in> B) \<and> (\<forall>x. x \<in> B \<longrightarrow> (\<exists>!m. m < n \<and> f m = x))" by auto
  define f' where "f' \<equiv> \<lambda>m. if m = card B then b else f m"
  from Suc.prems S IH
  have "(\<forall>m<Suc n. f' m \<in> S) \<and> (\<forall>x. x \<in> S \<longrightarrow> (\<exists>!m. m < Suc n \<and> f' m = x))"
    unfolding f'_def
    apply (clarsimp)
    apply (rule conjI, metis less_SucE)
    apply (metis less_SucE less_SucI nat_neq_iff)
    done
  thus ?case by blast
qed

lemma finite_index_works:
  "\<exists>!n. n < CARD('n::finite) \<and> finite_index n = (i::'n)"
proof -
  have "\<exists>f::nat \<Rightarrow> 'n. \<forall>i. \<exists>!n. n < CARD('n) \<and> f n = i"
    using has_index[where S = "UNIV :: 'n set"] by simp
  hence "\<forall>i. \<exists>!n. n < CARD('n::finite) \<and> finite_index n = (i::'n)"
    unfolding finite_index_def by (rule someI_ex)
  thus ?thesis ..
qed

lemma finite_index_inj:
  "\<lbrakk> i < CARD('a::finite); j < CARD('a) \<rbrakk> \<Longrightarrow>
   ((finite_index i :: 'a) = finite_index j) = (i = j)"
  using finite_index_works[where i = "finite_index j"] by blast

lemma forall_finite_index:
  "(\<forall>k::'a::finite. P k) = (\<forall>i. i < CARD('a) \<longrightarrow> P (finite_index i))"
  by (metis finite_index_works)

section \<open>Finite Cartesian Products\<close>

typedef ('a,'n::finite) array
    (\<open>(\<open>open_block notation=\<open>mixfix array\<close>\<close>_[_])\<close> [30,0] 31) = "UNIV :: ('n => 'a) set"
  by simp
setup_lifting type_definition_array

lift_definition index :: "('a,'n::finite) array \<Rightarrow> nat \<Rightarrow> 'a"
    (\<open>(\<open>open_block notation=\<open>mixfix array index\<close>\<close>_.[_])\<close> [900,0] 901) is
  "\<lambda>f i. f (finite_index i)".
 
lemma index_legacy_def: "index x i = Rep_array x (finite_index i)"
  by (transfer) simp

theorem array_index_eq:
  "((x::'a['n::finite]) = y) = (\<forall>i. i < CARD('n) \<longrightarrow> x.[i] = y.[i])"
  by (auto dest!: forall_finite_index [THEN iffD2]
           simp: index_def Rep_array_inject [symmetric])

(* fixme: legacy name *)
lemmas cart_eq = array_index_eq

lemma array_ext:
  fixes x :: "'a['n::finite]"
  shows "(\<And>i. i < CARD('n) \<Longrightarrow> x.[i] = y.[i]) \<Longrightarrow> x = y"
  by (simp add: array_index_eq)

definition FCP :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a['b::finite]" (binder \<open>ARRAY \<close> 10) where
  "FCP \<equiv> \<lambda>g. SOME a. \<forall>i. i < CARD('b) \<longrightarrow> a.[i] = g i"

definition update :: "'a['n::finite] \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a['n]" where
  "update f i x \<equiv> FCP ((index f)(i := x))"

definition fupdate :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a['b::finite] \<Rightarrow> 'a['b]" where
  "fupdate i f x \<equiv> update x i (f (index x i))"

lemma fcp_beta[simp]: "i < CARD('n :: finite) \<Longrightarrow> (FCP g :: 'a['n]).[i] = g i" 
proof -
  have "\<forall>i < CARD('n). (FCP g :: 'a['n]).[i] = g i"
    unfolding FCP_def
  proof (rule someI_ex)
    let ?g' = "\<lambda>k::'n. g (SOME i. i < CARD('n) \<and> finite_index i = k)"
    have "\<forall>i<CARD('n). (Abs_array ?g').[i] = g i"
      by (clarsimp simp: index_def Abs_array_inverse)
        (metis (mono_tags, lifting) finite_index_inj someI_ex)
    thus "\<exists>x::'a['n]. \<forall>i<CARD('n). x.[i] = g i" ..
  qed
  thus "i < CARD('n :: finite) \<Longrightarrow> (FCP g :: 'a['n]).[i] = g i" by auto
qed

lemma fcp_unique:
  "(\<forall>i. i < CARD('b::finite) \<longrightarrow> index f i = g i) =
   (FCP g = (f :: ('a,'b) array))"
  by (fastforce simp: cart_eq)

lemma fcp_eta[simp]:
  "(ARRAY i. g.[i]) = g"
  by (simp add: cart_eq)

lemma index_update[simp]:
  "n < CARD('b::finite) \<Longrightarrow> index (update (f::'a['b]) n x) n = x"
  by (simp add: update_def)

lemma index_update2[simp]:
  "\<lbrakk> k < CARD('b::finite); n \<noteq> k \<rbrakk> \<Longrightarrow> index (update (f::'a['b]) n x) k = index f k"
  by (simp add: update_def)

lemma update_update[simp]:
  "update (update f n x) n y = update f n y"
  by (simp add: cart_eq update_def)

lemma update_comm[simp]:
  "n \<noteq> m \<Longrightarrow> update (update f m v) n v' = update (update f n v') m v"
  by (simp add: cart_eq update_def)

lemma update_index_same [simp]:
  "update v n (index v n) = v"
  by (simp add: cart_eq update_def)

function foldli0 :: "(nat \<Rightarrow> 'acc \<Rightarrow> 'a \<Rightarrow> 'acc) \<Rightarrow> 'acc \<Rightarrow> nat \<Rightarrow> 'a['index::finite] \<Rightarrow> 'acc" where
  "foldli0 f a i arr = (if CARD('index) \<le> i then a else foldli0 f (f i a (index arr i)) (i+1) arr)"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(f,a,i,(arr::'b['c::finite])). CARD('c) - i)") auto

definition foldli :: "(nat \<Rightarrow> 'acc \<Rightarrow> 'a \<Rightarrow> 'acc) \<Rightarrow> 'acc \<Rightarrow> ('a,'i::finite) array \<Rightarrow> 'acc" where
  "foldli f a arr = foldli0 f a 0 arr"

(* for a traditional word presentation, with MSB on the left, you'd
   want a fold that numbered in the reverse direction (with element 0
   on the right rather than the left) *)

definition map_array :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a['n::finite] \<Rightarrow> 'b['n]" where
  "map_array f a \<equiv> ARRAY i. f (a.[i])"

definition map_array2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a['n::finite] \<Rightarrow> 'b['n] \<Rightarrow> 'c['n]" where
  "map_array2 f a b \<equiv> ARRAY i. f (a.[i]) (b.[i])"

definition zip_array :: "'a['b::finite] \<Rightarrow> 'c['b] \<Rightarrow> ('a \<times> 'c)['b]" where
  "zip_array \<equiv> map_array2 Pair"

definition list_array :: "('a,'n::finite) array \<Rightarrow> 'a list" where
  "list_array a = map (index a) [0..<CARD('n)]"

lift_definition set_array :: "'a['n::finite] \<Rightarrow> 'a set" is range .

lemma set_array_list:
  "set_array a = set (list_array a)"
  by (simp add: list_array_def index_def set_array.rep_eq image_def)
     (metis atLeast0LessThan finite_index_works lessThan_iff)

definition rel_array :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a['n::finite] \<Rightarrow> 'b['n] \<Rightarrow> bool" where
  "rel_array f a b \<equiv> \<forall>i < CARD('n). f (a.[i]) (b.[i])"

lemma map_array_index:
  fixes a :: "'a['n::finite]"
  shows "n < CARD('n) \<Longrightarrow> (map_array f a).[n] = f (a.[n])"
  by (metis fcp_beta map_array_def)

lemma map_array2_index:
  fixes a :: "'a['n::finite]"
  shows "n < CARD('n) \<Longrightarrow> (map_array2 f a b).[n] = f (a.[n]) (b.[n])"
  by (metis fcp_beta map_array2_def)

lemma zip_array_index:
  fixes a :: "'a['n::finite]"
  shows "n < CARD('n) \<Longrightarrow> (zip_array a b).[n] = (a.[n],b.[n])"
  by (simp add: zip_array_def map_array2_index)

lemma map_array_id[simp]:
  "map_array id = id"
  by (auto simp: map_array_index array_ext)

lemma map_array_comp:
  "map_array (g \<circ> f) = map_array g \<circ> map_array f"
  by (auto simp: map_array_def intro!: array_ext)

lemma list_array_nth:
  fixes a :: "'a['n::finite]"
  shows "n < CARD('n) \<Longrightarrow> list_array a ! n = index a n"
  by (simp add: list_array_def)

lemma list_array_length [simp]:
  "length (list_array (a :: 'a['n::finite])) = CARD('n)"
  by (simp add: list_array_def)

lemma in_set_array_index_conv:
  "(z \<in> set_array (a :: 'a['n::finite])) = (\<exists>n < CARD('n). z = a.[n])"
  by (metis in_set_conv_nth list_array_length list_array_nth nth_mem set_array_list)

lemma in_set_arrayE [elim!]:
  "\<lbrakk> z \<in> set_array (a :: 'a['n::finite]); \<And>n . \<lbrakk>n < CARD('n); z = a.[n]\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis in_set_array_index_conv)

lemma map_array_setI:
  "(\<And>z. z \<in> set_array x \<Longrightarrow> f z = g z) \<Longrightarrow> map_array f x = map_array g x"
  by (rule array_ext) (auto simp: map_array_index in_set_array_index_conv)

lemma list_array_map_array:
  "list_array (map_array f a) = map f (list_array a)"
  by (simp add: list_array_def map_array_index)

lemma list_array_FCP [simp]:
  "list_array (FCP f :: 'a['n]) = map f [0..<CARD('n::finite)]"
  by (simp add: list_array_def)

lemma set_array_FCP [simp]:
  "set_array (FCP f :: 'a['n]) = f ` {0..< CARD('n::finite)}"
  by (auto simp: set_array_list)

lemma map_array_set_img:
  "set_array \<circ> map_array f = (`) f \<circ> set_array"
  by (rule ext) (auto simp: map_array_def in_set_array_index_conv intro!: imageI)

lemma fcp_cong [cong]:
  "(\<And>i. i < CARD('n::finite) \<Longrightarrow> f i = g i) \<Longrightarrow> FCP f = (FCP g :: 'a['n])"
  by (rule array_ext) simp

bnf "('a,'n::finite) array"
  map: map_array
  sets: set_array
  bd: "card_suc (BNF_Cardinal_Arithmetic.csum natLeq (card_of (UNIV :: 'n set)))"
  rel: rel_array
proof -
  show "map_array id = id" by simp
next
  fix f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'c"
  show "map_array (g \<circ> f) = map_array g \<circ> map_array f"
    by (rule map_array_comp)
next
  fix x :: "'a['n::finite]" and f :: "'a \<Rightarrow> 'b" and g
  assume "\<And>z. z \<in> set_array x \<Longrightarrow> f z = g z"
  thus "map_array f x = map_array g x"
    by (rule map_array_setI)
next
  fix f :: "'a \<Rightarrow> 'b"
  show "set_array \<circ> map_array f = (`) f \<circ> set_array"
    by (rule map_array_set_img)
next
  show "card_order (card_suc (BNF_Cardinal_Arithmetic.csum natLeq (card_of UNIV)))"
    by (simp add: card_of_card_order_on card_order_card_suc card_order_csum natLeq_card_order)
next
  show " BNF_Cardinal_Arithmetic.cinfinite (card_suc (BNF_Cardinal_Arithmetic.csum natLeq (card_of UNIV)))"
    by (simp add: Card_order_csum Cinfinite_card_suc card_of_card_order_on card_order_csum 
        cinfinite_csum natLeq_Cinfinite natLeq_card_order)
next
  fix R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and S :: "'b \<Rightarrow> 'c \<Rightarrow> bool"
  show "rel_array R OO rel_array S \<le> rel_array (R OO S)"
    by (force simp: rel_array_def)
next
  fix R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  { fix a :: "('a \<times> 'b)['n::finite]" and i
    have "\<lbrakk>set_array a \<subseteq> {(x, y). R x y}; i < CARD('n)\<rbrakk> \<Longrightarrow> R (fst (a.[i])) (snd (a.[i]))"
      by (meson Collect_case_prodD in_set_array_index_conv subset_iff)
  } note conv = this
  show "rel_array R =
         (\<lambda>x y. \<exists>z. set_array z \<subseteq> {(x, y). R x y} \<and> map_array fst z = x \<and> map_array snd z = y)"
    unfolding rel_array_def
    apply (intro ext iffI)
    subgoal for a b
     apply (rule exI [where x="zip_array a b"])
      by (auto intro!: array_ext simp: conv map_array_index zip_array_index)
    subgoal 
      by (auto intro!: array_ext simp: conv map_array_index zip_array_index)
    done
next
  show "regularCard (card_suc (BNF_Cardinal_Arithmetic.csum natLeq (card_of UNIV)))"
    by (simp add: Card_order_csum card_of_card_order_on card_order_csum cinfinite_csum 
        natLeq_Cinfinite natLeq_card_order regularCard_card_suc)
next
  fix x :: "'a['n::finite]"
  let ?U = "UNIV :: 'n set"
  have "ordLeq3 (card_of (set_array x)) (card_of ?U)" by transfer (rule card_of_image)
  also
  have "ordLeq3 (card_of ?U) (BNF_Cardinal_Arithmetic.csum natLeq (card_of ?U))"
   by (rule ordLeq_csum2) (rule card_of_Card_order)
  finally
  have "ordLeq3 (card_of (set_array x)) (BNF_Cardinal_Arithmetic.csum natLeq (card_of ?U))" .
  then show "ordLess2 (card_of (set_array x))
          (card_suc (BNF_Cardinal_Arithmetic.csum natLeq (card_of ?U)))"
    using ordLeq_ordLess_trans card_suc_greater card_order_csum natLeq_card_order
          card_of_card_order_on  
    by blast
qed

lemma arr_fupdate_same: "i < CARD('n) \<Longrightarrow> 
  index (fupdate i f (x::'a['n::finite])) i = f (index x i)"
  by (simp add: fupdate_def)

lemma arr_fupdate_other: "j < CARD('n) \<Longrightarrow> i \<noteq> j \<Longrightarrow> 
  index (fupdate i f (x::'a['n::finite])) j = (index x j)"
  by (simp add: fupdate_def)

lemmas arr_fupdate_simps = arr_fupdate_same arr_fupdate_other

lemma surj_finite_index: "surj finite_index"
  by (metis finite_index_works surj_def)

lemma finite_index_inj_on: "inj_on (finite_index::nat\<Rightarrow>'a::finite) {i. i < CARD('a)}"
  by (simp add: finite_index_inj inj_on_def)

lemma finite_index_bij_betw: "bij_betw (finite_index::nat\<Rightarrow>'a::finite) {i. i < CARD('a)} UNIV"
  using finite_index_inj_on
  by (metis (mono_tags, lifting) UNIV_I bij_betw_def finite_index_works imageI mem_Collect_eq subsetI subset_antisym)


simproc_setup passive fold_update (\<open>Arrays.update a n v\<close>) = \<open>K (fn ctxt => fn ct => 
  \<comment> \<open>Prefer more abstract \<^const>\<open>Arrays.fupdate\<close> over \<^const>\<open>Arrays.update\<close>\<close>
  let
     val {a, n, v, ...} = @{cterm_match "Arrays.update ?a ?n ?v"} ct
     val elem = \<^infer_instantiate>\<open>a = a and n = n  in cterm \<open>a.[n]\<close>\<close> ctxt
     val elem_t = Thm.term_of elem
  in 
    if exists_subterm (fn t => elem_t aconv t) (Thm.term_of v) then 
      SOME (Drule.infer_instantiate ctxt 
        [(("a",0), a), (("n",0), n), (("f", 0), Thm.lambda_name ("v", elem) v)] 
        @{thm Arrays.fupdate_def[symmetric]})
    else 
      NONE 
  end)\<close>

experiment 
begin
lemma "Arrays.update a n (k - a.[n] + x) = fupdate n (\<lambda>v. k - v + x) a "
  supply [[simproc add: fold_update]]
  apply (simp)
  done
end
end

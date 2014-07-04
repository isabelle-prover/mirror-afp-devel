*** Obsolete ***
theory Collections_Patch1
imports 
  "../../Collections/Refine_Dflt"      

  "../../Native_Word/Bits_Integer"

  "../../Native_Word/Uint32" 
  "../../Native_Word/Uint16" 
  "../../Native_Word/Uint8"

  (* Native_Words: Added default-size integers. (Already in devel-version of Native_Words) *)
  "Uint"

(* Collections: Added Code_Target_ICF theory, that sets up code generator for ICF. *)
  "Code_Target_ICF"
begin
  text {* This patch brings the Autoref, Refinement, and Collections Framework to the current
    version in the CAVA repository. *}


(* Native_Words: More lemmas about words *)
context begin interpretation lifting_syntax .

lemma shiftl_transfer [transfer_rule]:
  "(pcr_word ===> op = ===> pcr_word) op << op <<"
  by (auto 
    intro!: Transfer.fun_relI word_eqI 
    simp add: word.pcr_cr_eq cr_word_def word_size nth_shiftl)
end

lemma mask_1: "mask 1 = 1"
by(simp add: mask_def)

lemma mask_Suc_0: "mask (Suc 0) = 1"
by(simp add: mask_def)

lemma mask_numeral: "mask (numeral n) = 2 * mask (pred_numeral n) + 1"
  unfolding mask_def 
  apply transfer 
  apply (simp, simp add: shiftl_int_def)
  apply (fo_rule arg_cong)
  apply auto
  done

(*lemma bin_last_bintrunc: "bin_last (bintrunc l n) = (l > 0 \<and> bin_last n)"
by(cases l) simp_all*)

lemma word_and_1:
  fixes n :: "_ word"
  shows "n AND 1 = (if n !! 0 then 1 else 0)"
by transfer (rule bin_rl_eqI, simp_all add: bin_rest_trunc, metis bin_last_numeral_simps(1) bintrunc_n_0 bitval_bin_last bitval_simps)

lemma bintrunc_shiftl: "bintrunc n (m << i) = bintrunc (n - i) m << i"
proof(induct i arbitrary: n)
  case (Suc i)
  thus ?case by(cases n) simp_all
qed simp

lemma uint_shiftl: "uint (n << i) = bintrunc (size n) (uint n << i)"
unfolding word_size by transfer(simp add: bintrunc_shiftl)

lemma word_and_mask_or_conv_and_mask:
  "n !! index \<Longrightarrow> (n AND mask index) OR (1 << index) = n AND mask (index + 1)"
by(rule word_eqI)(auto simp add: word_ao_nth word_size nth_shiftl simp del: shiftl_1)

lemma uint_and_mask_or_full:
  fixes n :: "'a :: len word"
  assumes "n !! (len_of TYPE('a) - 1)"
  and "mask1 = mask (len_of TYPE('a) - 1)"
  and "mask2 = 1 << len_of TYPE('a) - 1"
  shows "uint (n AND mask1) OR mask2 = uint n"
proof -
  have "mask2 = uint (1 << len_of TYPE('a) - 1 :: 'a word)" using assms
    by(simp add: uint_shiftl word_size bintrunc_shiftl del: shiftl_1)(metis One_nat_def Suc_diff_Suc bintrunc_minus bintrunc_shiftl diff_self_eq_0 len_gt_0 len_num1 lessI uint_1 uint_word_arith_bintrs(9))
  hence "uint (n AND mask1) OR mask2 = uint (n AND mask1 OR (1 << len_of TYPE('a) - 1 :: 'a word))"
    by(simp add: uint_or)
  also have "\<dots> = uint (n AND mask (len_of TYPE('a) - 1 + 1))"
    using assms by(simp only: word_and_mask_or_conv_and_mask)
  also have "\<dots> = uint n" by simp
  finally show ?thesis .
qed


(* Native_Word: Added conversion functions *)
definition uint16_of_nat :: "nat \<Rightarrow> uint16"
where "uint16_of_nat = uint16_of_int \<circ> int"

lift_definition int_of_uint16 :: "uint16 \<Rightarrow> int" is "uint" .
lift_definition nat_of_uint16 :: "uint16 \<Rightarrow> nat" is "unat" .

definition integer_of_uint16 :: "uint16 \<Rightarrow> integer"
  where "integer_of_uint16 = integer_of_int o int_of_uint16"

definition uint32_of_nat :: "nat \<Rightarrow> uint32"
where "uint32_of_nat = uint32_of_int \<circ> int"

lift_definition int_of_uint32 :: "uint32 \<Rightarrow> int" is "uint" .
lift_definition nat_of_uint32 :: "uint32 \<Rightarrow> nat" is "unat" .

definition integer_of_uint32 :: "uint32 \<Rightarrow> integer"
where "integer_of_uint32 = integer_of_int o int_of_uint32"

definition uint8_of_nat :: "nat \<Rightarrow> uint8"
where "uint8_of_nat = uint8_of_int \<circ> int"

lift_definition int_of_uint8 :: "uint8 \<Rightarrow> int" is "uint" .
lift_definition nat_of_uint8 :: "uint8 \<Rightarrow> nat" is "unat" .

definition integer_of_uint8 :: "uint8 \<Rightarrow> integer"
where "integer_of_uint8 = integer_of_int o int_of_uint8"


(* Native_Word: Optimized uintXX_of_int *)

lemma uint16_of_int_code [code]: "uint16_of_int i = Uint16 (integer_of_int i)"
by transfer simp

lemma int_of_uint16_code [code]:
  "int_of_uint16 x = int_of_integer (integer_of_uint16 x)"
by(simp add: integer_of_uint16_def)

lemma nat_of_uint16_code [code]:
  "nat_of_uint16 x = nat_of_integer (integer_of_uint16 x)"
unfolding integer_of_uint16_def by transfer (simp add: unat_def)

definition integer_of_uint16_signed :: "uint16 \<Rightarrow> integer"
where
  "integer_of_uint16_signed n = (if n !! 15 then undefined integer_of_uint16 n else integer_of_uint16 n)"

lemma integer_of_uint16_signed_code [code]:
  "integer_of_uint16_signed n =
  (if n !! 15 then undefined integer_of_uint16 n else integer_of_int (uint (Rep_uint16' n)))"
unfolding integer_of_uint16_signed_def integer_of_uint16_def
including undefined_transfer by simp (transfer, simp)

lemma integer_of_uint16_code [code]:
  "integer_of_uint16 n =
  (if n !! 15 then integer_of_uint16_signed (n AND 0x7FFF) OR 0x8000 else integer_of_uint16_signed n)"
unfolding integer_of_uint16_def integer_of_uint16_signed_def o_def
including undefined_transfer
by transfer(auto simp add: word_ao_nth uint_and_mask_or_full mask_numeral mask_Suc_0 intro!: uint_and_mask_or_full[symmetric])

code_printing
  constant "integer_of_uint16" \<rightharpoonup>
  (SML_word) "Word16.toInt _ : IntInf.int" and
  (Haskell) "Prelude.toInteger" and
  (Scala) "BigInt"

(**************)

lemma uint32_of_int_code [code]: "uint32_of_int i = Uint32 (integer_of_int i)"
by transfer simp

lemma int_of_uint32_code [code]:
  "int_of_uint32 x = int_of_integer (integer_of_uint32 x)"
by(simp add: integer_of_uint32_def)

lemma nat_of_uint32_code [code]:
  "nat_of_uint32 x = nat_of_integer (integer_of_uint32 x)"
unfolding integer_of_uint32_def by transfer (simp add: unat_def)

definition integer_of_uint32_signed :: "uint32 \<Rightarrow> integer"
where
  "integer_of_uint32_signed n = (if n !! 31 then undefined integer_of_uint32 n else integer_of_uint32 n)"

lemma integer_of_uint32_signed_code [code]:
  "integer_of_uint32_signed n =
  (if n !! 31 then undefined integer_of_uint32 n else integer_of_int (uint (Rep_uint32' n)))"
unfolding integer_of_uint32_signed_def integer_of_uint32_def
including undefined_transfer by simp (transfer, simp)

lemma integer_of_uint32_code [code]:
  "integer_of_uint32 n =
  (if n !! 31 then integer_of_uint32_signed (n AND 0x7FFFFFFF) OR 0x80000000 else integer_of_uint32_signed n)"
unfolding integer_of_uint32_def integer_of_uint32_signed_def o_def
including undefined_transfer
by transfer(auto simp add: word_ao_nth uint_and_mask_or_full mask_numeral mask_Suc_0 intro!: uint_and_mask_or_full[symmetric])

code_printing
  constant "integer_of_uint32" \<rightharpoonup>
  (SML) "Word32.toInt _ : IntInf.int" and
  (Haskell) "Prelude.toInteger"
| constant "integer_of_uint32_signed" \<rightharpoonup>
  (OCaml) "Big'_int.big'_int'_of'_int32" and
  (Scala) "BigInt"

(**************)

lemma uint8_of_int_code [code]: "uint8_of_int i = Uint8 (integer_of_int i)"
by transfer simp

lemma int_of_uint8_code [code]:
  "int_of_uint8 x = int_of_integer (integer_of_uint8 x)"
by(simp add: integer_of_uint8_def)

lemma nat_of_uint8_code [code]:
  "nat_of_uint8 x = nat_of_integer (integer_of_uint8 x)"
unfolding integer_of_uint8_def by transfer (simp add: unat_def)

definition integer_of_uint8_signed :: "uint8 \<Rightarrow> integer"
where
  "integer_of_uint8_signed n = (if n !! 7 then undefined integer_of_uint8 n else integer_of_uint8 n)"

lemma integer_of_uint8_signed_code [code]:
  "integer_of_uint8_signed n =
  (if n !! 7 then undefined integer_of_uint8 n else integer_of_int (uint (Rep_uint8' n)))"
unfolding integer_of_uint8_signed_def integer_of_uint8_def
including undefined_transfer
 by simp (transfer, simp)

lemma integer_of_uint8_code [code]:
  "integer_of_uint8 n =
  (if n !! 7 then integer_of_uint8_signed (n AND 0x7F) OR 0x80 else integer_of_uint8_signed n)"
unfolding integer_of_uint8_def integer_of_uint8_signed_def o_def
including undefined_transfer
by transfer(auto simp add: word_ao_nth uint_and_mask_or_full mask_numeral mask_Suc_0 intro!: uint_and_mask_or_full[symmetric])

code_printing
  constant "integer_of_uint8" \<rightharpoonup>
  (SML) "Word8.toInt _ : IntInf.int" and
  (Haskell) "Prelude.toInteger"
| constant "integer_of_uint8_signed" \<rightharpoonup>
  (Scala) "BigInt"




(****************************************************************************)  
(* Automatic_Refinement/Misc *)
(* Addition of Lemmas *)
  
lemma Suc_to_right: "Suc n = m \<Longrightarrow> n = m - Suc 0" by simp
lemma Suc_diff[simp]: "\<And>n m. n\<ge>m \<Longrightarrow> m\<ge>1 \<Longrightarrow> Suc (n - m) = n - (m - 1)"
  by simp
  
  lemma inter_eq_subsetI: "\<lbrakk> S\<subseteq>S'; A\<inter>S' = B\<inter>S' \<rbrakk> \<Longrightarrow> A\<inter>S = B\<inter>S"
    by auto

lemma len_greater_imp_nonempty[simp]: "length l > x \<Longrightarrow> l\<noteq>[]"
  by auto


  lemma drop_upd_irrelevant: "m < n \<Longrightarrow> drop n (l[m:=x]) = drop n l"
    apply (induct n arbitrary: l m)
    apply simp
    apply (case_tac l)
    apply (auto split: nat.split)
    done

lemma Union_take_drop_id: "\<Union>set (drop n l) \<union> \<Union>set (take n l) = \<Union>set l"
  by (metis Union_Un_distrib append_take_drop_id set_union_code sup_commute)

lemma drop_take_drop_unsplit: 
  "i\<le>j \<Longrightarrow> drop i (take j l) @ drop j l = drop i l"
proof -
  assume "i \<le> j"
  then obtain skf where "i + skf = j"
    by (metis Nat.le_iff_add)
  thus "drop i (take j l) @ drop j l = drop i l"
    by (metis append_take_drop_id diff_add_inverse drop_drop drop_take
      add.commute)
qed

lemma drop_last_conv[simp]: "l\<noteq>[] \<Longrightarrow> drop (length l - Suc 0) l = [last l]"
  by (cases l rule: rev_cases) auto

lemma take_butlast_conv[simp]: "take (length l - Suc 0) l = butlast l"
  by (cases l rule: rev_cases) auto


subsubsection {* Last and butlast *}
(* Maybe this should go into List.thy, next to snoc_eq_iff_butlast *)
lemma snoc_eq_iff_butlast': 
  "(ys = xs @ [x]) \<longleftrightarrow> (ys \<noteq> [] \<and> butlast ys = xs \<and> last ys = x)"
  by auto

  text {* A point-free induction rule for elements reachable from an initial set *}
  lemma rtrancl_reachable_induct[consumes 0, case_names base step]:
    assumes I0: "I \<subseteq> INV"
    assumes IS: "E``INV \<subseteq> INV"
    shows "E\<^sup>*``I \<subseteq> INV"
    by (metis I0 IS Image_closed_trancl Image_mono subset_refl)
 

  lemma trancl_image_by_rtrancl: "(E\<^sup>+)``Vi \<union> Vi = (E\<^sup>*)``Vi"
    by (metis Image_Id Un_Image rtrancl_trancl_reflcl)

  lemma reachable_mono: "\<lbrakk>R\<subseteq>R'; X\<subseteq>X'\<rbrakk> \<Longrightarrow> R\<^sup>*``X \<subseteq> R'\<^sup>*``X'"
    by (metis Image_mono rtrancl_mono)

  lemma finite_reachable_advance: 
    "\<lbrakk> finite (E\<^sup>*``{v0}); (v0,v)\<in>E\<^sup>* \<rbrakk> \<Longrightarrow> finite (E\<^sup>*``{v})"
    by (erule finite_subset[rotated]) auto

(****************************************************************************)  
(* Automatic_Refinement/Refine_Util*)
(* Addition of clarsimp_all method *)
setup {*
Method.setup @{binding clarsimp_all} (
           let open Clasimp in
             Method.sections clasimp_modifiers >> K (fn ctxt => SIMPLE_METHOD (
               CHANGED_PROP (ALLGOALS (clarsimp_tac ctxt))))
            end
         ) "Simplify and clarify all subgoals"
*}


(****************************************************************************)  
(* Automatic_Refinement/Relators: Added congruence rules on relations *)
lemma rel_cong: "(f,g)\<in>Id \<Longrightarrow> (x,y)\<in>Id \<Longrightarrow> (f x, g y)\<in>Id" by simp
lemma rel_fun_cong: "(f,g)\<in>Id \<Longrightarrow> (f x, g x)\<in>Id" by simp
lemma rel_arg_cong: "(x,y)\<in>Id \<Longrightarrow> (f x, f y)\<in>Id" by simp

(****************************************************************************)

(* Collections/Impl_Cfun_Set: Added rules for Collect, empty, and UNIV *)
lemma fun_set_Collect_refine[autoref_rules]: 
  "(\<lambda>x. x, Collect)\<in>(R\<rightarrow>bool_rel) \<rightarrow> \<langle>R\<rangle>fun_set_rel"
  unfolding fun_set_rel_def
  by (auto simp: br_def)

lemma fun_set_empty_refine[autoref_rules]: 
  "(\<lambda>_. False,{})\<in>\<langle>R\<rangle>fun_set_rel"
  by (force simp add: fun_set_rel_def br_def)

lemma fun_set_UNIV_refine[autoref_rules]: 
  "(\<lambda>_. True,UNIV)\<in>\<langle>R\<rangle>fun_set_rel"
  by (force simp add: fun_set_rel_def br_def)

(* Collections/Impl_List_Set_Rel: Added rule for filter *)
  lemma list_set_autoref_filter[autoref_rules]:
    "(filter,op_set_filter) 
      \<in> (R \<rightarrow> bool_rel) \<rightarrow> \<langle>R\<rangle>list_set_rel \<rightarrow> \<langle>R\<rangle>list_set_rel"
  proof -
    have "(filter, op_set_filter) 
      \<in> (Id \<rightarrow> bool_rel) \<rightarrow> \<langle>Id\<rangle>list_set_rel \<rightarrow> \<langle>Id\<rangle>list_set_rel"
      by (auto simp: list_set_rel_def br_def)
    note this[param_fo]
    moreover have "(filter,filter)\<in>(R \<rightarrow> bool_rel) \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel"
      unfolding List.filter_def
      by parametricity
    note this[param_fo]
    ultimately show ?thesis
      unfolding list_set_rel_def
      apply (intro fun_relI)
      apply (erule relcompE, simp)
      apply (rule relcompI)
      apply (rprems, assumption+)
      apply (rprems, simp+)
      done
  qed

(* Collections/Impl_List_Set_Rel: Added tagging for list reversal *)
text {* Hack to ensure specific ordering. Note that ordering has no meaning
    abstractly *}
  definition [simp]: "LIST_SET_REV_TAG \<equiv> \<lambda>x. x"
  
  lemma LIST_SET_REV_TAG_autoref[autoref_rules]: 
    "(rev,LIST_SET_REV_TAG) \<in> \<langle>R\<rangle>list_set_rel \<rightarrow> \<langle>R\<rangle>list_set_rel"
    unfolding list_set_rel_def
    apply (intro fun_relI)
    apply (elim relcompE)
    apply (clarsimp simp: br_def)
    apply (rule relcompI)
    apply (rule param_rev[param_fo], assumption)
    apply auto
    done

(* Collections: Added Code_Target_ICF theory, that sets up code generator for ICF. *)

  (* Collections: Added Impl_Bit_Set and Impl_Uv_Set, bitvector based sets *)

(******************** Impl_Bit_Set ***************************)
  text {*
    Based on the Native-Word library, using bit-operations on arbitrary
    precision integers. Fast for sets of small numbers, 
    direct and fast implementations of equal, union, inter, diff.

    Note: On Poly/ML 5.5.1, bit-operations on arbitrary precision integers are 
      rather inefficient. Use MLton instead, here they are efficiently implemented.
    *}

  type_synonym bitset = integer

  definition bs_\<alpha> :: "bitset \<Rightarrow> nat set" where "bs_\<alpha> s \<equiv> { n . test_bit s n}"

  definition bs_empty :: "unit \<Rightarrow> bitset" where "bs_empty \<equiv> \<lambda>_. 0"

  lemma bs_empty_correct: "bs_\<alpha> (bs_empty ()) = {}"
    unfolding bs_\<alpha>_def bs_empty_def 
    apply transfer
    by auto

  definition bs_isEmpty :: "bitset \<Rightarrow> bool" where "bs_isEmpty s \<equiv> s=0"

  lemma bs_isEmpty_correct: "bs_isEmpty s \<longleftrightarrow> bs_\<alpha> s = {}"
    unfolding bs_isEmpty_def bs_\<alpha>_def 
    by transfer (auto simp: bin_eq_iff) 
    
  term set_bit
  definition bs_insert :: "nat \<Rightarrow> bitset \<Rightarrow> bitset" where
    "bs_insert i s \<equiv> set_bit s i True"

  lemma bs_insert_correct: "bs_\<alpha> (bs_insert i s) = insert i (bs_\<alpha> s)"
    unfolding bs_\<alpha>_def bs_insert_def
    apply transfer
    apply auto
    apply (metis bin_nth_sc_gen bin_set_conv_OR int_set_bit_True_conv_OR)
    apply (metis bin_nth_sc_gen bin_set_conv_OR int_set_bit_True_conv_OR)
    by (metis bin_nth_sc_gen bin_set_conv_OR int_set_bit_True_conv_OR)

  definition bs_delete :: "nat \<Rightarrow> bitset \<Rightarrow> bitset" where
    "bs_delete i s \<equiv> set_bit s i False"

  lemma bs_delete_correct: "bs_\<alpha> (bs_delete i s) = (bs_\<alpha> s) - {i}"
    unfolding bs_\<alpha>_def bs_delete_def
    apply transfer
    apply auto
    apply (metis bin_nth_ops(1) int_set_bit_False_conv_NAND)
    apply (metis (full_types) bin_nth_sc bit_not_1_iff set_bit_int_def)
    by (metis (full_types) bin_nth_sc_gen set_bit_int_def)
  
  definition bs_mem :: "nat \<Rightarrow> bitset \<Rightarrow> bool" where
    "bs_mem i s \<equiv> test_bit s i"

  lemma bs_mem_correct: "bs_mem i s \<longleftrightarrow> i\<in>bs_\<alpha> s"
    unfolding bs_mem_def bs_\<alpha>_def by transfer auto


  definition bs_eq :: "bitset \<Rightarrow> bitset \<Rightarrow> bool" where 
    "bs_eq s1 s2 \<equiv> (s1=s2)"

  lemma bs_eq_correct: "bs_eq s1 s2 \<longleftrightarrow> bs_\<alpha> s1 = bs_\<alpha> s2"
    unfolding bs_eq_def bs_\<alpha>_def
    apply transfer
    apply auto
    by (metis bin_eqI mem_Collect_eq test_bit_int_def)

  definition bs_subset_eq :: "bitset \<Rightarrow> bitset \<Rightarrow> bool" where
    "bs_subset_eq s1 s2 \<equiv> s1 AND NOT s2 = 0"
  
  lemma bs_subset_eq_correct: "bs_subset_eq s1 s2 \<longleftrightarrow> bs_\<alpha> s1 \<subseteq> bs_\<alpha> s2"
    unfolding bs_\<alpha>_def bs_subset_eq_def
    apply transfer
    apply rule
    apply auto []
    apply (metis bin_nth_code(1) bin_nth_ops(1) bin_nth_ops(4))
    apply (auto intro!: bin_eqI simp: bin_nth_ops)
    done

  definition bs_disjoint :: "bitset \<Rightarrow> bitset \<Rightarrow> bool" where
    "bs_disjoint s1 s2 \<equiv> s1 AND s2 = 0"
  
  lemma bs_disjoint_correct: "bs_disjoint s1 s2 \<longleftrightarrow> bs_\<alpha> s1 \<inter> bs_\<alpha> s2 = {}"
    unfolding bs_\<alpha>_def bs_disjoint_def
    apply transfer
    apply rule
    apply auto []
    apply (metis bin_nth_code(1) bin_nth_ops(1))
    apply (auto intro!: bin_eqI simp: bin_nth_ops)
    done

  definition bs_union :: "bitset \<Rightarrow> bitset \<Rightarrow> bitset" where
    "bs_union s1 s2 = s1 OR s2"

  lemma bs_union_correct: "bs_\<alpha> (bs_union s1 s2) = bs_\<alpha> s1 \<union> bs_\<alpha> s2"
    unfolding bs_\<alpha>_def bs_union_def
    by transfer (auto simp: bin_nth_ops)

  definition bs_inter :: "bitset \<Rightarrow> bitset \<Rightarrow> bitset" where
    "bs_inter s1 s2 = s1 AND s2"

  lemma bs_inter_correct: "bs_\<alpha> (bs_inter s1 s2) = bs_\<alpha> s1 \<inter> bs_\<alpha> s2"
    unfolding bs_\<alpha>_def bs_inter_def
    by transfer (auto simp: bin_nth_ops)

  definition bs_diff :: "bitset \<Rightarrow> bitset \<Rightarrow> bitset" where
    "bs_diff s1 s2 = s1 AND NOT s2"

  lemma bs_diff_correct: "bs_\<alpha> (bs_diff s1 s2) = bs_\<alpha> s1 - bs_\<alpha> s2"
    unfolding bs_\<alpha>_def bs_diff_def
    by transfer (auto simp: bin_nth_ops)

  definition bs_UNIV :: "unit \<Rightarrow> bitset" where "bs_UNIV \<equiv> \<lambda>_. -1"

  lemma bs_UNIV_correct: "bs_\<alpha> (bs_UNIV ()) = UNIV"
    unfolding bs_\<alpha>_def bs_UNIV_def
    by transfer (auto)

  definition bs_complement :: "bitset \<Rightarrow> bitset" where
    "bs_complement s = NOT s"

  lemma bs_complement_correct: "bs_\<alpha> (bs_complement s) = - bs_\<alpha> s"
    unfolding bs_\<alpha>_def bs_complement_def
    by transfer (auto simp: bin_nth_ops)


  lemmas bs_correct[simp] = 
    bs_empty_correct
    bs_isEmpty_correct
    bs_insert_correct
    bs_delete_correct
    bs_mem_correct
    bs_eq_correct
    bs_subset_eq_correct
    bs_disjoint_correct
    bs_union_correct
    bs_inter_correct
    bs_diff_correct
    bs_UNIV_correct
    bs_complement_correct


subsection {* Autoref Setup *}

definition bs_set_rel_def_internal: 
  "bs_set_rel Rk \<equiv> 
    if Rk=nat_rel then br bs_\<alpha> (\<lambda>_. True) else {}"
lemma bs_set_rel_def: 
  "\<langle>nat_rel\<rangle>bs_set_rel \<equiv> br bs_\<alpha> (\<lambda>_. True)" 
  unfolding bs_set_rel_def_internal relAPP_def by simp

lemmas [autoref_rel_intf] = REL_INTFI[of "bs_set_rel" i_set]

lemma bs_set_rel_sv[relator_props]: "single_valued (\<langle>nat_rel\<rangle>bs_set_rel)"
  unfolding bs_set_rel_def by auto


term bs_empty

lemma [autoref_rules]: "(bs_empty (),{})\<in>\<langle>nat_rel\<rangle>bs_set_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_UNIV (),UNIV)\<in>\<langle>nat_rel\<rangle>bs_set_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_isEmpty,op_set_isEmpty)\<in>\<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> bool_rel"
  by (auto simp: bs_set_rel_def br_def)

term insert
lemma [autoref_rules]: "(bs_insert,insert)\<in>nat_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel"
  by (auto simp: bs_set_rel_def br_def)

term op_set_delete
lemma [autoref_rules]: "(bs_delete,op_set_delete)\<in>nat_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_mem,op \<in>)\<in>nat_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> bool_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_eq,op =)\<in>\<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> bool_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_subset_eq,op \<subseteq>)\<in>\<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> bool_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_union,op \<union>)\<in>\<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_inter,op \<inter>)\<in>\<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_diff,op -)\<in>\<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_complement,uminus)\<in>\<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_disjoint,op_set_disjoint)\<in>\<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> bool_rel"
  by (auto simp: bs_set_rel_def br_def)


export_code 
    bs_empty
    bs_isEmpty
    bs_insert
    bs_delete
    bs_mem
    bs_eq
    bs_subset_eq
    bs_disjoint
    bs_union
    bs_inter
    bs_diff
    bs_UNIV
    bs_complement
 in SML


(****************** Impl_Uv_Set ************************)
  subsection {* Bit-Vectors as Lists of Words *}

  subsubsection {* Lookup *}

  primrec lookup :: "nat \<Rightarrow> ('a::len) word list \<Rightarrow> bool" where
    "lookup _ [] \<longleftrightarrow> False"
  | "lookup n (w#ws) 
      \<longleftrightarrow> (if n<len_of TYPE('a) then test_bit w n else lookup (n-len_of TYPE('a)) ws)"

  lemma lookup_append[simp]: "lookup n (w1@w2 :: 'a::len word list) 
    \<longleftrightarrow> (
      if n < len_of TYPE('a) * length w1 then 
        lookup n w1 
      else lookup (n - len_of TYPE('a) * length w1) w2)"
    by (induction w1 arbitrary: n) auto

  lemma lookup_zeroes[simp]: "lookup i (replicate n (0\<Colon>'a::len word)) = False"
    by (induction n arbitrary: i) auto

  lemma lookup_out_of_bound: 
    fixes uv :: "'a::len word list"
    assumes "\<not> i < len_of TYPE('a::len) * length uv" 
    shows "\<not> lookup i uv"
    using assms
    by (induction uv arbitrary: i) auto


  subsubsection {* Empty *}

  definition empty :: "'a::len word list" where "empty = []"

  subsubsection {* Set and Reset Bit *}

  function single_bit :: "nat \<Rightarrow> ('a::len) word list" 
    where "single_bit n = (
      if (n<len_of TYPE('a)) then 
        [set_bit 0 n True] 
      else 0#single_bit (n-len_of TYPE('a)))"
    by pat_completeness auto
  termination
    apply (relation "measure id")
    apply simp
    apply simp
    by (metis diff_less le0 lens_not_0(2) sup.semilattice_strict_iff_order)

  declare single_bit.simps[simp del]

  lemma lookup_single_bit[simp]: "lookup i ((single_bit n)::'a::len word list) \<longleftrightarrow> i = n"
    apply (induction n arbitrary: i rule: single_bit.induct)
    apply (subst single_bit.simps)
    apply (auto simp: bin_nth_sc_gen)
    done

  primrec set_bit :: "nat \<Rightarrow> 'a::len word list \<Rightarrow> 'a::len word list" where
    "set_bit i [] = single_bit i"
  | "set_bit i (w#ws) = (
      if i<len_of TYPE('a) then 
        Bit_Operations.set_bit w i True # ws 
      else 
        w # set_bit (i - len_of TYPE('a)) ws)"
  
  lemma set_bit_lookup[simp]: "lookup i (set_bit j ws) \<longleftrightarrow> (lookup i ws \<or> i=j)"
    apply (induction ws arbitrary: i j)
    apply (auto simp: test_bit_set_gen word_size)
    done


  primrec reset_bit :: "nat \<Rightarrow> 'a::len word list \<Rightarrow> 'a::len word list" where
    "reset_bit i [] = []"
  | "reset_bit i (w#ws) = (
      if i<len_of TYPE('a) then 
        Bit_Operations.set_bit w i False # ws 
      else 
        w # reset_bit (i - len_of TYPE('a)) ws)"
  
  lemma reset_bit_lookup[simp]: "lookup i (reset_bit j ws) \<longleftrightarrow> (lookup i ws \<and> i\<noteq>j)"
    apply (induction ws arbitrary: i j)
    apply (auto simp: test_bit_set_gen word_size)
    done

  subsubsection {* Binary Operations *}

  definition 
    is_bin_op_impl 
    :: "(bool\<Rightarrow>bool\<Rightarrow>bool) \<Rightarrow> ('a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word) \<Rightarrow> bool"
    where "is_bin_op_impl f g \<equiv> 
    (\<forall>w v.  \<forall>i<len_of TYPE('a). test_bit (g w v) i \<longleftrightarrow> f (test_bit w i) (test_bit v i))"

  definition "is_strict_bin_op_impl f g \<equiv> is_bin_op_impl f g \<and> f False False = False"

  fun binary :: "('a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word) 
    \<Rightarrow> 'a::len word list \<Rightarrow> 'a::len word list \<Rightarrow> 'a::len word list"
    where 
    "binary f [] [] = []"
  | "binary f [] (w#ws) = f 0 w # binary f [] ws"
  | "binary f (v#vs) [] = f v 0 # binary f vs []"
  | "binary f (v#vs) (w#ws) = f v w # binary f vs ws"

  lemma binary_lookup:
    assumes "is_strict_bin_op_impl f g"
    shows "lookup i (binary g ws vs) \<longleftrightarrow> f (lookup i ws) (lookup i vs)"
    using assms
    apply (induction g ws vs arbitrary: i rule: binary.induct)
    apply (auto simp: is_strict_bin_op_impl_def is_bin_op_impl_def)
    done

  subsection {* Abstraction to Sets of Naturals *}

  definition "\<alpha> uv \<equiv> {n. lookup n uv}"
  
  lemma memb_correct: "lookup i ws \<longleftrightarrow> i\<in>\<alpha> ws"
    by (auto simp: \<alpha>_def)

  lemma empty_correct: "\<alpha> empty = {}"
    by (simp add: \<alpha>_def empty_def)

  lemma single_bit_correct: "\<alpha> (single_bit n) = {n}"
    by (simp add: \<alpha>_def)

  lemma insert_correct: "\<alpha> (set_bit i ws) = Set.insert i (\<alpha> ws)"
    by (auto simp add: \<alpha>_def)

  lemma delete_correct: "\<alpha> (reset_bit i ws) = (\<alpha> ws) - {i}"
    by (auto simp add: \<alpha>_def)

  lemma binary_correct:
    assumes "is_strict_bin_op_impl f g"
    shows "\<alpha> (binary g ws vs) = { i . f (i\<in>\<alpha> ws) (i\<in>\<alpha> vs) }"
    unfolding \<alpha>_def
    by (auto simp add: binary_lookup[OF assms])

  fun union :: "'a::len word list \<Rightarrow> 'a::len word list \<Rightarrow> 'a::len word list"
    where 
    "union [] ws = ws"
  | "union vs [] = vs"
  | "union (v#vs) (w#ws) = (v OR w) # union vs ws"

  lemma union_lookup[simp]:
    fixes vs :: "'a::len word list" 
    shows "lookup i (union vs ws) \<longleftrightarrow> lookup i vs \<or> lookup i ws"
    apply (induction vs ws arbitrary: i rule: union.induct)
    apply (auto simp: word_ao_nth)
    done

  lemma union_correct: "\<alpha> (union ws vs) = \<alpha> ws \<union> \<alpha> vs"
    by (auto simp add: \<alpha>_def)

  fun inter :: "'a::len word list \<Rightarrow> 'a::len word list \<Rightarrow> 'a::len word list"
    where 
    "inter [] ws = []"
  | "inter vs [] = []"
  | "inter (v#vs) (w#ws) = (v AND w) # inter vs ws"

  lemma inter_lookup[simp]:
    fixes vs :: "'a::len word list" 
    shows "lookup i (inter vs ws) \<longleftrightarrow> lookup i vs \<and> lookup i ws"
    apply (induction vs ws arbitrary: i rule: inter.induct)
    apply (auto simp: word_ao_nth)
    done

  lemma inter_correct: "\<alpha> (inter ws vs) = \<alpha> ws \<inter> \<alpha> vs"
    by (auto simp add: \<alpha>_def)


  fun diff :: "'a::len word list \<Rightarrow> 'a::len word list \<Rightarrow> 'a::len word list"
    where 
    "diff [] ws = []"
  | "diff vs [] = vs"
  | "diff (v#vs) (w#ws) = (v AND NOT w) # diff vs ws"

  lemma diff_lookup[simp]:
    fixes vs :: "'a::len word list" 
    shows "lookup i (diff vs ws) \<longleftrightarrow> lookup i vs - lookup i ws"
    apply (induction vs ws arbitrary: i rule: diff.induct)
    apply (auto simp: word_ops_nth_size word_size)
    done

  lemma diff_correct: "\<alpha> (diff ws vs) = \<alpha> ws - \<alpha> vs"
    by (auto simp add: \<alpha>_def)
   
  fun zeroes :: "'a::len word list \<Rightarrow> bool" where
    "zeroes [] \<longleftrightarrow> True"
  | "zeroes (w#ws) \<longleftrightarrow> w=0 \<and> zeroes ws"

  lemma zeroes_lookup: "zeroes ws \<longleftrightarrow> (\<forall>i. \<not>lookup i ws)"
    apply (induction ws)
    apply (auto simp: word_eq_iff)
    by (metis diff_add_inverse2 not_add_less2)

  lemma isEmpty_correct: "zeroes ws \<longleftrightarrow> \<alpha> ws = {}"
    by (auto simp: zeroes_lookup \<alpha>_def)

  fun equal :: "'a::len word list \<Rightarrow> 'a::len word list \<Rightarrow> bool" where
    "equal [] [] \<longleftrightarrow> True"
  | "equal [] ws \<longleftrightarrow> zeroes ws"
  | "equal vs [] \<longleftrightarrow> zeroes vs"
  | "equal (v#vs) (w#ws) \<longleftrightarrow> v=w \<and> equal vs ws"

  lemma equal_lookup: 
    fixes vs ws :: "'a::len word list"
    shows "equal vs ws \<longleftrightarrow> (\<forall>i. lookup i vs = lookup i ws)"
  proof (induction vs ws rule: equal.induct)
    fix v w and vs ws :: "'a::len word list"
    assume IH: "equal vs ws = (\<forall>i. lookup i vs = lookup i ws)"
    show "equal (v # vs) (w # ws) = (\<forall>i. lookup i (v # vs) = lookup i (w # ws))"
    proof (rule iffI, rule allI)
      fix i
      assume "equal (v#vs) (w#ws)"
      thus "lookup i (v # vs) = lookup i (w # ws)"
        by (auto simp: IH)
    next
      assume "\<forall>i. lookup i (v # vs) = lookup i (w # ws)"
      thus "equal (v # vs) (w # ws)"
        apply (auto simp: word_eq_iff IH)
        apply metis
        apply metis
        apply (drule_tac x="i + len_of TYPE('a)" in spec)
        apply auto []
        apply (drule_tac x="i + len_of TYPE('a)" in spec)
        apply auto []
        done
    qed
  qed (auto simp: zeroes_lookup)
    
  lemma equal_correct: "equal vs ws \<longleftrightarrow> \<alpha> vs = \<alpha> ws"
    by (auto simp: \<alpha>_def equal_lookup)
  
  fun subseteq :: "'a::len word list \<Rightarrow> 'a::len word list \<Rightarrow> bool" where
    "subseteq [] ws \<longleftrightarrow> True"
  | "subseteq vs [] \<longleftrightarrow> zeroes vs"
  | "subseteq (v#vs) (w#ws) \<longleftrightarrow> (v AND NOT w = 0) \<and> subseteq vs ws"

  
  lemma subseteq_lookup: 
    fixes vs ws :: "'a::len word list"
    shows "subseteq vs ws \<longleftrightarrow> (\<forall>i. lookup i vs \<longrightarrow> lookup i ws)"
    apply (induction vs ws rule: subseteq.induct)
    apply simp
    apply (auto simp: zeroes_lookup) []
    apply (auto simp: word_ops_nth_size word_size word_eq_iff)
    by (metis diff_add_inverse2 not_add_less2)

  lemma subseteq_correct: "subseteq vs ws \<longleftrightarrow> \<alpha> vs \<subseteq> \<alpha> ws"
    by (auto simp: \<alpha>_def subseteq_lookup)


  fun subset :: "'a::len word list \<Rightarrow> 'a::len word list \<Rightarrow> bool" where
    "subset [] ws \<longleftrightarrow> \<not>zeroes ws"
  | "subset vs [] \<longleftrightarrow> False"
  | "subset (v#vs) (w#ws) \<longleftrightarrow> (if v=w then subset vs ws else subseteq (v#vs) (w#ws))"

  lemma subset_lookup: 
    fixes vs ws :: "'a::len word list"
    shows "subset vs ws \<longleftrightarrow> ((\<forall>i. lookup i vs \<longrightarrow> lookup i ws) 
      \<and> (\<exists>i. \<not>lookup i vs \<and> lookup i ws))"
    apply (induction vs ws rule: subset.induct)
    apply (simp add: zeroes_lookup)
    apply (simp add: zeroes_lookup) []
    apply (simp del: subseteq_correct add: subseteq_lookup)
    apply safe
    apply simp_all
    apply (auto simp: word_ops_nth_size word_size word_eq_iff)
    done

  lemma subset_correct: "subset vs ws \<longleftrightarrow> \<alpha> vs \<subset> \<alpha> ws"
    by (auto simp: \<alpha>_def subset_lookup)

  
  fun disjoint :: "'a::len word list \<Rightarrow> 'a::len word list \<Rightarrow> bool" where
    "disjoint [] ws \<longleftrightarrow> True"
  | "disjoint vs [] \<longleftrightarrow> True"
  | "disjoint (v#vs) (w#ws) \<longleftrightarrow> (v AND w = 0) \<and> disjoint vs ws"

  lemma disjoint_lookup: 
    fixes vs ws :: "'a::len word list"
    shows "disjoint vs ws \<longleftrightarrow> (\<forall>i. \<not>(lookup i vs \<and> lookup i ws))"
    apply (induction vs ws rule: disjoint.induct)
    apply simp
    apply simp
    apply (auto simp: word_ops_nth_size word_size word_eq_iff)
    by (metis diff_add_inverse2 not_add_less2)

  lemma disjoint_correct: "disjoint vs ws \<longleftrightarrow> \<alpha> vs \<inter> \<alpha> ws = {}"
    by (auto simp: \<alpha>_def disjoint_lookup)

  
subsection {* Lifting to Uint *}
  type_synonym uint_vector = "uint list"

  lift_definition uv_\<alpha> :: "uint_vector \<Rightarrow> nat set" is \<alpha> .
  lift_definition uv_lookup :: "nat \<Rightarrow> uint_vector \<Rightarrow> bool" is lookup .
  lift_definition uv_empty :: "uint_vector" is empty .
  lift_definition uv_single_bit :: "nat \<Rightarrow> uint_vector" is single_bit .
  lift_definition uv_set_bit :: "nat \<Rightarrow> uint_vector \<Rightarrow> uint_vector" is set_bit .
  lift_definition uv_reset_bit :: "nat \<Rightarrow> uint_vector \<Rightarrow> uint_vector" is reset_bit .
  lift_definition uv_union :: "uint_vector \<Rightarrow> uint_vector \<Rightarrow> uint_vector" is union .
  lift_definition uv_inter :: "uint_vector \<Rightarrow> uint_vector \<Rightarrow> uint_vector" is inter .
  lift_definition uv_diff :: "uint_vector \<Rightarrow> uint_vector \<Rightarrow> uint_vector" is diff .
  lift_definition uv_zeroes :: "uint_vector \<Rightarrow> bool" is zeroes .
  lift_definition uv_equal :: "uint_vector \<Rightarrow> uint_vector \<Rightarrow> bool" is equal .
  lift_definition uv_subseteq :: "uint_vector \<Rightarrow> uint_vector \<Rightarrow> bool" is subseteq .
  lift_definition uv_subset :: "uint_vector \<Rightarrow> uint_vector \<Rightarrow> bool" is subset .
  lift_definition uv_disjoint :: "uint_vector \<Rightarrow> uint_vector \<Rightarrow> bool" is disjoint .

  lemmas uv_memb_correct = memb_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_empty_correct = empty_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_single_bit_correct = single_bit_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_insert_correct = insert_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_delete_correct = delete_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_union_correct = union_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_inter_correct = inter_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_diff_correct = diff_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_isEmpty_correct = isEmpty_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_equal_correct = equal_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_subseteq_correct = subseteq_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_subset_correct = subset_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_disjoint_correct = disjoint_correct[where 'a=dflt_size, Transfer.transferred]



  lemmas [where 'a=dflt_size, Transfer.transferred, code] = 
    lookup.simps 
    empty_def
    single_bit.simps 
    set_bit.simps 
    reset_bit.simps 
    union.simps 
    inter.simps 
    diff.simps 
    zeroes.simps 
    equal.simps 
    subseteq.simps 
    subset.simps 
    disjoint.simps 
    

  hide_const (open) \<alpha> lookup empty single_bit set_bit reset_bit union inter diff zeroes 
    equal subseteq subset disjoint


subsection {* Autoref Setup *}

  definition uv_set_rel_def_internal: 
    "uv_set_rel Rk \<equiv> 
      if Rk=nat_rel then br uv_\<alpha> (\<lambda>_. True) else {}"
  lemma uv_set_rel_def: 
    "\<langle>nat_rel\<rangle>uv_set_rel \<equiv> br uv_\<alpha> (\<lambda>_. True)" 
    unfolding uv_set_rel_def_internal relAPP_def by simp

  lemmas [autoref_rel_intf] = REL_INTFI[of "uv_set_rel" i_set]

  lemma uv_set_rel_sv[relator_props]: "single_valued (\<langle>nat_rel\<rangle>uv_set_rel)"
    unfolding uv_set_rel_def by auto

  lemma uv_autoref[autoref_rules,param]:
    "(uv_lookup,op \<in>) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> bool_rel"
    "(uv_empty,{}) \<in> \<langle>nat_rel\<rangle>uv_set_rel"
    "(uv_set_bit,insert) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel"
    "(uv_reset_bit,op_set_delete) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel"
    "(uv_union,op \<union>) \<in> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel"
    "(uv_inter,op \<inter>) \<in> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel"
    "(uv_diff,op -) \<in> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel"
    "(uv_zeroes,op_set_isEmpty) \<in> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> bool_rel"
    "(uv_equal,op =) \<in> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> bool_rel"
    "(uv_subseteq,op \<subseteq>) \<in> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> bool_rel"
    "(uv_subset,op \<subset>) \<in> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> bool_rel"
    "(uv_disjoint,op_set_disjoint) \<in> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> bool_rel"
    by (auto 
      simp: uv_set_rel_def br_def
      simp: uv_memb_correct uv_empty_correct uv_insert_correct uv_delete_correct
      simp: uv_union_correct uv_inter_correct uv_diff_correct uv_isEmpty_correct
      simp: uv_equal_correct uv_subseteq_correct uv_subset_correct uv_disjoint_correct)


  export_code 
    uv_lookup 
    uv_empty
    uv_single_bit 
    uv_set_bit 
    uv_reset_bit 
    uv_union 
    uv_inter 
    uv_diff 
    uv_zeroes 
    uv_equal 
    uv_subseteq 
    uv_subset 
    uv_disjoint 
  checking SML Scala (*Haskell?*) OCaml?


(* Collections/List_Set_Impl: Optimized set_op_to_list by list_of_dlist.
    Hard to patch w/o modifying existing source. 
    Only performance optimization, so leave it unchanged.
*)

(* Collections/List_Set_Impl_Invar: Optimized set_op_to_list *)


(* Refine_Monadic/Refine_Basic: Changed rules to be eta-expanded, to allow better
    preservation of original variable names within vcg *)

lemmas [refine_vcg del] = bind_rule
lemmas [refine del] = bind_refine bind_refine_RES REC_refine RECT_refine
  option_case_refine

lemmas [refine2 del] = bind2let_refine bind2letRETURN_refine intro_spec_refine

lemma bind_rule[refine_vcg]: 
  "\<lbrakk> M \<le> SPEC (\<lambda>x. f x \<le> SPEC \<Phi>) \<rbrakk> \<Longrightarrow> bind M (\<lambda>x. f x) \<le> SPEC \<Phi>"
  by (rule bind_rule)

lemma bind_refine':
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x'. \<lbrakk> (x,x')\<in>R'; inres M x; inres M' x';
    nofail M; nofail M'
  \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bind M (\<lambda>x. f x) \<le> \<Down> R (bind M' (\<lambda>x'. f' x'))"
  using assms
  by (rule bind_refine')+

lemma bind_refine[refine]:
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x'. \<lbrakk> (x,x')\<in>R' \<rbrakk> 
    \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bind M (\<lambda>x. f x) \<le> \<Down> R (bind M' (\<lambda>x'. f' x'))"
  using assms by (rule bind_refine)

lemma bind_refine_RES:
  "\<lbrakk>RES X \<le> \<Down> R' M';
  \<And>x x'. \<lbrakk>(x, x') \<in> R'; x \<in> X \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')\<rbrakk>
  \<Longrightarrow> RES X \<guillemotright>= (\<lambda>x. f x) \<le> \<Down> R (M' \<guillemotright>= (\<lambda>x'. f' x'))"

  "\<lbrakk>M \<le> \<Down> R' (RES X');
  \<And>x x'. \<lbrakk>(x, x') \<in> R'; x' \<in> X' \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')\<rbrakk>
  \<Longrightarrow> M \<guillemotright>= (\<lambda>x. f x) \<le> \<Down> R (RES X' \<guillemotright>= (\<lambda>x'. f' x'))"

  "\<lbrakk>RES X \<le> \<Down> R' (RES X');
  \<And>x x'. \<lbrakk>(x, x') \<in> R'; x \<in> X; x' \<in> X'\<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')\<rbrakk>
  \<Longrightarrow> RES X \<guillemotright>= (\<lambda>x. f x) \<le> \<Down> R (RES X' \<guillemotright>= (\<lambda>x'. f' x'))"
  apply (rule bind_refine_RES(1), assumption+)
  apply (rule bind_refine_RES(2), assumption+)
  apply (rule bind_refine_RES(3), assumption+)
  done

declare bind_refine_RES(1,2)[refine]
declare bind_refine_RES(3)[refine]

lemma REC_refine[refine]:
  assumes M: "mono body"
  assumes R0: "(x,x')\<in>R"
  assumes RS: "\<And>f f' x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> f x \<le>\<Down>S (f' x'); (x,x')\<in>R \<rbrakk> 
    \<Longrightarrow> body f x \<le>\<Down>S (body' f' x')"
  shows "REC (\<lambda>f x. body f x) x \<le>\<Down>S (REC (\<lambda>f' x'. body' f' x') x')"
  using assms by (rule REC_refine)

lemma RECT_refine[refine]:
  assumes M: "mono body"
  assumes R0: "(x,x')\<in>R"
  assumes RS: "\<And>f f' x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> f x \<le>\<Down>S (f' x'); (x,x')\<in>R \<rbrakk> 
    \<Longrightarrow> body f x \<le>\<Down>S (body' f' x')"
  shows "RECT (\<lambda>f x. body f x) x \<le>\<Down>S (RECT (\<lambda>f' x'. body' f' x') x')"
  using assms by (rule RECT_refine)

lemma Let_refine:
  assumes "(m,m')\<in>R'"
  assumes "\<And>x x'. (x,x')\<in>R' \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "Let m (\<lambda>x. f x) \<le>\<Down>R (Let m' (\<lambda>x'. f' x'))"
  using assms by auto

lemma option_case_refine[refine]:
  assumes "(x,x')\<in>Id"
  assumes "fn \<le> \<Down>R fn'"
  assumes "\<And>v v'. \<lbrakk>x=Some v; (v,v')\<in>Id\<rbrakk> \<Longrightarrow> fs v \<le> \<Down>R (fs' v')"
  shows "option_case fn (\<lambda>v. fs v) x \<le> \<Down>R (option_case fn' (\<lambda>v'. fs' v') x')"
  using assms by (auto split: option.split)

lemma bind2let_refine[refine2]:
  assumes "RETURN x \<le> \<Down>R' M'"
  assumes "\<And>x'. (x,x')\<in>R' \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "Let x f \<le> \<Down>R (bind M' (\<lambda>x'. f' x'))"
  using assms by (rule bind2let_refine)

lemma bind2letRETURN_refine[refine2]:
  assumes "RETURN x \<le> \<Down>R' M'"
  assumes "\<And>x'. (x,x')\<in>R' \<Longrightarrow> RETURN (f x) \<le> \<Down>R (f' x')"
  shows "RETURN (Let x f) \<le> \<Down>R (bind M' (\<lambda>x'. f' x'))"
  using assms by (rule bind2letRETURN_refine)

lemma intro_spec_refine[refine2]:
  assumes "\<And>x. x\<in>X \<Longrightarrow> f x \<le> \<Down>R M"
  shows "bind (RES X) (\<lambda>x. f x) \<le> \<Down>R M"
  using assms by (rule intro_spec_refine)

text {* Replacing a let by a deterministic computation *}
lemma let2bind_refine:
  assumes "m \<le> \<Down>R' (RETURN m')"
  assumes "\<And>x x'. (x,x')\<in>R' \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "bind m (\<lambda>x. f x) \<le> \<Down>R (Let m' (\<lambda>x'. f' x'))"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)
  apply blast
  done

text {* Introduce a new binding, without a structural match in the abstract 
  program *}
lemma intro_bind_refine:
  assumes "m \<le> \<Down>R' (RETURN m')"
  assumes "\<And>x. (x,m')\<in>R' \<Longrightarrow> f x \<le> \<Down>R m''"
  shows "bind m (\<lambda>x. f x) \<le> \<Down>R m''"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)
  apply blast
  done

(* Refine_Monadic/Refine_Basic: Added some convenience rules *)
lemma le_SPEC_bindI: 
  assumes "\<Phi> x"
  assumes "m \<le> f x"
  shows "m \<le> SPEC \<Phi> \<guillemotright>= f"
  using assms by (auto simp add: pw_le_iff refine_pw_simps)

lemma bind_assert_refine: 
  assumes "m1 \<le> SPEC \<Phi>"
  assumes "\<And>x. \<Phi> x \<Longrightarrow> m2 x \<le> m'"
  shows "do {x\<leftarrow>m1; ASSERT (\<Phi> x); m2 x} \<le> m'"
  using assms
  by (simp add: pw_le_iff refine_pw_simps) blast

lemma let_to_bind_conv: 
  "Let x f = RETURN x\<guillemotright>=f"
  by simp

lemmas bind_to_let_conv = let_to_bind_conv[symmetric]

lemma pull_out_let_conv: "RETURN (Let x f) = Let x (\<lambda>x. RETURN (f x))"
  by simp

lemma push_in_let_conv: 
  "Let x (\<lambda>x. RETURN (f x)) = RETURN (Let x f)"
  "Let x (RETURN o f) = RETURN (Let x f)"
  by simp_all

(* Refine_Monadic/Refine_Transfer: Added relator based transfer rules *)
subsection {* Relator-Based Transfer *}

definition dres_nres_rel_internal_def: 
  "dres_nres_rel R \<equiv> {(c,a). nres_of c \<le> \<Down> R a}"

lemma dres_nres_rel_def: "\<langle>R\<rangle>dres_nres_rel \<equiv> {(c,a). nres_of c \<le> \<Down> R a}"
  by (simp add: dres_nres_rel_internal_def relAPP_def)

lemma dres_nres_relI[intro?]: "nres_of c \<le> \<Down> R a \<Longrightarrow> (c,a)\<in>\<langle>R\<rangle>dres_nres_rel"
  by (simp add: dres_nres_rel_def)

lemma dres_nres_relD: "(c,a)\<in>\<langle>R\<rangle>dres_nres_rel \<Longrightarrow> nres_of c \<le> \<Down> R a"
  by (simp add: dres_nres_rel_def)

lemma dres_nres_rel_as_br_conv: 
  "\<langle>R\<rangle>dres_nres_rel = br nres_of (\<lambda>_. True) O \<langle>R\<rangle>nres_rel"
  unfolding dres_nres_rel_def br_def nres_rel_def by auto


definition plain_nres_rel_internal_def: 
  "plain_nres_rel R \<equiv> {(c,a). RETURN c \<le> \<Down> R a}"

lemma plain_nres_rel_def: "\<langle>R\<rangle>plain_nres_rel \<equiv> {(c,a). RETURN c \<le> \<Down> R a}"
  by (simp add: plain_nres_rel_internal_def relAPP_def)

lemma plain_nres_relI[intro?]: "RETURN c \<le> \<Down> R a \<Longrightarrow> (c,a)\<in>\<langle>R\<rangle>plain_nres_rel"
  by (simp add: plain_nres_rel_def)

lemma plain_nres_relD: "(c,a)\<in>\<langle>R\<rangle>plain_nres_rel \<Longrightarrow> RETURN c \<le> \<Down> R a"
  by (simp add: plain_nres_rel_def)

lemma plain_nres_rel_as_br_conv: 
  "\<langle>R\<rangle>plain_nres_rel = br RETURN (\<lambda>_. True) O \<langle>R\<rangle>nres_rel"
  unfolding plain_nres_rel_def br_def nres_rel_def by auto

(* TODO: Refine_Transfer could be expressed also just as a 
    parametricity based transfer, and based on the same infrastructure
    as autoref *)


(* Collections: Changed hashcode to use uint32 instead of nat. 
  Unfortunately, this change is difficult to patch without modifying the original
  sources. As it is only a performance issue, we'll leave it as is for now, and only
  apply the change to the development version of AFP.

  Nevertheless, we introduce some effcient hashcode here, that
  can be used to define hashcode for new types
*)
definition "nat_of_hashcode_uint \<equiv> nat_of_uint32"
definition "int_of_hashcode_uint \<equiv> int_of_uint32"
definition "integer_of_hashcode_uint \<equiv> integer_of_uint32"

class hashable_uint = 
  fixes hashcode_uint :: "'a \<Rightarrow> uint32"
  and def_hashmap_size_uint :: "'a itself \<Rightarrow> nat"
  assumes def_hashmap_size_uint: "1 < def_hashmap_size_uint TYPE('a)"
begin

  definition hashcode_nat where "hashcode_nat \<equiv> nat_of_hashcode_uint o hashcode_uint"
  definition bounded_hashcode_nat 
    where "bounded_hashcode_nat n x \<equiv> hashcode_nat x mod n"

  lemma hashable_from_hashable_uint: 
    "1 < n \<Longrightarrow> bounded_hashcode_nat n a < n"
    "1 < def_hashmap_size_uint TYPE('a)"
    unfolding bounded_hashcode_nat_def
    using def_hashmap_size_uint
    by auto

end


instantiation unit :: hashable_uint
begin
  definition [simp]: "hashcode_uint (u :: unit) = 0"
  definition "def_hashmap_size_uint = (\<lambda>_ :: unit itself. 2)"
  instance
    by (intro_classes)(simp_all add: def_hashmap_size_uint_unit_def)
end

instantiation bool :: hashable_uint
begin
  definition [simp]: "hashcode_uint (b :: bool) = (if b then 1 else 0)"
  definition "def_hashmap_size_uint = (\<lambda>_ :: bool itself. 2)"
  instance by (intro_classes)(simp_all add: def_hashmap_size_uint_bool_def)
end

instantiation "int" :: hashable_uint
begin
  definition [simp]: "hashcode_uint (i :: int) = uint32_of_int i"
  definition "def_hashmap_size_uint = (\<lambda>_ :: int itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_uint_int_def)
end

instantiation "integer" :: hashable_uint
begin
  definition [simp]: "hashcode_uint (i :: integer) = Uint32 i"
  definition "def_hashmap_size_uint = (\<lambda>_ :: integer itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_uint_integer_def)
end

instantiation integer :: hashable
begin
  definition hashcode_integer :: "integer \<Rightarrow> nat" 
    where "hashcode_integer \<equiv> hashcode_nat"

  definition bounded_hashcode_integer :: "nat \<Rightarrow> integer \<Rightarrow> nat" 
    where "bounded_hashcode_integer = bounded_hashcode_nat"

  definition def_hashmap_size_integer :: "integer itself \<Rightarrow> nat" 
    where "def_hashmap_size_integer \<equiv> def_hashmap_size_uint"

  instance
    apply default
    unfolding def_hashmap_size_integer_def bounded_hashcode_integer_def
    using hashable_from_hashable_uint by auto
end


instantiation "nat" :: hashable_uint
begin
  definition [simp]: "hashcode_uint (n :: nat) = uint32_of_int (int n)"
  definition "def_hashmap_size_uint = (\<lambda>_ :: nat itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_uint_nat_def)
end

instantiation "nibble" :: hashable_uint
begin
  definition [simp]: "hashcode_uint (c :: nibble) = uint32_of_int (int (nat_of_nibble c))"
  definition "def_hashmap_size_uint = (\<lambda>_ :: nibble itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_uint_nibble_def)
end

instantiation char :: hashable_uint
begin
  definition [simp]: "hashcode_uint (c :: char) == uint32_of_int (int (nat_of_char c))"
  definition "def_hashmap_size_uint = (\<lambda>_ :: char itself. 32)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_uint_char_def)
end

instantiation prod :: (hashable_uint, hashable_uint) hashable_uint
begin
  definition "hashcode_uint x == (hashcode_uint (fst x) * 33 + hashcode_uint (snd x))"
  definition "def_hashmap_size_uint = (\<lambda>_ :: ('a \<times> 'b) itself. def_hashmap_size_uint TYPE('a) + def_hashmap_size_uint TYPE('b))"
  instance using def_hashmap_size_uint[where ?'a="'a"] def_hashmap_size_uint[where ?'a="'b"]
    by(intro_classes)(simp_all add: def_hashmap_size_uint_prod_def)
end

instantiation sum :: (hashable_uint, hashable_uint) hashable_uint
begin
  definition "hashcode_uint x == (case x of Inl a \<Rightarrow> 2 * hashcode_uint a | Inr b \<Rightarrow> 2 * hashcode_uint b + 1)"
  definition "def_hashmap_size_uint = (\<lambda>_ :: ('a + 'b) itself. def_hashmap_size_uint TYPE('a) + def_hashmap_size_uint TYPE('b))"
  instance using def_hashmap_size_uint[where ?'a="'a"] def_hashmap_size_uint[where ?'a="'b"]
    by(intro_classes)(simp_all add:  def_hashmap_size_uint_sum_def split: sum.split)
end

instantiation list :: (hashable_uint) hashable_uint
begin
  definition "hashcode_uint = foldl (\<lambda>h x. h * 33 + hashcode_uint x) 5381"
  definition "def_hashmap_size_uint = (\<lambda>_ :: 'a list itself. 2 * def_hashmap_size_uint TYPE('a))"
  instance
  proof
    from def_hashmap_size_uint[where ?'a = "'a"]
    show "1 < def_hashmap_size_uint TYPE('a list)"
      by(simp add: def_hashmap_size_uint_list_def)
  qed
end

instantiation option :: (hashable_uint) hashable_uint
begin
  definition "hashcode_uint opt = (case opt of None \<Rightarrow> 0 | Some a \<Rightarrow> hashcode_uint a + 1)"
  definition "def_hashmap_size_uint = (\<lambda>_ :: 'a option itself. def_hashmap_size_uint TYPE('a) + 1)"
  instance using def_hashmap_size_uint[where ?'a = "'a"]
    by(intro_classes)(simp_all add: def_hashmap_size_uint_option_def split: option.split)
end

end

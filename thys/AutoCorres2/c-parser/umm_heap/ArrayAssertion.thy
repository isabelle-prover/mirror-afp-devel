(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* License: BSD, terms see file ./LICENSE *)

theory ArrayAssertion

imports
  "ArchArraysMemInstance"
  "StructSupport"

begin


lemma array_tag_n_eq:
  "(array_tag_n n :: ('a :: c_type['b :: finite]) xtyp_info) =
  TypDesc (align_td (typ_uinfo_t TYPE('a))) (TypAggregate
    (map (\<lambda>n. DTuple (adjust_ti (typ_info_t TYPE('a)) (\<lambda>x. index x n)
            (\<lambda>x f. Arrays.update f n x)) (replicate n CHR ''1'')
            \<lparr>field_access = xto_bytes \<circ> (\<lambda>x. index x n), 
             field_update = (\<lambda>x f. Arrays.update f n x) \<circ> xfrom_bytes,
             field_sz = size_of TYPE('a::c_type)\<rparr>) [0..<n]))
  (typ_name (typ_uinfo_t TYPE('a)) @ ''_array_'' @ nat_to_bin_string (card (UNIV :: 'b :: finite set)))"
  apply (induct n)
   apply (simp add: typ_info_array array_tag_def eval_nat_numeral 
     array_tag_n.simps empty_typ_info_def align_of_def align_td_uinfo)
   apply (simp add: typ_info_array array_tag_def eval_nat_numeral array_tag_n.simps empty_typ_info_def)
   apply (simp add: ti_typ_combine_def Let_def comp_def align_td_uinfo)
   done

lemma typ_info_array':
  "typ_info_t TYPE ('a :: c_type['b :: finite]) =
  TypDesc (align_td (typ_uinfo_t TYPE('a))) (TypAggregate
    (map (\<lambda>n. DTuple (adjust_ti (typ_info_t TYPE('a)) (\<lambda>x. index x n)
            (\<lambda>x f. Arrays.update f n x)) (replicate n CHR ''1'')
             \<lparr>field_access = xto_bytes \<circ> (\<lambda>x. index x n), 
             field_update = (\<lambda>x f. Arrays.update f n x) \<circ> xfrom_bytes,
             field_sz = size_of TYPE('a::c_type)\<rparr>) [0..<(card (UNIV :: 'b :: finite set))]))
  (typ_name (typ_uinfo_t TYPE('a)) @ ''_array_'' @ nat_to_bin_string (card (UNIV :: 'b :: finite set)))"
  by (simp add: typ_info_array array_tag_def array_tag_n_eq)

definition
  "uinfo_array_tag_n_m (v :: 'a itself) n m = TypDesc
    (align_td (typ_uinfo_t TYPE('a)))
    (TypAggregate (map (\<lambda>i. DTuple (typ_uinfo_t TYPE('a)) (replicate i CHR ''1'') ()) [0 ..< n]))
    (typ_name (typ_uinfo_t TYPE('a :: c_type)) @ ''_array_'' @ nat_to_bin_string m)"

lemma map_td_list_map:
  "map_td_list f g = map (map_td_tuple f g)"
  apply (rule ext)
  subgoal for x by (induct x) simp_all
  done


lemma uinfo_array_tag_n_m_eq:
  "n \<le> CARD('b)
    \<Longrightarrow> export_uinfo (array_tag_n n :: (('a :: wf_type)['b :: finite]) xtyp_info)
        = uinfo_array_tag_n_m TYPE ('a) n (CARD('b))"
  apply (clarsimp simp: uinfo_array_tag_n_m_def array_tag_n_eq map_td_list_map
                        o_def adjust_ti_def map_td_map typ_uinfo_t_def export_uinfo_def)
  apply (fastforce intro: map_td_extI simp: field_norm_blah)
  done

lemma typ_uinfo_array_tag_n_m_eq:
  "typ_uinfo_t TYPE (('a :: wf_type)['b :: finite])
        = uinfo_array_tag_n_m TYPE ('a) (CARD('b)) (CARD('b))"
  by (simp add: typ_uinfo_t_def typ_info_array array_tag_def uinfo_array_tag_n_m_eq)

text \<open>Alternative to \<^const>\<open>h_t_valid\<close> for arrays. This allows reasoning
about arrays of variable width.\<close>
definition h_t_array_valid :: "heap_typ_desc \<Rightarrow> ('a :: c_type) ptr \<Rightarrow> nat \<Rightarrow> bool" where
  "h_t_array_valid htd ptr n = valid_footprint htd (ptr_val ptr) (uinfo_array_tag_n_m TYPE ('a) n n)"

text \<open>Assertion that pointer p is within an array that continues for at least n more elements.\<close>
definition
  "array_assertion (p :: ('a :: c_type) ptr) n htd
    = (\<exists>q i j. h_t_array_valid htd q j
        \<and> p = CTypesDefs.ptr_add q (int i) \<and> i < j \<and> i + n \<le> j)"

lemma array_assertion_shrink_right:
  "array_assertion p n htd \<Longrightarrow> n' \<le> n \<Longrightarrow> array_assertion p n' htd"
  by (fastforce simp: array_assertion_def)

lemma array_assertion_shrink_leftD:
  "array_assertion p n htd \<Longrightarrow> j < n \<Longrightarrow> array_assertion (CTypesDefs.ptr_add p (int j)) (n - j) htd"
  apply (clarsimp simp: array_assertion_def)
  subgoal for q i
    apply (rule exI, rule exI[where x="i + j"], rule exI, erule conjI)
    apply (simp add: CTypesDefs.ptr_add_def field_simps)
    done
  done

lemma array_assertion_shrink_leftI:
  "array_assertion (CTypesDefs.ptr_add p (- (int j))) (n + j) htd
    \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> array_assertion p n htd"
  apply (drule_tac j=j in array_assertion_shrink_leftD, simp)
  apply (simp add: CTypesDefs.ptr_add_def)
  done

lemma h_t_array_valid:
  "h_t_valid htd gd (p :: (('a :: wf_type)['b :: finite]) ptr)
    \<Longrightarrow> h_t_array_valid htd (ptr_coerce p :: 'a ptr) (CARD('b))"
  by (clarsimp simp: h_t_valid_def h_t_array_valid_def typ_uinfo_array_tag_n_m_eq)

lemma array_ptr_valid_array_assertionD:
  "h_t_valid htd gd (p :: (('a :: wf_type)['b :: finite]) ptr)
    \<Longrightarrow> array_assertion (ptr_coerce p :: 'a ptr) (CARD('b)) htd"
  apply (clarsimp simp: array_assertion_def dest!: h_t_array_valid)
  apply (fastforce intro: exI[where x=0])
  done

lemma array_ptr_valid_array_assertionI:
  "h_t_valid htd gd (q :: (('a :: wf_type)['b :: finite]) ptr)
    \<Longrightarrow> q = ptr_coerce p
    \<Longrightarrow> n \<le> CARD('b)
    \<Longrightarrow> array_assertion (p :: 'a ptr) n htd"
  by (auto dest: array_ptr_valid_array_assertionD
           simp: array_assertion_shrink_right)

text \<open>Derived from \<^const>\<open>array_assertion\<close>, an appropriate assertion for performing
a pointer addition, or for dereferencing a pointer addition (the strong case).

In either case, there must be an array connecting the two ends of the pointer
transition, with the caveat that the last address can be just out of the array
if the pointer is not dereferenced, thus the strong/weak distinction.

If the pointer doesn't actually move, nothing is learned.
\<close>
definition ptr_add_assertion :: "('a :: c_type) ptr \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> heap_typ_desc \<Rightarrow> bool" where
  "ptr_add_assertion ptr offs strong htd \<equiv>
    offs = 0 \<or>
    array_assertion (if offs < 0 then CTypesDefs.ptr_add ptr offs else ptr)
                    (if offs < 0 then nat (- offs) else if strong then Suc (nat offs) else nat offs)
                    htd"

lemma ptr_add_assertion_positive:
  "offs \<ge> 0 \<Longrightarrow> ptr_add_assertion ptr offs strong htd
    = (offs = 0 \<or> array_assertion ptr (case strong of True \<Rightarrow> Suc (nat offs)
        | False \<Rightarrow> nat offs) htd)"
  by (simp add: ptr_add_assertion_def)

lemma ptr_add_assertion_negative:
  "offs < 0 \<Longrightarrow> ptr_add_assertion ptr offs strong htd
    = array_assertion (CTypesDefs.ptr_add ptr offs) (nat (- offs)) htd"
  by (simp add: ptr_add_assertion_def)

lemma ptr_add_assertion_uint[simp]:
  "ptr_add_assertion ptr (uint offs) strong htd
    = (offs = 0 \<or> array_assertion ptr
        (case strong of True \<Rightarrow> Suc (unat offs) | False \<Rightarrow> unat offs) htd)"
  by (simp add: ptr_add_assertion_positive uint_0_iff 
         split: bool.split)

text \<open>Ignore char and void pointers. The C standard specifies that arithmetic on
char and void pointers doesn't create any special checks.\<close>

definition ptr_add_assertion' :: "('a :: c_type) ptr \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> heap_typ_desc \<Rightarrow> bool" where
  "ptr_add_assertion' ptr offs strong htd =
     (typ_uinfo_t TYPE('a) = typ_uinfo_t TYPE(word8)
      \<or> typ_uinfo_t TYPE ('a) = typ_uinfo_t TYPE(unit)
      \<or> ptr_add_assertion ptr offs strong htd)"

(* Useful for clearing away these assumptions. *)
lemma td_diff_from_typ_name:
  "typ_name td \<noteq> typ_name td' \<Longrightarrow> td \<noteq> td'"
  by clarsimp

lemma typ_name_void:
  "typ_name (typ_uinfo_t TYPE(unit)) = ''unit''"
 by (simp add: typ_uinfo_t_def)

lemmas ptr_add_assertion' = ptr_add_assertion'_def td_diff_from_typ_name typ_name_void

text \<open>Mechanism for retyping a range of memory to a non-constant array size.\<close>

definition ptr_arr_retyps :: "nat \<Rightarrow> ('a :: c_type) ptr \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc" where
  "ptr_arr_retyps n p \<equiv>
    htd_update_list (ptr_val p)
        (map (\<lambda>i. list_map (typ_slice_t (uinfo_array_tag_n_m TYPE('a) n n) i))
             [0..<n * size_of TYPE('a)])"

lemma ptr_arr_retyps_to_retyp:
  "n = CARD('b :: finite)
    \<Longrightarrow> ptr_arr_retyps n (p :: ('c :: wf_type) ptr) = ptr_retyp (ptr_coerce p :: ('c['b]) ptr)"
  by (auto simp: ptr_arr_retyps_def ptr_retyp_def typ_slices_def typ_uinfo_array_tag_n_m_eq)

definition
  array_ptr_index :: "(('a :: c_type)['b :: finite]) ptr \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> 'a ptr"
where
  "array_ptr_index p coerce n = CTypesDefs.ptr_add (ptr_coerce p)
    (if coerce \<and> n \<ge> CARD ('b) then 0 else of_nat n)"


lemmas array_ptr_index_simps
    = array_ptr_index_def[where coerce=False, simplified]
        array_ptr_index_def[where coerce=True, simplified]

lemma field_lookup_list_Some_again:
  "dt_snd (xs ! i) = f
    \<Longrightarrow> i < length xs
    \<Longrightarrow> f \<notin> dt_snd ` set ((take i xs))
    \<Longrightarrow> field_lookup_list xs [f] n
        = Some (dt_fst (xs ! i), n + sum_list (map (size_td o dt_fst) (take i xs)))"
  apply (induct xs arbitrary: i n, simp_all)
  subgoal for x1 xs i
    apply (cases x1, simp)
    apply (cases i, auto split: if_split)
    done
  done

lemma field_lookup_array:
  "n < CARD('b) \<Longrightarrow> field_lookup (typ_info_t TYPE(('a :: c_type)['b :: finite]))
    [replicate n (CHR ''1'')] i = Some (adjust_ti (typ_info_t TYPE('a))
        (\<lambda>x. x.[n]) (\<lambda>x f. Arrays.update f n x), i + n * size_of TYPE ('a))"
  apply (simp add: typ_info_array array_tag_def array_tag_n_eq)
  apply (subst field_lookup_list_Some_again[where i=n],
    auto simp add: take_map o_def sum_list_triv size_of_def)
  done

lemma field_ti_array:
  "n < CARD('b) \<Longrightarrow> 
   field_ti (TYPE(('a :: c_type)['b :: finite])) [replicate n (CHR ''1'')]  = 
     Some (adjust_ti (typ_info_t TYPE('a)) (\<lambda>x. x.[n]) (\<lambda>x f. Arrays.update f n x))"
  by (simp add: field_ti_def field_lookup_array)

lemma fg_cons_array [simp]:
  "n < card (UNIV :: 'b :: finite set) \<Longrightarrow>
   fg_cons (\<lambda>x. index x n) (\<lambda>x f. Arrays.update (f :: 'a['b]) n x)"
  unfolding fg_cons_def by simp


lemma ptr_val_array_field_lvalue_0:
  fixes p:: "(('a :: c_type)['b :: finite]) ptr"
  shows "&(p\<rightarrow>[[]]) = ptr_val p"
proof -
  note fl =  field_lookup_array [where n=0 and i=0 and 'a='a and 'b='b, simplified]
  note fl_exp = field_lookup_export_uinfo_Some [OF fl]
  show ?thesis
    unfolding field_lvalue_def field_offset_def field_offset_untyped_def typ_uinfo_t_def
    apply (subst fl_exp)
    apply simp
    done
qed

end


theory Ailamazyan_Code
  imports "HOL-Library.Code_Target_Nat" "Containers.Containers" Ailamazyan
begin

(* Convert database to fo_intp *)

definition insert_db :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b set) mapping \<Rightarrow> ('a, 'b set) mapping" where
  "insert_db k v m = (case Mapping.lookup m k of None \<Rightarrow>
    Mapping.update k ({v}) m
  | Some vs \<Rightarrow> Mapping.update k (({v} \<union> vs)) m)"

fun convert_db_rec :: "('a \<times> 'c list) list \<Rightarrow> (('a \<times> nat), 'c list set) mapping \<Rightarrow>
  (('a \<times> nat), 'c list set) mapping" where
  "convert_db_rec [] m = m"
| "convert_db_rec ((r, ts) # ktss) m = convert_db_rec ktss (insert_db (r, length ts) ts m)"

lemma convert_db_rec_mono: "Mapping.lookup m (r, n) = Some tss \<Longrightarrow>
  \<exists>tss'. Mapping.lookup (convert_db_rec ktss m) (r, n) = Some tss' \<and> tss \<subseteq> tss'"
  apply (induction ktss m arbitrary: tss rule: convert_db_rec.induct)
   apply (auto simp: insert_db_def fun_upd_def Mapping.lookup_update' split: option.splits if_splits)
   apply (metis option.discI)
  apply (smt option.inject order_trans subset_insertI)
  done

lemma convert_db_rec_sound: "(r, ts) \<in> set ktss \<Longrightarrow>
  \<exists>tss. Mapping.lookup (convert_db_rec ktss m) (r, length ts) = Some tss \<and> ts \<in> tss"
proof (induction ktss m rule: convert_db_rec.induct)
  case (2 r ts ktss m)
  obtain tss where
    "Mapping.lookup (convert_db_rec ktss (insert_db (r, length ts) ts m)) (r, length ts) = Some tss"
    "ts \<in> tss"
    using convert_db_rec_mono[of "insert_db (r, length ts) ts m" r "length ts" _ ktss]
    by atomize_elim (auto simp: insert_db_def Mapping.lookup_update' split: option.splits)+
  then show ?case
    using 2
    by auto
qed auto

lemma convert_db_rec_complete: "Mapping.lookup (convert_db_rec ktss m) (r, n) = Some tss' \<Longrightarrow>
  ts \<in> tss' \<Longrightarrow>
  (length ts = n \<and> (r, ts) \<in> set ktss) \<or> (\<exists>tss. Mapping.lookup m (r, n) = Some tss \<and> ts \<in> tss)"
  by (induction ktss m rule: convert_db_rec.induct)
     (auto simp: insert_db_def Mapping.lookup_update' split: option.splits if_splits)

definition convert_db :: "('a \<times> 'c list) list \<Rightarrow> ('c table, 'a) fo_intp" where
  "convert_db ktss = (let m = convert_db_rec ktss Mapping.empty in
    (\<lambda>x. case Mapping.lookup m x of None \<Rightarrow> {} | Some v \<Rightarrow> v))"

lemma convert_db_correct: "(ts \<in> convert_db ktss (r, n) \<longrightarrow> n = length ts) \<and>
  ((r, ts) \<in> set ktss \<longleftrightarrow> ts \<in> convert_db ktss (r, length ts))"
  by (auto simp: convert_db_def dest!: convert_db_rec_sound[of _ _ _ Mapping.empty]
      split: option.splits)
     (metis Mapping.lookup_empty convert_db_rec_complete option.distinct(1))+

(* Code setup *)

lemma Inl_vimage_set_code[code_unfold]: "Inl -` set as = set (List.map_filter (case_sum Some Map.empty) as)"
  by (induction as) (auto simp: List.map_filter_simps split: option.splits sum.splits)

lemma Inr_vimage_set_code[code_unfold]: "Inr -` set as = set (List.map_filter (case_sum Map.empty Some) as)"
  by (induction as) (auto simp: List.map_filter_simps split: option.splits sum.splits)

lemma Inl_vimage_code: "Inl -` as = projl ` {x \<in> as. isl x}"
  by (force simp: vimage_def)

lemmas ad_pred_code[code] = ad_terms.simps[unfolded Inl_vimage_code]
lemmas fo_wf_code[code] = fo_wf.simps[unfolded Inl_vimage_code]

(* Monomorphise *)

definition empty_J :: "((nat, nat) fo_t, String.literal) fo_intp" where
  "empty_J = (\<lambda>(_, n). eval_pred (map Var [0..<n]) {})"

definition eval_fin_nat :: "(nat, String.literal) fo_fmla \<Rightarrow> (nat table, String.literal) fo_intp \<Rightarrow> nat eval_res" where
  "eval_fin_nat \<phi> I = eval \<phi> I"

definition sat_fin_nat :: "(nat, String.literal) fo_fmla \<Rightarrow> (nat table, String.literal) fo_intp \<Rightarrow> nat val \<Rightarrow> bool" where
  "sat_fin_nat \<phi> I = sat \<phi> I"

definition convert_nat_db :: "(String.literal \<times> nat list) list \<Rightarrow>
  (nat table, String.literal) fo_intp" where
  "convert_nat_db = convert_db"

definition rbt_nat_fold :: "_ \<Rightarrow> nat set_rbt \<Rightarrow> _ \<Rightarrow> _" where
  "rbt_nat_fold = RBT_Set2.fold"

definition rbt_nat_list_fold :: "_ \<Rightarrow> (nat list) set_rbt \<Rightarrow> _ \<Rightarrow> _" where
  "rbt_nat_list_fold = RBT_Set2.fold"

definition rbt_sum_list_fold :: "_ \<Rightarrow> ((nat + nat) list) set_rbt \<Rightarrow> _ \<Rightarrow> _" where
  "rbt_sum_list_fold = RBT_Set2.fold"

export_code eval_fin_nat sat_fin_nat fv_fo_fmla_list convert_nat_db rbt_nat_fold rbt_nat_list_fold
  rbt_sum_list_fold Const Conj Inl Fin nat_of_integer integer_of_nat RBT_set
  in OCaml module_name Eval_FO file_prefix verified

(* Examples *)

definition \<phi> :: "(nat, String.literal) fo_fmla" where
  "\<phi> \<equiv> Exists 0 (Conj (FO.Eqa (Var 0) (Const 2)) (FO.Eqa (Var 0) (Var 1)))"

value "eval_fin_nat \<phi> (convert_nat_db [])"

value "sat_fin_nat \<phi> (convert_nat_db []) (\<lambda>_. 0)"
value "sat_fin_nat \<phi> (convert_nat_db []) (\<lambda>_. 2)"

definition \<psi> :: "(nat, String.literal) fo_fmla" where
  "\<psi> \<equiv> Forall 2 (Disj (FO.Eqa (Var 2) (Const 42))
       (Exists 1 (Conj (FO.Pred (String.implode ''P'') [Var 0, Var 1])
                 (Neg (FO.Pred (String.implode ''Q'') [Var 1, Var 2])))))"

value "eval_fin_nat \<psi> (convert_nat_db
   [(String.implode ''P'', [1, 20]),
    (String.implode ''P'', [9, 20]),
    (String.implode ''P'', [2, 30]),
    (String.implode ''P'', [3, 31]),
    (String.implode ''P'', [4, 32]),
    (String.implode ''P'', [5, 30]),
    (String.implode ''P'', [6, 30]),
    (String.implode ''P'', [7, 30]),
    (String.implode ''Q'', [20, 42]),
    (String.implode ''Q'', [30, 43])])"

end

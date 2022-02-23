theory Monitor_Code
  imports "HOL-Library.Code_Target_Nat" "Containers.Containers" Monitor Preliminaries
begin

derive (eq) ceq enat

instantiation enat :: ccompare begin

definition ccompare_enat :: "enat comparator option" where
  "ccompare_enat = Some (\<lambda>x y. if x = y then order.Eq else if x < y then order.Lt else order.Gt)"

instance by intro_classes
    (auto simp: ccompare_enat_def split: if_splits intro!: comparator.intro)

end

code_printing
  code_module "IArray" \<rightharpoonup> (OCaml)
\<open>module IArray : sig
  val length' : 'a array -> Z.t
  val sub' : 'a array * Z.t -> 'a
end = struct

let length' xs = Z.of_int (Array.length xs);;

let sub' (xs, i) = Array.get xs (Z.to_int i);;

end\<close> for type_constructor iarray constant IArray.length' IArray.sub'

code_reserved OCaml IArray

code_printing
  type_constructor iarray \<rightharpoonup> (OCaml) "_ array"
| constant iarray_of_list \<rightharpoonup> (OCaml) "Array.of'_list"
| constant IArray.list_of \<rightharpoonup> (OCaml) "Array.to'_list"
| constant IArray.length' \<rightharpoonup> (OCaml) "IArray.length'"
| constant IArray.sub' \<rightharpoonup> (OCaml) "IArray.sub'"

lemma iarray_list_of_inj: "IArray.list_of xs = IArray.list_of ys \<Longrightarrow> xs = ys"
  by (cases xs; cases ys) auto

instantiation iarray :: (ccompare) ccompare
begin

definition ccompare_iarray :: "('a iarray \<Rightarrow> 'a iarray \<Rightarrow> order) option" where
  "ccompare_iarray = (case ID CCOMPARE('a list) of None \<Rightarrow> None
  | Some c \<Rightarrow> Some (\<lambda>xs ys. c (IArray.list_of xs) (IArray.list_of ys)))"

instance
  apply standard
  apply unfold_locales
  using comparator.sym[OF ID_ccompare'] comparator.weak_eq[OF ID_ccompare']
    comparator.comp_trans[OF ID_ccompare'] iarray_list_of_inj
    apply (auto simp: ccompare_iarray_def split: option.splits)
   apply blast+
  done

end

derive (rbt) mapping_impl iarray

definition mk_db :: "String.literal list \<Rightarrow> String.literal set" where "mk_db = set"

definition init_vydra_string_enat :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (String.literal, enat, 'e) vydra" where
  "init_vydra_string_enat = init_vydra"
definition run_vydra_string_enat :: " _  \<Rightarrow> (String.literal, enat, 'e) vydra \<Rightarrow> _" where
  "run_vydra_string_enat = run_vydra"
definition progress_enat :: "(String.literal, enat) formula \<Rightarrow> enat list \<Rightarrow> nat" where
  "progress_enat = progress"
definition bounded_future_fmla_enat :: "(String.literal, enat) formula \<Rightarrow> bool" where
  "bounded_future_fmla_enat = bounded_future_fmla"
definition wf_fmla_enat :: "(String.literal, enat) formula \<Rightarrow> bool" where
  "wf_fmla_enat = wf_fmla"
definition mdl2mdl'_enat :: "(String.literal, enat) formula \<Rightarrow> (String.literal, enat) Preliminaries.formula" where
  "mdl2mdl'_enat = mdl2mdl'"
definition interval_enat :: "enat \<Rightarrow> enat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> enat \<I>" where
  "interval_enat = interval"
definition rep_interval_enat :: "enat \<I> \<Rightarrow> enat \<times> enat \<times> bool \<times> bool" where
  "rep_interval_enat = Rep_\<I>"

definition init_vydra_string_ereal :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (String.literal, ereal, 'e) vydra" where
  "init_vydra_string_ereal = init_vydra"
definition run_vydra_string_ereal :: " _  \<Rightarrow> (String.literal, ereal, 'e) vydra \<Rightarrow> _" where
  "run_vydra_string_ereal = run_vydra"
definition progress_ereal :: "(String.literal, ereal) formula \<Rightarrow> ereal list \<Rightarrow> real" where
  "progress_ereal = progress"
definition bounded_future_fmla_ereal :: "(String.literal, ereal) formula \<Rightarrow> bool" where
  "bounded_future_fmla_ereal = bounded_future_fmla"
definition wf_fmla_ereal :: "(String.literal, ereal) formula \<Rightarrow> bool" where
  "wf_fmla_ereal = wf_fmla"
definition mdl2mdl'_ereal :: "(String.literal, ereal) formula \<Rightarrow> (String.literal, ereal) Preliminaries.formula" where
  "mdl2mdl'_ereal = mdl2mdl'"
definition interval_ereal :: "ereal \<Rightarrow> ereal \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ereal \<I>" where
  "interval_ereal = interval"
definition rep_interval_ereal :: "ereal \<I> \<Rightarrow> ereal \<times> ereal \<times> bool \<times> bool" where
  "rep_interval_ereal = Rep_\<I>"

lemma tfin_enat_code[code]: "(tfin :: enat set) = Collect_set (\<lambda>x. x \<noteq> \<infinity>)"
  by (auto simp: tfin_enat_def)

lemma tfin_ereal_code[code]: "(tfin :: ereal set) = Collect_set (\<lambda>x. x \<noteq> -\<infinity> \<and> x \<noteq> \<infinity>)"
  by (auto simp: tfin_ereal_def)

lemma Ball_atms[code_unfold]: "Ball (atms r) P = list_all P (collect_subfmlas r [])"
  using collect_subfmlas_atms[where ?phis="[]"]
  by (auto simp: list_all_def)

lemma MIN_fold: "(MIN x\<in>set (z # zs). f x) = fold min (map f zs) (f z)"
  by (metis Min.set_eq_fold list.set_map list.simps(9))

declare progress.simps(1-8)[code]

lemma progress_matchP_code[code]:
  "progress (MatchP I r) ts = (case collect_subfmlas r [] of x # xs \<Rightarrow> fold min (map (\<lambda>f. progress f ts) xs) (progress x ts))"
  using collect_subfmlas_atms[where ?r=r and ?phis="[]"] atms_nonempty[of r]
  by (auto split: list.splits) (smt (z3) MIN_fold[where ?f="\<lambda>f. progress f ts"] list.simps(15))

lemma progress_matchF_code[code]:
  "progress (MatchF I r) ts = (if length ts = 0 then 0 else
  (let k = min (length ts - 1) (case collect_subfmlas r [] of x # xs \<Rightarrow> fold min (map (\<lambda>f. progress f ts) xs) (progress x ts)) in
   Min {j \<in> {..k}. memR (ts ! j) (ts ! k) I}))"
  by (auto simp: progress_matchP_code[unfolded progress.simps])

export_code init_vydra_string_enat run_vydra_string_enat progress_enat bounded_future_fmla_enat wf_fmla_enat mdl2mdl'_enat
  Bool Preliminaries.Bool enat interval_enat rep_interval_enat nat_of_integer integer_of_nat mk_db
  in OCaml module_name VYDRA file_prefix "verified"

end

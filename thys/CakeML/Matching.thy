chapter "Matching adaptation"

theory Matching
imports Semantic_Extras
begin

context begin

qualified fun fold2 where
"fold2 f err [] [] init = init" |
"fold2 f err (x # xs) (y # ys) init = f init x y (fold2 f err xs ys)" |
"fold2 _ err _  _ _ = err"

qualified lemma fold2_cong[fundef_cong]:
  assumes "init1 = init2" "err1 = err2" "xs1 = xs2" "ys1 = ys2"
  assumes "\<And>acc x y. x \<in> set xs1 \<Longrightarrow> y \<in> set ys1 \<Longrightarrow> f acc x y = g acc x y"
  shows "fold2 f err1 xs1 ys1 init1 = fold2 g err2 xs2 ys2 init2"
using assms
apply (induction f err1 xs1 ys1 init1 arbitrary: init2 xs2 ys2 rule: fold2.induct)
apply auto
apply presburger
done

fun pmatch_single :: "((string),(string),(nat*tid_or_exn))namespace \<Rightarrow>((v)store_v)list \<Rightarrow> pat \<Rightarrow> v \<Rightarrow>(string*v)list \<Rightarrow>((string*v)list)match_result " where
"pmatch_single envC s Pany v' env = ( Match env )" |
"pmatch_single envC s (Pvar x) v' env = ( Match ((x,v')# env))" |
"pmatch_single envC s (Plit l) (Litv l') env = (
  if l = l' then
    Match env
  else if lit_same_type l l' then
    No_match
  else
    Match_type_error )" |
"pmatch_single envC s (Pcon (Some n) ps) (Conv (Some (n', t')) vs) env =
  (case  nsLookup envC n of
      Some (l, t1) =>
        if same_tid t1 t' \<and> (List.length ps = l) then
          if same_ctor (id_to_n n, t1) (n',t') then
            fold2 (\<lambda>m p v f. case m of
               Match env \<Rightarrow> (case pmatch_single envC s p v env of
                  Match env' \<Rightarrow> f (Match env')
                | m \<Rightarrow> m)
            | m \<Rightarrow> m) Match_type_error ps vs (Match env)
          else
            No_match
        else
          Match_type_error
    | _ => Match_type_error
  )" |
"pmatch_single envC s (Pcon None ps) (Conv None vs) env = (
  if List.length ps = List.length vs then
    fold2 (\<lambda>m p v f. case m of
       Match env \<Rightarrow> (case pmatch_single envC s p v env of
          Match env' \<Rightarrow> f (Match env')
        | m \<Rightarrow> m)
    | m \<Rightarrow> m) Match_type_error ps vs (Match env)
  else
    Match_type_error )" |
"pmatch_single envC s (Pref p) (Loc lnum) env =
  (case  store_lookup lnum s of
      Some (Refv v2) => pmatch_single envC s p v2 env
    | Some _ => Match_type_error
    | None => Match_type_error
  )" |
"pmatch_single envC s (Ptannot p t1) v2 env = pmatch_single envC s p v2 env" |
"pmatch_single envC _ _ _ env = Match_type_error"

private lemma pmatch_single_eq0:
  "pmatch_list cenv s ps vs env = fold2 (\<lambda>m p v f. case m of
               Match env \<Rightarrow> (case pmatch_single cenv s p v env of
                  Match env' \<Rightarrow> f (Match env')
                | m \<Rightarrow> m)
            | m \<Rightarrow> m) Match_type_error ps vs (Match env)"
  "pmatch cenv s p v0 env = pmatch_single cenv s p v0 env"
by (induction rule: pmatch_list_pmatch.induct)
   (auto split: option.splits match_result.splits store_v.splits)

lemma pmatch_single_equiv: "pmatch = pmatch_single"
by (rule ext)+ (simp add: pmatch_single_eq0)

end

export_code pmatch_single checking SML

end
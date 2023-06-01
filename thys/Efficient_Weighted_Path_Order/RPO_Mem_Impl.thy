section \<open>A Memoized Implementation of RPO\<close>

text \<open>We derive a memoized RPO implementation from the memoized WPO implementation\<close>

theory RPO_Mem_Impl
  imports
    RPO_Unbounded
    WPO_Mem_Impl
begin

definition rpo_mem :: "('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool) \<times> ('f \<times> nat \<Rightarrow> bool) 
  \<Rightarrow> ('f \<times> nat \<Rightarrow> order_tag) \<Rightarrow> _" where
  [code del]: "rpo_mem pr c mem st = 
  wpo_mem (fst pr) (snd pr) False (\<lambda> _. False) (\<lambda> _ _. False) (\<lambda> _ _. True) full_status c mem st" 

definition rpo_main :: "('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool) \<times> ('f \<times> nat \<Rightarrow> bool) 
  \<Rightarrow> ('f \<times> nat \<Rightarrow> order_tag) \<Rightarrow> _" where
  [code del]: "rpo_main pr c mem st = 
  wpo_main (fst pr) (snd pr) False (\<lambda> _. False) (\<lambda> _ _. False) (\<lambda> _ _. True) full_status c mem st"

lemma rpo_mem_code[code]: "rpo_mem pr c mem (s,t) =
      (let
        i = index s;
        j = index t
      in
        (case Mapping.lookup mem (i,j) of
          Some res \<Rightarrow> (res, mem)
        | None \<Rightarrow> case rpo_main pr c mem (s,t)  
     of (res, mem_new) \<Rightarrow> (res, Mapping.update (i,j) res mem_new)))"
  unfolding rpo_mem_def rpo_main_def wpo_mem.simps ..

lemma rpo_main_code[code]: "rpo_main pr c mem (s,t) = (case s of
      Var x \<Rightarrow> ((False,
        (case t of
          Var y \<Rightarrow> name_of x = name_of y
        | Fun g ts \<Rightarrow> ts = [] \<and> snd pr (name_of g, 0))), mem)
    | Fun f ss \<Rightarrow>
        let ff = (name_of f, length ss) in
          (case exists_mem (\<lambda> s'. (s',t)) (rpo_mem pr c) snd mem ss of
         (sub_result, mem_out_1) \<Rightarrow>
            if sub_result then ((True, True), mem_out_1)
            else
              (case t of
                Var _ \<Rightarrow> ((False, False), mem_out_1)
              | Fun g ts \<Rightarrow>
                let gg = (name_of g, length ts) in
                (case fst pr ff gg of (prs, prns) \<Rightarrow>
                  if prns then 
                  (case forall_mem (\<lambda> t'. (s,t')) (rpo_mem pr c) fst mem_out_1 ts of
                    (sub_result, mem_out_2) \<Rightarrow>
                    if sub_result then
                      if prs then ((True, True), mem_out_2)
                      else 
                        let cf = c ff; cg = c gg in
                         if cf = Lex \<and> cg = Lex then lex_ext_unbounded_mem (rpo_mem pr c) mem_out_2 ss ts
                         else if cf = Mul \<and> cg = Mul then mul_ext_mem (rpo_mem pr c) mem_out_2 ss ts
                         else if ts = [] then ((ss \<noteq> [], True), mem_out_2)
                         else ((False, False), mem_out_2)
                    else ((False, False), mem_out_2)) else ((False,False), mem_out_1))
                  )
            )
        )" 
  unfolding rpo_main_def rpo_mem_def wpo_main.simps Let_def if_False if_True
  unfolding rpo_main_def[symmetric] rpo_mem_def[symmetric]
  by (cases s; cases t, auto simp: map_nth split: prod.splits)

declare [[code drop: rpo_unbounded]]

lemma rpo_unbounded_memoized_code[code]: "rpo_unbounded pr c s t = fst (rpo_mem pr c Mapping.empty (index_term s, index_term t))" 
  unfolding rpo_mem_def wpo_mem_impl_def[symmetric] wpo_ub_memoized_code[symmetric]
proof (induct pr c s t rule: rpo_unbounded.induct)
  case (1 pr c x y)
  then show ?case unfolding rpo_unbounded.simps wpo_ub.simps[of _ _ _ _ _ _ _ _ "Var x" "Var y"]
    by simp
next
  case (2 pr c x g ts)
  then show ?case unfolding rpo_unbounded.simps wpo_ub.simps[of _ _ _ _ _ _ _ _ "Var x" "Fun g ts"] term.simps
    by auto
next
  case (3 pr c f ss y)
  then show ?case unfolding rpo_unbounded.simps wpo_ub.simps[of _ _ _ _ _ _ _ _ "Fun f ss" "Var y"] term.simps
      Let_def by (auto simp: set_conv_nth)
next
  case (4 pr c f ss g ts)
  obtain prs prns where pr: "fst pr (f, length ss) (g, length ts) = (prs,prns)" by force
  show ?case unfolding rpo_unbounded.simps wpo_ub.simps[of _ _ _ _ _ _ _ _ "Fun f ss" "Fun g ts"] term.simps
      if_False Let_def if_True pr split
  proof (rule sym, intro if_cong[OF _ refl if_cong[OF _ if_cong[OF refl refl] refl]], goal_cases)
    case 1
    show ?case using 4(1) by (auto simp: set_conv_nth)
  next
    case 2
    show ?case using 4(2)[unfolded pr, OF 2 refl] by (auto simp: set_conv_nth)
  next
    case 3
    note IH = 4(3-)[unfolded pr, OF 3(1) refl 3(2-3)]
    let ?cf = "c (f, length ss)" 
    let ?cg = "c (g, length ts)" 
    consider (Lex) "?cf = Lex" "?cg = Lex" | (Mul) "?cf = Mul" "?cg = Mul" | (Diff) "?cf \<noteq> ?cg"
      by (cases ?cf; cases ?cg, auto)
    thus ?case
    proof cases
      case Lex
      hence "?cf = ?cg" and "?cf \<noteq> Mul" by auto
      note IH = IH(2)[OF this]
      from Lex have id: "(?cf = Lex \<and> ?cg = Lex) = True" "(?cf = ?cg) = True" "(?cf = Mul) = False" by auto
      show ?thesis unfolding id if_True if_False using IH
        by (intro lex_ext_unbounded_cong, auto intro: nth_equalityI)
    next
      case Mul
      hence "?cf = ?cg" and "?cf = Mul" by auto
      note IH = IH(1)[OF this]
      from Mul have id: "(?cf = Lex \<and> ?cg = Lex) = False" "(?cf = Mul \<and> ?cg = Mul) = True" 
        "(?cf = ?cg) = True" "(?cf = Mul) = True" by auto
      show ?thesis unfolding id(1-3) if_True if_False unfolding id(4) if_True using IH
        by (intro mul_ext_cong[OF arg_cong[of _ _ mset] arg_cong[of _ _ mset]])
          (auto intro: nth_equalityI)
    qed auto
  qed
qed

end
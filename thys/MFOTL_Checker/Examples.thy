(*<*)
theory Examples
imports Monitor Checker_Code
begin
(*>*)

section \<open>Examples\<close>

definition monitor :: "(('n :: linorder \<times> 'd :: {default, linorder} list) set \<times> nat) list \<Rightarrow> ('n, 'd) formula \<Rightarrow> ('n, 'd) expl list" where
  "monitor \<pi> \<phi> = map (\<lambda>i. eval (trace_of_list \<pi>) (\<lambda>p q. size p \<le> size q) (sorted_list_of_set (fv \<phi>)) i \<phi>) [0 ..< length \<pi>]"
definition check :: "(('n :: linorder \<times> 'd :: {default, linorder} list) set \<times> nat) list \<Rightarrow> ('n, 'd) formula \<Rightarrow> bool" where
  "check \<pi> \<phi> = list_all (check_all (trace_of_list \<pi>) \<phi>) (monitor \<pi> \<phi>)"

subsection \<open>Infinite Domain\<close>

definition prefix :: "((string \<times> string list) set \<times> nat) list" where 
  "prefix =
     [({(''mgr_S'', [''Mallory'', ''Alice'']),
        (''mgr_S'', [''Merlin'', ''Bob'']),
        (''mgr_S'', [''Merlin'', ''Charlie''])}, 1307532861::nat),
      ({(''approve'', [''Mallory'', ''152''])}, 1307532861),
      ({(''approve'', [''Merlin'', ''163'']),
        (''publish'', [''Alice'', ''160'']),
        (''mgr_F'', [''Merlin'', ''Charlie''])}, 1307955600),
      ({(''approve'', [''Merlin'', ''187'']),
        (''publish'', [''Bob'', ''163'']),
        (''publish'', [''Alice'', ''163'']),
        (''publish'', [''Charlie'', ''163'']),
        (''publish'', [''Charlie'', ''152''])}, 1308477599)]"

definition phi :: "(string, string) Formula.formula" where
  "phi = Formula.Imp (Formula.Pred ''publish'' [Formula.Var ''a'', Formula.Var ''f''])
    (Formula.Once (init 604800) (Formula.Exists ''m'' (Formula.Since 
      (Formula.Neg (Formula.Pred ''mgr_F'' [Formula.Var ''m'', Formula.Var ''a''])) all
      (Formula.And (Formula.Pred ''mgr_S'' [Formula.Var ''m'', Formula.Var ''a''])
                 (Formula.Pred ''approve'' [Formula.Var ''m'', Formula.Var ''f''])))))"

value "monitor prefix phi"
lemma "check prefix phi"
  by eval

subsection \<open>Finite Domain\<close>

datatype Domain = Mallory | Merlin | Martin | Alice | Bob | Charlie | David | Default | R42 | R152 | R160 | R163 | R187

definition ord :: "Domain \<Rightarrow> nat" where
  "ord d = (case d of
     Mallory \<Rightarrow> 0
   | Merlin \<Rightarrow> 1
   | Martin \<Rightarrow> 2
   | Alice \<Rightarrow> 3
   | Bob \<Rightarrow> 4
   | Charlie \<Rightarrow> 5
   | David \<Rightarrow> 6
   | Default \<Rightarrow> 7
   | R42 \<Rightarrow> 8
   | R152 \<Rightarrow> 9
   | R160 \<Rightarrow> 10
   | R163 \<Rightarrow> 11
   | R187 \<Rightarrow> 12)"

instantiation Domain :: default begin
definition "default_Domain = Default"
instance ..
end
instantiation Domain :: universe begin
definition "universe_Domain = Some [Mallory, Merlin, Martin, Alice, Bob, Charlie, David, Default, R42, R152, R160, R163, R187]"
instance by standard (auto simp: universe_Domain_def intro: Domain.exhaust)
end
instantiation Domain :: linorder begin
definition "less_eq_Domain d d' = (ord d \<le> ord d')"
definition "less_Domain d d' = (ord d < ord d')"
instance by standard (auto simp: less_eq_Domain_def less_Domain_def ord_def split: Domain.splits)
end

definition fprefix :: "((string \<times> Domain list) set \<times> nat) list" where 
  "fprefix =
     [({(''mgr_S'', [Mallory, Alice]),
        (''mgr_S'', [Merlin, Bob]),
        (''mgr_S'', [Merlin, Charlie])}, 1307532861::nat),
      ({(''approve'', [Mallory, R152])}, 1307532861),
      ({(''approve'', [Merlin, R163]),
        (''publish'', [Alice, R160]),
        (''mgr_F'', [Merlin, Charlie])}, 1307955600),
      ({(''approve'', [Merlin, R187]),
        (''publish'', [Bob, R163]),
        (''publish'', [Alice, R163]),
        (''publish'', [Charlie, R163]),
        (''publish'', [Charlie, R152])}, 1308477599)]"

definition fphi :: "(string, Domain) Formula.formula" where
  "fphi = Formula.Imp (Formula.Pred ''publish'' [Formula.Var ''a'', Formula.Var ''f''])
    (Formula.Once (init 604800) (Formula.Exists ''m'' (Formula.Since 
      (Formula.Neg (Formula.Pred ''mgr_F'' [Formula.Var ''m'', Formula.Var ''a''])) all
      (Formula.And (Formula.Pred ''mgr_S'' [Formula.Var ''m'', Formula.Var ''a''])
                 (Formula.Pred ''approve'' [Formula.Var ''m'', Formula.Var ''f''])))))"

value "monitor fprefix fphi"
lemma "check fprefix fphi"
  by eval

(*<*)
end
(*>*)
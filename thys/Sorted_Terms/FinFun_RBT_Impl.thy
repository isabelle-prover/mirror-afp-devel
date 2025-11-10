(* implement fin-funs via red-black-trees, currently only update, const and apply are supported *)

theory FinFun_RBT_Impl
  imports 
    FinFun.FinFun
    "HOL-Library.RBT"
begin

fun def_option :: "'a \<Rightarrow> 'a option \<Rightarrow> 'a" where
  "def_option d (Some x) = x"
| "def_option d None = d" 

lift_definition ff_of_rbt :: "'b \<times> ('a::linorder, 'b) rbt \<Rightarrow> ('a,'b)finfun" is
  "\<lambda> dt x. def_option (fst dt) (RBT.lookup (snd dt) x)" 
  unfolding finfun_def
proof (standard, goal_cases)
  case (1 dt)
  have "{a. def_option (fst dt) (RBT.lookup (snd dt) a) \<noteq> fst dt} \<subseteq> set (RBT.keys (snd dt))" 
    apply clarsimp
    subgoal for x
      by (cases "RBT.lookup (snd dt) x", auto simp: RBT.keys_entries RBT.lookup_in_tree) 
    done
  from finite_subset[OF this]
  show ?case
    by (intro exI[of _ "fst dt"], auto)
qed

code_datatype ff_of_rbt

declare [[code drop: finfun_const]]
lemma finfun_const_impl[code]: "finfun_const c = ff_of_rbt (c, RBT.empty)" 
  by transfer auto

declare [[code drop: finfun_apply]]
lemma finfun_apply_impl[code]: "finfun_apply (ff_of_rbt (c, t)) x = def_option c (RBT.lookup t x)"
  by transfer auto

declare [[code drop: finfun_update]]
lemma finfun_update_impl[code]: "finfun_update (ff_of_rbt (c, t)) x y = ff_of_rbt (c, RBT.insert x y t)"
  by transfer auto

end
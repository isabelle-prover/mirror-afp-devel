section \<open>Combining Big and Small\<close>

theory States 
imports Big Small
begin

datatype direction = Left | Right

datatype 'a states = States direction "'a big_state" "'a small_state"

instantiation states::(type) step
begin

fun step_states :: "'a states \<Rightarrow> 'a states" where
  "step (States dir (Big1 currentB big auxB 0) (Small1 currentS _ auxS)) =
    States dir (step (Big1 currentB big auxB 0)) (Small2 currentS auxS big [] 0)"
| "step (States dir left right) = States dir (step left) (step right)"

instance..
end

end

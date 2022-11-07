section \<open>Combining Big and Small\<close>

theory States 
imports Big Small
begin

datatype direction = Left | Right

datatype 'a states = States direction "'a Big.state" "'a Small.state"

instantiation states::(type) step
begin

fun step_states :: "'a states \<Rightarrow> 'a states" where
  "step (States dir (Reverse currentB big auxB 0) (Reverse1 currentS _ auxS)) =
    States dir (step (Reverse currentB big auxB 0)) (Reverse2 currentS auxS big [] 0)"
| "step (States dir left right) = States dir (step left) (step right)"

instance..
end

end

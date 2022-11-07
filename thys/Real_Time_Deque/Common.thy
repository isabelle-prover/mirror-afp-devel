section \<open>Common\<close>

theory Common
imports Current Idle
begin

text \<open>
\<^noindent> The last two phases of both deque ends during transformation:

 \<^descr> \<open>Copy\<close>: Using the \<open>step\<close> function the new elements of this deque end are brought back into the original order.
 \<^descr> \<open>Idle\<close>: The transformation of the deque end is finished.

\<^noindent> Each phase contains a \<open>current\<close> state, that holds the original elements of the deque end.
\<close>

datatype (plugins del: size)'a state = 
      Copy "'a current" "'a list" "'a list" nat
    | Idle "'a current" "'a idle"

text\<open>
\<^noindent> Functions:

\<^descr> \<open>push\<close>, \<open>pop\<close>: Add and remove elements using the \<open>current\<close> state.
\<^descr> \<open>step\<close>: Executes one step of the transformation, while keeping the invariant.\<close>

(* TODO: Maybe inline function? *)
fun normalize :: "'a state \<Rightarrow> 'a state" where
  "normalize (Copy current old new moved) = (
      case current of Current extra added _ remained \<Rightarrow> 
      if moved \<ge> remained
      then Idle current (idle.Idle (Stack extra new) (added + moved))
      else Copy current old new moved
  )"
| "normalize state = state"


instantiation state ::(type) step
begin

fun step_state :: "'a state \<Rightarrow> 'a state" where
  "step (Idle current idle) = Idle current idle"
| "step (Copy current aux new moved) = (
    case current of Current _ _ _ remained \<Rightarrow>
      normalize (
        if moved < remained
        then Copy current (tl aux) ((hd aux)#new) (moved + 1)
        else Copy current aux new moved
      )
  )"

instance..
end

fun push :: "'a \<Rightarrow> 'a state \<Rightarrow> 'a state" where
  "push x (Idle current (idle.Idle stack stackSize)) = 
      Idle (Current.push x current) (idle.Idle (Stack.push x stack) (Suc stackSize))"
| "push x (Copy current aux new moved) = Copy (Current.push x current) aux new moved"

fun pop :: "'a state \<Rightarrow> 'a * 'a state" where
  "pop (Idle current idle) = (let (x, idle) = Idle.pop idle in (x, Idle (drop_first current) idle))"
| "pop (Copy current aux new moved) = 
      (first current, normalize (Copy (drop_first current) aux new moved))"

end

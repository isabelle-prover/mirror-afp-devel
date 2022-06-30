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
\<^descr> \<open>list\<close>: List abstraction of the elements which this end will contain after the transformation is finished
\<^descr> \<open>list_current\<close>: List abstraction of the elements currently in this deque end.
\<^descr> \<open>step\<close>: Executes one step of the transformation, while keeping the invariant.
\<^descr> \<open>remaining_steps\<close>: Returns how many steps are left until the transformation is finished.
\<^descr> \<open>size_new\<close>: Returns the size, that the deque end will have after the transformation is finished.
\<^descr> \<open>size\<close>: Minimum of \<open>size_new\<close> and the number of elements contained in the \<open>current\<close> state.
\<close>
(*
fun reverseN :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "reverseN 0 xs acc = acc"
| "reverseN n [] acc = acc"
| "reverseN (Suc n) (x#xs) acc = reverseN n xs (x#acc)"
*)
definition reverseN where
[simp]:  "reverseN n xs acc \<equiv> rev (take n xs) @ acc"

fun list :: "'a state \<Rightarrow> 'a list" where
  "list (Idle _ idle) = Idle.list idle"
| "list (Copy (Current extra _ _ remained) old new moved) 
   = extra @ reverseN (remained - moved) old new"

fun list_current :: "'a state \<Rightarrow> 'a list" where
  "list_current (Idle current _) = Current.list current"
| "list_current (Copy current _ _ _) = Current.list current"

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

instantiation state ::(type) is_empty
begin

fun is_empty_state :: "'a state \<Rightarrow> bool" where
  "is_empty (Idle current idle)  \<longleftrightarrow> is_empty current \<or> is_empty idle"
| "is_empty (Copy current _ _ _) \<longleftrightarrow> is_empty current"

instance..
end

instantiation state::(type) invar
begin

fun invar_state :: "'a state \<Rightarrow> bool" where
  "invar (Idle current idle) \<longleftrightarrow>
      invar idle 
    \<and> invar current 
    \<and> size_new current = size idle
    \<and> take (size idle) (Current.list current) = 
      take (size current) (Idle.list idle)"
| "invar (Copy current aux new moved) \<longleftrightarrow> (
    case current of Current _ _ old remained \<Rightarrow>
      moved < remained
    \<and> moved = length new
    \<and> remained \<le> length aux + moved
    \<and> invar current
    \<and> take remained (Stack.list old) = take (size old) (reverseN (remained - moved) aux new)
 )"

instance..
end

instantiation state::(type) size
begin

(* Use size for emptiness? *)
fun size_state :: "'a state \<Rightarrow> nat" where
  "size (Idle current idle) = min (size current) (size idle)"
| "size (Copy current _ _ _) = min (size current) (size_new current)"

instance..
end

instantiation state::(type) size_new
begin

fun size_new_state :: "'a state \<Rightarrow> nat" where
  "size_new (Idle current _) = size_new current"
| "size_new (Copy current _ _ _) = size_new current"

instance..
end

instantiation state::(type) remaining_steps
begin

fun remaining_steps_state :: "'a state \<Rightarrow> nat" where
  "remaining_steps (Idle _ _) = 0"
| "remaining_steps (Copy (Current _ _ _ remained) aux new moved) = remained - moved"

instance..
end

end

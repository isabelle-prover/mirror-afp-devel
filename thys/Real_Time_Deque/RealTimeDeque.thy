section \<open>Real-Time Deque Implementation\<close>

theory RealTimeDeque
imports States
begin

text\<open>
The real-time deque can be in the following states:

 \<^descr> \<open>Empty\<close>: No values stored. No dequeue operation possible.
 \<^descr> \<open>One\<close>: One element in the deque.
 \<^descr> \<open>Two\<close>: Two elements in the deque.
 \<^descr> \<open>Three\<close>: Three elements in the deque.
 \<^descr> \<open>Idles\<close>: Deque with a left and a right end, fulfilling the following invariant:
   \<^item> 3 * size of left end \<open>\<ge>\<close> size of right end
   \<^item> 3 * size of right end \<open>\<ge>\<close> size of left end
   \<^item> Neither of the ends is empty
 \<^descr> \<open>Rebal\<close>: Deque which violated the invariant of the \<open>Idles\<close> state by non-balanced dequeue and enqueue operations. The invariants during in this state are:
   \<^item> The rebalancing is not done yet. The deque needs to be in \<open>Idles\<close> state otherwise.
   \<^item> The rebalancing is in a valid state (Defined in theory \<open>States\<close>)
   \<^item> The two ends of the deque are in a size window, such that after finishing the rebalancing the invariant of the \<open>Idles\<close> state will be met. 

Functions:

 \<^descr> \<open>is_empty\<close>: Checks if a deque is in the \<open>Empty\<close> state
 \<^descr> \<open>deqL'\<close>: Dequeues an element on the left end and return the element and the deque without this element. If the deque is in \<open>idle\<close> state and the size invariant is violated either a \<open>rebalancing\<close> is started or if there are 3 or less elements left the respective states are used. On \<open>rebalancing\<close> start, six steps are executed initially. During \<open>rebalancing\<close> state four steps are executed and if it is finished the deque returns to \<open>idle\<close> state.
 \<^descr> \<open>deqL\<close>: Removes one element on the left end and only returns the new deque.
 \<^descr> \<open>firstL\<close>: Removes one element on the left end and only returns the element.
 \<^descr> \<open>enqL\<close>: Enqueues an element on the left and returns the resulting deque. Like in \<open>deqL'\<close> when violating the size invariant in \<open>idle\<close> state, a \<open>rebalancing\<close> with six initial steps is started. During \<open>rebalancing\<close> state four steps are executed and if it is finished the deque returns to \<open>idle\<close> state.
 \<^descr> \<open>swap\<close>: The two ends of the deque are swapped.
 \<^descr> \<open>deqR'\<close>, \<open>deqR\<close>, \<open>firstR\<close>, \<open>enqR\<close>: Same behaviour as the left-counterparts. Implemented using the left-counterparts by swapping the deque before and after the operation.
 \<^descr> \<open>listL\<close>, \<open>listR\<close>: Get all elements of the deque in a list starting at the left or right end. They are needed as list abstractions for the correctness proofs.
\<close>

datatype 'a deque =
    Empty
  | One 'a
  | Two 'a 'a
  | Three 'a 'a 'a 
  | Idles "'a idle" "'a idle"
  | Rebal "'a states"

definition empty where
  "empty = Empty"

instantiation deque::(type) is_empty
begin

fun is_empty_deque :: "'a deque \<Rightarrow> bool" where
  "is_empty_deque Empty = True"
| "is_empty_deque _ = False"

instance..
end

fun swap :: "'a deque \<Rightarrow> 'a deque" where
  "swap Empty = Empty"  
| "swap (One x) = One x"
| "swap (Two x y) = Two y x"
| "swap (Three x y z) = Three z y x"
| "swap (Idles left right) = Idles right left"
| "swap (Rebal (States Left big small)) = (Rebal (States Right big small))"
| "swap (Rebal (States Right big small)) = (Rebal (States Left big small))"

fun small_deque :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a deque" where
  "small_deque []     [] = Empty"

| "small_deque (x#[]) [] = One x"
| "small_deque [] (x#[]) = One x"

| "small_deque (x#[])(y#[]) = Two y x"
| "small_deque (x#y#[]) [] = Two y x"
| "small_deque [] (x#y#[])= Two y x"

| "small_deque [] (x#y#z#[])   = Three z y x"
| "small_deque (x#y#z#[]) []   = Three z y x"
| "small_deque (x#y#[]) (z#[]) = Three z y x"
| "small_deque (x#[]) (y#z#[]) = Three z y x"

fun deqL' :: "'a deque \<Rightarrow> 'a * 'a deque" where
  "deqL' (One x) = (x, Empty)"
| "deqL' (Two x y) = (x, One y)"
| "deqL' (Three x y z) = (x, Two y z)"
| "deqL' (Idles left (idle.Idle right length_right)) = (
   case Idle.pop left of (x, (idle.Idle left length_left)) \<Rightarrow>
    if 3 * length_left \<ge> length_right 
    then 
      (x, Idles (idle.Idle left length_left) (idle.Idle right length_right))
    else if length_left \<ge> 1
    then 
      let length_left' = 2 * length_left + 1 in
      let length_right' = length_right - length_left - 1 in

      let small  = Small1 (Current [] 0 left length_left') left [] in
      let big = Big1 (Current [] 0 right length_right') right [] length_right' in

      let states = States Left big small in
      let states = (step^^6) states in
      
      (x, Rebal states)
    else 
      case right of Stack r1 r2 \<Rightarrow> (x, small_deque r1 r2)
  )"
| "deqL' (Rebal (States Left big small)) = (
    let (x, small) = Small.pop small in 
    let states = (step^^4) (States Left big small) in
    case states of 
        States Left
          (Big2 (Common.Idle _ big))
          (Small3 (Common.Idle _ small)) 
           \<Rightarrow> (x, Idles small big)
     | _ \<Rightarrow> (x, Rebal states)
  )"
| "deqL' (Rebal (States Right big small)) = (
    let (x, big) = Big.pop big in 
    let states = (step^^4) (States Right big small) in
    case states of 
       States Right 
          (Big2 (Common.Idle _ big)) 
          (Small3 (Common.Idle _ small)) \<Rightarrow>
            (x, Idles big small)
     | _ \<Rightarrow> (x, Rebal states)
  )"

fun deqR' :: "'a deque \<Rightarrow> 'a * 'a deque" where
  "deqR' deque = (
    let (x, deque) = deqL' (swap deque) 
    in (x, swap deque)
  )"

fun deqL :: "'a deque \<Rightarrow> 'a deque" where
  "deqL deque = (let (_, deque) = deqL' deque in deque)"

fun deqR :: "'a deque \<Rightarrow> 'a deque" where
  "deqR deque = (let (_, deque) = deqR' deque in deque)"

fun firstL :: "'a deque \<Rightarrow> 'a" where
  "firstL deque = (let (x, _) = deqL' deque in x)" 

fun firstR :: "'a deque \<Rightarrow> 'a" where
  "firstR deque = (let (x, _) = deqR' deque in x)" 

fun enqL :: "'a \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqL x Empty = One x"
| "enqL x (One y) = Two x y"
| "enqL x (Two y z) = Three x y z"
| "enqL x (Three a b c) = Idles (idle.Idle (Stack [x, a] []) 2) (idle.Idle (Stack [c, b] []) 2)"
| "enqL x (Idles left (idle.Idle right length_right)) = (
    case Idle.push x left of idle.Idle left length_left \<Rightarrow> 
      if 3 * length_right \<ge> length_left
      then 
        Idles (idle.Idle left length_left) (idle.Idle right length_right)
      else 
        let length_left = length_left - length_right - 1 in
        let length_right = 2 * length_right + 1 in

        let big  = Big1  (Current [] 0 left length_left) left [] length_left in
        let small = Small1 (Current [] 0 right length_right) right [] in
  
        let states = States Right big small in
        let states = (step^^6) states in
        
        Rebal states
  )"
| "enqL x (Rebal (States Left big small)) = (
    let small = Small.push x small in 
    let states = (step^^4) (States Left big small) in
    case states of 
        States Left 
          (Big2 (Common.Idle _ big))
          (Small3 (Common.Idle _ small)) 
         \<Rightarrow> Idles small big
     | _ \<Rightarrow> Rebal states
  )"
| "enqL x (Rebal (States Right big small)) = (
    let big = Big.push x big in 
    let states = (step^^4) (States Right big small) in
    case states of 
        States Right 
          (Big2 (Common.Idle _ big)) 
          (Small3 (Common.Idle _ small)) 
         \<Rightarrow> Idles big small
     | _ \<Rightarrow> Rebal states
  )"

fun enqR :: "'a \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqR x deque = (
    let deque = enqL x (swap deque) 
    in swap deque
  )"    

end

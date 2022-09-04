section \<open>Underlying FSM Representation\<close>

text \<open>This theory contains the underlying datatype for (possibly not well-formed) finite state machines.\<close>

theory FSM_Impl
  imports Util Datatype_Order_Generator.Order_Generator "HOL-Library.FSet"
begin


text \<open>A finite state machine (FSM) is represented using its classical definition:\<close>

datatype ('state, 'input, 'output) fsm_impl = FSMI (initial : 'state)  
                                                  (states  : "'state set")
                                                  (inputs  : "'input set")
                                                  (outputs : "'output set")
                                                  (transitions : "('state \<times> 'input \<times> 'output \<times> 'state) set")


subsection \<open>Types for Transitions and Paths\<close>

type_synonym ('a,'b,'c) transition = "('a \<times> 'b \<times> 'c \<times> 'a)"
type_synonym ('a,'b,'c) path = "('a,'b,'c) transition list"

abbreviation "t_source (a :: ('a,'b,'c) transition) \<equiv> fst a" 
abbreviation "t_input  (a :: ('a,'b,'c) transition) \<equiv> fst (snd a)"
abbreviation "t_output (a :: ('a,'b,'c) transition) \<equiv> fst (snd (snd a))"
abbreviation "t_target (a :: ('a,'b,'c) transition) \<equiv> snd (snd (snd a))"

subsection \<open>Basic Algorithms on FSM\<close>

subsubsection \<open>Reading FSMs from Lists\<close>

fun fsm_impl_from_list :: "'a \<Rightarrow> 
                           ('a,'b,'c) transition list \<Rightarrow> 
                           ('a, 'b, 'c) fsm_impl" 
  where
  "fsm_impl_from_list q [] = FSMI q {q} {} {} {}" |
  "fsm_impl_from_list q (t#ts) = 
    (let ts' = set (t#ts) 
     in FSMI (t_source t)
             ((image t_source ts') \<union> (image t_target ts'))
             (image t_input ts')
             (image t_output ts')
             (ts'))"

fun fsm_impl_from_list' :: "'a \<Rightarrow> ('a,'b,'c) transition list \<Rightarrow> ('a, 'b, 'c) fsm_impl" where
  "fsm_impl_from_list' q [] = FSMI q {q} {} {} {}" |
  "fsm_impl_from_list' q (t#ts) = (let tsr = (remdups (t#ts))
                                   in FSMI (t_source t)
                                      (set (remdups ((map t_source tsr) @ (map t_target tsr))))
                                      (set (remdups (map t_input tsr)))
                                      (set (remdups (map t_output tsr)))
                                      (set tsr))"

lemma fsm_impl_from_list_code[code] :
  "fsm_impl_from_list q ts = fsm_impl_from_list' q ts" 
  by (cases ts; auto)


subsubsection \<open>Changing the initial State\<close>

fun from_FSMI :: "('a,'b,'c) fsm_impl \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "from_FSMI M q = (if q \<in> states M then FSMI q (states M) (inputs M) (outputs M) (transitions M) else M)"


subsubsection \<open>Product Construction\<close>

fun product :: "('a,'b,'c) fsm_impl \<Rightarrow> ('d,'b,'c) fsm_impl \<Rightarrow> ('a \<times> 'd,'b,'c) fsm_impl" where
  "product A B = FSMI ((initial A, initial B))
                     ((states A) \<times> (states B))
                     (inputs A \<union> inputs B)
                     (outputs A \<union> outputs B)
                     {((qA,qB),x,y,(qA',qB')) | qA qB x y qA' qB' . (qA,x,y,qA') \<in> transitions A \<and> (qB,x,y,qB') \<in> transitions B}"

lemma product_code_naive[code] :
  "product A B = FSMI ((initial A, initial B))
                     ((states A) \<times> (states B))
                     (inputs A \<union> inputs B)
                     (outputs A \<union> outputs B)
                     (image (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . ((qA,qB),x,y,(qA',qB'))) (Set.filter (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . x = x' \<and> y = y') (\<Union>(image (\<lambda> tA . image (\<lambda> tB . (tA,tB)) (transitions B)) (transitions A)))))"
  (is "?P1 = ?P2")
proof -
  have "(\<Union>(image (\<lambda> tA . image (\<lambda> tB . (tA,tB)) (transitions B)) (transitions A))) = {(tA,tB) | tA tB . tA \<in> transitions A \<and> tB \<in> transitions B}"
    by auto
  then have "(Set.filter (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . x = x' \<and> y = y') (\<Union>(image (\<lambda> tA . image (\<lambda> tB . (tA,tB)) (transitions B)) (transitions A)))) = {((qA,x,y,qA'),(qB,x,y,qB')) | qA qB x y qA' qB' . (qA,x,y,qA') \<in> transitions A \<and> (qB,x,y,qB') \<in> transitions B}"
    by auto
  then have "image (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . ((qA,qB),x,y,(qA',qB'))) (Set.filter (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . x = x' \<and> y = y') (\<Union>(image (\<lambda> tA . image (\<lambda> tB . (tA,tB)) (transitions B)) (transitions A)))) 
              = image (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . ((qA,qB),x,y,(qA',qB'))) {((qA,x,y,qA'),(qB,x,y,qB')) | qA qB x y qA' qB' . (qA,x,y,qA') \<in> transitions A \<and> (qB,x,y,qB') \<in> transitions B}"
    by auto
  moreover have "image (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . ((qA,qB),x,y,(qA',qB'))) {((qA,x,y,qA'),(qB,x,y,qB')) | qA qB x y qA' qB' . (qA,x,y,qA') \<in> transitions A \<and> (qB,x,y,qB') \<in> transitions B} =  {((qA,qB),x,y,(qA',qB')) | qA qB x y qA' qB' . (qA,x,y,qA') \<in> transitions A \<and> (qB,x,y,qB') \<in> transitions B}"
    by force
  ultimately have "transitions ?P1 = transitions ?P2" 
    unfolding product.simps by auto
  moreover have "initial ?P1 = initial ?P2" by auto
  moreover have "states ?P1 = states ?P2" by auto
  moreover have "inputs ?P1 = inputs ?P2" by auto
  moreover have "outputs ?P1 = outputs ?P2" by auto
  ultimately show ?thesis by auto
qed


subsubsection \<open>Filtering Transitions\<close>

fun filter_transitions :: "('a,'b,'c) fsm_impl \<Rightarrow> (('a,'b,'c) transition \<Rightarrow> bool) \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "filter_transitions M P = FSMI (initial M)
                                (states M)
                                (inputs M)
                                (outputs M)
                                (Set.filter P (transitions M))"


subsubsection \<open>Filtering States\<close>

fun filter_states :: "('a,'b,'c) fsm_impl \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "filter_states M P = (if P (initial M) then FSMI (initial M)
                                                  (Set.filter P (states M))
                                                  (inputs M)
                                                  (outputs M)
                                                  (Set.filter (\<lambda> t . P (t_source t) \<and> P (t_target t)) (transitions M))
                                         else M)"
 
subsubsection \<open>Initial Singleton FSMI (For Trivial Preamble)\<close>    

fun initial_singleton :: "('a,'b,'c) fsm_impl \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "initial_singleton M = FSMI (initial M)
                             {initial M}
                             (inputs M)
                             (outputs M)
                             {}"


subsubsection \<open>Canonical Separator\<close>

abbreviation "shift_Inl t \<equiv> (Inl (t_source t),t_input t, t_output t, Inl (t_target t))"

definition shifted_transitions :: "(('a \<times> 'a) \<times> 'b \<times> 'c \<times> ('a \<times> 'a)) set \<Rightarrow> ((('a \<times> 'a) + 'd) \<times> 'b \<times> 'c \<times> (('a \<times> 'a) + 'd)) set" where
  "shifted_transitions ts = image shift_Inl ts"

definition distinguishing_transitions :: "(('a \<times> 'b) \<Rightarrow> 'c set) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'b set \<Rightarrow> ((('a \<times> 'a) + 'a) \<times> 'b \<times> 'c \<times> (('a \<times> 'a) + 'a)) set" where
  "distinguishing_transitions f q1 q2 stateSet inputSet = \<Union> (Set.image (\<lambda>((q1',q2'),x) .  
                                                                (image (\<lambda>y . (Inl (q1',q2'),x,y,Inr q1)) (f (q1',x) - f (q2',x))) 
                                                                \<union> (image (\<lambda>y . (Inl (q1',q2'),x,y,Inr q2)) (f (q2',x) - f (q1',x))))
                                                            (stateSet \<times> inputSet))"



(* Note: parameter P is added to allow usage of different restricted versions of the product machine *)
fun canonical_separator' :: "('a,'b,'c) fsm_impl \<Rightarrow> (('a \<times> 'a),'b,'c) fsm_impl \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b,'c) fsm_impl" where
  "canonical_separator' M P q1 q2 = (if initial P = (q1,q2) 
  then
    (let f'  = set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y)) (transitions M));
         f   = (\<lambda>qx . (case f' qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}));
         shifted_transitions' = shifted_transitions (transitions P);
         distinguishing_transitions_lr = distinguishing_transitions f q1 q2 (states P) (inputs P);
         ts = shifted_transitions' \<union> distinguishing_transitions_lr
     in 
  
      FSMI (Inl (q1,q2))
      ((image Inl (states P)) \<union> {Inr q1, Inr q2})
      (inputs M \<union> inputs P)
      (outputs M \<union> outputs P)
      (ts))
  else FSMI (Inl (q1,q2)) {Inl (q1,q2)} {} {} {})"

lemma h_out_impl_helper: "(\<lambda> (q,x) . {y . \<exists> q' . (q,x,y,q') \<in> A}) = (\<lambda>qx . (case (set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y)) A)) qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}))"
proof 
  fix qx 
  show "(\<lambda> (q,x) . {y . \<exists> q' . (q,x,y,q') \<in> A}) qx = (\<lambda>qx . (case (set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y)) A)) qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {})) qx"
  proof -
    obtain q x where "qx = (q,x)" using prod.exhaust by metis
    have **: "\<And> z .  ((q, x), z) \<in> (\<lambda>(q, x, y, q'). ((q, x), y)) ` A = (z \<in> {y . \<exists> q' . (q,x,y,q') \<in> A})"
      by force
    show ?thesis unfolding \<open>qx = (q,x)\<close> case_prod_conv set_as_map_def 
      unfolding ** by auto
  qed
qed

lemma canonical_separator'_simps :
        "initial (canonical_separator' M P q1 q2) = Inl (q1,q2)"
        "states (canonical_separator' M P q1 q2) = (if initial P = (q1,q2) then (image Inl (states P)) \<union> {Inr q1, Inr q2} else {Inl (q1,q2)})"
        "inputs (canonical_separator' M P q1 q2) = (if initial P = (q1,q2) then inputs M \<union> inputs P else {})"
        "outputs (canonical_separator' M P q1 q2) = (if initial P = (q1,q2) then outputs M \<union> outputs P else {})"
        "transitions (canonical_separator' M P q1 q2) = (if initial P = (q1,q2) then shifted_transitions (transitions P) \<union> distinguishing_transitions (\<lambda> (q,x) . {y . \<exists> q' . (q,x,y,q') \<in> transitions M}) q1 q2 (states P) (inputs P) else {})"
  unfolding h_out_impl_helper by (simp add: Let_def)+



subsubsection \<open>Generalised Canonical Separator\<close>

text \<open>A variation on the state separator that uses states @{text "L"} and @{text "R"} instead of
      @{text "Inr q1"} and @{text "Inr q2"} to indicate targets of transitions in the 
      canonical separator that are available only for the left or right component of a state pair\<close>

text \<open>Note: this definition of a canonical separator might serve as a way to avoid recalculation
            of state separators for different pairs of states, but is currently not fully 
            implemented\<close>

datatype LR = Left | Right
derive linorder LR

definition distinguishing_transitions_LR :: "(('a \<times> 'b) \<Rightarrow> 'c set) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'b set \<Rightarrow> ((('a \<times> 'a) + LR) \<times> 'b \<times> 'c \<times> (('a \<times> 'a) + LR)) set" where
  "distinguishing_transitions_LR f stateSet inputSet = \<Union> (Set.image (\<lambda>((q1',q2'),x) .  
                                                                (image (\<lambda>y . (Inl (q1',q2'),x,y,Inr Left)) (f (q1',x) - f (q2',x))) 
                                                                \<union> (image (\<lambda>y . (Inl (q1',q2'),x,y,Inr Right)) (f (q2',x) - f (q1',x))))
                                                            (stateSet \<times> inputSet))"


fun canonical_separator_complete' :: "('a,'b,'c) fsm_impl \<Rightarrow> (('a \<times> 'a) + LR,'b,'c) fsm_impl" where
  "canonical_separator_complete' M =  
    (let P = product M M; 
         f'  = set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y)) (transitions M));
         f   = (\<lambda>qx . (case f' qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}));
         shifted_transitions' = shifted_transitions (transitions P);
         distinguishing_transitions_lr = distinguishing_transitions_LR f (states P) (inputs P);
         ts = shifted_transitions' \<union> distinguishing_transitions_lr
     in   
      FSMI (Inl (initial P))
          ((image Inl (states P)) \<union> {Inr Left, Inr Right})
          (inputs M \<union> inputs P)
          (outputs M \<union> outputs P)
          ts )"



subsubsection \<open>Adding Transitions\<close>

fun add_transitions :: "('a,'b,'c) fsm_impl \<Rightarrow> ('a,'b,'c) transition set \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "add_transitions M ts = (if (\<forall> t \<in> ts . t_source t \<in> states M \<and> t_input t \<in> inputs M \<and> t_output t \<in> outputs M \<and> t_target t \<in> states M)
    then FSMI (initial M)
             (states M)
             (inputs M)
             (outputs M)
             ((transitions M) \<union> ts)
    else M)"


subsubsection \<open>Creating an FSMI without transitions\<close>

fun create_unconnected_FSMI :: "'a \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'c set \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "create_unconnected_FSMI q ns ins outs = (if (finite ns \<and> finite ins \<and> finite outs)
    then FSMI q (insert q ns) ins outs {}
    else FSMI q {q} {} {} {})"

fun create_unconnected_fsm_from_lists :: "'a \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "create_unconnected_fsm_from_lists q ns ins outs = FSMI q (insert q (set ns)) (set ins) (set outs) {}"

fun create_unconnected_fsm_from_fsets :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'b fset \<Rightarrow> 'c fset \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "create_unconnected_fsm_from_fsets q ns ins outs = FSMI q (insert q (fset ns)) (fset ins) (fset outs) {}"

fun create_fsm_from_sets :: "'a \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'c set \<Rightarrow> ('a,'b,'c) transition set \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "create_fsm_from_sets q qs ins outs ts = (if q \<in> qs \<and> finite qs \<and> finite ins \<and> finite outs 
    then add_transitions (FSMI q qs ins outs {}) ts
    else FSMI q {q} {} {} {})"
 

subsection \<open>Transition Function h\<close>

text \<open>Function @{text "h"} represents the classical view of the transition relation of an FSM @{text "M"} as a
      function: given a state @{text "q"} and an input @{text "x"}, @{text "(h M) (q,x)"} returns all
      possibly reactions @{text "(y,q')"} of @{text "M"} in state @{text "q"} to @{text "x"}, where
      @{text "y"} is the produced output and @{text "q'"} the target state of the reaction transition.\<close>

fun h :: "('state, 'input, 'output) fsm_impl \<Rightarrow> ('state \<times> 'input) \<Rightarrow> ('output \<times> 'state) set" where
  "h M (q,x) = { (y,q') . (q,x,y,q') \<in> transitions M }"

fun h_obs :: "('a,'b,'c) fsm_impl \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'a option" where
  "h_obs M q x y = (let 
      tgts = snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x))
    in if card tgts = 1
      then Some (the_elem tgts)
      else None)"

lemma h_code[code] : 
  "h M (q,x) = (let m = set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y,q')) (transitions M)) 
                 in (case m (q,x) of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}))"
  unfolding set_as_map_def by force


subsection \<open>Extending FSMs by single elements\<close>

fun add_transition :: "('a,'b,'c) fsm_impl \<Rightarrow> 
                       ('a,'b,'c) transition \<Rightarrow> 
                       ('a,'b,'c) fsm_impl" 
  where
  "add_transition M t = 
    (if t_source t \<in> states M \<and> t_input t \<in> inputs M \<and> 
        t_output t \<in> outputs M \<and> t_target t \<in> states M
     then FSMI (initial M) 
               (states M) 
               (inputs M) 
               (outputs M) 
               (insert t (transitions M))
     else M)"

fun add_state :: "('a,'b,'c) fsm_impl \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "add_state M q = FSMI (initial M) (insert q (states M)) (inputs M) (outputs M) (transitions M)"

fun add_input :: "('a,'b,'c) fsm_impl \<Rightarrow> 'b \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "add_input M x = FSMI (initial M) (states M) (insert x (inputs M)) (outputs M) (transitions M)"

fun add_output :: "('a,'b,'c) fsm_impl \<Rightarrow> 'c \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "add_output M y = FSMI (initial M) (states M) (inputs M) (insert y (outputs M)) (transitions M)"

fun add_transition_with_components :: "('a,'b,'c) fsm_impl \<Rightarrow> ('a,'b,'c) transition \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "add_transition_with_components M t = add_transition (add_state (add_state (add_input (add_output M (t_output t)) (t_input t)) (t_source t)) (t_target t)) t"

subsection \<open>Renaming elements\<close>

fun rename_states :: "('a,'b,'c) fsm_impl \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> ('d,'b,'c) fsm_impl" where
  "rename_states M f = FSMI (f (initial M))
                            (f ` states M)
                            (inputs M)
                            (outputs M)
                            ((\<lambda>t . (f (t_source t), t_input t, t_output t, f (t_target t))) ` transitions M)"
                              

end
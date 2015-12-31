(*Author: Giuliano Losa *)

section {* The ALM Automata specification*}
theory ALM
imports "~~/src/HOL/HOLCF/IOA/IOA" LCP
begin

typedecl client
  -- {*A non-empty set of clients*}
typedecl data
  -- {*Data contained in requests*}
datatype request = 
  -- {*A request is composed of a sender and data*}
  Req client data

definition request_snd :: "request \<Rightarrow> client"
  where "request_snd \<equiv> \<lambda> r. case r of Req c _ \<Rightarrow> c"

type_synonym hist = "request list" 
  -- {*Type of histories of requests.*}

datatype ALM_action = 
  -- {*The actions of the ALM automaton*}
  Invoke client "request" 
  | Commit client nat "hist"
  | Switch client nat "hist" "request"
  | Initialize nat "hist"
  | Linearize nat "hist"
  | Abort nat

datatype phase = Sleep | Pending | Ready | Aborted
  -- {*Executions phases of a client*}

definition linearizations :: "request set \<Rightarrow> hist set"
  -- {*The possible linearizations of a set of requests*}
  where 
  "linearizations \<equiv> \<lambda> reqs . {h . set h \<subseteq> reqs \<and> distinct h}"

definition postfix_all :: "hist \<Rightarrow> hist set \<Rightarrow> hist set"
  -- {*appends to the right the first argument to every member of the history set*}
  where 
  "postfix_all \<equiv> \<lambda> h hs . {h' . \<exists> h'' . h' = h'' @ h \<and> h'' \<in> hs}"
    
definition
  ALM_asig :: "nat \<Rightarrow> nat \<Rightarrow> ALM_action signature" 
  -- {*The action signature of ALM automata*}
  -- {*Input actions, output actions, and internal actions*}
  where
  "ALM_asig \<equiv> \<lambda> id1 id2 . (
    {act . \<exists> c r h . 
             act = Invoke c r | act = Switch c id1 h r},
    {act . \<exists> c h r id' . 
             id1 <= id' \<and> id' < id2 \<and> act = Commit c id' h
             | act = Switch c id2 h r},
    {act . \<exists> h . 
             act = Abort id1
             | act = Linearize id1 h 
             | act = Initialize id1 h} )"

record ALM_state = 
  -- {*The state of the ALM automata *}
  pending :: "client \<Rightarrow> request"
  -- {*Associates a pending request to a client process*}
  initHists :: "hist set"
  -- {*The set of init histories submitted by clients*}
  phase :: "client \<Rightarrow> phase"
  -- {*Associates a phase to a client process*}
  hist :: "hist"
  -- {*Represents the chosen linearization of the concurrent history of the current instance only*}
  aborted :: "bool"
  initialized :: "bool"

definition pendingReqs :: "ALM_state \<Rightarrow> request set" 
  -- {*the set of requests that have been invoked but that are not yet in the hist parameter*}
  where
  "pendingReqs \<equiv> \<lambda> s . {r . \<exists> c . 
     r = pending s c
     \<and> r \<notin> set (hist s)
     \<and> phase s c \<in> {Pending, Aborted}}"

definition initValidReqs :: "ALM_state \<Rightarrow> request set" 
  -- {*any request that appears in an init hist after the longest common prefix or that is pending*}
  where
  "initValidReqs \<equiv> \<lambda>s . {r . 
     (r \<in> pendingReqs s  \<or> (\<exists> h \<in> initHists s . r \<in> set h))
     \<and> r \<notin> set (l_c_p (initHists s))}"

definition
  ALM_trans :: "nat \<Rightarrow> nat \<Rightarrow> (ALM_action, ALM_state)transition set" 
  -- {*the transitions of the ALM automaton*}
  where
  "ALM_trans \<equiv> \<lambda> id1 id2 . {trans . 
    let s = fst trans; s' = snd (snd trans); a = fst (snd trans) in 

     case a of Invoke c r \<Rightarrow> 
      if phase s c = Ready \<and> request_snd r = c \<and> r \<notin> set (hist s)
      then s' = s\<lparr>pending := (pending s)(c := r),
                  phase := (phase s)(c := Pending)\<rparr>
      else s' = s

    |Linearize i h \<Rightarrow> 
      initialized s \<and> \<not> aborted s
      \<and> h \<in> postfix_all (hist s) (linearizations (pendingReqs s ))
      \<and> s' = s\<lparr>hist := h\<rparr>

    |Initialize i h \<Rightarrow>
      (\<exists> c . phase s c \<noteq> Sleep) \<and> \<not> aborted s \<and> \<not> initialized s
      \<and> h \<in> postfix_all (l_c_p (initHists s)) (linearizations (initValidReqs s))
      \<and> s' = s\<lparr>hist := h, initialized := True\<rparr>

    |Abort i \<Rightarrow> 
      \<not> aborted s \<and>  (\<exists> c . phase s c \<noteq> Sleep)
      \<and> s' = s\<lparr>aborted:= True\<rparr>

    |Commit c i h \<Rightarrow> 
      phase s c = Pending \<and> pending s c \<in> set (hist s)
      \<and> h = dropWhile (\<lambda> r . r \<noteq> pending s c) (hist s)
      \<and> s' = s \<lparr>phase := (phase s)(c := Ready)\<rparr>

    |Switch c i h r \<Rightarrow> 
      if i = id1
      then if phase s c = Sleep
        then s' = s \<lparr>initHists := {h} \<union> (initHists s), 
                     phase := (phase s)(c := Pending), 
                     pending := (pending s)(c := r)\<rparr>
        else s' = s
      else if i = id2
        then aborted s 
             \<and> phase s c = Pending \<and> r = pending s c 
             \<and> (if initialized s
                then (h \<in> postfix_all (hist s) (linearizations (pendingReqs s )))
                else (h \<in> postfix_all (l_c_p (initHists s)) (linearizations (initValidReqs s))))
             \<and> s' = s\<lparr>phase := (phase s)(c := Aborted)\<rparr>
        else False }"

definition ALM_start :: "nat \<Rightarrow> ALM_state set" 
  -- {*the set of start states*}
  where
  "ALM_start \<equiv> \<lambda> id . {s . 
    \<forall> c . phase s c = (if id \<noteq> 0 then Sleep else Ready) 
    \<and> hist s = [] 
    \<and> \<not> aborted s 
    \<and> (if id \<noteq> 0 then \<not> initialized s else initialized s)
    \<and> initHists s = {}}"

definition ALM_ioa :: "nat \<Rightarrow> nat \<Rightarrow> (ALM_action, ALM_state)ioa" 
  -- {*The ALM automaton*}
  where
  "ALM_ioa \<equiv> \<lambda> (id1::nat) id2 . 
     (ALM_asig id1 id2, 
      ALM_start id1, 
      ALM_trans id1 id2,
      {}, {})"

type_synonym compo_state = "ALM_state \<times> ALM_state"

definition composeALMs :: "nat \<Rightarrow> nat \<Rightarrow> (ALM_action, compo_state) ioa" 
  -- {*the composition of two ALMs*}
  where
  "composeALMs \<equiv> \<lambda> id1 id2 . 
     hide (ALM_ioa 0 id1 \<parallel> ALM_ioa id1 id2)
          {act . EX c tr r . act = Switch c id1 tr r}"

end
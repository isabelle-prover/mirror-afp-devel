theory Abstract_Context
  imports Generic_Term_Context
begin

datatype ('f, extra_set: 'extra, term_set: 't) "context" =
  Hole (\<open>\<box>\<close>) |
  More
    (fun_sym: 'f) (extra: 'extra) (subterms\<^sub>l: "'t list") 
    (subcontext: "('f, 'extra, 't) context") (subterms\<^sub>r: "'t list")

primrec compose_context (infixl \<open>\<circ>\<^sub>c\<close> 75) where
  "Hole \<circ>\<^sub>c c = c"
| "More f e ls C rs \<circ>\<^sub>c D = More f e ls (C \<circ>\<^sub>c D) rs"

fun hole_position :: "('f, 'extra, 't) context \<Rightarrow> position" where
  "hole_position \<box> = []"
| "hole_position (More _  _ ss D _) = length ss # hole_position D"

interpretation abstract_context: smaller_subcontext where
  hole = \<box> and size = size and subcontext = subcontext
proof unfold_locales
  fix c :: "('f, 'extra, 't) context"
  assume "c \<noteq> \<box>"

  then show "size (subcontext c) < size c"
    by (cases c) auto
qed

locale abstract_context = 
  term_interpretation where Fun = Fun +
  smaller_subterms 
for Fun :: "'f \<Rightarrow> 'e \<Rightarrow> 't list \<Rightarrow> 't"
begin

primrec apply_context (\<open>_\<langle>_\<rangle>\<close> [1000, 0] 1000) where
  "\<box>\<langle>t\<rangle> = t"
| "(More f e ls C rs)\<langle>t\<rangle> = Fun f e (ls @ C\<langle>t\<rangle> # rs)"

primrec context_at :: "'t \<Rightarrow> position \<Rightarrow> ('f, 'e, 't) context" (infixl \<open>!\<^sub>c\<close> 64) where
  "t !\<^sub>c [] = \<box>"
| "t !\<^sub>c i # ps =
   More
    (fun_sym t)
    (extra t)
    (take i (subterms t)) (subterms t ! i !\<^sub>c ps)
    (drop (Suc i) (subterms t))"

sublocale "context" where
  hole = \<box> and 
  apply_context = apply_context and 
  compose_context = compose_context
proof unfold_locales
  fix c c' t

  show "(c \<circ>\<^sub>c c')\<langle>t\<rangle> = c\<langle>c'\<langle>t\<rangle>\<rangle>"
    by (induction c) auto
next
  fix t

  show "\<box>\<langle>t\<rangle> = t"
    by simp
next
  fix c t t'
  assume "c\<langle>t\<rangle> = c\<langle>t'\<rangle>"

  then show "t = t'"
  proof(induction c)
    case Hole
    then show ?case
      by simp
  next
    case (More f e ls c rs)
    then show ?case 
      by (metis apply_context.simps(2) nth_append_length subterms)
  qed
next
  fix c :: "('f, 'extra, 't) context"
  show "c \<circ>\<^sub>c \<box> = c"
    by (induction c) auto
qed auto

sublocale term_context_interpretation where
  hole = \<box> and apply_context = apply_context and compose_context = "(\<circ>\<^sub>c)" and
  More = More and fun_sym\<^sub>c = context.fun_sym and extra\<^sub>c = context.extra and subterms\<^sub>l = subterms\<^sub>l and
  subcontext = subcontext and subterms\<^sub>r = subterms\<^sub>r 
proof unfold_locales
  fix c :: "('f, 'e, 't) context"

  show "c \<noteq> \<box> \<longleftrightarrow> (\<exists>f e ls c' rs. c = More f e ls c' rs)"
    by (metis context.discI context.exhaust_sel)
qed auto

sublocale replace_at_subterm where  
  hole = \<box> and apply_context = apply_context and compose_context = "(\<circ>\<^sub>c)" and
  hole_position = hole_position and context_at = context_at
proof unfold_locales
  fix c :: "('f, 'e, 't) context" and t

  show "c\<langle>t\<rangle> !\<^sub>t hole_position c = t"
    by (induction c) auto

  show "hole_position c \<in> positions c\<langle>t\<rangle>"
    by (induction c) (auto simp: term_destruct)

  show "c\<langle>t\<rangle> !\<^sub>c hole_position c = c"
    by (induction c) auto
next
  fix p and t
  assume "p \<in> positions t"

  then show "(t !\<^sub>c p)\<langle>t !\<^sub>t p\<rangle> = t"
  by (induction p arbitrary: t) (auto simp: Cons_nth_drop_Suc)
qed auto

end

end

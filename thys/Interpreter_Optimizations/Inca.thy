theory Inca
  imports Global OpInl Env Dynamic
    "VeriComp.Language"
begin


section \<open>Inline caching\<close>

subsection \<open>Static representation\<close>

datatype ('dyn, 'var, 'fun, 'label, 'op, 'opinl) instr =
  IPush 'dyn |
  IPop |
  IGet nat |
  ISet nat |
  ILoad 'var |
  IStore 'var |
  IOp 'op |
  IOpInl 'opinl |
  is_jump: ICJump 'label 'label |
  ICall 'fun |
  is_return: IReturn

locale inca =
  Fenv: env F_empty F_get F_add F_to_list +
  Henv: env heap_empty heap_get heap_add heap_to_list +
  dynval uninitialized is_true is_false +
  nary_operations_inl \<OO>\<pp> \<AA>\<rr>\<ii>\<tt>\<yy> \<II>\<nn>\<ll>\<OO>\<pp> \<II>\<nn>\<ll> \<II>\<ss>\<II>\<nn>\<ll> \<DD>\<ee>\<II>\<nn>\<ll>
  for
    \<comment> \<open>Functions environment\<close>
    F_empty and
    F_get :: "'fenv \<Rightarrow> 'fun \<Rightarrow> ('label, ('dyn, 'var, 'fun, 'label, 'op, 'opinl) instr) fundef option" and
    F_add and F_to_list and

    \<comment> \<open>Memory heap\<close>
    heap_empty and
    heap_get :: "'henv \<Rightarrow> 'var \<times> 'dyn \<Rightarrow> 'dyn option" and
    heap_add and heap_to_list and

    \<comment> \<open>Dynamic values\<close>
    uninitialized :: 'dyn and is_true and is_false and

    \<comment> \<open>n-ary operations\<close>
    \<OO>\<pp> :: "'op \<Rightarrow> 'dyn list \<Rightarrow> 'dyn" and \<AA>\<rr>\<ii>\<tt>\<yy> and
    \<II>\<nn>\<ll>\<OO>\<pp> and \<II>\<nn>\<ll> and \<II>\<ss>\<II>\<nn>\<ll> and \<DD>\<ee>\<II>\<nn>\<ll> :: "'opinl \<Rightarrow> 'op"
begin


subsection \<open>Semantics\<close>

inductive step (infix "\<rightarrow>" 55) where
  step_push:
    "next_instr (F_get F) f l pc = Some (IPush d) \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F H (Frame f l (Suc pc) R (d # \<Sigma>) # st)" |

  step_pop:
    "next_instr (F_get F) f l pc = Some IPop \<Longrightarrow>
    State F H (Frame f l pc R (d # \<Sigma>) # st) \<rightarrow> State F H (Frame f l (Suc pc) R \<Sigma> # st)" |

  step_get:
    "next_instr (F_get F) f l pc = Some (IGet n) \<Longrightarrow>
    n < length R \<Longrightarrow> d = R ! n \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F H (Frame f l (Suc pc) R (d # \<Sigma>) # st)" |

  step_set:
    "next_instr (F_get F) f l pc = Some (ISet n) \<Longrightarrow>
    n < length R \<Longrightarrow>  R' = R[n := d] \<Longrightarrow>
    State F H (Frame f l pc R (d # \<Sigma>) # st) \<rightarrow> State F H (Frame f l (Suc pc) R' \<Sigma> # st)" |

  step_load:
    "next_instr (F_get F) f l pc = Some (ILoad x) \<Longrightarrow>
    heap_get H (x, y) = Some d \<Longrightarrow>
    State F H (Frame f l pc R (y # \<Sigma>) # st) \<rightarrow> State F H (Frame f l (Suc pc) R (d # \<Sigma>) # st)" |

  step_store:
    "next_instr (F_get F) f l pc = Some (IStore x) \<Longrightarrow>
    heap_add H (x, y) d = H' \<Longrightarrow>
    State F H (Frame f l pc R (y # d # \<Sigma>) # st) \<rightarrow> State F H' (Frame f l (Suc pc) R \<Sigma> # st)" |

  step_op:
    "next_instr (F_get F) f l pc = Some (IOp op) \<Longrightarrow>
    \<AA>\<rr>\<ii>\<tt>\<yy> op = ar \<Longrightarrow> ar \<le> length \<Sigma> \<Longrightarrow> \<II>\<nn>\<ll> op (take ar \<Sigma>) = None \<Longrightarrow>
    \<OO>\<pp> op (take ar \<Sigma>) = x \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F H (Frame f l (Suc pc) R (x # drop ar \<Sigma>) # st)" |

  step_op_inl:
    "next_instr (F_get F) f l pc = Some (IOp op) \<Longrightarrow>
    \<AA>\<rr>\<ii>\<tt>\<yy> op = ar \<Longrightarrow> ar \<le> length \<Sigma> \<Longrightarrow> \<II>\<nn>\<ll> op (take ar \<Sigma>) = Some opinl \<Longrightarrow>
    \<II>\<nn>\<ll>\<OO>\<pp> opinl (take ar \<Sigma>) = x \<Longrightarrow>
    F' = Fenv.map_entry F f (\<lambda>fd. rewrite_fundef_body fd l pc (IOpInl opinl)) \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F' H (Frame f l (Suc pc) R (x # drop ar \<Sigma>) # st)" |

  step_op_inl_hit:
    "next_instr (F_get F) f l pc = Some (IOpInl opinl) \<Longrightarrow>
    \<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl) = ar \<Longrightarrow> ar \<le> length \<Sigma> \<Longrightarrow> \<II>\<ss>\<II>\<nn>\<ll> opinl (take ar \<Sigma>) \<Longrightarrow>
    \<II>\<nn>\<ll>\<OO>\<pp> opinl (take ar \<Sigma>) = x \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F H (Frame f l (Suc pc) R (x # drop ar \<Sigma>) # st)" |

  step_op_inl_miss:
    "next_instr (F_get F) f l pc = Some (IOpInl opinl) \<Longrightarrow>
    \<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl) = ar \<Longrightarrow> ar \<le> length \<Sigma> \<Longrightarrow> \<not> \<II>\<ss>\<II>\<nn>\<ll> opinl (take ar \<Sigma>) \<Longrightarrow>
    \<II>\<nn>\<ll>\<OO>\<pp> opinl (take ar \<Sigma>) = x \<Longrightarrow>
    F' = Fenv.map_entry F f (\<lambda>fd. rewrite_fundef_body fd l pc (IOp (\<DD>\<ee>\<II>\<nn>\<ll> opinl))) \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F' H (Frame f l (Suc pc) R (x # drop ar \<Sigma>) # st)" |

  step_cjump:
    "next_instr (F_get F) f l pc = Some (ICJump l\<^sub>t l\<^sub>f) \<Longrightarrow>
    is_true d \<and> l' = l\<^sub>t \<or> is_false d \<and> l' = l\<^sub>f \<Longrightarrow>
    State F H (Frame f l pc R (d # \<Sigma>) # st) \<rightarrow> State F H (Frame f l' 0 R \<Sigma> # st)" |

  step_call:
    "next_instr (F_get F) f l pc = Some (ICall g) \<Longrightarrow>
    F_get F g = Some gd \<Longrightarrow> arity gd \<le> length \<Sigma> \<Longrightarrow>
    frame\<^sub>g = allocate_frame g gd (take (arity gd) \<Sigma>) uninitialized \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F H (frame\<^sub>g # Frame f l pc R \<Sigma> # st)" |

  step_return:
    "next_instr (F_get F) g l\<^sub>g pc\<^sub>g = Some IReturn \<Longrightarrow>
    F_get F g = Some gd \<Longrightarrow> arity gd \<le> length \<Sigma>\<^sub>f \<Longrightarrow>
    length \<Sigma>\<^sub>g = return gd \<Longrightarrow> 
    frame\<^sub>f' = Frame f l\<^sub>f (Suc pc\<^sub>f) R\<^sub>f (\<Sigma>\<^sub>g @ drop (arity gd) \<Sigma>\<^sub>f) \<Longrightarrow>
    State F H (Frame g l\<^sub>g pc\<^sub>g R\<^sub>g \<Sigma>\<^sub>g # Frame f l\<^sub>f pc\<^sub>f R\<^sub>f \<Sigma>\<^sub>f # st) \<rightarrow> State F H (frame\<^sub>f' # st)"

lemma step_deterministic:
  assumes "s1 \<rightarrow> s2" and "s1 \<rightarrow> s3"
  shows "s2 = s3"
  using assms
  apply (cases s1 s2 rule: step.cases)
  apply (auto elim: step.cases dest: is_true_and_is_false_implies_False) [3]
  apply (auto elim: step.cases dest: is_true_and_is_false_implies_False) [3]
  apply (auto elim: step.cases dest: is_true_and_is_false_implies_False) [3]
  apply (auto elim: step.cases dest: is_true_and_is_false_implies_False) [3]
  apply (auto elim: step.cases dest: is_true_and_is_false_implies_False) [1]
  done

lemma step_right_unique: "right_unique step"
  using step_deterministic
  by (rule right_uniqueI)

lemma final_finished:
  assumes "final F_get IReturn s"
  shows "finished step s"
  unfolding finished_def
proof (rule notI)
  assume "\<exists>x. step s x"
  then obtain s' where "step s s'" by auto
  thus False
    using \<open>final F_get IReturn s\<close>
    by (auto simp: state_ok_def elim!: step.cases final.cases)
qed

sublocale semantics step "final F_get IReturn"
  using final_finished step_deterministic
  by unfold_locales

definition load where
  "load \<equiv> Global.load F_get uninitialized"

sublocale language step "final F_get IReturn" load
  by unfold_locales

end

end